/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Data.EReal.Inv
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Topological structure on `EReal`

We prove basic properties of the topology on `EReal`.

## Main results

* `Real.toEReal : ℝ → EReal` is an open embedding
* `ENNReal.toEReal : ℝ≥0∞ → EReal` is a closed embedding
* The addition on `EReal` is continuous except at `(⊥, ⊤)` and at `(⊤, ⊥)`.
* Negation is a homeomorphism on `EReal`.

## Implementation

Most proofs are adapted from the corresponding proofs on `ℝ≥0∞`.
-/

@[expose] public section

noncomputable section

open Set Filter Metric TopologicalSpace Topology
open scoped ENNReal

variable {α : Type*} [TopologicalSpace α]

namespace EReal

/-! ### Real coercion -/

/-
**EReal.isEmbedding_coe** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：isEmbedding_coe : IsEmbedding ((↑) : Real -> EReal)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.isEmbedding_of_ordConnected`：StrictMono.isEmbedding_of_ordCon
nected {α β : Type*} [LinearOrder α] [LinearOrder β] [TopologicalSpace α] [h : O
rderTopology α] [Topological…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `EReal.instOrderTopology`：OrderTopology EReal
· 使用定理 `EReal.coe_strictMono`：coe_strictMono : StrictMono Real.toEReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.range_coe_eq_Ioo`：range_coe_eq_Ioo : range Real.toEReal = Ioo ⊥ ⊤

--- 原说明 ---
### Real coercion
-/
theorem isEmbedding_coe : IsEmbedding ((↑) : ℝ → EReal) :=
  coe_strictMono.isEmbedding_of_ordConnected <| by rw [range_coe_eq_Ioo]; exact ordConnected_Ioo
/-
**EReal.isOpenEmbedding_coe** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：isOpenEmbedding_coe : IsOpenEmbedding ((↑) : Real -> EReal)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EReal.isEmbedding_coe`：isEmbedding_coe : IsEmbedding ((↑) : Real -> ERea
l)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.range_coe_eq_Ioo`：range_coe_eq_Ioo : range Real.toEReal = Ioo ⊥ ⊤
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `EReal.instOrderTopology`：OrderTopology EReal
-/
theorem isOpenEmbedding_coe : IsOpenEmbedding ((↑) : ℝ → EReal) :=
  ⟨isEmbedding_coe, by simp only [range_coe_eq_Ioo, isOpen_Ioo]⟩

@[norm_cast]
/-
**EReal.tendsto_coe** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：tendsto_coe {α : Type*} {f : Filter α} {m : α -> Real} {a : Real} : Tendst
o (fun a => (m a : EReal)) f (𝓝 ↑a) ↔ Tendsto m f (𝓝 a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Topology.IsEmbedding.tendsto_nhds_iff`：∀ {Y : Type u_2} {Z : Type u_3} {
ι : Type u_4} {g : Y → Z} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace
 Z]   {f : ι → Y} {l : Filt…
· 使用定理 `EReal.isEmbedding_coe`：isEmbedding_coe : IsEmbedding ((↑) : Real -> ERea
l)
-/
theorem tendsto_coe {α : Type*} {f : Filter α} {m : α → ℝ} {a : ℝ} :
    Tendsto (fun a => (m a : EReal)) f (𝓝 ↑a) ↔ Tendsto m f (𝓝 a) :=
  isEmbedding_coe.tendsto_nhds_iff.symm
/-
**EReal._root_.continuous_coe_real_ereal** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.continuous_coe_real_ereal : Continuous ((↑) : ℝ → EReal) :=
  isEmbedding_coe.continuous
/-
**EReal.continuous_coe_iff** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：continuous_coe_iff {f : α -> Real} : (Continuous fun a => (f a : EReal)) ↔
 Continuous f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Topology.IsEmbedding.continuous_iff`：∀ {X : Type u_1} {Y : Type u_2} {Z 
: Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topo
logicalSpace Y] [inst_2 :…
· 使用定理 `EReal.isEmbedding_coe`：isEmbedding_coe : IsEmbedding ((↑) : Real -> ERea
l)
-/
theorem continuous_coe_iff {f : α → ℝ} : (Continuous fun a => (f a : EReal)) ↔ Continuous f :=
  isEmbedding_coe.continuous_iff.symm
/-
**EReal.nhds_coe** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：nhds_coe {r : Real} : 𝓝 (r : EReal) = (𝓝 r).map (↑)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsOpenEmbedding.map_nhds_eq`：∀ {X : Type u_1} {Y : Type u_2} {f
 : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.
IsOpenEmbedding f → ∀ (x :…
· 使用定理 `EReal.isOpenEmbedding_coe`：isOpenEmbedding_coe : IsOpenEmbedding ((↑) : 
Real -> EReal)
-/
theorem nhds_coe {r : ℝ} : 𝓝 (r : EReal) = (𝓝 r).map (↑) :=
  (isOpenEmbedding_coe.map_nhds_eq r).symm
/-
**EReal.nhds_coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：nhds_coe_coe {r p : Real} : 𝓝 ((r : EReal), (p : EReal)) = (𝓝 (r, p)).map 
fun p : Real × Real => (↑p.1, ↑p.2)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsOpenEmbedding.map_nhds_eq`：∀ {X : Type u_1} {Y : Type u_2} {f
 : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.
IsOpenEmbedding f → ∀ (x :…
· 使用定理 `Topology.IsOpenEmbedding.prodMap`：∀ {X : Type u} {Y : Type v} {W : Type 
u_1} {Z : Type u_2} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   
[inst_2 : TopologicalS…
· 使用定理 `EReal.isOpenEmbedding_coe`：isOpenEmbedding_coe : IsOpenEmbedding ((↑) : 
Real -> EReal)
-/
theorem nhds_coe_coe {r p : ℝ} :
    𝓝 ((r : EReal), (p : EReal)) = (𝓝 (r, p)).map fun p : ℝ × ℝ => (↑p.1, ↑p.2) :=
  ((isOpenEmbedding_coe.prodMap isOpenEmbedding_coe).map_nhds_eq (r, p)).symm
/-
**EReal.tendsto_toReal** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：tendsto_toReal {a : EReal} (ha : a != ⊤) (h'a : a != ⊥) : Tendsto EReal.to
Real (𝓝 a) (𝓝 a.toReal)
参数：ha : a != ⊤；h'a : a != ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.nhds_coe`：nhds_coe {r : Real} : 𝓝 (r : EReal) = (𝓝 r).map (↑)
· 使用定理 `Filter.tendsto_map'_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{f : β → γ} {g : α → β} {x : Filter α} {y : Filter γ},   Filter.Tendsto f (Filte
r.map g x) y …
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
-/
theorem tendsto_toReal {a : EReal} (ha : a ≠ ⊤) (h'a : a ≠ ⊥) :
    Tendsto EReal.toReal (𝓝 a) (𝓝 a.toReal) := by
  lift a to ℝ using ⟨ha, h'a⟩
  rw [nhds_coe, tendsto_map'_iff]
  exact tendsto_id
/-
**EReal.continuousOn_toReal** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：continuousOn_toReal : ContinuousOn EReal.toReal ({⊥, ⊤}ᶜ : Set EReal)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `EReal.tendsto_toReal`：tendsto_toReal {a : EReal} (ha : a != ⊤) (h'a : a 
!= ⊥) : Tendsto EReal.toReal (𝓝 a) (𝓝 a.toReal)
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
-/
theorem continuousOn_toReal : ContinuousOn EReal.toReal ({⊥, ⊤}ᶜ : Set EReal) := fun _a ha =>
  ContinuousAt.continuousWithinAt (tendsto_toReal (mt Or.inr ha) (mt Or.inl ha))

/-- The set of finite `EReal` numbers is homeomorphic to `ℝ`. -/
/-
**EReal.neBotTopHomeomorphReal** 是 Mathlib 中的一个定义，位于命名空间 `EReal`。
形式化陈述：neBotTopHomeomorphReal : ({⊥, ⊤}ᶜ : Set EReal) ≃ₜ Real where toEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of finite `EReal` numbers is homeomorphic to `ℝ`.
-/
def neBotTopHomeomorphReal : ({⊥, ⊤}ᶜ : Set EReal) ≃ₜ ℝ where
  toEquiv := neTopBotEquivReal
  continuous_toFun := continuousOn_iff_continuous_domRestrict.1 continuousOn_toReal
  continuous_invFun := continuous_coe_real_ereal.subtype_mk _

/-! ### ENNReal coercion -/

/-
**EReal.isEmbedding_coe_ennreal** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：isEmbedding_coe_ennreal : IsEmbedding ((↑) : Real>=0∞ -> EReal)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.isEmbedding_of_ordConnected`：StrictMono.isEmbedding_of_ordCon
nected {α β : Type*} [LinearOrder α] [LinearOrder β] [TopologicalSpace α] [h : O
rderTopology α] [Topological…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `EReal.instOrderTopology`：OrderTopology EReal
· 使用定理 `EReal.coe_ennreal_strictMono`：coe_ennreal_strictMono : StrictMono ((↑) :
 Real>=0∞ -> EReal)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.range_coe_ennreal`：Set.range ENNReal.toEReal = Set.Ici 0

--- 原说明 ---
### ENNReal coercion
-/
theorem isEmbedding_coe_ennreal : IsEmbedding ((↑) : ℝ≥0∞ → EReal) :=
  coe_ennreal_strictMono.isEmbedding_of_ordConnected <| by
    rw [range_coe_ennreal]; exact ordConnected_Ici
/-
**EReal.isClosedEmbedding_coe_ennreal** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：isClosedEmbedding_coe_ennreal : IsClosedEmbedding ((↑) : Real>=0∞ -> EReal
)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EReal.isEmbedding_coe_ennreal`：isEmbedding_coe_ennreal : IsEmbedding ((↑
) : Real>=0∞ -> EReal)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.range_coe_ennreal`：Set.range ENNReal.toEReal = Set.Ici 0
· 使用定理 `isClosed_Ici`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Preor
der α] [ClosedIciTopology α] {a : α}, IsClosed (Set.Ici a)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `EReal.instOrderTopology`：OrderTopology EReal
-/
theorem isClosedEmbedding_coe_ennreal : IsClosedEmbedding ((↑) : ℝ≥0∞ → EReal) :=
  ⟨isEmbedding_coe_ennreal, by rw [range_coe_ennreal]; exact isClosed_Ici⟩

@[norm_cast]
/-
**EReal.tendsto_coe_ennreal** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：tendsto_coe_ennreal {α : Type*} {f : Filter α} {m : α -> Real>=0∞} {a : Re
al>=0∞} : Tendsto (fun a => (m a : EReal)) f (𝓝 ↑a) ↔ Tendsto m f (𝓝 a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Topology.IsEmbedding.tendsto_nhds_iff`：∀ {Y : Type u_2} {Z : Type u_3} {
ι : Type u_4} {g : Y → Z} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace
 Z]   {f : ι → Y} {l : Filt…
· 使用定理 `EReal.isEmbedding_coe_ennreal`：isEmbedding_coe_ennreal : IsEmbedding ((↑
) : Real>=0∞ -> EReal)
-/
theorem tendsto_coe_ennreal {α : Type*} {f : Filter α} {m : α → ℝ≥0∞} {a : ℝ≥0∞} :
    Tendsto (fun a => (m a : EReal)) f (𝓝 ↑a) ↔ Tendsto m f (𝓝 a) :=
  isEmbedding_coe_ennreal.tendsto_nhds_iff.symm
/-
**EReal._root_.continuous_coe_ennreal_ereal** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.continuous_coe_ennreal_ereal : Continuous ((↑) : ℝ≥0∞ → EReal) :=
  isEmbedding_coe_ennreal.continuous
/-
**EReal.continuous_coe_ennreal_iff** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：continuous_coe_ennreal_iff {f : α -> Real>=0∞} : (Continuous fun a => (f a
 : EReal)) ↔ Continuous f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Topology.IsEmbedding.continuous_iff`：∀ {X : Type u_1} {Y : Type u_2} {Z 
: Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : Topo
logicalSpace Y] [inst_2 :…
· 使用定理 `EReal.isEmbedding_coe_ennreal`：isEmbedding_coe_ennreal : IsEmbedding ((↑
) : Real>=0∞ -> EReal)
-/
theorem continuous_coe_ennreal_iff {f : α → ℝ≥0∞} :
    (Continuous fun a => (f a : EReal)) ↔ Continuous f :=
  isEmbedding_coe_ennreal.continuous_iff.symm

/-! ### Neighborhoods of infinity -/

/-
**EReal.nhds_top** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：nhds_top : 𝓝 (⊤ : EReal) = ⨅ (a) (_ : a != ⊤), 𝓟 (Ioi a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `nhds_top_order`：nhds_top_order [TopologicalSpace α] [Preorder α] [OrderT
op α] [OrderTopology α] : 𝓝 (⊤ : α) = ⨅ (l) (_ : l < ⊤), 𝓟 (Ioi l)
· 使用定理 `EReal.instOrderTopology`：OrderTopology EReal
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

--- 原说明 ---
### Neighborhoods of infinity
-/
theorem nhds_top : 𝓝 (⊤ : EReal) = ⨅ (a) (_ : a ≠ ⊤), 𝓟 (Ioi a) :=
  nhds_top_order.trans <| by simp only [lt_top_iff_ne_top]

nonrec theorem nhds_top_basis : (𝓝 (⊤ : EReal)).HasBasis (fun _ : ℝ ↦ True) (Ioi ·) := by
  refine (nhds_top_basis (α := EReal)).to_hasBasis (fun x hx => ?_)
    fun _ _ ↦ ⟨_, coe_lt_top _, Subset.rfl⟩
  rcases exists_rat_btwn_of_lt hx with ⟨y, hxy, -⟩
  exact ⟨_, trivial, Ioi_subset_Ioi hxy.le⟩
/-
**EReal.nhds_top'** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：nhds_top' : 𝓝 (⊤ : EReal) = ⨅ a : Real, 𝓟 (Ioi ↑a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.eq_iInf`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{s : ι → Set α},   l.HasBasis (fun x => True) s → l = ⨅ i, Filter.principal (s i
)
· 使用定理 `EReal.nhds_top_basis`：(nhds ⊤).HasBasis (fun x => True) fun x => Set.Ioi
 ↑x
-/
theorem nhds_top' : 𝓝 (⊤ : EReal) = ⨅ a : ℝ, 𝓟 (Ioi ↑a) := nhds_top_basis.eq_iInf
/-
**EReal.mem_nhds_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：mem_nhds_top_iff {s : Set EReal} : s in 𝓝 (⊤ : EReal) ↔ exists y : Real, I
oi (y : EReal) subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `EReal.nhds_top_basis`：(nhds ⊤).HasBasis (fun x => True) fun x => Set.Ioi
 ↑x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_nhds_top_iff {s : Set EReal} : s ∈ 𝓝 (⊤ : EReal) ↔ ∃ y : ℝ, Ioi (y : EReal) ⊆ s :=
  nhds_top_basis.mem_iff.trans <| by simp only [true_and]
/-
**EReal.tendsto_nhds_top_iff_real** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：tendsto_nhds_top_iff_real {α : Type*} {m : α -> EReal} {f : Filter α} : Te
ndsto m f (𝓝 ⊤) ↔ forall x : Real, forallᶠ a in f, ↑x < m a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `EReal.nhds_top_basis`：(nhds ⊤).HasBasis (fun x => True) fun x => Set.Ioi
 ↑x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `true_implies`：∀ (p : Prop), (True → p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_nhds_top_iff_real {α : Type*} {m : α → EReal} {f : Filter α} :
    Tendsto m f (𝓝 ⊤) ↔ ∀ x : ℝ, ∀ᶠ a in f, ↑x < m a :=
  nhds_top_basis.tendsto_right_iff.trans <| by simp only [true_implies, mem_Ioi]
/-
**EReal.nhds_bot** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：nhds_bot : 𝓝 (⊥ : EReal) = ⨅ (a) (_ : a != ⊥), 𝓟 (Iio a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `nhds_bot_order`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Pre
order α] [inst_2 : OrderBot α] [OrderTopology α],   nhds ⊥ = ⨅ l, ⨅ (_ : ⊥ < l),
 Fil…
· 使用定理 `EReal.instOrderTopology`：OrderTopology EReal
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
theorem nhds_bot : 𝓝 (⊥ : EReal) = ⨅ (a) (_ : a ≠ ⊥), 𝓟 (Iio a) :=
  nhds_bot_order.trans <| by simp only [bot_lt_iff_ne_bot]
/-
**EReal.nhds_bot_basis** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：nhds_bot_basis : (𝓝 (⊥ : EReal)).HasBasis (fun _ : Real => True) (Iio ·)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.to_hasBasis`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort 
u_5} {l : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' →
 Set α},   l.HasB…
· 使用定理 `nhds_bot_basis`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Lin
earOrder α] [inst_2 : OrderBot α] [OrderTopology α]   [Nontrivial α], (nhds ⊥).H
asBa…
· 使用定理 `EReal.instOrderTopology`：OrderTopology EReal
· 使用定理 `instNontrivialEReal`：Nontrivial EReal
· 使用定理 `EReal.exists_rat_btwn_of_lt`：exists_rat_btwn_of_lt : forall {a b : EReal
}, a < b -> exists x : Rat, a < (x : Real) ∧ ((x : Real) : EReal) < b | ⊤, _, h 
=> (not_top_lt h)…
· 使用定理 `trivial`：True
· 使用定理 `Set.Iio_subset_Iio`：Iio_subset_Iio (h : a <= b) : Iio a subseteq Iio b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `EReal.bot_lt_coe`：bot_lt_coe (x : Real) : (⊥ : EReal) < x
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem nhds_bot_basis : (𝓝 (⊥ : EReal)).HasBasis (fun _ : ℝ ↦ True) (Iio ·) := by
  refine (_root_.nhds_bot_basis (α := EReal)).to_hasBasis (fun x hx => ?_)
    fun _ _ ↦ ⟨_, bot_lt_coe _, Subset.rfl⟩
  rcases exists_rat_btwn_of_lt hx with ⟨y, -, hxy⟩
  exact ⟨_, trivial, Iio_subset_Iio hxy.le⟩
/-
**EReal.nhds_bot'** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：nhds_bot' : 𝓝 (⊥ : EReal) = ⨅ a : Real, 𝓟 (Iio ↑a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.eq_iInf`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{s : ι → Set α},   l.HasBasis (fun x => True) s → l = ⨅ i, Filter.principal (s i
)
· 使用定理 `EReal.nhds_bot_basis`：nhds_bot_basis : (𝓝 (⊥ : EReal)).HasBasis (fun _ :
 Real => True) (Iio ·)
-/
theorem nhds_bot' : 𝓝 (⊥ : EReal) = ⨅ a : ℝ, 𝓟 (Iio ↑a) :=
  nhds_bot_basis.eq_iInf
/-
**EReal.mem_nhds_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：mem_nhds_bot_iff {s : Set EReal} : s in 𝓝 (⊥ : EReal) ↔ exists y : Real, I
io (y : EReal) subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `EReal.nhds_bot_basis`：nhds_bot_basis : (𝓝 (⊥ : EReal)).HasBasis (fun _ :
 Real => True) (Iio ·)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_nhds_bot_iff {s : Set EReal} : s ∈ 𝓝 (⊥ : EReal) ↔ ∃ y : ℝ, Iio (y : EReal) ⊆ s :=
  nhds_bot_basis.mem_iff.trans <| by simp only [true_and]
/-
**EReal.tendsto_nhds_bot_iff_real** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：tendsto_nhds_bot_iff_real {α : Type*} {m : α -> EReal} {f : Filter α} : Te
ndsto m f (𝓝 ⊥) ↔ forall x : Real, forallᶠ a in f, m a < x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `EReal.nhds_bot_basis`：nhds_bot_basis : (𝓝 (⊥ : EReal)).HasBasis (fun _ :
 Real => True) (Iio ·)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `true_implies`：∀ (p : Prop), (True → p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_nhds_bot_iff_real {α : Type*} {m : α → EReal} {f : Filter α} :
    Tendsto m f (𝓝 ⊥) ↔ ∀ x : ℝ, ∀ᶠ a in f, m a < x :=
  nhds_bot_basis.tendsto_right_iff.trans <| by simp only [true_implies, mem_Iio]
/-
**EReal.nhdsWithin_top** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：nhdsWithin_top : 𝓝[!=] (⊤ : EReal) = (atTop).map Real.toEReal
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.ext`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} {l 
l' : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' → Set 
α},   l.H…
· 使用定理 `nhdsWithin_hasBasis`：nhdsWithin_hasBasis {ι : Sort*} {p : ι -> Prop} {s 
: ι -> Set α} {a : α} (h : (𝓝 a).HasBasis p s) (t : Set α) : (𝓝[t] a).HasBasis p
 fun i =>…
· 使用定理 `nhds_top_basis_Ici`：nhds_top_basis_Ici [TopologicalSpace α] [LinearOrder
 α] [OrderTop α] [OrderTopology α] [Nontrivial α] [DenselyOrdered α] : (𝓝 ⊤).Has
Basis (f…
· 使用定理 `EReal.instOrderTopology`：OrderTopology EReal
· 使用定理 `instNontrivialEReal`：Nontrivial EReal
· 使用定理 `instDenselyOrderedEReal`：DenselyOrdered EReal
· 使用定理 `Filter.HasBasis.map`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l :
 Filter α} {p : ι → Prop} {s : ι → Set α} (f : α → β),   l.HasBasis p s → (Filte
r.map f l…
· 使用定理 `Filter.atTop_basis`：atTop_basis [Nonempty α] : (@atTop α _).HasBasis (fu
n _ => True) Ici
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `EReal.image_coe_Ici`：image_coe_Ici (x : Real) : Real.toEReal '' Ici x = 
Ico ↑x ⊤
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.Ici_bot`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : OrderBot α],
 Set.Ici ⊥ = Set.univ
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LT.lt.ne_top`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderTop α] {
a b : α}, a < b → a ≠ ⊤
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `true_implies`：∀ (p : Prop), (True → p) = p
（共 33 条，此处仅展示前 30 条）
-/
lemma nhdsWithin_top : 𝓝[≠] (⊤ : EReal) = (atTop).map Real.toEReal := by
  apply (nhdsWithin_hasBasis nhds_top_basis_Ici _).ext (atTop_basis.map Real.toEReal)
  · simp only [EReal.image_coe_Ici, true_and]
    intro x hx
    by_cases hx_bot : x = ⊥
    · simp [hx_bot]
    lift x to ℝ using ⟨hx.ne_top, hx_bot⟩
    refine ⟨x, fun x ⟨h1, h2⟩ ↦ ?_⟩
    simp [h1, h2.ne_top]
  · simp only [EReal.image_coe_Ici, true_implies]
    refine fun x ↦ ⟨x, ⟨EReal.coe_lt_top x, fun x ⟨(h1 : _ ≤ x), h2⟩ ↦ ?_⟩⟩
    simp [h1, Ne.lt_top' fun a ↦ h2 a.symm]
/-
**EReal.nhdsWithin_bot** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：nhdsWithin_bot : 𝓝[!=] (⊥ : EReal) = (atBot).map Real.toEReal
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.ext`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} {l 
l' : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' → Set 
α},   l.H…
· 使用定理 `nhdsWithin_hasBasis`：nhdsWithin_hasBasis {ι : Sort*} {p : ι -> Prop} {s 
: ι -> Set α} {a : α} (h : (𝓝 a).HasBasis p s) (t : Set α) : (𝓝[t] a).HasBasis p
 fun i =>…
· 使用定理 `nhds_bot_basis_Iic`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 :
 LinearOrder α] [inst_2 : OrderBot α] [OrderTopology α]   [Nontrivial α] [Densel
yOrdered…
· 使用定理 `EReal.instOrderTopology`：OrderTopology EReal
· 使用定理 `instNontrivialEReal`：Nontrivial EReal
· 使用定理 `instDenselyOrderedEReal`：DenselyOrdered EReal
· 使用定理 `Filter.HasBasis.map`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l :
 Filter α} {p : ι → Prop} {s : ι → Set α} (f : α → β),   l.HasBasis p s → (Filte
r.map f l…
· 使用引理 `Filter.atBot_basis`：atBot_basis {α : Type*} [Preorder α] [IsCodirectedOr
der α] [Nonempty α] : (@atBot α _).HasBasis (fun _ => True) Iic
· 使用定理 `instIsCodirectedOrder`：∀ {R : Type u_3} [inst : Ring R] [inst_1 : Partia
lOrder R] [IsOrderedRing R] [Archimedean R], IsCodirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `EReal.image_coe_Iic`：image_coe_Iic (x : Real) : Real.toEReal '' Iic x = 
Ioc ⊥ ↑x
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.Iic_top`：Iic_top : Iic (⊤ : α) = univ
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LT.lt.ne_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → a ≠ ⊥
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `true_implies`：∀ (p : Prop), (True → p) = p
（共 33 条，此处仅展示前 30 条）
-/
lemma nhdsWithin_bot : 𝓝[≠] (⊥ : EReal) = (atBot).map Real.toEReal := by
  apply (nhdsWithin_hasBasis nhds_bot_basis_Iic _).ext (atBot_basis.map Real.toEReal)
  · simp only [EReal.image_coe_Iic,
      true_and]
    intro x hx
    by_cases hx_top : x = ⊤
    · simp [hx_top]
    lift x to ℝ using ⟨hx_top, hx.ne_bot⟩
    refine ⟨x, fun x ⟨h1, h2⟩ ↦ ?_⟩
    simp [h2, h1.ne_bot]
  · simp only [EReal.image_coe_Iic, true_implies]
    refine fun x ↦ ⟨x, ⟨EReal.bot_lt_coe x, fun x ⟨(h1 : x ≤ _), h2⟩ ↦ ?_⟩⟩
    simp [h1, Ne.bot_lt' fun a ↦ h2 a.symm]

omit [TopologicalSpace α] in
@[simp]
/-
**EReal.tendsto_coe_nhds_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：tendsto_coe_nhds_top_iff {f : α -> Real} {l : Filter α} : Tendsto (fun x =
> Real.toEReal (f x)) l (𝓝 ⊤) ↔ Tendsto f l atTop
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.tendsto_nhds_top_iff_real`：tendsto_nhds_top_iff_real {α : Type*} {
m : α -> EReal} {f : Filter α} : Tendsto m f (𝓝 ⊤) ↔ forall x : Real, forallᶠ a 
in f, ↑x < m a
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用引理 `Filter.atTop_basis_Ioi`：atTop_basis_Ioi [Nonempty α] [NoMaxOrder α] : (@
atTop α _).HasBasis (fun _ => True) Ioi
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
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
lemma tendsto_coe_nhds_top_iff {f : α → ℝ} {l : Filter α} :
    Tendsto (fun x ↦ Real.toEReal (f x)) l (𝓝 ⊤) ↔ Tendsto f l atTop := by
  rw [tendsto_nhds_top_iff_real, atTop_basis_Ioi.tendsto_right_iff]; simp
/-
**EReal.tendsto_coe_atTop** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：tendsto_coe_atTop : Tendsto Real.toEReal atTop (𝓝 ⊤)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `EReal.tendsto_coe_nhds_top_iff`：tendsto_coe_nhds_top_iff {f : α -> Real}
 {l : Filter α} : Tendsto (fun x => Real.toEReal (f x)) l (𝓝 ⊤) ↔ Tendsto f l at
Top
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
-/
lemma tendsto_coe_atTop : Tendsto Real.toEReal atTop (𝓝 ⊤) :=
  tendsto_coe_nhds_top_iff.2 tendsto_id

omit [TopologicalSpace α] in
@[simp]
/-
**EReal.tendsto_coe_nhds_bot_iff** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：tendsto_coe_nhds_bot_iff {f : α -> Real} {l : Filter α} : Tendsto (fun x =
> Real.toEReal (f x)) l (𝓝 ⊥) ↔ Tendsto f l atBot
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.tendsto_nhds_bot_iff_real`：tendsto_nhds_bot_iff_real {α : Type*} {
m : α -> EReal} {f : Filter α} : Tendsto m f (𝓝 ⊥) ↔ forall x : Real, forallᶠ a 
in f, m a < x
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `Filter.atBot_basis_Iio`：∀ {α : Type u_3} [inst : Preorder α] [IsCodirect
edOrder α] [Nonempty α] [NoMinOrder α],   Filter.atBot.HasBasis (fun x => True) 
Set.Iio
· 使用定理 `instIsCodirectedOrder`：∀ {R : Type u_3} [inst : Ring R] [inst_1 : Partia
lOrder R] [IsOrderedRing R] [Archimedean R], IsCodirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
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
lemma tendsto_coe_nhds_bot_iff {f : α → ℝ} {l : Filter α} :
    Tendsto (fun x ↦ Real.toEReal (f x)) l (𝓝 ⊥) ↔ Tendsto f l atBot := by
  rw [tendsto_nhds_bot_iff_real, atBot_basis_Iio.tendsto_right_iff]; simp
/-
**EReal.tendsto_coe_atBot** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：tendsto_coe_atBot : Tendsto Real.toEReal atBot (𝓝 ⊥)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `EReal.tendsto_coe_nhds_bot_iff`：tendsto_coe_nhds_bot_iff {f : α -> Real}
 {l : Filter α} : Tendsto (fun x => Real.toEReal (f x)) l (𝓝 ⊥) ↔ Tendsto f l at
Bot
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
-/
lemma tendsto_coe_atBot : Tendsto Real.toEReal atBot (𝓝 ⊥) :=
  tendsto_coe_nhds_bot_iff.2 tendsto_id
/-
**EReal.tendsto_toReal_atTop** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：tendsto_toReal_atTop : Tendsto EReal.toReal (𝓝[!=] ⊤) atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `EReal.nhdsWithin_top`：nhdsWithin_top : 𝓝[!=] (⊤ : EReal) = (atTop).map R
eal.toEReal
· 使用定理 `Filter.tendsto_map'_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{f : β → γ} {g : α → β} {x : Filter α} {y : Filter γ},   Filter.Tendsto f (Filte
r.map g x) y …
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
-/
lemma tendsto_toReal_atTop : Tendsto EReal.toReal (𝓝[≠] ⊤) atTop := by
  rw [nhdsWithin_top, tendsto_map'_iff]
  exact tendsto_id
/-
**EReal.tendsto_toReal_atBot** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：tendsto_toReal_atBot : Tendsto EReal.toReal (𝓝[!=] ⊥) atBot
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `EReal.nhdsWithin_bot`：nhdsWithin_bot : 𝓝[!=] (⊥ : EReal) = (atBot).map R
eal.toEReal
· 使用定理 `Filter.tendsto_map'_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{f : β → γ} {g : α → β} {x : Filter α} {y : Filter γ},   Filter.Tendsto f (Filte
r.map g x) y …
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
-/
lemma tendsto_toReal_atBot : Tendsto EReal.toReal (𝓝[≠] ⊥) atBot := by
  rw [nhdsWithin_bot, tendsto_map'_iff]
  exact tendsto_id

/-! ### toENNReal -/

/-
**EReal.continuous_toENNReal** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：continuous_toENNReal : Continuous EReal.toENNReal
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.tendsto_nhds_top`：tendsto_nhds_top {m : α -> Real>=0∞} {f : Filt
er α} (h : forall n : Nat, forallᶠ a in f, ↑n < m a) : Tendsto m f (𝓝 ∞)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `eventually_gt_nhds`：eventually_gt_nhds (hab : b < a) : forallᶠ x in 𝓝 a,
 b < x
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `EReal.instOrderTopology`：OrderTopology EReal
· 使用定理 `EReal.coe_lt_top`：coe_lt_top (x : Real) : (x : EReal) < ⊤
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `EReal.toENNReal_lt_toENNReal`：toENNReal_lt_toENNReal {x y : EReal} (hx :
 0 <= x) (hxy : x < y) : x.toENNReal < y.toENNReal
· 使用定理 `EReal.coe_ennreal_nonneg`：coe_ennreal_nonneg (x : Real>=0∞) : (0 : EReal
) <= x
· 使用引理 `EReal.toENNReal_coe`：toENNReal_coe {x : Real>=0∞} : (x : EReal).toENNRea
l = x
· 使用定理 `ContinuousOn.continuousAt`：ContinuousOn.continuousAt (h : ContinuousOn f
 s) (hx : s in 𝓝 x) : ContinuousAt f x
· 使用定理 `ContinuousOn.congr`：ContinuousOn.congr (h : ContinuousOn f s) (h' : EqOn
 g f s) : ContinuousOn g s
· 使用定理 `continuousOn_of_forall_continuousAt`：continuousOn_of_forall_continuousAt
 (hcont : forall x in s, ContinuousAt f x) : ContinuousOn f s
· 使用定理 `tendsto_nhds_of_eventually_eq`：tendsto_nhds_of_eventually_eq {l : Filter
 α} {f : α -> X} (h : forallᶠ x' in l, f x' = x) : Tendsto f l (𝓝 x)
· 使用定理 `Filter.HasBasis.eventually_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fil
ter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : α → Prop}, (∀ᶠ 
(x : α) in l, q x) ↔…
· 使用定理 `EReal.nhds_bot_basis`：nhds_bot_basis : (𝓝 (⊥ : EReal)).HasBasis (fun _ :
 Real => True) (Iio ·)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `ENNReal.ofReal_zero`：ENNReal.ofReal 0 = 0
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用引理 `EReal.toReal_nonpos`：toReal_nonpos {x : EReal} (hx : x <= 0) : x.toReal 
<= 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `ContinuousAt.comp'`：ContinuousAt.comp' {g : Y -> Z} {x : X} (hg : Contin
uousAt g (f x)) (hf : ContinuousAt f x) : ContinuousAt (fun x => g (f x)) x
（共 45 条，此处仅展示前 30 条）

--- 原说明 ---
### toENNReal
-/
lemma continuous_toENNReal : Continuous EReal.toENNReal := by
  refine continuous_iff_continuousAt.mpr fun x ↦ ?_
  by_cases h_top : x = ⊤
  · simp only [ContinuousAt, h_top, toENNReal_top]
    refine ENNReal.tendsto_nhds_top fun n ↦ ?_
    filter_upwards [eventually_gt_nhds (coe_lt_top n)] with y hy
    exact toENNReal_coe (x := n) ▸ toENNReal_lt_toENNReal (coe_ennreal_nonneg _) hy
  refine ContinuousOn.continuousAt ?_ (compl_singleton_mem_nhds_iff.mpr h_top)
  refine (continuousOn_of_forall_continuousAt fun x hx ↦ ?_).congr (fun _ h ↦ toENNReal_of_ne_top h)
  by_cases h_bot : x = ⊥
  · refine tendsto_nhds_of_eventually_eq ?_
    rw [h_bot, nhds_bot_basis.eventually_iff]
    simpa [toReal_bot, ENNReal.ofReal_zero, ENNReal.ofReal_eq_zero, true_and] using
      ⟨0, fun _ hx ↦ toReal_nonpos hx.le⟩
  refine ENNReal.continuous_ofReal.continuousAt.comp' <| continuousOn_toReal.continuousAt
    <| (toFinite _).isClosed.compl_mem_nhds ?_
  simp_all only [mem_compl_iff, mem_singleton_iff, mem_insert_iff, or_self, not_false_eq_true]

@[fun_prop]
/-
**EReal._root_.Continuous.ereal_toENNReal** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Continuous.ereal_toENNReal {α : Type*} [TopologicalSpace α] {f : α → EReal}
    (hf : Continuous f) :
    Continuous fun x => (f x).toENNReal :=
  continuous_toENNReal.comp hf

@[fun_prop]
/-
**EReal._root_.ContinuousOn.ereal_toENNReal** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ContinuousOn.ereal_toENNReal {α : Type*} [TopologicalSpace α] {s : Set α}
    {f : α → EReal} (hf : ContinuousOn f s) :
    ContinuousOn (fun x => (f x).toENNReal) s :=
  continuous_toENNReal.comp_continuousOn hf

@[fun_prop]
/-
**EReal._root_.ContinuousWithinAt.ereal_toENNReal** 是 Mathlib 中的一个引理，位于命名空间 `ERe
al`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ContinuousWithinAt.ereal_toENNReal {α : Type*} [TopologicalSpace α] {f : α → EReal}
    {s : Set α} {x : α} (hf : ContinuousWithinAt f s x) :
    ContinuousWithinAt (fun x => (f x).toENNReal) s x :=
  continuous_toENNReal.continuousAt.comp_continuousWithinAt hf

@[fun_prop]
/-
**EReal._root_.ContinuousAt.ereal_toENNReal** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ContinuousAt.ereal_toENNReal {α : Type*} [TopologicalSpace α] {f : α → EReal}
    {x : α} (hf : ContinuousAt f x) :
    ContinuousAt (fun x => (f x).toENNReal) x :=
  continuous_toENNReal.continuousAt.comp hf

/-! ### Infs and Sups -/

variable {α : Type*} {u v : α → EReal}

/-
**EReal.add_iInf_le_iInf_add** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：add_iInf_le_iInf_add : (⨅ x, u x) + ⨅ x, v x <= ⨅ x, (u + v) x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsOrderedAddMonoidEReal`：IsOrderedAddMonoid EReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
-/
lemma add_iInf_le_iInf_add : (⨅ x, u x) + ⨅ x, v x ≤ ⨅ x, (u + v) x :=
  le_iInf fun i ↦ add_le_add (iInf_le u i) (iInf_le v i)
/-
**EReal.iSup_add_le_add_iSup** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：iSup_add_le_add_iSup : ⨆ x, (u + v) x <= (⨆ x, u x) + ⨆ x, v x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsOrderedAddMonoidEReal`：IsOrderedAddMonoid EReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
lemma iSup_add_le_add_iSup : ⨆ x, (u + v) x ≤ (⨆ x, u x) + ⨆ x, v x :=
  iSup_le fun i ↦ add_le_add (le_iSup u i) (le_iSup v i)

/-! ### Liminfs and Limsups -/

section LimInfSup

variable {α : Type*} {f : Filter α} {u v : α → EReal}

/-
**EReal.liminf_neg** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：liminf_neg : liminf (-v) f = -limsup v f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderIso.limsup_apply`：OrderIso.limsup_apply {γ} [ConditionallyCompleteL
attice β] [ConditionallyCompleteLattice γ] {f : Filter α} {u : α -> β} (g : β ≃o
 γ) (hu : f…
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `Filter.isCobounded_le_of_bot`：isCobounded_le_of_bot [LE α] [OrderBot α] 
{f : Filter α} : f.IsCobounded (· <= ·)
-/
lemma liminf_neg : liminf (-v) f = -limsup v f :=
  EReal.negOrderIso.limsup_apply.symm
/-
**EReal.limsup_neg** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：limsup_neg : limsup (-v) f = -liminf v f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderIso.liminf_apply`：OrderIso.liminf_apply {γ} [ConditionallyCompleteL
attice β] [ConditionallyCompleteLattice γ] {f : Filter α} {u : α -> β} (g : β ≃o
 γ) (hu : f…
· 使用定理 `Filter.isBounded_ge_of_bot`：∀ {α : Type u_1} [inst : LE α] [OrderBot α] 
{f : Filter α}, Filter.IsBounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `Filter.isCobounded_ge_of_top`：∀ {α : Type u_1} [inst : LE α] [OrderTop α
] {f : Filter α}, Filter.IsCobounded (fun x1 x2 => x2 ≤ x1) f
-/
lemma limsup_neg : limsup (-v) f = -liminf v f :=
  EReal.negOrderIso.liminf_apply.symm
/-
**EReal.le_liminf_add** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：le_liminf_add : (liminf u f) + (liminf v f) <= liminf (u + v) f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `EReal.add_le_of_forall_lt`：add_le_of_forall_lt {a b c : EReal} (h : fora
ll a' < a, forall b' < b, a' + b' <= c) : a + b <= c
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
· 使用定理 `EReal.add_lt_add`：add_lt_add {x y z t : EReal} (h1 : x < y) (h2 : z < t)
 : x + z < y + t
-/
lemma le_liminf_add : (liminf u f) + (liminf v f) ≤ liminf (u + v) f := by
  refine add_le_of_forall_lt fun a a_u b b_v ↦ (le_liminf_iff).2 fun c c_ab ↦ ?_
  filter_upwards [eventually_lt_of_lt_liminf a_u, eventually_lt_of_lt_liminf b_v] with x a_x b_x
  exact c_ab.trans (add_lt_add a_x b_x)
/-
**EReal.limsup_add_le** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：limsup_add_le (h : limsup u f != ⊥ ∨ limsup v f != ⊤) (h' : limsup u f != 
⊤ ∨ limsup v f != ⊥) : limsup (u + v) f <= (limsup u f) + (limsup v f)
参数：h : limsup u f != ⊥ ∨ limsup v f != ⊤；h' : limsup u f != ⊤ ∨ limsup v f != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `EReal.le_add_of_forall_gt`：le_add_of_forall_gt {a b c : EReal} (h₁ : a !
= ⊥ ∨ b != ⊤) (h₂ : a != ⊤ ∨ b != ⊥) (h : forall a' > a, forall b' > b, c <= a' 
+ b') : c <= a …
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
· 使用定理 `EReal.add_lt_add`：add_lt_add {x y z t : EReal} (h1 : x < y) (h2 : z < t)
 : x + z < y + t
-/
lemma limsup_add_le (h : limsup u f ≠ ⊥ ∨ limsup v f ≠ ⊤) (h' : limsup u f ≠ ⊤ ∨ limsup v f ≠ ⊥) :
    limsup (u + v) f ≤ (limsup u f) + (limsup v f) := by
  refine le_add_of_forall_gt h h' fun a a_u b b_v ↦ (limsup_le_iff).2 fun c c_ab ↦ ?_
  filter_upwards [eventually_lt_of_limsup_lt a_u, eventually_lt_of_limsup_lt b_v] with x a_x b_x
  exact (add_lt_add a_x b_x).trans c_ab
/-
**EReal.le_limsup_add** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：le_limsup_add : (limsup u f) + (liminf v f) <= limsup (u + v) f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `EReal.add_le_of_forall_lt`：add_le_of_forall_lt {a b c : EReal} (h : fora
ll a' < a, forall b' < b, a' + b' <= c) : a + b <= c
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
· 使用定理 `EReal.add_lt_add`：add_lt_add {x y z t : EReal} (h1 : x < y) (h2 : z < t)
 : x + z < y + t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma le_limsup_add : (limsup u f) + (liminf v f) ≤ limsup (u + v) f :=
  add_le_of_forall_lt fun _ a_u _ b_v ↦ (le_limsup_iff).2 fun _ c_ab ↦
    (((frequently_lt_of_lt_limsup) a_u).and_eventually ((eventually_lt_of_lt_liminf) b_v)).mono
    fun _ ab_x ↦ c_ab.trans (add_lt_add ab_x.1 ab_x.2)
/-
**EReal.liminf_add_le** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：liminf_add_le (h : limsup u f != ⊥ ∨ liminf v f != ⊤) (h' : limsup u f != 
⊤ ∨ liminf v f != ⊥) : liminf (u + v) f <= (limsup u f) + (liminf v f)
参数：h : limsup u f != ⊥ ∨ liminf v f != ⊤；h' : limsup u f != ⊤ ∨ liminf v f != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `EReal.le_add_of_forall_gt`：le_add_of_forall_gt {a b c : EReal} (h₁ : a !
= ⊥ ∨ b != ⊤) (h₂ : a != ⊤ ∨ b != ⊥) (h : forall a' > a, forall b' > b, c <= a' 
+ b') : c <= a …
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
· 使用定理 `EReal.add_lt_add`：add_lt_add {x y z t : EReal} (h1 : x < y) (h2 : z < t)
 : x + z < y + t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma liminf_add_le (h : limsup u f ≠ ⊥ ∨ liminf v f ≠ ⊤) (h' : limsup u f ≠ ⊤ ∨ liminf v f ≠ ⊥) :
    liminf (u + v) f ≤ (limsup u f) + (liminf v f) :=
  le_add_of_forall_gt h h' fun _ a_u _ b_v ↦ (liminf_le_iff).2 fun _ c_ab ↦
    (((frequently_lt_of_liminf_lt) b_v).and_eventually ((eventually_lt_of_limsup_lt) a_u)).mono
    fun _ ab_x ↦ (add_lt_add ab_x.2 ab_x.1).trans c_ab
/-
**EReal.limsup_add_bot_of_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：limsup_add_bot_of_ne_top (h : limsup u f = ⊥) (h' : limsup v f != ⊤) : lim
sup (u + v) f = ⊥
参数：h : limsup u f = ⊥；h' : limsup v f != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `EReal.limsup_add_le`：limsup_add_le (h : limsup u f != ⊥ ∨ limsup v f != 
⊤) (h' : limsup u f != ⊤ ∨ limsup v f != ⊥) : limsup (u + v) f <= (limsup u f) +
 (limsup …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `bot_ne_top`：bot_ne_top : (⊥ : α) != ⊤
· 使用定理 `instNontrivialEReal`：Nontrivial EReal
· 使用定理 `EReal.bot_add`：bot_add (x : EReal) : ⊥ + x = ⊥
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma limsup_add_bot_of_ne_top (h : limsup u f = ⊥) (h' : limsup v f ≠ ⊤) :
    limsup (u + v) f = ⊥ := by
  apply le_bot_iff.1 ((limsup_add_le (.inr h') _).trans _)
  · rw [h]; exact .inl bot_ne_top
  · rw [h, bot_add]
/-
**EReal.limsup_add_le_of_le** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：limsup_add_le_of_le {a b : EReal} (ha : limsup u f < a) (hb : limsup v f <
= b) : limsup (u + v) f <= a + b
参数：ha : limsup u f < a；hb : limsup v f <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_top_or_lt_top`：eq_top_or_lt_top (a : α) : a = ⊤ ∨ a < ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.add_top_of_ne_bot`：add_top_of_ne_bot {x : EReal} (h : x != ⊥) : x 
+ ⊤ = ⊤
· 使用定理 `LT.lt.ne_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → a ≠ ⊥
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `EReal.limsup_add_le`：limsup_add_le (h : limsup u f != ⊥ ∨ limsup v f != 
⊤) (h' : limsup u f != ⊤ ∨ limsup v f != ⊥) : limsup (u + v) f <= (limsup u f) +
 (limsup …
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `LT.lt.ne_top`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderTop α] {
a b : α}, a < b → a ≠ ⊤
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsOrderedAddMonoidEReal`：IsOrderedAddMonoid EReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma limsup_add_le_of_le {a b : EReal} (ha : limsup u f < a) (hb : limsup v f ≤ b) :
    limsup (u + v) f ≤ a + b := by
  rcases eq_top_or_lt_top b with rfl | h
  · rw [add_top_of_ne_bot ha.ne_bot]; exact le_top
  · exact (limsup_add_le (.inr (hb.trans_lt h).ne) (.inl ha.ne_top)).trans (add_le_add ha.le hb)
/-
**EReal.liminf_add_gt_of_gt** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：liminf_add_gt_of_gt {a b : EReal} (ha : a < liminf u f) (hb : b < liminf v
 f) : a + b < liminf (u + v) f
参数：ha : a < liminf u f；hb : b < liminf v f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `EReal.add_lt_add`：add_lt_add {x y z t : EReal} (h1 : x < y) (h2 : z < t)
 : x + z < y + t
· 使用引理 `EReal.le_liminf_add`：le_liminf_add : (liminf u f) + (liminf v f) <= limi
nf (u + v) f
-/
lemma liminf_add_gt_of_gt {a b : EReal} (ha : a < liminf u f) (hb : b < liminf v f) :
    a + b < liminf (u + v) f :=
  (add_lt_add ha hb).trans_le le_liminf_add
/-
**EReal.liminf_add_top_of_ne_bot** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：liminf_add_top_of_ne_bot (h : liminf u f = ⊤) (h' : liminf v f != ⊥) : lim
inf (u + v) f = ⊤
参数：h : liminf u f = ⊤；h' : liminf v f != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.top_add_of_ne_bot`：top_add_of_ne_bot {x : EReal} (h : x != ⊥) : ⊤ 
+ x = ⊤
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `EReal.le_liminf_add`：le_liminf_add : (liminf u f) + (liminf v f) <= limi
nf (u + v) f
-/
lemma liminf_add_top_of_ne_bot (h : liminf u f = ⊤) (h' : liminf v f ≠ ⊥) :
    liminf (u + v) f = ⊤ := by
  apply top_le_iff.1 (le_trans _ le_liminf_add)
  rw [h, top_add_of_ne_bot h']
/-
**EReal.limsup_const_mul_of_nonneg_of_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：limsup_const_mul_of_nonneg_of_ne_top [NeBot f] {c : EReal} (h₁ : 0 <= c) (
h₂ : c != ⊤) : limsup (fun x => c * u x) f = c * limsup u f
参数：h₁ : 0 <= c；h₂ : c != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Filter.limsup_const`：limsup_const {α : Type*} [ConditionallyCompleteLatt
ice β] {f : Filter α} [NeBot f] (b : β) : limsup (fun _ => b) f = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `EReal.mul_comm`：∀ (x y : EReal), x * y = y * x
· 使用定理 `eq_of_le_of_ge`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Filter.limsup_le_iff`：limsup_le_iff {x : β} (h₁ : f.IsCoboundedUnder (· 
<= ·) u
· 使用定理 `Filter.isCobounded_le_of_bot`：isCobounded_le_of_bot [LE α] [OrderBot α] 
{f : Filter α} : f.IsCobounded (· <= ·)
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `EReal.lt_div_iff`：lt_div_iff (h : 0 < b) (h' : b != ⊤) : a < c / b ↔ a *
 b < c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Filter.eventually_lt_of_limsup_lt`：eventually_lt_of_limsup_lt {f : Filte
r α} [ConditionallyCompleteLinearOrder β] {u : α -> β} {b : β} (h : limsup u f <
 b) (hu : f.IsBoundedUn…
· 使用定理 `Filter.le_limsup_iff`：le_limsup_iff {x : β} (h₁ : f.IsCoboundedUnder (· 
<= ·) u
· 使用引理 `EReal.div_lt_iff`：div_lt_iff (h : 0 < c) (h' : c != ⊤) : b / c < a ↔ b <
 a * c
· 使用定理 `Filter.frequently_lt_of_lt_limsup`：frequently_lt_of_lt_limsup {b : β} (h
u : f.IsCoboundedUnder (· <= ·) u
-/
theorem limsup_const_mul_of_nonneg_of_ne_top [NeBot f] {c : EReal} (h₁ : 0 ≤ c) (h₂ : c ≠ ⊤) :
    limsup (fun x => c * u x) f = c * limsup u f := by
  obtain rfl | h₃ := h₁.eq_or_lt
  · simp
  simp_rw [EReal.mul_comm (x := c)]
  apply eq_of_le_of_ge
  · rw [limsup_le_iff]
    simpa [← EReal.lt_div_iff (by aesop) (by aesop)]
      using fun _ ↦ eventually_lt_of_limsup_lt
  · rw [le_limsup_iff]
    simpa [← EReal.div_lt_iff (by aesop) (by aesop)]
      using fun _ ↦ frequently_lt_of_lt_limsup
/-
**EReal.limsup_const_mul_of_nonpos_of_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：limsup_const_mul_of_nonpos_of_ne_bot [NeBot f] {c : EReal} (h₁ : c <= 0) (
h₂ : c != ⊥) : limsup (fun x => c * u x) f = c * liminf u f
参数：h₁ : c <= 0；h₂ : c != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用引理 `EReal.limsup_neg`：limsup_neg : limsup (-v) f = -liminf v f
· 使用定理 `EReal.limsup_const_mul_of_nonneg_of_ne_top`：limsup_const_mul_of_nonneg_o
f_ne_top [NeBot f] {c : EReal} (h₁ : 0 <= c) (h₂ : c != ⊤) : limsup (fun x => c 
* u x) f = c * limsup u f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem limsup_const_mul_of_nonpos_of_ne_bot [NeBot f] {c : EReal} (h₁ : c ≤ 0) (h₂ : c ≠ ⊥) :
    limsup (fun x => c * u x) f = c * liminf u f := by
  simpa [limsup_neg] using
    limsup_const_mul_of_nonneg_of_ne_top (u := -u) (c := -c) (by aesop) (by aesop)
/-
**EReal.liminf_const_mul_of_nonneg_of_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：liminf_const_mul_of_nonneg_of_ne_top [NeBot f] {c : EReal} (h₁ : 0 <= c) (
h₂ : c != ⊤) : liminf (fun x => c * u x) f = c * liminf u f
参数：h₁ : 0 <= c；h₂ : c != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用引理 `EReal.limsup_neg`：limsup_neg : limsup (-v) f = -liminf v f
· 使用定理 `EReal.limsup_const_mul_of_nonneg_of_ne_top`：limsup_const_mul_of_nonneg_o
f_ne_top [NeBot f] {c : EReal} (h₁ : 0 <= c) (h₂ : c != ⊤) : limsup (fun x => c 
* u x) f = c * limsup u f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem liminf_const_mul_of_nonneg_of_ne_top [NeBot f] {c : EReal} (h₁ : 0 ≤ c) (h₂ : c ≠ ⊤) :
    liminf (fun x => c * u x) f = c * liminf u f := by
  simpa [mul_neg, ← Pi.neg_def, limsup_neg] using
    limsup_const_mul_of_nonneg_of_ne_top (u := -u) (by aesop) (by aesop)
/-
**EReal.liminf_const_mul_of_nonpos_of_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：liminf_const_mul_of_nonpos_of_ne_bot [NeBot f] {c : EReal} (h₁ : c <= 0) (
h₂ : c != ⊥) : liminf (fun x => c * u x) f = c * limsup u f
参数：h₁ : c <= 0；h₂ : c != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用引理 `EReal.limsup_neg`：limsup_neg : limsup (-v) f = -liminf v f
· 使用定理 `EReal.limsup_const_mul_of_nonneg_of_ne_top`：limsup_const_mul_of_nonneg_o
f_ne_top [NeBot f] {c : EReal} (h₁ : 0 <= c) (h₂ : c != ⊤) : limsup (fun x => c 
* u x) f = c * limsup u f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem liminf_const_mul_of_nonpos_of_ne_bot [NeBot f] {c : EReal} (h₁ : c ≤ 0) (h₂ : c ≠ ⊥) :
    liminf (fun x => c * u x) f = c * limsup u f := by
  simpa [neg_mul, ← Pi.neg_def, limsup_neg] using
    limsup_const_mul_of_nonneg_of_ne_top (c := -c) (by aesop) (by aesop)
/-
**EReal.le_limsup_mul** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：le_limsup_mul (hu : existsᶠ x in f, 0 <= u x) (hv : 0 <=ᶠ[f] v) : limsup u
 f * liminf v f <= limsup (u * v) f
参数：hu : existsᶠ x in f, 0 <= u x；hv : 0 <=ᶠ[f] v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.limsup_bot`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLatti
ce α] (f : β → α), Filter.limsup f ⊥ = ⊥
· 使用定理 `Filter.liminf_bot`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLatti
ce α] (f : β → α), Filter.liminf f ⊥ = ⊤
· 使用定理 `EReal.bot_mul_top`：⊥ * ⊤ = ⊥
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Filter.le_limsup_of_frequently_le`：le_limsup_of_frequently_le (hu : exis
tsᶠ i in f, a <= u i) (hu_le : f.IsBoundedUnder (· <= ·) u
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `Filter.Frequently.and_eventually`：∀ {α : Type u} {p q : α → Prop} {f : F
ilter α},   (∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, q x) → ∃ᶠ (x : α) in f, p
 x ∧ q x
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `EReal.instPosMulMono`：PosMulMono EReal
· 使用引理 `EReal.mul_le_of_forall_lt_of_nonneg`：mul_le_of_forall_lt_of_nonneg (ha :
 0 <= a) (hc : 0 <= c) (h : forall a' in Ioo 0 a, forall b' in Ioo 0 b, a' * b' 
<= c) : a * b <= c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_limsup_iff`：le_limsup_iff {x : β} (h₁ : f.IsCoboundedUnder (· 
<= ·) u
· 使用定理 `Filter.isCobounded_le_of_bot`：isCobounded_le_of_bot [LE α] [OrderBot α] 
{f : Filter α} : f.IsCobounded (· <= ·)
· 使用定理 `Filter.frequently_lt_of_lt_limsup`：frequently_lt_of_lt_limsup {b : β} (h
u : f.IsCoboundedUnder (· <= ·) u
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_Ioo`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
oo a b ↔ a < x ∧ x < b
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Filter.eventually_lt_of_lt_liminf`：eventually_lt_of_lt_liminf {f : Filte
r α} [ConditionallyCompleteLinearOrder β] {u : α -> β} {b : β} (h : b < liminf u
 f) (hu : f.IsBoundedUn…
· 使用定理 `Filter.isBounded_ge_of_bot`：∀ {α : Type u_1} [inst : LE α] [OrderBot α] 
{f : Filter α}, Filter.IsBounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `EReal.instMulPosMono`：MulPosMono EReal
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma le_limsup_mul (hu : ∃ᶠ x in f, 0 ≤ u x) (hv : 0 ≤ᶠ[f] v) :
    limsup u f * liminf v f ≤ limsup (u * v) f := by
  rcases f.eq_or_neBot with rfl | _
  · rw [limsup_bot, limsup_bot, liminf_bot, bot_mul_top]
  have u0 : 0 ≤ limsup u f := le_limsup_of_frequently_le hu
  have uv0 : 0 ≤ limsup (u * v) f :=
    le_limsup_of_frequently_le <| (hu.and_eventually hv).mono fun _ ⟨hu, hv⟩ ↦ mul_nonneg hu hv
  refine mul_le_of_forall_lt_of_nonneg u0 uv0 fun a ha b hb ↦ (le_limsup_iff).2 fun c c_ab ↦ ?_
  refine (((frequently_lt_of_lt_limsup) (mem_Ioo.1 ha).2).and_eventually
    <| (eventually_lt_of_lt_liminf (mem_Ioo.1 hb).2).and
    <| hv).mono fun x ⟨xa, ⟨xb, vx⟩⟩ ↦ ?_
  exact c_ab.trans_le (mul_le_mul xa.le xb.le (mem_Ioo.1 hb).1.le ((mem_Ioo.1 ha).1.le.trans xa.le))
/-
**EReal.limsup_mul_le** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：limsup_mul_le (hu : existsᶠ x in f, 0 <= u x) (hv : 0 <=ᶠ[f] v) (h₁ : lims
up u f != 0 ∨ limsup v f != ⊤) (h₂ : limsup u f != ⊤ ∨ limsup v f != 0) : limsup
 (u * v) f <= limsup u f * limsup v f
参数：hu : existsᶠ x in f, 0 <= u x；hv : 0 <=ᶠ[f] v；h₁ : limsup u f != 0 ∨ limsup v
 f != ⊤；h₂ : limsup u f != ⊤ ∨ limsup v f != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.limsup_bot`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLatti
ce α] (f : β → α), Filter.limsup f ⊥ = ⊥
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Filter.le_limsup_of_frequently_le`：le_limsup_of_frequently_le (hu : exis
tsᶠ i in f, a <= u i) (hu_le : f.IsBoundedUnder (· <= ·) u
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `Or.imp_left`：∀ {a b c : Prop}, (a → b) → a ∨ c → b ∨ c
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `Filter.Eventually.frequently`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p
 : α → Prop}, (∀ᶠ (x : α) in f, p x) → ∃ᶠ (x : α) in f, p x
· 使用引理 `EReal.le_mul_of_forall_lt`：le_mul_of_forall_lt (h₁ : 0 < a ∨ b != ⊤) (h₂
 : a != ⊤ ∨ 0 < b) (h : forall a' > a, forall b' > b, c <= a' * b') : c <= a * b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.limsup_le_iff`：limsup_le_iff {x : β} (h₁ : f.IsCoboundedUnder (· 
<= ·) u
· 使用定理 `Filter.isCobounded_le_of_bot`：isCobounded_le_of_bot [LE α] [OrderBot α] 
{f : Filter α} : f.IsCobounded (· <= ·)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_lt_of_limsup_lt`：eventually_lt_of_limsup_lt {f : Filte
r α} [ConditionallyCompleteLinearOrder β] {u : α -> β} {b : β} (h : limsup u f <
 b) (hu : f.IsBoundedUn…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `EReal.mul_nonpos_iff`：mul_nonpos_iff {a b : EReal} : a * b <= 0 ↔ 0 <= a
 ∧ b <= 0 ∨ a <= 0 ∧ 0 <= b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `EReal.instPosMulMono`：PosMulMono EReal
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `EReal.instMulPosMono`：MulPosMono EReal
-/
lemma limsup_mul_le (hu : ∃ᶠ x in f, 0 ≤ u x) (hv : 0 ≤ᶠ[f] v)
    (h₁ : limsup u f ≠ 0 ∨ limsup v f ≠ ⊤) (h₂ : limsup u f ≠ ⊤ ∨ limsup v f ≠ 0) :
    limsup (u * v) f ≤ limsup u f * limsup v f := by
  rcases f.eq_or_neBot with rfl | _
  · rw [limsup_bot]; exact bot_le
  have u_0 : 0 ≤ limsup u f := le_limsup_of_frequently_le hu
  replace h₁ : 0 < limsup u f ∨ limsup v f ≠ ⊤ := h₁.imp_left fun h ↦ lt_of_le_of_ne u_0 h.symm
  replace h₂ : limsup u f ≠ ⊤ ∨ 0 < limsup v f :=
    h₂.imp_right fun h ↦ lt_of_le_of_ne (le_limsup_of_frequently_le hv.frequently) h.symm
  refine le_mul_of_forall_lt h₁ h₂ fun a a_u b b_v ↦ (limsup_le_iff).2 fun c c_ab ↦ ?_
  filter_upwards [eventually_lt_of_limsup_lt a_u, eventually_lt_of_limsup_lt b_v, hv]
    with x x_a x_b v_0
  apply lt_of_le_of_lt _ c_ab
  rcases lt_or_ge (u x) 0 with hux | hux
  · apply (mul_nonpos_iff.2 (.inr ⟨hux.le, v_0⟩)).trans
    exact mul_nonneg (u_0.trans a_u.le) (v_0.trans x_b.le)
  · exact mul_le_mul x_a.le x_b.le v_0 (hux.trans x_a.le)
/-
**EReal.le_liminf_mul** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：le_liminf_mul (hu : 0 <=ᶠ[f] u) (hv : 0 <=ᶠ[f] v) : liminf u f * liminf v 
f <= liminf (u * v) f
参数：hu : 0 <=ᶠ[f] u；hv : 0 <=ᶠ[f] v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `EReal.mul_le_of_forall_lt_of_nonneg`：mul_le_of_forall_lt_of_nonneg (ha :
 0 <= a) (hc : 0 <= c) (h : forall a' in Ioo 0 a, forall b' in Ioo 0 b, a' * b' 
<= c) : a * b <= c
· 使用定理 `Filter.le_liminf_of_le`：le_liminf_of_le {f : Filter β} {u : β -> α} {a} 
(hf : f.IsCoboundedUnder (· >= ·) u
· 使用定理 `Filter.isCobounded_ge_of_top`：∀ {α : Type u_1} [inst : LE α] [OrderTop α
] {f : Filter α}, Filter.IsCobounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `EReal.instPosMulMono`：PosMulMono EReal
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_liminf_iff`：le_liminf_iff {x : β} (h₁ : f.IsCoboundedUnder (· 
>= ·) u
· 使用定理 `Filter.isBounded_ge_of_bot`：∀ {α : Type u_1} [inst : LE α] [OrderBot α] 
{f : Filter α}, Filter.IsBounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_lt_of_lt_liminf`：eventually_lt_of_lt_liminf {f : Filte
r α} [ConditionallyCompleteLinearOrder β] {u : α -> β} {b : β} (h : b < liminf u
 f) (hu : f.IsBoundedUn…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_Ioo`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
oo a b ↔ a < x ∧ x < b
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `EReal.instMulPosMono`：MulPosMono EReal
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma le_liminf_mul (hu : 0 ≤ᶠ[f] u) (hv : 0 ≤ᶠ[f] v) :
    liminf u f * liminf v f ≤ liminf (u * v) f := by
  apply mul_le_of_forall_lt_of_nonneg ((le_liminf_of_le) hu)
    <| (le_liminf_of_le) ((hu.and hv).mono fun x ⟨u0, v0⟩ ↦ mul_nonneg u0 v0)
  refine fun a ha b hb ↦ (le_liminf_iff).2 fun c c_ab ↦ ?_
  filter_upwards [eventually_lt_of_lt_liminf (mem_Ioo.1 ha).2,
    eventually_lt_of_lt_liminf (mem_Ioo.1 hb).2] with x xa xb
  exact c_ab.trans_le (mul_le_mul xa.le xb.le (mem_Ioo.1 hb).1.le ((mem_Ioo.1 ha).1.le.trans xa.le))
/-
**EReal.liminf_mul_le** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：liminf_mul_le [NeBot f] (hu : 0 <=ᶠ[f] u) (hv : 0 <=ᶠ[f] v) (h₁ : limsup u
 f != 0 ∨ liminf v f != ⊤) (h₂ : limsup u f != ⊤ ∨ liminf v f != 0) : liminf (u 
* v) f <= limsup u f * liminf v f
参数：hu : 0 <=ᶠ[f] u；hv : 0 <=ᶠ[f] v；h₁ : limsup u f != 0 ∨ liminf v f != ⊤；h₂ : l
imsup u f != ⊤ ∨ liminf v f != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp_left`：∀ {a b c : Prop}, (a → b) → a ∨ c → b ∨ c
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `le_of_eq_of_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ 
c → a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.limsup_const`：limsup_const {α : Type*} [ConditionallyCompleteLatt
ice β] {f : Filter α} [NeBot f] (b : β) : limsup (fun _ => b) f = b
· 使用定理 `Filter.limsup_le_limsup`：limsup_le_limsup {α : Type*} [ConditionallyComp
leteLattice β] {f : Filter α} {u v : α -> β} (h : u <=ᶠ[f] v) (hu : f.IsCobounde
dUnder (· <= …
· 使用定理 `Filter.isCobounded_le_of_bot`：isCobounded_le_of_bot [LE α] [OrderBot α] 
{f : Filter α} : f.IsCobounded (· <= ·)
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `Filter.liminf_const`：liminf_const {α : Type*} [ConditionallyCompleteLatt
ice β] {f : Filter α} [NeBot f] (b : β) : liminf (fun _ => b) f = b
· 使用定理 `Filter.liminf_le_liminf`：liminf_le_liminf {α : Type*} [ConditionallyComp
leteLattice β] {f : Filter α} {u v : α -> β} (h : forallᶠ a in f, u a <= v a) (h
u : f.IsBound…
· 使用定理 `Filter.isBounded_ge_of_bot`：∀ {α : Type u_1} [inst : LE α] [OrderBot α] 
{f : Filter α}, Filter.IsBounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `Filter.isCobounded_ge_of_top`：∀ {α : Type u_1} [inst : LE α] [OrderTop α
] {f : Filter α}, Filter.IsCobounded (fun x1 x2 => x2 ≤ x1) f
· 使用引理 `EReal.le_mul_of_forall_lt`：le_mul_of_forall_lt (h₁ : 0 < a ∨ b != ⊤) (h₂
 : a != ⊤ ∨ 0 < b) (h : forall a' > a, forall b' > b, c <= a' * b') : c <= a * b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.liminf_le_iff`：liminf_le_iff {x : β} (h₁ : f.IsCoboundedUnder (· 
>= ·) u
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `Filter.Frequently.and_eventually`：∀ {α : Type u} {p q : α → Prop} {f : F
ilter α},   (∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, q x) → ∃ᶠ (x : α) in f, p
 x ∧ q x
· 使用定理 `Filter.frequently_lt_of_liminf_lt`：frequently_lt_of_liminf_lt {b : β} (h
u : f.IsCoboundedUnder (· >= ·) u
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Filter.eventually_lt_of_limsup_lt`：eventually_lt_of_limsup_lt {f : Filte
r α} [ConditionallyCompleteLinearOrder β] {u : α -> β} {b : β} (h : limsup u f <
 b) (hu : f.IsBoundedUn…
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `EReal.instPosMulMono`：PosMulMono EReal
· 使用定理 `EReal.instMulPosMono`：MulPosMono EReal
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma liminf_mul_le [NeBot f] (hu : 0 ≤ᶠ[f] u) (hv : 0 ≤ᶠ[f] v)
    (h₁ : limsup u f ≠ 0 ∨ liminf v f ≠ ⊤) (h₂ : limsup u f ≠ ⊤ ∨ liminf v f ≠ 0) :
    liminf (u * v) f ≤ limsup u f * liminf v f := by
  replace h₁ : 0 < limsup u f ∨ liminf v f ≠ ⊤ := by
    refine h₁.imp_left fun h ↦ lt_of_le_of_ne ?_ h.symm
    exact le_of_eq_of_le (limsup_const 0).symm (limsup_le_limsup hu)
  replace h₂ : limsup u f ≠ ⊤ ∨ 0 < liminf v f := by
    refine h₂.imp_right fun h ↦ lt_of_le_of_ne ?_ h.symm
    exact le_of_eq_of_le (liminf_const 0).symm (liminf_le_liminf hv)
  refine le_mul_of_forall_lt h₁ h₂ fun a a_u b b_v ↦ (liminf_le_iff).2 fun c c_ab ↦ ?_
  refine (((frequently_lt_of_liminf_lt) b_v).and_eventually <| (eventually_lt_of_limsup_lt a_u).and
    <| hu.and hv).mono fun x ⟨x_v, x_u, u_0, v_0⟩ ↦ ?_
  exact (mul_le_mul x_u.le x_v.le v_0 (u_0.trans x_u.le)).trans_lt c_ab

end LimInfSup

/-! ### Continuity of addition -/

/-
**EReal.continuousAt_add_coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：continuousAt_add_coe_coe (a b : Real) : ContinuousAt (fun p : EReal × ERea
l => p.1 + p.2) (a, b)
参数：a b : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.nhds_coe_coe`：nhds_coe_coe {r p : Real} : 𝓝 ((r : EReal), (p : ERe
al)) = (𝓝 (r, p)).map fun p : Real × Real => (↑p.1, ↑p.2)
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ

--- 原说明 ---
### Continuity of addition
-/
theorem continuousAt_add_coe_coe (a b : ℝ) :
    ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (a, b) := by
  simp only [ContinuousAt, nhds_coe_coe, ← coe_add, tendsto_map'_iff, Function.comp_def,
    tendsto_coe, tendsto_add]
/-
**EReal.continuousAt_add_top_coe** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：continuousAt_add_top_coe (a : Real) : ContinuousAt (fun p : EReal × EReal 
=> p.1 + p.2) (⊤, a)
参数：a : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.prod_nhds`：Filter.Eventually.prod_nhds {p : X -> Prop}
 {q : Y -> Prop} {x : X} {y : Y} (hx : forallᶠ x in 𝓝 x, p x) (hy : forallᶠ y in
 𝓝 y, q y) : fora…
· 使用定理 `lt_mem_nhds`：lt_mem_nhds [OrderTopology α] {a b : α} (h : a < b) : foral
lᶠ x in 𝓝 b, a < x
· 使用定理 `EReal.instOrderTopology`：OrderTopology EReal
· 使用定理 `EReal.coe_lt_top`：coe_lt_top (x : Real) : (x : EReal) < ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EReal.coe_lt_coe_iff`：∀ {x y : ℝ}, ↑x < ↑y ↔ x < y
· 使用引理 `sub_one_lt`：sub_one_lt [ZeroLEOneClass R] [NeZero (1 : R)] [AddLeftStric
tMono R] (a : R) : a - 1 < a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `EReal.add_lt_add`：add_lt_add {x y z t : EReal} (h1 : x < y) (h2 : z < t)
 : x + z < y + t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem continuousAt_add_top_coe (a : ℝ) :
    ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (⊤, a) := by
  simp only [ContinuousAt, tendsto_nhds_top_iff_real, top_add_coe]
  refine fun r ↦ ((lt_mem_nhds (coe_lt_top (r - (a - 1)))).prod_nhds
    (lt_mem_nhds <| EReal.coe_lt_coe_iff.2 <| sub_one_lt _)).mono fun _ h ↦ ?_
  simpa only [← coe_add, _root_.sub_add_cancel] using add_lt_add h.1 h.2
/-
**EReal.continuousAt_add_coe_top** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：continuousAt_add_coe_top (a : Real) : ContinuousAt (fun p : EReal × EReal 
=> p.1 + p.2) (a, ⊤)
参数：a : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `EReal.continuousAt_add_top_coe`：continuousAt_add_top_coe (a : Real) : Co
ntinuousAt (fun p : EReal × EReal => p.1 + p.2) (⊤, a)
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `continuous_swap`：continuous_swap : Continuous (Prod.swap : X × Y -> Y × 
X)
-/
theorem continuousAt_add_coe_top (a : ℝ) :
    ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (a, ⊤) := by
  simpa only [add_comm, Function.comp_def, ContinuousAt, Prod.swap]
    using Tendsto.comp (continuousAt_add_top_coe a) (continuous_swap.tendsto ((a : EReal), ⊤))
/-
**EReal.continuousAt_add_top_top** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：continuousAt_add_top_top : ContinuousAt (fun p : EReal × EReal => p.1 + p.
2) (⊤, ⊤)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.prod_nhds`：Filter.Eventually.prod_nhds {p : X -> Prop}
 {q : Y -> Prop} {x : X} {y : Y} (hx : forallᶠ x in 𝓝 x, p x) (hy : forallᶠ y in
 𝓝 y, q y) : fora…
· 使用定理 `lt_mem_nhds`：lt_mem_nhds [OrderTopology α] {a b : α} (h : a < b) : foral
lᶠ x in 𝓝 b, a < x
· 使用定理 `EReal.instOrderTopology`：OrderTopology EReal
· 使用定理 `EReal.coe_lt_top`：coe_lt_top (x : Real) : (x : EReal) < ⊤
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `EReal.add_lt_add`：add_lt_add {x y z t : EReal} (h1 : x < y) (h2 : z < t)
 : x + z < y + t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem continuousAt_add_top_top : ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (⊤, ⊤) := by
  simp only [ContinuousAt, tendsto_nhds_top_iff_real, top_add_top]
  refine fun r ↦ ((lt_mem_nhds (coe_lt_top 0)).prod_nhds
    (lt_mem_nhds <| coe_lt_top r)).mono fun _ h ↦ ?_
  simpa only [coe_zero, zero_add] using add_lt_add h.1 h.2
/-
**EReal.continuousAt_add_bot_coe** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：continuousAt_add_bot_coe (a : Real) : ContinuousAt (fun p : EReal × EReal 
=> p.1 + p.2) (⊥, a)
参数：a : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.bot_add`：bot_add (x : EReal) : ⊥ + x = ⊥
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.prod_nhds`：Filter.Eventually.prod_nhds {p : X -> Prop}
 {q : Y -> Prop} {x : X} {y : Y} (hx : forallᶠ x in 𝓝 x, p x) (hy : forallᶠ y in
 𝓝 y, q y) : fora…
· 使用定理 `gt_mem_nhds`：∀ {α : Type u} [ts : TopologicalSpace α] [inst : Preorder α
] [OrderTopology α] {a b : α},   b < a → ∀ᶠ (x : α) in nhds b, x < a
· 使用定理 `EReal.instOrderTopology`：OrderTopology EReal
· 使用定理 `EReal.bot_lt_coe`：bot_lt_coe (x : Real) : (⊥ : EReal) < x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EReal.coe_lt_coe_iff`：∀ {x y : ℝ}, ↑x < ↑y ↔ x < y
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `EReal.add_lt_add`：add_lt_add {x y z t : EReal} (h1 : x < y) (h2 : z < t)
 : x + z < y + t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem continuousAt_add_bot_coe (a : ℝ) :
    ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (⊥, a) := by
  simp only [ContinuousAt, tendsto_nhds_bot_iff_real, bot_add]
  refine fun r ↦ ((gt_mem_nhds (bot_lt_coe (r - (a + 1)))).prod_nhds
    (gt_mem_nhds <| EReal.coe_lt_coe_iff.2 <| lt_add_one _)).mono fun _ h ↦ ?_
  simpa only [← coe_add, _root_.sub_add_cancel] using add_lt_add h.1 h.2
/-
**EReal.continuousAt_add_coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：continuousAt_add_coe_bot (a : Real) : ContinuousAt (fun p : EReal × EReal 
=> p.1 + p.2) (a, ⊥)
参数：a : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `EReal.continuousAt_add_bot_coe`：continuousAt_add_bot_coe (a : Real) : Co
ntinuousAt (fun p : EReal × EReal => p.1 + p.2) (⊥, a)
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `continuous_swap`：continuous_swap : Continuous (Prod.swap : X × Y -> Y × 
X)
-/
theorem continuousAt_add_coe_bot (a : ℝ) :
    ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (a, ⊥) := by
  simpa only [add_comm, Function.comp_def, ContinuousAt, Prod.swap]
    using Tendsto.comp (continuousAt_add_bot_coe a) (continuous_swap.tendsto ((a : EReal), ⊥))
/-
**EReal.continuousAt_add_bot_bot** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：continuousAt_add_bot_bot : ContinuousAt (fun p : EReal × EReal => p.1 + p.
2) (⊥, ⊥)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.bot_add`：bot_add (x : EReal) : ⊥ + x = ⊥
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.prod_nhds`：Filter.Eventually.prod_nhds {p : X -> Prop}
 {q : Y -> Prop} {x : X} {y : Y} (hx : forallᶠ x in 𝓝 x, p x) (hy : forallᶠ y in
 𝓝 y, q y) : fora…
· 使用定理 `gt_mem_nhds`：∀ {α : Type u} [ts : TopologicalSpace α] [inst : Preorder α
] [OrderTopology α] {a b : α},   b < a → ∀ᶠ (x : α) in nhds b, x < a
· 使用定理 `EReal.instOrderTopology`：OrderTopology EReal
· 使用定理 `EReal.bot_lt_coe`：bot_lt_coe (x : Real) : (⊥ : EReal) < x
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `EReal.add_lt_add`：add_lt_add {x y z t : EReal} (h1 : x < y) (h2 : z < t)
 : x + z < y + t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem continuousAt_add_bot_bot : ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (⊥, ⊥) := by
  simp only [ContinuousAt, tendsto_nhds_bot_iff_real, bot_add]
  refine fun r ↦ ((gt_mem_nhds (bot_lt_coe 0)).prod_nhds
    (gt_mem_nhds <| bot_lt_coe r)).mono fun _ h ↦ ?_
  simpa only [coe_zero, zero_add] using add_lt_add h.1 h.2

/-- The addition on `EReal` is continuous except where it doesn't make sense (i.e., at `(⊥, ⊤)`
and at `(⊤, ⊥)`). -/
/-
**EReal.continuousAt_add** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：continuousAt_add {p : EReal × EReal} (h : p.1 != ⊤ ∨ p.2 != ⊥) (h' : p.1 !
= ⊥ ∨ p.2 != ⊤) : ContinuousAt (fun p : EReal × EReal => p.1 + p.2) p
参数：h : p.1 != ⊤ ∨ p.2 != ⊥；h' : p.1 != ⊥ ∨ p.2 != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EReal.continuousAt_add_bot_bot`：continuousAt_add_bot_bot : ContinuousAt 
(fun p : EReal × EReal => p.1 + p.2) (⊥, ⊥)
· 使用定理 `EReal.continuousAt_add_bot_coe`：continuousAt_add_bot_coe (a : Real) : Co
ntinuousAt (fun p : EReal × EReal => p.1 + p.2) (⊥, a)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `EReal.continuousAt_add_coe_bot`：continuousAt_add_coe_bot (a : Real) : Co
ntinuousAt (fun p : EReal × EReal => p.1 + p.2) (a, ⊥)
· 使用定理 `EReal.continuousAt_add_coe_coe`：continuousAt_add_coe_coe (a b : Real) : 
ContinuousAt (fun p : EReal × EReal => p.1 + p.2) (a, b)
· 使用定理 `EReal.continuousAt_add_coe_top`：continuousAt_add_coe_top (a : Real) : Co
ntinuousAt (fun p : EReal × EReal => p.1 + p.2) (a, ⊤)
· 使用定理 `EReal.continuousAt_add_top_coe`：continuousAt_add_top_coe (a : Real) : Co
ntinuousAt (fun p : EReal × EReal => p.1 + p.2) (⊤, a)
· 使用定理 `EReal.continuousAt_add_top_top`：continuousAt_add_top_top : ContinuousAt 
(fun p : EReal × EReal => p.1 + p.2) (⊤, ⊤)

--- 原说明 ---
The addition on `EReal` is continuous except where it doesn't make sense (i.e., 
at `(⊥, ⊤)`
and at `(⊤, ⊥)`).
-/
theorem continuousAt_add {p : EReal × EReal} (h : p.1 ≠ ⊤ ∨ p.2 ≠ ⊥) (h' : p.1 ≠ ⊥ ∨ p.2 ≠ ⊤) :
    ContinuousAt (fun p : EReal × EReal => p.1 + p.2) p := by
  rcases p with ⟨x, y⟩
  induction x <;> induction y
  · exact continuousAt_add_bot_bot
  · exact continuousAt_add_bot_coe _
  · simp at h'
  · exact continuousAt_add_coe_bot _
  · exact continuousAt_add_coe_coe _ _
  · exact continuousAt_add_coe_top _
  · simp at h
  · exact continuousAt_add_top_coe _
  · exact continuousAt_add_top_top
/-
**EReal.lowerSemicontinuous_add** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
形式化陈述：lowerSemicontinuous_add : LowerSemicontinuous fun p : EReal × EReal => p.1
 + p.2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EReal.bot_add`：bot_add (x : EReal) : ⊥ + x = ⊥
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `EReal.add_bot`：add_bot (x : EReal) : x + ⊥ = ⊥
· 使用定理 `ContinuousAt.lowerSemicontinuousAt`：ContinuousAt.lowerSemicontinuousAt {
f : α -> γ} (h : ContinuousAt f x) : LowerSemicontinuousAt f x
· 使用定理 `EReal.instOrderTopology`：OrderTopology EReal
· 使用定理 `EReal.continuousAt_add`：continuousAt_add {p : EReal × EReal} (h : p.1 !=
 ⊤ ∨ p.2 != ⊥) (h' : p.1 != ⊥ ∨ p.2 != ⊤) : ContinuousAt (fun p : EReal × EReal 
=> p.1 + p.2…
-/
lemma lowerSemicontinuous_add : LowerSemicontinuous fun p : EReal × EReal ↦ p.1 + p.2 := by
  intro x y
  by_cases hx₁ : x.1 = ⊥
  · simp [hx₁]
  by_cases hx₂ : x.2 = ⊥
  · simp [hx₂]
  · exact continuousAt_add (.inr hx₂) (.inl hx₁) |>.lowerSemicontinuousAt _

/-! ### Continuity of multiplication -/

/- Outside of indeterminacies `(0, ±∞)` and `(±∞, 0)`, the multiplication on `EReal` is continuous.
There are many different cases to consider, so we first prove some special cases and leverage as
much as possible the symmetries of the multiplication. -/

/-
**EReal.continuousAt_mul_swap** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Outside of indeterminacies `(0, ±∞)` and `(±∞, 0)`, the multiplication on `EReal
` is continuous.
There are many different cases to consider, so we first prove some special cases
 and leverage as
much as possible the symmetries of the multiplication.
-/
private lemma continuousAt_mul_swap {a b : EReal}
    (h : ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (a, b)) :
    ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (b, a) := by
  convert! h.comp continuous_swap.continuousAt (x := (b, a))
  simp [mul_comm]
/-
**EReal.continuousAt_mul_symm1** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma continuousAt_mul_symm1 {a b : EReal}
    (h : ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (a, b)) :
    ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (-a, b) := by
  have : (fun p : EReal × EReal ↦ p.1 * p.2) = (fun x : EReal ↦ -x)
      ∘ (fun p : EReal × EReal ↦ p.1 * p.2) ∘ (fun p : EReal × EReal ↦ (-p.1, p.2)) := by
    ext p
    simp
  rw [this]
  apply ContinuousAt.comp (Continuous.continuousAt continuous_neg)
    <| ContinuousAt.comp _ (ContinuousAt.prodMap (Continuous.continuousAt continuous_neg)
      (Continuous.continuousAt continuous_id))
  simp [h]
/-
**EReal.continuousAt_mul_symm2** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma continuousAt_mul_symm2 {a b : EReal}
    (h : ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (a, b)) :
    ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (a, -b) :=
  continuousAt_mul_swap (continuousAt_mul_symm1 (continuousAt_mul_swap h))
/-
**EReal.continuousAt_mul_symm3** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma continuousAt_mul_symm3 {a b : EReal}
    (h : ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (a, b)) :
    ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (-a, -b) :=
  continuousAt_mul_symm1 (continuousAt_mul_symm2 h)
/-
**EReal.continuousAt_mul_coe_coe** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma continuousAt_mul_coe_coe (a b : ℝ) :
    ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (a, b) := by
  simp [ContinuousAt, EReal.nhds_coe_coe, ← EReal.coe_mul, Filter.tendsto_map'_iff,
    Function.comp_def, EReal.tendsto_coe, tendsto_mul]
/-
**EReal.continuousAt_mul_top_top** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma continuousAt_mul_top_top :
    ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (⊤, ⊤) := by
  simp only [ContinuousAt, EReal.top_mul_top, EReal.tendsto_nhds_top_iff_real]
  intro x
  rw [_root_.eventually_nhds_iff]
  use (Set.Ioi ((max x 0) : EReal)) ×ˢ (Set.Ioi 1)
  split_ands
  · intro p p_in_prod
    simp only [Set.mem_prod, Set.mem_Ioi, max_lt_iff] at p_in_prod
    rcases p_in_prod with ⟨⟨p1_gt_x, p1_pos⟩, p2_gt_1⟩
    have := mul_le_mul_of_nonneg_left (le_of_lt p2_gt_1) (le_of_lt p1_pos)
    rw [mul_one p.1] at this
    exact lt_of_lt_of_le p1_gt_x this
  · exact IsOpen.prod isOpen_Ioi isOpen_Ioi
  · simp
  · rw [Set.mem_Ioi, ← EReal.coe_one]; exact EReal.coe_lt_top 1
/-
**EReal.continuousAt_mul_top_pos** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma continuousAt_mul_top_pos {a : ℝ} (h : 0 < a) :
    ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (⊤, a) := by
  simp only [ContinuousAt, EReal.top_mul_coe_of_pos h, EReal.tendsto_nhds_top_iff_real]
  intro x
  rw [_root_.eventually_nhds_iff]
  use (Set.Ioi ((2 * (max (x + 1) 0) / a : ℝ) : EReal)) ×ˢ (Set.Ioi ((a / 2 : ℝ) : EReal))
  split_ands
  · intro p p_in_prod
    simp only [Set.mem_prod, Set.mem_Ioi] at p_in_prod
    rcases p_in_prod with ⟨p1_gt, p2_gt⟩
    have p1_pos : 0 < p.1 := by
      apply lt_of_le_of_lt _ p1_gt
      rw [EReal.coe_nonneg]
      apply mul_nonneg _ (le_of_lt (inv_pos_of_pos h))
      simp only [Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, le_max_iff, le_refl, or_true]
    have a2_pos : 0 < ((a / 2 : ℝ) : EReal) := by rw [EReal.coe_pos]; linarith
    have lock := mul_le_mul_of_nonneg_right (le_of_lt p1_gt) (le_of_lt a2_pos)
    have key := mul_le_mul_of_nonneg_left (le_of_lt p2_gt) (le_of_lt p1_pos)
    replace lock := le_trans lock key
    apply lt_of_lt_of_le _ lock
    rw [← EReal.coe_mul, EReal.coe_lt_coe_iff, _root_.div_mul_div_comm, mul_comm,
      ← _root_.div_mul_div_comm, mul_div_right_comm]
    simp only [ne_eq, Ne.symm (ne_of_lt h), not_false_eq_true, _root_.div_self, OfNat.ofNat_ne_zero,
      one_mul, lt_max_iff, lt_add_iff_pos_right, zero_lt_one, true_or]
  · exact IsOpen.prod isOpen_Ioi isOpen_Ioi
  · simp
  · simp [h]
/-
**EReal.continuousAt_mul_top_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `EReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma continuousAt_mul_top_ne_zero {a : ℝ} (h : a ≠ 0) :
    ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) (⊤, a) := by
  rcases lt_or_gt_of_ne h with a_neg | a_pos
  · exact neg_neg a ▸ continuousAt_mul_symm2 (continuousAt_mul_top_pos (neg_pos.2 a_neg))
  · exact continuousAt_mul_top_pos a_pos

/-- The multiplication on `EReal` is continuous except at indeterminacies
(i.e. whenever one value is zero and the other infinite). -/
/-
**EReal.continuousAt_mul** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：continuousAt_mul {p : EReal × EReal} (h₁ : p.1 != 0 ∨ p.2 != ⊥) (h₂ : p.1 
!= 0 ∨ p.2 != ⊤) (h₃ : p.1 != ⊥ ∨ p.2 != 0) (h₄ : p.1 != ⊤ ∨ p.2 != 0) : Continu
ousAt (fun p : EReal × EReal => p.1 * p.2) p
参数：h₁ : p.1 != 0 ∨ p.2 != ⊥；h₂ : p.1 != 0 ∨ p.2 != ⊤；h₃ : p.1 != ⊥ ∨ p.2 != 0；h₄
 : p.1 != ⊤ ∨ p.2 != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Topology.Instances.EReal.Lemmas.0.EReal.continuousAt_mu
l_symm3`：∀ {a b : EReal}, ContinuousAt (fun p => p.1 * p.2) (a, b) → ContinuousA
t (fun p => p.1 * p.2) (-a, -b)
· 使用定理 `_private.Mathlib.Topology.Instances.EReal.Lemmas.0.EReal.continuousAt_mu
l_top_top`：ContinuousAt (fun p => p.1 * p.2) (⊤, ⊤)
· 使用定理 `_private.Mathlib.Topology.Instances.EReal.Lemmas.0.EReal.continuousAt_mu
l_symm1`：∀ {a b : EReal}, ContinuousAt (fun p => p.1 * p.2) (a, b) → ContinuousA
t (fun p => p.1 * p.2) (-a, b)
· 使用定理 `_private.Mathlib.Topology.Instances.EReal.Lemmas.0.EReal.continuousAt_mu
l_top_ne_zero`：∀ {a : ℝ}, a ≠ 0 → ContinuousAt (fun p => p.1 * p.2) (⊤, ↑a)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `EReal.neg_top`：neg_top : -(⊤ : EReal) = ⊥
· 使用定理 `_private.Mathlib.Topology.Instances.EReal.Lemmas.0.EReal.continuousAt_mu
l_symm2`：∀ {a b : EReal}, ContinuousAt (fun p => p.1 * p.2) (a, b) → ContinuousA
t (fun p => p.1 * p.2) (a, -b)
· 使用定理 `_private.Mathlib.Topology.Instances.EReal.Lemmas.0.EReal.continuousAt_mu
l_swap`：∀ {a b : EReal}, ContinuousAt (fun p => p.1 * p.2) (a, b) → ContinuousAt
 (fun p => p.1 * p.2) (b, a)
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `_private.Mathlib.Topology.Instances.EReal.Lemmas.0.EReal.continuousAt_mu
l_coe_coe`：∀ (a b : ℝ), ContinuousAt (fun p => p.1 * p.2) (↑a, ↑b)

--- 原说明 ---
The multiplication on `EReal` is continuous except at indeterminacies
(i.e. whenever one value is zero and the other infinite).
-/
theorem continuousAt_mul {p : EReal × EReal} (h₁ : p.1 ≠ 0 ∨ p.2 ≠ ⊥)
    (h₂ : p.1 ≠ 0 ∨ p.2 ≠ ⊤) (h₃ : p.1 ≠ ⊥ ∨ p.2 ≠ 0) (h₄ : p.1 ≠ ⊤ ∨ p.2 ≠ 0) :
    ContinuousAt (fun p : EReal × EReal ↦ p.1 * p.2) p := by
  rcases p with ⟨x, y⟩
  induction x <;> induction y
  · exact continuousAt_mul_symm3 continuousAt_mul_top_top
  · simp only [ne_eq, not_true_eq_false, EReal.coe_eq_zero, false_or] at h₃
    exact continuousAt_mul_symm1 (continuousAt_mul_top_ne_zero h₃)
  · exact EReal.neg_top ▸ continuousAt_mul_symm1 continuousAt_mul_top_top
  · simp only [ne_eq, EReal.coe_eq_zero, not_true_eq_false, or_false] at h₁
    exact continuousAt_mul_symm2 (continuousAt_mul_swap (continuousAt_mul_top_ne_zero h₁))
  · exact continuousAt_mul_coe_coe _ _
  · simp only [ne_eq, EReal.coe_eq_zero, not_true_eq_false, or_false] at h₂
    exact continuousAt_mul_swap (continuousAt_mul_top_ne_zero h₂)
  · exact continuousAt_mul_symm2 continuousAt_mul_top_top
  · simp only [ne_eq, not_true_eq_false, EReal.coe_eq_zero, false_or] at h₄
    exact continuousAt_mul_top_ne_zero h₄
  · exact continuousAt_mul_top_top

variable {a b : EReal}
/-
**EReal.tendsto_mul** 是 Mathlib 中的一个定理，位于命名空间 `EReal`。
形式化陈述：∀ {a b : EReal},   a ≠ 0 ∨ b ≠ ⊥ →     a ≠ 0 ∨ b ≠ ⊤ → a ≠ ⊥ ∨ b ≠ 0 → a ≠
 ⊤ ∨ b ≠ 0 → Filter.Tendsto (fun p => p.1 * p.2) (nhds (a, b)) (nhds (a * b))
参数：fun p => p.1 * p.2；nhds (a, b)；nhds (a * b)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `EReal.continuousAt_mul`：continuousAt_mul {p : EReal × EReal} (h₁ : p.1 !
= 0 ∨ p.2 != ⊥) (h₂ : p.1 != 0 ∨ p.2 != ⊤) (h₃ : p.1 != ⊥ ∨ p.2 != 0) (h₄ : p.1 
!= ⊤ ∨ p.2 !…
-/
protected theorem tendsto_mul (h₁ : a ≠ 0 ∨ b ≠ ⊥) (h₂ : a ≠ 0 ∨ b ≠ ⊤) (h₃ : a ≠ ⊥ ∨ b ≠ 0)
    (h₄ : a ≠ ⊤ ∨ b ≠ 0) :
    Tendsto (fun p : EReal × EReal ↦ p.1 * p.2) (𝓝 (a, b)) (𝓝 (a * b)) :=
  (continuousAt_mul h₁ h₂ h₃ h₄).tendsto
/-
**EReal.Tendsto.mul** 是 Mathlib 中的一个定理，位于命名空间 `EReal.Tendsto`。
形式化陈述：∀ {α : Type u_2} {f : Filter α} {ma mb : α → EReal} {a b : EReal},   Filte
r.Tendsto ma f (nhds a) →     Filter.Tendsto mb f (nhds b) →       a ≠ 0 ∨ b ≠ ⊥
 →         a ≠ 0 ∨ b ≠ ⊤ → a ≠ ⊥ ∨ b ≠ 0 → a ≠ ⊤ ∨ b ≠ 0 → Filter.Tendsto (fun x
 => ma x * mb x) f (nhds (a * b))
参数：nhds a；nhds b；fun x => ma x * mb x；nhds (a * b)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `EReal.tendsto_mul`：∀ {a b : EReal},   a ≠ 0 ∨ b ≠ ⊥ →     a ≠ 0 ∨ b ≠ ⊤ 
→ a ≠ ⊥ ∨ b ≠ 0 → a ≠ ⊤ ∨ b ≠ 0 → Filter.Tendsto (fun p => p.1 * p.2) (nhds (a, 
b)) (nh…
· 使用定理 `Filter.Tendsto.prodMk_nhds`：Filter.Tendsto.prodMk_nhds {γ} {x : X} {y : 
Y} {f : Filter γ} {mx : γ -> X} {my : γ -> Y} (hx : Tendsto mx f (𝓝 x)) (hy : Te
ndsto my f (𝓝 y)…
-/
protected theorem Tendsto.mul {f : Filter α} {ma : α → EReal} {mb : α → EReal} {a b : EReal}
    (hma : Tendsto ma f (𝓝 a)) (hmb : Tendsto mb f (𝓝 b)) (h₁ : a ≠ 0 ∨ b ≠ ⊥)
    (h₂ : a ≠ 0 ∨ b ≠ ⊤) (h₃ : a ≠ ⊥ ∨ b ≠ 0) (h₄ : a ≠ ⊤ ∨ b ≠ 0) :
    Tendsto (fun x ↦ ma x * mb x) f (𝓝 (a * b)) :=
  (EReal.tendsto_mul h₁ h₂ h₃ h₄).comp (hma.prodMk_nhds hmb)
/-
**EReal.Tendsto.const_mul** 是 Mathlib 中的一个定理，位于命名空间 `EReal.Tendsto`。
形式化陈述：∀ {α : Type u_2} {f : Filter α} {m : α → EReal} {a b : EReal},   Filter.Te
ndsto m f (nhds b) → a ≠ ⊥ ∨ b ≠ 0 → a ≠ ⊤ ∨ b ≠ 0 → Filter.Tendsto (fun b => a 
* m b) f (nhds (a * b))
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
· 使用定理 `EReal.Tendsto.mul`：∀ {α : Type u_2} {f : Filter α} {ma mb : α → EReal} {
a b : EReal},   Filter.Tendsto ma f (nhds a) →     Filter.Tendsto mb f (nhds b) 
→      …
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
protected theorem Tendsto.const_mul {f : Filter α} {m : α → EReal} {a b : EReal}
    (hm : Tendsto m f (𝓝 b)) (h₁ : a ≠ ⊥ ∨ b ≠ 0) (h₂ : a ≠ ⊤ ∨ b ≠ 0) :
    Tendsto (fun b ↦ a * m b) f (𝓝 (a * b)) :=
  by_cases (fun (this : a = 0) => by simp [this, tendsto_const_nhds])
    fun ha : a ≠ 0 => EReal.Tendsto.mul tendsto_const_nhds hm (Or.inl ha) (Or.inl ha) h₁ h₂
/-
**EReal.Tendsto.mul_const** 是 Mathlib 中的一个定理，位于命名空间 `EReal.Tendsto`。
形式化陈述：∀ {α : Type u_2} {f : Filter α} {m : α → EReal} {a b : EReal},   Filter.Te
ndsto m f (nhds a) → a ≠ 0 ∨ b ≠ ⊥ → a ≠ 0 ∨ b ≠ ⊤ → Filter.Tendsto (fun x => m 
x * b) f (nhds (a * b))
参数：nhds a；fun x => m x * b；nhds (a * b)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `EReal.Tendsto.const_mul`：∀ {α : Type u_2} {f : Filter α} {m : α → EReal}
 {a b : EReal},   Filter.Tendsto m f (nhds b) → a ≠ ⊥ ∨ b ≠ 0 → a ≠ ⊤ ∨ b ≠ 0 → 
Filter.Tendst…
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
-/
protected theorem Tendsto.mul_const {f : Filter α} {m : α → EReal} {a b : EReal}
    (hm : Tendsto m f (𝓝 a)) (h₁ : a ≠ 0 ∨ b ≠ ⊥) (h₂ : a ≠ 0 ∨ b ≠ ⊤) :
    Tendsto (fun x ↦ m x * b) f (𝓝 (a * b)) := by
  simpa only [mul_comm] using EReal.Tendsto.const_mul hm h₁.symm h₂.symm

end EReal

