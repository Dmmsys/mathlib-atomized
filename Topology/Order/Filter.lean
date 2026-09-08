/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Filter
public import Mathlib.Topology.Order.Basic

/-!
# Topology on filters of a space with order topology

In this file we prove that `𝓝 (f x)` tends to `𝓝 Filter.atTop` provided that `f` tends to
`Filter.atTop`, and similarly for `Filter.atBot`.
-/

public section


open Topology

namespace Filter

variable {α X : Type*} [TopologicalSpace X] [PartialOrder X] [OrderTopology X]

/-
**Filter.tendsto_nhds_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {X : Type u_2} [inst : TopologicalSpace X] [inst_1 : PartialOrder X] [Or
derTopology X] [NoMaxOrder X],   Filter.Tendsto nhds Filter.atTop (nhds Filter.a
tTop)
参数：nhds Filter.atTop。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_nhds_atTop_iff`：∀ {α : Type u_2} {β : Type u_3} [inst : P
reorder β] {l : Filter α} {f : α → Filter β},   Filter.Tendsto f l (nhds Filter.
atTop) ↔ ∀ (y : β),…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `le_mem_nhds`：le_mem_nhds [OrderTopology α] {a b : α} (h : a < b) : foral
lᶠ x in 𝓝 b, a <= x
-/
protected theorem tendsto_nhds_atTop [NoMaxOrder X] : Tendsto 𝓝 (atTop : Filter X) (𝓝 atTop) :=
  Filter.tendsto_nhds_atTop_iff.2 fun x => (eventually_gt_atTop x).mono fun _ => le_mem_nhds
/-
**Filter.tendsto_nhds_atBot** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {X : Type u_2} [inst : TopologicalSpace X] [inst_1 : PartialOrder X] [Or
derTopology X] [NoMinOrder X],   Filter.Tendsto nhds Filter.atBot (nhds Filter.a
tBot)
参数：nhds Filter.atBot。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_nhds_atTop`：∀ {X : Type u_2} [inst : TopologicalSpace X] 
[inst_1 : PartialOrder X] [OrderTopology X] [NoMaxOrder X],   Filter.Tendsto nhd
s Filter.atTop …
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `OrderDual.noMaxOrder`：∀ {α : Type u_1} [inst : LT α] [NoMinOrder α], NoM
axOrder αᵒᵈ
-/
protected theorem tendsto_nhds_atBot [NoMinOrder X] : Tendsto 𝓝 (atBot : Filter X) (𝓝 atBot) :=
  @Filter.tendsto_nhds_atTop Xᵒᵈ _ _ _ _
/-
**Filter.Tendsto.nhds_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {X : Type u_2} [inst : TopologicalSpace X] [inst_1 : Part
ialOrder X] [OrderTopology X] [NoMaxOrder X]   {f : α → X} {l : Filter α}, Filte
r.Tendsto f l Filter.atTop → Filter.Tendsto (nhds ∘ f) l (nhds Filter.atTop)
参数：nhds ∘ f；nhds Filter.atTop。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.tendsto_nhds_atTop`：∀ {X : Type u_2} [inst : TopologicalSpace X] 
[inst_1 : PartialOrder X] [OrderTopology X] [NoMaxOrder X],   Filter.Tendsto nhd
s Filter.atTop …
-/
theorem Tendsto.nhds_atTop [NoMaxOrder X] {f : α → X} {l : Filter α} (h : Tendsto f l atTop) :
    Tendsto (𝓝 ∘ f) l (𝓝 atTop) :=
  Filter.tendsto_nhds_atTop.comp h
/-
**Filter.Tendsto.nhds_atBot** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {X : Type u_2} [inst : TopologicalSpace X] [inst_1 : Part
ialOrder X] [OrderTopology X] [NoMinOrder X]   {f : α → X} {l : Filter α}, Filte
r.Tendsto f l Filter.atBot → Filter.Tendsto (nhds ∘ f) l (nhds Filter.atBot)
参数：nhds ∘ f；nhds Filter.atBot。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.nhds_atTop`：∀ {α : Type u_1} {X : Type u_2} [inst : Topol
ogicalSpace X] [inst_1 : PartialOrder X] [OrderTopology X] [NoMaxOrder X]   {f :
 α → X} {l : Fi…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `OrderDual.noMaxOrder`：∀ {α : Type u_1} [inst : LT α] [NoMinOrder α], NoM
axOrder αᵒᵈ
-/
theorem Tendsto.nhds_atBot [NoMinOrder X] {f : α → X} {l : Filter α} (h : Tendsto f l atBot) :
    Tendsto (𝓝 ∘ f) l (𝓝 atBot) :=
  @Tendsto.nhds_atTop α Xᵒᵈ _ _ _ _ _ _ h

end Filter

