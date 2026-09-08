/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
module

public import Mathlib.Order.Filter.CountableInter
public import Mathlib.Topology.Order.LeftRightNhds

/-!
# Properties of LUB and GLB in an order topology
-/

public section

open Set Filter TopologicalSpace Topology Function

open OrderDual (toDual ofDual)

variable {α γ : Type*}

section OrderTopology

variable [TopologicalSpace α] [LinearOrder α] [OrderTopology α]

/-
**IsLUB.frequently_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLUB.frequently_mem {a : α} {s : Set α} (ha : IsLUB s a) (hs : s.Nonempty
) : existsᶠ x in 𝓝[<=] a, x in s
参数：ha : IsLUB s a；hs : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.Eventually.self_of_nhdsWithin`：Filter.Eventually.self_of_nhdsWith
in {p : α -> Prop} {s : Set α} {x : α} (h : forallᶠ y in 𝓝[s] x, p y) (hx : x in
 s) : p x
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhdsLE_iff_exists_Ioc_subset'`：mem_nhdsLE_iff_exists_Ioc_subset' {a 
l' : α} {s : Set α} (hl' : l' < a) : s in 𝓝[<=] a ↔ exists l in Iio a, Ioc l a s
ubseteq s
· 使用定理 `IsLUB.exists_between`：IsLUB.exists_between (h : IsLUB s a) (hb : b < a) 
: exists c in s, b < c ∧ c <= a
-/
theorem IsLUB.frequently_mem {a : α} {s : Set α} (ha : IsLUB s a) (hs : s.Nonempty) :
    ∃ᶠ x in 𝓝[≤] a, x ∈ s := by
  rcases hs with ⟨a', ha'⟩
  intro h
  rcases (ha.1 ha').eq_or_lt with (rfl | ha'a)
  · exact h.self_of_nhdsWithin le_rfl ha'
  · rcases (mem_nhdsLE_iff_exists_Ioc_subset' ha'a).1 h with ⟨b, hba, hb⟩
    rcases ha.exists_between hba with ⟨b', hb's, hb'⟩
    exact hb hb' hb's
/-
**IsLUB.frequently_nhds_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLUB.frequently_nhds_mem {a : α} {s : Set α} (ha : IsLUB s a) (hs : s.Non
empty) : existsᶠ x in 𝓝 a, x in s
参数：ha : IsLUB s a；hs : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Frequently.filter_mono`：∀ {α : Type u} {p : α → Prop} {f g : Filt
er α}, (∃ᶠ (x : α) in f, p x) → f ≤ g → ∃ᶠ (x : α) in g, p x
· 使用定理 `IsLUB.frequently_mem`：IsLUB.frequently_mem {a : α} {s : Set α} (ha : IsL
UB s a) (hs : s.Nonempty) : existsᶠ x in 𝓝[<=] a, x in s
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem IsLUB.frequently_nhds_mem {a : α} {s : Set α} (ha : IsLUB s a) (hs : s.Nonempty) :
    ∃ᶠ x in 𝓝 a, x ∈ s :=
  (ha.frequently_mem hs).filter_mono inf_le_left
/-
**IsGLB.frequently_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsGLB.frequently_mem {a : α} {s : Set α} (ha : IsGLB s a) (hs : s.Nonempty
) : existsᶠ x in 𝓝[>=] a, x in s
参数：ha : IsGLB s a；hs : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.frequently_mem`：IsLUB.frequently_mem {a : α} {s : Set α} (ha : IsL
UB s a) (hs : s.Nonempty) : existsᶠ x in 𝓝[<=] a, x in s
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
-/
theorem IsGLB.frequently_mem {a : α} {s : Set α} (ha : IsGLB s a) (hs : s.Nonempty) :
    ∃ᶠ x in 𝓝[≥] a, x ∈ s :=
  IsLUB.frequently_mem (α := αᵒᵈ) ha hs
/-
**IsGLB.frequently_nhds_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsGLB.frequently_nhds_mem {a : α} {s : Set α} (ha : IsGLB s a) (hs : s.Non
empty) : existsᶠ x in 𝓝 a, x in s
参数：ha : IsGLB s a；hs : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Frequently.filter_mono`：∀ {α : Type u} {p : α → Prop} {f g : Filt
er α}, (∃ᶠ (x : α) in f, p x) → f ≤ g → ∃ᶠ (x : α) in g, p x
· 使用定理 `IsGLB.frequently_mem`：IsGLB.frequently_mem {a : α} {s : Set α} (ha : IsG
LB s a) (hs : s.Nonempty) : existsᶠ x in 𝓝[>=] a, x in s
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem IsGLB.frequently_nhds_mem {a : α} {s : Set α} (ha : IsGLB s a) (hs : s.Nonempty) :
    ∃ᶠ x in 𝓝 a, x ∈ s :=
  (ha.frequently_mem hs).filter_mono inf_le_left
/-
**IsLUB.mem_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLUB.mem_closure {a : α} {s : Set α} (ha : IsLUB s a) (hs : s.Nonempty) :
 a in closure s
参数：ha : IsLUB s a；hs : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Frequently.mem_closure`：∀ {X : Type u} [inst : TopologicalSpace X
] {x : X} {s : Set X}, (∃ᶠ (x : X) in nhds x, x ∈ s) → x ∈ closure s
· 使用定理 `IsLUB.frequently_nhds_mem`：IsLUB.frequently_nhds_mem {a : α} {s : Set α}
 (ha : IsLUB s a) (hs : s.Nonempty) : existsᶠ x in 𝓝 a, x in s
-/
theorem IsLUB.mem_closure {a : α} {s : Set α} (ha : IsLUB s a) (hs : s.Nonempty) : a ∈ closure s :=
  (ha.frequently_nhds_mem hs).mem_closure
/-
**IsGLB.mem_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsGLB.mem_closure {a : α} {s : Set α} (ha : IsGLB s a) (hs : s.Nonempty) :
 a in closure s
参数：ha : IsGLB s a；hs : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Frequently.mem_closure`：∀ {X : Type u} [inst : TopologicalSpace X
] {x : X} {s : Set X}, (∃ᶠ (x : X) in nhds x, x ∈ s) → x ∈ closure s
· 使用定理 `IsGLB.frequently_nhds_mem`：IsGLB.frequently_nhds_mem {a : α} {s : Set α}
 (ha : IsGLB s a) (hs : s.Nonempty) : existsᶠ x in 𝓝 a, x in s
-/
theorem IsGLB.mem_closure {a : α} {s : Set α} (ha : IsGLB s a) (hs : s.Nonempty) : a ∈ closure s :=
  (ha.frequently_nhds_mem hs).mem_closure
/-
**IsLUB.nhdsWithin_neBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLUB.nhdsWithin_neBot {a : α} {s : Set α} (ha : IsLUB s a) (hs : s.Nonemp
ty) : NeBot (𝓝[s] a)
参数：ha : IsLUB s a；hs : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_closure_iff_nhdsWithin_neBot`：mem_closure_iff_nhdsWithin_neBot : x i
n closure s ↔ NeBot (𝓝[s] x)
· 使用定理 `IsLUB.mem_closure`：IsLUB.mem_closure {a : α} {s : Set α} (ha : IsLUB s a
) (hs : s.Nonempty) : a in closure s
-/
theorem IsLUB.nhdsWithin_neBot {a : α} {s : Set α} (ha : IsLUB s a) (hs : s.Nonempty) :
    NeBot (𝓝[s] a) :=
  mem_closure_iff_nhdsWithin_neBot.1 (ha.mem_closure hs)
/-
**IsGLB.nhdsWithin_neBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsGLB.nhdsWithin_neBot {a : α} {s : Set α} (ha : IsGLB s a) (hs : s.Nonemp
ty) : NeBot (𝓝[s] a)
参数：ha : IsGLB s a；hs : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.nhdsWithin_neBot`：IsLUB.nhdsWithin_neBot {a : α} {s : Set α} (ha :
 IsLUB s a) (hs : s.Nonempty) : NeBot (𝓝[s] a)
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
-/
theorem IsGLB.nhdsWithin_neBot {a : α} {s : Set α} (ha : IsGLB s a) (hs : s.Nonempty) :
    NeBot (𝓝[s] a) :=
  IsLUB.nhdsWithin_neBot (α := αᵒᵈ) ha hs
/-
**isLUB_of_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLUB_of_mem_nhds {s : Set α} {a : α} {f : Filter α} (hsa : a in upperBoun
ds s) (hsf : s in f) [NeBot (f ⊓ 𝓝 a)] : IsLUB s a
参数：hsa : a in upperBounds s；hsf : s in f；f ⊓ 𝓝 a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Filter.inter_mem_inf`：inter_mem_inf {α : Type u} {f g : Filter α} {s t :
 Set α} (hs : s in f) (ht : t in g) : s inter t in f ⊓ g
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_lt'`：isOpen_lt' [OrderTopology α] (a : α) : IsOpen { b : α | a < 
b }
· 使用定理 `Filter.nonempty_of_mem`：nonempty_of_mem {f : Filter α} [hf : NeBot f] {s
 : Set α} (hs : s in f) : s.Nonempty
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
-/
theorem isLUB_of_mem_nhds {s : Set α} {a : α} {f : Filter α} (hsa : a ∈ upperBounds s) (hsf : s ∈ f)
    [NeBot (f ⊓ 𝓝 a)] : IsLUB s a :=
  ⟨hsa, fun b hb =>
    not_lt.1 fun hba =>
      have : s ∩ { a | b < a } ∈ f ⊓ 𝓝 a := inter_mem_inf hsf (IsOpen.mem_nhds (isOpen_lt' _) hba)
      let ⟨_x, ⟨hxs, hxb⟩⟩ := Filter.nonempty_of_mem this
      have : b < b := lt_of_lt_of_le hxb <| hb hxs
      lt_irrefl b this⟩
/-
**isLUB_of_mem_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLUB_of_mem_closure {s : Set α} {a : α} (hsa : a in upperBounds s) (hsf :
 a in closure s) : IsLUB s a
参数：hsa : a in upperBounds s；hsf : a in closure s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLUB_of_mem_nhds`：isLUB_of_mem_nhds {s : Set α} {a : α} {f : Filter α} 
(hsa : a in upperBounds s) (hsf : s in f) [NeBot (f ⊓ 𝓝 a)] : IsLUB s a
· 使用定理 `Filter.mem_principal_self`：mem_principal_self (s : Set α) : s in 𝓟 s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `ClusterPt.eq_1`：∀ {X : Type u_1} [inst : TopologicalSpace X] (x : X) (F 
: Filter X), ClusterPt x F = (nhds x ⊓ F).NeBot
· 使用定理 `mem_closure_iff_clusterPt`：mem_closure_iff_clusterPt : x in closure s ↔ 
ClusterPt x (𝓟 s)
-/
theorem isLUB_of_mem_closure {s : Set α} {a : α} (hsa : a ∈ upperBounds s) (hsf : a ∈ closure s) :
    IsLUB s a := by
  rw [mem_closure_iff_clusterPt, ClusterPt, inf_comm] at hsf
  exact isLUB_of_mem_nhds hsa (mem_principal_self s)

set_option backward.isDefEq.respectTransparency false in
/-
**isGLB_of_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isGLB_of_mem_nhds {s : Set α} {a : α} {f : Filter α} (hsa : a in lowerBoun
ds s) (hsf : s in f) [NeBot (f ⊓ 𝓝 a)] : IsGLB s a
参数：hsa : a in lowerBounds s；hsf : s in f；f ⊓ 𝓝 a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLUB_of_mem_nhds`：isLUB_of_mem_nhds {s : Set α} {a : α} {f : Filter α} 
(hsa : a in upperBounds s) (hsf : s in f) [NeBot (f ⊓ 𝓝 a)] : IsLUB s a
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
-/
theorem isGLB_of_mem_nhds {s : Set α} {a : α} {f : Filter α} (hsa : a ∈ lowerBounds s) (hsf : s ∈ f)
    [NeBot (f ⊓ 𝓝 a)] :
    IsGLB s a :=
  isLUB_of_mem_nhds (α := αᵒᵈ) hsa hsf
/-
**isGLB_of_mem_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isGLB_of_mem_closure {s : Set α} {a : α} (hsa : a in lowerBounds s) (hsf :
 a in closure s) : IsGLB s a
参数：hsa : a in lowerBounds s；hsf : a in closure s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLUB_of_mem_closure`：isLUB_of_mem_closure {s : Set α} {a : α} (hsa : a 
in upperBounds s) (hsf : a in closure s) : IsLUB s a
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
-/
theorem isGLB_of_mem_closure {s : Set α} {a : α} (hsa : a ∈ lowerBounds s) (hsf : a ∈ closure s) :
    IsGLB s a :=
  isLUB_of_mem_closure (α := αᵒᵈ) hsa hsf
/-
**IsLUB.mem_upperBounds_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLUB.mem_upperBounds_of_tendsto [Preorder γ] [TopologicalSpace γ] [OrderC
losedTopology γ] {f : α -> γ} {s : Set α} {a : α} {b : γ} (hf : MonotoneOn f s) 
(ha : IsLUB s a) (hb : Tendsto f (𝓝[s] a) (𝓝 b)) : b in upperBounds (f '' s)
参数：hf : MonotoneOn f s；ha : IsLUB s a；hb : Tendsto f (𝓝[s] a) (𝓝 b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.inter_Ici_of_mem`：IsLUB.inter_Ici_of_mem [LinearOrder γ] {s : Set 
γ} {a b : γ} (ha : IsLUB s a) (hb : b in s) : IsLUB (s inter Ici b) a
· 使用定理 `IsLUB.nhdsWithin_neBot`：IsLUB.nhdsWithin_neBot {a : α} {s : Set α} (ha :
 IsLUB s a) (hs : s.Nonempty) : NeBot (𝓝[s] a)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `ge_of_tendsto`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] [
inst_1 : Preorder α] [ClosedIciTopology α] {f : β → α}   {a b : α} {x : Filter β
} […
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsLUB.mem_upperBounds_of_tendsto [Preorder γ] [TopologicalSpace γ] [OrderClosedTopology γ]
    {f : α → γ} {s : Set α} {a : α} {b : γ} (hf : MonotoneOn f s) (ha : IsLUB s a)
    (hb : Tendsto f (𝓝[s] a) (𝓝 b)) : b ∈ upperBounds (f '' s) := by
  rintro _ ⟨x, hx, rfl⟩
  replace ha := ha.inter_Ici_of_mem hx
  have := ha.nhdsWithin_neBot ⟨x, hx, le_rfl⟩
  refine ge_of_tendsto (hb.mono_left (nhdsWithin_mono a (inter_subset_left (t := Ici x)))) ?_
  exact mem_of_superset self_mem_nhdsWithin fun y hy => hf hx hy.1 hy.2

-- For a version of this theorem in which the convergence considered on the domain `α` is as `x : α`
-- tends to infinity, rather than tending to a point `x` in `α`, see `isLUB_of_tendsto_atTop`
/-
**IsLUB.isLUB_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLUB.isLUB_of_tendsto [Preorder γ] [TopologicalSpace γ] [OrderClosedTopol
ogy γ] {f : α -> γ} {s : Set α} {a : α} {b : γ} (hf : MonotoneOn f s) (ha : IsLU
B s a) (hs : s.Nonempty) (hb : Tendsto f (𝓝[s] a) (𝓝 b)) : IsLUB (f '' s) b
参数：hf : MonotoneOn f s；ha : IsLUB s a；hs : s.Nonempty；hb : Tendsto f (𝓝[s] a) (𝓝
 b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.mem_upperBounds_of_tendsto`：IsLUB.mem_upperBounds_of_tendsto [Preo
rder γ] [TopologicalSpace γ] [OrderClosedTopology γ] {f : α -> γ} {s : Set α} {a
 : α} {b : γ} (hf : Mo…
· 使用定理 `le_of_tendsto`：le_of_tendsto {x : Filter β} [hx : NeBot x] (lim : Tendst
o f x (𝓝 a)) (h : forallᶠ c in x, f c <= b) : a <= b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `IsLUB.nhdsWithin_neBot`：IsLUB.nhdsWithin_neBot {a : α} {s : Set α} (ha :
 IsLUB s a) (hs : s.Nonempty) : NeBot (𝓝[s] a)
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
theorem IsLUB.isLUB_of_tendsto [Preorder γ] [TopologicalSpace γ] [OrderClosedTopology γ] {f : α → γ}
    {s : Set α} {a : α} {b : γ} (hf : MonotoneOn f s) (ha : IsLUB s a) (hs : s.Nonempty)
    (hb : Tendsto f (𝓝[s] a) (𝓝 b)) : IsLUB (f '' s) b :=
  haveI := ha.nhdsWithin_neBot hs
  ⟨ha.mem_upperBounds_of_tendsto hf hb, fun _b' hb' =>
    le_of_tendsto hb (mem_of_superset self_mem_nhdsWithin fun _ hx => hb' <| mem_image_of_mem _ hx)⟩
/-
**IsGLB.mem_lowerBounds_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsGLB.mem_lowerBounds_of_tendsto [Preorder γ] [TopologicalSpace γ] [OrderC
losedTopology γ] {f : α -> γ} {s : Set α} {a : α} {b : γ} (hf : MonotoneOn f s) 
(ha : IsGLB s a) (hb : Tendsto f (𝓝[s] a) (𝓝 b)) : b in lowerBounds (f '' s)
参数：hf : MonotoneOn f s；ha : IsGLB s a；hb : Tendsto f (𝓝[s] a) (𝓝 b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.mem_upperBounds_of_tendsto`：IsLUB.mem_upperBounds_of_tendsto [Preo
rder γ] [TopologicalSpace γ] [OrderClosedTopology γ] {f : α -> γ} {s : Set α} {a
 : α} {b : γ} (hf : Mo…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `instOrderClosedTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpac
e α] [inst_1 : Preorder α] [t : OrderClosedTopology α], OrderClosedTopology αᵒᵈ
· 使用定理 `MonotoneOn.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1
 : Preorder β] {f : α → β} {s : Set α},   MonotoneOn f s → MonotoneOn (⇑OrderDua
l.toD…
-/
theorem IsGLB.mem_lowerBounds_of_tendsto [Preorder γ] [TopologicalSpace γ] [OrderClosedTopology γ]
    {f : α → γ} {s : Set α} {a : α} {b : γ} (hf : MonotoneOn f s) (ha : IsGLB s a)
    (hb : Tendsto f (𝓝[s] a) (𝓝 b)) : b ∈ lowerBounds (f '' s) :=
  IsLUB.mem_upperBounds_of_tendsto (α := αᵒᵈ) (γ := γᵒᵈ) hf.dual ha hb

-- For a version of this theorem in which the convergence considered on the domain `α` is as
-- `x : α` tends to negative infinity, rather than tending to a point `x` in `α`, see
-- `isGLB_of_tendsto_atBot`
@[to_dual existing]
/-
**IsGLB.isGLB_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsGLB.isGLB_of_tendsto [Preorder γ] [TopologicalSpace γ] [OrderClosedTopol
ogy γ] {f : α -> γ} {s : Set α} {a : α} {b : γ} (hf : MonotoneOn f s) : IsGLB s 
a -> s.Nonempty -> Tendsto f (𝓝[s] a) (𝓝 b) -> IsGLB (f '' s) b
参数：hf : MonotoneOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.isLUB_of_tendsto`：IsLUB.isLUB_of_tendsto [Preorder γ] [Topological
Space γ] [OrderClosedTopology γ] {f : α -> γ} {s : Set α} {a : α} {b : γ} (hf : 
MonotoneOn f…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `instOrderClosedTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpac
e α] [inst_1 : Preorder α] [t : OrderClosedTopology α], OrderClosedTopology αᵒᵈ
· 使用定理 `MonotoneOn.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1
 : Preorder β] {f : α → β} {s : Set α},   MonotoneOn f s → MonotoneOn (⇑OrderDua
l.toD…
-/
theorem IsGLB.isGLB_of_tendsto [Preorder γ] [TopologicalSpace γ] [OrderClosedTopology γ] {f : α → γ}
    {s : Set α} {a : α} {b : γ} (hf : MonotoneOn f s) :
    IsGLB s a → s.Nonempty → Tendsto f (𝓝[s] a) (𝓝 b) → IsGLB (f '' s) b :=
  IsLUB.isLUB_of_tendsto (α := αᵒᵈ) (γ := γᵒᵈ) hf.dual
/-
**IsLUB.mem_lowerBounds_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLUB.mem_lowerBounds_of_tendsto [Preorder γ] [TopologicalSpace γ] [OrderC
losedTopology γ] {f : α -> γ} {s : Set α} {a : α} {b : γ} (hf : AntitoneOn f s) 
(ha : IsLUB s a) (hb : Tendsto f (𝓝[s] a) (𝓝 b)) : b in lowerBounds (f '' s)
参数：hf : AntitoneOn f s；ha : IsLUB s a；hb : Tendsto f (𝓝[s] a) (𝓝 b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.mem_upperBounds_of_tendsto`：IsLUB.mem_upperBounds_of_tendsto [Preo
rder γ] [TopologicalSpace γ] [OrderClosedTopology γ] {f : α -> γ} {s : Set α} {a
 : α} {b : γ} (hf : Mo…
· 使用定理 `instOrderClosedTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpac
e α] [inst_1 : Preorder α] [t : OrderClosedTopology α], OrderClosedTopology αᵒᵈ
-/
theorem IsLUB.mem_lowerBounds_of_tendsto [Preorder γ] [TopologicalSpace γ] [OrderClosedTopology γ]
    {f : α → γ} {s : Set α} {a : α} {b : γ} (hf : AntitoneOn f s) (ha : IsLUB s a)
    (hb : Tendsto f (𝓝[s] a) (𝓝 b)) : b ∈ lowerBounds (f '' s) :=
  IsLUB.mem_upperBounds_of_tendsto (γ := γᵒᵈ) hf ha hb
/-
**IsLUB.isGLB_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLUB.isGLB_of_tendsto [Preorder γ] [TopologicalSpace γ] [OrderClosedTopol
ogy γ] {f : α -> γ} {s : Set α} {a : α} {b : γ} (hf : AntitoneOn f s) (ha : IsLU
B s a) (hs : s.Nonempty) (hb : Tendsto f (𝓝[s] a) (𝓝 b)) : IsGLB (f '' s) b
参数：hf : AntitoneOn f s；ha : IsLUB s a；hs : s.Nonempty；hb : Tendsto f (𝓝[s] a) (𝓝
 b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.isLUB_of_tendsto`：IsLUB.isLUB_of_tendsto [Preorder γ] [Topological
Space γ] [OrderClosedTopology γ] {f : α -> γ} {s : Set α} {a : α} {b : γ} (hf : 
MonotoneOn f…
· 使用定理 `instOrderClosedTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpac
e α] [inst_1 : Preorder α] [t : OrderClosedTopology α], OrderClosedTopology αᵒᵈ
-/
theorem IsLUB.isGLB_of_tendsto [Preorder γ] [TopologicalSpace γ] [OrderClosedTopology γ] {f : α → γ}
    {s : Set α} {a : α} {b : γ} (hf : AntitoneOn f s) (ha : IsLUB s a) (hs : s.Nonempty)
    (hb : Tendsto f (𝓝[s] a) (𝓝 b)) : IsGLB (f '' s) b :=
  IsLUB.isLUB_of_tendsto (γ := γᵒᵈ) hf ha hs hb
/-
**IsGLB.mem_upperBounds_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsGLB.mem_upperBounds_of_tendsto [Preorder γ] [TopologicalSpace γ] [OrderC
losedTopology γ] {f : α -> γ} {s : Set α} {a : α} {b : γ} (hf : AntitoneOn f s) 
(ha : IsGLB s a) (hb : Tendsto f (𝓝[s] a) (𝓝 b)) : b in upperBounds (f '' s)
参数：hf : AntitoneOn f s；ha : IsGLB s a；hb : Tendsto f (𝓝[s] a) (𝓝 b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGLB.mem_lowerBounds_of_tendsto`：IsGLB.mem_lowerBounds_of_tendsto [Preo
rder γ] [TopologicalSpace γ] [OrderClosedTopology γ] {f : α -> γ} {s : Set α} {a
 : α} {b : γ} (hf : Mo…
· 使用定理 `instOrderClosedTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpac
e α] [inst_1 : Preorder α] [t : OrderClosedTopology α], OrderClosedTopology αᵒᵈ
-/
theorem IsGLB.mem_upperBounds_of_tendsto [Preorder γ] [TopologicalSpace γ] [OrderClosedTopology γ]
    {f : α → γ} {s : Set α} {a : α} {b : γ} (hf : AntitoneOn f s) (ha : IsGLB s a)
    (hb : Tendsto f (𝓝[s] a) (𝓝 b)) : b ∈ upperBounds (f '' s) :=
  IsGLB.mem_lowerBounds_of_tendsto (γ := γᵒᵈ) hf ha hb
/-
**IsGLB.isLUB_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsGLB.isLUB_of_tendsto [Preorder γ] [TopologicalSpace γ] [OrderClosedTopol
ogy γ] {f : α -> γ} {s : Set α} {a : α} {b : γ} (hf : AntitoneOn f s) (ha : IsGL
B s a) (hs : s.Nonempty) (hb : Tendsto f (𝓝[s] a) (𝓝 b)) : IsLUB (f '' s) b
参数：hf : AntitoneOn f s；ha : IsGLB s a；hs : s.Nonempty；hb : Tendsto f (𝓝[s] a) (𝓝
 b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGLB.isGLB_of_tendsto`：IsGLB.isGLB_of_tendsto [Preorder γ] [Topological
Space γ] [OrderClosedTopology γ] {f : α -> γ} {s : Set α} {a : α} {b : γ} (hf : 
MonotoneOn f…
· 使用定理 `instOrderClosedTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpac
e α] [inst_1 : Preorder α] [t : OrderClosedTopology α], OrderClosedTopology αᵒᵈ
-/
theorem IsGLB.isLUB_of_tendsto [Preorder γ] [TopologicalSpace γ] [OrderClosedTopology γ] {f : α → γ}
    {s : Set α} {a : α} {b : γ} (hf : AntitoneOn f s) (ha : IsGLB s a) (hs : s.Nonempty)
    (hb : Tendsto f (𝓝[s] a) (𝓝 b)) : IsLUB (f '' s) b :=
  IsGLB.isGLB_of_tendsto (γ := γᵒᵈ) hf ha hs hb
/-
**IsLUB.mem_of_isClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLUB.mem_of_isClosed {a : α} {s : Set α} (ha : IsLUB s a) (hs : s.Nonempt
y) (sc : IsClosed s) : a in s
参数：ha : IsLUB s a；hs : s.Nonempty；sc : IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.closure_subset`：IsClosed.closure_subset (hs : IsClosed s) : clo
sure s subseteq s
· 使用定理 `IsLUB.mem_closure`：IsLUB.mem_closure {a : α} {s : Set α} (ha : IsLUB s a
) (hs : s.Nonempty) : a in closure s
-/
theorem IsLUB.mem_of_isClosed {a : α} {s : Set α} (ha : IsLUB s a) (hs : s.Nonempty)
    (sc : IsClosed s) : a ∈ s :=
  sc.closure_subset <| ha.mem_closure hs

alias IsClosed.isLUB_mem := IsLUB.mem_of_isClosed
/-
**IsGLB.mem_of_isClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsGLB.mem_of_isClosed {a : α} {s : Set α} (ha : IsGLB s a) (hs : s.Nonempt
y) (sc : IsClosed s) : a in s
参数：ha : IsGLB s a；hs : s.Nonempty；sc : IsClosed s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.closure_subset`：IsClosed.closure_subset (hs : IsClosed s) : clo
sure s subseteq s
· 使用定理 `IsGLB.mem_closure`：IsGLB.mem_closure {a : α} {s : Set α} (ha : IsGLB s a
) (hs : s.Nonempty) : a in closure s
-/
theorem IsGLB.mem_of_isClosed {a : α} {s : Set α} (ha : IsGLB s a) (hs : s.Nonempty)
    (sc : IsClosed s) : a ∈ s :=
  sc.closure_subset <| ha.mem_closure hs

alias IsClosed.isGLB_mem := IsGLB.mem_of_isClosed
/-
**isLUB_iff_of_subset_of_subset_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLUB_iff_of_subset_of_subset_closure {α : Type*} [TopologicalSpace α] [Pr
eorder α] [ClosedIicTopology α] {s t : Set α} (hst : s subseteq t) (hts : t subs
eteq closure s) {x : α} : IsLUB s x ↔ IsLUB t x
参数：hst : s subseteq t；hts : t subseteq closure s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLUB_congr`：isLUB_congr (h : upperBounds s = upperBounds t) : IsLUB s a
 ↔ IsLUB t a
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `upperBounds_mono_set`：upperBounds_mono_set ⦃s t : Set α⦄ (hst : s subset
eq t) : upperBounds t subseteq upperBounds s
· 使用引理 `upperBounds_closure`：upperBounds_closure (s : Set α) : upperBounds (clos
ure s : Set α) = upperBounds s
-/
theorem isLUB_iff_of_subset_of_subset_closure {α : Type*} [TopologicalSpace α] [Preorder α]
    [ClosedIicTopology α] {s t : Set α} (hst : s ⊆ t) (hts : t ⊆ closure s) {x : α} :
    IsLUB s x ↔ IsLUB t x :=
  isLUB_congr <| (upperBounds_closure (s := s) ▸ upperBounds_mono_set hts).antisymm <|
    upperBounds_mono_set hst
/-
**isGLB_iff_of_subset_of_subset_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isGLB_iff_of_subset_of_subset_closure {α : Type*} [TopologicalSpace α] [Pr
eorder α] [ClosedIciTopology α] {s t : Set α} (hst : s subseteq t) (hts : t subs
eteq closure s) {x : α} : IsGLB s x ↔ IsGLB t x
参数：hst : s subseteq t；hts : t subseteq closure s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLUB_iff_of_subset_of_subset_closure`：isLUB_iff_of_subset_of_subset_clo
sure {α : Type*} [TopologicalSpace α] [Preorder α] [ClosedIicTopology α] {s t : 
Set α} (hst : s subseteq t)…
· 使用定理 `instClosedIicTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : Preorder α] [ClosedIciTopology α], ClosedIicTopology αᵒᵈ
-/
theorem isGLB_iff_of_subset_of_subset_closure {α : Type*} [TopologicalSpace α] [Preorder α]
    [ClosedIciTopology α] {s t : Set α} (hst : s ⊆ t) (hts : t ⊆ closure s) {x : α} :
    IsGLB s x ↔ IsGLB t x :=
  isLUB_iff_of_subset_of_subset_closure (α := αᵒᵈ) hst hts
/-
**Dense.isLUB_inter_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Dense.isLUB_inter_iff {α : Type*} [TopologicalSpace α] [Preorder α] [Close
dIicTopology α] {s t : Set α} (hs : Dense s) (ht : IsOpen t) {x : α} : IsLUB (t 
inter s) x ↔ IsLUB t x
参数：hs : Dense s；ht : IsOpen t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLUB_iff_of_subset_of_subset_closure`：isLUB_iff_of_subset_of_subset_clo
sure {α : Type*} [TopologicalSpace α] [Preorder α] [ClosedIicTopology α] {s t : 
Set α} (hst : s subseteq t)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Dense.open_subset_closure_inter`：Dense.open_subset_closure_inter (hs : D
ense s) (ht : IsOpen t) : t subseteq closure (t inter s)
-/
theorem Dense.isLUB_inter_iff {α : Type*} [TopologicalSpace α] [Preorder α] [ClosedIicTopology α]
    {s t : Set α} (hs : Dense s) (ht : IsOpen t) {x : α} :
    IsLUB (t ∩ s) x ↔ IsLUB t x :=
  isLUB_iff_of_subset_of_subset_closure (by simp) <| hs.open_subset_closure_inter ht
/-
**Dense.isGLB_inter_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Dense.isGLB_inter_iff {α : Type*} [TopologicalSpace α] [Preorder α] [Close
dIciTopology α] {s t : Set α} (hs : Dense s) (ht : IsOpen t) {x : α} : IsGLB (t 
inter s) x ↔ IsGLB t x
参数：hs : Dense s；ht : IsOpen t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dense.isLUB_inter_iff`：Dense.isLUB_inter_iff {α : Type*} [TopologicalSpa
ce α] [Preorder α] [ClosedIicTopology α] {s t : Set α} (hs : Dense s) (ht : IsOp
en t) {x : …
· 使用定理 `instClosedIicTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : Preorder α] [ClosedIciTopology α], ClosedIicTopology αᵒᵈ
-/
theorem Dense.isGLB_inter_iff {α : Type*} [TopologicalSpace α] [Preorder α] [ClosedIciTopology α]
    {s t : Set α} (hs : Dense s) (ht : IsOpen t) {x : α} :
    IsGLB (t ∩ s) x ↔ IsGLB t x :=
  hs.isLUB_inter_iff (α := αᵒᵈ) ht

/-- The upper bounds of the image of a continuous function on a dense set are equal to the upper
bounds of the range of the universe. -/
/-
**Dense.upperBounds_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Dense.upperBounds_image {α : Type*} [TopologicalSpace α] [Preorder α] [Clo
sedIicTopology α] {f : γ -> α} [TopologicalSpace γ] {S : Set γ} (hS : Dense S) (
hf : Continuous f) : upperBounds (f '' S) = upperBounds (range f)
参数：hS : Dense S；hf : Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Filter.Frequently.mem_of_closed`：Filter.Frequently.mem_of_closed (h : ex
istsᶠ x in 𝓝 x, x in s) (hs : IsClosed s) : x in s
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_closure_iff_frequently`：mem_closure_iff_frequently : x in closure s 
↔ existsᶠ x in 𝓝 x, x in s
· 使用定理 `isClosed_Iic`：isClosed_Iic : IsClosed (Iic a)
· 使用定理 `upperBounds_mono`：upperBounds_mono ⦃s t : Set α⦄ (hst : s subseteq t) ⦃a
 b⦄ (hab : a <= b) : a in upperBounds t -> b in upperBounds s
· 使用定理 `Continuous.range_subset_closure_image_dense`：Continuous.range_subset_clo
sure_image_dense {f : X -> Y} (hf : Continuous f) (hs : Dense s) : range f subse
teq closure (f '' s)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f

--- 原说明 ---
The upper bounds of the image of a continuous function on a dense set are equal 
to the upper
bounds of the range of the universe.
-/
theorem Dense.upperBounds_image {α : Type*} [TopologicalSpace α] [Preorder α]
    [ClosedIicTopology α] {f : γ → α} [TopologicalSpace γ] {S : Set γ} (hS : Dense S)
    (hf : Continuous f) :
    upperBounds (f '' S) = upperBounds (range f) := by
  refine subset_antisymm ?_ fun _ => upperBounds_mono (Set.image_subset_range f S) le_rfl
  refine subset_trans ?_ fun _ => upperBounds_mono (hf.range_subset_closure_image_dense hS) le_rfl
  intro x hx i hi
  rw [mem_closure_iff_frequently] at hi
  exact (hi.mono hx).mem_of_closed isClosed_Iic

/-- The lower bounds of the image of a continuous function on a dense set are equal to the lower
bounds of the range of the universe. -/
/-
**Dense.lowerBounds_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Dense.lowerBounds_image {α : Type*} [TopologicalSpace α] [Preorder α] [Clo
sedIciTopology α] {f : γ -> α} [TopologicalSpace γ] {S : Set γ} (hS : Dense S) (
hf : Continuous f) : lowerBounds (f '' S) = lowerBounds (range f)
参数：hS : Dense S；hf : Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dense.upperBounds_image`：Dense.upperBounds_image {α : Type*} [Topologica
lSpace α] [Preorder α] [ClosedIicTopology α] {f : γ -> α} [TopologicalSpace γ] {
S : Set γ} (h…
· 使用定理 `instClosedIicTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : Preorder α] [ClosedIciTopology α], ClosedIicTopology αᵒᵈ

--- 原说明 ---
The lower bounds of the image of a continuous function on a dense set are equal 
to the lower
bounds of the range of the universe.
-/
theorem Dense.lowerBounds_image {α : Type*} [TopologicalSpace α] [Preorder α]
    [ClosedIciTopology α] {f : γ → α} [TopologicalSpace γ] {S : Set γ} (hS : Dense S)
    (hf : Continuous f) :
    lowerBounds (f '' S) = lowerBounds (range f) :=
  hS.upperBounds_image (α := αᵒᵈ) hf

/-- The supremum of a bounded above, continuous function on a dense set is equal to the supremum on
the universe. -/
/-
**Dense.ciSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Dense.ciSup {α : Type*} [TopologicalSpace α] [ConditionallyCompleteLattice
 α] [ClosedIicTopology α] {f : γ -> α} [TopologicalSpace γ] {S : Set γ} (hS : De
nse S) (hf : Continuous f) (h : BddAbove (range f)) : ⨆ s : S, f s = ⨆ i, f i
参数：hS : Dense S；hf : Continuous f；h : BddAbove (range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sSup_range`：sSup_range : sSup (range f) = iSup f
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.range_eq_empty`：range_eq_empty [IsEmpty ι] (f : ι -> α) : range f = 
∅
· 使用定理 `instIsEmptySubtype`：∀ {α : Sort u} [IsEmpty α] (p : α → Prop), IsEmpty (
Subtype p)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsLUB.unique`：IsLUB.unique (Ha : IsLUB s a) (Hb : IsLUB s b) : a = b
· 使用定理 `isLUB_csSup`：isLUB_csSup (hn : s.Nonempty) (hb : BddAbove s
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isLUB_congr`：isLUB_congr (h : upperBounds s = upperBounds t) : IsLUB s a
 ↔ IsLUB t a
· 使用定理 `Dense.upperBounds_image`：Dense.upperBounds_image {α : Type*} [Topologica
lSpace α] [Preorder α] [ClosedIicTopology α] {f : γ -> α} [TopologicalSpace γ] {
S : Set γ} (h…
· 使用定理 `isLUB_ciSup_set`：isLUB_ciSup_set {f : β -> α} {s : Set β} (H : BddAbove 
(f '' s)) (Hne : s.Nonempty) : IsLUB (f '' s) (⨆ i : s, f i)
· 使用定理 `BddAbove.mono`：BddAbove.mono ⦃s t : Set α⦄ (h : s subseteq t) : BddAbove
 t -> BddAbove s
· 使用定理 `Dense.nonempty`：Dense.nonempty [h : Nonempty X] (hs : Dense s) : s.Nonem
pty

--- 原说明 ---
The supremum of a bounded above, continuous function on a dense set is equal to 
the supremum on
the universe.
-/
theorem Dense.ciSup {α : Type*} [TopologicalSpace α]
    [ConditionallyCompleteLattice α] [ClosedIicTopology α] {f : γ → α} [TopologicalSpace γ]
    {S : Set γ} (hS : Dense S) (hf : Continuous f) (h : BddAbove (range f)) :
    ⨆ s : S, f s = ⨆ i, f i := by
  rw [← sSup_range, ← sSup_range]
  obtain (_ | _) := isEmpty_or_nonempty γ
  · simp [Set.range_eq_empty]
  refine ((isLUB_csSup (range_nonempty f) h).unique ?_).symm
  refine (isLUB_congr (hS.upperBounds_image hf)).mp (isLUB_ciSup_set ?_ hS.nonempty)
  exact h.mono (by grind)

/-- The infimum of a bounded below, continuous function on a dense set is equal to the infimum on
the universe. -/
/-
**Dense.ciInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Dense.ciInf {α : Type*} [TopologicalSpace α] [ConditionallyCompleteLattice
 α] [ClosedIciTopology α] {f : γ -> α} [TopologicalSpace γ] {S : Set γ} (hS : De
nse S) (hf : Continuous f) (h : BddBelow (range f)) : ⨅ s : S, f s = ⨅ i, f i
参数：hS : Dense S；hf : Continuous f；h : BddBelow (range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dense.ciSup`：Dense.ciSup {α : Type*} [TopologicalSpace α] [Conditionally
CompleteLattice α] [ClosedIicTopology α] {f : γ -> α} [TopologicalSpace γ] {S : 
S…
· 使用定理 `instClosedIicTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : Preorder α] [ClosedIciTopology α], ClosedIicTopology αᵒᵈ

--- 原说明 ---
The infimum of a bounded below, continuous function on a dense set is equal to t
he infimum on
the universe.
-/
theorem Dense.ciInf {α : Type*} [TopologicalSpace α]
    [ConditionallyCompleteLattice α] [ClosedIciTopology α] {f : γ → α} [TopologicalSpace γ]
    {S : Set γ} (hS : Dense S) (hf : Continuous f) (h : BddBelow (range f)) :
    ⨅ s : S, f s = ⨅ i, f i :=
  hS.ciSup (α := αᵒᵈ) hf h

/-- This is an analogue of `Dense.continuous_sup` for functions taking values in a conditionally
complete linear order. The assumption of `BddAbove (range f)` is not needed in this theorem. -/
/-
**Dense.ciSup'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Dense.ciSup' {α : Type*} [TopologicalSpace α] [ConditionallyCompleteLinear
Order α] [ClosedIicTopology α] {f : γ -> α} [TopologicalSpace γ] {S : Set γ} (hS
 : Dense S) (hf : Continuous f) : ⨆ s : S, f s = ⨆ i, f i
参数：hS : Dense S；hf : Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dense.ciSup`：Dense.ciSup {α : Type*} [TopologicalSpace α] [Conditionally
CompleteLattice α] [ClosedIicTopology α] {f : γ -> α} [TopologicalSpace γ] {S : 
S…
· 使用定理 `BddAbove.mono`：BddAbove.mono ⦃s t : Set α⦄ (h : s subseteq t) : BddAbove
 t -> BddAbove s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Continuous.range_subset_closure_image_dense`：Continuous.range_subset_clo
sure_image_dense {f : X -> Y} (hf : Continuous f) (hs : Dense s) : range f subse
teq closure (f '' s)
· 使用定理 `BddAbove.closure`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : P
reorder α] [ClosedIicTopology α] {s : Set α},   BddAbove s → BddAbove (closure s
)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `ciSup_of_not_bddAbove`：ciSup_of_not_bddAbove (hf : ¬BddAbove (range f)) 
: ⨆ i, f i = sSup ∅
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
This is an analogue of `Dense.continuous_sup` for functions taking values in a c
onditionally
complete linear order. The assumption of `BddAbove (range f)` is not needed in t
his theorem.
-/
theorem Dense.ciSup' {α : Type*} [TopologicalSpace α]
    [ConditionallyCompleteLinearOrder α] [ClosedIicTopology α] {f : γ → α} [TopologicalSpace γ]
    {S : Set γ} (hS : Dense S) (hf : Continuous f) :
    ⨆ s : S, f s = ⨆ i, f i := by
  by_cases h : BddAbove (range (fun x : S ↦ f x))
  · refine hS.ciSup hf <| h.closure.mono ?_
    simpa [← Function.comp_def, range_comp] using hf.range_subset_closure_image_dense hS
  · suffices ¬ BddAbove (range f) by simp [ciSup_of_not_bddAbove, this, h]
    contrapose h
    grind [h.mono]

/-- This is an analogue of `Dense.continuous_inf` for functions taking values in a conditionally
complete linear order. The assumption of `BddBelow (range f)` is not needed in this theorem. -/
/-
**Dense.ciInf'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Dense.ciInf' {α : Type*} [TopologicalSpace α] [ConditionallyCompleteLinear
Order α] [ClosedIciTopology α] {f : γ -> α} [TopologicalSpace γ] {S : Set γ} (hS
 : Dense S) (hf : Continuous f) : ⨅ s : S, f s = ⨅ i, f i
参数：hS : Dense S；hf : Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dense.ciSup'`：Dense.ciSup' {α : Type*} [TopologicalSpace α] [Conditional
lyCompleteLinearOrder α] [ClosedIicTopology α] {f : γ -> α} [TopologicalSpace γ]
 {…
· 使用定理 `instClosedIicTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : Preorder α] [ClosedIciTopology α], ClosedIicTopology αᵒᵈ

--- 原说明 ---
This is an analogue of `Dense.continuous_inf` for functions taking values in a c
onditionally
complete linear order. The assumption of `BddBelow (range f)` is not needed in t
his theorem.
-/
theorem Dense.ciInf' {α : Type*} [TopologicalSpace α]
    [ConditionallyCompleteLinearOrder α] [ClosedIciTopology α] {f : γ → α} [TopologicalSpace γ]
    {S : Set γ} (hS : Dense S) (hf : Continuous f) :
    ⨅ s : S, f s = ⨅ i, f i :=
  hS.ciSup' (α := αᵒᵈ) hf

section ConditionallyCompleteLinearOrder

variable {α : Type*} [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]

/-- A closed interval in a conditionally complete linear order is compact.
Also see general API on `CompactIccSpace`. -/
/-
**ConditionallyCompleteLinearOrder.isCompact_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Cond
itionallyCompleteLinearOrder`。
形式化陈述：∀ {α : Type u_3} [inst : ConditionallyCompleteLinearOrder α] [inst_1 : Top
ologicalSpace α] [OrderTopology α] (a b : α),   IsCompact (Set.Icc a b)
参数：a b : α；Set.Icc a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `pure_le_nhds`：pure_le_nhds : pure <= (𝓝 : X -> Filter X)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `isLUB_csSup`：isLUB_csSup (hn : s.Nonempty) (hb : BddAbove s
· 使用定理 `IsLUB.exists_between`：IsLUB.exists_between (h : IsLUB s a) (hb : b < a) 
: exists c in s, b < c ∧ c <= a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ultrafilter.compl_mem_iff_notMem`：compl_mem_iff_notMem : sᶜ in f ↔ s ∉ f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `nhds_eq_order`：nhds_eq_order [OrderTopology α] (a : α) : 𝓝 a = (⨅ b in I
io a, 𝓟 (Ioi b)) ⊓ ⨅ b in Ioi a, 𝓟 (Iio b)
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
A closed interval in a conditionally complete linear order is compact.
Also see general API on `CompactIccSpace`.
-/
protected lemma ConditionallyCompleteLinearOrder.isCompact_Icc (a b : α) :
    IsCompact (Icc a b) := by
  simp only [isCompact_iff_ultrafilter_le_nhds, le_principal_iff]
  refine (le_or_gt a b).elim (fun _ f hfab ↦ ?_) (by simp [·])
  by_contra! hf
  have hpt : ∀ x ∈ Icc a b, {x} ∉ f := fun x hx _ ↦ hf x hx (le_trans (by simpa) (pure_le_nhds x))
  set s := { x ∈ Icc a b | Icc a x ∉ f }
  have hsb : b ∈ upperBounds s := fun x hx ↦ hx.1.2
  have ha : a ∈ s := by simp [s, *]
  let c := sSup s
  have hsc : IsLUB s c := isLUB_csSup ⟨a, ha⟩ ⟨b, hsb⟩
  have hc : c ∈ Icc a b := ⟨hsc.1 ha, hsc.2 hsb⟩
  have (i : _) (hic : i < c) : Ioi i ∈ f := by
    have ⟨j, hj, hij, hjc⟩ := hsc.exists_between hic
    filter_upwards [f.compl_mem_iff_notMem.mpr hj.2, hfab]; grind
  have ⟨x, hx, hxf⟩ : ∃ x, c < x ∧ Iio x ∉ f := by simpa [nhds_eq_order, eq_true this] using hf c hc
  have : Icc a c ∉ f := mt (mem_of_superset · (by grind)) hxf
  have : x ∈ Icc a b := ⟨by grind, le_of_not_gt fun h ↦ hxf (mem_of_superset hfab (by grind))⟩
  have : Icc a x ∈ f := by simpa [s, this.1, this.2] using notMem_of_csSup_lt hx ⟨b, hsb⟩
  exact hpt _ ‹_› (by filter_upwards [f.compl_mem_iff_notMem.mpr hxf, this]; grind)
/-
**upperClosure_eq_Ici_csInf** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：upperClosure_eq_Ici_csInf {s : Set α} (h₁ : s.Nonempty) (h₂ : BddBelow s) 
(hs : IsClosed s) : upperClosure s = Ici (sInf s)
参数：h₁ : s.Nonempty；h₂ : BddBelow s；hs : IsClosed s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `csInf_le_of_le`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α]
 {s : Set α} {a b : α}, BddBelow s → b ∈ s → b ≤ a → sInf s ≤ a
· 使用定理 `IsGLB.mem_of_isClosed`：IsGLB.mem_of_isClosed {a : α} {s : Set α} (ha : I
sGLB s a) (hs : s.Nonempty) (sc : IsClosed s) : a in s
· 使用定理 `isGLB_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s
 : Set α},   s.Nonempty → autoParam (BddBelow s) isGLB_csInf._auto_1 → IsGLB s (
s…
-/
lemma upperClosure_eq_Ici_csInf {s : Set α} (h₁ : s.Nonempty) (h₂ : BddBelow s) (hs : IsClosed s) :
    upperClosure s = Ici (sInf s) :=
  Set.ext fun _ ↦ ⟨fun ⟨_, h, h'⟩ ↦ csInf_le_of_le h₂ h h',
    (⟨_, (isGLB_csInf h₁ h₂).mem_of_isClosed h₁ hs, ·⟩)⟩
/-
**lowerClosure_eq_Iic_csSup** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lowerClosure_eq_Iic_csSup {s : Set α} (h₁ : s.Nonempty) (h₂ : BddAbove s) 
(hs : IsClosed s) : lowerClosure s = Iic (sSup s)
参数：h₁ : s.Nonempty；h₂ : BddAbove s；hs : IsClosed s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `upperClosure_eq_Ici_csInf`：upperClosure_eq_Ici_csInf {s : Set α} (h₁ : s
.Nonempty) (h₂ : BddBelow s) (hs : IsClosed s) : upperClosure s = Ici (sInf s)
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
-/
lemma lowerClosure_eq_Iic_csSup {s : Set α} (h₁ : s.Nonempty) (h₂ : BddAbove s) (hs : IsClosed s) :
    lowerClosure s = Iic (sSup s) :=
  upperClosure_eq_Ici_csInf (α := αᵒᵈ) h₁ h₂ hs
/-
**IsClosed.upperClosure** 是 Mathlib 中的一个定理，位于命名空间 `IsClosed`。
形式化陈述：∀ {α : Type u_3} [inst : ConditionallyCompleteLinearOrder α] [inst_1 : Top
ologicalSpace α] [OrderTopology α]   {s : Set α}, IsClosed s → IsClosed ↑(upperC
losure s)
参数：upperClosure s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `upperClosure_empty`：upperClosure_empty : upperClosure (∅ : Set α) = ⊤
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `OrderClosedTopology.to_t2Space`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : PartialOrder α] [t : OrderClosedTopology α], T2Space α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isClosed_Ici`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Preor
der α] [ClosedIciTopology α] {a : α}, IsClosed (Set.Ici a)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用引理 `upperClosure_eq_Ici_csInf`：upperClosure_eq_Ici_csInf {s : Set α} (h₁ : s
.Nonempty) (h₂ : BddBelow s) (hs : IsClosed s) : upperClosure s = Ici (sInf s)
· 使用定理 `isClosed_univ`：isClosed_univ : IsClosed (univ : Set X)
· 使用引理 `upperClosure_eq_bot`：upperClosure_eq_bot {s : Set α} (hs : ¬ BddBelow s)
 : upperClosure s = ⊥
-/
protected lemma IsClosed.upperClosure {s : Set α} (hs : IsClosed s) :
    IsClosed (upperClosure s : Set α) := by
  obtain rfl | h₁ := s.eq_empty_or_nonempty
  · simp
  by_cases h₂ : BddBelow s
  · exact upperClosure_eq_Ici_csInf h₁ h₂ hs ▸ isClosed_Ici
  · exact upperClosure_eq_bot h₂ ▸ isClosed_univ
/-
**IsClosed.lowerClosure** 是 Mathlib 中的一个定理，位于命名空间 `IsClosed`。
形式化陈述：∀ {α : Type u_3} [inst : ConditionallyCompleteLinearOrder α] [inst_1 : Top
ologicalSpace α] [OrderTopology α]   {s : Set α}, IsClosed s → IsClosed (lowerCl
osure s).carrier
参数：lowerClosure s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.upperClosure`：∀ {α : Type u_3} [inst : ConditionallyCompleteLin
earOrder α] [inst_1 : TopologicalSpace α] [OrderTopology α]   {s : Set α}, IsClo
sed s → IsC…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
-/
protected lemma IsClosed.lowerClosure {s : Set α} (hs : IsClosed s) :
    IsClosed (lowerClosure s).1 :=
  IsClosed.upperClosure (α := αᵒᵈ) hs

end ConditionallyCompleteLinearOrder

/-!
### Existence of sequences tending to `sInf` or `sSup` of a given set
-/

/-
**IsLUB.exists_seq_strictMono_tendsto_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLUB.exists_seq_strictMono_tendsto_of_notMem {t : Set α} {x : α} [IsCount
ablyGenerated (𝓝 x)] (htx : IsLUB t x) (notMem : x ∉ t) (ht : t.Nonempty) : exis
ts u : Nat -> α, StrictMono u ∧ (forall n, u n < x) ∧ Tendsto u atTop (𝓝 x) ∧ fo
rall n, u n in t
参数：𝓝 x；htx : IsLUB t x；notMem : x ∉ t；ht : t.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.exists_seq_forall_of_frequently`：exists_seq_forall_of_frequently 
{ι : Type*} {l : Filter ι} {p : ι -> Prop} [l.IsCountablyGenerated] (h : existsᶠ
 n in l, p n) : exists ns : …
· 使用定理 `IsLUB.frequently_mem`：IsLUB.frequently_mem {a : α} {s : Set α} (ha : IsL
UB s a) (hs : s.Nonempty) : existsᶠ x in 𝓝[<=] a, x in s
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `lt_mem_nhds`：lt_mem_nhds [OrderTopology α] {a b : α} (h : a < b) : foral
lᶠ x in 𝓝 b, a < x
· 使用定理 `strictMono_nat_of_lt_succ`：strictMono_nat_of_lt_succ {f : Nat -> α} (hf 
: forall n, f n < f (n + 1)) : StrictMono f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `StrictMono.tendsto_atTop`：∀ {φ : ℕ → ℕ}, StrictMono φ → Filter.Tendsto φ
 Filter.atTop Filter.atTop
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
### Existence of sequences tending to `sInf` or `sSup` of a given set
-/
theorem IsLUB.exists_seq_strictMono_tendsto_of_notMem {t : Set α} {x : α}
    [IsCountablyGenerated (𝓝 x)] (htx : IsLUB t x) (notMem : x ∉ t) (ht : t.Nonempty) :
    ∃ u : ℕ → α, StrictMono u ∧ (∀ n, u n < x) ∧ Tendsto u atTop (𝓝 x) ∧ ∀ n, u n ∈ t := by
  obtain ⟨v, hvx, hvt⟩ := exists_seq_forall_of_frequently (htx.frequently_mem ht)
  replace hvx := hvx.mono_right nhdsWithin_le_nhds
  have hvx' : ∀ {n}, v n < x := (htx.1 (hvt _)).lt_of_ne (ne_of_mem_of_not_mem (hvt _) notMem)
  have : ∀ k, ∀ᶠ l in atTop, v k < v l := fun k => hvx.eventually (lt_mem_nhds hvx')
  choose N hN hvN using fun k => ((eventually_gt_atTop k).and (this k)).exists
  refine ⟨fun k => v (N^[k] 0), strictMono_nat_of_lt_succ fun _ => ?_, fun _ => hvx',
    hvx.comp (strictMono_nat_of_lt_succ fun _ => ?_).tendsto_atTop, fun _ => hvt _⟩
  · rw [iterate_succ_apply']; exact hvN _
  · rw [iterate_succ_apply']; exact hN _
/-
**IsLUB.exists_seq_monotone_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLUB.exists_seq_monotone_tendsto {t : Set α} {x : α} [IsCountablyGenerate
d (𝓝 x)] (htx : IsLUB t x) (ht : t.Nonempty) : exists u : Nat -> α, Monotone u ∧
 (forall n, u n <= x) ∧ Tendsto u atTop (𝓝 x) ∧ forall n, u n in t
参数：𝓝 x；htx : IsLUB t x；ht : t.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `monotone_const`：monotone_const [Preorder α] [Preorder β] {c : β} : Monot
one fun _ : α => c
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `IsLUB.exists_seq_strictMono_tendsto_of_notMem`：IsLUB.exists_seq_strictMo
no_tendsto_of_notMem {t : Set α} {x : α} [IsCountablyGenerated (𝓝 x)] (htx : IsL
UB t x) (notMem : x ∉ t) (ht : t.No…
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsLUB.exists_seq_monotone_tendsto {t : Set α} {x : α} [IsCountablyGenerated (𝓝 x)]
    (htx : IsLUB t x) (ht : t.Nonempty) :
    ∃ u : ℕ → α, Monotone u ∧ (∀ n, u n ≤ x) ∧ Tendsto u atTop (𝓝 x) ∧ ∀ n, u n ∈ t := by
  by_cases h : x ∈ t
  · exact ⟨fun _ => x, monotone_const, fun n => le_rfl, tendsto_const_nhds, fun _ => h⟩
  · rcases htx.exists_seq_strictMono_tendsto_of_notMem h ht with ⟨u, hu⟩
    exact ⟨u, hu.1.monotone, fun n => (hu.2.1 n).le, hu.2.2⟩
/-
**exists_seq_strictMono_tendsto'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_seq_strictMono_tendsto' {α : Type*} [LinearOrder α] [TopologicalSpa
ce α] [DenselyOrdered α] [OrderTopology α] [FirstCountableTopology α] {x y : α} 
(hy : y < x) : exists u : Nat -> α, StrictMono u ∧ (forall n, u n in Ioo y x) ∧ 
Tendsto u atTop (𝓝 x)
参数：hy : y < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_Ioo`：nonempty_Ioo [DenselyOrdered α] : (Ioo a b).Nonempty ↔
 a < b
· 使用定理 `IsLUB.exists_seq_strictMono_tendsto_of_notMem`：IsLUB.exists_seq_strictMo
no_tendsto_of_notMem {t : Set α} {x : α} [IsCountablyGenerated (𝓝 x)] (htx : IsL
UB t x) (notMem : x ∉ t) (ht : t.No…
· 使用定理 `FirstCountableTopology.nhds_generated_countable`：∀ {α : Type u} {t : Top
ologicalSpace α} [self : FirstCountableTopology α] (a : α), (nhds a).IsCountably
Generated
· 使用定理 `isLUB_Ioo`：∀ {γ : Type u_3} [inst : SemilatticeInf γ] [DenselyOrdered γ]
 {a b : γ}, b < a → IsLUB (Set.Ioo b a) a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.symm`：∀ {a b : Prop}, a ∧ b → b ∧ a
-/
theorem exists_seq_strictMono_tendsto' {α : Type*} [LinearOrder α] [TopologicalSpace α]
    [DenselyOrdered α] [OrderTopology α] [FirstCountableTopology α] {x y : α} (hy : y < x) :
    ∃ u : ℕ → α, StrictMono u ∧ (∀ n, u n ∈ Ioo y x) ∧ Tendsto u atTop (𝓝 x) := by
  have hx : x ∉ Ioo y x := fun h => (lt_irrefl x h.2).elim
  have ht : Set.Nonempty (Ioo y x) := nonempty_Ioo.2 hy
  rcases (isLUB_Ioo hy).exists_seq_strictMono_tendsto_of_notMem hx ht with ⟨u, hu⟩
  exact ⟨u, hu.1, hu.2.2.symm⟩
/-
**exists_seq_strictMono_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_seq_strictMono_tendsto [DenselyOrdered α] [NoMinOrder α] [FirstCoun
tableTopology α] (x : α) : exists u : Nat -> α, StrictMono u ∧ (forall n, u n < 
x) ∧ Tendsto u atTop (𝓝 x)
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NoMinOrder.exists_lt`：∀ {α : Type u_3} {inst : LT α} [self : NoMinOrder 
α] (a : α), ∃ b, b < a
· 使用定理 `exists_seq_strictMono_tendsto'`：exists_seq_strictMono_tendsto' {α : Type
*} [LinearOrder α] [TopologicalSpace α] [DenselyOrdered α] [OrderTopology α] [Fi
rstCountableTopology…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem exists_seq_strictMono_tendsto [DenselyOrdered α] [NoMinOrder α] [FirstCountableTopology α]
    (x : α) : ∃ u : ℕ → α, StrictMono u ∧ (∀ n, u n < x) ∧ Tendsto u atTop (𝓝 x) := by
  obtain ⟨y, hy⟩ : ∃ y, y < x := exists_lt x
  rcases exists_seq_strictMono_tendsto' hy with ⟨u, hu_mono, hu_mem, hux⟩
  exact ⟨u, hu_mono, fun n => (hu_mem n).2, hux⟩
/-
**exists_seq_strictMono_tendsto_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_seq_strictMono_tendsto_nhdsWithin [DenselyOrdered α] [NoMinOrder α]
 [FirstCountableTopology α] (x : α) : exists u : Nat -> α, StrictMono u ∧ (foral
l n, u n < x) ∧ Tendsto u atTop (𝓝[<] x)
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_seq_strictMono_tendsto`：exists_seq_strictMono_tendsto [DenselyOrd
ered α] [NoMinOrder α] [FirstCountableTopology α] (x : α) : exists u : Nat -> α,
 StrictMono u ∧ (fo…
· 使用定理 `tendsto_nhdsWithin_mono_right`：tendsto_nhdsWithin_mono_right {f : β -> α
} {l : Filter β} {a : α} {s t : Set α} (hst : s subseteq t) (h : Tendsto f l (𝓝[
s] a)) : Tendsto f …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `tendsto_nhdsWithin_range`：tendsto_nhdsWithin_range {a : α} {l : Filter β
} {f : β -> α} : Tendsto f l (𝓝[range f] a) ↔ Tendsto f l (𝓝 a)
-/
theorem exists_seq_strictMono_tendsto_nhdsWithin [DenselyOrdered α] [NoMinOrder α]
    [FirstCountableTopology α] (x : α) :
    ∃ u : ℕ → α, StrictMono u ∧ (∀ n, u n < x) ∧ Tendsto u atTop (𝓝[<] x) :=
  let ⟨u, hu, hx, h⟩ := exists_seq_strictMono_tendsto x
  ⟨u, hu, hx, tendsto_nhdsWithin_mono_right (range_subset_iff.2 hx) <| tendsto_nhdsWithin_range.2 h⟩
/-
**exists_seq_tendsto_sSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_seq_tendsto_sSup {α : Type*} [ConditionallyCompleteLinearOrder α] [
TopologicalSpace α] [OrderTopology α] [FirstCountableTopology α] {S : Set α} (hS
 : S.Nonempty) (hS' : BddAbove S) : exists u : Nat -> α, Monotone u ∧ Tendsto u 
atTop (𝓝 (sSup S)) ∧ forall n, u n in S
参数：hS : S.Nonempty；hS' : BddAbove S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.exists_seq_monotone_tendsto`：IsLUB.exists_seq_monotone_tendsto {t 
: Set α} {x : α} [IsCountablyGenerated (𝓝 x)] (htx : IsLUB t x) (ht : t.Nonempty
) : exists u : Nat -> α…
· 使用定理 `FirstCountableTopology.nhds_generated_countable`：∀ {α : Type u} {t : Top
ologicalSpace α} [self : FirstCountableTopology α] (a : α), (nhds a).IsCountably
Generated
· 使用定理 `isLUB_csSup`：isLUB_csSup (hn : s.Nonempty) (hb : BddAbove s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem exists_seq_tendsto_sSup {α : Type*} [ConditionallyCompleteLinearOrder α]
    [TopologicalSpace α] [OrderTopology α] [FirstCountableTopology α] {S : Set α} (hS : S.Nonempty)
    (hS' : BddAbove S) : ∃ u : ℕ → α, Monotone u ∧ Tendsto u atTop (𝓝 (sSup S)) ∧ ∀ n, u n ∈ S := by
  rcases (isLUB_csSup hS hS').exists_seq_monotone_tendsto hS with ⟨u, hu⟩
  exact ⟨u, hu.1, hu.2.2⟩
/-
**Dense.exists_seq_strictMono_tendsto_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Dense.exists_seq_strictMono_tendsto_of_lt [DenselyOrdered α] [FirstCountab
leTopology α] {s : Set α} (hs : Dense s) {x y : α} (hy : y < x) : exists u : Nat
 -> α, StrictMono u ∧ (forall n, u n in (Ioo y x inter s)) ∧ Tendsto u atTop (𝓝 
x)
参数：hs : Dense s；hy : y < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dense.exists_between`：Dense.exists_between [DenselyOrdered α] {s : Set α
} (hs : Dense s) {x y : α} (h : x < y) : exists z in s, z in Ioo x y
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Set.mem_inter`：mem_inter {x : α} {a b : Set α} (ha : x in a) (hb : x in 
b) : x in a inter b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Dense.isLUB_inter_iff`：Dense.isLUB_inter_iff {α : Type*} [TopologicalSpa
ce α] [Preorder α] [ClosedIicTopology α] {s t : Set α} (hs : Dense s) (ht : IsOp
en t) {x : …
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `isOpen_Ioo`：isOpen_Ioo : IsOpen (Ioo a b)
· 使用定理 `isLUB_Ioo`：∀ {γ : Type u_3} [inst : SemilatticeInf γ] [DenselyOrdered γ]
 {a b : γ}, b < a → IsLUB (Set.Ioo b a) a
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `IsLUB.exists_seq_strictMono_tendsto_of_notMem`：IsLUB.exists_seq_strictMo
no_tendsto_of_notMem {t : Set α} {x : α} [IsCountablyGenerated (𝓝 x)] (htx : IsL
UB t x) (notMem : x ∉ t) (ht : t.No…
· 使用定理 `FirstCountableTopology.nhds_generated_countable`：∀ {α : Type u} {t : Top
ologicalSpace α} [self : FirstCountableTopology α] (a : α), (nhds a).IsCountably
Generated
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem Dense.exists_seq_strictMono_tendsto_of_lt [DenselyOrdered α] [FirstCountableTopology α]
    {s : Set α} (hs : Dense s) {x y : α} (hy : y < x) :
    ∃ u : ℕ → α, StrictMono u ∧ (∀ n, u n ∈ (Ioo y x ∩ s)) ∧ Tendsto u atTop (𝓝 x) := by
  have hnonempty : (Ioo y x ∩ s).Nonempty := by
    obtain ⟨z, hyz, hzx⟩ := hs.exists_between hy
    exact ⟨z, mem_inter hzx hyz⟩
  have hx : IsLUB (Ioo y x ∩ s) x := hs.isLUB_inter_iff isOpen_Ioo |>.mpr <| isLUB_Ioo hy
  apply hx.exists_seq_strictMono_tendsto_of_notMem (by simp) hnonempty |>.imp
  simp_all
/-
**Dense.exists_seq_strictMono_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Dense.exists_seq_strictMono_tendsto [DenselyOrdered α] [NoMinOrder α] [Fir
stCountableTopology α] {s : Set α} (hs : Dense s) (x : α) : exists u : Nat -> α,
 StrictMono u ∧ (forall n, u n in (Iio x inter s)) ∧ Tendsto u atTop (𝓝 x)
参数：hs : Dense s；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NoMinOrder.exists_lt`：∀ {α : Type u_3} {inst : LT α} [self : NoMinOrder 
α] (a : α), ∃ b, b < a
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Dense.exists_seq_strictMono_tendsto_of_lt`：Dense.exists_seq_strictMono_t
endsto_of_lt [DenselyOrdered α] [FirstCountableTopology α] {s : Set α} (hs : Den
se s) {x y : α} (hy : y < x) : …
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem Dense.exists_seq_strictMono_tendsto [DenselyOrdered α] [NoMinOrder α]
    [FirstCountableTopology α] {s : Set α} (hs : Dense s) (x : α) :
    ∃ u : ℕ → α, StrictMono u ∧ (∀ n, u n ∈ (Iio x ∩ s)) ∧ Tendsto u atTop (𝓝 x) := by
  obtain ⟨y, hy⟩ := exists_lt x
  apply hs.exists_seq_strictMono_tendsto_of_lt (exists_lt x).choose_spec |>.imp
  simp_all
/-
**DenseRange.exists_seq_strictMono_tendsto_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DenseRange.exists_seq_strictMono_tendsto_of_lt {β : Type*} [LinearOrder β]
 [DenselyOrdered α] [FirstCountableTopology α] {f : β -> α} {x y : α} (hf : Dens
eRange f) (hmono : Monotone f) (hlt : y < x) : exists u : Nat -> β, StrictMono u
 ∧ (forall n, f (u n) in Ioo y x) ∧ Tendsto (f ∘ u) atTop (𝓝 x)
参数：hf : DenseRange f；hmono : Monotone f；hlt : y < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dense.exists_seq_strictMono_tendsto_of_lt`：Dense.exists_seq_strictMono_t
endsto_of_lt [DenselyOrdered α] [FirstCountableTopology α] {s : Set α} (hs : Den
se s) {x y : α} (hy : y < x) : …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Monotone.reflect_lt`：Monotone.reflect_lt (hf : Monotone f) {a b : α} (h 
: f a < f b) : a < b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem DenseRange.exists_seq_strictMono_tendsto_of_lt {β : Type*} [LinearOrder β]
    [DenselyOrdered α] [FirstCountableTopology α] {f : β → α} {x y : α} (hf : DenseRange f)
    (hmono : Monotone f) (hlt : y < x) :
    ∃ u : ℕ → β, StrictMono u ∧ (∀ n, f (u n) ∈ Ioo y x) ∧ Tendsto (f ∘ u) atTop (𝓝 x) := by
  rcases Dense.exists_seq_strictMono_tendsto_of_lt hf hlt with ⟨u, hu, huyxf, hlim⟩
  have huyx (n : ℕ) : u n ∈ Ioo y x := (huyxf n).1
  have huf (n : ℕ) : u n ∈ range f := (huyxf n).2
  choose v hv using huf
  obtain rfl : f ∘ v = u := funext hv
  exact ⟨v, fun a b hlt ↦ hmono.reflect_lt <| hu hlt, huyx, hlim⟩
/-
**DenseRange.exists_seq_strictMono_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DenseRange.exists_seq_strictMono_tendsto {β : Type*} [LinearOrder β] [Dens
elyOrdered α] [NoMinOrder α] [FirstCountableTopology α] {f : β -> α} (hf : Dense
Range f) (hmono : Monotone f) (x : α) : exists u : Nat -> β, StrictMono u ∧ (for
all n, f (u n) in Iio x) ∧ Tendsto (f ∘ u) atTop (𝓝 x)
参数：hf : DenseRange f；hmono : Monotone f；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dense.exists_seq_strictMono_tendsto`：Dense.exists_seq_strictMono_tendsto
 [DenselyOrdered α] [NoMinOrder α] [FirstCountableTopology α] {s : Set α} (hs : 
Dense s) (x : α) : exists…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Monotone.reflect_lt`：Monotone.reflect_lt (hf : Monotone f) {a b : α} (h 
: f a < f b) : a < b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem DenseRange.exists_seq_strictMono_tendsto {β : Type*} [LinearOrder β] [DenselyOrdered α]
    [NoMinOrder α] [FirstCountableTopology α] {f : β → α} (hf : DenseRange f) (hmono : Monotone f)
    (x : α) :
    ∃ u : ℕ → β, StrictMono u ∧ (∀ n, f (u n) ∈ Iio x) ∧ Tendsto (f ∘ u) atTop (𝓝 x) := by
  rcases Dense.exists_seq_strictMono_tendsto hf x with ⟨u, hu, huxf, hlim⟩
  have hux (n : ℕ) : u n ∈ Iio x := (huxf n).1
  have huf (n : ℕ) : u n ∈ range f := (huxf n).2
  choose v hv using huf
  obtain rfl : f ∘ v = u := funext hv
  exact ⟨v, fun a b hlt ↦ hmono.reflect_lt <| hu hlt, hux, hlim⟩

set_option backward.isDefEq.respectTransparency false in
/-
**IsGLB.exists_seq_strictAnti_tendsto_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsGLB.exists_seq_strictAnti_tendsto_of_notMem {t : Set α} {x : α} [IsCount
ablyGenerated (𝓝 x)] (htx : IsGLB t x) (notMem : x ∉ t) (ht : t.Nonempty) : exis
ts u : Nat -> α, StrictAnti u ∧ (forall n, x < u n) ∧ Tendsto u atTop (𝓝 x) ∧ fo
rall n, u n in t
参数：𝓝 x；htx : IsGLB t x；notMem : x ∉ t；ht : t.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.exists_seq_strictMono_tendsto_of_notMem`：IsLUB.exists_seq_strictMo
no_tendsto_of_notMem {t : Set α} {x : α} [IsCountablyGenerated (𝓝 x)] (htx : IsL
UB t x) (notMem : x ∉ t) (ht : t.No…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
-/
theorem IsGLB.exists_seq_strictAnti_tendsto_of_notMem {t : Set α} {x : α}
    [IsCountablyGenerated (𝓝 x)] (htx : IsGLB t x) (notMem : x ∉ t) (ht : t.Nonempty) :
    ∃ u : ℕ → α, StrictAnti u ∧ (∀ n, x < u n) ∧ Tendsto u atTop (𝓝 x) ∧ ∀ n, u n ∈ t :=
  IsLUB.exists_seq_strictMono_tendsto_of_notMem (α := αᵒᵈ) htx notMem ht

set_option backward.isDefEq.respectTransparency false in
/-
**IsGLB.exists_seq_antitone_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsGLB.exists_seq_antitone_tendsto {t : Set α} {x : α} [IsCountablyGenerate
d (𝓝 x)] (htx : IsGLB t x) (ht : t.Nonempty) : exists u : Nat -> α, Antitone u ∧
 (forall n, x <= u n) ∧ Tendsto u atTop (𝓝 x) ∧ forall n, u n in t
参数：𝓝 x；htx : IsGLB t x；ht : t.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLUB.exists_seq_monotone_tendsto`：IsLUB.exists_seq_monotone_tendsto {t 
: Set α} {x : α} [IsCountablyGenerated (𝓝 x)] (htx : IsLUB t x) (ht : t.Nonempty
) : exists u : Nat -> α…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
-/
theorem IsGLB.exists_seq_antitone_tendsto {t : Set α} {x : α} [IsCountablyGenerated (𝓝 x)]
    (htx : IsGLB t x) (ht : t.Nonempty) :
    ∃ u : ℕ → α, Antitone u ∧ (∀ n, x ≤ u n) ∧ Tendsto u atTop (𝓝 x) ∧ ∀ n, u n ∈ t :=
  IsLUB.exists_seq_monotone_tendsto (α := αᵒᵈ) htx ht
/-
**exists_seq_strictAnti_tendsto'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_seq_strictAnti_tendsto' [DenselyOrdered α] [FirstCountableTopology 
α] {x y : α} (hy : x < y) : exists u : Nat -> α, StrictAnti u ∧ (forall n, u n i
n Ioo x y) ∧ Tendsto u atTop (𝓝 x)
参数：hy : x < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.Ioo_toDual`：Ioo_toDual : Ioo (toDual a) (toDual b) = ofDual ⁻¹' Ioo 
b a
· 使用定理 `exists_seq_strictMono_tendsto'`：exists_seq_strictMono_tendsto' {α : Type
*} [LinearOrder α] [TopologicalSpace α] [DenselyOrdered α] [OrderTopology α] [Fi
rstCountableTopology…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `instFirstCountableTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalS
pace α] [h : FirstCountableTopology α], FirstCountableTopology αᵒᵈ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `OrderDual.toDual_lt_toDual`：toDual_lt_toDual [LT α] {a b : α} : toDual a
 < toDual b ↔ b < a
-/
theorem exists_seq_strictAnti_tendsto' [DenselyOrdered α] [FirstCountableTopology α] {x y : α}
    (hy : x < y) : ∃ u : ℕ → α, StrictAnti u ∧ (∀ n, u n ∈ Ioo x y) ∧ Tendsto u atTop (𝓝 x) := by
  simpa using! exists_seq_strictMono_tendsto' (α := αᵒᵈ) (OrderDual.toDual_lt_toDual.2 hy)
/-
**exists_seq_strictAnti_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_seq_strictAnti_tendsto [DenselyOrdered α] [NoMaxOrder α] [FirstCoun
tableTopology α] (x : α) : exists u : Nat -> α, StrictAnti u ∧ (forall n, x < u 
n) ∧ Tendsto u atTop (𝓝 x)
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_seq_strictMono_tendsto`：exists_seq_strictMono_tendsto [DenselyOrd
ered α] [NoMinOrder α] [FirstCountableTopology α] (x : α) : exists u : Nat -> α,
 StrictMono u ∧ (fo…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `instFirstCountableTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalS
pace α] [h : FirstCountableTopology α], FirstCountableTopology αᵒᵈ
-/
theorem exists_seq_strictAnti_tendsto [DenselyOrdered α] [NoMaxOrder α] [FirstCountableTopology α]
    (x : α) : ∃ u : ℕ → α, StrictAnti u ∧ (∀ n, x < u n) ∧ Tendsto u atTop (𝓝 x) :=
  exists_seq_strictMono_tendsto (α := αᵒᵈ) x
/-
**exists_seq_strictAnti_tendsto_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_seq_strictAnti_tendsto_nhdsWithin [DenselyOrdered α] [NoMaxOrder α]
 [FirstCountableTopology α] (x : α) : exists u : Nat -> α, StrictAnti u ∧ (foral
l n, x < u n) ∧ Tendsto u atTop (𝓝[>] x)
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_seq_strictMono_tendsto_nhdsWithin`：exists_seq_strictMono_tendsto_
nhdsWithin [DenselyOrdered α] [NoMinOrder α] [FirstCountableTopology α] (x : α) 
: exists u : Nat -> α, StrictM…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `instFirstCountableTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalS
pace α] [h : FirstCountableTopology α], FirstCountableTopology αᵒᵈ
-/
theorem exists_seq_strictAnti_tendsto_nhdsWithin [DenselyOrdered α] [NoMaxOrder α]
    [FirstCountableTopology α] (x : α) :
    ∃ u : ℕ → α, StrictAnti u ∧ (∀ n, x < u n) ∧ Tendsto u atTop (𝓝[>] x) :=
  exists_seq_strictMono_tendsto_nhdsWithin (α := αᵒᵈ) _
/-
**exists_seq_strictAnti_strictMono_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_seq_strictAnti_strictMono_tendsto [DenselyOrdered α] [FirstCountabl
eTopology α] {x y : α} (h : x < y) : exists u v : Nat -> α, StrictAnti u ∧ Stric
tMono v ∧ (forall k, u k in Ioo x y) ∧ (forall l, v l in Ioo x y) ∧ (forall k l,
 u k < v l) ∧ Tendsto u atTop (𝓝 x) ∧ Tendsto v atTop (𝓝 y)
参数：h : x < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_seq_strictAnti_tendsto'`：exists_seq_strictAnti_tendsto' [DenselyO
rdered α] [FirstCountableTopology α] {x y : α} (hy : x < y) : exists u : Nat -> 
α, StrictAnti u ∧ (f…
· 使用定理 `exists_seq_strictMono_tendsto'`：exists_seq_strictMono_tendsto' {α : Type
*} [LinearOrder α] [TopologicalSpace α] [DenselyOrdered α] [OrderTopology α] [Fi
rstCountableTopology…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `StrictAnti.antitone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictAnti f → Antitone f
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
theorem exists_seq_strictAnti_strictMono_tendsto [DenselyOrdered α] [FirstCountableTopology α]
    {x y : α} (h : x < y) :
    ∃ u v : ℕ → α, StrictAnti u ∧ StrictMono v ∧ (∀ k, u k ∈ Ioo x y) ∧ (∀ l, v l ∈ Ioo x y) ∧
      (∀ k l, u k < v l) ∧ Tendsto u atTop (𝓝 x) ∧ Tendsto v atTop (𝓝 y) := by
  rcases exists_seq_strictAnti_tendsto' h with ⟨u, hu_anti, hu_mem, hux⟩
  rcases exists_seq_strictMono_tendsto' (hu_mem 0).2 with ⟨v, hv_mono, hv_mem, hvy⟩
  exact
    ⟨u, v, hu_anti, hv_mono, hu_mem, fun l => ⟨(hu_mem 0).1.trans (hv_mem l).1, (hv_mem l).2⟩,
      fun k l => (hu_anti.antitone zero_le).trans_lt (hv_mem l).1, hux, hvy⟩
/-
**exists_seq_tendsto_sInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_seq_tendsto_sInf {α : Type*} [ConditionallyCompleteLinearOrder α] [
TopologicalSpace α] [OrderTopology α] [FirstCountableTopology α] {S : Set α} (hS
 : S.Nonempty) (hS' : BddBelow S) : exists u : Nat -> α, Antitone u ∧ Tendsto u 
atTop (𝓝 (sInf S)) ∧ forall n, u n in S
参数：hS : S.Nonempty；hS' : BddBelow S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_seq_tendsto_sSup`：exists_seq_tendsto_sSup {α : Type*} [Conditiona
llyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α] [FirstCountable
Topology α] {…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `instFirstCountableTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalS
pace α] [h : FirstCountableTopology α], FirstCountableTopology αᵒᵈ
-/
theorem exists_seq_tendsto_sInf {α : Type*} [ConditionallyCompleteLinearOrder α]
    [TopologicalSpace α] [OrderTopology α] [FirstCountableTopology α] {S : Set α} (hS : S.Nonempty)
    (hS' : BddBelow S) : ∃ u : ℕ → α, Antitone u ∧ Tendsto u atTop (𝓝 (sInf S)) ∧ ∀ n, u n ∈ S :=
  exists_seq_tendsto_sSup (α := αᵒᵈ) hS hS'
/-
**Dense.exists_seq_strictAnti_tendsto_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Dense.exists_seq_strictAnti_tendsto_of_lt [DenselyOrdered α] [FirstCountab
leTopology α] {s : Set α} (hs : Dense s) {x y : α} (hy : x < y) : exists u : Nat
 -> α, StrictAnti u ∧ (forall n, u n in (Ioo x y inter s)) ∧ Tendsto u atTop (𝓝 
x)
参数：hs : Dense s；hy : x < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.Ioo_toDual`：Ioo_toDual : Ioo (toDual a) (toDual b) = ofDual ⁻¹' Ioo 
b a
· 使用定理 `Dense.exists_seq_strictMono_tendsto_of_lt`：Dense.exists_seq_strictMono_t
endsto_of_lt [DenselyOrdered α] [FirstCountableTopology α] {s : Set α} (hs : Den
se s) {x y : α} (hy : y < x) : …
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `instFirstCountableTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalS
pace α] [h : FirstCountableTopology α], FirstCountableTopology αᵒᵈ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `OrderDual.toDual_lt_toDual`：toDual_lt_toDual [LT α] {a b : α} : toDual a
 < toDual b ↔ b < a
-/
theorem Dense.exists_seq_strictAnti_tendsto_of_lt [DenselyOrdered α] [FirstCountableTopology α]
    {s : Set α} (hs : Dense s) {x y : α} (hy : x < y) :
    ∃ u : ℕ → α, StrictAnti u ∧ (∀ n, u n ∈ (Ioo x y ∩ s)) ∧ Tendsto u atTop (𝓝 x) := by
  simpa using! hs.exists_seq_strictMono_tendsto_of_lt (α := αᵒᵈ) (OrderDual.toDual_lt_toDual.2 hy)
/-
**Dense.exists_seq_strictAnti_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Dense.exists_seq_strictAnti_tendsto [DenselyOrdered α] [NoMaxOrder α] [Fir
stCountableTopology α] {s : Set α} (hs : Dense s) (x : α) : exists u : Nat -> α,
 StrictAnti u ∧ (forall n, u n in (Ioi x inter s)) ∧ Tendsto u atTop (𝓝 x)
参数：hs : Dense s；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dense.exists_seq_strictMono_tendsto`：Dense.exists_seq_strictMono_tendsto
 [DenselyOrdered α] [NoMinOrder α] [FirstCountableTopology α] {s : Set α} (hs : 
Dense s) (x : α) : exists…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `instFirstCountableTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalS
pace α] [h : FirstCountableTopology α], FirstCountableTopology αᵒᵈ
-/
theorem Dense.exists_seq_strictAnti_tendsto [DenselyOrdered α] [NoMaxOrder α]
    [FirstCountableTopology α] {s : Set α} (hs : Dense s) (x : α) :
    ∃ u : ℕ → α, StrictAnti u ∧ (∀ n, u n ∈ (Ioi x ∩ s)) ∧ Tendsto u atTop (𝓝 x) :=
  hs.exists_seq_strictMono_tendsto (α := αᵒᵈ) x
/-
**DenseRange.exists_seq_strictAnti_tendsto_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DenseRange.exists_seq_strictAnti_tendsto_of_lt {β : Type*} [LinearOrder β]
 [DenselyOrdered α] [FirstCountableTopology α] {f : β -> α} {x y : α} (hf : Dens
eRange f) (hmono : Monotone f) (hlt : x < y) : exists u : Nat -> β, StrictAnti u
 ∧ (forall n, f (u n) in Ioo x y) ∧ Tendsto (f ∘ u) atTop (𝓝 x)
参数：hf : DenseRange f；hmono : Monotone f；hlt : x < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Set.Ioo_toDual`：Ioo_toDual : Ioo (toDual a) (toDual b) = ofDual ⁻¹' Ioo 
b a
· 使用定理 `DenseRange.exists_seq_strictMono_tendsto_of_lt`：DenseRange.exists_seq_st
rictMono_tendsto_of_lt {β : Type*} [LinearOrder β] [DenselyOrdered α] [FirstCoun
tableTopology α] {f : β -> α} {x y :…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `instFirstCountableTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalS
pace α] [h : FirstCountableTopology α], FirstCountableTopology αᵒᵈ
· 使用定理 `Monotone.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 :
 Preorder β] {f : α → β},   Monotone f → Monotone (⇑OrderDual.toDual ∘ f ∘ ⇑Orde
rDu…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `OrderDual.toDual_lt_toDual`：toDual_lt_toDual [LT α] {a b : α} : toDual a
 < toDual b ↔ b < a
-/
theorem DenseRange.exists_seq_strictAnti_tendsto_of_lt {β : Type*} [LinearOrder β]
    [DenselyOrdered α] [FirstCountableTopology α] {f : β → α} {x y : α} (hf : DenseRange f)
    (hmono : Monotone f) (hlt : x < y) :
    ∃ u : ℕ → β, StrictAnti u ∧ (∀ n, f (u n) ∈ Ioo x y) ∧ Tendsto (f ∘ u) atTop (𝓝 x) := by
  simpa using! hf.exists_seq_strictMono_tendsto_of_lt (α := αᵒᵈ) (β := βᵒᵈ) hmono.dual
    (OrderDual.toDual_lt_toDual.2 hlt)
/-
**DenseRange.exists_seq_strictAnti_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DenseRange.exists_seq_strictAnti_tendsto {β : Type*} [LinearOrder β] [Dens
elyOrdered α] [NoMaxOrder α] [FirstCountableTopology α] {f : β -> α} (hf : Dense
Range f) (hmono : Monotone f) (x : α) : exists u : Nat -> β, StrictAnti u ∧ (for
all n, f (u n) in Ioi x) ∧ Tendsto (f ∘ u) atTop (𝓝 x)
参数：hf : DenseRange f；hmono : Monotone f；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DenseRange.exists_seq_strictMono_tendsto`：DenseRange.exists_seq_strictMo
no_tendsto {β : Type*} [LinearOrder β] [DenselyOrdered α] [NoMinOrder α] [FirstC
ountableTopology α] {f : β -> …
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `instFirstCountableTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalS
pace α] [h : FirstCountableTopology α], FirstCountableTopology αᵒᵈ
· 使用定理 `Monotone.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1 :
 Preorder β] {f : α → β},   Monotone f → Monotone (⇑OrderDual.toDual ∘ f ∘ ⇑Orde
rDu…
-/
theorem DenseRange.exists_seq_strictAnti_tendsto {β : Type*} [LinearOrder β] [DenselyOrdered α]
    [NoMaxOrder α] [FirstCountableTopology α] {f : β → α} (hf : DenseRange f) (hmono : Monotone f)
    (x : α) :
    ∃ u : ℕ → β, StrictAnti u ∧ (∀ n, f (u n) ∈ Ioi x) ∧ Tendsto (f ∘ u) atTop (𝓝 x) :=
  hf.exists_seq_strictMono_tendsto (α := αᵒᵈ) (β := βᵒᵈ) hmono.dual x
/-
**eventually_le_const_iff_forall_gt_eventually_lt_const** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：eventually_le_const_iff_forall_gt_eventually_lt_const [FirstCountableTopol
ogy α] {l : Filter γ} [CountableInterFilter l] {f : γ -> α} {a : α} : (forallᶠ x
 in l, f x <= a) ↔ forall b, a < b -> forallᶠ x in l, f x < b where mp h c hbc
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `exists_glb_Ioi`：∀ {γ : Type u_3} [inst : LinearOrder γ] (i : γ), ∃ j, Is
GLB (Set.Ioi i) j
· 使用定理 `glb_Ioi_eq_self_or_Ioi_eq_Ici`：∀ {γ : Type u_3} [inst : PartialOrder γ] 
{j : γ} (i : γ), IsGLB (Set.Ioi i) j → j = i ∨ Set.Ioi i = Set.Ici j
· 使用定理 `isTop_or_exists_gt`：isTop_or_exists_gt [IsDirectedOrder α] (a : α) : IsT
op a ∨ exists b, a < b
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `IsGLB.exists_seq_antitone_tendsto`：IsGLB.exists_seq_antitone_tendsto {t 
: Set α} {x : α} [IsCountablyGenerated (𝓝 x)] (htx : IsGLB t x) (ht : t.Nonempty
) : exists u : Nat -> α…
· 使用定理 `FirstCountableTopology.nhds_generated_countable`：∀ {α : Type u} {t : Top
ologicalSpace α} [self : FirstCountableTopology α] (a : α), (nhds a).IsCountably
Generated
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eventually_countable_forall`：eventually_countable_forall [Countable ι] {
p : α -> ι -> Prop} : (forallᶠ x in l, forall i, p x i) ↔ forall i, forallᶠ x in
 l, p x i
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ge_of_tendsto`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] [
inst_1 : Preorder α] [ClosedIciTopology α] {f : β → α}   {a b : α} {x : Filter β
} […
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `compl_inj_iff`：compl_inj_iff : xᶜ = yᶜ ↔ x = y
· 使用定理 `Set.compl_Iio`：compl_Iio : (Iio a)ᶜ = Ici a
· 使用定理 `Set.compl_Iic`：compl_Iic : (Iic a)ᶜ = Ioi a
-/
theorem eventually_le_const_iff_forall_gt_eventually_lt_const [FirstCountableTopology α]
    {l : Filter γ} [CountableInterFilter l] {f : γ → α} {a : α} :
    (∀ᶠ x in l, f x ≤ a) ↔ ∀ b, a < b → ∀ᶠ x in l, f x < b where
  mp h c hbc := h.mono <| fun x hx ↦ lt_of_le_of_lt hx hbc
  mpr h := by
    rcases exists_glb_Ioi a with ⟨d, hd⟩
    obtain rfl | H0 := glb_Ioi_eq_self_or_Ioi_eq_Ici _ hd
    · obtain h | _ := isTop_or_exists_gt d
      · exact .of_forall (fun _ ↦ h _)
      obtain ⟨u, -, -, hu_tt, hu_gt⟩ := hd.exists_seq_antitone_tendsto (by simpa)
      replace h := fun n ↦ h (u n) (by grind)
      rw [← eventually_countable_forall] at h
      filter_upwards [h] with x hx
      exact ge_of_tendsto hu_tt <| .of_forall <| fun n ↦ le_of_lt <| hx n
    · specialize h d <| by simp [← Set.mem_Ioi, H0]
      filter_upwards [h] with x hx
      rw [← Set.compl_Iic, ← Set.compl_Iio, compl_inj_iff] at H0
      simpa [← Set.mem_Iic, ← Set.mem_Iio, H0] using hx
/-
**eventually_const_le_iff_forall_lt_eventually_const_lt** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：eventually_const_le_iff_forall_lt_eventually_const_lt [FirstCountableTopol
ogy α] {l : Filter γ} [CountableInterFilter l] {f : γ -> α} {a : α} : (forallᶠ x
 in l, a <= f x) ↔ forall b, b < a -> forallᶠ x in l, b < f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eventually_le_const_iff_forall_gt_eventually_lt_const`：eventually_le_con
st_iff_forall_gt_eventually_lt_const [FirstCountableTopology α] {l : Filter γ} [
CountableInterFilter l] {f : γ -> α} {a : α…
· 使用定理 `instOrderTopologyOrderDual`：∀ {α : Type u} [ts : TopologicalSpace α] [in
st : Preorder α] [t : OrderTopology α], OrderTopology αᵒᵈ
· 使用定理 `instFirstCountableTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalS
pace α] [h : FirstCountableTopology α], FirstCountableTopology αᵒᵈ
-/
theorem eventually_const_le_iff_forall_lt_eventually_const_lt [FirstCountableTopology α]
    {l : Filter γ} [CountableInterFilter l] {f : γ → α} {a : α} :
    (∀ᶠ x in l, a ≤ f x) ↔ ∀ b, b < a → ∀ᶠ x in l, b < f x :=
  eventually_le_const_iff_forall_gt_eventually_lt_const (α := αᵒᵈ)

end OrderTopology

