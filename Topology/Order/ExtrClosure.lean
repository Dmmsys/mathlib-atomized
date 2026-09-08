/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.Order.LocalExtr

/-!
# Maximum/minimum on the closure of a set

In this file we prove several versions of the following statement: if `f : X → Y` has a (local or
not) maximum (or minimum) on a set `s` at a point `a` and is continuous on the closure of `s`, then
`f` has an extremum of the same type on `Closure s` at `a`.
-/

public section


open Filter Set

open Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Preorder Y]
  [OrderClosedTopology Y] {f : X → Y} {s : Set X} {a : X}

/-
**IsMaxOn.closure** 是 Mathlib 中的一个定理，位于命名空间 `IsMaxOn`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [inst_2 : Preorder Y]   [OrderClosedTopology Y] {f : X → Y} {s :
 Set X} {a : X},   IsMaxOn f s a → ContinuousOn f (closure s) → IsMaxOn f (closu
re s) a
参数：closure s；closure s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.closure_le`：ContinuousWithinAt.closure_le [Topologica
lSpace β] {f g : β -> α} {s : Set β} {x : β} (hx : x in closure s) (hf : Continu
ousWithinAt f s x) …
· 使用定理 `ContinuousWithinAt.mono`：ContinuousWithinAt.mono (h : ContinuousWithinAt
 f t x) (hs : s subseteq t) : ContinuousWithinAt f s x
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `continuousWithinAt_const`：continuousWithinAt_const {b : β} {s : Set α} {
x : α} : ContinuousWithinAt (fun _ : α => b) s x
-/
protected theorem IsMaxOn.closure (h : IsMaxOn f s a) (hc : ContinuousOn f (closure s)) :
    IsMaxOn f (closure s) a := fun x hx =>
  ContinuousWithinAt.closure_le hx ((hc x hx).mono subset_closure) continuousWithinAt_const h
/-
**IsMinOn.closure** 是 Mathlib 中的一个定理，位于命名空间 `IsMinOn`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [inst_2 : Preorder Y]   [OrderClosedTopology Y] {f : X → Y} {s :
 Set X} {a : X},   IsMinOn f s a → ContinuousOn f (closure s) → IsMinOn f (closu
re s) a
参数：closure s；closure s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsMaxOn.closure`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpac
e X] [inst_1 : TopologicalSpace Y] [inst_2 : Preorder Y]   [OrderClosedTopology 
Y] {f…
· 使用定理 `instOrderClosedTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpac
e α] [inst_1 : Preorder α] [t : OrderClosedTopology α], OrderClosedTopology αᵒᵈ
· 使用定理 `IsMinOn.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder β] {f : α → β
} {s : Set α} {a : α},   IsMinOn f s a → IsMaxOn (⇑OrderDual.toDual ∘ f) s a
-/
protected theorem IsMinOn.closure (h : IsMinOn f s a) (hc : ContinuousOn f (closure s)) :
    IsMinOn f (closure s) a :=
  h.dual.closure hc
/-
**IsExtrOn.closure** 是 Mathlib 中的一个定理，位于命名空间 `IsExtrOn`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [inst_2 : Preorder Y]   [OrderClosedTopology Y] {f : X → Y} {s :
 Set X} {a : X},   IsExtrOn f s a → ContinuousOn f (closure s) → IsExtrOn f (clo
sure s) a
参数：closure s；closure s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsExtrOn.elim`：IsExtrOn.elim {p : Prop} : IsExtrOn f s a -> (IsMinOn f s
 a -> p) -> (IsMaxOn f s a -> p) -> p
· 使用定理 `IsMinOn.closure`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpac
e X] [inst_1 : TopologicalSpace Y] [inst_2 : Preorder Y]   [OrderClosedTopology 
Y] {f…
· 使用定理 `IsMaxOn.closure`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpac
e X] [inst_1 : TopologicalSpace Y] [inst_2 : Preorder Y]   [OrderClosedTopology 
Y] {f…
-/
protected theorem IsExtrOn.closure (h : IsExtrOn f s a) (hc : ContinuousOn f (closure s)) :
    IsExtrOn f (closure s) a :=
  h.elim (fun h => Or.inl <| h.closure hc) fun h => Or.inr <| h.closure hc
/-
**IsLocalMaxOn.closure** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalMaxOn`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [inst_2 : Preorder Y]   [OrderClosedTopology Y] {f : X → Y} {s :
 Set X} {a : X},   IsLocalMaxOn f s a → ContinuousOn f (closure s) → IsLocalMaxO
n f (closure s) a
参数：closure s；closure s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhdsWithin`：mem_nhdsWithin {t : Set α} {a : α} {s : Set α} : t in 𝓝[
s] a ↔ exists u, IsOpen u ∧ a in u ∧ u inter s subseteq t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ContinuousWithinAt.closure_le`：ContinuousWithinAt.closure_le [Topologica
lSpace β] {f g : β -> α} {s : Set β} {x : β} (hx : x in closure s) (hf : Continu
ousWithinAt f s x) …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_closure_iff_nhdsWithin_neBot`：mem_closure_iff_nhdsWithin_neBot : x i
n closure s ↔ NeBot (𝓝[s] x)
· 使用定理 `nhdsWithin_inter_of_mem`：nhdsWithin_inter_of_mem {a : α} {s t : Set α} (
h : s in 𝓝[t] a) : 𝓝[s inter t] a = 𝓝[t] a
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousWithinAt.mono`：ContinuousWithinAt.mono (h : ContinuousWithinAt
 f t x) (hs : s subseteq t) : ContinuousWithinAt f s x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `continuousWithinAt_const`：continuousWithinAt_const {b : β} {s : Set α} {
x : α} : ContinuousWithinAt (fun _ : α => b) s x
-/
protected theorem IsLocalMaxOn.closure (h : IsLocalMaxOn f s a) (hc : ContinuousOn f (closure s)) :
    IsLocalMaxOn f (closure s) a := by
  rcases mem_nhdsWithin.1 h with ⟨U, Uo, aU, hU⟩
  refine mem_nhdsWithin.2 ⟨U, Uo, aU, ?_⟩
  rintro x ⟨hxU, hxs⟩
  refine ContinuousWithinAt.closure_le ?_ ?_ continuousWithinAt_const hU
  · rwa [mem_closure_iff_nhdsWithin_neBot, nhdsWithin_inter_of_mem, ←
      mem_closure_iff_nhdsWithin_neBot]
    exact nhdsWithin_le_nhds (Uo.mem_nhds hxU)
  · exact (hc _ hxs).mono (inter_subset_right.trans subset_closure)
/-
**IsLocalMinOn.closure** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalMinOn`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [inst_2 : Preorder Y]   [OrderClosedTopology Y] {f : X → Y} {s :
 Set X} {a : X},   IsLocalMinOn f s a → ContinuousOn f (closure s) → IsLocalMinO
n f (closure s) a
参数：closure s；closure s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalMaxOn.closure`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] [inst_2 : Preorder Y]   [OrderClosedTopo
logy Y] {f…
· 使用定理 `instOrderClosedTopologyOrderDual`：∀ {α : Type u} [inst : TopologicalSpac
e α] [inst_1 : Preorder α] [t : OrderClosedTopology α], OrderClosedTopology αᵒᵈ
· 使用定理 `IsMinFilter.dual`：∀ {α : Type u} {β : Type v} [inst : Preorder β] {f : α
 → β} {l : Filter α} {a : α},   IsMinFilter f l a → IsMaxFilter (⇑OrderDual.toDu
al ∘ f…
-/
protected theorem IsLocalMinOn.closure (h : IsLocalMinOn f s a) (hc : ContinuousOn f (closure s)) :
    IsLocalMinOn f (closure s) a :=
  IsLocalMaxOn.closure h.dual hc
/-
**IsLocalExtrOn.closure** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalExtrOn`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [inst_2 : Preorder Y]   [OrderClosedTopology Y] {f : X → Y} {s :
 Set X} {a : X},   IsLocalExtrOn f s a → ContinuousOn f (closure s) → IsLocalExt
rOn f (closure s) a
参数：closure s；closure s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalExtrOn.elim`：IsLocalExtrOn.elim {p : Prop} : IsLocalExtrOn f s a 
-> (IsLocalMinOn f s a -> p) -> (IsLocalMaxOn f s a -> p) -> p
· 使用定理 `IsLocalMinOn.closure`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] [inst_2 : Preorder Y]   [OrderClosedTopo
logy Y] {f…
· 使用定理 `IsLocalMaxOn.closure`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] [inst_2 : Preorder Y]   [OrderClosedTopo
logy Y] {f…
-/
protected theorem IsLocalExtrOn.closure (h : IsLocalExtrOn f s a)
    (hc : ContinuousOn f (closure s)) : IsLocalExtrOn f (closure s) a :=
  h.elim (fun h => Or.inl <| h.closure hc) fun h => Or.inr <| h.closure hc
