/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
module

public import Mathlib.Order.Filter.Ultrafilter.Basic
public import Mathlib.Topology.Continuous

/-! # Characterization of basic topological properties in terms of ultrafilters -/

public section

open Set Filter Topology

universe u v w x

variable {X : Type u} {Y : Type v} {ι : Sort w} {α β : Type*} {x : X} {s s₁ s₂ t : Set X}
    {p p₁ p₂ : X → Prop} [TopologicalSpace X] [TopologicalSpace Y] {F : Filter α} {u : α → X}

/-
**Ultrafilter.clusterPt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ultrafilter.clusterPt_iff {f : Ultrafilter X} : ClusterPt x f ↔ ↑f <= 𝓝 x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ultrafilter.le_of_inf_neBot'`：le_of_inf_neBot' (f : Ultrafilter α) {g : 
Filter α} (hg : NeBot (g ⊓ f)) : ↑f <= g
· 使用定理 `ClusterPt.of_le_nhds`：ClusterPt.of_le_nhds {f : Filter X} (H : f <= 𝓝 x)
 [NeBot f] : ClusterPt x f
-/
theorem Ultrafilter.clusterPt_iff {f : Ultrafilter X} : ClusterPt x f ↔ ↑f ≤ 𝓝 x :=
  ⟨f.le_of_inf_neBot', fun h => ClusterPt.of_le_nhds h⟩
/-
**clusterPt_iff_ultrafilter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：clusterPt_iff_ultrafilter {f : Filter X} : ClusterPt x f ↔ exists u : Ultr
afilter X, u <= f ∧ u <= 𝓝 x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem clusterPt_iff_ultrafilter {f : Filter X} : ClusterPt x f ↔
    ∃ u : Ultrafilter X, u ≤ f ∧ u ≤ 𝓝 x := by
  simp_rw [ClusterPt, ← le_inf_iff, exists_ultrafilter_iff, inf_comm]
/-
**mapClusterPt_iff_ultrafilter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mapClusterPt_iff_ultrafilter : MapClusterPt x F u ↔ exists U : Ultrafilter
 α, U <= F ∧ Tendsto u U (𝓝 x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mapClusterPt_iff_ultrafilter :
    MapClusterPt x F u ↔ ∃ U : Ultrafilter α, U ≤ F ∧ Tendsto u U (𝓝 x) := by
  simp_rw [MapClusterPt, ClusterPt, ← Filter.push_pull', map_neBot_iff, tendsto_iff_comap,
    ← le_inf_iff, exists_ultrafilter_iff, inf_comm]
/-
**isOpen_iff_ultrafilter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_iff_ultrafilter : IsOpen s ↔ forall x in s, forall (l : Ultrafilter
 X), ↑l <= 𝓝 x -> s in l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isOpen_iff_ultrafilter :
    IsOpen s ↔ ∀ x ∈ s, ∀ (l : Ultrafilter X), ↑l ≤ 𝓝 x → s ∈ l := by
  simp_rw [isOpen_iff_mem_nhds, ← mem_iff_ultrafilter]

/-- `x` belongs to the closure of `s` if and only if some ultrafilter
  supported on `s` converges to `x`. -/
/-
**mem_closure_iff_ultrafilter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_closure_iff_ultrafilter : x in closure s ↔ exists u : Ultrafilter X, s
 in u ∧ ↑u <= 𝓝 x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `closure_eq_cluster_pts`：closure_eq_cluster_pts : closure s = { a | Clust
erPt a (𝓟 s) }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`x` belongs to the closure of `s` if and only if some ultrafilter
  supported on `s` converges to `x`.
-/
theorem mem_closure_iff_ultrafilter :
    x ∈ closure s ↔ ∃ u : Ultrafilter X, s ∈ u ∧ ↑u ≤ 𝓝 x := by
  simp [closure_eq_cluster_pts, ClusterPt, ← exists_ultrafilter_iff, and_comm]
/-
**isClosed_iff_ultrafilter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_iff_ultrafilter : IsClosed s ↔ forall x, forall u : Ultrafilter X
, ↑u <= 𝓝 x -> s in u -> x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isClosed_iff_ultrafilter : IsClosed s ↔
    ∀ x, ∀ u : Ultrafilter X, ↑u ≤ 𝓝 x → s ∈ u → x ∈ s := by
  simp [isClosed_iff_clusterPt, ClusterPt, ← exists_ultrafilter_iff]

variable {f : X → Y}
/-
**continuousAt_iff_ultrafilter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_iff_ultrafilter : ContinuousAt f x ↔ forall g : Ultrafilter X
, ↑g <= 𝓝 x -> Tendsto f g (𝓝 (f x))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_iff_ultrafilter`：tendsto_iff_ultrafilter (f : α -> β) (l₁
 : Filter α) (l₂ : Filter β) : Tendsto f l₁ l₂ ↔ forall g : Ultrafilter α, ↑g <=
 l₁ -> Tendsto f g l…
-/
theorem continuousAt_iff_ultrafilter :
    ContinuousAt f x ↔ ∀ g : Ultrafilter X, ↑g ≤ 𝓝 x → Tendsto f g (𝓝 (f x)) :=
  tendsto_iff_ultrafilter f (𝓝 x) (𝓝 (f x))
/-
**continuous_iff_ultrafilter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_iff_ultrafilter : Continuous f ↔ forall (x) (g : Ultrafilter X)
, ↑g <= 𝓝 x -> Tendsto f g (𝓝 (f x))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuous_iff_ultrafilter :
    Continuous f ↔ ∀ (x) (g : Ultrafilter X), ↑g ≤ 𝓝 x → Tendsto f g (𝓝 (f x)) := by
  simp only [continuous_iff_continuousAt, continuousAt_iff_ultrafilter]
