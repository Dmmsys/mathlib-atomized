/-
Copyright (c) 2024 PFR contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PFR contributors
-/
module

public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Topology.Piecewise
public import Mathlib.Topology.Clopen

/-!
# Continuity of indicator functions
-/

public section

open Set
open scoped Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {f : α → β} {s : Set α} [One β]

@[to_additive]
/-
**continuous_mulIndicator** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：continuous_mulIndicator (hs : forall a in frontier s, f a = 1) (hf : Conti
nuousOn f (closure s)) : Continuous (mulIndicator s f)
参数：hs : forall a in frontier s, f a = 1；hf : ContinuousOn f (closure s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_piecewise`：continuous_piecewise [forall a, Decidable (a in s)
] (hs : forall a in frontier s, f a = g a) (hf : ContinuousOn f (closure s)) (hg
 : Continu…
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
-/
lemma continuous_mulIndicator (hs : ∀ a ∈ frontier s, f a = 1) (hf : ContinuousOn f (closure s)) :
    Continuous (mulIndicator s f) := by
  classical exact continuous_piecewise hs hf continuousOn_const

@[to_additive]
/-
**Continuous.mulIndicator** 是 Mathlib 中的一个定理，位于命名空间 `Continuous`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace α] [inst_1 : Topo
logicalSpace β] {f : α → β} {s : Set α}   [inst_2 : One β], (∀ a ∈ frontier s, f
 a = 1) → Continuous f → Continuous (s.mulIndicator f)
参数：∀ a ∈ frontier s, f a = 1；s.mulIndicator f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.piecewise`：Continuous.piecewise [forall a, Decidable (a in s)
] (hs : forall a in frontier s, f a = g a) (hf : Continuous f) (hg : Continuous 
g) : Conti…
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
-/
protected lemma Continuous.mulIndicator (hs : ∀ a ∈ frontier s, f a = 1) (hf : Continuous f) :
    Continuous (mulIndicator s f) := by
  classical exact hf.piecewise hs continuous_const

@[to_additive]
/-
**ContinuousOn.continuousAt_mulIndicator** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.continuousAt_mulIndicator (hf : ContinuousOn f (interior s)) 
{x : α} (hx : x ∉ frontier s) : ContinuousAt (s.mulIndicator f) x
参数：hf : ContinuousOn f (interior s)；hx : x ∉ frontier s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `compl_frontier_eq_union_interior`：compl_frontier_eq_union_interior : (fr
ontier s)ᶜ = interior s union interior sᶜ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_compl_iff`：mem_compl_iff (s : Set α) (x : α) : x in sᶜ ↔ x ∉ s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `interior_interior`：interior_interior : interior (interior s) = interior 
s
· 使用定理 `ContinuousAt.congr`：ContinuousAt.congr {g : X -> Y} (hf : ContinuousAt f
 x) (h : f =ᶠ[𝓝 x] g) : ContinuousAt g x
· 使用定理 `ContinuousOn.continuousAt`：ContinuousOn.continuousAt (h : ContinuousOn f
 s) (hx : s in 𝓝 x) : ContinuousAt f x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventuallyEq_iff_exists_mem`：eventuallyEq_iff_exists_mem {l : Fil
ter α} {f g : α -> β} : f =ᶠ[l] g ↔ exists s in l, EqOn f g s
· 使用定理 `Set.EqOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f₁ f₂ : 
α → β}, s₁ ⊆ s₂ → Set.EqOn f₁ f₂ s₂ → Set.EqOn f₁ f₂ s₁
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `Set.EqOn.symm`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α → 
β}, Set.EqOn f₁ f₂ s → Set.EqOn f₂ f₁ s
· 使用引理 `Set.eqOn_mulIndicator`：eqOn_mulIndicator : EqOn (mulIndicator s f) f s
· 使用定理 `continuousAt_const`：continuousAt_const : ContinuousAt (fun _ : X => y) x
· 使用引理 `Set.eqOn_mulIndicator'`：eqOn_mulIndicator' : EqOn (mulIndicator s f) 1 s
ᶜ
-/
theorem ContinuousOn.continuousAt_mulIndicator (hf : ContinuousOn f (interior s)) {x : α}
    (hx : x ∉ frontier s) :
    ContinuousAt (s.mulIndicator f) x := by
  rw [← Set.mem_compl_iff, compl_frontier_eq_union_interior] at hx
  obtain h | h := hx
  · have hs : interior s ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp (by rwa [interior_interior])
    exact ContinuousAt.congr (hf.continuousAt hs) <| Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨interior s, hs, Set.eqOn_mulIndicator.symm.mono interior_subset⟩
  · exact ContinuousAt.congr continuousAt_const <| Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨sᶜ, mem_interior_iff_mem_nhds.mp h, Set.eqOn_mulIndicator'.symm⟩

@[to_additive]
/-
**IsClopen.continuous_mulIndicator** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsClopen.continuous_mulIndicator (hs : IsClopen s) (hf : Continuous f) : C
ontinuous (s.mulIndicator f)
参数：hs : IsClopen s；hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.mulIndicator`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolog
icalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α}   [inst_2 : O
ne β], (∀ a ∈…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isClopen_iff_frontier_eq_empty`：isClopen_iff_frontier_eq_empty : IsClope
n s ↔ frontier s = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma IsClopen.continuous_mulIndicator (hs : IsClopen s) (hf : Continuous f) :
    Continuous (s.mulIndicator f) :=
  hf.mulIndicator (by simp [isClopen_iff_frontier_eq_empty.mp hs])
