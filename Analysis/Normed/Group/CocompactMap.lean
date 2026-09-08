/-
Copyright (c) 2024 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.ContinuousMap.CocompactMap
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Cocompact maps in normed groups

This file gives a characterization of cocompact maps in terms of norm estimates.

## Main statements

* `CocompactMapClass.norm_le`: Every cocompact map satisfies a norm estimate
* `ContinuousMapClass.toCocompactMapClass_of_norm`: Conversely, this norm estimate implies that a
  map is cocompact.

-/

public section

open Filter Metric

variable {𝕜 E F 𝓕 : Type*}
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable {f : 𝓕}

/-
**CocompactMapClass.norm_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CocompactMapClass.norm_le [ProperSpace F] [FunLike 𝓕 E F] [CocompactMapCla
ss 𝓕 E F] (ε : Real) : exists r : Real, forall x : E, r < ‖x‖ -> ε < ‖f x‖
参数：ε : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CocompactMapClass.cocompact_tendsto`：∀ {F : Type u_1} {α : outParam (Typ
e u_2)} {β : outParam (Type u_3)} {inst : TopologicalSpace α}   {inst_1 : Topolo
gicalSpace β} {inst_2 : F…
· 使用定理 `Metric.closedBall_compl_subset_of_mem_cocompact`：closedBall_compl_subset
_of_mem_cocompact {s : Set α} (hs : s in cocompact α) (c : α) : exists (r : Real
), (Metric.closedBall c r)ᶜ subseteq …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.tendsto_def`：tendsto_def {f : α -> β} {l₁ : Filter α} {l₂ : Filte
r β} : Tendsto f l₁ l₂ ↔ forall s in l₂, f ⁻¹' s in l₁
· 使用定理 `Metric.mem_cocompact_of_closedBall_compl_subset`：mem_cocompact_of_closed
Ball_compl_subset [ProperSpace α] (c : α) (h : exists r, (closedBall c r)ᶜ subse
teq s) : s in cocompact α
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem CocompactMapClass.norm_le [ProperSpace F] [FunLike 𝓕 E F] [CocompactMapClass 𝓕 E F]
    (ε : ℝ) : ∃ r : ℝ, ∀ x : E, r < ‖x‖ → ε < ‖f x‖ := by
  have h := cocompact_tendsto f
  rw [tendsto_def] at h
  specialize h (Metric.closedBall 0 ε)ᶜ (mem_cocompact_of_closedBall_compl_subset 0 ⟨ε, rfl.subset⟩)
  rcases closedBall_compl_subset_of_mem_cocompact h 0 with ⟨r, hr⟩
  use r
  intro x hx
  suffices x ∈ f ⁻¹' (Metric.closedBall 0 ε)ᶜ by simp_all
  apply hr
  simp [hx]
/-
**Filter.tendsto_cocompact_cocompact_of_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.tendsto_cocompact_cocompact_of_norm [ProperSpace E] {f : E -> F} (h
 : forall ε : Real, exists r : Real, forall x : E, r < ‖x‖ -> ε < ‖f x‖) : Tends
to f (cocompact E) (cocompact F)
参数：h : forall ε : Real, exists r : Real, forall x : E, r < ‖x‖ -> ε < ‖f x‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.tendsto_def`：tendsto_def {f : α -> β} {l₁ : Filter α} {l₂ : Filte
r β} : Tendsto f l₁ l₂ ↔ forall s in l₂, f ⁻¹' s in l₁
· 使用定理 `Metric.closedBall_compl_subset_of_mem_cocompact`：closedBall_compl_subset
_of_mem_cocompact {s : Set α} (hs : s in cocompact α) (c : α) : exists (r : Real
), (Metric.closedBall c r)ᶜ subseteq …
· 使用定理 `Metric.mem_cocompact_of_closedBall_compl_subset`：mem_cocompact_of_closed
Ball_compl_subset [ProperSpace α] (c : α) (h : exists r, (closedBall c r)ᶜ subse
teq s) : s in cocompact α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem Filter.tendsto_cocompact_cocompact_of_norm [ProperSpace E] {f : E → F}
    (h : ∀ ε : ℝ, ∃ r : ℝ, ∀ x : E, r < ‖x‖ → ε < ‖f x‖) :
    Tendsto f (cocompact E) (cocompact F) := by
  rw [tendsto_def]
  intro s hs
  rcases closedBall_compl_subset_of_mem_cocompact hs 0 with ⟨ε, hε⟩
  rcases h ε with ⟨r, hr⟩
  apply mem_cocompact_of_closedBall_compl_subset 0
  use r
  intro x hx
  simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hx
  apply hε
  simp [hr x hx]
/-
**ContinuousMapClass.toCocompactMapClass_of_norm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMapClass.toCocompactMapClass_of_norm [ProperSpace E] [FunLike 𝓕 
E F] [ContinuousMapClass 𝓕 E F] (h : forall (f : 𝓕) (ε : Real), exists r : Real,
 forall x : E, r < ‖x‖ -> ε < ‖f x‖) : CocompactMapClass 𝓕 E F where cocompact_t
endsto
参数：h : forall (f : 𝓕) (ε : Real), exists r : Real, forall x : E, r < ‖x‖ -> ε < 
‖f x‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_cocompact_cocompact_of_norm`：Filter.tendsto_cocompact_coc
ompact_of_norm [ProperSpace E] {f : E -> F} (h : forall ε : Real, exists r : Rea
l, forall x : E, r < ‖x‖ -> ε < …
-/
theorem ContinuousMapClass.toCocompactMapClass_of_norm [ProperSpace E] [FunLike 𝓕 E F]
    [ContinuousMapClass 𝓕 E F] (h : ∀ (f : 𝓕) (ε : ℝ), ∃ r : ℝ, ∀ x : E, r < ‖x‖ → ε < ‖f x‖) :
    CocompactMapClass 𝓕 E F where
  cocompact_tendsto := (tendsto_cocompact_cocompact_of_norm <| h ·)
