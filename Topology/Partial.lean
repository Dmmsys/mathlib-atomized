/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import Mathlib.Order.Filter.Partial
public import Mathlib.Topology.Neighborhoods

/-!
# Partial functions and topological spaces

In this file we prove properties of `Filter.PTendsto` etc. in topological spaces. We also introduce
`PContinuous`, a version of `Continuous` for partially defined functions.
-/

@[expose] public section


open Filter

open Topology

variable {X Y : Type*} [TopologicalSpace X]

/-
**rtendsto_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rtendsto_nhds {r : SetRel Y X} {l : Filter Y} {x : X} : RTendsto r l (𝓝 x)
 ↔ forall s, IsOpen s -> x in s -> r.core s in l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `all_mem_nhds_filter`：all_mem_nhds_filter (x : X) (f : Set X -> Set α) (h
f : forall s t, s subseteq t -> f s subseteq f t) (l : Filter α) : (forall s in 
𝓝 x, f s …
-/
theorem rtendsto_nhds {r : SetRel Y X} {l : Filter Y} {x : X} :
    RTendsto r l (𝓝 x) ↔ ∀ s, IsOpen s → x ∈ s → r.core s ∈ l :=
  all_mem_nhds_filter _ _ (fun _s _t => id) _
/-
**rtendsto'_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] {r : SetRel Y 
X} {l : Filter Y} {x : X},   Filter.RTendsto' r l (nhds x) ↔ ∀ (s : Set X), IsOp
en s → x ∈ s → r.preimage s ∈ l
参数：nhds x；s : Set X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.rtendsto'_def`：∀ {α : Type u} {β : Type v} (r : SetRel α β) (l₁ :
 Filter α) (l₂ : Filter β),   Filter.RTendsto' r l₁ l₂ ↔ ∀ s ∈ l₂, r.preimage s 
∈ l₁
· 使用定理 `all_mem_nhds_filter`：all_mem_nhds_filter (x : X) (f : Set X -> Set α) (h
f : forall s t, s subseteq t -> f s subseteq f t) (l : Filter α) : (forall s in 
𝓝 x, f s …
· 使用引理 `SetRel.preimage_mono`：preimage_mono : Monotone R.preimage
-/
theorem rtendsto'_nhds {r : SetRel Y X} {l : Filter Y} {x : X} :
    RTendsto' r l (𝓝 x) ↔ ∀ s, IsOpen s → x ∈ s → r.preimage s ∈ l := by
  rw [rtendsto'_def]
  apply all_mem_nhds_filter
  apply SetRel.preimage_mono
/-
**ptendsto_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ptendsto_nhds {f : Y ->. X} {l : Filter Y} {x : X} : PTendsto f l (𝓝 x) ↔ 
forall s, IsOpen s -> x in s -> f.core s in l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `rtendsto_nhds`：rtendsto_nhds {r : SetRel Y X} {l : Filter Y} {x : X} : R
Tendsto r l (𝓝 x) ↔ forall s, IsOpen s -> x in s -> r.core s in l
-/
theorem ptendsto_nhds {f : Y →. X} {l : Filter Y} {x : X} :
    PTendsto f l (𝓝 x) ↔ ∀ s, IsOpen s → x ∈ s → f.core s ∈ l :=
  rtendsto_nhds
/-
**ptendsto'_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] {f : Y →. X} {
l : Filter Y} {x : X},   Filter.PTendsto' f l (nhds x) ↔ ∀ (s : Set X), IsOpen s
 → x ∈ s → f.preimage s ∈ l
参数：nhds x；s : Set X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `rtendsto'_nhds`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace
 X] {r : SetRel Y X} {l : Filter Y} {x : X},   Filter.RTendsto' r l (nhds x) ↔ ∀
 (s …
-/
theorem ptendsto'_nhds {f : Y →. X} {l : Filter Y} {x : X} :
    PTendsto' f l (𝓝 x) ↔ ∀ s, IsOpen s → x ∈ s → f.preimage s ∈ l :=
  rtendsto'_nhds

/-! ### Continuity and partial functions -/


variable [TopologicalSpace Y]

/-- Continuity of a partial function -/
/-
**PContinuous** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：PContinuous (f : X ->. Y)
参数：f : X ->. Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Continuity of a partial function
-/
def PContinuous (f : X →. Y) :=
  ∀ s, IsOpen s → IsOpen (f.preimage s)
/-
**open_dom_of_pcontinuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：open_dom_of_pcontinuous {f : X ->. Y} (h : PContinuous f) : IsOpen f.Dom
参数：h : PContinuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PFun.preimage_univ`：preimage_univ : f.preimage Set.univ = f.Dom
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
-/
theorem open_dom_of_pcontinuous {f : X →. Y} (h : PContinuous f) : IsOpen f.Dom := by
  rw [← PFun.preimage_univ]; exact h _ isOpen_univ
/-
**pcontinuous_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pcontinuous_iff' {f : X ->. Y} : PContinuous f ↔ forall {x y} (_ : y in f 
x), PTendsto' f (𝓝 x) (𝓝 y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `PFun.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f.p
reimage s subseteq f.preimage t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_iff_nhds`：isOpen_iff_nhds : IsOpen s ↔ forall x in s, 𝓝 x <= 𝓟 s
· 使用定理 `Filter.mem_principal`：∀ {α : Type u_1} {s t : Set α}, s ∈ Filter.princip
al t ↔ t ⊆ s
· 使用定理 `Filter.mem_of_superset._gcongr_1`：∀ {α : Type u_1} {f : Filter α} {x y :
 Set α}, x ⊆ y → x ∈ f → y ∈ f
· 使用定理 `Filter.ptendsto'_def`：∀ {α : Type u} {β : Type v} (f : α →. β) (l₁ : Fil
ter α) (l₂ : Filter β),   Filter.PTendsto' f l₁ l₂ ↔ ∀ s ∈ l₂, f.preimage s ∈ l₁
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
-/
theorem pcontinuous_iff' {f : X →. Y} :
    PContinuous f ↔ ∀ {x y} (_ : y ∈ f x), PTendsto' f (𝓝 x) (𝓝 y) := by
  constructor
  · intro h x y h'
    simp only [ptendsto'_def, mem_nhds_iff]
    rintro s ⟨t, tsubs, opent, yt⟩
    exact ⟨f.preimage t, PFun.preimage_mono _ tsubs, h _ opent, ⟨y, yt, h'⟩⟩
  intro hf s os
  rw [isOpen_iff_nhds]
  rintro x ⟨y, ys, fxy⟩ t
  rw [mem_principal]
  intro (h : f.preimage s ⊆ t)
  grw [← h]
  have h' : ∀ s ∈ 𝓝 y, f.preimage s ∈ 𝓝 x := by
    intro s hs
    have : PTendsto' f (𝓝 x) (𝓝 y) := hf fxy
    rw [ptendsto'_def] at this
    exact this s hs
  change f.preimage s ∈ 𝓝 x
  apply h'
  rw [mem_nhds_iff]
  exact ⟨s, Set.Subset.refl _, os, ys⟩
/-
**continuousWithinAt_iff_ptendsto_res** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_iff_ptendsto_res (f : X -> Y) {x : X} {s : Set X} : Con
tinuousWithinAt f s x ↔ PTendsto (PFun.res f s) (𝓝 x) (𝓝 (f x))
参数：f : X -> Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_iff_ptendsto`：tendsto_iff_ptendsto (l₁ : Filter α) (l₂ : 
Filter β) (s : Set α) (f : α -> β) : Tendsto f (l₁ ⊓ 𝓟 s) l₂ ↔ PTendsto (PFun.re
s f s) l₁ l₂
-/
theorem continuousWithinAt_iff_ptendsto_res (f : X → Y) {x : X} {s : Set X} :
    ContinuousWithinAt f s x ↔ PTendsto (PFun.res f s) (𝓝 x) (𝓝 (f x)) :=
  tendsto_iff_ptendsto _ _ _ _
