/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.NhdsWithin

/-!
# Neighborhoods and continuity relative to a subset

This file develops API on the relative versions

* `ContinuousOn`        of `Continuous`
* `ContinuousWithinAt`  of `ContinuousAt`

related to continuity, which are defined in previous definition files.
Their basic properties studied in this file include the relationships between
these restricted notions and the corresponding notions for the subtype
equipped with the subspace topology.

-/

public section

open Set Filter Function Topology

variable {α β γ δ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
  [TopologicalSpace δ] {f g : α → β} {s s' s₁ t : Set α} {x : α}

/-!
## `ContinuousWithinAt`
-/

/-- If a function is continuous within `s` at `x`, then it tends to `f x` within `s` by definition.
We register this fact for use with the dot notation, especially to use `Filter.Tendsto.comp` as
`ContinuousWithinAt.comp` will have a different meaning. -/
/-
**ContinuousWithinAt.tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.tendsto (h : ContinuousWithinAt f s x) : Tendsto f (𝓝[s
] x) (𝓝 (f x))
参数：h : ContinuousWithinAt f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a function is continuous within `s` at `x`, then it tends to `f x` within `s`
 by definition.
We register this fact for use with the dot notation, especially to use `Filter.T
endsto.comp` as
`ContinuousWithinAt.comp` will have a different meaning.
-/
theorem ContinuousWithinAt.tendsto (h : ContinuousWithinAt f s x) :
    Tendsto f (𝓝[s] x) (𝓝 (f x)) :=
  h
/-
**continuousWithinAt_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_univ (f : α -> β) (x : α) : ContinuousWithinAt f Set.un
iv x ↔ ContinuousAt f x
参数：f : α -> β；x : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (x : X),   ContinuousAt f x = F
ilter.T…
· 使用定理 `ContinuousWithinAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (s : Set X)   (x : X), Co
ntinuousWithi…
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem continuousWithinAt_univ (f : α → β) (x : α) :
    ContinuousWithinAt f Set.univ x ↔ ContinuousAt f x := by
  rw [ContinuousAt, ContinuousWithinAt, nhdsWithin_univ]

@[simp]
/-
**continuousOn_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_univ {f : α -> β} : ContinuousOn f univ ↔ Continuous f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuousOn_univ {f : α → β} : ContinuousOn f univ ↔ Continuous f := by
  simp [continuous_iff_continuousAt, ContinuousOn, ContinuousAt, ContinuousWithinAt,
    nhdsWithin_univ]
/-
**continuousWithinAt_iff_continuousAt_domRestrict** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_iff_continuousAt_domRestrict (f : α -> β) {x : α} {s : 
Set α} (h : x in s) : ContinuousWithinAt f s x ↔ ContinuousAt (s.domRestrict f) 
⟨x, h⟩
参数：f : α -> β；h : x in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhdsWithin_iff_subtype`：tendsto_nhdsWithin_iff_subtype {s : Set 
α} {a : α} (h : a in s) (f : α -> β) (l : Filter β) : Tendsto f (𝓝[s] a) l ↔ Ten
dsto (s.domRestrict …
-/
theorem continuousWithinAt_iff_continuousAt_domRestrict (f : α → β) {x : α} {s : Set α}
    (h : x ∈ s) : ContinuousWithinAt f s x ↔ ContinuousAt (s.domRestrict f) ⟨x, h⟩ :=
  tendsto_nhdsWithin_iff_subtype h f _

@[deprecated (since := "2026-07-19")] alias continuousWithinAt_iff_continuousAt_restrict :=
  continuousWithinAt_iff_continuousAt_domRestrict
/-
**ContinuousWithinAt.tendsto_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.tendsto_nhdsWithin {t : Set β} (h : ContinuousWithinAt 
f s x) (ht : MapsTo f s t) : Tendsto f (𝓝[s] x) (𝓝[t] f x)
参数：h : ContinuousWithinAt f s x；ht : MapsTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_inf`：tendsto_inf {f : α -> β} {x : Filter α} {y₁ y₂ : Fil
ter β} : Tendsto f x (y₁ ⊓ y₂) ↔ Tendsto f x y₁ ∧ Tendsto f x y₂
· 使用定理 `Filter.tendsto_principal`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l
 : Filter α} {s : Set β},   Filter.Tendsto f l (Filter.principal s) ↔ ∀ᶠ (a : α)
 in l, f a ∈ s
· 使用定理 `Filter.mem_inf_of_right`：mem_inf_of_right {f g : Filter α} {s : Set α} (
h : s in g) : s in f ⊓ g
· 使用定理 `Filter.mem_principal`：∀ {α : Type u_1} {s t : Set α}, s ∈ Filter.princip
al t ↔ t ⊆ s
-/
theorem ContinuousWithinAt.tendsto_nhdsWithin {t : Set β}
    (h : ContinuousWithinAt f s x) (ht : MapsTo f s t) :
    Tendsto f (𝓝[s] x) (𝓝[t] f x) :=
  tendsto_inf.2 ⟨h, tendsto_principal.2 <| mem_inf_of_right <| mem_principal.2 <| ht⟩
/-
**ContinuousWithinAt.tendsto_nhdsWithin_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.tendsto_nhdsWithin_image (h : ContinuousWithinAt f s x)
 : Tendsto f (𝓝[s] x) (𝓝[f '' s] f x)
参数：h : ContinuousWithinAt f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.tendsto_nhdsWithin`：ContinuousWithinAt.tendsto_nhdsWi
thin {t : Set β} (h : ContinuousWithinAt f s x) (ht : MapsTo f s t) : Tendsto f 
(𝓝[s] x) (𝓝[t] f x)
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
-/
theorem ContinuousWithinAt.tendsto_nhdsWithin_image (h : ContinuousWithinAt f s x) :
    Tendsto f (𝓝[s] x) (𝓝[f '' s] f x) :=
  h.tendsto_nhdsWithin (mapsTo_image _ _)
/-
**nhdsWithin_le_comap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_le_comap (ctsf : ContinuousWithinAt f s x) : 𝓝[s] x <= comap f 
(𝓝[f '' s] f x)
参数：ctsf : ContinuousWithinAt f s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.le_comap`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁
 : Filter α} {l₂ : Filter β},   Filter.Tendsto f l₁ l₂ → l₁ ≤ Filter.comap f l₂
· 使用定理 `ContinuousWithinAt.tendsto_nhdsWithin_image`：ContinuousWithinAt.tendsto_
nhdsWithin_image (h : ContinuousWithinAt f s x) : Tendsto f (𝓝[s] x) (𝓝[f '' s] 
f x)
-/
theorem nhdsWithin_le_comap (ctsf : ContinuousWithinAt f s x) :
    𝓝[s] x ≤ comap f (𝓝[f '' s] f x) :=
  ctsf.tendsto_nhdsWithin_image.le_comap
/-
**ContinuousWithinAt.preimage_mem_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.preimage_mem_nhdsWithin {t : Set β} (h : ContinuousWith
inAt f s x) (ht : t in 𝓝 (f x)) : f ⁻¹' t in 𝓝[s] x
参数：h : ContinuousWithinAt f s x；ht : t in 𝓝 (f x)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ContinuousWithinAt.preimage_mem_nhdsWithin {t : Set β}
    (h : ContinuousWithinAt f s x) (ht : t ∈ 𝓝 (f x)) : f ⁻¹' t ∈ 𝓝[s] x :=
  h ht
/-
**ContinuousWithinAt.preimage_mem_nhdsWithin'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.preimage_mem_nhdsWithin' {t : Set β} (h : ContinuousWit
hinAt f s x) (ht : t in 𝓝[f '' s] f x) : f ⁻¹' t in 𝓝[s] x
参数：h : ContinuousWithinAt f s x；ht : t in 𝓝[f '' s] f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.tendsto_nhdsWithin`：ContinuousWithinAt.tendsto_nhdsWi
thin {t : Set β} (h : ContinuousWithinAt f s x) (ht : MapsTo f s t) : Tendsto f 
(𝓝[s] x) (𝓝[t] f x)
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
-/
theorem ContinuousWithinAt.preimage_mem_nhdsWithin' {t : Set β}
    (h : ContinuousWithinAt f s x) (ht : t ∈ 𝓝[f '' s] f x) : f ⁻¹' t ∈ 𝓝[s] x :=
  h.tendsto_nhdsWithin (mapsTo_image _ _) ht
/-
**ContinuousWithinAt.preimage_mem_nhdsWithin''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.preimage_mem_nhdsWithin'' {y : β} {s t : Set β} (h : Co
ntinuousWithinAt f (f ⁻¹' s) x) (ht : t in 𝓝[s] y) (hxy : y = f x) : f ⁻¹' t in 
𝓝[f ⁻¹' s] x
参数：h : ContinuousWithinAt f (f ⁻¹' s) x；ht : t in 𝓝[s] y；hxy : y = f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.preimage_mem_nhdsWithin'`：ContinuousWithinAt.preimage
_mem_nhdsWithin' {t : Set β} (h : ContinuousWithinAt f s x) (ht : t in 𝓝[f '' s]
 f x) : f ⁻¹' t in 𝓝[s] x
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem ContinuousWithinAt.preimage_mem_nhdsWithin'' {y : β} {s t : Set β}
    (h : ContinuousWithinAt f (f ⁻¹' s) x) (ht : t ∈ 𝓝[s] y) (hxy : y = f x) :
    f ⁻¹' t ∈ 𝓝[f ⁻¹' s] x := by
  rw [hxy] at ht
  exact h.preimage_mem_nhdsWithin' (nhdsWithin_mono _ (image_preimage_subset f s) ht)
/-
**continuousWithinAt_of_notMem_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_of_notMem_closure (hx : x ∉ closure s) : ContinuousWith
inAt f s x
参数：hx : x ∉ closure s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousWithinAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (s : Set X)   (x : X), Co
ntinuousWithi…
· 使用定理 `Filter.not_neBot`：not_neBot {f : Filter α} : ¬f.NeBot ↔ f = ⊥
· 使用定理 `mem_closure_iff_nhdsWithin_neBot`：mem_closure_iff_nhdsWithin_neBot : x i
n closure s ↔ NeBot (𝓝[s] x)
· 使用定理 `Filter.tendsto_bot`：tendsto_bot {f : α -> β} {l : Filter β} : Tendsto f 
⊥ l
-/
theorem continuousWithinAt_of_notMem_closure (hx : x ∉ closure s) :
    ContinuousWithinAt f s x := by
  rw [mem_closure_iff_nhdsWithin_neBot, not_neBot] at hx
  rw [ContinuousWithinAt, hx]
  exact tendsto_bot

/-!
## `ContinuousOn`
-/

/-
**continuousOn_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_iff : ContinuousOn f s ↔ forall x in s, forall t : Set β, IsO
pen t -> f x in t -> exists u, IsOpen u ∧ x in u ∧ u inter s subseteq f ⁻¹' t
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
## `ContinuousOn`
-/
theorem continuousOn_iff :
    ContinuousOn f s ↔
      ∀ x ∈ s, ∀ t : Set β, IsOpen t → f x ∈ t → ∃ u, IsOpen u ∧ x ∈ u ∧ u ∩ s ⊆ f ⁻¹' t := by
  simp only [ContinuousOn, ContinuousWithinAt, tendsto_nhds, mem_nhdsWithin]
/-
**ContinuousOn.continuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.continuousWithinAt (hf : ContinuousOn f s) (hx : x in s) : Co
ntinuousWithinAt f s x
参数：hf : ContinuousOn f s；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ContinuousOn.continuousWithinAt (hf : ContinuousOn f s) (hx : x ∈ s) :
    ContinuousWithinAt f s x :=
  hf x hx
/-
**continuousOn_iff_continuous_domRestrict** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_iff_continuous_domRestrict : ContinuousOn f s ↔ Continuous (s
.domRestrict f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousOn.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (s : Set X),   ContinuousOn f s
 = ∀ x …
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuousWithinAt_iff_continuousAt_domRestrict`：continuousWithinAt_iff_
continuousAt_domRestrict (f : α -> β) {x : α} {s : Set α} (h : x in s) : Continu
ousWithinAt f s x ↔ ContinuousAt (s.d…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem continuousOn_iff_continuous_domRestrict :
    ContinuousOn f s ↔ Continuous (s.domRestrict f) := by
  rw [ContinuousOn, continuous_iff_continuousAt]; constructor
  · rintro h ⟨x, xs⟩
    exact (continuousWithinAt_iff_continuousAt_domRestrict f xs).mp (h x xs)
  intro h x xs
  exact (continuousWithinAt_iff_continuousAt_domRestrict f xs).mpr (h ⟨x, xs⟩)

alias ⟨ContinuousOn.domRestrict, _⟩ := continuousOn_iff_continuous_domRestrict

@[deprecated (since := "2026-07-19")]
alias continuousOn_iff_continuous_restrict := continuousOn_iff_continuous_domRestrict
@[deprecated (since := "2026-07-19")]
alias ContinuousOn.restrict := ContinuousOn.domRestrict
/-
**ContinuousOn.mapsToRestrict** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.mapsToRestrict {t : Set β} (hf : ContinuousOn f s) (ht : Maps
To f s t) : Continuous (ht.restrict f s t)
参数：hf : ContinuousOn f s；ht : MapsTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.codRestrict`：Continuous.codRestrict {f : X -> Y} {s : Set Y} 
(hf : Continuous f) (hs : forall a, f a in s) : Continuous (s.codRestrict f hs)
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
-/
theorem ContinuousOn.mapsToRestrict {t : Set β} (hf : ContinuousOn f s) (ht : MapsTo f s t) :
    Continuous (ht.restrict f s t) :=
  hf.domRestrict.codRestrict _
/-
**continuousOn_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_iff' : ContinuousOn f s ↔ forall t : Set β, IsOpen t -> exist
s u, IsOpen u ∧ f ⁻¹' t inter s = u inter s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_induced_iff`：isOpen_induced_iff [t : TopologicalSpace β] {s : Set
 α} {f : α -> β} : IsOpen[t.induced f] s ↔ exists t, IsOpen t ∧ f ⁻¹' t = s
· 使用定理 `Set.domRestrict_eq`：domRestrict_eq (f : α -> β) (s : Set α) : s.domRestr
ict f = f ∘ Subtype.val
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `continuousOn_iff_continuous_domRestrict`：continuousOn_iff_continuous_dom
Restrict : ContinuousOn f s ↔ Continuous (s.domRestrict f)
· 使用定理 `continuous_def`：continuous_def {_ : TopologicalSpace X} {_ : Topological
Space Y} {f : X -> Y} : Continuous f ↔ forall s, IsOpen s -> IsOpen (f ⁻¹' s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuousOn_iff' :
    ContinuousOn f s ↔ ∀ t : Set β, IsOpen t → ∃ u, IsOpen u ∧ f ⁻¹' t ∩ s = u ∩ s := by
  have : ∀ t, IsOpen (s.domRestrict f ⁻¹' t) ↔ ∃ u : Set α, IsOpen u ∧ f ⁻¹' t ∩ s = u ∩ s := by
    intro t
    rw [isOpen_induced_iff, Set.domRestrict_eq, Set.preimage_comp]
    simp only [Subtype.preimage_coe_eq_preimage_coe_iff]
    constructor <;>
      · rintro ⟨u, ou, useq⟩
        exact ⟨u, ou, by simpa only [Set.inter_comm, eq_comm] using useq⟩
  rw [continuousOn_iff_continuous_domRestrict, continuous_def]; simp only [this]

/-- If a function is continuous on a set for some topologies, then it is
continuous on the same set with respect to any finer topology on the source space. -/
/-
**ContinuousOn.mono_dom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.mono_dom {α β : Type*} {t₁ t₂ : TopologicalSpace α} {t₃ : Top
ologicalSpace β} (h₁ : t₂ <= t₁) {s : Set α} {f : α -> β} (h₂ : @ContinuousOn α 
β t₁ t₃ f s) : @ContinuousOn α β t₂ t₃ f s
参数：h₁ : t₂ <= t₁；h₂ : @ContinuousOn α β t₁ t₃ f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
· 使用定理 `inf_le_inf_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α} (c 
: α), b ≤ a → b ⊓ c ≤ a ⊓ c
· 使用定理 `nhds_mono`：nhds_mono {t₁ t₂ : TopologicalSpace α} {a : α} (h : t₁ <= t₂)
 : @nhds α t₁ a <= @nhds α t₂ a

--- 原说明 ---
If a function is continuous on a set for some topologies, then it is
continuous on the same set with respect to any finer topology on the source spac
e.
-/
theorem ContinuousOn.mono_dom {α β : Type*} {t₁ t₂ : TopologicalSpace α} {t₃ : TopologicalSpace β}
    (h₁ : t₂ ≤ t₁) {s : Set α} {f : α → β} (h₂ : @ContinuousOn α β t₁ t₃ f s) :
    @ContinuousOn α β t₂ t₃ f s := fun x hx _u hu =>
  map_mono (inf_le_inf_right _ <| nhds_mono h₁) (h₂ x hx hu)

/-- If a function is continuous on a set for some topologies, then it is
continuous on the same set with respect to any coarser topology on the target space. -/
/-
**ContinuousOn.mono_rng** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.mono_rng {α β : Type*} {t₁ : TopologicalSpace α} {t₂ t₃ : Top
ologicalSpace β} (h₁ : t₂ <= t₃) {s : Set α} {f : α -> β} (h₂ : @ContinuousOn α 
β t₁ t₂ f s) : @ContinuousOn α β t₁ t₃ f s
参数：h₁ : t₂ <= t₃；h₂ : @ContinuousOn α β t₁ t₂ f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhds_mono`：nhds_mono {t₁ t₂ : TopologicalSpace α} {a : α} (h : t₁ <= t₂)
 : @nhds α t₁ a <= @nhds α t₂ a

--- 原说明 ---
If a function is continuous on a set for some topologies, then it is
continuous on the same set with respect to any coarser topology on the target sp
ace.
-/
theorem ContinuousOn.mono_rng {α β : Type*} {t₁ : TopologicalSpace α} {t₂ t₃ : TopologicalSpace β}
    (h₁ : t₂ ≤ t₃) {s : Set α} {f : α → β} (h₂ : @ContinuousOn α β t₁ t₂ f s) :
    @ContinuousOn α β t₁ t₃ f s := fun x hx _u hu =>
  h₂ x hx <| nhds_mono h₁ hu
/-
**continuousOn_iff_isClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_iff_isClosed : ContinuousOn f s ↔ forall t : Set β, IsClosed 
t -> exists u, IsClosed u ∧ f ⁻¹' t inter s = u inter s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isClosed_induced_iff`：isClosed_induced_iff [t : TopologicalSpace β] {s :
 Set α} {f : α -> β} : IsClosed[t.induced f] s ↔ exists t, IsClosed t ∧ f ⁻¹' t 
= s
· 使用定理 `Set.domRestrict_eq`：domRestrict_eq (f : α -> β) (s : Set α) : s.domRestr
ict f = f ∘ Subtype.val
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `continuousOn_iff_continuous_domRestrict`：continuousOn_iff_continuous_dom
Restrict : ContinuousOn f s ↔ Continuous (s.domRestrict f)
· 使用定理 `continuous_iff_isClosed`：continuous_iff_isClosed : Continuous f ↔ forall
 s, IsClosed s -> IsClosed (f ⁻¹' s)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem continuousOn_iff_isClosed :
    ContinuousOn f s ↔ ∀ t : Set β, IsClosed t → ∃ u, IsClosed u ∧ f ⁻¹' t ∩ s = u ∩ s := by
  have : ∀ t, IsClosed (s.domRestrict f ⁻¹' t) ↔ ∃ u : Set α, IsClosed u ∧ f ⁻¹' t ∩ s = u ∩ s := by
    intro t
    rw [isClosed_induced_iff, Set.domRestrict_eq, Set.preimage_comp]
    simp only [Subtype.preimage_coe_eq_preimage_coe_iff, eq_comm, Set.inter_comm s]
  rw [continuousOn_iff_continuous_domRestrict, continuous_iff_isClosed]; simp only [this]
/-
**continuous_of_cover_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_of_cover_nhds {ι : Sort*} {s : ι -> Set α} (hs : forall x : α, 
exists i, s i in 𝓝 x) (hf : forall i, ContinuousOn f (s i)) : Continuous f
参数：hs : forall x : α, exists i, s i in 𝓝 x；hf : forall i, ContinuousOn f (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (x : X),   ContinuousAt f x = F
ilter.T…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_eq_nhds`：∀ {α : Type u_1} [inst : TopologicalSpace α] {a : α}
 {s : Set α}, nhdsWithin a s = nhds a ↔ s ∈ nhds a
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
-/
theorem continuous_of_cover_nhds {ι : Sort*} {s : ι → Set α}
    (hs : ∀ x : α, ∃ i, s i ∈ 𝓝 x) (hf : ∀ i, ContinuousOn f (s i)) :
    Continuous f :=
  continuous_iff_continuousAt.mpr fun x ↦ let ⟨i, hi⟩ := hs x; by
    rw [ContinuousAt, ← nhdsWithin_eq_nhds.2 hi]
    exact hf _ _ (mem_of_mem_nhds hi)
/-
**continuousOn_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace α] [inst_1 : Topo
logicalSpace β] (f : α → β), ContinuousOn f ∅
参数：f : α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem continuousOn_empty (f : α → β) : ContinuousOn f ∅ := fun _ => False.elim

@[simp]
/-
**continuousOn_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_singleton (f : α -> β) (a : α) : ContinuousOn f {a}
参数：f : α -> β；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `forall_eq`：∀ {α : Sort u_1} {p : α → Prop} {a' : α}, (∀ (a : α), a = a' 
→ p a) ↔ p a'
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_singleton`：nhdsWithin_singleton (a : α) : 𝓝[{a}] a = pure a
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
-/
theorem continuousOn_singleton (f : α → β) (a : α) : ContinuousOn f {a} :=
  forall_eq.2 <| by
    simpa only [ContinuousWithinAt, nhdsWithin_singleton, tendsto_pure_left] using fun s =>
      mem_of_mem_nhds
/-
**Set.Subsingleton.continuousOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Subsingleton.continuousOn {s : Set α} (hs : s.Subsingleton) (f : α -> 
β) : ContinuousOn f s
参数：hs : s.Subsingleton；f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.induction_on`：∀ {α : Type u} {s : Set α} {p : Set α → P
rop}, s.Subsingleton → p ∅ → (∀ (x : α), p {x}) → p s
· 使用定理 `continuousOn_empty`：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalS
pace α] [inst_1 : TopologicalSpace β] (f : α → β), ContinuousOn f ∅
· 使用定理 `continuousOn_singleton`：continuousOn_singleton (f : α -> β) (a : α) : Co
ntinuousOn f {a}
-/
theorem Set.Subsingleton.continuousOn {s : Set α} (hs : s.Subsingleton) (f : α → β) :
    ContinuousOn f s :=
  hs.induction_on (continuousOn_empty f) (continuousOn_singleton f)
/-
**continuousOn_open_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_open_iff (hs : IsOpen s) : ContinuousOn f s ↔ forall t, IsOpe
n t -> IsOpen (s inter f ⁻¹' t)
参数：hs : IsOpen s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuousOn_iff'`：continuousOn_iff' : ContinuousOn f s ↔ forall t : Set
 β, IsOpen t -> exists u, IsOpen u ∧ f ⁻¹' t inter s = u inter s
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
-/
theorem continuousOn_open_iff (hs : IsOpen s) :
    ContinuousOn f s ↔ ∀ t, IsOpen t → IsOpen (s ∩ f ⁻¹' t) := by
  rw [continuousOn_iff']
  constructor
  · intro h t ht
    rcases h t ht with ⟨u, u_open, hu⟩
    rw [inter_comm, hu]
    apply IsOpen.inter u_open hs
  · intro h t ht
    refine ⟨s ∩ f ⁻¹' t, h t ht, ?_⟩
    rw [@inter_comm _ s (f ⁻¹' t), inter_assoc, inter_self]
/-
**ContinuousOn.isOpen_inter_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.isOpen_inter_preimage {t : Set β} (hf : ContinuousOn f s) (hs
 : IsOpen s) (ht : IsOpen t) : IsOpen (s inter f ⁻¹' t)
参数：hf : ContinuousOn f s；hs : IsOpen s；ht : IsOpen t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuousOn_open_iff`：continuousOn_open_iff (hs : IsOpen s) : Continuou
sOn f s ↔ forall t, IsOpen t -> IsOpen (s inter f ⁻¹' t)
-/
theorem ContinuousOn.isOpen_inter_preimage {t : Set β}
    (hf : ContinuousOn f s) (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∩ f ⁻¹' t) :=
  (continuousOn_open_iff hs).1 hf t ht
/-
**ContinuousOn.isOpen_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.isOpen_preimage {t : Set β} (h : ContinuousOn f s) (hs : IsOp
en s) (hp : f ⁻¹' t subseteq s) (ht : IsOpen t) : IsOpen (f ⁻¹' t)
参数：h : ContinuousOn f s；hs : IsOpen s；hp : f ⁻¹' t subseteq s；ht : IsOpen t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Set.inter_eq_self_of_subset_left`：inter_eq_self_of_subset_left {s t : Se
t α} : s subseteq t -> s inter t = s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuousOn_open_iff`：continuousOn_open_iff (hs : IsOpen s) : Continuou
sOn f s ↔ forall t, IsOpen t -> IsOpen (s inter f ⁻¹' t)
-/
theorem ContinuousOn.isOpen_preimage {t : Set β} (h : ContinuousOn f s)
    (hs : IsOpen s) (hp : f ⁻¹' t ⊆ s) (ht : IsOpen t) : IsOpen (f ⁻¹' t) := by
  convert! (continuousOn_open_iff hs).mp h t ht
  rw [inter_comm, inter_eq_self_of_subset_left hp]
/-
**ContinuousOn.preimage_isClosed_of_isClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.preimage_isClosed_of_isClosed {t : Set β} (hf : ContinuousOn 
f s) (hs : IsClosed s) (ht : IsClosed t) : IsClosed (s inter f ⁻¹' t)
参数：hf : ContinuousOn f s；hs : IsClosed s；ht : IsClosed t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuousOn_iff_isClosed`：continuousOn_iff_isClosed : ContinuousOn f s 
↔ forall t : Set β, IsClosed t -> exists u, IsClosed u ∧ f ⁻¹' t inter s = u int
er s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem ContinuousOn.preimage_isClosed_of_isClosed {t : Set β}
    (hf : ContinuousOn f s) (hs : IsClosed s) (ht : IsClosed t) : IsClosed (s ∩ f ⁻¹' t) := by
  rcases continuousOn_iff_isClosed.1 hf t ht with ⟨u, hu⟩
  rw [inter_comm, hu.2]
  apply IsClosed.inter hu.1 hs
/-
**ContinuousOn.preimage_interior_subset_interior_preimage** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：ContinuousOn.preimage_interior_subset_interior_preimage {t : Set β} (hf : 
ContinuousOn f s) (hs : IsOpen s) : s inter f ⁻¹' interior t subseteq s inter in
terior (f ⁻¹' t)
参数：hf : ContinuousOn f s；hs : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `interior_maximal`：interior_maximal (h₁ : t subseteq s) (h₂ : IsOpen t) :
 t subseteq interior s
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `ContinuousOn.isOpen_inter_preimage`：ContinuousOn.isOpen_inter_preimage {
t : Set β} (hf : ContinuousOn f s) (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s i
nter f ⁻¹' t)
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_inter`：interior_inter : interior (s inter t) = interior s inter
 interior t
· 使用定理 `IsOpen.interior_eq`：IsOpen.interior_eq (h : IsOpen s) : interior s = s
-/
theorem ContinuousOn.preimage_interior_subset_interior_preimage {t : Set β}
    (hf : ContinuousOn f s) (hs : IsOpen s) : s ∩ f ⁻¹' interior t ⊆ s ∩ interior (f ⁻¹' t) :=
  calc
    s ∩ f ⁻¹' interior t ⊆ interior (s ∩ f ⁻¹' t) :=
      interior_maximal (inter_subset_inter (Subset.refl _) (preimage_mono interior_subset))
        (hf.isOpen_inter_preimage hs isOpen_interior)
    _ = s ∩ interior (f ⁻¹' t) := by rw [interior_inter, hs.interior_eq]
/-
**continuousOn_of_locally_continuousOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_of_locally_continuousOn (h : forall x in s, exists t, IsOpen 
t ∧ x in t ∧ ContinuousOn f (s inter t)) : ContinuousOn f s
参数：h : forall x in s, exists t, IsOpen t ∧ x in t ∧ ContinuousOn f (s inter t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_restrict`：nhdsWithin_restrict {a : α} (s : Set α) {t : Set α}
 (h₀ : a in t) (h₁ : IsOpen t) : 𝓝[s] a = 𝓝[s inter t] a
· 使用定理 `ContinuousWithinAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (s : Set X)   (x : X), Co
ntinuousWithi…
-/
theorem continuousOn_of_locally_continuousOn
    (h : ∀ x ∈ s, ∃ t, IsOpen t ∧ x ∈ t ∧ ContinuousOn f (s ∩ t)) : ContinuousOn f s := by
  intro x xs
  rcases h x xs with ⟨t, open_t, xt, ct⟩
  have := ct x ⟨xs, xt⟩
  rwa [ContinuousWithinAt, ← nhdsWithin_restrict _ xt open_t] at this
/-
**continuousOn_to_generateFrom_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_to_generateFrom_iff {β : Type*} {T : Set (Set β)} {f : α -> β
} : @ContinuousOn α β _ (.generateFrom T) f s ↔ forall x in s, forall t in T, f 
x in t -> f ⁻¹' t in 𝓝[s] x
参数：Set β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `TopologicalSpace.nhds_generateFrom`：nhds_generateFrom {g : Set (Set α)} 
{a : α} : @nhds α (generateFrom g) a = ⨅ s in { s | a in s ∧ s in g }, 𝓟 s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
-/
theorem continuousOn_to_generateFrom_iff {β : Type*} {T : Set (Set β)} {f : α → β} :
    @ContinuousOn α β _ (.generateFrom T) f s ↔ ∀ x ∈ s, ∀ t ∈ T, f x ∈ t → f ⁻¹' t ∈ 𝓝[s] x :=
  forall₂_congr fun x _ => by
    delta ContinuousWithinAt
    simp only [TopologicalSpace.nhds_generateFrom, tendsto_iInf, tendsto_principal, mem_ofPred_eq,
      and_imp]
    exact forall_congr' fun t => forall_comm
/-
**continuousOn_isOpen_of_generateFrom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_isOpen_of_generateFrom {β : Type*} {s : Set α} {T : Set (Set 
β)} {f : α -> β} (h : forall t in T, IsOpen (s inter f ⁻¹' t)) : @ContinuousOn α
 β _ (.generateFrom T) f s
参数：Set β；h : forall t in T, IsOpen (s inter f ⁻¹' t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuousOn_to_generateFrom_iff`：continuousOn_to_generateFrom_iff {β : 
Type*} {T : Set (Set β)} {f : α -> β} : @ContinuousOn α β _ (.generateFrom T) f 
s ↔ forall x in s, for…
· 使用定理 `mem_nhdsWithin`：mem_nhdsWithin {t : Set α} {a : α} {s : Set α} : t in 𝓝[
s] a ↔ exists u, IsOpen u ∧ a in u ∧ u inter s subseteq t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem continuousOn_isOpen_of_generateFrom {β : Type*} {s : Set α} {T : Set (Set β)} {f : α → β}
    (h : ∀ t ∈ T, IsOpen (s ∩ f ⁻¹' t)) :
    @ContinuousOn α β _ (.generateFrom T) f s :=
  continuousOn_to_generateFrom_iff.2 fun _x hx t ht hxt => mem_nhdsWithin.2
    ⟨_, h t ht, ⟨hx, hxt⟩, fun _y hy => hy.1.2⟩

/-!
## Congruence and monotonicity properties with respect to sets
-/

/-
**ContinuousWithinAt.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.mono (h : ContinuousWithinAt f t x) (hs : s subseteq t)
 : ContinuousWithinAt f s x
参数：h : ContinuousWithinAt f t x；hs : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x

--- 原说明 ---
## Congruence and monotonicity properties with respect to sets
-/
theorem ContinuousWithinAt.mono (h : ContinuousWithinAt f t x)
    (hs : s ⊆ t) : ContinuousWithinAt f s x :=
  h.mono_left (nhdsWithin_mono x hs)
/-
**ContinuousWithinAt.mono_of_mem_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.mono_of_mem_nhdsWithin (h : ContinuousWithinAt f t x) (
hs : t in 𝓝[s] x) : ContinuousWithinAt f s x
参数：h : ContinuousWithinAt f t x；hs : t in 𝓝[s] x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `nhdsWithin_le_of_mem`：nhdsWithin_le_of_mem {a : α} {s t : Set α} (h : s 
in 𝓝[t] a) : 𝓝[t] a <= 𝓝[s] a
-/
theorem ContinuousWithinAt.mono_of_mem_nhdsWithin (h : ContinuousWithinAt f t x) (hs : t ∈ 𝓝[s] x) :
    ContinuousWithinAt f s x :=
  h.mono_left (nhdsWithin_le_of_mem hs)

/-- If two sets coincide around `x`, then being continuous within one or the other at `x` is
equivalent. See also `continuousWithinAt_congr_set'` which requires that the sets coincide
locally away from a point `y`, in a T1 space. -/
/-
**continuousWithinAt_congr_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_congr_set (h : s =ᶠ[𝓝 x] t) : ContinuousWithinAt f s x 
↔ ContinuousWithinAt f t x
参数：h : s =ᶠ[𝓝 x] t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `nhdsWithin_eq_iff_eventuallyEq`：nhdsWithin_eq_iff_eventuallyEq {s t : Se
t α} {x : α} : 𝓝[s] x = 𝓝[t] x ↔ s =ᶠ[𝓝 x] t
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
If two sets coincide around `x`, then being continuous within one or the other a
t `x` is
equivalent. See also `continuousWithinAt_congr_set'` which requires that the set
s coincide
locally away from a point `y`, in a T1 space.
-/
theorem continuousWithinAt_congr_set (h : s =ᶠ[𝓝 x] t) :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt f t x := by
  simp only [ContinuousWithinAt, nhdsWithin_eq_iff_eventuallyEq.mpr h]
/-
**ContinuousWithinAt.congr_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.congr_set (hf : ContinuousWithinAt f s x) (h : s =ᶠ[𝓝 x
] t) : ContinuousWithinAt f t x
参数：hf : ContinuousWithinAt f s x；h : s =ᶠ[𝓝 x] t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuousWithinAt_congr_set`：continuousWithinAt_congr_set (h : s =ᶠ[𝓝 x
] t) : ContinuousWithinAt f s x ↔ ContinuousWithinAt f t x
-/
theorem ContinuousWithinAt.congr_set (hf : ContinuousWithinAt f s x) (h : s =ᶠ[𝓝 x] t) :
    ContinuousWithinAt f t x :=
  (continuousWithinAt_congr_set h).1 hf
/-
**continuousWithinAt_inter'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_inter' (h : t in 𝓝[s] x) : ContinuousWithinAt f (s inte
r t) x ↔ ContinuousWithinAt f s x
参数：h : t in 𝓝[s] x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nhdsWithin_restrict''`：nhdsWithin_restrict'' {a : α} (s : Set α) {t : Se
t α} (h : t in 𝓝[s] a) : 𝓝[s] a = 𝓝[s inter t] a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuousWithinAt_inter' (h : t ∈ 𝓝[s] x) :
    ContinuousWithinAt f (s ∩ t) x ↔ ContinuousWithinAt f s x := by
  simp [ContinuousWithinAt, nhdsWithin_restrict'' s h]
/-
**continuousWithinAt_inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_inter (h : t in 𝓝 x) : ContinuousWithinAt f (s inter t)
 x ↔ ContinuousWithinAt f s x
参数：h : t in 𝓝 x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nhdsWithin_restrict'`：nhdsWithin_restrict' {a : α} (s : Set α) {t : Set 
α} (h : t in 𝓝 a) : 𝓝[s] a = 𝓝[s inter t] a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuousWithinAt_inter (h : t ∈ 𝓝 x) :
    ContinuousWithinAt f (s ∩ t) x ↔ ContinuousWithinAt f s x := by
  simp [ContinuousWithinAt, nhdsWithin_restrict' s h]
/-
**continuousWithinAt_union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_union : ContinuousWithinAt f (s union t) x ↔ Continuous
WithinAt f s x ∧ ContinuousWithinAt f t x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_union`：nhdsWithin_union (a : α) (s t : Set α) : 𝓝[s union t] 
a = 𝓝[s] a ⊔ 𝓝[t] a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuousWithinAt_union :
    ContinuousWithinAt f (s ∪ t) x ↔ ContinuousWithinAt f s x ∧ ContinuousWithinAt f t x := by
  simp only [ContinuousWithinAt, nhdsWithin_union, tendsto_sup]
/-
**ContinuousWithinAt.union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.union (hs : ContinuousWithinAt f s x) (ht : ContinuousW
ithinAt f t x) : ContinuousWithinAt f (s union t) x
参数：hs : ContinuousWithinAt f s x；ht : ContinuousWithinAt f t x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuousWithinAt_union`：continuousWithinAt_union : ContinuousWithinAt 
f (s union t) x ↔ ContinuousWithinAt f s x ∧ ContinuousWithinAt f t x
-/
theorem ContinuousWithinAt.union (hs : ContinuousWithinAt f s x) (ht : ContinuousWithinAt f t x) :
    ContinuousWithinAt f (s ∪ t) x :=
  continuousWithinAt_union.2 ⟨hs, ht⟩

@[simp]
/-
**continuousWithinAt_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_singleton : ContinuousWithinAt f {x} x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_singleton`：nhdsWithin_singleton (a : α) : 𝓝[{a}] a = pure a
-/
theorem continuousWithinAt_singleton : ContinuousWithinAt f {x} x := by
  simp only [ContinuousWithinAt, nhdsWithin_singleton, tendsto_pure_nhds]

@[simp]
/-
**continuousWithinAt_insert_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_insert_self : ContinuousWithinAt f (insert x s) x ↔ Con
tinuousWithinAt f s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuousWithinAt_insert_self :
    ContinuousWithinAt f (insert x s) x ↔ ContinuousWithinAt f s x := by
  simp only [← singleton_union, continuousWithinAt_union, continuousWithinAt_singleton, true_and]

protected alias ⟨_, ContinuousWithinAt.insert⟩ := continuousWithinAt_insert_self

/-- `continuousWithinAt_insert` gives the same equivalence but at a point `y` possibly different
from `x`. As this requires the space to be T1, and this property is not available in this file,
this is found in another file although it is part of the basic API for `continuousWithinAt`. -/
/-
**ContinuousWithinAt.sdiff_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.sdiff_iff (ht : ContinuousWithinAt f t x) : ContinuousW
ithinAt f (s \ t) x ↔ ContinuousWithinAt f s x
参数：ht : ContinuousWithinAt f t x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.mono`：ContinuousWithinAt.mono (h : ContinuousWithinAt
 f t x) (hs : s subseteq t) : ContinuousWithinAt f s x
· 使用定理 `ContinuousWithinAt.union`：ContinuousWithinAt.union (hs : ContinuousWithi
nAt f s x) (ht : ContinuousWithinAt f t x) : ContinuousWithinAt f (s union t) x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sdiff_union_self`：sdiff_union_self {s t : Set α} : s \ t union t = s
 union t
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s

--- 原说明 ---
`continuousWithinAt_insert` gives the same equivalence but at a point `y` possib
ly different
from `x`. As this requires the space to be T1, and this property is not availabl
e in this file,
this is found in another file although it is part of the basic API for `continuo
usWithinAt`.
-/
theorem ContinuousWithinAt.sdiff_iff
    (ht : ContinuousWithinAt f t x) : ContinuousWithinAt f (s \ t) x ↔ ContinuousWithinAt f s x :=
  ⟨fun h => (h.union ht).mono <| by simp only [sdiff_union_self, subset_union_left], fun h =>
    h.mono sdiff_subset⟩

/-- See also `continuousWithinAt_sdiff_singleton` for the case of `s \ {y}`, but
requiring `T1Space α`. -/
@[simp]
/-
**continuousWithinAt_sdiff_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_sdiff_self : ContinuousWithinAt f (s \ {x}) x ↔ Continu
ousWithinAt f s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.sdiff_iff`：ContinuousWithinAt.sdiff_iff (ht : Continu
ousWithinAt f t x) : ContinuousWithinAt f (s \ t) x ↔ ContinuousWithinAt f s x
· 使用定理 `continuousWithinAt_singleton`：continuousWithinAt_singleton : ContinuousW
ithinAt f {x} x

--- 原说明 ---
See also `continuousWithinAt_sdiff_singleton` for the case of `s \ {y}`, but
requiring `T1Space α`.
-/
theorem continuousWithinAt_sdiff_self :
    ContinuousWithinAt f (s \ {x}) x ↔ ContinuousWithinAt f s x :=
  continuousWithinAt_singleton.sdiff_iff

@[deprecated (since := "2026-06-03")]
alias continuousWithinAt_diff_self := continuousWithinAt_sdiff_self

/-- A function is continuous at a point `x` within a set `s` if `x` is not an accumulation point of
`s`. -/
/-
**continuousWithinAt_of_not_accPt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：continuousWithinAt_of_not_accPt (h : ¬AccPt x (𝓟 s)) : ContinuousWithinAt 
f s x
参数：h : ¬AccPt x (𝓟 s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuousWithinAt_sdiff_self`：continuousWithinAt_sdiff_self : Continuou
sWithinAt f (s \ {x}) x ↔ ContinuousWithinAt f s x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a

--- 原说明 ---
A function is continuous at a point `x` within a set `s` if `x` is not an accumu
lation point of
`s`.
-/
lemma continuousWithinAt_of_not_accPt (h : ¬AccPt x (𝓟 s)) : ContinuousWithinAt f s x := by
  rw [← continuousWithinAt_sdiff_self]
  simp_all [ContinuousWithinAt, AccPt, ← nhdsWithin_inter', Set.sdiff_eq, Set.inter_comm]

@[simp]
/-
**continuousWithinAt_compl_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_compl_self : ContinuousWithinAt f {x}ᶜ x ↔ ContinuousAt
 f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_eq_univ_sdiff`：compl_eq_univ_sdiff (s : Set α) : sᶜ = univ \ s
· 使用定理 `continuousWithinAt_sdiff_self`：continuousWithinAt_sdiff_self : Continuou
sWithinAt f (s \ {x}) x ↔ ContinuousWithinAt f s x
· 使用定理 `continuousWithinAt_univ`：continuousWithinAt_univ (f : α -> β) (x : α) : 
ContinuousWithinAt f Set.univ x ↔ ContinuousAt f x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem continuousWithinAt_compl_self :
    ContinuousWithinAt f {x}ᶜ x ↔ ContinuousAt f x := by
  rw [compl_eq_univ_sdiff, continuousWithinAt_sdiff_self, continuousWithinAt_univ]

/-- A function is continuous at a point `x` if `x` is isolated. -/
/-
**continuousAt_of_not_accPt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：continuousAt_of_not_accPt (h : ¬AccPt x (𝓟 {x}ᶜ)) : ContinuousAt f x
参数：h : ¬AccPt x (𝓟 {x}ᶜ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuousWithinAt_compl_self`：continuousWithinAt_compl_self : Continuou
sWithinAt f {x}ᶜ x ↔ ContinuousAt f x
· 使用引理 `continuousWithinAt_of_not_accPt`：continuousWithinAt_of_not_accPt (h : ¬A
ccPt x (𝓟 s)) : ContinuousWithinAt f s x

--- 原说明 ---
A function is continuous at a point `x` if `x` is isolated.
-/
lemma continuousAt_of_not_accPt (h : ¬AccPt x (𝓟 {x}ᶜ)) : ContinuousAt f x := by
  rw [← continuousWithinAt_compl_self]
  exact continuousWithinAt_of_not_accPt h

/-- A function is continuous at a point `x` if `x` is isolated. -/
/-
**continuousAt_of_not_accPt_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：continuousAt_of_not_accPt_top (h : ¬AccPt x ⊤) : ContinuousAt f x
参数：h : ¬AccPt x ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `continuousAt_of_not_accPt`：continuousAt_of_not_accPt (h : ¬AccPt x (𝓟 {x
}ᶜ)) : ContinuousAt f x
· 使用定理 `AccPt.mono`：AccPt.mono {F G : Filter X} (h : AccPt x F) (hFG : F <= G) :
 AccPt x G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
A function is continuous at a point `x` if `x` is isolated.
-/
lemma continuousAt_of_not_accPt_top (h : ¬AccPt x ⊤) : ContinuousAt f x :=
  continuousAt_of_not_accPt fun hh ↦ h <| AccPt.mono hh (by simp)
/-
**ContinuousOn.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subseteq s) : ContinuousO
n f t
参数：hf : ContinuousOn f s；h : t subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
-/
theorem ContinuousOn.mono (hf : ContinuousOn f s) (h : t ⊆ s) :
    ContinuousOn f t := fun x hx => (hf x (h hx)).mono_left (nhdsWithin_mono _ h)
/-
**antitone_continuousOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antitone_continuousOn {f : α -> β} : Antitone (ContinuousOn f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
-/
theorem antitone_continuousOn {f : α → β} : Antitone (ContinuousOn f) := fun _s _t hst hf =>
  hf.mono hst

/-!
## Relation between `ContinuousAt` and `ContinuousWithinAt`
-/

@[fun_prop]
/-
**ContinuousAt.continuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.continuousWithinAt (h : ContinuousAt f x) : ContinuousWithinA
t f s x
参数：h : ContinuousAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.mono`：ContinuousWithinAt.mono (h : ContinuousWithinAt
 f t x) (hs : s subseteq t) : ContinuousWithinAt f s x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuousWithinAt_univ`：continuousWithinAt_univ (f : α -> β) (x : α) : 
ContinuousWithinAt f Set.univ x ↔ ContinuousAt f x
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ

--- 原说明 ---
## Relation between `ContinuousAt` and `ContinuousWithinAt`
-/
theorem ContinuousAt.continuousWithinAt (h : ContinuousAt f x) :
    ContinuousWithinAt f s x :=
  ContinuousWithinAt.mono ((continuousWithinAt_univ f x).2 h) (subset_univ _)
/-
**continuousWithinAt_iff_continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_iff_continuousAt (h : s in 𝓝 x) : ContinuousWithinAt f 
s x ↔ ContinuousAt f x
参数：h : s in 𝓝 x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `continuousWithinAt_inter`：continuousWithinAt_inter (h : t in 𝓝 x) : Cont
inuousWithinAt f (s inter t) x ↔ ContinuousWithinAt f s x
· 使用定理 `continuousWithinAt_univ`：continuousWithinAt_univ (f : α -> β) (x : α) : 
ContinuousWithinAt f Set.univ x ↔ ContinuousAt f x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem continuousWithinAt_iff_continuousAt (h : s ∈ 𝓝 x) :
    ContinuousWithinAt f s x ↔ ContinuousAt f x := by
  rw [← univ_inter s, continuousWithinAt_inter h, continuousWithinAt_univ]
/-
**ContinuousWithinAt.continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.continuousAt (h : ContinuousWithinAt f s x) (hs : s in 
𝓝 x) : ContinuousAt f x
参数：h : ContinuousWithinAt f s x；hs : s in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuousWithinAt_iff_continuousAt`：continuousWithinAt_iff_continuousAt
 (h : s in 𝓝 x) : ContinuousWithinAt f s x ↔ ContinuousAt f x
-/
theorem ContinuousWithinAt.continuousAt
    (h : ContinuousWithinAt f s x) (hs : s ∈ 𝓝 x) : ContinuousAt f x :=
  (continuousWithinAt_iff_continuousAt hs).mp h
/-
**IsOpen.continuousOn_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.continuousOn_iff (hs : IsOpen s) : ContinuousOn f s ↔ forall ⦃a⦄, a
 in s -> ContinuousAt f a
参数：hs : IsOpen s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `continuousWithinAt_iff_continuousAt`：continuousWithinAt_iff_continuousAt
 (h : s in 𝓝 x) : ContinuousWithinAt f s x ↔ ContinuousAt f x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
-/
theorem IsOpen.continuousOn_iff (hs : IsOpen s) :
    ContinuousOn f s ↔ ∀ ⦃a⦄, a ∈ s → ContinuousAt f a :=
  forall₂_congr fun _ => continuousWithinAt_iff_continuousAt ∘ hs.mem_nhds
/-
**ContinuousOn.continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.continuousAt (h : ContinuousOn f s) (hx : s in 𝓝 x) : Continu
ousAt f x
参数：h : ContinuousOn f s；hx : s in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.continuousAt`：ContinuousWithinAt.continuousAt (h : Co
ntinuousWithinAt f s x) (hs : s in 𝓝 x) : ContinuousAt f x
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
-/
theorem ContinuousOn.continuousAt (h : ContinuousOn f s)
    (hx : s ∈ 𝓝 x) : ContinuousAt f x :=
  (h x (mem_of_mem_nhds hx)).continuousAt hx
/-
**continuousOn_of_forall_continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_of_forall_continuousAt (hcont : forall x in s, ContinuousAt f
 x) : ContinuousOn f s
参数：hcont : forall x in s, ContinuousAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
-/
theorem continuousOn_of_forall_continuousAt (hcont : ∀ x ∈ s, ContinuousAt f x) :
    ContinuousOn f s := fun x hx => (hcont x hx).continuousWithinAt

@[fun_prop]
/-
**Continuous.continuousOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.continuousOn (h : Continuous f) : ContinuousOn f s
参数：h : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuousOn_univ`：continuousOn_univ {f : α -> β} : ContinuousOn f univ 
↔ Continuous f
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem Continuous.continuousOn (h : Continuous f) : ContinuousOn f s := by
  rw [← continuousOn_univ] at h
  exact h.mono (subset_univ _)

@[fun_prop]
/-
**Continuous.continuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.continuousWithinAt (h : Continuous f) : ContinuousWithinAt f s 
x
参数：h : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
theorem Continuous.continuousWithinAt (h : Continuous f) :
    ContinuousWithinAt f s x :=
  h.continuousAt.continuousWithinAt


/-!
## Congruence properties with respect to functions
-/

/-
**ContinuousOn.congr_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.congr_mono (h : ContinuousOn f s) (h' : EqOn g f s₁) (h₁ : s₁
 subseteq s) : ContinuousOn g s₁
参数：h : ContinuousOn f s；h' : EqOn g f s₁；h₁ : s₁ subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.mono`：ContinuousWithinAt.mono (h : ContinuousWithinAt
 f t x) (hs : s subseteq t) : ContinuousWithinAt f s x
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Set.EqOn.eventuallyEq_nhdsWithin`：Set.EqOn.eventuallyEq_nhdsWithin {f g 
: α -> β} {s : Set α} {a : α} (h : EqOn f g s) : f =ᶠ[𝓝[s] a] g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
## Congruence properties with respect to functions
-/
theorem ContinuousOn.congr_mono (h : ContinuousOn f s) (h' : EqOn g f s₁) (h₁ : s₁ ⊆ s) :
    ContinuousOn g s₁ := by
  intro x hx
  unfold ContinuousWithinAt
  have A := (h x (h₁ hx)).mono h₁
  unfold ContinuousWithinAt at A
  rw [← h' hx] at A
  exact A.congr' h'.eventuallyEq_nhdsWithin.symm
/-
**ContinuousOn.congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.congr (h : ContinuousOn f s) (h' : EqOn g f s) : ContinuousOn
 g s
参数：h : ContinuousOn f s；h' : EqOn g f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.congr_mono`：ContinuousOn.congr_mono (h : ContinuousOn f s) 
(h' : EqOn g f s₁) (h₁ : s₁ subseteq s) : ContinuousOn g s₁
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
-/
theorem ContinuousOn.congr (h : ContinuousOn f s) (h' : EqOn g f s) :
    ContinuousOn g s :=
  h.congr_mono h' (Subset.refl _)
/-
**continuousOn_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_congr (h' : EqOn g f s) : ContinuousOn g s ↔ ContinuousOn f s
参数：h' : EqOn g f s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.congr`：ContinuousOn.congr (h : ContinuousOn f s) (h' : EqOn
 g f s) : ContinuousOn g s
· 使用定理 `Set.EqOn.symm`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α → 
β}, Set.EqOn f₁ f₂ s → Set.EqOn f₂ f₁ s
-/
theorem continuousOn_congr (h' : EqOn g f s) :
    ContinuousOn g s ↔ ContinuousOn f s :=
  ⟨fun h => ContinuousOn.congr h h'.symm, fun h => h.congr h'⟩
/-
**Filter.EventuallyEq.congr_continuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.congr_continuousWithinAt (h : f =ᶠ[𝓝[s] x] g) (hx : f 
x = g x) : ContinuousWithinAt f s x ↔ ContinuousWithinAt g s x
参数：h : f =ᶠ[𝓝[s] x] g；hx : f x = g x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousWithinAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (s : Set X)   (x : X), Co
ntinuousWithi…
· 使用定理 `Filter.tendsto_congr'`：tendsto_congr' {f₁ f₂ : α -> β} {l₁ : Filter α} {
l₂ : Filter β} (hl : f₁ =ᶠ[l₁] f₂) : Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Filter.EventuallyEq.congr_continuousWithinAt (h : f =ᶠ[𝓝[s] x] g) (hx : f x = g x) :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt g s x := by
  rw [ContinuousWithinAt, hx, tendsto_congr' h, ContinuousWithinAt]
/-
**ContinuousWithinAt.congr_of_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.congr_of_eventuallyEq (h : ContinuousWithinAt f s x) (h
₁ : g =ᶠ[𝓝[s] x] f) (hx : g x = f x) : ContinuousWithinAt g s x
参数：h : ContinuousWithinAt f s x；h₁ : g =ᶠ[𝓝[s] x] f；hx : g x = f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.EventuallyEq.congr_continuousWithinAt`：Filter.EventuallyEq.congr_
continuousWithinAt (h : f =ᶠ[𝓝[s] x] g) (hx : f x = g x) : ContinuousWithinAt f 
s x ↔ ContinuousWithinAt g s x
-/
theorem ContinuousWithinAt.congr_of_eventuallyEq
    (h : ContinuousWithinAt f s x) (h₁ : g =ᶠ[𝓝[s] x] f) (hx : g x = f x) :
    ContinuousWithinAt g s x :=
  (h₁.congr_continuousWithinAt hx).2 h
/-
**ContinuousWithinAt.congr_of_eventuallyEq_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.congr_of_eventuallyEq_of_mem (h : ContinuousWithinAt f 
s x) (h₁ : g =ᶠ[𝓝[s] x] f) (hx : x in s) : ContinuousWithinAt g s x
参数：h : ContinuousWithinAt f s x；h₁ : g =ᶠ[𝓝[s] x] f；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.congr_of_eventuallyEq`：ContinuousWithinAt.congr_of_ev
entuallyEq (h : ContinuousWithinAt f s x) (h₁ : g =ᶠ[𝓝[s] x] f) (hx : g x = f x)
 : ContinuousWithinAt g s x
· 使用定理 `mem_of_mem_nhdsWithin`：mem_of_mem_nhdsWithin {a : α} {s t : Set α} (ha :
 a in s) (ht : t in 𝓝[s] a) : a in t
-/
theorem ContinuousWithinAt.congr_of_eventuallyEq_of_mem
    (h : ContinuousWithinAt f s x) (h₁ : g =ᶠ[𝓝[s] x] f) (hx : x ∈ s) :
    ContinuousWithinAt g s x :=
  h.congr_of_eventuallyEq h₁ (mem_of_mem_nhdsWithin hx h₁ :)
/-
**Filter.EventuallyEq.congr_continuousWithinAt_of_mem** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：Filter.EventuallyEq.congr_continuousWithinAt_of_mem (h : f =ᶠ[𝓝[s] x] g) (
hx : x in s) : ContinuousWithinAt f s x ↔ ContinuousWithinAt g s x
参数：h : f =ᶠ[𝓝[s] x] g；hx : x in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.congr_of_eventuallyEq_of_mem`：ContinuousWithinAt.cong
r_of_eventuallyEq_of_mem (h : ContinuousWithinAt f s x) (h₁ : g =ᶠ[𝓝[s] x] f) (h
x : x in s) : ContinuousWithinAt g s …
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem Filter.EventuallyEq.congr_continuousWithinAt_of_mem (h : f =ᶠ[𝓝[s] x] g) (hx : x ∈ s) :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt g s x :=
  ⟨fun h' ↦ h'.congr_of_eventuallyEq_of_mem h.symm hx,
    fun h' ↦  h'.congr_of_eventuallyEq_of_mem h hx⟩
/-
**ContinuousWithinAt.congr_of_eventuallyEq_insert** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.congr_of_eventuallyEq_insert (h : ContinuousWithinAt f 
s x) (h₁ : g =ᶠ[𝓝[insert x s] x] f) : ContinuousWithinAt g s x
参数：h : ContinuousWithinAt f s x；h₁ : g =ᶠ[𝓝[insert x s] x] f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.congr_of_eventuallyEq`：ContinuousWithinAt.congr_of_ev
entuallyEq (h : ContinuousWithinAt f s x) (h₁ : g =ᶠ[𝓝[s] x] f) (hx : g x = f x)
 : ContinuousWithinAt g s x
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `mem_of_mem_nhdsWithin`：mem_of_mem_nhdsWithin {a : α} {s t : Set α} (ha :
 a in s) (ht : t in 𝓝[s] a) : a in t
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
-/
theorem ContinuousWithinAt.congr_of_eventuallyEq_insert
    (h : ContinuousWithinAt f s x) (h₁ : g =ᶠ[𝓝[insert x s] x] f) :
    ContinuousWithinAt g s x :=
  h.congr_of_eventuallyEq (nhdsWithin_mono _ (subset_insert _ _) h₁)
    (mem_of_mem_nhdsWithin (mem_insert _ _) h₁ :)
/-
**Filter.EventuallyEq.congr_continuousWithinAt_of_insert** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：Filter.EventuallyEq.congr_continuousWithinAt_of_insert (h : f =ᶠ[𝓝[insert 
x s] x] g) : ContinuousWithinAt f s x ↔ ContinuousWithinAt g s x
参数：h : f =ᶠ[𝓝[insert x s] x] g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.congr_of_eventuallyEq_insert`：ContinuousWithinAt.cong
r_of_eventuallyEq_insert (h : ContinuousWithinAt f s x) (h₁ : g =ᶠ[𝓝[insert x s]
 x] f) : ContinuousWithinAt g s x
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem Filter.EventuallyEq.congr_continuousWithinAt_of_insert (h : f =ᶠ[𝓝[insert x s] x] g) :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt g s x :=
  ⟨fun h' ↦ h'.congr_of_eventuallyEq_insert h.symm,
    fun h' ↦  h'.congr_of_eventuallyEq_insert h⟩
/-
**ContinuousWithinAt.congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.congr (h : ContinuousWithinAt f s x) (h₁ : forall y in 
s, g y = f y) (hx : g x = f x) : ContinuousWithinAt g s x
参数：h : ContinuousWithinAt f s x；h₁ : forall y in s, g y = f y；hx : g x = f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.congr_of_eventuallyEq`：ContinuousWithinAt.congr_of_ev
entuallyEq (h : ContinuousWithinAt f s x) (h₁ : g =ᶠ[𝓝[s] x] f) (hx : g x = f x)
 : ContinuousWithinAt g s x
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
-/
theorem ContinuousWithinAt.congr (h : ContinuousWithinAt f s x)
    (h₁ : ∀ y ∈ s, g y = f y) (hx : g x = f x) : ContinuousWithinAt g s x :=
  h.congr_of_eventuallyEq (mem_of_superset self_mem_nhdsWithin h₁) hx
/-
**continuousWithinAt_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_congr (h₁ : forall y in s, g y = f y) (hx : g x = f x) 
: ContinuousWithinAt g s x ↔ ContinuousWithinAt f s x
参数：h₁ : forall y in s, g y = f y；hx : g x = f x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.congr`：ContinuousWithinAt.congr (h : ContinuousWithin
At f s x) (h₁ : forall y in s, g y = f y) (hx : g x = f x) : ContinuousWithinAt 
g s x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem continuousWithinAt_congr (h₁ : ∀ y ∈ s, g y = f y) (hx : g x = f x) :
    ContinuousWithinAt g s x ↔ ContinuousWithinAt f s x :=
  ⟨fun h' ↦ h'.congr (fun x hx ↦ (h₁ x hx).symm) hx.symm, fun h' ↦  h'.congr h₁ hx⟩
/-
**ContinuousWithinAt.congr_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.congr_of_mem (h : ContinuousWithinAt f s x) (h₁ : foral
l y in s, g y = f y) (hx : x in s) : ContinuousWithinAt g s x
参数：h : ContinuousWithinAt f s x；h₁ : forall y in s, g y = f y；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.congr`：ContinuousWithinAt.congr (h : ContinuousWithin
At f s x) (h₁ : forall y in s, g y = f y) (hx : g x = f x) : ContinuousWithinAt 
g s x
-/
theorem ContinuousWithinAt.congr_of_mem (h : ContinuousWithinAt f s x)
    (h₁ : ∀ y ∈ s, g y = f y) (hx : x ∈ s) : ContinuousWithinAt g s x :=
  h.congr h₁ (h₁ x hx)
/-
**continuousWithinAt_congr_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_congr_of_mem (h₁ : forall y in s, g y = f y) (hx : x in
 s) : ContinuousWithinAt g s x ↔ ContinuousWithinAt f s x
参数：h₁ : forall y in s, g y = f y；hx : x in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousWithinAt_congr`：continuousWithinAt_congr (h₁ : forall y in s, 
g y = f y) (hx : g x = f x) : ContinuousWithinAt g s x ↔ ContinuousWithinAt f s 
x
-/
theorem continuousWithinAt_congr_of_mem (h₁ : ∀ y ∈ s, g y = f y) (hx : x ∈ s) :
    ContinuousWithinAt g s x ↔ ContinuousWithinAt f s x :=
  continuousWithinAt_congr h₁ (h₁ x hx)
/-
**ContinuousWithinAt.congr_of_insert** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.congr_of_insert (h : ContinuousWithinAt f s x) (h₁ : fo
rall y in insert x s, g y = f y) : ContinuousWithinAt g s x
参数：h : ContinuousWithinAt f s x；h₁ : forall y in insert x s, g y = f y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.congr`：ContinuousWithinAt.congr (h : ContinuousWithin
At f s x) (h₁ : forall y in s, g y = f y) (hx : g x = f x) : ContinuousWithinAt 
g s x
· 使用定理 `Set.mem_insert_of_mem`：mem_insert_of_mem {x : α} {s : Set α} (y : α) : x
 in s -> x in insert y s
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
-/
theorem ContinuousWithinAt.congr_of_insert (h : ContinuousWithinAt f s x)
    (h₁ : ∀ y ∈ insert x s, g y = f y) : ContinuousWithinAt g s x :=
  h.congr (fun y hy ↦ h₁ y (mem_insert_of_mem _ hy)) (h₁ x (mem_insert _ _))
/-
**continuousWithinAt_congr_of_insert** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_congr_of_insert (h₁ : forall y in insert x s, g y = f y
) : ContinuousWithinAt g s x ↔ ContinuousWithinAt f s x
参数：h₁ : forall y in insert x s, g y = f y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousWithinAt_congr`：continuousWithinAt_congr (h₁ : forall y in s, 
g y = f y) (hx : g x = f x) : ContinuousWithinAt g s x ↔ ContinuousWithinAt f s 
x
· 使用定理 `Set.mem_insert_of_mem`：mem_insert_of_mem {x : α} {s : Set α} (y : α) : x
 in s -> x in insert y s
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
-/
theorem continuousWithinAt_congr_of_insert
    (h₁ : ∀ y ∈ insert x s, g y = f y) :
    ContinuousWithinAt g s x ↔ ContinuousWithinAt f s x :=
  continuousWithinAt_congr (fun y hy ↦ h₁ y (mem_insert_of_mem _ hy)) (h₁ x (mem_insert _ _))
/-
**ContinuousWithinAt.congr_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.congr_mono (h : ContinuousWithinAt f s x) (h' : EqOn g 
f s₁) (h₁ : s₁ subseteq s) (hx : g x = f x) : ContinuousWithinAt g s₁ x
参数：h : ContinuousWithinAt f s x；h' : EqOn g f s₁；h₁ : s₁ subseteq s；hx : g x = f
 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.congr`：ContinuousWithinAt.congr (h : ContinuousWithin
At f s x) (h₁ : forall y in s, g y = f y) (hx : g x = f x) : ContinuousWithinAt 
g s x
· 使用定理 `ContinuousWithinAt.mono`：ContinuousWithinAt.mono (h : ContinuousWithinAt
 f t x) (hs : s subseteq t) : ContinuousWithinAt f s x
-/
theorem ContinuousWithinAt.congr_mono
    (h : ContinuousWithinAt f s x) (h' : EqOn g f s₁) (h₁ : s₁ ⊆ s) (hx : g x = f x) :
    ContinuousWithinAt g s₁ x :=
  (h.mono h₁).congr h' hx
/-
**ContinuousAt.congr_of_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.congr_of_eventuallyEq (h : ContinuousAt f x) (hg : g =ᶠ[𝓝 x] 
f) : ContinuousAt g x
参数：h : ContinuousAt f x；hg : g =ᶠ[𝓝 x] f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.congr`：ContinuousAt.congr {g : X -> Y} (hf : ContinuousAt f
 x) (h : f =ᶠ[𝓝 x] g) : ContinuousAt g x
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem ContinuousAt.congr_of_eventuallyEq (h : ContinuousAt f x) (hg : g =ᶠ[𝓝 x] f) :
    ContinuousAt g x :=
  congr h (EventuallyEq.symm hg)

/-!
## Composition
-/

/-
**ContinuousWithinAt.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.comp {g : β -> γ} {t : Set β} (hg : ContinuousWithinAt 
g t (f x)) (hf : ContinuousWithinAt f s x) (h : MapsTo f s t) : ContinuousWithin
At (g ∘ f) s x
参数：hg : ContinuousWithinAt g t (f x)；hf : ContinuousWithinAt f s x；h : MapsTo f 
s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ContinuousWithinAt.tendsto`：ContinuousWithinAt.tendsto (h : ContinuousWi
thinAt f s x) : Tendsto f (𝓝[s] x) (𝓝 (f x))
· 使用定理 `ContinuousWithinAt.tendsto_nhdsWithin`：ContinuousWithinAt.tendsto_nhdsWi
thin {t : Set β} (h : ContinuousWithinAt f s x) (ht : MapsTo f s t) : Tendsto f 
(𝓝[s] x) (𝓝[t] f x)

--- 原说明 ---
## Composition
-/
theorem ContinuousWithinAt.comp {g : β → γ} {t : Set β}
    (hg : ContinuousWithinAt g t (f x)) (hf : ContinuousWithinAt f s x) (h : MapsTo f s t) :
    ContinuousWithinAt (g ∘ f) s x :=
  hg.tendsto.comp (hf.tendsto_nhdsWithin h)
/-
**ContinuousWithinAt.comp_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.comp_of_eq {g : β -> γ} {t : Set β} {y : β} (hg : Conti
nuousWithinAt g t y) (hf : ContinuousWithinAt f s x) (h : MapsTo f s t) (hy : f 
x = y) : ContinuousWithinAt (g ∘ f) s x
参数：hg : ContinuousWithinAt g t y；hf : ContinuousWithinAt f s x；h : MapsTo f s t；
hy : f x = y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.comp`：ContinuousWithinAt.comp {g : β -> γ} {t : Set β
} (hg : ContinuousWithinAt g t (f x)) (hf : ContinuousWithinAt f s x) (h : MapsT
o f s t) : Co…
-/
theorem ContinuousWithinAt.comp_of_eq {g : β → γ} {t : Set β} {y : β}
    (hg : ContinuousWithinAt g t y) (hf : ContinuousWithinAt f s x) (h : MapsTo f s t)
    (hy : f x = y) : ContinuousWithinAt (g ∘ f) s x := by
  subst hy; exact hg.comp hf h
/-
**ContinuousWithinAt.comp_inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.comp_inter {g : β -> γ} {t : Set β} (hg : ContinuousWit
hinAt g t (f x)) (hf : ContinuousWithinAt f s x) : ContinuousWithinAt (g ∘ f) (s
 inter f ⁻¹' t) x
参数：hg : ContinuousWithinAt g t (f x)；hf : ContinuousWithinAt f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.comp`：ContinuousWithinAt.comp {g : β -> γ} {t : Set β
} (hg : ContinuousWithinAt g t (f x)) (hf : ContinuousWithinAt f s x) (h : MapsT
o f s t) : Co…
· 使用定理 `ContinuousWithinAt.mono`：ContinuousWithinAt.mono (h : ContinuousWithinAt
 f t x) (hs : s subseteq t) : ContinuousWithinAt f s x
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
theorem ContinuousWithinAt.comp_inter {g : β → γ} {t : Set β}
    (hg : ContinuousWithinAt g t (f x)) (hf : ContinuousWithinAt f s x) :
    ContinuousWithinAt (g ∘ f) (s ∩ f ⁻¹' t) x :=
  hg.comp (hf.mono inter_subset_left) inter_subset_right
/-
**ContinuousWithinAt.comp_inter_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.comp_inter_of_eq {g : β -> γ} {t : Set β} {y : β} (hg :
 ContinuousWithinAt g t y) (hf : ContinuousWithinAt f s x) (hy : f x = y) : Cont
inuousWithinAt (g ∘ f) (s inter f ⁻¹' t) x
参数：hg : ContinuousWithinAt g t y；hf : ContinuousWithinAt f s x；hy : f x = y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.comp_inter`：ContinuousWithinAt.comp_inter {g : β -> γ
} {t : Set β} (hg : ContinuousWithinAt g t (f x)) (hf : ContinuousWithinAt f s x
) : ContinuousWithi…
-/
theorem ContinuousWithinAt.comp_inter_of_eq {g : β → γ} {t : Set β} {y : β}
    (hg : ContinuousWithinAt g t y) (hf : ContinuousWithinAt f s x) (hy : f x = y) :
    ContinuousWithinAt (g ∘ f) (s ∩ f ⁻¹' t) x := by
  subst hy; exact hg.comp_inter hf
/-
**ContinuousWithinAt.comp_of_preimage_mem_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：ContinuousWithinAt.comp_of_preimage_mem_nhdsWithin {g : β -> γ} {t : Set β
} (hg : ContinuousWithinAt g t (f x)) (hf : ContinuousWithinAt f s x) (h : f ⁻¹'
 t in 𝓝[s] x) : ContinuousWithinAt (g ∘ f) s x
参数：hg : ContinuousWithinAt g t (f x)；hf : ContinuousWithinAt f s x；h : f ⁻¹' t i
n 𝓝[s] x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ContinuousWithinAt.tendsto`：ContinuousWithinAt.tendsto (h : ContinuousWi
thinAt f s x) : Tendsto f (𝓝[s] x) (𝓝 (f x))
· 使用定理 `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within`：tendsto_nhdsWit
hin_of_tendsto_nhds_of_eventually_within {a : α} {l : Filter β} {s : Set α} (f :
 β -> α) (h1 : Tendsto f l (𝓝 a)) (h2 : foral…
-/
theorem ContinuousWithinAt.comp_of_preimage_mem_nhdsWithin {g : β → γ} {t : Set β}
    (hg : ContinuousWithinAt g t (f x)) (hf : ContinuousWithinAt f s x) (h : f ⁻¹' t ∈ 𝓝[s] x) :
    ContinuousWithinAt (g ∘ f) s x :=
  hg.tendsto.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within f hf h)
/-
**ContinuousWithinAt.comp_of_preimage_mem_nhdsWithin_of_eq** 是 Mathlib 中的一个定理，位于
命名空间 ``。
形式化陈述：ContinuousWithinAt.comp_of_preimage_mem_nhdsWithin_of_eq {g : β -> γ} {t :
 Set β} {y : β} (hg : ContinuousWithinAt g t y) (hf : ContinuousWithinAt f s x) 
(h : f ⁻¹' t in 𝓝[s] x) (hy : f x = y) : ContinuousWithinAt (g ∘ f) s x
参数：hg : ContinuousWithinAt g t y；hf : ContinuousWithinAt f s x；h : f ⁻¹' t in 𝓝[
s] x；hy : f x = y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.comp_of_preimage_mem_nhdsWithin`：ContinuousWithinAt.c
omp_of_preimage_mem_nhdsWithin {g : β -> γ} {t : Set β} (hg : ContinuousWithinAt
 g t (f x)) (hf : ContinuousWithinAt f s…
-/
theorem ContinuousWithinAt.comp_of_preimage_mem_nhdsWithin_of_eq {g : β → γ} {t : Set β} {y : β}
    (hg : ContinuousWithinAt g t y) (hf : ContinuousWithinAt f s x) (h : f ⁻¹' t ∈ 𝓝[s] x)
    (hy : f x = y) :
    ContinuousWithinAt (g ∘ f) s x := by
  subst hy; exact hg.comp_of_preimage_mem_nhdsWithin hf h
/-
**ContinuousWithinAt.comp_of_mem_nhdsWithin_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.comp_of_mem_nhdsWithin_image {g : β -> γ} {t : Set β} (
hg : ContinuousWithinAt g t (f x)) (hf : ContinuousWithinAt f s x) (hs : t in 𝓝[
f '' s] f x) : ContinuousWithinAt (g ∘ f) s x
参数：hg : ContinuousWithinAt g t (f x)；hf : ContinuousWithinAt f s x；hs : t in 𝓝[f
 '' s] f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.comp`：ContinuousWithinAt.comp {g : β -> γ} {t : Set β
} (hg : ContinuousWithinAt g t (f x)) (hf : ContinuousWithinAt f s x) (h : MapsT
o f s t) : Co…
· 使用定理 `ContinuousWithinAt.mono_of_mem_nhdsWithin`：ContinuousWithinAt.mono_of_me
m_nhdsWithin (h : ContinuousWithinAt f t x) (hs : t in 𝓝[s] x) : ContinuousWithi
nAt f s x
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
-/
theorem ContinuousWithinAt.comp_of_mem_nhdsWithin_image {g : β → γ} {t : Set β}
    (hg : ContinuousWithinAt g t (f x)) (hf : ContinuousWithinAt f s x)
    (hs : t ∈ 𝓝[f '' s] f x) : ContinuousWithinAt (g ∘ f) s x :=
  (hg.mono_of_mem_nhdsWithin hs).comp hf (mapsTo_image f s)
/-
**ContinuousWithinAt.comp_of_mem_nhdsWithin_image_of_eq** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：ContinuousWithinAt.comp_of_mem_nhdsWithin_image_of_eq {g : β -> γ} {t : Se
t β} {y : β} (hg : ContinuousWithinAt g t y) (hf : ContinuousWithinAt f s x) (hs
 : t in 𝓝[f '' s] y) (hy : f x = y) : ContinuousWithinAt (g ∘ f) s x
参数：hg : ContinuousWithinAt g t y；hf : ContinuousWithinAt f s x；hs : t in 𝓝[f '' 
s] y；hy : f x = y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.comp_of_mem_nhdsWithin_image`：ContinuousWithinAt.comp
_of_mem_nhdsWithin_image {g : β -> γ} {t : Set β} (hg : ContinuousWithinAt g t (
f x)) (hf : ContinuousWithinAt f s x)…
-/
theorem ContinuousWithinAt.comp_of_mem_nhdsWithin_image_of_eq {g : β → γ} {t : Set β} {y : β}
    (hg : ContinuousWithinAt g t y) (hf : ContinuousWithinAt f s x)
    (hs : t ∈ 𝓝[f '' s] y) (hy : f x = y) : ContinuousWithinAt (g ∘ f) s x := by
  subst hy; exact hg.comp_of_mem_nhdsWithin_image hf hs
/-
**ContinuousAt.comp_continuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAt`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : TopologicalSpace α]
 [inst_1 : TopologicalSpace β]   [inst_2 : TopologicalSpace γ] {f : α → β} {s : 
Set α} {x : α} {g : β → γ},   ContinuousAt g (f x) → ContinuousWithinAt f s x → 
ContinuousWithinAt (g ∘ f) s x
参数：f x；g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.comp`：ContinuousWithinAt.comp {g : β -> γ} {t : Set β
} (hg : ContinuousWithinAt g t (f x)) (hf : ContinuousWithinAt f s x) (h : MapsT
o f s t) : Co…
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ
-/
@[fun_prop] theorem ContinuousAt.comp_continuousWithinAt {g : β → γ}
    (hg : ContinuousAt g (f x)) (hf : ContinuousWithinAt f s x) : ContinuousWithinAt (g ∘ f) s x :=
  hg.continuousWithinAt.comp hf (mapsTo_univ _ _)
/-
**ContinuousAt.comp_continuousWithinAt_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.comp_continuousWithinAt_of_eq {g : β -> γ} {y : β} (hg : Cont
inuousAt g y) (hf : ContinuousWithinAt f s x) (hy : f x = y) : ContinuousWithinA
t (g ∘ f) s x
参数：hg : ContinuousAt g y；hf : ContinuousWithinAt f s x；hy : f x = y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.comp_continuousWithinAt`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2
 : TopologicalSpace γ] {f …
-/
theorem ContinuousAt.comp_continuousWithinAt_of_eq {g : β → γ} {y : β}
    (hg : ContinuousAt g y) (hf : ContinuousWithinAt f s x) (hy : f x = y) :
    ContinuousWithinAt (g ∘ f) s x := by
  subst hy; exact hg.comp_continuousWithinAt hf

/-- See also `ContinuousOn.comp'` using the form `fun y ↦ g (f y)` instead of `g ∘ f`. -/
/-
**ContinuousOn.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : ContinuousOn g t) (hf : C
ontinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) s
参数：hg : ContinuousOn g t；hf : ContinuousOn f s；h : MapsTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.comp`：ContinuousWithinAt.comp {g : β -> γ} {t : Set β
} (hg : ContinuousWithinAt g t (f x)) (hf : ContinuousWithinAt f s x) (h : MapsT
o f s t) : Co…

--- 原说明 ---
See also `ContinuousOn.comp'` using the form `fun y ↦ g (f y)` instead of `g ∘ f
`.
-/
theorem ContinuousOn.comp {g : β → γ} {t : Set β} (hg : ContinuousOn g t)
    (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) s := fun x hx =>
  ContinuousWithinAt.comp (hg _ (h hx)) (hf x hx) h

/-- Variant of `ContinuousOn.comp` using the form `fun y ↦ g (f y)` instead of `g ∘ f`. -/
@[fun_prop]
/-
**ContinuousOn.comp'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.comp' {g : β -> γ} {f : α -> β} {s : Set α} {t : Set β} (hg :
 ContinuousOn g t) (hf : ContinuousOn f s) (h : Set.MapsTo f s t) : ContinuousOn
 (fun x => g (f x)) s
参数：hg : ContinuousOn g t；hf : ContinuousOn f s；h : Set.MapsTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s

--- 原说明 ---
Variant of `ContinuousOn.comp` using the form `fun y ↦ g (f y)` instead of `g ∘ 
f`.
-/
theorem ContinuousOn.comp' {g : β → γ} {f : α → β} {s : Set α} {t : Set β} (hg : ContinuousOn g t)
    (hf : ContinuousOn f s) (h : Set.MapsTo f s t) : ContinuousOn (fun x => g (f x)) s :=
  ContinuousOn.comp hg hf h

@[fun_prop]
/-
**ContinuousOn.comp_inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.comp_inter {g : β -> γ} {t : Set β} (hg : ContinuousOn g t) (
hf : ContinuousOn f s) : ContinuousOn (g ∘ f) (s inter f ⁻¹' t)
参数：hg : ContinuousOn g t；hf : ContinuousOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
theorem ContinuousOn.comp_inter {g : β → γ} {t : Set β} (hg : ContinuousOn g t)
    (hf : ContinuousOn f s) : ContinuousOn (g ∘ f) (s ∩ f ⁻¹' t) :=
  hg.comp (hf.mono inter_subset_left) inter_subset_right

/-- See also `Continuous.comp_continuousOn'` using the form `fun y ↦ g (f y)`
instead of `g ∘ f`. -/
/-
**Continuous.comp_continuousOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.comp_continuousOn {g : β -> γ} {f : α -> β} {s : Set α} (hg : C
ontinuous g) (hf : ContinuousOn f s) : ContinuousOn (g ∘ f) s
参数：hg : Continuous g；hf : ContinuousOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ

--- 原说明 ---
See also `Continuous.comp_continuousOn'` using the form `fun y ↦ g (f y)`
instead of `g ∘ f`.
-/
theorem Continuous.comp_continuousOn {g : β → γ} {f : α → β} {s : Set α} (hg : Continuous g)
    (hf : ContinuousOn f s) : ContinuousOn (g ∘ f) s :=
  hg.continuousOn.comp hf (mapsTo_univ _ _)

/-- Variant of `Continuous.comp_continuousOn` using the form `fun y ↦ g (f y)`
instead of `g ∘ f`. -/
@[fun_prop]
/-
**Continuous.comp_continuousOn'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.comp_continuousOn' {g : β -> γ} {f : α -> β} {s : Set α} (hg : 
Continuous g) (hf : ContinuousOn f s) : ContinuousOn (fun x => g (f x)) s
参数：hg : Continuous g；hf : ContinuousOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp_continuousOn`：Continuous.comp_continuousOn {g : β -> γ} 
{f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continuou
sOn (g ∘ f) s

--- 原说明 ---
Variant of `Continuous.comp_continuousOn` using the form `fun y ↦ g (f y)`
instead of `g ∘ f`.
-/
theorem Continuous.comp_continuousOn' {g : β → γ} {f : α → β} {s : Set α} (hg : Continuous g)
    (hf : ContinuousOn f s) : ContinuousOn (fun x ↦ g (f x)) s :=
  hg.comp_continuousOn hf
/-
**ContinuousOn.comp_continuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.comp_continuous {g : β -> γ} {f : α -> β} {s : Set β} (hg : C
ontinuousOn g s) (hf : Continuous f) (hs : forall x, f x in s) : Continuous (g ∘
 f)
参数：hg : ContinuousOn g s；hf : Continuous f；hs : forall x, f x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuousOn_univ`：continuousOn_univ {f : α -> β} : ContinuousOn f univ 
↔ Continuous f
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
-/
theorem ContinuousOn.comp_continuous {g : β → γ} {f : α → β} {s : Set β} (hg : ContinuousOn g s)
    (hf : Continuous f) (hs : ∀ x, f x ∈ s) : Continuous (g ∘ f) := by
  rw [← continuousOn_univ] at *
  exact hg.comp hf fun x _ => hs x
/-
**ContinuousOn.image_comp_continuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.image_comp_continuous {g : β -> γ} {f : α -> β} {s : Set α} (
hg : ContinuousOn g (f '' s)) (hf : Continuous f) : ContinuousOn (g ∘ f) s
参数：hg : ContinuousOn g (f '' s)；hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
-/
theorem ContinuousOn.image_comp_continuous {g : β → γ} {f : α → β} {s : Set α}
    (hg : ContinuousOn g (f '' s)) (hf : Continuous f) : ContinuousOn (g ∘ f) s :=
  hg.comp hf.continuousOn (s.mapsTo_image f)
/-
**ContinuousAt.comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAt`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst : TopologicalSpace X]
 [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace Z] {f : X → Y} {x : 
X} {g : Y → Z},   ContinuousAt g (f x) → ContinuousAt f x → ContinuousAt (g ∘ f)
 x
参数：f x；g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
-/
theorem ContinuousAt.comp₂_continuousWithinAt {f : β × γ → δ} {g : α → β} {h : α → γ} {x : α}
    {s : Set α} (hf : ContinuousAt f (g x, h x)) (hg : ContinuousWithinAt g s x)
    (hh : ContinuousWithinAt h s x) :
    ContinuousWithinAt (fun x ↦ f (g x, h x)) s x :=
  ContinuousAt.comp_continuousWithinAt hf (hg.prodMk_nhds hh)
/-
**ContinuousAt.comp** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAt`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst : TopologicalSpace X]
 [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace Z] {f : X → Y} {x : 
X} {g : Y → Z},   ContinuousAt g (f x) → ContinuousAt f x → ContinuousAt (g ∘ f)
 x
参数：f x；g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
-/
theorem ContinuousAt.comp₂_continuousWithinAt_of_eq {f : β × γ → δ} {g : α → β}
    {h : α → γ} {x : α} {s : Set α} {y : β × γ} (hf : ContinuousAt f y)
    (hg : ContinuousWithinAt g s x) (hh : ContinuousWithinAt h s x) (e : (g x, h x) = y) :
    ContinuousWithinAt (fun x ↦ f (g x, h x)) s x := by
  rw [← e] at hf
  exact hf.comp₂_continuousWithinAt hg hh

/-!
## Image
-/

/-
**ContinuousWithinAt.mem_closure_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.mem_closure_image (h : ContinuousWithinAt f s x) (hx : 
x in closure s) : f x in closure (f '' s)
参数：h : ContinuousWithinAt f s x；hx : x in closure s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_closure_of_tendsto`：mem_closure_of_tendsto {f : α -> X} {b : Filter 
α} [NeBot b] (hf : Tendsto f b (𝓝 x)) (h : forallᶠ x in b, f x in s) : x in clos
ure s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_closure_iff_nhdsWithin_neBot`：mem_closure_iff_nhdsWithin_neBot : x i
n closure s ↔ NeBot (𝓝[s] x)
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Set.subset_preimage_image`：subset_preimage_image (f : α -> β) (s : Set α
) : s subseteq f ⁻¹' f '' s

--- 原说明 ---
## Image
-/
theorem ContinuousWithinAt.mem_closure_image
    (h : ContinuousWithinAt f s x) (hx : x ∈ closure s) : f x ∈ closure (f '' s) :=
  haveI := mem_closure_iff_nhdsWithin_neBot.1 hx
  mem_closure_of_tendsto h <| mem_of_superset self_mem_nhdsWithin (subset_preimage_image f s)
/-
**ContinuousWithinAt.mem_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.mem_closure {t : Set β} (h : ContinuousWithinAt f s x) 
(hx : x in closure s) (ht : MapsTo f s t) : f x in closure t
参数：h : ContinuousWithinAt f s x；hx : x in closure s；ht : MapsTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `ContinuousWithinAt.mem_closure_image`：ContinuousWithinAt.mem_closure_ima
ge (h : ContinuousWithinAt f s x) (hx : x in closure s) : f x in closure (f '' s
)
-/
theorem ContinuousWithinAt.mem_closure {t : Set β}
    (h : ContinuousWithinAt f s x) (hx : x ∈ closure s) (ht : MapsTo f s t) : f x ∈ closure t :=
  closure_mono (image_subset_iff.2 ht) (h.mem_closure_image hx)
/-
**Set.MapsTo.closure_of_continuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.MapsTo.closure_of_continuousWithinAt {t : Set β} (h : MapsTo f s t) (h
c : forall x in closure s, ContinuousWithinAt f s x) : MapsTo f (closure s) (clo
sure t)
参数：h : MapsTo f s t；hc : forall x in closure s, ContinuousWithinAt f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.mem_closure`：ContinuousWithinAt.mem_closure {t : Set 
β} (h : ContinuousWithinAt f s x) (hx : x in closure s) (ht : MapsTo f s t) : f 
x in closure t
-/
theorem Set.MapsTo.closure_of_continuousWithinAt {t : Set β}
    (h : MapsTo f s t) (hc : ∀ x ∈ closure s, ContinuousWithinAt f s x) :
    MapsTo f (closure s) (closure t) := fun x hx => (hc x hx).mem_closure hx h
/-
**Set.MapsTo.closure_of_continuousOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.MapsTo.closure_of_continuousOn {t : Set β} (h : MapsTo f s t) (hc : Co
ntinuousOn f (closure s)) : MapsTo f (closure s) (closure t)
参数：h : MapsTo f s t；hc : ContinuousOn f (closure s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.closure_of_continuousWithinAt`：Set.MapsTo.closure_of_continuo
usWithinAt {t : Set β} (h : MapsTo f s t) (hc : forall x in closure s, Continuou
sWithinAt f s x) : MapsTo f (c…
· 使用定理 `ContinuousWithinAt.mono`：ContinuousWithinAt.mono (h : ContinuousWithinAt
 f t x) (hs : s subseteq t) : ContinuousWithinAt f s x
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem Set.MapsTo.closure_of_continuousOn {t : Set β} (h : MapsTo f s t)
    (hc : ContinuousOn f (closure s)) : MapsTo f (closure s) (closure t) :=
  h.closure_of_continuousWithinAt fun x hx => (hc x hx).mono subset_closure
/-
**ContinuousWithinAt.image_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.image_closure (hf : forall x in closure s, ContinuousWi
thinAt f s x) : f '' closure s subseteq closure (f '' s)
参数：hf : forall x in closure s, ContinuousWithinAt f s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.image_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β}, Set.MapsTo f s t → f '' s ⊆ t
· 使用定理 `Set.MapsTo.closure_of_continuousWithinAt`：Set.MapsTo.closure_of_continuo
usWithinAt {t : Set β} (h : MapsTo f s t) (hc : forall x in closure s, Continuou
sWithinAt f s x) : MapsTo f (c…
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
-/
theorem ContinuousWithinAt.image_closure
    (hf : ∀ x ∈ closure s, ContinuousWithinAt f s x) : f '' closure s ⊆ closure (f '' s) :=
  ((mapsTo_image f s).closure_of_continuousWithinAt hf).image_subset
/-
**ContinuousOn.image_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.image_closure (hf : ContinuousOn f (closure s)) : f '' closur
e s subseteq closure (f '' s)
参数：hf : ContinuousOn f (closure s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.image_closure`：ContinuousWithinAt.image_closure (hf :
 forall x in closure s, ContinuousWithinAt f s x) : f '' closure s subseteq clos
ure (f '' s)
· 使用定理 `ContinuousWithinAt.mono`：ContinuousWithinAt.mono (h : ContinuousWithinAt
 f t x) (hs : s subseteq t) : ContinuousWithinAt f s x
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem ContinuousOn.image_closure (hf : ContinuousOn f (closure s)) :
    f '' closure s ⊆ closure (f '' s) :=
  ContinuousWithinAt.image_closure fun x hx => (hf x hx).mono subset_closure

/-!
## Product
-/

/-
**ContinuousWithinAt.prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.prodMk {f : α -> β} {g : α -> γ} {s : Set α} {x : α} (h
f : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) : ContinuousWithin
At (fun x => (f x, g x)) s x
参数：hf : ContinuousWithinAt f s x；hg : ContinuousWithinAt g s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.prodMk_nhds`：Filter.Tendsto.prodMk_nhds {γ} {x : X} {y : 
Y} {f : Filter γ} {mx : γ -> X} {my : γ -> Y} (hx : Tendsto mx f (𝓝 x)) (hy : Te
ndsto my f (𝓝 y)…

--- 原说明 ---
## Product
-/
theorem ContinuousWithinAt.prodMk {f : α → β} {g : α → γ} {s : Set α} {x : α}
    (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (fun x => (f x, g x)) s x :=
  hf.prodMk_nhds hg

@[fun_prop]
/-
**ContinuousOn.prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.prodMk {f : α -> β} {g : α -> γ} {s : Set α} (hf : Continuous
On f s) (hg : ContinuousOn g s) : ContinuousOn (fun x => (f x, g x)) s
参数：hf : ContinuousOn f s；hg : ContinuousOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.prodMk`：ContinuousWithinAt.prodMk {f : α -> β} {g : α
 -> γ} {s : Set α} {x : α} (hf : ContinuousWithinAt f s x) (hg : ContinuousWithi
nAt g s x) : Co…
-/
theorem ContinuousOn.prodMk {f : α → β} {g : α → γ} {s : Set α} (hf : ContinuousOn f s)
    (hg : ContinuousOn g s) : ContinuousOn (fun x => (f x, g x)) s := fun x hx =>
  (hf x hx).prodMk (hg x hx)
/-
**continuousOn_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_fst {s : Set (α × β)} : ContinuousOn Prod.fst s
参数：α × β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
-/
theorem continuousOn_fst {s : Set (α × β)} : ContinuousOn Prod.fst s :=
  continuous_fst.continuousOn
/-
**continuousWithinAt_fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_fst {s : Set (α × β)} {p : α × β} : ContinuousWithinAt 
Prod.fst s p
参数：α × β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousWithinAt`：Continuous.continuousWithinAt (h : Contin
uous f) : ContinuousWithinAt f s x
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
-/
theorem continuousWithinAt_fst {s : Set (α × β)} {p : α × β} : ContinuousWithinAt Prod.fst s p :=
  continuous_fst.continuousWithinAt

@[fun_prop]
/-
**ContinuousOn.fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.fst {f : α -> β × γ} {s : Set α} (hf : ContinuousOn f s) : Co
ntinuousOn (fun x => (f x).1) s
参数：hf : ContinuousOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp_continuousOn`：Continuous.comp_continuousOn {g : β -> γ} 
{f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continuou
sOn (g ∘ f) s
· 使用定理 `continuous_fst`：continuous_fst (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).fst)
-/
theorem ContinuousOn.fst {f : α → β × γ} {s : Set α} (hf : ContinuousOn f s) :
    ContinuousOn (fun x => (f x).1) s :=
  continuous_fst.comp_continuousOn hf
/-
**ContinuousWithinAt.fst** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.fst {f : α -> β × γ} {s : Set α} {a : α} (h : Continuou
sWithinAt f s a) : ContinuousWithinAt (fun x => (f x).fst) s a
参数：h : ContinuousWithinAt f s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.comp_continuousWithinAt`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2
 : TopologicalSpace γ] {f …
· 使用定理 `continuousAt_fst`：continuousAt_fst {p : X × Y} : ContinuousAt Prod.fst p
-/
theorem ContinuousWithinAt.fst {f : α → β × γ} {s : Set α} {a : α} (h : ContinuousWithinAt f s a) :
    ContinuousWithinAt (fun x => (f x).fst) s a :=
  continuousAt_fst.comp_continuousWithinAt h
/-
**continuousOn_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_snd {s : Set (α × β)} : ContinuousOn Prod.snd s
参数：α × β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
-/
theorem continuousOn_snd {s : Set (α × β)} : ContinuousOn Prod.snd s :=
  continuous_snd.continuousOn
/-
**continuousWithinAt_snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_snd {s : Set (α × β)} {p : α × β} : ContinuousWithinAt 
Prod.snd s p
参数：α × β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousWithinAt`：Continuous.continuousWithinAt (h : Contin
uous f) : ContinuousWithinAt f s x
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
-/
theorem continuousWithinAt_snd {s : Set (α × β)} {p : α × β} : ContinuousWithinAt Prod.snd s p :=
  continuous_snd.continuousWithinAt

@[fun_prop]
/-
**ContinuousOn.snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.snd {f : α -> β × γ} {s : Set α} (hf : ContinuousOn f s) : Co
ntinuousOn (fun x => (f x).2) s
参数：hf : ContinuousOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp_continuousOn`：Continuous.comp_continuousOn {g : β -> γ} 
{f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continuou
sOn (g ∘ f) s
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
-/
theorem ContinuousOn.snd {f : α → β × γ} {s : Set α} (hf : ContinuousOn f s) :
    ContinuousOn (fun x => (f x).2) s :=
  continuous_snd.comp_continuousOn hf
/-
**ContinuousWithinAt.snd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.snd {f : α -> β × γ} {s : Set α} {a : α} (h : Continuou
sWithinAt f s a) : ContinuousWithinAt (fun x => (f x).snd) s a
参数：h : ContinuousWithinAt f s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.comp_continuousWithinAt`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2
 : TopologicalSpace γ] {f …
· 使用定理 `continuousAt_snd`：continuousAt_snd {p : X × Y} : ContinuousAt Prod.snd p
-/
theorem ContinuousWithinAt.snd {f : α → β × γ} {s : Set α} {a : α} (h : ContinuousWithinAt f s a) :
    ContinuousWithinAt (fun x => (f x).snd) s a :=
  continuousAt_snd.comp_continuousWithinAt h
/-
**continuousWithinAt_prod_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_prod_iff {f : α -> β × γ} {s : Set α} {x : α} : Continu
ousWithinAt f s x ↔ ContinuousWithinAt (Prod.fst ∘ f) s x ∧ ContinuousWithinAt (
Prod.snd ∘ f) s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.fst`：ContinuousWithinAt.fst {f : α -> β × γ} {s : Set
 α} {a : α} (h : ContinuousWithinAt f s a) : ContinuousWithinAt (fun x => (f x).
fst) s a
· 使用定理 `ContinuousWithinAt.snd`：ContinuousWithinAt.snd {f : α -> β × γ} {s : Set
 α} {a : α} (h : ContinuousWithinAt f s a) : ContinuousWithinAt (fun x => (f x).
snd) s a
· 使用定理 `ContinuousWithinAt.prodMk`：ContinuousWithinAt.prodMk {f : α -> β} {g : α
 -> γ} {s : Set α} {x : α} (hf : ContinuousWithinAt f s x) (hg : ContinuousWithi
nAt g s x) : Co…
-/
theorem continuousWithinAt_prod_iff {f : α → β × γ} {s : Set α} {x : α} :
    ContinuousWithinAt f s x ↔
      ContinuousWithinAt (Prod.fst ∘ f) s x ∧ ContinuousWithinAt (Prod.snd ∘ f) s x :=
  ⟨fun h => ⟨h.fst, h.snd⟩, fun ⟨h1, h2⟩ => h1.prodMk h2⟩
/-
**ContinuousWithinAt.prodMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.prodMap {f : α -> γ} {g : β -> δ} {s : Set α} {t : Set 
β} {x : α} {y : β} (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g t 
y) : ContinuousWithinAt (Prod.map f g) (s ×ˢ t) (x, y)
参数：hf : ContinuousWithinAt f s x；hg : ContinuousWithinAt g t y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.prodMk`：ContinuousWithinAt.prodMk {f : α -> β} {g : α
 -> γ} {s : Set α} {x : α} (hf : ContinuousWithinAt f s x) (hg : ContinuousWithi
nAt g s x) : Co…
· 使用定理 `ContinuousWithinAt.comp`：ContinuousWithinAt.comp {g : β -> γ} {t : Set β
} (hg : ContinuousWithinAt g t (f x)) (hf : ContinuousWithinAt f s x) (h : MapsT
o f s t) : Co…
· 使用定理 `continuousWithinAt_fst`：continuousWithinAt_fst {s : Set (α × β)} {p : α 
× β} : ContinuousWithinAt Prod.fst s p
· 使用引理 `Set.mapsTo_fst_prod`：mapsTo_fst_prod {s : Set α} {t : Set β} : MapsTo Pr
od.fst (s ×ˢ t) s
· 使用定理 `continuousWithinAt_snd`：continuousWithinAt_snd {s : Set (α × β)} {p : α 
× β} : ContinuousWithinAt Prod.snd s p
· 使用引理 `Set.mapsTo_snd_prod`：mapsTo_snd_prod {s : Set α} {t : Set β} : MapsTo Pr
od.snd (s ×ˢ t) t
-/
theorem ContinuousWithinAt.prodMap {f : α → γ} {g : β → δ} {s : Set α} {t : Set β} {x : α} {y : β}
    (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g t y) :
    ContinuousWithinAt (Prod.map f g) (s ×ˢ t) (x, y) :=
  .prodMk (hf.comp continuousWithinAt_fst mapsTo_fst_prod)
    (hg.comp continuousWithinAt_snd mapsTo_snd_prod)
/-
**ContinuousOn.prodMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.prodMap {f : α -> γ} {g : β -> δ} {s : Set α} {t : Set β} (hf
 : ContinuousOn f s) (hg : ContinuousOn g t) : ContinuousOn (Prod.map f g) (s ×ˢ
 t)
参数：hf : ContinuousOn f s；hg : ContinuousOn g t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.prodMap`：ContinuousWithinAt.prodMap {f : α -> γ} {g :
 β -> δ} {s : Set α} {t : Set β} {x : α} {y : β} (hf : ContinuousWithinAt f s x)
 (hg : Continuou…
-/
theorem ContinuousOn.prodMap {f : α → γ} {g : β → δ} {s : Set α} {t : Set β} (hf : ContinuousOn f s)
    (hg : ContinuousOn g t) : ContinuousOn (Prod.map f g) (s ×ˢ t) := fun ⟨x, y⟩ ⟨hx, hy⟩ =>
  (hf x hx).prodMap (hg y hy)
/-
**continuousWithinAt_prod_of_discrete_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_prod_of_discrete_left [DiscreteTopology α] {f : α × β -
> γ} {s : Set (α × β)} {x : α × β} : ContinuousWithinAt f s x ↔ ContinuousWithin
At (f ⟨x.1, ·⟩) {b | (x.1, b) in s} x.2
参数：α × β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Prod.eta`：∀ {α : Type u_1} {β : Type u_2} (p : α × β), (p.1, p.2) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `nhds_discrete`：nhds_discrete (α : Type*) [TopologicalSpace α] [DiscreteT
opology α] : @nhds α _ = pure
· 使用定理 `Filter.pure_prod`：pure_prod {a : α} {f : Filter β} : pure a ×ˢ f = map (
Prod.mk a) f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem continuousWithinAt_prod_of_discrete_left [DiscreteTopology α]
    {f : α × β → γ} {s : Set (α × β)} {x : α × β} :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt (f ⟨x.1, ·⟩) {b | (x.1, b) ∈ s} x.2 := by
  rw [← x.eta]; simp_rw [ContinuousWithinAt, nhdsWithin, nhds_prod_eq, nhds_discrete, pure_prod,
    ← map_inf_principal_preimage]; rfl
/-
**continuousWithinAt_prod_of_discrete_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_prod_of_discrete_right [DiscreteTopology β] {f : α × β 
-> γ} {s : Set (α × β)} {x : α × β} : ContinuousWithinAt f s x ↔ ContinuousWithi
nAt (f ⟨·, x.2⟩) {a | (a, x.2) in s} x.1
参数：α × β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Prod.eta`：∀ {α : Type u_1} {β : Type u_2} (p : α × β), (p.1, p.2) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `nhds_discrete`：nhds_discrete (α : Type*) [TopologicalSpace α] [DiscreteT
opology α] : @nhds α _ = pure
· 使用定理 `Filter.prod_pure`：prod_pure {b : β} : f ×ˢ pure b = map (fun a => (a, b)
) f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem continuousWithinAt_prod_of_discrete_right [DiscreteTopology β]
    {f : α × β → γ} {s : Set (α × β)} {x : α × β} :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt (f ⟨·, x.2⟩) {a | (a, x.2) ∈ s} x.1 := by
  rw [← x.eta]; simp_rw [ContinuousWithinAt, nhdsWithin, nhds_prod_eq, nhds_discrete, prod_pure,
    ← map_inf_principal_preimage]; rfl
/-
**continuousAt_prod_of_discrete_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_prod_of_discrete_left [DiscreteTopology α] {f : α × β -> γ} {
x : α × β} : ContinuousAt f x ↔ ContinuousAt (f ⟨x.1, ·⟩) x.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuousWithinAt_prod_of_discrete_left`：continuousWithinAt_prod_of_dis
crete_left [DiscreteTopology α] {f : α × β -> γ} {s : Set (α × β)} {x : α × β} :
 ContinuousWithinAt f s x ↔ Co…
-/
theorem continuousAt_prod_of_discrete_left [DiscreteTopology α] {f : α × β → γ} {x : α × β} :
    ContinuousAt f x ↔ ContinuousAt (f ⟨x.1, ·⟩) x.2 := by
  simp_rw [← continuousWithinAt_univ]; exact continuousWithinAt_prod_of_discrete_left
/-
**continuousAt_prod_of_discrete_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_prod_of_discrete_right [DiscreteTopology β] {f : α × β -> γ} 
{x : α × β} : ContinuousAt f x ↔ ContinuousAt (f ⟨·, x.2⟩) x.1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuousWithinAt_prod_of_discrete_right`：continuousWithinAt_prod_of_di
screte_right [DiscreteTopology β] {f : α × β -> γ} {s : Set (α × β)} {x : α × β}
 : ContinuousWithinAt f s x ↔ C…
-/
theorem continuousAt_prod_of_discrete_right [DiscreteTopology β] {f : α × β → γ} {x : α × β} :
    ContinuousAt f x ↔ ContinuousAt (f ⟨·, x.2⟩) x.1 := by
  simp_rw [← continuousWithinAt_univ]; exact continuousWithinAt_prod_of_discrete_right
/-
**continuousOn_prod_of_discrete_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_prod_of_discrete_left [DiscreteTopology α] {f : α × β -> γ} {
s : Set (α × β)} : ContinuousOn f s ↔ forall a, ContinuousOn (f ⟨a, ·⟩) {b | (a,
 b) in s}
参数：α × β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem continuousOn_prod_of_discrete_left [DiscreteTopology α] {f : α × β → γ} {s : Set (α × β)} :
    ContinuousOn f s ↔ ∀ a, ContinuousOn (f ⟨a, ·⟩) {b | (a, b) ∈ s} := by
  simp_rw [ContinuousOn, Prod.forall, continuousWithinAt_prod_of_discrete_left]; rfl
/-
**continuousOn_prod_of_discrete_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_prod_of_discrete_right [DiscreteTopology β] {f : α × β -> γ} 
{s : Set (α × β)} : ContinuousOn f s ↔ forall b, ContinuousOn (f ⟨·, b⟩) {a | (a
, b) in s}
参数：α × β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
-/
theorem continuousOn_prod_of_discrete_right [DiscreteTopology β] {f : α × β → γ} {s : Set (α × β)} :
    ContinuousOn f s ↔ ∀ b, ContinuousOn (f ⟨·, b⟩) {a | (a, b) ∈ s} := by
  simp_rw [ContinuousOn, Prod.forall, continuousWithinAt_prod_of_discrete_right]; apply forall_comm

/-- If a function `f a b` is such that `y ↦ f a b` is continuous for all `a`, and `a` lives in a
discrete space, then `f` is continuous, and vice versa. -/
/-
**continuous_prod_of_discrete_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_prod_of_discrete_left [DiscreteTopology α] {f : α × β -> γ} : C
ontinuous f ↔ forall a, Continuous (f ⟨a, ·⟩)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `continuousOn_prod_of_discrete_left`：continuousOn_prod_of_discrete_left [
DiscreteTopology α] {f : α × β -> γ} {s : Set (α × β)} : ContinuousOn f s ↔ fora
ll a, ContinuousOn (f ⟨a…

--- 原说明 ---
If a function `f a b` is such that `y ↦ f a b` is continuous for all `a`, and `a
` lives in a
discrete space, then `f` is continuous, and vice versa.
-/
theorem continuous_prod_of_discrete_left [DiscreteTopology α] {f : α × β → γ} :
    Continuous f ↔ ∀ a, Continuous (f ⟨a, ·⟩) := by
  simp_rw [← continuousOn_univ]; exact continuousOn_prod_of_discrete_left
/-
**continuous_prod_of_discrete_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_prod_of_discrete_right [DiscreteTopology β] {f : α × β -> γ} : 
Continuous f ↔ forall b, Continuous (f ⟨·, b⟩)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `continuousOn_prod_of_discrete_right`：continuousOn_prod_of_discrete_right
 [DiscreteTopology β] {f : α × β -> γ} {s : Set (α × β)} : ContinuousOn f s ↔ fo
rall b, ContinuousOn (f ⟨…
-/
theorem continuous_prod_of_discrete_right [DiscreteTopology β] {f : α × β → γ} :
    Continuous f ↔ ∀ b, Continuous (f ⟨·, b⟩) := by
  simp_rw [← continuousOn_univ]; exact continuousOn_prod_of_discrete_right
/-
**isOpenMap_prod_of_discrete_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpenMap_prod_of_discrete_left [DiscreteTopology α] {f : α × β -> γ} : Is
OpenMap f ↔ forall a, IsOpenMap (f ⟨a, ·⟩)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `nhds_discrete`：nhds_discrete (α : Type*) [TopologicalSpace α] [DiscreteT
opology α] : @nhds α _ = pure
· 使用定理 `Filter.pure_prod`：pure_prod {a : α} {f : Filter β} : pure a ×ˢ f = map (
Prod.mk a) f
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isOpenMap_prod_of_discrete_left [DiscreteTopology α] {f : α × β → γ} :
    IsOpenMap f ↔ ∀ a, IsOpenMap (f ⟨a, ·⟩) := by
  simp_rw [isOpenMap_iff_nhds_le, Prod.forall, nhds_prod_eq, nhds_discrete, pure_prod, map_map]
  rfl
/-
**isOpenMap_prod_of_discrete_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpenMap_prod_of_discrete_right [DiscreteTopology β] {f : α × β -> γ} : I
sOpenMap f ↔ forall b, IsOpenMap (f ⟨·, b⟩)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `nhds_discrete`：nhds_discrete (α : Type*) [TopologicalSpace α] [DiscreteT
opology α] : @nhds α _ = pure
· 使用定理 `Filter.prod_pure`：prod_pure {b : β} : f ×ˢ pure b = map (fun a => (a, b)
) f
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isOpenMap_prod_of_discrete_right [DiscreteTopology β] {f : α × β → γ} :
    IsOpenMap f ↔ ∀ b, IsOpenMap (f ⟨·, b⟩) := by
  simp_rw [isOpenMap_iff_nhds_le, Prod.forall, forall_comm (α := α) (β := β), nhds_prod_eq,
    nhds_discrete, prod_pure, map_map]; rfl
/-
**ContinuousOn.uncurry_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.uncurry_left {f : α -> β -> γ} {sα : Set α} {sβ : Set β} (a :
 α) (ha : a in sα) (h : ContinuousOn f.uncurry (sα ×ˢ sβ)) : ContinuousOn (f a) 
sβ
参数：a : α；ha : a in sα；h : ContinuousOn f.uncurry (sα ×ˢ sβ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.congr`：ContinuousOn.congr (h : ContinuousOn f s) (h' : EqOn
 g f s) : ContinuousOn g s
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem ContinuousOn.uncurry_left {f : α → β → γ} {sα : Set α} {sβ : Set β} (a : α) (ha : a ∈ sα)
    (h : ContinuousOn f.uncurry (sα ×ˢ sβ)) : ContinuousOn (f a) sβ := by
  let g : β → γ := f.uncurry ∘ (fun b => (a, b))
  refine ContinuousOn.congr (f := g) ?_ (fun y => by simp [g])
  exact ContinuousOn.comp h (by fun_prop) (by grind [Set.MapsTo])
/-
**ContinuousOn.uncurry_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.uncurry_right {f : α -> β -> γ} {sα : Set α} {sβ : Set β} (b 
: β) (ha : b in sβ) (h : ContinuousOn f.uncurry (sα ×ˢ sβ)) : ContinuousOn (fun 
a => f a b) sα
参数：b : β；ha : b in sβ；h : ContinuousOn f.uncurry (sα ×ˢ sβ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.congr`：ContinuousOn.congr (h : ContinuousOn f s) (h' : EqOn
 g f s) : ContinuousOn g s
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem ContinuousOn.uncurry_right {f : α → β → γ} {sα : Set α} {sβ : Set β} (b : β) (ha : b ∈ sβ)
    (h : ContinuousOn f.uncurry (sα ×ˢ sβ)) : ContinuousOn (fun a => f a b) sα := by
  let g : α → γ := f.uncurry ∘ (fun a => (a, b))
  refine ContinuousOn.congr (f := g) ?_ (fun y => by simp [g])
  exact ContinuousOn.comp h (by fun_prop) (by grind [Set.MapsTo])

/-!
## Pi
-/

/-
**continuousWithinAt_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_pi {ι : Type*} {X : ι -> Type*} [forall i, TopologicalS
pace (X i)] {f : α -> forall i, X i} {s : Set α} {x : α} : ContinuousWithinAt f 
s x ↔ forall i, ContinuousWithinAt (fun y => f y i) s x
参数：X i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_pi_nhds`：tendsto_pi_nhds {f : Y -> forall i, A i} {g : forall i,
 A i} {u : Filter Y} : Tendsto f u (𝓝 g) ↔ forall x, Tendsto (fun i => f i x) u 
(𝓝 (g…

--- 原说明 ---
## Pi
-/
theorem continuousWithinAt_pi {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    {f : α → ∀ i, X i} {s : Set α} {x : α} :
    ContinuousWithinAt f s x ↔ ∀ i, ContinuousWithinAt (fun y => f y i) s x :=
  tendsto_pi_nhds
/-
**continuousOn_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_pi {ι : Type*} {X : ι -> Type*} [forall i, TopologicalSpace (
X i)] {f : α -> forall i, X i} {s : Set α} : ContinuousOn f s ↔ forall i, Contin
uousOn (fun y => f y i) s
参数：X i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tendsto_pi_nhds`：tendsto_pi_nhds {f : Y -> forall i, A i} {g : forall i,
 A i} {u : Filter Y} : Tendsto f u (𝓝 g) ↔ forall x, Tendsto (fun i => f i x) u 
(𝓝 (g…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem continuousOn_pi {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    {f : α → ∀ i, X i} {s : Set α} : ContinuousOn f s ↔ ∀ i, ContinuousOn (fun y => f y i) s :=
  ⟨fun h i x hx => tendsto_pi_nhds.1 (h x hx) i, fun h x hx => tendsto_pi_nhds.2 fun i => h i x hx⟩

@[fun_prop]
/-
**continuousOn_pi'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_pi' {ι : Type*} {X : ι -> Type*} [forall i, TopologicalSpace 
(X i)] {f : α -> forall i, X i} {s : Set α} (hf : forall i, ContinuousOn (fun y 
=> f y i) s) : ContinuousOn f s
参数：X i；hf : forall i, ContinuousOn (fun y => f y i) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuousOn_pi`：continuousOn_pi {ι : Type*} {X : ι -> Type*} [forall i,
 TopologicalSpace (X i)] {f : α -> forall i, X i} {s : Set α} : ContinuousOn f s
 ↔ fo…
-/
theorem continuousOn_pi' {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    {f : α → ∀ i, X i} {s : Set α} (hf : ∀ i, ContinuousOn (fun y => f y i) s) :
    ContinuousOn f s :=
  continuousOn_pi.2 hf

@[fun_prop]
/-
**continuousOn_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_apply {ι : Type*} {X : ι -> Type*} [forall i, TopologicalSpac
e (X i)] (i : ι) (s) : ContinuousOn (fun p : forall i, X i => p i) s
参数：X i；i : ι；s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
-/
theorem continuousOn_apply {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    (i : ι) (s) : ContinuousOn (fun p : ∀ i, X i => p i) s :=
  Continuous.continuousOn (continuous_apply i)


/-!
## Specific functions
-/

@[fun_prop]
/-
**continuousOn_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_const {s : Set α} {c : β} : ContinuousOn (fun _ => c) s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)

--- 原说明 ---
## Specific functions
-/
theorem continuousOn_const {s : Set α} {c : β} : ContinuousOn (fun _ => c) s :=
  continuous_const.continuousOn

@[fun_prop]
/-
**continuousWithinAt_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_const {b : β} {s : Set α} {x : α} : ContinuousWithinAt 
(fun _ : α => b) s x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousWithinAt`：Continuous.continuousWithinAt (h : Contin
uous f) : ContinuousWithinAt f s x
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
-/
theorem continuousWithinAt_const {b : β} {s : Set α} {x : α} :
    ContinuousWithinAt (fun _ : α => b) s x :=
  continuous_const.continuousWithinAt
/-
**continuousOn_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_id {s : Set α} : ContinuousOn id s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem continuousOn_id {s : Set α} : ContinuousOn id s :=
  continuous_id.continuousOn

@[fun_prop]
/-
**continuousOn_id'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α => x) s
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousOn_id`：continuousOn_id {s : Set α} : ContinuousOn id s
-/
theorem continuousOn_id' (s : Set α) : ContinuousOn (fun x : α => x) s := continuousOn_id
/-
**continuousWithinAt_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_id {s : Set α} {x : α} : ContinuousWithinAt id s x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousWithinAt`：Continuous.continuousWithinAt (h : Contin
uous f) : ContinuousWithinAt f s x
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem continuousWithinAt_id {s : Set α} {x : α} : ContinuousWithinAt id s x :=
  continuous_id.continuousWithinAt
/-
**ContinuousOn.iterate** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOn`。
形式化陈述：∀ {α : Type u_1} [inst : TopologicalSpace α] {f : α → α} {s : Set α},   Co
ntinuousOn f s → Set.MapsTo f s s → ∀ (n : ℕ), ContinuousOn f^[n] s
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem ContinuousOn.iterate {f : α → α} {s : Set α} (hcont : ContinuousOn f s)
    (hmaps : MapsTo f s s) : ∀ n, ContinuousOn (f^[n]) s
  | 0 => continuousOn_id
  | (n + 1) => (hcont.iterate hmaps n).comp hcont hmaps

section Fin
variable {n : ℕ} {X : Fin (n + 1) → Type*} [∀ i, TopologicalSpace (X i)]

/-
**ContinuousWithinAt.finCons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.finCons {f : α -> X 0} {g : α -> forall j : Fin n, X (F
in.succ j)} {a : α} {s : Set α} (hf : ContinuousWithinAt f s a) (hg : Continuous
WithinAt g s a) : ContinuousWithinAt (fun a => Fin.cons (f a) (g a)) s a
参数：Fin.succ j；hf : ContinuousWithinAt f s a；hg : ContinuousWithinAt g s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Filter.Tendsto.finCons`：Filter.Tendsto.finCons {f : Y -> A 0} {g : Y -> 
forall j : Fin n, A j.succ} {l : Filter Y} {x : A 0} {y : forall j, A (Fin.succ 
j)} (hf : Te…
· 使用定理 `ContinuousWithinAt.tendsto`：ContinuousWithinAt.tendsto (h : ContinuousWi
thinAt f s x) : Tendsto f (𝓝[s] x) (𝓝 (f x))
-/
theorem ContinuousWithinAt.finCons
    {f : α → X 0} {g : α → ∀ j : Fin n, X (Fin.succ j)} {a : α} {s : Set α}
    (hf : ContinuousWithinAt f s a) (hg : ContinuousWithinAt g s a) :
    ContinuousWithinAt (fun a => Fin.cons (f a) (g a)) s a :=
  hf.tendsto.finCons hg
/-
**ContinuousOn.finCons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.finCons {f : α -> X 0} {s : Set α} {g : α -> forall j : Fin n
, X (Fin.succ j)} (hf : ContinuousOn f s) (hg : ContinuousOn g s) : ContinuousOn
 (fun a => Fin.cons (f a) (g a)) s
参数：Fin.succ j；hf : ContinuousOn f s；hg : ContinuousOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ContinuousWithinAt.finCons`：ContinuousWithinAt.finCons {f : α -> X 0} {g
 : α -> forall j : Fin n, X (Fin.succ j)} {a : α} {s : Set α} (hf : ContinuousWi
thinAt f s a) (h…
-/
theorem ContinuousOn.finCons {f : α → X 0} {s : Set α} {g : α → ∀ j : Fin n, X (Fin.succ j)}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun a => Fin.cons (f a) (g a)) s := fun a ha =>
  (hf a ha).finCons (hg a ha)
/-
**ContinuousWithinAt.matrixVecCons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.matrixVecCons {f : α -> β} {g : α -> Fin n -> β} {a : α
} {s : Set α} (hf : ContinuousWithinAt f s a) (hg : ContinuousWithinAt g s a) : 
ContinuousWithinAt (fun a => Matrix.vecCons (f a) (g a)) s a
参数：hf : ContinuousWithinAt f s a；hg : ContinuousWithinAt g s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.matrixVecCons`：Filter.Tendsto.matrixVecCons {f : Y -> Z} 
{g : Y -> Fin n -> Z} {l : Filter Y} {x : Z} {y : Fin n -> Z} (hf : Tendsto f l 
(𝓝 x)) (hg : Tends…
· 使用定理 `ContinuousWithinAt.tendsto`：ContinuousWithinAt.tendsto (h : ContinuousWi
thinAt f s x) : Tendsto f (𝓝[s] x) (𝓝 (f x))
-/
theorem ContinuousWithinAt.matrixVecCons {f : α → β} {g : α → Fin n → β} {a : α} {s : Set α}
    (hf : ContinuousWithinAt f s a) (hg : ContinuousWithinAt g s a) :
    ContinuousWithinAt (fun a => Matrix.vecCons (f a) (g a)) s a :=
  hf.tendsto.matrixVecCons hg
/-
**ContinuousOn.matrixVecCons** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.matrixVecCons {f : α -> β} {g : α -> Fin n -> β} {s : Set α} 
(hf : ContinuousOn f s) (hg : ContinuousOn g s) : ContinuousOn (fun a => Matrix.
vecCons (f a) (g a)) s
参数：hf : ContinuousOn f s；hg : ContinuousOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.matrixVecCons`：ContinuousWithinAt.matrixVecCons {f : 
α -> β} {g : α -> Fin n -> β} {a : α} {s : Set α} (hf : ContinuousWithinAt f s a
) (hg : ContinuousWith…
-/
theorem ContinuousOn.matrixVecCons {f : α → β} {g : α → Fin n → β} {s : Set α}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun a => Matrix.vecCons (f a) (g a)) s := fun a ha =>
  (hf a ha).matrixVecCons (hg a ha)
/-
**ContinuousWithinAt.finSnoc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.finSnoc {f : α -> forall j : Fin n, X (Fin.castSucc j)}
 {g : α -> X (Fin.last _)} {a : α} {s : Set α} (hf : ContinuousWithinAt f s a) (
hg : ContinuousWithinAt g s a) : ContinuousWithinAt (fun a => Fin.snoc (f a) (g 
a)) s a
参数：Fin.castSucc j；Fin.last _；hf : ContinuousWithinAt f s a；hg : ContinuousWithin
At g s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.finSnoc`：Filter.Tendsto.finSnoc {f : Y -> forall j : Fin 
n, A j.castSucc} {g : Y -> A (Fin.last _)} {l : Filter Y} {x : forall j, A (Fin.
castSucc j)}…
· 使用定理 `ContinuousWithinAt.tendsto`：ContinuousWithinAt.tendsto (h : ContinuousWi
thinAt f s x) : Tendsto f (𝓝[s] x) (𝓝 (f x))
-/
theorem ContinuousWithinAt.finSnoc
    {f : α → ∀ j : Fin n, X (Fin.castSucc j)} {g : α → X (Fin.last _)} {a : α} {s : Set α}
    (hf : ContinuousWithinAt f s a) (hg : ContinuousWithinAt g s a) :
    ContinuousWithinAt (fun a => Fin.snoc (f a) (g a)) s a :=
  hf.tendsto.finSnoc hg
/-
**ContinuousOn.finSnoc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.finSnoc {f : α -> forall j : Fin n, X (Fin.castSucc j)} {g : 
α -> X (Fin.last _)} {s : Set α} (hf : ContinuousOn f s) (hg : ContinuousOn g s)
 : ContinuousOn (fun a => Fin.snoc (f a) (g a)) s
参数：Fin.castSucc j；Fin.last _；hf : ContinuousOn f s；hg : ContinuousOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.finSnoc`：ContinuousWithinAt.finSnoc {f : α -> forall 
j : Fin n, X (Fin.castSucc j)} {g : α -> X (Fin.last _)} {a : α} {s : Set α} (hf
 : ContinuousWit…
-/
theorem ContinuousOn.finSnoc
    {f : α → ∀ j : Fin n, X (Fin.castSucc j)} {g : α → X (Fin.last _)} {s : Set α}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun a => Fin.snoc (f a) (g a)) s := fun a ha =>
  (hf a ha).finSnoc (hg a ha)
/-
**ContinuousWithinAt.finInsertNth** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.finInsertNth (i : Fin (n + 1)) {f : α -> X i} {g : α ->
 forall j : Fin n, X (i.succAbove j)} {a : α} {s : Set α} (hf : ContinuousWithin
At f s a) (hg : ContinuousWithinAt g s a) : ContinuousWithinAt (fun a => i.inser
tNth (f a) (g a)) s a
参数：i : Fin (n + 1)；i.succAbove j；hf : ContinuousWithinAt f s a；hg : ContinuousWi
thinAt g s a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.finInsertNth`：Filter.Tendsto.finInsertNth (i : Fin (n + 1
)) {f : Y -> A i} {g : Y -> forall j : Fin n, A (i.succAbove j)} {l : Filter Y} 
{x : A i} {y : fo…
· 使用定理 `ContinuousWithinAt.tendsto`：ContinuousWithinAt.tendsto (h : ContinuousWi
thinAt f s x) : Tendsto f (𝓝[s] x) (𝓝 (f x))
-/
theorem ContinuousWithinAt.finInsertNth
    (i : Fin (n + 1)) {f : α → X i} {g : α → ∀ j : Fin n, X (i.succAbove j)} {a : α} {s : Set α}
    (hf : ContinuousWithinAt f s a) (hg : ContinuousWithinAt g s a) :
    ContinuousWithinAt (fun a => i.insertNth (f a) (g a)) s a :=
  hf.tendsto.finInsertNth i hg
/-
**ContinuousOn.finInsertNth** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.finInsertNth (i : Fin (n + 1)) {f : α -> X i} {g : α -> foral
l j : Fin n, X (i.succAbove j)} {s : Set α} (hf : ContinuousOn f s) (hg : Contin
uousOn g s) : ContinuousOn (fun a => i.insertNth (f a) (g a)) s
参数：i : Fin (n + 1)；i.succAbove j；hf : ContinuousOn f s；hg : ContinuousOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.finInsertNth`：ContinuousWithinAt.finInsertNth (i : Fi
n (n + 1)) {f : α -> X i} {g : α -> forall j : Fin n, X (i.succAbove j)} {a : α}
 {s : Set α} (hf : Co…
-/
theorem ContinuousOn.finInsertNth
    (i : Fin (n + 1)) {f : α → X i} {g : α → ∀ j : Fin n, X (i.succAbove j)} {s : Set α}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun a => i.insertNth (f a) (g a)) s := fun a ha =>
  (hf a ha).finInsertNth i (hg a ha)

end Fin

/-
**Set.LeftInvOn.map_nhdsWithin_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.LeftInvOn.map_nhdsWithin_eq {f : α -> β} {g : β -> α} {x : β} {s : Set
 β} (h : LeftInvOn f g s) (hx : f (g x) = x) (hf : ContinuousWithinAt f (g '' s)
 (g x)) (hg : ContinuousWithinAt g s x) : map g (𝓝[s] x) = 𝓝[g '' s] g x
参数：h : LeftInvOn f g s；hx : f (g x) = x；hf : ContinuousWithinAt f (g '' s) (g x)
；hg : ContinuousWithinAt g s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `ContinuousWithinAt.tendsto_nhdsWithin`：ContinuousWithinAt.tendsto_nhdsWi
thin {t : Set β} (h : ContinuousWithinAt f s x) (ht : MapsTo f s t) : Tendsto f 
(𝓝[s] x) (𝓝[t] f x)
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
· 使用定理 `Set.EqOn.eventuallyEq_of_mem`：Set.EqOn.eventuallyEq_of_mem {α β} {s : Se
t α} {l : Filter α} {f g : α -> β} (h : EqOn f g s) (hl : s in l) : f =ᶠ[l] g
· 使用定理 `Set.RightInvOn.eqOn`：eqOn (h : RightInvOn f' f t) : EqOn (f ∘ f') id t
· 使用定理 `Set.LeftInvOn.rightInvOn_image`：∀ {α : Type u_1} {β : Type u_2} {s : Set
 α} {f : α → β} {f' : β → α},   Set.LeftInvOn f' f s → Set.RightInvOn f' f (f ''
 s)
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.le_map_of_right_inverse`：le_map_of_right_inverse {mab : α -> β} {
mba : β -> α} {f : Filter α} {g : Filter β} (h₁ : mab ∘ mba =ᶠ[g] id) (h₂ : Tend
sto mba g f) : g <= …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.LeftInvOn.mapsTo`：mapsTo (h : LeftInvOn f' f s) (hf : SurjOn f s t) 
: MapsTo f' t s
· 使用定理 `Set.surjOn_image`：surjOn_image (f : α -> β) (s : Set α) : SurjOn f s (f 
'' s)
-/
theorem Set.LeftInvOn.map_nhdsWithin_eq {f : α → β} {g : β → α} {x : β} {s : Set β}
    (h : LeftInvOn f g s) (hx : f (g x) = x) (hf : ContinuousWithinAt f (g '' s) (g x))
    (hg : ContinuousWithinAt g s x) : map g (𝓝[s] x) = 𝓝[g '' s] g x := by
  apply le_antisymm
  · exact hg.tendsto_nhdsWithin (mapsTo_image _ _)
  · have A : g ∘ f =ᶠ[𝓝[g '' s] g x] id :=
      h.rightInvOn_image.eqOn.eventuallyEq_of_mem self_mem_nhdsWithin
    refine le_map_of_right_inverse A ?_
    simpa only [hx] using hf.tendsto_nhdsWithin (h.mapsTo (surjOn_image _ _))
/-
**Function.LeftInverse.map_nhds_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.LeftInverse.map_nhds_eq {f : α -> β} {g : β -> α} {x : β} (h : Fu
nction.LeftInverse f g) (hf : ContinuousWithinAt f (range g) (g x)) (hg : Contin
uousAt g x) : map g (𝓝 x) = 𝓝[range g] g x
参数：h : Function.LeftInverse f g；hf : ContinuousWithinAt f (range g) (g x)；hg : C
ontinuousAt g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Set.LeftInvOn.map_nhdsWithin_eq`：Set.LeftInvOn.map_nhdsWithin_eq {f : α 
-> β} {g : β -> α} {x : β} {s : Set β} (h : LeftInvOn f g s) (hx : f (g x) = x) 
(hf : ContinuousWithi…
· 使用定理 `Function.LeftInverse.leftInvOn`：∀ {α : Type u_1} {β : Type u_2} {f : α →
 β} {g : β → α}, Function.LeftInverse f g → ∀ (s : Set β), Set.LeftInvOn f g s
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
-/
theorem Function.LeftInverse.map_nhds_eq {f : α → β} {g : β → α} {x : β}
    (h : Function.LeftInverse f g) (hf : ContinuousWithinAt f (range g) (g x))
    (hg : ContinuousAt g x) : map g (𝓝 x) = 𝓝[range g] g x := by
  simpa only [nhdsWithin_univ, image_univ] using
    (h.leftInvOn univ).map_nhdsWithin_eq (h x) (by rwa [image_univ]) hg.continuousWithinAt
/-
**Topology.IsInducing.continuousWithinAt_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.continuousWithinAt_iff {f : α -> β} {g : β -> γ} (hg :
 IsInducing g) {s : Set α} {x : α} : ContinuousWithinAt f s x ↔ ContinuousWithin
At (g ∘ f) s x
参数：hg : IsInducing g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.IsInducing.tendsto_nhds_iff`：tendsto_nhds_iff {f : ι -> Y} {l :
 Filter ι} {y : Y} (hg : IsInducing g) : Tendsto f l (𝓝 y) ↔ Tendsto (g ∘ f) l (
𝓝 (g y))
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Topology.IsInducing.continuousWithinAt_iff {f : α → β} {g : β → γ} (hg : IsInducing g)
    {s : Set α} {x : α} : ContinuousWithinAt f s x ↔ ContinuousWithinAt (g ∘ f) s x := by
  simp_rw [ContinuousWithinAt, hg.tendsto_nhds_iff]; rfl
/-
**Topology.IsInducing.continuousOn_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.continuousOn_iff {f : α -> β} {g : β -> γ} (hg : IsInd
ucing g) {s : Set α} : ContinuousOn f s ↔ ContinuousOn (g ∘ f) s
参数：hg : IsInducing g。
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
· 使用引理 `Topology.IsInducing.continuousWithinAt_iff`：Topology.IsInducing.continuo
usWithinAt_iff {f : α -> β} {g : β -> γ} (hg : IsInducing g) {s : Set α} {x : α}
 : ContinuousWithinAt f s x ↔ Co…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Topology.IsInducing.continuousOn_iff {f : α → β} {g : β → γ} (hg : IsInducing g)
    {s : Set α} : ContinuousOn f s ↔ ContinuousOn (g ∘ f) s := by
  simp_rw [ContinuousOn, hg.continuousWithinAt_iff]
/-
**Topology.IsInducing.map_nhdsWithin_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.map_nhdsWithin_eq {f : α -> β} (hf : IsInducing f) (s 
: Set α) (x : α) : map f (𝓝[s] x) = 𝓝[f '' s] f x
参数：hf : IsInducing f；s : Set α；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用引理 `Topology.IsInducing.nhds_eq_comap`：nhds_eq_comap (hf : IsInducing f) : f
orall x : X, 𝓝 x = comap f (𝓝 <| f x)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Topology.IsInducing.map_nhdsWithin_eq {f : α → β} (hf : IsInducing f) (s : Set α) (x : α) :
    map f (𝓝[s] x) = 𝓝[f '' s] f x := by
  ext; simp +contextual [mem_nhdsWithin_iff_eventually, hf.nhds_eq_comap, forall_comm (α := _ ∈ _)]
/-
**Topology.IsInducing.continuousOn_image_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.continuousOn_image_iff {g : β -> γ} {s : Set α} (hf : 
IsInducing f) : ContinuousOn g (f '' s) ↔ ContinuousOn (g ∘ f) s
参数：hf : IsInducing f。
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Topology.IsInducing.map_nhdsWithin_eq`：Topology.IsInducing.map_nhdsWithi
n_eq {f : α -> β} (hf : IsInducing f) (s : Set α) (x : α) : map f (𝓝[s] x) = 𝓝[f
 '' s] f x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Topology.IsInducing.continuousOn_image_iff {g : β → γ} {s : Set α} (hf : IsInducing f) :
    ContinuousOn g (f '' s) ↔ ContinuousOn (g ∘ f) s := by
  simp [ContinuousOn, ContinuousWithinAt, ← hf.map_nhdsWithin_eq]
/-
**Topology.IsEmbedding.continuousOn_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsEmbedding.continuousOn_iff {f : α -> β} {g : β -> γ} (hg : IsEm
bedding g) {s : Set α} : ContinuousOn f s ↔ ContinuousOn (g ∘ f) s
参数：hg : IsEmbedding g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsInducing.continuousOn_iff`：Topology.IsInducing.continuousOn_i
ff {f : α -> β} {g : β -> γ} (hg : IsInducing g) {s : Set α} : ContinuousOn f s 
↔ ContinuousOn (g ∘ f) s
· 使用定理 `Topology.IsEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Topology.I…
-/
lemma Topology.IsEmbedding.continuousOn_iff {f : α → β} {g : β → γ} (hg : IsEmbedding g)
    {s : Set α} : ContinuousOn f s ↔ ContinuousOn (g ∘ f) s :=
  hg.isInducing.continuousOn_iff
/-
**Topology.IsEmbedding.map_nhdsWithin_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsEmbedding.map_nhdsWithin_eq {f : α -> β} (hf : IsEmbedding f) (
s : Set α) (x : α) : map f (𝓝[s] x) = 𝓝[f '' s] f x
参数：hf : IsEmbedding f；s : Set α；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsInducing.map_nhdsWithin_eq`：Topology.IsInducing.map_nhdsWithi
n_eq {f : α -> β} (hf : IsInducing f) (s : Set α) (x : α) : map f (𝓝[s] x) = 𝓝[f
 '' s] f x
· 使用定理 `Topology.IsEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Topology.I…
-/
lemma Topology.IsEmbedding.map_nhdsWithin_eq {f : α → β} (hf : IsEmbedding f) (s : Set α) (x : α) :
    map f (𝓝[s] x) = 𝓝[f '' s] f x :=
  hf.isInducing.map_nhdsWithin_eq s x
/-
**Topology.IsOpenEmbedding.map_nhdsWithin_preimage_eq** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：Topology.IsOpenEmbedding.map_nhdsWithin_preimage_eq {f : α -> β} (hf : IsO
penEmbedding f) (s : Set β) (x : α) : map f (𝓝[f ⁻¹' s] x) = 𝓝[s] f x
参数：hf : IsOpenEmbedding f；s : Set β；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.IsEmbedding.map_nhdsWithin_eq`：Topology.IsEmbedding.map_nhdsWit
hin_eq {f : α -> β} (hf : IsEmbedding f) (s : Set α) (x : α) : map f (𝓝[s] x) = 
𝓝[f '' s] f x
· 使用定理 `Topology.IsOpenEmbedding.isEmbedding`：∀ {X : Type u_1} {Y : Type u_2} {f
 : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.
IsOpenEmbedding f → Topolo…
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `nhdsWithin_eq_nhdsWithin`：nhdsWithin_eq_nhdsWithin {a : α} {s t u : Set 
α} (h₀ : a in s) (h₁ : IsOpen s) (h₂ : t inter s = u inter s) : 𝓝[t] a = 𝓝[u] a
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Topology.IsOpenEmbedding.isOpen_range`：∀ {X : Type u_1} {Y : Type u_2} [
tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOpe
nEmbedding f → IsOpen (Set.…
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
-/
theorem Topology.IsOpenEmbedding.map_nhdsWithin_preimage_eq {f : α → β} (hf : IsOpenEmbedding f)
    (s : Set β) (x : α) : map f (𝓝[f ⁻¹' s] x) = 𝓝[s] f x := by
  rw [hf.isEmbedding.map_nhdsWithin_eq, image_preimage_eq_inter_range]
  apply nhdsWithin_eq_nhdsWithin (mem_range_self _) hf.isOpen_range
  rw [inter_assoc, inter_self]
/-
**Topology.IsQuotientMap.continuousOn_isOpen_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsQuotientMap.continuousOn_isOpen_iff {f : α -> β} {g : β -> γ} (
h : IsQuotientMap f) {s : Set β} (hs : IsOpen s) : ContinuousOn g s ↔ Continuous
On (g ∘ f) (f ⁻¹' s)
参数：h : IsQuotientMap f；hs : IsOpen s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Topology.IsQuotientMap.continuous_iff`：∀ {X : Type u_1} {Y : Type u_2} {
Z : Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : To
pologicalSpace Y] [inst_2 :…
· 使用定理 `Topology.IsQuotientMap.restrictPreimage_isOpen`：Topology.IsQuotientMap.r
estrictPreimage_isOpen {f : X -> Y} (hf : IsQuotientMap f) {s : Set Y} (hs : IsO
pen s) : IsQuotientMap (s.restrictPr…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Topology.IsQuotientMap.continuousOn_isOpen_iff {f : α → β} {g : β → γ} (h : IsQuotientMap f)
    {s : Set β} (hs : IsOpen s) : ContinuousOn g s ↔ ContinuousOn (g ∘ f) (f ⁻¹' s) := by
  simp only [continuousOn_iff_continuous_domRestrict, (h.restrictPreimage_isOpen hs).continuous_iff]
  rfl
/-
**IsOpenMap.continuousOn_image_of_leftInvOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpenMap.continuousOn_image_of_leftInvOn {f : α -> β} {s : Set α} (h : Is
OpenMap (s.domRestrict f)) {finv : β -> α} (hleft : LeftInvOn finv f s) : Contin
uousOn finv (f '' s)
参数：h : IsOpenMap (s.domRestrict f)；hleft : LeftInvOn finv f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuousOn_iff'`：continuousOn_iff' : ContinuousOn f s ↔ forall t : Set
 β, IsOpen t -> exists u, IsOpen u ∧ f ⁻¹' t inter s = u inter s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_domRestrict`：image_domRestrict (f : α -> β) (s t : Set α) : s.
domRestrict f '' Subtype.val ⁻¹' t = f '' (t inter s)
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `Set.inter_eq_self_of_subset_left`：inter_eq_self_of_subset_left {s t : Se
t α} : s subseteq t -> s inter t = s
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Set.LeftInvOn.image_inter'`：image_inter' (hf : LeftInvOn f' f s) : f '' 
(s₁ inter s) = f' ⁻¹' s₁ inter f '' s
-/
theorem IsOpenMap.continuousOn_image_of_leftInvOn {f : α → β} {s : Set α}
    (h : IsOpenMap (s.domRestrict f)) {finv : β → α} (hleft : LeftInvOn finv f s) :
    ContinuousOn finv (f '' s) := by
  refine continuousOn_iff'.2 fun t ht => ⟨f '' (t ∩ s), ?_, ?_⟩
  · rw [← image_domRestrict]
    exact h _ (ht.preimage continuous_subtype_val)
  · rw [inter_eq_self_of_subset_left (image_mono inter_subset_right), hleft.image_inter']
/-
**IsOpenMap.continuousOn_range_of_leftInverse** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpenMap.continuousOn_range_of_leftInverse {f : α -> β} (hf : IsOpenMap f
) {finv : β -> α} (hleft : Function.LeftInverse finv f) : ContinuousOn finv (ran
ge f)
参数：hf : IsOpenMap f；hleft : Function.LeftInverse finv f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `IsOpenMap.continuousOn_image_of_leftInvOn`：IsOpenMap.continuousOn_image_
of_leftInvOn {f : α -> β} {s : Set α} (h : IsOpenMap (s.domRestrict f)) {finv : 
β -> α} (hleft : LeftInvOn finv…
· 使用定理 `IsOpenMap.domRestrict`：IsOpenMap.domRestrict {f : X -> Y} (hf : IsOpenMa
p f) {s : Set X} (hs : IsOpen s) : IsOpenMap (s.domRestrict f)
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
-/
theorem IsOpenMap.continuousOn_range_of_leftInverse {f : α → β} (hf : IsOpenMap f) {finv : β → α}
    (hleft : Function.LeftInverse finv f) : ContinuousOn finv (range f) := by
  rw [← image_univ]
  exact (hf.domRestrict isOpen_univ).continuousOn_image_of_leftInvOn fun x _ => hleft x

/-- If `f` is continuous on an open set `s` and continuous at each point of another
set `t` then `f` is continuous on `s ∪ t`. -/
/-
**ContinuousOn.union_continuousAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousOn.union_continuousAt {f : α -> β} (s_op : IsOpen s) (hs : Conti
nuousOn f s) (ht : forall x in t, ContinuousAt f x) : ContinuousOn f (s union t)
参数：s_op : IsOpen s；hs : ContinuousOn f s；ht : forall x in t, ContinuousAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousOn_of_forall_continuousAt`：continuousOn_of_forall_continuousAt
 (hcont : forall x in s, ContinuousAt f x) : ContinuousOn f s
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `ContinuousWithinAt.continuousAt`：ContinuousWithinAt.continuousAt (h : Co
ntinuousWithinAt f s x) (hs : s in 𝓝 x) : ContinuousAt f x
· 使用定理 `ContinuousOn.continuousWithinAt`：ContinuousOn.continuousWithinAt (hf : C
ontinuousOn f s) (hx : x in s) : ContinuousWithinAt f s x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x

--- 原说明 ---
If `f` is continuous on an open set `s` and continuous at each point of another
set `t` then `f` is continuous on `s ∪ t`.
-/
lemma ContinuousOn.union_continuousAt {f : α → β} (s_op : IsOpen s)
    (hs : ContinuousOn f s) (ht : ∀ x ∈ t, ContinuousAt f x) :
    ContinuousOn f (s ∪ t) :=
  continuousOn_of_forall_continuousAt <| fun _ hx => hx.elim
  (fun h => ContinuousWithinAt.continuousAt (continuousWithinAt hs h) <| IsOpen.mem_nhds s_op h)
  (ht _)

/-- If a function is continuous on two closed sets, it is also continuous on their union. -/
/-
**ContinuousOn.union_of_isClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.union_of_isClosed {f : α -> β} (hfs : ContinuousOn f s) (hft 
: ContinuousOn f t) (hs : IsClosed s) (ht : IsClosed t) : ContinuousOn f (s unio
n t)
参数：hfs : ContinuousOn f s；hft : ContinuousOn f t；hs : IsClosed s；ht : IsClosed t
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.union`：ContinuousWithinAt.union (hs : ContinuousWithi
nAt f s x) (ht : ContinuousWithinAt f t x) : ContinuousWithinAt f (s union t) x
· 使用定理 `continuousWithinAt_of_notMem_closure`：continuousWithinAt_of_notMem_closu
re (hx : x ∉ closure s) : ContinuousWithinAt f s x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x

--- 原说明 ---
If a function is continuous on two closed sets, it is also continuous on their u
nion.
-/
theorem ContinuousOn.union_of_isClosed {f : α → β} (hfs : ContinuousOn f s) (hft : ContinuousOn f t)
    (hs : IsClosed s) (ht : IsClosed t) : ContinuousOn f (s ∪ t) := by
  classical
  refine fun x hx ↦ .union ?_ ?_
  · refine if hx : x ∈ s then hfs x hx else continuousWithinAt_of_notMem_closure ?_
    rwa [hs.closure_eq]
  · refine if hx : x ∈ t then hft x hx else continuousWithinAt_of_notMem_closure ?_
    rwa [ht.closure_eq]

/-- A function is continuous on two closed sets iff it is also continuous on their union. -/
/-
**continuousOn_union_iff_of_isClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_union_iff_of_isClosed {f : α -> β} (hs : IsClosed s) (ht : Is
Closed t) : ContinuousOn f (s union t) ↔ ContinuousOn f s ∧ ContinuousOn f t
参数：hs : IsClosed s；ht : IsClosed t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `ContinuousOn.union_of_isClosed`：ContinuousOn.union_of_isClosed {f : α ->
 β} (hfs : ContinuousOn f s) (hft : ContinuousOn f t) (hs : IsClosed s) (ht : Is
Closed t) : Continuo…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
A function is continuous on two closed sets iff it is also continuous on their u
nion.
-/
theorem continuousOn_union_iff_of_isClosed {f : α → β} (hs : IsClosed s) (ht : IsClosed t) :
    ContinuousOn f (s ∪ t) ↔ ContinuousOn f s ∧ ContinuousOn f t :=
  ⟨fun h ↦ ⟨h.mono s.subset_union_left, h.mono s.subset_union_right⟩,
   fun h ↦ h.left.union_of_isClosed h.right hs ht⟩

@[deprecated (since := "2026-02-20")]
alias continouousOn_union_iff_of_isClosed := continuousOn_union_iff_of_isClosed

/-- If a function is continuous on two open sets, it is also continuous on their union. -/
/-
**ContinuousOn.union_of_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.union_of_isOpen {f : α -> β} (hfs : ContinuousOn f s) (hft : 
ContinuousOn f t) (hs : IsOpen s) (ht : IsOpen t) : ContinuousOn f (s union t)
参数：hfs : ContinuousOn f s；hft : ContinuousOn f t；hs : IsOpen s；ht : IsOpen t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousOn.union_continuousAt`：ContinuousOn.union_continuousAt {f : α 
-> β} (s_op : IsOpen s) (hs : ContinuousOn f s) (ht : forall x in t, ContinuousA
t f x) : ContinuousOn…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsOpen.continuousOn_iff`：IsOpen.continuousOn_iff (hs : IsOpen s) : Conti
nuousOn f s ↔ forall ⦃a⦄, a in s -> ContinuousAt f a

--- 原说明 ---
If a function is continuous on two open sets, it is also continuous on their uni
on.
-/
theorem ContinuousOn.union_of_isOpen {f : α → β} (hfs : ContinuousOn f s) (hft : ContinuousOn f t)
    (hs : IsOpen s) (ht : IsOpen t) : ContinuousOn f (s ∪ t) :=
  union_continuousAt hs hfs fun _ hx ↦ ht.continuousOn_iff.mp hft hx

/-- A function is continuous on two open sets iff it is also continuous on their union. -/
/-
**continuousOn_union_iff_of_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_union_iff_of_isOpen {f : α -> β} (hs : IsOpen s) (ht : IsOpen
 t) : ContinuousOn f (s union t) ↔ ContinuousOn f s ∧ ContinuousOn f t
参数：hs : IsOpen s；ht : IsOpen t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `ContinuousOn.union_of_isOpen`：ContinuousOn.union_of_isOpen {f : α -> β} 
(hfs : ContinuousOn f s) (hft : ContinuousOn f t) (hs : IsOpen s) (ht : IsOpen t
) : ContinuousOn f…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
A function is continuous on two open sets iff it is also continuous on their uni
on.
-/
theorem continuousOn_union_iff_of_isOpen {f : α → β} (hs : IsOpen s) (ht : IsOpen t) :
    ContinuousOn f (s ∪ t) ↔ ContinuousOn f s ∧ ContinuousOn f t :=
  ⟨fun h ↦ ⟨h.mono s.subset_union_left, h.mono s.subset_union_right⟩,
   fun h ↦ h.left.union_of_isOpen h.right hs ht⟩

@[deprecated (since := "2026-02-20")]
alias continouousOn_union_iff_of_isOpen := continuousOn_union_iff_of_isOpen

/-- If a function is continuous on open sets `s i`, it is continuous on their union -/
/-
**ContinuousOn.iUnion_of_isOpen** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousOn.iUnion_of_isOpen {ι : Type*} {s : ι -> Set α} (hf : forall i 
: ι, ContinuousOn f (s i)) (hs : forall i, IsOpen (s i)) : ContinuousOn f (⋃ i, 
s i)
参数：hf : forall i : ι, ContinuousOn f (s i)；hs : forall i, IsOpen (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `ContinuousOn.continuousAt`：ContinuousOn.continuousAt (h : ContinuousOn f
 s) (hx : s in 𝓝 x) : ContinuousAt f x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x

--- 原说明 ---
If a function is continuous on open sets `s i`, it is continuous on their union
-/
lemma ContinuousOn.iUnion_of_isOpen {ι : Type*} {s : ι → Set α}
    (hf : ∀ i : ι, ContinuousOn f (s i)) (hs : ∀ i, IsOpen (s i)) :
    ContinuousOn f (⋃ i, s i) := by
  rintro x ⟨si, ⟨i, rfl⟩, hxsi⟩
  exact (hf i).continuousAt ((hs i).mem_nhds hxsi) |>.continuousWithinAt

/-- A function is continuous on a union of open sets `s i` iff it is continuous on each `s i`. -/
/-
**continuousOn_iUnion_iff_of_isOpen** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：continuousOn_iUnion_iff_of_isOpen {ι : Type*} {s : ι -> Set α} (hs : foral
l i, IsOpen (s i)) : ContinuousOn f (⋃ i, s i) ↔ forall i : ι, ContinuousOn f (s
 i)
参数：hs : forall i, IsOpen (s i)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `Set.subset_iUnion_of_subset`：subset_iUnion_of_subset {s : Set α} {t : ι 
-> Set α} (i : ι) (h : s subseteq t i) : s subseteq ⋃ i, t i
· 使用引理 `ContinuousOn.iUnion_of_isOpen`：ContinuousOn.iUnion_of_isOpen {ι : Type*}
 {s : ι -> Set α} (hf : forall i : ι, ContinuousOn f (s i)) (hs : forall i, IsOp
en (s i)) : Continu…

--- 原说明 ---
A function is continuous on a union of open sets `s i` iff it is continuous on e
ach `s i`.
-/
lemma continuousOn_iUnion_iff_of_isOpen {ι : Type*} {s : ι → Set α}
    (hs : ∀ i, IsOpen (s i)) :
    ContinuousOn f (⋃ i, s i) ↔ ∀ i : ι, ContinuousOn f (s i) :=
  ⟨fun h i ↦ h.mono <| subset_iUnion_of_subset i fun _ a ↦ a,
   fun h ↦ ContinuousOn.iUnion_of_isOpen h hs⟩
/-
**continuous_of_continuousOn_iUnion_of_isOpen** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：continuous_of_continuousOn_iUnion_of_isOpen {ι : Type*} {s : ι -> Set α} (
hf : forall i : ι, ContinuousOn f (s i)) (hs : forall i, IsOpen (s i)) (hs' : ⋃ 
i, s i = univ) : Continuous f
参数：hf : forall i : ι, ContinuousOn f (s i)；hs : forall i, IsOpen (s i)；hs' : ⋃ i
, s i = univ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuousOn_univ`：continuousOn_univ {f : α -> β} : ContinuousOn f univ 
↔ Continuous f
· 使用引理 `ContinuousOn.iUnion_of_isOpen`：ContinuousOn.iUnion_of_isOpen {ι : Type*}
 {s : ι -> Set α} (hf : forall i : ι, ContinuousOn f (s i)) (hs : forall i, IsOp
en (s i)) : Continu…
-/
lemma continuous_of_continuousOn_iUnion_of_isOpen {ι : Type*} {s : ι → Set α}
    (hf : ∀ i : ι, ContinuousOn f (s i)) (hs : ∀ i, IsOpen (s i)) (hs' : ⋃ i, s i = univ) :
    Continuous f := by
  rw [← continuousOn_univ, ← hs']
  exact ContinuousOn.iUnion_of_isOpen hf hs

/-- If `f` is continuous on some neighbourhood `s'` of `s` and `f` maps `s` to `t`,
the preimage of a set neighbourhood of `t` is a set neighbourhood of `s`. -/
-- See `Continuous.tendsto_nhdsSet` for a special case.
/-
**ContinuousOn.tendsto_nhdsSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.tendsto_nhdsSet {f : α -> β} {s s' : Set α} {t : Set β} (hf :
 ContinuousOn f s') (hs' : s' in 𝓝ˢ s) (hst : MapsTo f s t) : Tendsto f (𝓝ˢ s) (
𝓝ˢ t)
参数：hf : ContinuousOn f s'；hs' : s' in 𝓝ˢ s；hst : MapsTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhdsSet_iff_exists`：mem_nhdsSet_iff_exists : s in 𝓝ˢ t ↔ exists U : 
Set X, IsOpen U ∧ t subseteq U ∧ U subseteq s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `hasBasis_nhdsSet`：hasBasis_nhdsSet (s : Set X) : (𝓝ˢ s).HasBasis (fun U 
=> IsOpen U ∧ s subseteq U) fun U => U
· 使用定理 `ContinuousOn.isOpen_inter_preimage`：ContinuousOn.isOpen_inter_preimage {
t : Set β} (hf : ContinuousOn f s) (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s i
nter f ⁻¹' t)
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `Set.MapsTo.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {t₁ t₂ 
: Set β} {f : α → β},   Set.MapsTo f s₁ t₁ → s₂ ⊆ s₁ → t₁ ⊆ t₂ → Set.MapsTo f s₂
 t₂
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Set.mem_of_mem_inter_right`：mem_of_mem_inter_right {x : α} {a b : Set α}
 (h : x in a inter b) : x in b
-/
theorem ContinuousOn.tendsto_nhdsSet {f : α → β} {s s' : Set α} {t : Set β}
    (hf : ContinuousOn f s') (hs' : s' ∈ 𝓝ˢ s) (hst : MapsTo f s t) : Tendsto f (𝓝ˢ s) (𝓝ˢ t) := by
  obtain ⟨V, hV, hsV, hVs'⟩ := mem_nhdsSet_iff_exists.mp hs'
  refine ((hasBasis_nhdsSet s).tendsto_iff (hasBasis_nhdsSet t)).mpr fun U hU ↦
    ⟨V ∩ f ⁻¹' U, ?_, fun _ ↦ ?_⟩
  · exact ⟨(hf.mono hVs').isOpen_inter_preimage hV hU.1,
      subset_inter hsV (hst.mono Subset.rfl hU.2)⟩
  · intro h
    rw [← mem_preimage]
    exact mem_of_mem_inter_right h

/-- Preimage of a set neighborhood of `t` under a continuous map `f` is a set neighborhood of `s`
provided that `f` maps `s` to `t`. -/
/-
**Continuous.tendsto_nhdsSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.tendsto_nhdsSet {f : α -> β} {t : Set β} (hf : Continuous f) (h
st : MapsTo f s t) : Tendsto f (𝓝ˢ s) (𝓝ˢ t)
参数：hf : Continuous f；hst : MapsTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.tendsto_nhdsSet`：ContinuousOn.tendsto_nhdsSet {f : α -> β} 
{s s' : Set α} {t : Set β} (hf : ContinuousOn f s') (hs' : s' in 𝓝ˢ s) (hst : Ma
psTo f s t) : Tend…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f

--- 原说明 ---
Preimage of a set neighborhood of `t` under a continuous map `f` is a set neighb
orhood of `s`
provided that `f` maps `s` to `t`.
-/
theorem Continuous.tendsto_nhdsSet {f : α → β} {t : Set β} (hf : Continuous f)
    (hst : MapsTo f s t) : Tendsto f (𝓝ˢ s) (𝓝ˢ t) :=
  hf.continuousOn.tendsto_nhdsSet univ_mem hst
/-
**Continuous.tendsto_nhdsSet_nhds** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Continuous.tendsto_nhdsSet_nhds {b : β} {f : α -> β} (h : Continuous f) (h
' : EqOn f (fun _ => b) s) : Tendsto f (𝓝ˢ s) (𝓝 b)
参数：h : Continuous f；h' : EqOn f (fun _ => b) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsSet_singleton`：nhdsSet_singleton : 𝓝ˢ {x} = 𝓝 x
· 使用定理 `Continuous.tendsto_nhdsSet`：Continuous.tendsto_nhdsSet {f : α -> β} {t :
 Set β} (hf : Continuous f) (hst : MapsTo f s t) : Tendsto f (𝓝ˢ s) (𝓝ˢ t)
-/
lemma Continuous.tendsto_nhdsSet_nhds
    {b : β} {f : α → β} (h : Continuous f) (h' : EqOn f (fun _ ↦ b) s) :
    Tendsto f (𝓝ˢ s) (𝓝 b) := by
  rw [← nhdsSet_singleton]
  exact h.tendsto_nhdsSet h'
/-
**ContinuousOn.preimage_mem_nhdsSetWithin** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousOn.preimage_mem_nhdsSetWithin {f : α -> β} {s : Set α} (hf : Con
tinuousOn f s) {t u t' : Set β} (h : u in 𝓝ˢ[t'] t) : f ⁻¹' u in 𝓝ˢ[s inter f ⁻¹
' t'] (s inter f ⁻¹' t)
参数：hf : ContinuousOn f s；h : u in 𝓝ˢ[t'] t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `mem_nhdsSetWithin`：mem_nhdsSetWithin {s t u : Set α} : u in 𝓝ˢ[t] s ↔ ex
ists v, IsOpen v ∧ s subseteq v ∧ v inter t subseteq u
· 使用定理 `continuousOn_iff'`：continuousOn_iff' : ContinuousOn f s ↔ forall t : Set
 β, IsOpen t -> exists u, IsOpen u ∧ f ⁻¹' t inter s = u inter s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Eq.trans_subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] {a b c : α
} [inst : LE α], a = b → b ⊆ c → a ⊆ c
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.inter_subset_inter_left`：inter_subset_inter_left {s t : Set α} (u : 
Set α) (H : s subseteq t) : s inter u subseteq t inter u
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `Set.preimage_inter`：preimage_inter {s t : Set β} : f ⁻¹' (s inter t) = f
 ⁻¹' s inter f ⁻¹' t
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
lemma ContinuousOn.preimage_mem_nhdsSetWithin {f : α → β} {s : Set α}
    (hf : ContinuousOn f s) {t u t' : Set β} (h : u ∈ 𝓝ˢ[t'] t) :
    f ⁻¹' u ∈ 𝓝ˢ[s ∩ f ⁻¹' t'] (s ∩ f ⁻¹' t) := by
  have ⟨v, hv⟩ := mem_nhdsSetWithin.1 h
  have ⟨w, hw⟩ := continuousOn_iff'.1 hf v hv.1
  refine mem_nhdsSetWithin.2 ⟨w, hw.1, ?_, ?_⟩
  · exact (inter_comm _ _).trans_subset <| (inter_subset_inter_left _ <| preimage_mono hv.2.1).trans
      (hw.2.trans_subset inter_subset_left)
  · rw [← inter_assoc, ← hw.2, inter_comm _ s, inter_assoc, ← preimage_inter]
    exact inter_subset_right.trans <| preimage_mono hv.2.2

/-- If `f` is continuous on `s` and `u` is a neighbourhood of `t`, then `f ⁻¹' u` is a neighbourhood
of `s ∩ f ⁻¹' t` within `s`. -/
/-
**ContinuousOn.preimage_mem_nhdsSetWithin_of_mem_nhdsSet** 是 Mathlib 中的一个引理，位于命名
空间 ``。
形式化陈述：ContinuousOn.preimage_mem_nhdsSetWithin_of_mem_nhdsSet {f : α -> β} {s : S
et α} (hf : ContinuousOn f s) {t u : Set β} (h : u in 𝓝ˢ t) : f ⁻¹' u in 𝓝ˢ[s] (
s inter f ⁻¹' t)
参数：hf : ContinuousOn f s；h : u in 𝓝ˢ t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `nhdsSetWithin_univ`：nhdsSetWithin_univ {s : Set α} : 𝓝ˢ[univ] s = 𝓝ˢ s
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `ContinuousOn.preimage_mem_nhdsSetWithin`：ContinuousOn.preimage_mem_nhdsS
etWithin {f : α -> β} {s : Set α} (hf : ContinuousOn f s) {t u t' : Set β} (h : 
u in 𝓝ˢ[t'] t) : f ⁻¹' u in 𝓝…

--- 原说明 ---
If `f` is continuous on `s` and `u` is a neighbourhood of `t`, then `f ⁻¹' u` is
 a neighbourhood
of `s ∩ f ⁻¹' t` within `s`.
-/
lemma ContinuousOn.preimage_mem_nhdsSetWithin_of_mem_nhdsSet {f : α → β} {s : Set α}
    (hf : ContinuousOn f s) {t u : Set β} (h : u ∈ 𝓝ˢ t) : f ⁻¹' u ∈ 𝓝ˢ[s] (s ∩ f ⁻¹' t) := by
  simpa [h] using ContinuousOn.preimage_mem_nhdsSetWithin hf (t := t) (u := u) (t' := univ)
/-
**Continuous.preimage_mem_nhdsSetWithin** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Continuous.preimage_mem_nhdsSetWithin {f : α -> β} (hf : Continuous f) {s 
u s' : Set β} (h : u in 𝓝ˢ[s'] s) : f ⁻¹' u in 𝓝ˢ[f ⁻¹' s'] (f ⁻¹' s)
参数：hf : Continuous f；h : u in 𝓝ˢ[s'] s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用引理 `ContinuousOn.preimage_mem_nhdsSetWithin`：ContinuousOn.preimage_mem_nhdsS
etWithin {f : α -> β} {s : Set α} (hf : ContinuousOn f s) {t u t' : Set β} (h : 
u in 𝓝ˢ[t'] t) : f ⁻¹' u in 𝓝…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
-/
lemma Continuous.preimage_mem_nhdsSetWithin {f : α → β} (hf : Continuous f) {s u s' : Set β}
    (h : u ∈ 𝓝ˢ[s'] s) : f ⁻¹' u ∈ 𝓝ˢ[f ⁻¹' s'] (f ⁻¹' s) := by
  simpa using (hf.continuousOn (s := univ)).preimage_mem_nhdsSetWithin h
/-
**Continuous.preimage_mem_nhdsSet** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Continuous.preimage_mem_nhdsSet {f : α -> β} (hf : Continuous f) {s u : Se
t β} (h : u in 𝓝ˢ s) : f ⁻¹' u in 𝓝ˢ (f ⁻¹' s)
参数：hf : Continuous f；h : u in 𝓝ˢ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `nhdsSetWithin_univ`：nhdsSetWithin_univ {s : Set α} : 𝓝ˢ[univ] s = 𝓝ˢ s
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `Continuous.preimage_mem_nhdsSetWithin`：Continuous.preimage_mem_nhdsSetWi
thin {f : α -> β} (hf : Continuous f) {s u s' : Set β} (h : u in 𝓝ˢ[s'] s) : f ⁻
¹' u in 𝓝ˢ[f ⁻¹' s'] (f ⁻¹'…
-/
lemma Continuous.preimage_mem_nhdsSet {f : α → β} (hf : Continuous f) {s u : Set β}
    (h : u ∈ 𝓝ˢ s) : f ⁻¹' u ∈ 𝓝ˢ (f ⁻¹' s) := by
  simpa [h] using hf.preimage_mem_nhdsSetWithin (s := s) (u := u) (s' := univ)
