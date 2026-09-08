/-
Copyright (c) 2020 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo
-/
module

public import Mathlib.Dynamics.Flow

/-!
# ω-limits

For a function `ϕ : τ → α → β` where `β` is a topological space, we
define the ω-limit under `ϕ` of a set `s` in `α` with respect to
filter `f` on `τ`: an element `y : β` is in the ω-limit of `s` if the
forward images of `s` intersect arbitrarily small neighbourhoods of
`y` frequently "in the direction of `f`".

In practice `ϕ` is often a continuous monoid-act, but the definition
requires only that `ϕ` has a coercion to the appropriate function
type. In the case where `τ` is `ℕ` or `ℝ` and `f` is `atTop`, we
recover the usual definition of the ω-limit set as the set of all `y`
such that there exist sequences `(tₙ)`, `(xₙ)` such that `ϕ tₙ xₙ ⟶ y`
as `n ⟶ ∞`.

## Notation

The `omegaLimit` scope provides the localised notation `ω` for
`omegaLimit`, as well as `ω⁺` and `ω⁻` for `omegaLimit atTop` and
`omegaLimit atBot` respectively for when the acting monoid is
endowed with an order.
-/

@[expose] public section


open Set Function Filter Topology

/-!
### Definition and notation
-/
section omegaLimit

variable {τ : Type*} {α : Type*} {β : Type*} {ι : Type*}

/-- The ω-limit of a set `s` under `ϕ` with respect to a filter `f` is `⋂ u ∈ f, cl (ϕ u s)`. -/
/-
**omegaLimit** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：omegaLimit [TopologicalSpace β] (f : Filter τ) (ϕ : τ -> α -> β) (s : Set 
α) : Set β
参数：f : Filter τ；ϕ : τ -> α -> β；s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ω-limit of a set `s` under `ϕ` with respect to a filter `f` is `⋂ u ∈ f, cl 
(ϕ u s)`.
-/
def omegaLimit [TopologicalSpace β] (f : Filter τ) (ϕ : τ → α → β) (s : Set α) : Set β :=
  ⋂ u ∈ f, closure (image2 ϕ u s)

@[inherit_doc]
scoped[omegaLimit] notation "ω" => omegaLimit

/-- The ω-limit w.r.t. `Filter.atTop`. -/
scoped[omegaLimit] notation "ω⁺" => omegaLimit Filter.atTop

/-- The ω-limit w.r.t. `Filter.atBot`. -/
scoped[omegaLimit] notation "ω⁻" => omegaLimit Filter.atBot

variable [TopologicalSpace β]
variable (f : Filter τ) (ϕ : τ → α → β) (s s₁ s₂ : Set α)

/-!
### Elementary properties
-/
open omegaLimit

/-
**omegaLimit_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：omegaLimit_def : ω f ϕ s = ⋂ u in f, closure (image2 ϕ u s)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem omegaLimit_def : ω f ϕ s = ⋂ u ∈ f, closure (image2 ϕ u s) := rfl
/-
**omegaLimit_subset_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：omegaLimit_subset_of_tendsto {m : τ -> τ} {f₁ f₂ : Filter τ} (hf : Tendsto
 m f₁ f₂) : ω f₁ (fun t x => ϕ (m t) x) s subseteq ω f₂ ϕ s
参数：hf : Tendsto m f₁ f₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.iInter₂_mono'`：iInter₂_mono' {s : forall i, κ i -> Set α} {t : foral
l i', κ' i' -> Set α} (h : forall i' j', exists i j, s i j subseteq t i' j') : ⋂
 (i) (j…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.tendsto_def`：tendsto_def {f : α -> β} {l₁ : Filter α} {l₂ : Filte
r β} : Tendsto f l₁ l₂ ↔ forall s in l₂, f ⁻¹' s in l₁
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image2_image_left`：image2_image_left (f : γ -> β -> δ) (g : α -> γ) 
: image2 f (g '' s) t = image2 (fun a b => f (g a) b) s t
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `Set.image2_subset`：image2_subset (hs : s subseteq s') (ht : t subseteq t
') : image2 f s t subseteq image2 f s' t'
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem omegaLimit_subset_of_tendsto {m : τ → τ} {f₁ f₂ : Filter τ} (hf : Tendsto m f₁ f₂) :
    ω f₁ (fun t x ↦ ϕ (m t) x) s ⊆ ω f₂ ϕ s := by
  refine iInter₂_mono' fun u hu ↦ ⟨m ⁻¹' u, tendsto_def.mp hf _ hu, ?_⟩
  rw [← image2_image_left]
  exact closure_mono (image2_subset (image_preimage_subset _ _) Subset.rfl)
/-
**omegaLimit_mono_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：omegaLimit_mono_left {f₁ f₂ : Filter τ} (hf : f₁ <= f₂) : ω f₁ ϕ s subsete
q ω f₂ ϕ s
参数：hf : f₁ <= f₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `omegaLimit_subset_of_tendsto`：omegaLimit_subset_of_tendsto {m : τ -> τ} 
{f₁ f₂ : Filter τ} (hf : Tendsto m f₁ f₂) : ω f₁ (fun t x => ϕ (m t) x) s subset
eq ω f₂ ϕ s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_id'`：tendsto_id' {x y : Filter α} : Tendsto id x y ↔ x <=
 y
-/
theorem omegaLimit_mono_left {f₁ f₂ : Filter τ} (hf : f₁ ≤ f₂) : ω f₁ ϕ s ⊆ ω f₂ ϕ s :=
  omegaLimit_subset_of_tendsto ϕ s (tendsto_id'.2 hf)
/-
**omegaLimit_mono_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：omegaLimit_mono_right {s₁ s₂ : Set α} (hs : s₁ subseteq s₂) : ω f ϕ s₁ sub
seteq ω f ϕ s₂
参数：hs : s₁ subseteq s₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.iInter₂_mono`：iInter₂_mono {s t : forall i, κ i -> Set α} (h : foral
l i j, s i j subseteq t i j) : ⋂ (i) (j), s i j subseteq ⋂ (i) (j), t i j
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `Set.image2_subset`：image2_subset (hs : s subseteq s') (ht : t subseteq t
') : image2 f s t subseteq image2 f s' t'
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
-/
theorem omegaLimit_mono_right {s₁ s₂ : Set α} (hs : s₁ ⊆ s₂) : ω f ϕ s₁ ⊆ ω f ϕ s₂ :=
  iInter₂_mono fun _u _hu ↦ closure_mono (image2_subset Subset.rfl hs)
/-
**isClosed_omegaLimit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_omegaLimit : IsClosed (ω f ϕ s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_iInter`：isClosed_iInter {f : ι -> Set X} (h : forall i, IsClose
d (f i)) : IsClosed (⋂ i, f i)
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
-/
theorem isClosed_omegaLimit : IsClosed (ω f ϕ s) :=
  isClosed_iInter fun _u ↦ isClosed_iInter fun _hu ↦ isClosed_closure
/-
**mapsTo_omegaLimit'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mapsTo_omegaLimit' {α' β' : Type*} [TopologicalSpace β'] {f : Filter τ} {ϕ
 : τ -> α -> β} {ϕ' : τ -> α' -> β'} {ga : α -> α'} {s' : Set α'} (hs : MapsTo g
a s s') {gb : β -> β'} (hg : forallᶠ t in f, EqOn (gb ∘ ϕ t) (ϕ' t ∘ ga) s) (hgc
 : Continuous gb) : MapsTo gb (ω f ϕ s) (ω f ϕ' s')
参数：hs : MapsTo ga s s'；hg : forallᶠ t in f, EqOn (gb ∘ ϕ t) (ϕ' t ∘ ga) s；hgc : 
Continuous gb。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_mem_closure`：map_mem_closure {t : Set Y} (hf : Continuous f) (hx : x
 in closure s) (ht : MapsTo f s t) : f x in closure t
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.forall_mem_image2`：forall_mem_image2 {p : γ -> Prop} : (forall z in 
image2 f s t, p z) ↔ forall x in s, forall y in t, p (f x y)
· 使用定理 `Set.mem_image2_of_mem`：mem_image2_of_mem (ha : a in s) (hb : b in t) : f
 a b in image2 f s t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem mapsTo_omegaLimit' {α' β' : Type*} [TopologicalSpace β'] {f : Filter τ} {ϕ : τ → α → β}
    {ϕ' : τ → α' → β'} {ga : α → α'} {s' : Set α'} (hs : MapsTo ga s s') {gb : β → β'}
    (hg : ∀ᶠ t in f, EqOn (gb ∘ ϕ t) (ϕ' t ∘ ga) s) (hgc : Continuous gb) :
    MapsTo gb (ω f ϕ s) (ω f ϕ' s') := by
  simp only [omegaLimit_def, mem_iInter, MapsTo]
  intro y hy u hu
  refine map_mem_closure hgc (hy _ (inter_mem hu hg)) (forall_mem_image2.2 fun t ht x hx ↦ ?_)
  calc
    ϕ' t (ga x) ∈ image2 ϕ' u s' := mem_image2_of_mem ht.1 (hs hx)
    _ = gb (ϕ t x) := ht.2 hx |>.symm
/-
**mapsTo_omegaLimit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mapsTo_omegaLimit {α' β' : Type*} [TopologicalSpace β'] {f : Filter τ} {ϕ 
: τ -> α -> β} {ϕ' : τ -> α' -> β'} {ga : α -> α'} {s' : Set α'} (hs : MapsTo ga
 s s') {gb : β -> β'} (hg : forall t x, gb (ϕ t x) = ϕ' t (ga x)) (hgc : Continu
ous gb) : MapsTo gb (ω f ϕ s) (ω f ϕ' s')
参数：hs : MapsTo ga s s'；hg : forall t x, gb (ϕ t x) = ϕ' t (ga x)；hgc : Continuou
s gb。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mapsTo_omegaLimit'`：mapsTo_omegaLimit' {α' β' : Type*} [TopologicalSpace
 β'] {f : Filter τ} {ϕ : τ -> α -> β} {ϕ' : τ -> α' -> β'} {ga : α -> α'} {s' : 
Set α'} …
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
theorem mapsTo_omegaLimit {α' β' : Type*} [TopologicalSpace β'] {f : Filter τ} {ϕ : τ → α → β}
    {ϕ' : τ → α' → β'} {ga : α → α'} {s' : Set α'} (hs : MapsTo ga s s') {gb : β → β'}
    (hg : ∀ t x, gb (ϕ t x) = ϕ' t (ga x)) (hgc : Continuous gb) :
    MapsTo gb (ω f ϕ s) (ω f ϕ' s') :=
  mapsTo_omegaLimit' _ hs (Eventually.of_forall fun t x _hx ↦ hg t x) hgc
/-
**omegaLimit_image_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：omegaLimit_image_eq {α' : Type*} (ϕ : τ -> α' -> β) (f : Filter τ) (g : α 
-> α') : ω f ϕ (g '' s) = ω f (fun t x => ϕ t (g x)) s
参数：ϕ : τ -> α' -> β；f : Filter τ；g : α -> α'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.image2_image_right`：image2_image_right (f : α -> γ -> δ) (g : β -> γ
) : image2 f s (g '' t) = image2 (fun a b => f a (g b)) s t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem omegaLimit_image_eq {α' : Type*} (ϕ : τ → α' → β) (f : Filter τ) (g : α → α') :
    ω f ϕ (g '' s) = ω f (fun t x ↦ ϕ t (g x)) s := by simp only [omegaLimit, image2_image_right]
/-
**omegaLimit_preimage_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：omegaLimit_preimage_subset {α' : Type*} (ϕ : τ -> α' -> β) (s : Set α') (f
 : Filter τ) (g : α -> α') : ω f (fun t x => ϕ t (g x)) (g ⁻¹' s) subseteq ω f ϕ
 s
参数：ϕ : τ -> α' -> β；s : Set α'；f : Filter τ；g : α -> α'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mapsTo_omegaLimit`：mapsTo_omegaLimit {α' β' : Type*} [TopologicalSpace β
'] {f : Filter τ} {ϕ : τ -> α -> β} {ϕ' : τ -> α' -> β'} {ga : α -> α'} {s' : Se
t α'} (…
· 使用定理 `Set.mapsTo_preimage`：mapsTo_preimage (f : α -> β) (t : Set β) : MapsTo f
 (f ⁻¹' t) t
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem omegaLimit_preimage_subset {α' : Type*} (ϕ : τ → α' → β) (s : Set α') (f : Filter τ)
    (g : α → α') : ω f (fun t x ↦ ϕ t (g x)) (g ⁻¹' s) ⊆ ω f ϕ s :=
  mapsTo_omegaLimit _ (mapsTo_preimage _ _) (fun _t _x ↦ rfl) continuous_id

/-!
### Equivalent definitions of the omega limit

The next few lemmas are various versions of the property
characterising ω-limits:
-/

/-- An element `y` is in the ω-limit set of `s` w.r.t. `f` if the
preimages of an arbitrary neighbourhood of `y` frequently (w.r.t. `f`) intersects of `s`. -/
/-
**mem_omegaLimit_iff_frequently** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_omegaLimit_iff_frequently (y : β) : y in ω f ϕ s ↔ forall n in 𝓝 y, ex
istsᶠ t in f, (s inter ϕ t ⁻¹' n).Nonempty
参数：y : β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s

--- 原说明 ---
An element `y` is in the ω-limit set of `s` w.r.t. `f` if the
preimages of an arbitrary neighbourhood of `y` frequently (w.r.t. `f`) intersect
s of `s`.
-/
theorem mem_omegaLimit_iff_frequently (y : β) :
    y ∈ ω f ϕ s ↔ ∀ n ∈ 𝓝 y, ∃ᶠ t in f, (s ∩ ϕ t ⁻¹' n).Nonempty := by
  simp_rw [frequently_iff, omegaLimit_def, mem_iInter, mem_closure_iff_nhds]
  constructor
  · intro h _ hn _ hu
    rcases h _ hu _ hn with ⟨_, _, _, ht, _, hx, rfl⟩
    exact ⟨_, ht, _, hx, by rwa [mem_preimage]⟩
  · intro h _ hu _ hn
    rcases h _ hn hu with ⟨_, ht, _, hx, hϕtx⟩
    exact ⟨_, hϕtx, _, ht, _, hx, rfl⟩

/-- An element `y` is in the ω-limit set of `s` w.r.t. `f` if the forward images of `s`
frequently (w.r.t. `f`) intersect arbitrary neighbourhoods of `y`. -/
/-
**mem_omegaLimit_iff_frequently** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_omegaLimit_iff_frequently (y : β) : y in ω f ϕ s ↔ forall n in 𝓝 y, ex
istsᶠ t in f, (s inter ϕ t ⁻¹' n).Nonempty
参数：y : β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s

--- 原说明 ---
An element `y` is in the ω-limit set of `s` w.r.t. `f` if the forward images of 
`s`
frequently (w.r.t. `f`) intersect arbitrary neighbourhoods of `y`.
-/
theorem mem_omegaLimit_iff_frequently₂ (y : β) :
    y ∈ ω f ϕ s ↔ ∀ n ∈ 𝓝 y, ∃ᶠ t in f, (ϕ t '' s ∩ n).Nonempty := by
  simp_rw [mem_omegaLimit_iff_frequently, image_inter_nonempty_iff]

/-- An element `y` is in the ω-limit of `x` w.r.t. `f` if the forward
images of `x` frequently (w.r.t. `f`) falls within an arbitrary neighbourhood of `y`. -/
/-
**mem_omegaLimit_singleton_iff_mapClusterPt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_omegaLimit_singleton_iff_mapClusterPt (x : α) (y : β) : y in ω f ϕ {x}
 ↔ MapClusterPt y f fun t => ϕ t x
参数：x : α；y : β。
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
An element `y` is in the ω-limit of `x` w.r.t. `f` if the forward
images of `x` frequently (w.r.t. `f`) falls within an arbitrary neighbourhood of
 `y`.
-/
theorem mem_omegaLimit_singleton_iff_mapClusterPt (x : α) (y : β) :
    y ∈ ω f ϕ {x} ↔ MapClusterPt y f fun t ↦ ϕ t x := by
  simp_rw [mem_omegaLimit_iff_frequently, mapClusterPt_iff_frequently, singleton_inter_nonempty,
    mem_preimage]

@[deprecated (since := "2026-03-31")]
alias mem_omegaLimit_singleton_iff_map_cluster_point := mem_omegaLimit_singleton_iff_mapClusterPt

/-!
### Set operations and omega limits
-/

/-
**omegaLimit_inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：omegaLimit_inter : ω f ϕ (s₁ inter s₂) subseteq ω f ϕ s₁ inter ω f ϕ s₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `omegaLimit_mono_right`：omegaLimit_mono_right {s₁ s₂ : Set α} (hs : s₁ su
bseteq s₂) : ω f ϕ s₁ subseteq ω f ϕ s₂
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t

--- 原说明 ---
### Set operations and omega limits
-/
theorem omegaLimit_inter : ω f ϕ (s₁ ∩ s₂) ⊆ ω f ϕ s₁ ∩ ω f ϕ s₂ :=
  subset_inter (omegaLimit_mono_right _ _ inter_subset_left)
    (omegaLimit_mono_right _ _ inter_subset_right)
/-
**omegaLimit_iInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：omegaLimit_iInter (p : ι -> Set α) : ω f ϕ (⋂ i, p i) subseteq ⋂ i, ω f ϕ 
(p i)
参数：p : ι -> Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_iInter`：subset_iInter {t : Set β} {s : ι -> Set β} (h : foral
l i, t subseteq s i) : t subseteq ⋂ i, s i
· 使用定理 `omegaLimit_mono_right`：omegaLimit_mono_right {s₁ s₂ : Set α} (hs : s₁ su
bseteq s₂) : ω f ϕ s₁ subseteq ω f ϕ s₂
· 使用定理 `Set.iInter_subset`：iInter_subset : forall (s : ι -> Set β) (i : ι), ⋂ i,
 s i subseteq s i
-/
theorem omegaLimit_iInter (p : ι → Set α) : ω f ϕ (⋂ i, p i) ⊆ ⋂ i, ω f ϕ (p i) :=
  subset_iInter fun _i ↦ omegaLimit_mono_right _ _ (iInter_subset _ _)
/-
**omegaLimit_union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：omegaLimit_union : ω f ϕ (s₁ union s₂) = ω f ϕ s₁ union ω f ϕ s₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.union_inter_distrib_right`：union_inter_distrib_right (s t u : Set α)
 : (s union t) inter u = s inter u union t inter u
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.inter_subset_inter_right`：inter_subset_inter_right {s t : Set α} (u 
: Set α) (H : s subseteq t) : u inter s subseteq u inter t
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `omegaLimit_mono_right`：omegaLimit_mono_right {s₁ s₂ : Set α} (hs : s₁ su
bseteq s₂) : ω f ϕ s₁ subseteq ω f ϕ s₂
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
-/
theorem omegaLimit_union : ω f ϕ (s₁ ∪ s₂) = ω f ϕ s₁ ∪ ω f ϕ s₂ := by
  ext y; constructor
  · simp only [mem_union, mem_omegaLimit_iff_frequently, union_inter_distrib_right, union_nonempty,
      frequently_or_distrib]
    contrapose!
    simp only [← subset_empty_iff]
    rintro ⟨⟨n₁, hn₁, h₁⟩, ⟨n₂, hn₂, h₂⟩⟩
    refine ⟨n₁ ∩ n₂, inter_mem hn₁ hn₂, h₁.mono fun t ↦ ?_, h₂.mono fun t ↦ ?_⟩
    exacts [Subset.trans <| inter_subset_inter_right _ <| preimage_mono inter_subset_left,
      Subset.trans <| inter_subset_inter_right _ <| preimage_mono inter_subset_right]
  · rintro (hy | hy)
    exacts [omegaLimit_mono_right _ _ subset_union_left hy,
      omegaLimit_mono_right _ _ subset_union_right hy]
/-
**omegaLimit_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：omegaLimit_iUnion (p : ι -> Set α) : ⋃ i, ω f ϕ (p i) subseteq ω f ϕ (⋃ i,
 p i)
参数：p : ι -> Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnion_subset_iff`：iUnion_subset_iff {s : ι -> Set α} {t : Set α} : 
⋃ i, s i subseteq t ↔ forall i, s i subseteq t
· 使用定理 `omegaLimit_mono_right`：omegaLimit_mono_right {s₁ s₂ : Set α} (hs : s₁ su
bseteq s₂) : ω f ϕ s₁ subseteq ω f ϕ s₂
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
-/
theorem omegaLimit_iUnion (p : ι → Set α) : ⋃ i, ω f ϕ (p i) ⊆ ω f ϕ (⋃ i, p i) := by
  rw [iUnion_subset_iff]
  exact fun i ↦ omegaLimit_mono_right _ _ (subset_iUnion _ _)

/-!
Different expressions for omega limits, useful for rewrites. In
particular, one may restrict the intersection to sets in `f` which are
subsets of some set `v` also in `f`.
-/

/-
**omegaLimit_eq_iInter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：omegaLimit_eq_iInter : ω f ϕ s = ⋂ u : ↥f.sets, closure (image2 ϕ u s)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.biInter_eq_iInter`：biInter_eq_iInter (s : Set α) (t : forall x in s,
 Set β) : ⋂ x in s, t x ‹_› = ⋂ x : s, t x x.2

--- 原说明 ---
Different expressions for omega limits, useful for rewrites. In
particular, one may restrict the intersection to sets in `f` which are
subsets of some set `v` also in `f`.
-/
theorem omegaLimit_eq_iInter : ω f ϕ s = ⋂ u : ↥f.sets, closure (image2 ϕ u s) :=
  biInter_eq_iInter _ _
/-
**omegaLimit_eq_biInter_inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：omegaLimit_eq_biInter_inter {v : Set τ} (hv : v in f) : ω f ϕ s = ⋂ u in f
, closure (image2 ϕ (u inter v) s)
参数：hv : v in f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.iInter₂_mono'`：iInter₂_mono' {s : forall i, κ i -> Set α} {t : foral
l i', κ' i' -> Set α} (h : forall i' j', exists i j, s i j subseteq t i' j') : ⋂
 (i) (j…
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `Set.iInter₂_mono`：iInter₂_mono {s t : forall i, κ i -> Set α} (h : foral
l i j, s i j subseteq t i j) : ⋂ (i) (j), s i j subseteq ⋂ (i) (j), t i j
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `Set.image2_subset`：image2_subset (hs : s subseteq s') (ht : t subseteq t
') : image2 f s t subseteq image2 f s' t'
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
theorem omegaLimit_eq_biInter_inter {v : Set τ} (hv : v ∈ f) :
    ω f ϕ s = ⋂ u ∈ f, closure (image2 ϕ (u ∩ v) s) :=
  Subset.antisymm (iInter₂_mono' fun u hu ↦ ⟨u ∩ v, inter_mem hu hv, Subset.rfl⟩)
    (iInter₂_mono fun _u _hu ↦ closure_mono <| image2_subset inter_subset_left Subset.rfl)
/-
**omegaLimit_eq_iInter_inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：omegaLimit_eq_iInter_inter {v : Set τ} (hv : v in f) : ω f ϕ s = ⋂ u : ↥f.
sets, closure (image2 ϕ (u inter v) s)
参数：hv : v in f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `omegaLimit_eq_biInter_inter`：omegaLimit_eq_biInter_inter {v : Set τ} (hv
 : v in f) : ω f ϕ s = ⋂ u in f, closure (image2 ϕ (u inter v) s)
· 使用定理 `Set.biInter_eq_iInter`：biInter_eq_iInter (s : Set α) (t : forall x in s,
 Set β) : ⋂ x in s, t x ‹_› = ⋂ x : s, t x x.2
-/
theorem omegaLimit_eq_iInter_inter {v : Set τ} (hv : v ∈ f) :
    ω f ϕ s = ⋂ u : ↥f.sets, closure (image2 ϕ (u ∩ v) s) := by
  rw [omegaLimit_eq_biInter_inter _ _ _ hv]
  apply biInter_eq_iInter
/-
**omegaLimit_subset_closure_image2** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：omegaLimit_subset_closure_image2 {u : Set τ} (hu : u in f) : ω f ϕ s subse
teq closure (image2 ϕ u s)
参数：hu : u in f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `omegaLimit_eq_iInter`：omegaLimit_eq_iInter : ω f ϕ s = ⋂ u : ↥f.sets, cl
osure (image2 ϕ u s)
· 使用定理 `Set.mem_iInter`：mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ 
forall i, x in s i
-/
theorem omegaLimit_subset_closure_image2 {u : Set τ} (hu : u ∈ f) :
    ω f ϕ s ⊆ closure (image2 ϕ u s) := by
  rw [omegaLimit_eq_iInter]
  intro _ hx
  rw [mem_iInter] at hx
  exact hx ⟨u, hu⟩

@[deprecated (since := "2026-03-31")]
alias omegaLimit_subset_closure_fw_image := omegaLimit_subset_closure_image2

-- An instance with better keys
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited f.sets := Filter.inhabitedMem

/-!
### ω-limits and compactness
-/

/-- A set is eventually carried into any open neighbourhood of its ω-limit:
if `c` is a compact set such that `closure {ϕ t x | t ∈ v, x ∈ s} ⊆ c` for some `v ∈ f`
and `n` is an open neighbourhood of `ω f ϕ s`, then for some `u ∈ f` we have
`closure {ϕ t x | t ∈ u, x ∈ s} ⊆ n`. -/
/-
**eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subse
t'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_s
ubset' {c : Set β} (hc₁ : IsCompact c) (hc₂ : exists v in f, closure (image2 ϕ v
 s) subseteq c) {n : Set β} (hn₁ : IsOpen n) (hn₂ : ω f ϕ s subseteq n) : exists
 u in f, closure (image2 ϕ u s) subseteq n
参数：hc₁ : IsCompact c；hc₂ : exists v in f, closure (image2 ϕ v s) subseteq c；hn₁ 
: IsOpen n；hn₂ : ω f ϕ s subseteq n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.diff`：IsCompact.diff (hs : IsCompact s) (ht : IsOpen t) : IsCo
mpact (s \ t)
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `Set.biUnion_eq_iUnion`：biUnion_eq_iUnion (s : Set α) (t : forall x in s,
 Set β) : ⋃ x in s, t x ‹_› = ⋃ x : s, t x x.2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sdiff_subset_comm`：sdiff_subset_comm {s t u : Set α} : s \ t subsete
q u ↔ s \ u subseteq t
· 使用定理 `Set.sdiff_iUnion`：sdiff_iUnion [Nonempty ι] (s : Set β) (t : ι -> Set β)
 : (s \ ⋃ i, t i) = ⋂ i, s \ t i
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.sdiff_compl`：sdiff_compl : s \ tᶜ = s inter t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_iInter`：inter_iInter [Nonempty ι] (s : Set β) (t : ι -> Set β)
 : (s inter ⋂ i, t i) = ⋂ i, s inter t i
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `omegaLimit_eq_iInter_inter`：omegaLimit_eq_iInter_inter {v : Set τ} (hv :
 v in f) : ω f ϕ s = ⋂ u : ↥f.sets, closure (image2 ϕ (u inter v) s)
· 使用定理 `IsCompact.elim_finite_subcover_image`：IsCompact.elim_finite_subcover_ima
ge {b : Set ι} {c : ι -> Set X} (hs : IsCompact s) (hc₁ : forall i in b, IsOpen 
(c i)) (hc₂ : s subseteq ⋃…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `Set.image2_subset`：image2_subset (hs : s subseteq s') (ht : t subseteq t
') : image2 f s t subseteq image2 f s' t'
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
A set is eventually carried into any open neighbourhood of its ω-limit:
if `c` is a compact set such that `closure {ϕ t x | t ∈ v, x ∈ s} ⊆ c` for some 
`v ∈ f`
and `n` is an open neighbourhood of `ω f ϕ s`, then for some `u ∈ f` we have
`closure {ϕ t x | t ∈ u, x ∈ s} ⊆ n`.
-/
theorem eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset' {c : Set β}
    (hc₁ : IsCompact c) (hc₂ : ∃ v ∈ f, closure (image2 ϕ v s) ⊆ c) {n : Set β} (hn₁ : IsOpen n)
    (hn₂ : ω f ϕ s ⊆ n) : ∃ u ∈ f, closure (image2 ϕ u s) ⊆ n := by
  rcases hc₂ with ⟨v, hv₁, hv₂⟩
  let k := closure (image2 ϕ v s)
  have hk : IsCompact (k \ n) :=
    (hc₁.of_isClosed_subset isClosed_closure hv₂).diff hn₁
  let j u := (closure (image2 ϕ (u ∩ v) s))ᶜ
  have hj₁ : ∀ u ∈ f, IsOpen (j u) := fun _ _ ↦ isOpen_compl_iff.mpr isClosed_closure
  have hj₂ : k \ n ⊆ ⋃ u ∈ f, j u := by
    have : ⋃ u ∈ f, j u = ⋃ u : (↥f.sets), j u := biUnion_eq_iUnion _ _
    rw [this, sdiff_subset_comm, sdiff_iUnion]
    rw [omegaLimit_eq_iInter_inter _ _ _ hv₁] at hn₂
    simp_rw [j, sdiff_compl]
    rw [← inter_iInter]
    exact Subset.trans inter_subset_right hn₂
  rcases hk.elim_finite_subcover_image hj₁ hj₂ with ⟨g, hg₁ : ∀ u ∈ g, u ∈ f, hg₂, hg₃⟩
  let w := (⋂ u ∈ g, u) ∩ v
  have hw₂ : w ∈ f := by simpa [w, *]
  have hw₃ : k \ n ⊆ (closure (image2 ϕ w s))ᶜ := by
    apply Subset.trans hg₃
    simp only [j, iUnion_subset_iff, compl_subset_compl]
    intro u hu
    unfold w
    gcongr
    refine iInter_subset_of_subset u (iInter_subset_of_subset hu ?_)
    all_goals exact Subset.rfl
  have hw₄ : kᶜ ⊆ (closure (image2 ϕ w s))ᶜ := by
    simp only [compl_subset_compl]
    exact closure_mono (image2_subset inter_subset_right Subset.rfl)
  have hnc : nᶜ ⊆ k \ n ∪ kᶜ := by rw [union_comm, ← inter_subset, sdiff_eq, inter_comm]
  have hw : closure (image2 ϕ w s) ⊆ n :=
    compl_subset_compl.mp (Subset.trans hnc (union_subset hw₃ hw₄))
  exact ⟨_, hw₂, hw⟩

/-- A set is eventually carried into any open neighbourhood of its ω-limit:
if `c` is a compact set such that `closure {ϕ t x | t ∈ v, x ∈ s} ⊆ c` for some `v ∈ f`
and `n` is an open neighbourhood of `ω f ϕ s`, then for some `u ∈ f` we have
`closure {ϕ t x | t ∈ u, x ∈ s} ⊆ n`. -/
/-
**eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subse
t** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_s
ubset [T2Space β] {c : Set β} (hc₁ : IsCompact c) (hc₂ : forallᶠ t in f, MapsTo 
(ϕ t) s c) {n : Set β} (hn₁ : IsOpen n) (hn₂ : ω f ϕ s subseteq n) : exists u in
 f, closure (image2 ϕ u s) subseteq n
参数：hc₁ : IsCompact c；hc₂ : forallᶠ t in f, MapsTo (ϕ t) s c；hn₁ : IsOpen n；hn₂ :
 ω f ϕ s subseteq n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit
_subset'`：eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLim
it_subset' {c : Set β} (hc₁ : IsCompact c) (hc₂ : exists v in f, closu…
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image2_subset_iff`：image2_subset_iff {u : Set γ} : image2 f s t subs
eteq u ↔ forall x in s, forall y in t, f x y in u
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s

--- 原说明 ---
A set is eventually carried into any open neighbourhood of its ω-limit:
if `c` is a compact set such that `closure {ϕ t x | t ∈ v, x ∈ s} ⊆ c` for some 
`v ∈ f`
and `n` is an open neighbourhood of `ω f ϕ s`, then for some `u ∈ f` we have
`closure {ϕ t x | t ∈ u, x ∈ s} ⊆ n`.
-/
theorem eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset [T2Space β]
    {c : Set β} (hc₁ : IsCompact c) (hc₂ : ∀ᶠ t in f, MapsTo (ϕ t) s c) {n : Set β} (hn₁ : IsOpen n)
    (hn₂ : ω f ϕ s ⊆ n) : ∃ u ∈ f, closure (image2 ϕ u s) ⊆ n :=
  eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset' f ϕ _ hc₁
    ⟨_, hc₂, closure_minimal (image2_subset_iff.2 fun _t ↦ id) hc₁.isClosed⟩ hn₁ hn₂
/-
**eventually_mapsTo_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset** 是 Ma
thlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_mapsTo_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset [T
2Space β] {c : Set β} (hc₁ : IsCompact c) (hc₂ : forallᶠ t in f, MapsTo (ϕ t) s 
c) {n : Set β} (hn₁ : IsOpen n) (hn₂ : ω f ϕ s subseteq n) : forallᶠ t in f, Map
sTo (ϕ t) s n
参数：hc₁ : IsCompact c；hc₂ : forallᶠ t in f, MapsTo (ϕ t) s c；hn₁ : IsOpen n；hn₂ :
 ω f ϕ s subseteq n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit
_subset`：eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimi
t_subset [T2Space β] {c : Set β} (hc₁ : IsCompact c) (hc₂ : forallᶠ t…
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Set.mem_image2_of_mem`：mem_image2_of_mem (ha : a in s) (hb : b in t) : f
 a b in image2 f s t
-/
theorem eventually_mapsTo_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset [T2Space β]
    {c : Set β} (hc₁ : IsCompact c) (hc₂ : ∀ᶠ t in f, MapsTo (ϕ t) s c) {n : Set β} (hn₁ : IsOpen n)
    (hn₂ : ω f ϕ s ⊆ n) : ∀ᶠ t in f, MapsTo (ϕ t) s n := by
  rcases eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset f ϕ s hc₁
      hc₂ hn₁ hn₂ with
    ⟨u, hu_mem, hu⟩
  refine mem_of_superset hu_mem fun t ht x hx ↦ ?_
  exact hu (subset_closure <| mem_image2_of_mem ht hx)
/-
**eventually_closure_subset_of_isOpen_of_omegaLimit_subset** 是 Mathlib 中的一个定理，位于
命名空间 ``。
形式化陈述：eventually_closure_subset_of_isOpen_of_omegaLimit_subset [CompactSpace β] 
{v : Set β} (hv₁ : IsOpen v) (hv₂ : ω f ϕ s subseteq v) : exists u in f, closure
 (image2 ϕ u s) subseteq v
参数：hv₁ : IsOpen v；hv₂ : ω f ϕ s subseteq v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit
_subset'`：eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLim
it_subset' {c : Set β} (hc₁ : IsCompact c) (hc₂ : exists v in f, closu…
· 使用定理 `isCompact_univ`：isCompact_univ [h : CompactSpace X] : IsCompact (univ : 
Set X)
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem eventually_closure_subset_of_isOpen_of_omegaLimit_subset [CompactSpace β] {v : Set β}
    (hv₁ : IsOpen v) (hv₂ : ω f ϕ s ⊆ v) : ∃ u ∈ f, closure (image2 ϕ u s) ⊆ v :=
  eventually_closure_subset_of_isCompact_absorbing_of_isOpen_of_omegaLimit_subset' _ _ _
    isCompact_univ ⟨univ, univ_mem, subset_univ _⟩ hv₁ hv₂
/-
**eventually_mapsTo_of_isOpen_of_omegaLimit_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_mapsTo_of_isOpen_of_omegaLimit_subset [CompactSpace β] {v : Set
 β} (hv₁ : IsOpen v) (hv₂ : ω f ϕ s subseteq v) : forallᶠ t in f, MapsTo (ϕ t) s
 v
参数：hv₁ : IsOpen v；hv₂ : ω f ϕ s subseteq v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eventually_closure_subset_of_isOpen_of_omegaLimit_subset`：eventually_clo
sure_subset_of_isOpen_of_omegaLimit_subset [CompactSpace β] {v : Set β} (hv₁ : I
sOpen v) (hv₂ : ω f ϕ s subseteq v) : exists u…
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Set.mem_image2_of_mem`：mem_image2_of_mem (ha : a in s) (hb : b in t) : f
 a b in image2 f s t
-/
theorem eventually_mapsTo_of_isOpen_of_omegaLimit_subset [CompactSpace β] {v : Set β}
    (hv₁ : IsOpen v) (hv₂ : ω f ϕ s ⊆ v) : ∀ᶠ t in f, MapsTo (ϕ t) s v := by
  rcases eventually_closure_subset_of_isOpen_of_omegaLimit_subset f ϕ s hv₁ hv₂ with ⟨u, hu_mem, hu⟩
  refine mem_of_superset hu_mem fun t ht x hx ↦ ?_
  exact hu (subset_closure <| mem_image2_of_mem ht hx)

/-- The ω-limit of a nonempty set w.r.t. a nontrivial filter is nonempty. -/
/-
**nonempty_omegaLimit_of_isCompact_absorbing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonempty_omegaLimit_of_isCompact_absorbing [NeBot f] {c : Set β} (hc₁ : Is
Compact c) (hc₂ : exists v in f, closure (image2 ϕ v s) subseteq c) (hs : s.None
mpty) : (ω f ϕ s).Nonempty
参数：hc₁ : IsCompact c；hc₂ : exists v in f, closure (image2 ϕ v s) subseteq c；hs :
 s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `omegaLimit_eq_iInter_inter`：omegaLimit_eq_iInter_inter {v : Set τ} (hv :
 v in f) : ω f ϕ s = ⋂ u : ↥f.sets, closure (image2 ϕ (u inter v) s)
· 使用定理 `IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed`：IsCom
pact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed {ι : Type v} [hι : 
Nonempty ι] (t : ι -> Set X) (htd : Directed (· ⊇ ·) t)…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `Set.image2_subset`：image2_subset (hs : s subseteq s') (ht : t subseteq t
') : image2 f s t subseteq image2 f s' t'
· 使用定理 `Set.inter_subset_inter_left`：inter_subset_inter_left {s t : Set α} (u : 
Set α) (H : s subseteq t) : s inter u subseteq t inter u
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `Set.Nonempty.image2`：∀ {α : Type u_1} {β : Type u_3} {γ : Type u_5} {f :
 α → β → γ} {s : Set α} {t : Set β},   s.Nonempty → t.Nonempty → (Set.image2 f s
 t).Nonem…
· 使用定理 `Filter.nonempty_of_mem`：nonempty_of_mem {f : Filter α} [hf : NeBot f] {s
 : Set α} (hs : s in f) : s.Nonempty
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
The ω-limit of a nonempty set w.r.t. a nontrivial filter is nonempty.
-/
theorem nonempty_omegaLimit_of_isCompact_absorbing [NeBot f] {c : Set β} (hc₁ : IsCompact c)
    (hc₂ : ∃ v ∈ f, closure (image2 ϕ v s) ⊆ c) (hs : s.Nonempty) : (ω f ϕ s).Nonempty := by
  rcases hc₂ with ⟨v, hv₁, hv₂⟩
  rw [omegaLimit_eq_iInter_inter _ _ _ hv₁]
  apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
  · rintro ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩
    use ⟨u₁ ∩ u₂, inter_mem hu₁ hu₂⟩
    constructor
    all_goals exact closure_mono (image2_subset (inter_subset_inter_left _ (by simp)) Subset.rfl)
  · intro u
    have hn : (image2 ϕ (u ∩ v) s).Nonempty :=
      Nonempty.image2 (Filter.nonempty_of_mem (inter_mem u.prop hv₁)) hs
    exact hn.mono subset_closure
  · intro
    apply hc₁.of_isClosed_subset isClosed_closure
    grw [inter_subset_right, hv₂]
  · exact fun _ ↦ isClosed_closure
/-
**nonempty_omegaLimit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonempty_omegaLimit [CompactSpace β] [NeBot f] (hs : s.Nonempty) : (ω f ϕ 
s).Nonempty
参数：hs : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_omegaLimit_of_isCompact_absorbing`：nonempty_omegaLimit_of_isCom
pact_absorbing [NeBot f] {c : Set β} (hc₁ : IsCompact c) (hc₂ : exists v in f, c
losure (image2 ϕ v s) subseteq c…
· 使用定理 `isCompact_univ`：isCompact_univ [h : CompactSpace X] : IsCompact (univ : 
Set X)
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem nonempty_omegaLimit [CompactSpace β] [NeBot f] (hs : s.Nonempty) : (ω f ϕ s).Nonempty :=
  nonempty_omegaLimit_of_isCompact_absorbing _ _ _ isCompact_univ ⟨univ, univ_mem, subset_univ _⟩ hs

end omegaLimit

/-!
### ω-limits of flows by a monoid
-/
namespace Flow

variable {τ : Type*} [TopologicalSpace τ] [AddMonoid τ] {α : Type*}
  [TopologicalSpace α] (f : Filter τ) (ϕ : Flow τ α) (s : Set α)

open omegaLimit

/-
**Flow.isInvariant_omegaLimit** 是 Mathlib 中的一个定理，位于命名空间 `Flow`。
形式化陈述：isInvariant_omegaLimit (hf : forall t, Tendsto (t + ·) f f) : IsInvariant 
ϕ (ω f ϕ s)
参数：hf : forall t, Tendsto (t + ·) f f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.mono_right`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t₁ t
₂ : Set β} {f : α → β}, Set.MapsTo f s t₁ → t₁ ⊆ t₂ → Set.MapsTo f s t₂
· 使用定理 `mapsTo_omegaLimit`：mapsTo_omegaLimit {α' β' : Type*} [TopologicalSpace β
'] {f : Filter τ} {ϕ : τ -> α -> β} {ϕ' : τ -> α' -> β'} {ga : α -> α'} {s' : Se
t α'} (…
· 使用定理 `Set.mapsTo_id`：mapsTo_id (s : Set α) : MapsTo id s s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Flow.map_add`：map_add (t₁ t₂ : τ) (x : α) : ϕ (t₁ + t₂) x = ϕ t₁ (ϕ t₂ x
)
· 使用定理 `Continuous.flow`：∀ {τ : Type u_1} {α : Type u_2} [inst : TopologicalSpac
e τ] [inst_1 : TopologicalSpace α] [inst_2 : AddZero τ]   (ϕ : Flow τ α) {β : Ty
pe u_…
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `omegaLimit_subset_of_tendsto`：omegaLimit_subset_of_tendsto {m : τ -> τ} 
{f₁ f₂ : Filter τ} (hf : Tendsto m f₁ f₂) : ω f₁ (fun t x => ϕ (m t) x) s subset
eq ω f₂ ϕ s
-/
theorem isInvariant_omegaLimit (hf : ∀ t, Tendsto (t + ·) f f) : IsInvariant ϕ (ω f ϕ s) := by
  refine fun t ↦ MapsTo.mono_right ?_ (omegaLimit_subset_of_tendsto ϕ s (hf t))
  exact
    mapsTo_omegaLimit _ (mapsTo_id _) (fun t' x ↦ (ϕ.map_add _ _ _).symm)
      (continuous_const.flow ϕ continuous_id)
/-
**Flow.omegaLimit_image_subset** 是 Mathlib 中的一个定理，位于命名空间 `Flow`。
形式化陈述：omegaLimit_image_subset (t : τ) (ht : Tendsto (· + t) f f) : ω f ϕ (ϕ t ''
 s) subseteq ω f ϕ s
参数：t : τ；ht : Tendsto (· + t) f f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `omegaLimit_image_eq`：omegaLimit_image_eq {α' : Type*} (ϕ : τ -> α' -> β)
 (f : Filter τ) (g : α -> α') : ω f ϕ (g '' s) = ω f (fun t x => ϕ t (g x)) s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `omegaLimit_subset_of_tendsto`：omegaLimit_subset_of_tendsto {m : τ -> τ} 
{f₁ f₂ : Filter τ} (hf : Tendsto m f₁ f₂) : ω f₁ (fun t x => ϕ (m t) x) s subset
eq ω f₂ ϕ s
-/
theorem omegaLimit_image_subset (t : τ) (ht : Tendsto (· + t) f f) :
    ω f ϕ (ϕ t '' s) ⊆ ω f ϕ s := by
  simp only [omegaLimit_image_eq, ← map_add]
  exact omegaLimit_subset_of_tendsto ϕ s ht

end Flow

/-!
### ω-limits of flows by a group
-/
namespace Flow

variable {τ : Type*} [TopologicalSpace τ] [AddCommGroup τ] {α : Type*}
  [TopologicalSpace α] (f : Filter τ) (ϕ : Flow τ α) (s : Set α)

open omegaLimit

/-- the ω-limit of a forward image of `s` is the same as the ω-limit of `s`. -/
@[simp]
/-
**Flow.omegaLimit_image_eq** 是 Mathlib 中的一个定理，位于命名空间 `Flow`。
形式化陈述：omegaLimit_image_eq (hf : forall t, Tendsto (· + t) f f) (t : τ) : ω f ϕ (
ϕ t '' s) = ω f ϕ s
参数：hf : forall t, Tendsto (· + t) f f；t : τ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Flow.omegaLimit_image_subset`：omegaLimit_image_subset (t : τ) (ht : Tend
sto (· + t) f f) : ω f ϕ (ϕ t '' s) subseteq ω f ϕ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Flow.map_zero`：map_zero : ϕ 0 = id
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
the ω-limit of a forward image of `s` is the same as the ω-limit of `s`.
-/
theorem omegaLimit_image_eq (hf : ∀ t, Tendsto (· + t) f f) (t : τ) : ω f ϕ (ϕ t '' s) = ω f ϕ s :=
  Subset.antisymm (omegaLimit_image_subset _ _ _ _ (hf t)) <|
    calc
      ω f ϕ s = ω f ϕ (ϕ (-t) '' ϕ t '' s) := by simp [image_image, ← map_add]
      _ ⊆ ω f ϕ (ϕ t '' s) := omegaLimit_image_subset _ _ _ _ (hf _)
/-
**Flow.omegaLimit_omegaLimit** 是 Mathlib 中的一个定理，位于命名空间 `Flow`。
形式化陈述：omegaLimit_omegaLimit (hf : forall t, Tendsto (t + ·) f f) : ω f ϕ (ω f ϕ 
s) subseteq ω f ϕ s
参数：hf : forall t, Tendsto (t + ·) f f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `Set.inter_subset_inter_left`：inter_subset_inter_left {s t : Set α} (u : 
Set α) (H : s subseteq t) : s inter u subseteq t inter u
· 使用定理 `isInvariant_iff_image`：isInvariant_iff_image : IsInvariant ϕ s ↔ forall 
t, ϕ t '' s subseteq s
· 使用定理 `Flow.isInvariant_omegaLimit`：isInvariant_omegaLimit (hf : forall t, Tend
sto (t + ·) f f) : IsInvariant ϕ (ω f ϕ s)
· 使用定理 `omegaLimit_subset_closure_image2`：omegaLimit_subset_closure_image2 {u : 
Set τ} (hu : u in f) : ω f ϕ s subseteq closure (image2 ϕ u s)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `mem_closure_iff_nhds`：mem_closure_iff_nhds : x in closure s ↔ forall t i
n 𝓝 x, (t inter s).Nonempty
-/
theorem omegaLimit_omegaLimit (hf : ∀ t, Tendsto (t + ·) f f) : ω f ϕ (ω f ϕ s) ⊆ ω f ϕ s := by
  simp only [subset_def, mem_omegaLimit_iff_frequently₂, frequently_iff]
  intro _ h n hn u hu
  rcases mem_nhds_iff.mp hn with ⟨o, ho₁, ho₂, ho₃⟩
  rcases h o (IsOpen.mem_nhds ho₂ ho₃) hu with ⟨t, _ht₁, ht₂⟩
  have l₁ : (ω f ϕ s ∩ o).Nonempty :=
    ht₂.mono
      (inter_subset_inter_left _
        ((isInvariant_iff_image _ _).mp (isInvariant_omegaLimit _ _ _ hf) _))
  have l₂ : (closure (image2 ϕ u s) ∩ o).Nonempty :=
    l₁.mono fun b hb ↦ ⟨omegaLimit_subset_closure_image2 _ _ _ hu hb.1, hb.2⟩
  have l₃ : (o ∩ image2 ϕ u s).Nonempty := by
    rcases l₂ with ⟨b, hb₁, hb₂⟩
    exact mem_closure_iff_nhds.mp hb₁ o (IsOpen.mem_nhds ho₂ hb₂)
  rcases l₃ with ⟨ϕra, ho, ⟨_, hr, _, ha, hϕra⟩⟩
  exact ⟨_, hr, ϕra, ⟨_, ha, hϕra⟩, ho₁ ho⟩

end Flow

