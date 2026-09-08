/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Locally uniform convergence

We define a sequence of functions `Fₙ` to *converge locally uniformly* to a limiting function `f`
with respect to a filter `p`, spelled `TendstoLocallyUniformly F f p`, if for any `x ∈ s` and any
entourage of the diagonal `u`, there is a neighbourhood `v` of `x` such that `p`-eventually we have
`(f y, Fₙ y) ∈ u` for all `y ∈ v`.

It is important to note that this definition is somewhat non-standard; it is **not** in general
equivalent to "every point has a neighborhood on which the convergence is uniform", which is the
definition more commonly encountered in the literature. The reason is that in our definition the
neighborhood `v` of `x` can depend on the entourage `u`; so our condition is *a priori* weaker than
the usual one, although the two conditions are equivalent if the domain is locally compact. See
`tendstoLocallyUniformlyOn_of_forall_exists_nhds` for the one-way implication; the equivalence
assuming local compactness is part of `tendstoLocallyUniformlyOn_TFAE`.

We adopt this weaker condition because it is more general but appears to be sufficient for
the standard applications of locally-uniform convergence (in particular, for proving that a
locally-uniform limit of continuous functions is continuous).

We also define variants for locally uniform convergence on a subset, called
`TendstoLocallyUniformlyOn F f p s`.

## Tags

Uniform limit, uniform convergence, tends uniformly to
-/

@[expose] public section

noncomputable section

open Topology Uniformity Filter Set Uniform

variable {α β γ ι : Type*} [TopologicalSpace α] [UniformSpace β]
variable {F : ι → α → β} {f : α → β} {s s' : Set α} {x : α} {p : Filter ι}

/-- A sequence of functions `Fₙ` converges locally uniformly on a set `s` to a limiting function
`f` with respect to a filter `p` if, for any entourage of the diagonal `u`, for any `x ∈ s`, one
has `p`-eventually `(f y, Fₙ y) ∈ u` for all `y` in a neighborhood of `x` in `s`. -/
/-
**TendstoLocallyUniformlyOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：TendstoLocallyUniformlyOn (F : ι -> α -> β) (f : α -> β) (p : Filter ι) (s
 : Set α)
参数：F : ι -> α -> β；f : α -> β；p : Filter ι；s : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sequence of functions `Fₙ` converges locally uniformly on a set `s` to a limit
ing function
`f` with respect to a filter `p` if, for any entourage of the diagonal `u`, for 
any `x ∈ s`, one
has `p`-eventually `(f y, Fₙ y) ∈ u` for all `y` in a neighborhood of `x` in `s`
.
-/
def TendstoLocallyUniformlyOn (F : ι → α → β) (f : α → β) (p : Filter ι) (s : Set α) :=
  ∀ u ∈ 𝓤 β, ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, ∀ᶠ n in p, ∀ y ∈ t, (f y, F n y) ∈ u

/-- A sequence of functions `Fₙ` converges locally uniformly to a limiting function `f` with respect
to a filter `p` if, for any entourage of the diagonal `u`, for any `x`, one has `p`-eventually
`(f y, Fₙ y) ∈ u` for all `y` in a neighborhood of `x`. -/
/-
**TendstoLocallyUniformly** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：TendstoLocallyUniformly (F : ι -> α -> β) (f : α -> β) (p : Filter ι)
参数：F : ι -> α -> β；f : α -> β；p : Filter ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sequence of functions `Fₙ` converges locally uniformly to a limiting function 
`f` with respect
to a filter `p` if, for any entourage of the diagonal `u`, for any `x`, one has 
`p`-eventually
`(f y, Fₙ y) ∈ u` for all `y` in a neighborhood of `x`.
-/
def TendstoLocallyUniformly (F : ι → α → β) (f : α → β) (p : Filter ι) :=
  ∀ u ∈ 𝓤 β, ∀ x : α, ∃ t ∈ 𝓝 x, ∀ᶠ n in p, ∀ y ∈ t, (f y, F n y) ∈ u
/-
**tendstoLocallyUniformlyOn_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendstoLocallyUniformlyOn_univ : TendstoLocallyUniformlyOn F f p univ ↔ Te
ndstoLocallyUniformly F f p
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
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendstoLocallyUniformlyOn_univ :
    TendstoLocallyUniformlyOn F f p univ ↔ TendstoLocallyUniformly F f p := by
  simp [TendstoLocallyUniformlyOn, TendstoLocallyUniformly, nhdsWithin_univ]
/-
**tendstoLocallyUniformlyOn_iff_forall_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendstoLocallyUniformlyOn_iff_forall_tendsto : TendstoLocallyUniformlyOn F
 f p s ↔ forall x in s, Tendsto (fun y : ι × α => (f y.2, F y.1 y.2)) (p ×ˢ 𝓝[s]
 x) (𝓤 β)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `forall₂_comm`：forall₂_comm {ι₁ ι₂ : Sort*} {κ₁ : ι₁ -> Sort*} {κ₂ : ι₂ -
> Sort*} {p : forall i₁, κ₁ i₁ -> forall i₂, κ₂ i₂ -> Prop} : (forall i₁ j₁ i₂ j
₂,…
· 使用定理 `forall₄_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → 
Sort u_3} {δ : (a : α) → (b : β a) → γ a b → Sort u_4}   {p q : (a : α) → (b : β
 a)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendstoLocallyUniformlyOn_iff_forall_tendsto :
    TendstoLocallyUniformlyOn F f p s ↔
      ∀ x ∈ s, Tendsto (fun y : ι × α => (f y.2, F y.1 y.2)) (p ×ˢ 𝓝[s] x) (𝓤 β) :=
  forall₂_comm.trans <| forall₄_congr fun _ _ _ _ => by
    simp_rw [mem_map, mem_prod_iff_right, mem_preimage]

nonrec theorem IsOpen.tendstoLocallyUniformlyOn_iff_forall_tendsto (hs : IsOpen s) :
    TendstoLocallyUniformlyOn F f p s ↔
      ∀ x ∈ s, Tendsto (fun y : ι × α => (f y.2, F y.1 y.2)) (p ×ˢ 𝓝 x) (𝓤 β) :=
  tendstoLocallyUniformlyOn_iff_forall_tendsto.trans <| forall₂_congr fun x hx => by
    rw [hs.nhdsWithin_eq hx]
/-
**tendstoLocallyUniformly_iff_forall_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendstoLocallyUniformly_iff_forall_tendsto : TendstoLocallyUniformly F f p
 ↔ forall x, Tendsto (fun y : ι × α => (f y.2, F y.1 y.2)) (p ×ˢ 𝓝 x) (𝓤 β)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOpen.tendstoLocallyUniformlyOn_iff_forall_tendsto`：∀ {α : Type u_1} {β
 : Type u_2} {ι : Type u_4} [inst : TopologicalSpace α] [inst_1 : UniformSpace β
] {F : ι → α → β}   {f : α → β} {s : Set …
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendstoLocallyUniformly_iff_forall_tendsto :
    TendstoLocallyUniformly F f p ↔
      ∀ x, Tendsto (fun y : ι × α => (f y.2, F y.1 y.2)) (p ×ˢ 𝓝 x) (𝓤 β) := by
  simp [← tendstoLocallyUniformlyOn_univ, isOpen_univ.tendstoLocallyUniformlyOn_iff_forall_tendsto]
/-
**tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe** 是 Mathlib 中的一
个定理，位于命名空间 ``。
形式化陈述：tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe : TendstoLo
callyUniformlyOn F f p s ↔ TendstoLocallyUniformly (fun i (x : s) => F i x) (f ∘
 (↑)) p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.prod_map_right`：prod_map_right (f : β -> γ) (F : Filter α) (G : F
ilter β) : F ×ˢ map f G = map (Prod.map id f) (F ×ˢ G)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe :
    TendstoLocallyUniformlyOn F f p s ↔
      TendstoLocallyUniformly (fun i (x : s) => F i x) (f ∘ (↑)) p := by
  simp only [tendstoLocallyUniformly_iff_forall_tendsto, Subtype.forall', tendsto_map'_iff,
    tendstoLocallyUniformlyOn_iff_forall_tendsto, ← map_nhds_subtype_val, prod_map_right]; rfl
/-
**TendstoUniformlyOn.tendstoLocallyUniformlyOn** 是 Mathlib 中的一个定理，位于命名空间 `Tendst
oUniformlyOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Type u_4} [inst : TopologicalSpace α]
 [inst_1 : UniformSpace β] {F : ι → α → β}   {f : α → β} {s : Set α} {p : Filter
 ι}, TendstoUniformlyOn F f p s → TendstoLocallyUniformlyOn F f p s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
-/
protected theorem TendstoUniformlyOn.tendstoLocallyUniformlyOn (h : TendstoUniformlyOn F f p s) :
    TendstoLocallyUniformlyOn F f p s := fun u hu _ _ =>
  ⟨s, self_mem_nhdsWithin, by simpa using h u hu⟩
/-
**TendstoUniformly.tendstoLocallyUniformly** 是 Mathlib 中的一个定理，位于命名空间 `TendstoUni
formly`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Type u_4} [inst : TopologicalSpace α]
 [inst_1 : UniformSpace β] {F : ι → α → β}   {f : α → β} {p : Filter ι}, Tendsto
Uniformly F f p → TendstoLocallyUniformly F f p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
protected theorem TendstoUniformly.tendstoLocallyUniformly (h : TendstoUniformly F f p) :
    TendstoLocallyUniformly F f p := fun u hu _ => ⟨univ, univ_mem, by simpa using h u hu⟩
/-
**TendstoLocallyUniformlyOn.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoLocallyUniformlyOn.mono (h : TendstoLocallyUniformlyOn F f p s) (h'
 : s' subseteq s) : TendstoLocallyUniformlyOn F f p s'
参数：h : TendstoLocallyUniformlyOn F f p s；h' : s' subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
-/
theorem TendstoLocallyUniformlyOn.mono (h : TendstoLocallyUniformlyOn F f p s) (h' : s' ⊆ s) :
    TendstoLocallyUniformlyOn F f p s' := by
  intro u hu x hx
  rcases h u hu x (h' hx) with ⟨t, ht, H⟩
  exact ⟨t, nhdsWithin_mono x h' ht, H.mono fun n => id⟩
/-
**tendstoLocallyUniformlyOn_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendstoLocallyUniformlyOn_iUnion {ι' : Sort*} {S : ι' -> Set α} (hS : fora
ll i, IsOpen (S i)) (h : forall i, TendstoLocallyUniformlyOn F f p (S i)) : Tend
stoLocallyUniformlyOn F f p (⋃ i, S i)
参数：hS : forall i, IsOpen (S i)；h : forall i, TendstoLocallyUniformlyOn F f p (S 
i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsOpen.tendstoLocallyUniformlyOn_iff_forall_tendsto`：∀ {α : Type u_1} {β
 : Type u_2} {ι : Type u_4} [inst : TopologicalSpace α] [inst_1 : UniformSpace β
] {F : ι → α → β}   {f : α → β} {s : Set …
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
-/
theorem tendstoLocallyUniformlyOn_iUnion {ι' : Sort*} {S : ι' → Set α} (hS : ∀ i, IsOpen (S i))
    (h : ∀ i, TendstoLocallyUniformlyOn F f p (S i)) :
    TendstoLocallyUniformlyOn F f p (⋃ i, S i) :=
  (isOpen_iUnion hS).tendstoLocallyUniformlyOn_iff_forall_tendsto.2 fun _x hx =>
    let ⟨i, hi⟩ := mem_iUnion.1 hx
    (hS i).tendstoLocallyUniformlyOn_iff_forall_tendsto.1 (h i) _ hi
/-
**tendstoLocallyUniformlyOn_biUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendstoLocallyUniformlyOn_biUnion {s : Set γ} {S : γ -> Set α} (hS : foral
l i in s, IsOpen (S i)) (h : forall i in s, TendstoLocallyUniformlyOn F f p (S i
)) : TendstoLocallyUniformlyOn F f p (⋃ i in s, S i)
参数：hS : forall i in s, IsOpen (S i)；h : forall i in s, TendstoLocallyUniformlyOn
 F f p (S i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendstoLocallyUniformlyOn_iUnion`：tendstoLocallyUniformlyOn_iUnion {ι' :
 Sort*} {S : ι' -> Set α} (hS : forall i, IsOpen (S i)) (h : forall i, TendstoLo
callyUniformlyOn F f p…
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
-/
theorem tendstoLocallyUniformlyOn_biUnion {s : Set γ} {S : γ → Set α} (hS : ∀ i ∈ s, IsOpen (S i))
    (h : ∀ i ∈ s, TendstoLocallyUniformlyOn F f p (S i)) :
    TendstoLocallyUniformlyOn F f p (⋃ i ∈ s, S i) :=
  tendstoLocallyUniformlyOn_iUnion (fun i => isOpen_iUnion (hS i))
    fun i ↦ tendstoLocallyUniformlyOn_iUnion (hS i) (h i)
/-
**tendstoLocallyUniformlyOn_sUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendstoLocallyUniformlyOn_sUnion (S : Set (Set α)) (hS : forall s in S, Is
Open s) (h : forall s in S, TendstoLocallyUniformlyOn F f p s) : TendstoLocallyU
niformlyOn F f p (⋃₀ S)
参数：S : Set (Set α)；hS : forall s in S, IsOpen s；h : forall s in S, TendstoLocall
yUniformlyOn F f p s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_biUnion`：sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i
 : Set α) (_ : i in s), i
· 使用定理 `tendstoLocallyUniformlyOn_biUnion`：tendstoLocallyUniformlyOn_biUnion {s 
: Set γ} {S : γ -> Set α} (hS : forall i in s, IsOpen (S i)) (h : forall i in s,
 TendstoLocallyUniforml…
-/
theorem tendstoLocallyUniformlyOn_sUnion (S : Set (Set α)) (hS : ∀ s ∈ S, IsOpen s)
    (h : ∀ s ∈ S, TendstoLocallyUniformlyOn F f p s) : TendstoLocallyUniformlyOn F f p (⋃₀ S) := by
  rw [sUnion_eq_biUnion]
  exact tendstoLocallyUniformlyOn_biUnion hS h
/-
**TendstoLocallyUniformlyOn.union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoLocallyUniformlyOn.union (hs₁ : IsOpen s) (hs₂ : IsOpen s') (h₁ : T
endstoLocallyUniformlyOn F f p s) (h₂ : TendstoLocallyUniformlyOn F f p s') : Te
ndstoLocallyUniformlyOn F f p (s union s')
参数：hs₁ : IsOpen s；hs₂ : IsOpen s'；h₁ : TendstoLocallyUniformlyOn F f p s；h₂ : Te
ndstoLocallyUniformlyOn F f p s'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sUnion_pair`：sUnion_pair (s t : Set α) : ⋃₀ {s, t} = s union t
· 使用定理 `tendstoLocallyUniformlyOn_sUnion`：tendstoLocallyUniformlyOn_sUnion (S : 
Set (Set α)) (hS : forall s in S, IsOpen s) (h : forall s in S, TendstoLocallyUn
iformlyOn F f p s) : T…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem TendstoLocallyUniformlyOn.union (hs₁ : IsOpen s) (hs₂ : IsOpen s')
    (h₁ : TendstoLocallyUniformlyOn F f p s) (h₂ : TendstoLocallyUniformlyOn F f p s') :
    TendstoLocallyUniformlyOn F f p (s ∪ s') := by
  rw [← sUnion_pair]
  refine tendstoLocallyUniformlyOn_sUnion _ ?_ ?_ <;> simp [*]
/-
**TendstoLocallyUniformly.tendstoLocallyUniformlyOn** 是 Mathlib 中的一个定理，位于命名空间 `T
endstoLocallyUniformly`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Type u_4} [inst : TopologicalSpace α]
 [inst_1 : UniformSpace β] {F : ι → α → β}   {f : α → β} {s : Set α} {p : Filter
 ι}, TendstoLocallyUniformly F f p → TendstoLocallyUniformlyOn F f p s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TendstoLocallyUniformlyOn.mono`：TendstoLocallyUniformlyOn.mono (h : Tend
stoLocallyUniformlyOn F f p s) (h' : s' subseteq s) : TendstoLocallyUniformlyOn 
F f p s'
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendstoLocallyUniformlyOn_univ`：tendstoLocallyUniformlyOn_univ : Tendsto
LocallyUniformlyOn F f p univ ↔ TendstoLocallyUniformly F f p
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
protected theorem TendstoLocallyUniformly.tendstoLocallyUniformlyOn
    (h : TendstoLocallyUniformly F f p) : TendstoLocallyUniformlyOn F f p s :=
  (tendstoLocallyUniformlyOn_univ.mpr h).mono (subset_univ _)

/-- On a compact space, locally uniform convergence is just uniform convergence. -/
/-
**tendstoLocallyUniformly_iff_tendstoUniformly_of_compactSpace** 是 Mathlib 中的一个定
理，位于命名空间 ``。
形式化陈述：tendstoLocallyUniformly_iff_tendstoUniformly_of_compactSpace [CompactSpace
 α] : TendstoLocallyUniformly F f p ↔ TendstoUniformly F f p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.elim_nhds_subcover'`：IsCompact.elim_nhds_subcover' (hs : IsCom
pact s) (U : forall x in s, Set X) (hU : forall x (hx : x in s), U x ‹x in s› in
 𝓝 x) : exists t : …
· 使用定理 `isCompact_univ`：isCompact_univ [h : CompactSpace X] : IsCompact (univ : 
Set X)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.eventually_all`：eventually_all {ι : Sort*} [Finite ι] {l} {p : ι 
-> α -> Prop} : (forallᶠ x in l, forall i, p i x) ↔ forall i, forallᶠ x in l, p 
i x
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `TendstoUniformly.tendstoLocallyUniformly`：∀ {α : Type u_1} {β : Type u_2
} {ι : Type u_4} [inst : TopologicalSpace α] [inst_1 : UniformSpace β] {F : ι → 
α → β}   {f : α → β} {p : Filt…

--- 原说明 ---
On a compact space, locally uniform convergence is just uniform convergence.
-/
theorem tendstoLocallyUniformly_iff_tendstoUniformly_of_compactSpace [CompactSpace α] :
    TendstoLocallyUniformly F f p ↔ TendstoUniformly F f p := by
  refine ⟨fun h V hV => ?_, TendstoUniformly.tendstoLocallyUniformly⟩
  choose U hU using h V hV
  obtain ⟨t, ht⟩ := isCompact_univ.elim_nhds_subcover' (fun k _ => U k) fun k _ => (hU k).1
  replace hU := fun x : t => (hU x).2
  rw [← eventually_all] at hU
  refine hU.mono fun i hi x => ?_
  specialize ht (mem_univ x)
  simp only [exists_prop, mem_iUnion, SetCoe.exists, exists_and_right] at ht
  obtain ⟨y, ⟨hy₁, hy₂⟩, hy₃⟩ := ht
  exact hi ⟨⟨y, hy₁⟩, hy₂⟩ x hy₃

/-- For a compact set `s`, locally uniform convergence on `s` is just uniform convergence on `s`. -/
/-
**tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact** 是 Mathlib 中的一个定理
，位于命名空间 ``。
形式化陈述：tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (hs : IsCompac
t s) : TendstoLocallyUniformlyOn F f p s ↔ TendstoUniformlyOn F f p s
参数：hs : IsCompact s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tendstoUniformlyOn_iff_tendstoUniformly_comp_coe`：tendstoUniformlyOn_iff
_tendstoUniformly_comp_coe : TendstoUniformlyOn F f p s ↔ TendstoUniformly (fun 
i (x : s) => F i x) (f ∘ (↑)) p
· 使用定理 `tendstoLocallyUniformly_iff_tendstoUniformly_of_compactSpace`：tendstoLoc
allyUniformly_iff_tendstoUniformly_of_compactSpace [CompactSpace α] : TendstoLoc
allyUniformly F f p ↔ TendstoUniformly F f p
· 使用定理 `tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe`：tendstoL
ocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe : TendstoLocallyUniformly
On F f p s ↔ TendstoLocallyUniformly (fun i (x : s) …
· 使用定理 `TendstoUniformlyOn.tendstoLocallyUniformlyOn`：∀ {α : Type u_1} {β : Type
 u_2} {ι : Type u_4} [inst : TopologicalSpace α] [inst_1 : UniformSpace β] {F : 
ι → α → β}   {f : α → β} {s : Set …

--- 原说明 ---
For a compact set `s`, locally uniform convergence on `s` is just uniform conver
gence on `s`.
-/
theorem tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (hs : IsCompact s) :
    TendstoLocallyUniformlyOn F f p s ↔ TendstoUniformlyOn F f p s := by
  have : CompactSpace s := isCompact_iff_compactSpace.mp hs
  refine ⟨fun h => ?_, TendstoUniformlyOn.tendstoLocallyUniformlyOn⟩
  rwa [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe,
    tendstoLocallyUniformly_iff_tendstoUniformly_of_compactSpace, ←
    tendstoUniformlyOn_iff_tendstoUniformly_comp_coe] at h

/-!
### Composition
-/

section Comp

/-
**TendstoLocallyUniformlyOn.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoLocallyUniformlyOn.comp [TopologicalSpace γ] {t : Set γ} (h : Tends
toLocallyUniformlyOn F f p s) (g : γ -> α) (hg : MapsTo g t s) (cg : ContinuousO
n g t) : TendstoLocallyUniformlyOn (fun n => F n ∘ g) (f ∘ g) p t
参数：h : TendstoLocallyUniformlyOn F f p s；g : γ -> α；hg : MapsTo g t s；cg : Conti
nuousOn g t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.preimage_mem_nhdsWithin'`：ContinuousWithinAt.preimage
_mem_nhdsWithin' {t : Set β} (h : ContinuousWithinAt f s x) (ht : t in 𝓝[f '' s]
 f x) : f ⁻¹' t in 𝓝[s] x
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `Set.MapsTo.image_subset`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t 
: Set β} {f : α → β}, Set.MapsTo f s t → f '' s ⊆ t
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
-/
theorem TendstoLocallyUniformlyOn.comp [TopologicalSpace γ] {t : Set γ}
    (h : TendstoLocallyUniformlyOn F f p s) (g : γ → α) (hg : MapsTo g t s)
    (cg : ContinuousOn g t) : TendstoLocallyUniformlyOn (fun n => F n ∘ g) (f ∘ g) p t := by
  intro u hu x hx
  rcases h u hu (g x) (hg hx) with ⟨a, ha, H⟩
  have : g ⁻¹' a ∈ 𝓝[t] x :=
    (cg x hx).preimage_mem_nhdsWithin' (nhdsWithin_mono (g x) hg.image_subset ha)
  exact ⟨g ⁻¹' a, this, H.mono fun n hn y hy => hn _ hy⟩
/-
**TendstoLocallyUniformly.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoLocallyUniformly.comp [TopologicalSpace γ] (h : TendstoLocallyUnifo
rmly F f p) (g : γ -> α) (cg : Continuous g) : TendstoLocallyUniformly (fun n =>
 F n ∘ g) (f ∘ g) p
参数：h : TendstoLocallyUniformly F f p；g : γ -> α；cg : Continuous g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tendstoLocallyUniformlyOn_univ`：tendstoLocallyUniformlyOn_univ : Tendsto
LocallyUniformlyOn F f p univ ↔ TendstoLocallyUniformly F f p
· 使用定理 `TendstoLocallyUniformlyOn.comp`：TendstoLocallyUniformlyOn.comp [Topologi
calSpace γ] {t : Set γ} (h : TendstoLocallyUniformlyOn F f p s) (g : γ -> α) (hg
 : MapsTo g t s) (cg…
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ
· 使用定理 `continuousOn_univ`：continuousOn_univ {f : α -> β} : ContinuousOn f univ 
↔ Continuous f
-/
theorem TendstoLocallyUniformly.comp [TopologicalSpace γ] (h : TendstoLocallyUniformly F f p)
    (g : γ → α) (cg : Continuous g) : TendstoLocallyUniformly (fun n => F n ∘ g) (f ∘ g) p := by
  rw [← tendstoLocallyUniformlyOn_univ] at h ⊢
  rw [← continuousOn_univ] at cg
  exact h.comp _ (mapsTo_univ _ _) cg

variable [UniformSpace γ] {g : β → γ}
/-
**UniformContinuousOn.comp_tendstoLocallyUniformlyOn** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：UniformContinuousOn.comp_tendstoLocallyUniformlyOn {t : Set β} (hg : Unifo
rmContinuousOn g t) (hf : TendstoLocallyUniformlyOn F f p s) (hfs : MapsTo f s t
) (hFs : forallᶠ n in p, MapsTo (F n) s t) : TendstoLocallyUniformlyOn (g ∘ F ·)
 (g ∘ f) p s
参数：hg : UniformContinuousOn g t；hf : TendstoLocallyUniformlyOn F f p s；hfs : Map
sTo f s t；hFs : forallᶠ n in p, MapsTo (F n) s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendstoLocallyUniformlyOn_iff_forall_tendsto`：tendstoLocallyUniformlyOn_
iff_forall_tendsto : TendstoLocallyUniformlyOn F f p s ↔ forall x in s, Tendsto 
(fun y : ι × α => (f y.2, F y.1 y.…
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_inf`：tendsto_inf {f : α -> β} {x : Filter α} {y₁ y₂ : Fil
ter β} : Tendsto f x (y₁ ⊓ y₂) ↔ Tendsto f x y₁ ∧ Tendsto f x y₂
· 使用定理 `Filter.tendsto_principal`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l
 : Filter α} {s : Set β},   Filter.Tendsto f l (Filter.principal s) ↔ ∀ᶠ (a : α)
 in l, f a ∈ s
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Eventually.prod_mk`：∀ {α : Type u_1} {β : Type u_2} {la : Filter 
α} {pa : α → Prop},   (∀ᶠ (x : α) in la, pa x) →     ∀ {lb : Filter β} {pb : β →
 Prop}, (∀ᶠ (y …
· 使用定理 `eventually_mem_nhdsWithin`：eventually_mem_nhdsWithin {a : α} {s : Set α}
 : forallᶠ x in 𝓝[s] a, x in s
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem UniformContinuousOn.comp_tendstoLocallyUniformlyOn {t : Set β}
    (hg : UniformContinuousOn g t) (hf : TendstoLocallyUniformlyOn F f p s)
    (hfs : MapsTo f s t) (hFs : ∀ᶠ n in p, MapsTo (F n) s t) :
    TendstoLocallyUniformlyOn (g ∘ F ·) (g ∘ f) p s := by
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto] at hf ⊢
  refine fun x hx ↦ Tendsto.comp hg (tendsto_inf.mpr ⟨hf x hx, tendsto_principal.mpr ?_⟩)
  filter_upwards [hFs.prod_mk eventually_mem_nhdsWithin] with y hy using ⟨hfs hy.2, hy.1 hy.2⟩
/-
**UniformContinuousOn.comp_tendstoLocallyUniformly** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformContinuousOn.comp_tendstoLocallyUniformly {t : Set β} (hg : Uniform
ContinuousOn g t) (hf : TendstoLocallyUniformly F f p) (hfs : forall x, f x in t
) (hFs : forallᶠ n in p, forall x, F n x in t) : TendstoLocallyUniformly (g ∘ F 
·) (g ∘ f) p
参数：hg : UniformContinuousOn g t；hf : TendstoLocallyUniformly F f p；hfs : forall 
x, f x in t；hFs : forallᶠ n in p, forall x, F n x in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tendstoLocallyUniformlyOn_univ`：tendstoLocallyUniformlyOn_univ : Tendsto
LocallyUniformlyOn F f p univ ↔ TendstoLocallyUniformly F f p
· 使用定理 `UniformContinuousOn.comp_tendstoLocallyUniformlyOn`：UniformContinuousOn.
comp_tendstoLocallyUniformlyOn {t : Set β} (hg : UniformContinuousOn g t) (hf : 
TendstoLocallyUniformlyOn F f p s) (hfs …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem UniformContinuousOn.comp_tendstoLocallyUniformly {t : Set β}
    (hg : UniformContinuousOn g t) (hf : TendstoLocallyUniformly F f p)
    (hfs : ∀ x, f x ∈ t) (hFs : ∀ᶠ n in p, ∀ x, F n x ∈ t) :
    TendstoLocallyUniformly (g ∘ F ·) (g ∘ f) p := by
  rw [← tendstoLocallyUniformlyOn_univ] at *
  apply hg.comp_tendstoLocallyUniformlyOn hf <;> simpa [MapsTo]
/-
**UniformContinuous.comp_tendstoLocallyUniformlyOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformContinuous.comp_tendstoLocallyUniformlyOn (hg : UniformContinuous g
) (hf : TendstoLocallyUniformlyOn F f p s) : TendstoLocallyUniformlyOn (g ∘ F ·)
 (g ∘ f) p s
参数：hg : UniformContinuous g；hf : TendstoLocallyUniformlyOn F f p s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousOn.comp_tendstoLocallyUniformlyOn`：UniformContinuousOn.
comp_tendstoLocallyUniformlyOn {t : Set β} (hg : UniformContinuousOn g t) (hf : 
TendstoLocallyUniformlyOn F f p s) (hfs …
· 使用引理 `UniformContinuous.uniformContinuousOn`：UniformContinuous.uniformContinuo
usOn (hf : UniformContinuous f) : UniformContinuousOn f s
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
theorem UniformContinuous.comp_tendstoLocallyUniformlyOn (hg : UniformContinuous g)
    (hf : TendstoLocallyUniformlyOn F f p s) :
    TendstoLocallyUniformlyOn (g ∘ F ·) (g ∘ f) p s :=
  hg.uniformContinuousOn.comp_tendstoLocallyUniformlyOn hf (mapsTo_univ _ _) <| .of_forall fun _ ↦
    mapsTo_univ _ _
/-
**UniformContinuous.comp_tendstoLocallyUniformly** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformContinuous.comp_tendstoLocallyUniformly (hg : UniformContinuous g) 
(hf : TendstoLocallyUniformly F f p) : TendstoLocallyUniformly (g ∘ F ·) (g ∘ f)
 p
参数：hg : UniformContinuous g；hf : TendstoLocallyUniformly F f p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuousOn.comp_tendstoLocallyUniformly`：UniformContinuousOn.co
mp_tendstoLocallyUniformly {t : Set β} (hg : UniformContinuousOn g t) (hf : Tend
stoLocallyUniformly F f p) (hfs : fora…
· 使用引理 `UniformContinuous.uniformContinuousOn`：UniformContinuous.uniformContinuo
usOn (hf : UniformContinuous f) : UniformContinuousOn f s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem UniformContinuous.comp_tendstoLocallyUniformly (hg : UniformContinuous g)
    (hf : TendstoLocallyUniformly F f p) :
    TendstoLocallyUniformly (g ∘ F ·) (g ∘ f) p :=
  (hg.uniformContinuousOn (s := univ)).comp_tendstoLocallyUniformly hf (by simp) (by simp)

end Comp

/-
**TendstoLocallyUniformlyOn.prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoLocallyUniformlyOn.prodMk [UniformSpace γ] {G : ι -> α -> γ} {g : α
 -> γ} (hF : TendstoLocallyUniformlyOn F f p s) (hG : TendstoLocallyUniformlyOn 
G g p s) : TendstoLocallyUniformlyOn (fun n x => (F n x, G n x)) (fun x => (f x,
 g x)) p s
参数：hF : TendstoLocallyUniformlyOn F f p s；hG : TendstoLocallyUniformlyOn G g p s
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendstoLocallyUniformlyOn_iff_forall_tendsto`：tendstoLocallyUniformlyOn_
iff_forall_tendsto : TendstoLocallyUniformlyOn F f p s ↔ forall x in s, Tendsto 
(fun y : ι × α => (f y.2, F y.1 y.…
· 使用定理 `uniformity_prod_eq_comap_prod`：uniformity_prod_eq_comap_prod [UniformSpa
ce α] [UniformSpace β] : 𝓤 (α × β) = comap (fun p : (α × β) × α × β => ((p.1.1, 
p.2.1), (p.1.2, p.2…
· 使用定理 `Filter.tendsto_comap_iff`：tendsto_comap_iff {f : α -> β} {g : β -> γ} {a
 : Filter α} {c : Filter γ} : Tendsto f a (c.comap g) ↔ Tendsto (g ∘ f) a c
· 使用定理 `Filter.Tendsto.prodMk`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f
 : Filter α} {g : Filter β} {h : Filter γ} {m₁ : α → β} {m₂ : α → γ},   Filter.T
endsto m₁ f…
-/
theorem TendstoLocallyUniformlyOn.prodMk [UniformSpace γ] {G : ι → α → γ} {g : α → γ}
    (hF : TendstoLocallyUniformlyOn F f p s) (hG : TendstoLocallyUniformlyOn G g p s) :
    TendstoLocallyUniformlyOn (fun n x ↦ (F n x, G n x)) (fun x ↦ (f x, g x)) p s := by
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto] at *
  intro x hx
  rw [uniformity_prod_eq_comap_prod, tendsto_comap_iff]
  exact (hF x hx).prodMk (hG x hx)
/-
**TendstoLocallyUniformlyOn.piProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoLocallyUniformlyOn.piProd [UniformSpace γ] {G : ι -> α -> γ} {g : α
 -> γ} (hF : TendstoLocallyUniformlyOn F f p s) (hG : TendstoLocallyUniformlyOn 
G g p s) : TendstoLocallyUniformlyOn (fun n => Function.prod (F n) (G n)) (Funct
ion.prod f g) p s
参数：hF : TendstoLocallyUniformlyOn F f p s；hG : TendstoLocallyUniformlyOn G g p s
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TendstoLocallyUniformlyOn.prodMk`：TendstoLocallyUniformlyOn.prodMk [Unif
ormSpace γ] {G : ι -> α -> γ} {g : α -> γ} (hF : TendstoLocallyUniformlyOn F f p
 s) (hG : TendstoLocal…
-/
theorem TendstoLocallyUniformlyOn.piProd [UniformSpace γ] {G : ι → α → γ} {g : α → γ}
    (hF : TendstoLocallyUniformlyOn F f p s) (hG : TendstoLocallyUniformlyOn G g p s) :
    TendstoLocallyUniformlyOn (fun n ↦ Function.prod (F n) (G n)) (Function.prod f g) p s :=
  hF.prodMk hG
/-
**TendstoLocallyUniformly.prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoLocallyUniformly.prodMk [UniformSpace γ] {G : ι -> α -> γ} {g : α -
> γ} (hF : TendstoLocallyUniformly F f p) (hG : TendstoLocallyUniformly G g p) :
 TendstoLocallyUniformly (fun n x => (F n x, G n x)) (fun x => (f x, g x)) p
参数：hF : TendstoLocallyUniformly F f p；hG : TendstoLocallyUniformly G g p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tendstoLocallyUniformlyOn_univ`：tendstoLocallyUniformlyOn_univ : Tendsto
LocallyUniformlyOn F f p univ ↔ TendstoLocallyUniformly F f p
· 使用定理 `TendstoLocallyUniformlyOn.prodMk`：TendstoLocallyUniformlyOn.prodMk [Unif
ormSpace γ] {G : ι -> α -> γ} {g : α -> γ} (hF : TendstoLocallyUniformlyOn F f p
 s) (hG : TendstoLocal…
-/
theorem TendstoLocallyUniformly.prodMk [UniformSpace γ] {G : ι → α → γ} {g : α → γ}
    (hF : TendstoLocallyUniformly F f p) (hG : TendstoLocallyUniformly G g p) :
    TendstoLocallyUniformly (fun n x ↦ (F n x, G n x)) (fun x ↦ (f x, g x)) p := by
  rw [← tendstoLocallyUniformlyOn_univ] at *
  exact hF.prodMk hG
/-
**TendstoLocallyUniformly.piProd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoLocallyUniformly.piProd [UniformSpace γ] {G : ι -> α -> γ} {g : α -
> γ} (hF : TendstoLocallyUniformly F f p) (hG : TendstoLocallyUniformly G g p) :
 TendstoLocallyUniformly (fun n => Function.prod (F n) (G n)) (Function.prod f g
) p
参数：hF : TendstoLocallyUniformly F f p；hG : TendstoLocallyUniformly G g p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TendstoLocallyUniformly.prodMk`：TendstoLocallyUniformly.prodMk [UniformS
pace γ] {G : ι -> α -> γ} {g : α -> γ} (hF : TendstoLocallyUniformly F f p) (hG 
: TendstoLocallyUnif…
-/
theorem TendstoLocallyUniformly.piProd [UniformSpace γ] {G : ι → α → γ} {g : α → γ}
    (hF : TendstoLocallyUniformly F f p) (hG : TendstoLocallyUniformly G g p) :
    TendstoLocallyUniformly (fun n ↦ Function.prod (F n) (G n)) (Function.prod f g) p :=
  hF.prodMk hG

/-- If every `x ∈ s` has a neighbourhood within `s` on which `F i` tends uniformly to `f`, then
`F i` tends locally uniformly on `s` to `f`.

Note this is **not** a tautology, since our definition of `TendstoLocallyUniformlyOn` is slightly
more general (although the conditions are equivalent if `β` is locally compact and `s` is open,
see `tendstoLocallyUniformlyOn_TFAE`). -/
/-
**tendstoLocallyUniformlyOn_of_forall_exists_nhds** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendstoLocallyUniformlyOn_of_forall_exists_nhds (h : forall x in s, exists
 t in 𝓝[s] x, TendstoUniformlyOn F f p t) : TendstoLocallyUniformlyOn F f p s
参数：h : forall x in s, exists t in 𝓝[s] x, TendstoUniformlyOn F f p t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendstoLocallyUniformlyOn_iff_forall_tendsto`：tendstoLocallyUniformlyOn_
iff_forall_tendsto : TendstoLocallyUniformlyOn F f p s ↔ forall x in s, Tendsto 
(fun y : ι × α => (f y.2, F y.1 y.…
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendstoUniformlyOn_iff_tendsto`：tendstoUniformlyOn_iff_tendsto : Tendsto
UniformlyOn F f p s ↔ Tendsto (fun q : ι × α => (f q.2, F q.1 q.2)) (p ×ˢ 𝓟 s) (
𝓤 β)
· 使用定理 `Filter.prod_mono_right`：prod_mono_right (f : Filter α) {g₁ g₂ : Filter β
} (hf : g₁ <= g₂) : f ×ˢ g₁ <= f ×ˢ g₂
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f

--- 原说明 ---
If every `x ∈ s` has a neighbourhood within `s` on which `F i` tends uniformly t
o `f`, then
`F i` tends locally uniformly on `s` to `f`.

Note this is **not** a tautology, since our definition of `TendstoLocallyUniform
lyOn` is slightly
more general (although the conditions are equivalent if `β` is locally compact a
nd `s` is open,
see `tendstoLocallyUniformlyOn_TFAE`).
-/
lemma tendstoLocallyUniformlyOn_of_forall_exists_nhds
    (h : ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, TendstoUniformlyOn F f p t) :
    TendstoLocallyUniformlyOn F f p s := by
  refine tendstoLocallyUniformlyOn_iff_forall_tendsto.mpr fun x hx ↦ ?_
  obtain ⟨t, ht, htr⟩ := h x hx
  rw [tendstoUniformlyOn_iff_tendsto] at htr
  exact htr.mono_left <| prod_mono_right _ <| le_principal_iff.mpr ht

/-- If every `x` has a neighbourhood on which `F i` tends uniformly to `f`, then `F i` tends
locally uniformly to `f`. (Special case of `tendstoLocallyUniformlyOn_of_forall_exists_nhds`
where `s = univ`.) -/
/-
**tendstoLocallyUniformly_of_forall_exists_nhds** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendstoLocallyUniformly_of_forall_exists_nhds (h : forall x, exists t in 𝓝
 x, TendstoUniformlyOn F f p t) : TendstoLocallyUniformly F f p
参数：h : forall x, exists t in 𝓝 x, TendstoUniformlyOn F f p t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tendstoLocallyUniformlyOn_univ`：tendstoLocallyUniformlyOn_univ : Tendsto
LocallyUniformlyOn F f p univ ↔ TendstoLocallyUniformly F f p
· 使用引理 `tendstoLocallyUniformlyOn_of_forall_exists_nhds`：tendstoLocallyUniformly
On_of_forall_exists_nhds (h : forall x in s, exists t in 𝓝[s] x, TendstoUniforml
yOn F f p t) : TendstoLocallyUniforml…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
If every `x` has a neighbourhood on which `F i` tends uniformly to `f`, then `F 
i` tends
locally uniformly to `f`. (Special case of `tendstoLocallyUniformlyOn_of_forall_
exists_nhds`
where `s = univ`.)
-/
lemma tendstoLocallyUniformly_of_forall_exists_nhds
    (h : ∀ x, ∃ t ∈ 𝓝 x, TendstoUniformlyOn F f p t) :
    TendstoLocallyUniformly F f p :=
  tendstoLocallyUniformlyOn_univ.mp
    <| tendstoLocallyUniformlyOn_of_forall_exists_nhds (by simpa using h)
/-
**tendstoLocallyUniformlyOn_TFAE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendstoLocallyUniformlyOn_TFAE [LocallyCompactSpace α] (G : ι -> α -> β) (
g : α -> β) (p : Filter ι) (hs : IsOpen s) : List.TFAE [ TendstoLocallyUniformly
On G g p s, forall K, K subseteq s -> IsCompact K -> TendstoUniformlyOn G g p K,
 forall x in s, exists v in 𝓝[s] x, TendstoUniformlyOn G g p v]
参数：G : ι -> α -> β；g : α -> β；p : Filter ι；hs : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact`：tendstoLoca
llyUniformlyOn_iff_tendstoUniformlyOn_of_compact (hs : IsCompact s) : TendstoLoc
allyUniformlyOn F f p s ↔ TendstoUniformlyOn F f …
· 使用定理 `TendstoLocallyUniformlyOn.mono`：TendstoLocallyUniformlyOn.mono (h : Tend
stoLocallyUniformlyOn F f p s) (h' : s' subseteq s) : TendstoLocallyUniformlyOn 
F f p s'
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `compact_basis_nhds`：compact_basis_nhds [LocallyCompactSpace X] (x : X) :
 (𝓝 x).HasBasis (fun s => s in 𝓝 x ∧ IsCompact s) fun s => s
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)
-/
theorem tendstoLocallyUniformlyOn_TFAE [LocallyCompactSpace α] (G : ι → α → β) (g : α → β)
    (p : Filter ι) (hs : IsOpen s) :
    List.TFAE [
      TendstoLocallyUniformlyOn G g p s,
      ∀ K, K ⊆ s → IsCompact K → TendstoUniformlyOn G g p K,
      ∀ x ∈ s, ∃ v ∈ 𝓝[s] x, TendstoUniformlyOn G g p v] := by
  tfae_have 1 → 2
  | h, K, hK1, hK2 =>
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK2).mp (h.mono hK1)
  tfae_have 2 → 3
  | h, x, hx => by
    obtain ⟨K, ⟨hK1, hK2⟩, hK3⟩ := (compact_basis_nhds x).mem_iff.mp (hs.mem_nhds hx)
    exact ⟨K, nhdsWithin_le_nhds hK1, h K hK3 hK2⟩
  tfae_have 3 → 1
  | h, u, hu, x, hx => by
    obtain ⟨v, hv1, hv2⟩ := h x hx
    exact ⟨v, hv1, hv2 u hu⟩
  tfae_finish
/-
**tendstoLocallyUniformlyOn_iff_forall_isCompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendstoLocallyUniformlyOn_iff_forall_isCompact [LocallyCompactSpace α] (hs
 : IsOpen s) : TendstoLocallyUniformlyOn F f p s ↔ forall K, K subseteq s -> IsC
ompact K -> TendstoUniformlyOn F f p K
参数：hs : IsOpen s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `tendstoLocallyUniformlyOn_TFAE`：tendstoLocallyUniformlyOn_TFAE [LocallyC
ompactSpace α] (G : ι -> α -> β) (g : α -> β) (p : Filter ι) (hs : IsOpen s) : L
ist.TFAE [ TendstoLo…
-/
theorem tendstoLocallyUniformlyOn_iff_forall_isCompact [LocallyCompactSpace α] (hs : IsOpen s) :
    TendstoLocallyUniformlyOn F f p s ↔ ∀ K, K ⊆ s → IsCompact K → TendstoUniformlyOn F f p K :=
  (tendstoLocallyUniformlyOn_TFAE F f p hs).out 0 1
/-
**tendstoLocallyUniformly_iff_forall_isCompact** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendstoLocallyUniformly_iff_forall_isCompact [LocallyCompactSpace α] : Ten
dstoLocallyUniformly F f p ↔ forall K : Set α, IsCompact K -> TendstoUniformlyOn
 F f p K
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendstoLocallyUniformlyOn_iff_forall_isCompact`：tendstoLocallyUniformlyO
n_iff_forall_isCompact [LocallyCompactSpace α] (hs : IsOpen s) : TendstoLocallyU
niformlyOn F f p s ↔ forall K, K sub…
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma tendstoLocallyUniformly_iff_forall_isCompact [LocallyCompactSpace α] :
    TendstoLocallyUniformly F f p ↔ ∀ K : Set α, IsCompact K → TendstoUniformlyOn F f p K := by
  simp only [← tendstoLocallyUniformlyOn_univ,
    tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ, Set.subset_univ, forall_true_left]
/-
**tendstoLocallyUniformlyOn_iff_filter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendstoLocallyUniformlyOn_iff_filter : TendstoLocallyUniformlyOn F f p s ↔
 forall x in s, TendstoUniformlyOnFilter F f p (𝓝[s] x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Filter.eventually_of_mem`：eventually_of_mem {f : Filter α} {P : α -> Pro
p} {U : Set α} (hU : U in f) (h : forall x in U, P x) : forallᶠ x in f, P x
-/
theorem tendstoLocallyUniformlyOn_iff_filter :
    TendstoLocallyUniformlyOn F f p s ↔ ∀ x ∈ s, TendstoUniformlyOnFilter F f p (𝓝[s] x) := by
  simp only [TendstoUniformlyOnFilter, eventually_prod_iff]
  constructor
  · rintro h x hx u hu
    obtain ⟨s, hs1, hs2⟩ := h u hu x hx
    exact ⟨_, hs2, _, eventually_of_mem hs1 fun x => id, fun hi y hy => hi y hy⟩
  · rintro h u hu x hx
    obtain ⟨pa, hpa, pb, hpb, h⟩ := h x hx u hu
    exact ⟨{a | pb a}, hpb, eventually_of_mem hpa fun i hi y hy => h hi hy⟩
/-
**tendstoLocallyUniformly_iff_filter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendstoLocallyUniformly_iff_filter : TendstoLocallyUniformly F f p ↔ foral
l x, TendstoUniformlyOnFilter F f p (𝓝 x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `tendstoLocallyUniformlyOn_iff_filter`：tendstoLocallyUniformlyOn_iff_filt
er : TendstoLocallyUniformlyOn F f p s ↔ forall x in s, TendstoUniformlyOnFilter
 F f p (𝓝[s] x)
-/
theorem tendstoLocallyUniformly_iff_filter :
    TendstoLocallyUniformly F f p ↔ ∀ x, TendstoUniformlyOnFilter F f p (𝓝 x) := by
  simpa [← tendstoLocallyUniformlyOn_univ, ← nhdsWithin_univ] using
    @tendstoLocallyUniformlyOn_iff_filter _ _ _ _ _ F f univ p
/-
**TendstoLocallyUniformlyOn.tendsto_at** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoLocallyUniformlyOn.tendsto_at (hf : TendstoLocallyUniformlyOn F f p
 s) {a : α} (ha : a in s) : Tendsto (fun i => F i a) p (𝓝 (f a))
参数：hf : TendstoLocallyUniformlyOn F f p s；ha : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TendstoUniformlyOnFilter.tendsto_at`：TendstoUniformlyOnFilter.tendsto_at
 (h : TendstoUniformlyOnFilter F f p p') (hx : 𝓟 {x} <= p') : Tendsto (fun n => 
F n x) p 𝓝 (f x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tendstoLocallyUniformlyOn_iff_filter`：tendstoLocallyUniformlyOn_iff_filt
er : TendstoLocallyUniformlyOn F f p s ↔ forall x in s, TendstoUniformlyOnFilter
 F f p (𝓝[s] x)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.principal_singleton`：principal_singleton (a : α) : 𝓟 {a} = pure a
· 使用定理 `pure_le_nhdsWithin`：pure_le_nhdsWithin {a : α} {s : Set α} (ha : a in s)
 : pure a <= 𝓝[s] a
-/
theorem TendstoLocallyUniformlyOn.tendsto_at (hf : TendstoLocallyUniformlyOn F f p s) {a : α}
    (ha : a ∈ s) : Tendsto (fun i => F i a) p (𝓝 (f a)) := by
  refine ((tendstoLocallyUniformlyOn_iff_filter.mp hf) a ha).tendsto_at ?_
  simpa only [Filter.principal_singleton] using pure_le_nhdsWithin ha
/-
**TendstoLocallyUniformlyOn.unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoLocallyUniformlyOn.unique [p.NeBot] [T2Space β] {g : α -> β} (hf : 
TendstoLocallyUniformlyOn F f p s) (hg : TendstoLocallyUniformlyOn F g p s) : s.
EqOn f g
参数：hf : TendstoLocallyUniformlyOn F f p s；hg : TendstoLocallyUniformlyOn F g p s
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `TendstoLocallyUniformlyOn.tendsto_at`：TendstoLocallyUniformlyOn.tendsto_
at (hf : TendstoLocallyUniformlyOn F f p s) {a : α} (ha : a in s) : Tendsto (fun
 i => F i a) p (𝓝 (f a))
-/
theorem TendstoLocallyUniformlyOn.unique [p.NeBot] [T2Space β] {g : α → β}
    (hf : TendstoLocallyUniformlyOn F f p s) (hg : TendstoLocallyUniformlyOn F g p s) :
    s.EqOn f g := fun _a ha => tendsto_nhds_unique (hf.tendsto_at ha) (hg.tendsto_at ha)
/-
**TendstoLocallyUniformlyOn.congr_inseparable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoLocallyUniformlyOn.congr_inseparable {G : ι -> α -> β} (hf : Tendst
oLocallyUniformlyOn F f p s) (hg : forallᶠ n in p, forall x in s, Inseparable (F
 n x) (G n x)) : TendstoLocallyUniformlyOn G f p s
参数：hf : TendstoLocallyUniformlyOn F f p s；hg : forallᶠ n in p, forall x in s, In
separable (F n x) (G n x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_prod_principal_iff`：eventually_prod_principal_iff {p :
 α × β -> Prop} {s : Set β} : (forallᶠ x : α × β in f ×ˢ 𝓟 s, p x) ↔ forallᶠ x :
 α in f, forall y : β, y i…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendstoLocallyUniformlyOn_iff_forall_tendsto`：tendstoLocallyUniformlyOn_
iff_forall_tendsto : TendstoLocallyUniformlyOn F f p s ↔ forall x in s, Tendsto 
(fun y : ι × α => (f y.2, F y.1 y.…
· 使用定理 `forall₂_imp`：forall₂_imp {p q : forall a, β a -> Prop} (h : forall a b, 
p a b -> q a b) : (forall a b, p a b) -> forall a b, q a b
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `uniformity_hasBasis_open`：uniformity_hasBasis_open : HasBasis (𝓤 α) (fun
 V : SetRel α α => V in 𝓤 α ∧ IsOpen V) id
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `Filter.prod_mono_right`：prod_mono_right (f : Filter α) {g₁ g₂ : Filter β
} (hf : g₁ <= g₂) : f ×ˢ g₁ <= f ×ˢ g₂
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Inseparable.mem_open_iff`：mem_open_iff (h : x ~ᵢ y) (hs : IsOpen s) : x 
in s ↔ y in s
· 使用定理 `Inseparable.prod`：Inseparable.prod {x₁ x₂ : X} {y₁ y₂ : Y} (hx : x₁ ~ᵢ x
₂) (hy : y₁ ~ᵢ y₂) : (x₁, y₁) ~ᵢ (x₂, y₂)
· 使用定理 `Inseparable.rfl`：rfl : x ~ᵢ x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem TendstoLocallyUniformlyOn.congr_inseparable {G : ι → α → β}
    (hf : TendstoLocallyUniformlyOn F f p s)
    (hg : ∀ᶠ n in p, ∀ x ∈ s, Inseparable (F n x) (G n x)) : TendstoLocallyUniformlyOn G f p s := by
  have hg : ∀ᶠ x in p ×ˢ 𝓟 s, Inseparable (F x.1 x.2) (G x.1 x.2) := by
    simpa using eventually_prod_principal_iff.2 hg
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto] at hf ⊢
  refine forall₂_imp (fun x hx hf => ?_) hf
  rw [uniformity_hasBasis_open.tendsto_right_iff] at hf ⊢
  exact fun i hi => (hf i hi).mp ((hg.filter_mono (prod_mono_right p inf_le_right)).mono
    fun x hg hf => ((Inseparable.rfl.prod hg).mem_open_iff hi.2).1 hf)
/-
**TendstoLocallyUniformlyOn.congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoLocallyUniformlyOn.congr {G : ι -> α -> β} (hf : TendstoLocallyUnif
ormlyOn F f p s) (hg : forall n, s.EqOn (F n) (G n)) : TendstoLocallyUniformlyOn
 G f p s
参数：hf : TendstoLocallyUniformlyOn F f p s；hg : forall n, s.EqOn (F n) (G n)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TendstoLocallyUniformlyOn.congr_inseparable`：TendstoLocallyUniformlyOn.c
ongr_inseparable {G : ι -> α -> β} (hf : TendstoLocallyUniformlyOn F f p s) (hg 
: forallᶠ n in p, forall x in s, …
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Inseparable.of_eq`：of_eq (e : x = y) : Inseparable x y
-/
theorem TendstoLocallyUniformlyOn.congr {G : ι → α → β} (hf : TendstoLocallyUniformlyOn F f p s)
    (hg : ∀ n, s.EqOn (F n) (G n)) : TendstoLocallyUniformlyOn G f p s :=
  hf.congr_inseparable (.of_forall fun n _ hx => .of_eq (hg n hx))
/-
**TendstoLocallyUniformlyOn.congr_inseparable_right** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：TendstoLocallyUniformlyOn.congr_inseparable_right {g : α -> β} (hf : Tends
toLocallyUniformlyOn F f p s) (hg : forall x in s, Inseparable (f x) (g x)) : Te
ndstoLocallyUniformlyOn F g p s
参数：hf : TendstoLocallyUniformlyOn F f p s；hg : forall x in s, Inseparable (f x) 
(g x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventually_prod_principal_iff`：eventually_prod_principal_iff {p :
 α × β -> Prop} {s : Set β} : (forallᶠ x : α × β in f ×ˢ 𝓟 s, p x) ↔ forallᶠ x :
 α in f, forall y : β, y i…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `tendstoLocallyUniformlyOn_iff_forall_tendsto`：tendstoLocallyUniformlyOn_
iff_forall_tendsto : TendstoLocallyUniformlyOn F f p s ↔ forall x in s, Tendsto 
(fun y : ι × α => (f y.2, F y.1 y.…
· 使用定理 `forall₂_imp`：forall₂_imp {p q : forall a, β a -> Prop} (h : forall a b, 
p a b -> q a b) : (forall a b, p a b) -> forall a b, q a b
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `uniformity_hasBasis_open`：uniformity_hasBasis_open : HasBasis (𝓤 α) (fun
 V : SetRel α α => V in 𝓤 α ∧ IsOpen V) id
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `Filter.prod_mono_right`：prod_mono_right (f : Filter α) {g₁ g₂ : Filter β
} (hf : g₁ <= g₂) : f ×ˢ g₁ <= f ×ˢ g₂
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Inseparable.mem_open_iff`：mem_open_iff (h : x ~ᵢ y) (hs : IsOpen s) : x 
in s ↔ y in s
· 使用定理 `Inseparable.prod`：Inseparable.prod {x₁ x₂ : X} {y₁ y₂ : Y} (hx : x₁ ~ᵢ x
₂) (hy : y₁ ~ᵢ y₂) : (x₁, y₁) ~ᵢ (x₂, y₂)
· 使用定理 `Inseparable.rfl`：rfl : x ~ᵢ x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem TendstoLocallyUniformlyOn.congr_inseparable_right {g : α → β}
    (hf : TendstoLocallyUniformlyOn F f p s)
    (hg : ∀ x ∈ s, Inseparable (f x) (g x)) : TendstoLocallyUniformlyOn F g p s := by
  have hg : ∀ᶠ x in p ×ˢ 𝓟 s, Inseparable (f x.2) (g x.2) := by
    rw [eventually_prod_principal_iff]
    exact .of_forall fun _ => hg
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto] at hf ⊢
  refine forall₂_imp (fun x hx hf => ?_) hf
  rw [uniformity_hasBasis_open.tendsto_right_iff] at hf ⊢
  exact fun i hi => (hf i hi).mp ((hg.filter_mono (prod_mono_right p inf_le_right)).mono
    fun x hg hf => ((hg.prod .rfl).mem_open_iff hi.2).1 hf)
/-
**TendstoLocallyUniformlyOn.congr_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoLocallyUniformlyOn.congr_right {g : α -> β} (hf : TendstoLocallyUni
formlyOn F f p s) (hg : s.EqOn f g) : TendstoLocallyUniformlyOn F g p s
参数：hf : TendstoLocallyUniformlyOn F f p s；hg : s.EqOn f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TendstoLocallyUniformlyOn.congr_inseparable_right`：TendstoLocallyUniform
lyOn.congr_inseparable_right {g : α -> β} (hf : TendstoLocallyUniformlyOn F f p 
s) (hg : forall x in s, Inseparable (f …
· 使用定理 `Inseparable.of_eq`：of_eq (e : x = y) : Inseparable x y
-/
theorem TendstoLocallyUniformlyOn.congr_right {g : α → β} (hf : TendstoLocallyUniformlyOn F f p s)
    (hg : s.EqOn f g) : TendstoLocallyUniformlyOn F g p s :=
  hf.congr_inseparable_right fun _ hx => .of_eq (hg hx)
/-
**TendstoLocallyUniformly.congr_inseparable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoLocallyUniformly.congr_inseparable {G : ι -> α -> β} (hf : TendstoL
ocallyUniformly F f p) (hg : forallᶠ n in p, forall x, Inseparable (F n x) (G n 
x)) : TendstoLocallyUniformly G f p
参数：hf : TendstoLocallyUniformly F f p；hg : forallᶠ n in p, forall x, Inseparable
 (F n x) (G n x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tendstoLocallyUniformlyOn_univ`：tendstoLocallyUniformlyOn_univ : Tendsto
LocallyUniformlyOn F f p univ ↔ TendstoLocallyUniformly F f p
· 使用定理 `TendstoLocallyUniformlyOn.congr_inseparable`：TendstoLocallyUniformlyOn.c
ongr_inseparable {G : ι -> α -> β} (hf : TendstoLocallyUniformlyOn F f p s) (hg 
: forallᶠ n in p, forall x in s, …
· 使用定理 `TendstoLocallyUniformly.tendstoLocallyUniformlyOn`：∀ {α : Type u_1} {β :
 Type u_2} {ι : Type u_4} [inst : TopologicalSpace α] [inst_1 : UniformSpace β] 
{F : ι → α → β}   {f : α → β} {s : Set …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem TendstoLocallyUniformly.congr_inseparable {G : ι → α → β}
    (hf : TendstoLocallyUniformly F f p)
    (hg : ∀ᶠ n in p, ∀ x, Inseparable (F n x) (G n x)) : TendstoLocallyUniformly G f p :=
  tendstoLocallyUniformlyOn_univ.1
    (hf.tendstoLocallyUniformlyOn.congr_inseparable (by simpa using hg))
/-
**TendstoLocallyUniformly.congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoLocallyUniformly.congr {G : ι -> α -> β} (hf : TendstoLocallyUnifor
mly F f p) (hg : forall n x, F n x = G n x) : TendstoLocallyUniformly G f p
参数：hf : TendstoLocallyUniformly F f p；hg : forall n x, F n x = G n x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TendstoLocallyUniformly.congr_inseparable`：TendstoLocallyUniformly.congr
_inseparable {G : ι -> α -> β} (hf : TendstoLocallyUniformly F f p) (hg : forall
ᶠ n in p, forall x, Inseparable…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Inseparable.of_eq`：of_eq (e : x = y) : Inseparable x y
-/
theorem TendstoLocallyUniformly.congr {G : ι → α → β} (hf : TendstoLocallyUniformly F f p)
    (hg : ∀ n x, F n x = G n x) : TendstoLocallyUniformly G f p :=
  hf.congr_inseparable (.of_forall fun n x => .of_eq (hg n x))
/-
**TendstoLocallyUniformly.congr_inseparable_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoLocallyUniformly.congr_inseparable_right {g : α -> β} (hf : Tendsto
LocallyUniformly F f p) (hg : forall x, Inseparable (f x) (g x)) : TendstoLocall
yUniformly F g p
参数：hf : TendstoLocallyUniformly F f p；hg : forall x, Inseparable (f x) (g x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tendstoLocallyUniformlyOn_univ`：tendstoLocallyUniformlyOn_univ : Tendsto
LocallyUniformlyOn F f p univ ↔ TendstoLocallyUniformly F f p
· 使用定理 `TendstoLocallyUniformlyOn.congr_inseparable_right`：TendstoLocallyUniform
lyOn.congr_inseparable_right {g : α -> β} (hf : TendstoLocallyUniformlyOn F f p 
s) (hg : forall x in s, Inseparable (f …
· 使用定理 `TendstoLocallyUniformly.tendstoLocallyUniformlyOn`：∀ {α : Type u_1} {β :
 Type u_2} {ι : Type u_4} [inst : TopologicalSpace α] [inst_1 : UniformSpace β] 
{F : ι → α → β}   {f : α → β} {s : Set …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem TendstoLocallyUniformly.congr_inseparable_right {g : α → β}
    (hf : TendstoLocallyUniformly F f p)
    (hg : ∀ x, Inseparable (f x) (g x)) : TendstoLocallyUniformly F g p :=
  tendstoLocallyUniformlyOn_univ.1
    (hf.tendstoLocallyUniformlyOn.congr_inseparable_right (by simpa using hg))
/-
**TendstoLocallyUniformly.congr_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoLocallyUniformly.congr_right {g : α -> β} (hf : TendstoLocallyUnifo
rmly F f p) (hg : forall x, f x = g x) : TendstoLocallyUniformly F g p
参数：hf : TendstoLocallyUniformly F f p；hg : forall x, f x = g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TendstoLocallyUniformly.congr_inseparable_right`：TendstoLocallyUniformly
.congr_inseparable_right {g : α -> β} (hf : TendstoLocallyUniformly F f p) (hg :
 forall x, Inseparable (f x) (g x)) :…
· 使用定理 `Inseparable.of_eq`：of_eq (e : x = y) : Inseparable x y
-/
theorem TendstoLocallyUniformly.congr_right {g : α → β} (hf : TendstoLocallyUniformly F f p)
    (hg : ∀ x, f x = g x) : TendstoLocallyUniformly F g p :=
  hf.congr_inseparable_right fun x => .of_eq (hg x)
