/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.UniformSpace.Cauchy

/-!
# Uniform convergence

A sequence of functions `Fₙ` (with values in a metric space) converges uniformly on a set `s` to a
function `f` if, for all `ε > 0`, for all large enough `n`, one has for all `y ∈ s` the inequality
`dist (f y, Fₙ y) < ε`. Under uniform convergence, many properties of the `Fₙ` pass to the limit,
most notably continuity. We prove this in the file, defining the notion of uniform convergence
in the more general setting of uniform spaces, and with respect to an arbitrary indexing set
endowed with a filter (instead of just `ℕ` with `atTop`).

## Main results

Let `α` be a topological space, `β` a uniform space, `Fₙ` and `f` be functions from `α` to `β`
(where the index `n` belongs to an indexing type `ι` endowed with a filter `p`).

* `TendstoUniformlyOn F f p s`: the fact that `Fₙ` converges uniformly to `f` on `s`. This means
  that, for any entourage `u` of the diagonal, for large enough `n` (with respect to `p`), one has
  `(f y, Fₙ y) ∈ u` for all `y ∈ s`.
* `TendstoUniformly F f p`: same notion with `s = univ`.
* `TendstoUniformlyOn.continuousOn`: a uniform limit on a set of functions which are continuous
  on this set is itself continuous on this set.
* `TendstoUniformly.continuous`: a uniform limit of continuous functions is continuous.
* `TendstoUniformlyOn.tendsto_comp`: If `Fₙ` tends uniformly to `f` on a set `s`, and `gₙ` tends
  to `x` within `s`, then `Fₙ gₙ` tends to `f x` if `f` is continuous at `x` within `s`.
* `TendstoUniformly.tendsto_comp`: If `Fₙ` tends uniformly to `f`, and `gₙ` tends to `x`, then
  `Fₙ gₙ` tends to `f x`.

Finally, we introduce the notion of a uniform Cauchy sequence, which is to uniform
convergence what a Cauchy sequence is to the usual notion of convergence.

## Implementation notes

We derive most of our initial results from an auxiliary definition `TendstoUniformlyOnFilter`.
This definition in and of itself can sometimes be useful, e.g., when studying the local behavior
of the `Fₙ` near a point, which would typically look like `TendstoUniformlyOnFilter F f p (𝓝 x)`.
Still, while this may be the "correct" definition (see
`tendstoUniformlyOn_iff_tendstoUniformlyOnFilter`), it is somewhat unwieldy to work with in
practice. Thus, we provide the more traditional definition in `TendstoUniformlyOn`.

## Tags

Uniform limit, uniform convergence, tends uniformly to
-/

@[expose] public section

noncomputable section

open Topology Uniformity Filter Set Uniform

variable {α β γ ι : Type*} [UniformSpace β]
variable {F : ι → α → β} {f : α → β} {s s' : Set α} {x : α} {p : Filter ι} {p' : Filter α}

/-!
### Different notions of uniform convergence

We define uniform convergence, on a set or in the whole space.
-/

/-- A sequence of functions `Fₙ` converges uniformly on a filter `p'` to a limiting function `f`
with respect to the filter `p` if, for any entourage of the diagonal `u`, one has
`p ×ˢ p'`-eventually `(f x, Fₙ x) ∈ u`. -/
/-
**TendstoUniformlyOnFilter** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：TendstoUniformlyOnFilter (F : ι -> α -> β) (f : α -> β) (p : Filter ι) (p'
 : Filter α)
参数：F : ι -> α -> β；f : α -> β；p : Filter ι；p' : Filter α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sequence of functions `Fₙ` converges uniformly on a filter `p'` to a limiting 
function `f`
with respect to the filter `p` if, for any entourage of the diagonal `u`, one ha
s
`p ×ˢ p'`-eventually `(f x, Fₙ x) ∈ u`.
-/
def TendstoUniformlyOnFilter (F : ι → α → β) (f : α → β) (p : Filter ι) (p' : Filter α) :=
  ∀ u ∈ 𝓤 β, ∀ᶠ n : ι × α in p ×ˢ p', (f n.snd, F n.fst n.snd) ∈ u

/--
A sequence of functions `Fₙ` converges uniformly on a filter `p'` to a limiting function `f` w.r.t.
filter `p` iff the function `(n, x) ↦ (f x, Fₙ x)` converges along `p ×ˢ p'` to the uniformity.
In other words: one knows nothing about the behavior of `x` in this limit besides it being in `p'`.
-/
/-
**tendstoUniformlyOnFilter_iff_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendstoUniformlyOnFilter_iff_tendsto : TendstoUniformlyOnFilter F f p p' ↔
 Tendsto (fun q : ι × α => (f q.2, F q.1 q.2)) (p ×ˢ p') (𝓤 β)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A sequence of functions `Fₙ` converges uniformly on a filter `p'` to a limiting 
function `f` w.r.t.
filter `p` iff the function `(n, x) ↦ (f x, Fₙ x)` converges along `p ×ˢ p'` to 
the uniformity.
In other words: one knows nothing about the behavior of `x` in this limit beside
s it being in `p'`.
-/
theorem tendstoUniformlyOnFilter_iff_tendsto :
    TendstoUniformlyOnFilter F f p p' ↔
      Tendsto (fun q : ι × α => (f q.2, F q.1 q.2)) (p ×ˢ p') (𝓤 β) :=
  Iff.rfl

/-- A sequence of functions `Fₙ` converges uniformly on a set `s` to a limiting function `f` with
respect to the filter `p` if, for any entourage of the diagonal `u`, one has `p`-eventually
`(f x, Fₙ x) ∈ u` for all `x ∈ s`. -/
/-
**TendstoUniformlyOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：TendstoUniformlyOn (F : ι -> α -> β) (f : α -> β) (p : Filter ι) (s : Set 
α)
参数：F : ι -> α -> β；f : α -> β；p : Filter ι；s : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sequence of functions `Fₙ` converges uniformly on a set `s` to a limiting func
tion `f` with
respect to the filter `p` if, for any entourage of the diagonal `u`, one has `p`
-eventually
`(f x, Fₙ x) ∈ u` for all `x ∈ s`.
-/
def TendstoUniformlyOn (F : ι → α → β) (f : α → β) (p : Filter ι) (s : Set α) :=
  ∀ u ∈ 𝓤 β, ∀ᶠ n in p, ∀ x : α, x ∈ s → (f x, F n x) ∈ u
/-
**tendstoUniformlyOn_iff_tendstoUniformlyOnFilter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendstoUniformlyOn_iff_tendstoUniformlyOnFilter : TendstoUniformlyOn F f p
 s ↔ TendstoUniformlyOnFilter F f p (𝓟 s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem tendstoUniformlyOn_iff_tendstoUniformlyOnFilter :
    TendstoUniformlyOn F f p s ↔ TendstoUniformlyOnFilter F f p (𝓟 s) := by
  simp only [TendstoUniformlyOn, TendstoUniformlyOnFilter]
  apply forall₂_congr
  simp_rw [eventually_prod_principal_iff]
  simp

alias ⟨TendstoUniformlyOn.tendstoUniformlyOnFilter, TendstoUniformlyOnFilter.tendstoUniformlyOn⟩ :=
  tendstoUniformlyOn_iff_tendstoUniformlyOnFilter

/-- A sequence of functions `Fₙ` converges uniformly on a set `s` to a limiting function `f` w.r.t.
filter `p` iff the function `(n, x) ↦ (f x, Fₙ x)` converges along `p ×ˢ 𝓟 s` to the uniformity.
In other words: one knows nothing about the behavior of `x` in this limit besides it being in `s`.
-/
/-
**tendstoUniformlyOn_iff_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendstoUniformlyOn_iff_tendsto : TendstoUniformlyOn F f p s ↔ Tendsto (fun
 q : ι × α => (f q.2, F q.1 q.2)) (p ×ˢ 𝓟 s) (𝓤 β)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A sequence of functions `Fₙ` converges uniformly on a set `s` to a limiting func
tion `f` w.r.t.
filter `p` iff the function `(n, x) ↦ (f x, Fₙ x)` converges along `p ×ˢ 𝓟 s` to
 the uniformity.
In other words: one knows nothing about the behavior of `x` in this limit beside
s it being in `s`.
-/
theorem tendstoUniformlyOn_iff_tendsto :
    TendstoUniformlyOn F f p s ↔
    Tendsto (fun q : ι × α => (f q.2, F q.1 q.2)) (p ×ˢ 𝓟 s) (𝓤 β) := by
  simp [tendstoUniformlyOn_iff_tendstoUniformlyOnFilter, tendstoUniformlyOnFilter_iff_tendsto]

/-- A sequence of functions `Fₙ` converges uniformly to a limiting function `f` with respect to a
filter `p` if, for any entourage of the diagonal `u`, one has `p`-eventually
`(f x, Fₙ x) ∈ u` for all `x`. -/
@[wikidata Q1411887]
/-
**TendstoUniformly** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：TendstoUniformly (F : ι -> α -> β) (f : α -> β) (p : Filter ι)
参数：F : ι -> α -> β；f : α -> β；p : Filter ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sequence of functions `Fₙ` converges uniformly to a limiting function `f` with
 respect to a
filter `p` if, for any entourage of the diagonal `u`, one has `p`-eventually
`(f x, Fₙ x) ∈ u` for all `x`.
-/
def TendstoUniformly (F : ι → α → β) (f : α → β) (p : Filter ι) :=
  ∀ u ∈ 𝓤 β, ∀ᶠ n in p, ∀ x : α, (f x, F n x) ∈ u
/-
**tendstoUniformlyOn_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendstoUniformlyOn_univ : TendstoUniformlyOn F f p univ ↔ TendstoUniformly
 F f p
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
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendstoUniformlyOn_univ : TendstoUniformlyOn F f p univ ↔ TendstoUniformly F f p := by
  simp [TendstoUniformlyOn, TendstoUniformly]
/-
**tendstoUniformly_iff_tendstoUniformlyOnFilter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendstoUniformly_iff_tendstoUniformlyOnFilter : TendstoUniformly F f p ↔ T
endstoUniformlyOnFilter F f p ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tendstoUniformlyOn_univ`：tendstoUniformlyOn_univ : TendstoUniformlyOn F 
f p univ ↔ TendstoUniformly F f p
· 使用定理 `tendstoUniformlyOn_iff_tendstoUniformlyOnFilter`：tendstoUniformlyOn_iff_
tendstoUniformlyOnFilter : TendstoUniformlyOn F f p s ↔ TendstoUniformlyOnFilter
 F f p (𝓟 s)
· 使用定理 `Filter.principal_univ`：∀ {α : Type u}, Filter.principal Set.univ = ⊤
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem tendstoUniformly_iff_tendstoUniformlyOnFilter :
    TendstoUniformly F f p ↔ TendstoUniformlyOnFilter F f p ⊤ := by
  rw [← tendstoUniformlyOn_univ, tendstoUniformlyOn_iff_tendstoUniformlyOnFilter, principal_univ]
/-
**TendstoUniformly.tendstoUniformlyOnFilter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoUniformly.tendstoUniformlyOnFilter (h : TendstoUniformly F f p) : T
endstoUniformlyOnFilter F f p ⊤
参数：h : TendstoUniformly F f p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tendstoUniformly_iff_tendstoUniformlyOnFilter`：tendstoUniformly_iff_tend
stoUniformlyOnFilter : TendstoUniformly F f p ↔ TendstoUniformlyOnFilter F f p ⊤
-/
theorem TendstoUniformly.tendstoUniformlyOnFilter (h : TendstoUniformly F f p) :
    TendstoUniformlyOnFilter F f p ⊤ := by rwa [← tendstoUniformly_iff_tendstoUniformlyOnFilter]
/-
**tendstoUniformlyOn_iff_tendstoUniformly_comp_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendstoUniformlyOn_iff_tendstoUniformly_comp_coe : TendstoUniformlyOn F f 
p s ↔ TendstoUniformly (fun i (x : s) => F i x) (f ∘ (↑)) p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendstoUniformlyOn_iff_tendstoUniformly_comp_coe :
    TendstoUniformlyOn F f p s ↔ TendstoUniformly (fun i (x : s) => F i x) (f ∘ (↑)) p :=
  forall₂_congr fun u _ => by simp
/-
**tendstoUniformlyOn_iff_restrict** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendstoUniformlyOn_iff_restrict {K : Set α} : TendstoUniformlyOn F f p K ↔
 TendstoUniformly (fun n : ι => K.domRestrict (F n)) (K.domRestrict f) p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendstoUniformlyOn_iff_tendstoUniformly_comp_coe`：tendstoUniformlyOn_iff
_tendstoUniformly_comp_coe : TendstoUniformlyOn F f p s ↔ TendstoUniformly (fun 
i (x : s) => F i x) (f ∘ (↑)) p
-/
lemma tendstoUniformlyOn_iff_restrict {K : Set α} : TendstoUniformlyOn F f p K ↔
    TendstoUniformly (fun n : ι => K.domRestrict (F n)) (K.domRestrict f) p :=
  tendstoUniformlyOn_iff_tendstoUniformly_comp_coe

/-- A sequence of functions `Fₙ` converges uniformly to a limiting function `f` w.r.t.
filter `p` iff the function `(n, x) ↦ (f x, Fₙ x)` converges along `p ×ˢ ⊤` to the uniformity.
In other words: one knows nothing about the behavior of `x` in this limit.
-/
/-
**tendstoUniformly_iff_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendstoUniformly_iff_tendsto : TendstoUniformly F f p ↔ Tendsto (fun q : ι
 × α => (f q.2, F q.1 q.2)) (p ×ˢ ⊤) (𝓤 β)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A sequence of functions `Fₙ` converges uniformly to a limiting function `f` w.r.
t.
filter `p` iff the function `(n, x) ↦ (f x, Fₙ x)` converges along `p ×ˢ ⊤` to t
he uniformity.
In other words: one knows nothing about the behavior of `x` in this limit.
-/
theorem tendstoUniformly_iff_tendsto :
    TendstoUniformly F f p ↔ Tendsto (fun q : ι × α => (f q.2, F q.1 q.2)) (p ×ˢ ⊤) (𝓤 β) := by
  simp [tendstoUniformly_iff_tendstoUniformlyOnFilter, tendstoUniformlyOnFilter_iff_tendsto]

/-- Uniform convergence implies pointwise convergence. -/
/-
**TendstoUniformlyOnFilter.tendsto_at** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoUniformlyOnFilter.tendsto_at (h : TendstoUniformlyOnFilter F f p p'
) (hx : 𝓟 {x} <= p') : Tendsto (fun n => F n x) p 𝓝 (f x)
参数：h : TendstoUniformlyOnFilter F f p p'；hx : 𝓟 {x} <= p'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Uniform.tendsto_nhds_right`：tendsto_nhds_right {f : Filter β} {u : β -> 
α} {a : α} : Tendsto u f (𝓝 a) ↔ Tendsto (fun x => (a, u x)) f (𝓤 α)
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Eventually.curry`：∀ {α : Type u_1} {β : Type u_2} {la : Filter α}
 {lb : Filter β} {p : α × β → Prop},   (∀ᶠ (x : α × β) in la ×ˢ lb, p x) → ∀ᶠ (x
 : α) in la, …
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.principal_singleton`：principal_singleton (a : α) : 𝓟 {a} = pure a
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x

--- 原说明 ---
Uniform convergence implies pointwise convergence.
-/
theorem TendstoUniformlyOnFilter.tendsto_at (h : TendstoUniformlyOnFilter F f p p')
    (hx : 𝓟 {x} ≤ p') : Tendsto (fun n => F n x) p <| 𝓝 (f x) := by
  refine Uniform.tendsto_nhds_right.mpr fun u hu => mem_map.mpr ?_
  filter_upwards [(h u hu).curry]
  intro i h
  simpa using h.filter_mono hx

/-- Uniform convergence implies pointwise convergence. -/
/-
**TendstoUniformlyOn.tendsto_at** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoUniformlyOn.tendsto_at (h : TendstoUniformlyOn F f p s) (hx : x in 
s) : Tendsto (fun n => F n x) p 𝓝 (f x)
参数：h : TendstoUniformlyOn F f p s；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TendstoUniformlyOnFilter.tendsto_at`：TendstoUniformlyOnFilter.tendsto_at
 (h : TendstoUniformlyOnFilter F f p p') (hx : 𝓟 {x} <= p') : Tendsto (fun n => 
F n x) p 𝓝 (f x)
· 使用定理 `TendstoUniformlyOn.tendstoUniformlyOnFilter`：∀ {α : Type u_1} {β : Type 
u_2} {ι : Type u_4} [inst : UniformSpace β] {F : ι → α → β} {f : α → β} {s : Set
 α}   {p : Filter ι}, TendstoUnif…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `Filter.mem_principal`：∀ {α : Type u_1} {s t : Set α}, s ∈ Filter.princip
al t ↔ t ⊆ s
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s

--- 原说明 ---
Uniform convergence implies pointwise convergence.
-/
theorem TendstoUniformlyOn.tendsto_at (h : TendstoUniformlyOn F f p s) (hx : x ∈ s) :
    Tendsto (fun n => F n x) p <| 𝓝 (f x) :=
  h.tendstoUniformlyOnFilter.tendsto_at
    (le_principal_iff.mpr <| mem_principal.mpr <| singleton_subset_iff.mpr <| hx)

/-- Uniform convergence implies pointwise convergence. -/
/-
**TendstoUniformly.tendsto_at** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoUniformly.tendsto_at (h : TendstoUniformly F f p) (x : α) : Tendsto
 (fun n => F n x) p 𝓝 (f x)
参数：h : TendstoUniformly F f p；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TendstoUniformlyOnFilter.tendsto_at`：TendstoUniformlyOnFilter.tendsto_at
 (h : TendstoUniformlyOnFilter F f p p') (hx : 𝓟 {x} <= p') : Tendsto (fun n => 
F n x) p 𝓝 (f x)
· 使用定理 `TendstoUniformly.tendstoUniformlyOnFilter`：TendstoUniformly.tendstoUnifo
rmlyOnFilter (h : TendstoUniformly F f p) : TendstoUniformlyOnFilter F f p ⊤
· 使用定理 `le_top`：le_top : a <= ⊤

--- 原说明 ---
Uniform convergence implies pointwise convergence.
-/
theorem TendstoUniformly.tendsto_at (h : TendstoUniformly F f p) (x : α) :
    Tendsto (fun n => F n x) p <| 𝓝 (f x) :=
  h.tendstoUniformlyOnFilter.tendsto_at le_top
/-
**TendstoUniformlyOnFilter.mono_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoUniformlyOnFilter.mono_left {p'' : Filter ι} (h : TendstoUniformlyO
nFilter F f p p') (hp : p'' <= p) : TendstoUniformlyOnFilter F f p'' p'
参数：h : TendstoUniformlyOnFilter F f p p'；hp : p'' <= p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `Filter.prod_mono_left`：prod_mono_left (g : Filter β) {f₁ f₂ : Filter α} 
(hf : f₁ <= f₂) : f₁ ×ˢ g <= f₂ ×ˢ g
-/
theorem TendstoUniformlyOnFilter.mono_left {p'' : Filter ι} (h : TendstoUniformlyOnFilter F f p p')
    (hp : p'' ≤ p) : TendstoUniformlyOnFilter F f p'' p' := fun u hu =>
  (h u hu).filter_mono (p'.prod_mono_left hp)
/-
**TendstoUniformlyOnFilter.mono_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoUniformlyOnFilter.mono_right {p'' : Filter α} (h : TendstoUniformly
OnFilter F f p p') (hp : p'' <= p') : TendstoUniformlyOnFilter F f p p''
参数：h : TendstoUniformlyOnFilter F f p p'；hp : p'' <= p'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `Filter.prod_mono_right`：prod_mono_right (f : Filter α) {g₁ g₂ : Filter β
} (hf : g₁ <= g₂) : f ×ˢ g₁ <= f ×ˢ g₂
-/
theorem TendstoUniformlyOnFilter.mono_right {p'' : Filter α} (h : TendstoUniformlyOnFilter F f p p')
    (hp : p'' ≤ p') : TendstoUniformlyOnFilter F f p p'' := fun u hu =>
  (h u hu).filter_mono (p.prod_mono_right hp)
/-
**TendstoUniformlyOn.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoUniformlyOn.mono (h : TendstoUniformlyOn F f p s) (h' : s' subseteq
 s) : TendstoUniformlyOn F f p s'
参数：h : TendstoUniformlyOn F f p s；h' : s' subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendstoUniformlyOn_iff_tendstoUniformlyOnFilter`：tendstoUniformlyOn_iff_
tendstoUniformlyOnFilter : TendstoUniformlyOn F f p s ↔ TendstoUniformlyOnFilter
 F f p (𝓟 s)
· 使用定理 `TendstoUniformlyOnFilter.mono_right`：TendstoUniformlyOnFilter.mono_right
 {p'' : Filter α} (h : TendstoUniformlyOnFilter F f p p') (hp : p'' <= p') : Ten
dstoUniformlyOnFilter F f…
· 使用定理 `TendstoUniformlyOn.tendstoUniformlyOnFilter`：∀ {α : Type u_1} {β : Type 
u_2} {ι : Type u_4} [inst : UniformSpace β] {F : ι → α → β} {f : α → β} {s : Set
 α}   {p : Filter ι}, TendstoUnif…
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `Filter.mem_principal`：∀ {α : Type u_1} {s t : Set α}, s ∈ Filter.princip
al t ↔ t ⊆ s
-/
theorem TendstoUniformlyOn.mono (h : TendstoUniformlyOn F f p s) (h' : s' ⊆ s) :
    TendstoUniformlyOn F f p s' :=
  tendstoUniformlyOn_iff_tendstoUniformlyOnFilter.mpr
    (h.tendstoUniformlyOnFilter.mono_right (le_principal_iff.mpr <| mem_principal.mpr h'))
/-
**TendstoUniformlyOnFilter.congr_inseparable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoUniformlyOnFilter.congr_inseparable {F' : ι -> α -> β} (hf : Tendst
oUniformlyOnFilter F f p p') (hff' : forallᶠ n : ι × α in p ×ˢ p', Inseparable (
F n.fst n.snd) (F' n.fst n.snd)) : TendstoUniformlyOnFilter F' f p p'
参数：hf : TendstoUniformlyOnFilter F f p p'；hff' : forallᶠ n : ι × α in p ×ˢ p', I
nseparable (F n.fst n.snd) (F' n.fst n.snd)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendstoUniformlyOnFilter_iff_tendsto`：tendstoUniformlyOnFilter_iff_tends
to : TendstoUniformlyOnFilter F f p p' ↔ Tendsto (fun q : ι × α => (f q.2, F q.1
 q.2)) (p ×ˢ p') (𝓤 β)
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `uniformity_hasBasis_open`：uniformity_hasBasis_open : HasBasis (𝓤 α) (fun
 V : SetRel α α => V in 𝓤 α ∧ IsOpen V) id
· 使用定理 `Filter.Eventually.congr`：∀ {α : Type u} {f : Filter α} {p q : α → Prop},
   (∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x ↔ q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Inseparable.mem_open_iff`：mem_open_iff (h : x ~ᵢ y) (hs : IsOpen s) : x 
in s ↔ y in s
· 使用定理 `Inseparable.prod`：Inseparable.prod {x₁ x₂ : X} {y₁ y₂ : Y} (hx : x₁ ~ᵢ x
₂) (hy : y₁ ~ᵢ y₂) : (x₁, y₁) ~ᵢ (x₂, y₂)
· 使用定理 `Inseparable.rfl`：rfl : x ~ᵢ x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem TendstoUniformlyOnFilter.congr_inseparable {F' : ι → α → β}
    (hf : TendstoUniformlyOnFilter F f p p')
    (hff' : ∀ᶠ n : ι × α in p ×ˢ p', Inseparable (F n.fst n.snd) (F' n.fst n.snd)) :
    TendstoUniformlyOnFilter F' f p p' := by
  rw [tendstoUniformlyOnFilter_iff_tendsto, uniformity_hasBasis_open.tendsto_right_iff] at hf ⊢
  exact fun i hi => (hf i hi).congr (hff'.mono fun x hx =>
    (Inseparable.rfl.prod hx).mem_open_iff hi.2)
/-
**TendstoUniformlyOnFilter.congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoUniformlyOnFilter.congr {F' : ι -> α -> β} (hf : TendstoUniformlyOn
Filter F f p p') (hff' : forallᶠ n : ι × α in p ×ˢ p', F n.fst n.snd = F' n.fst 
n.snd) : TendstoUniformlyOnFilter F' f p p'
参数：hf : TendstoUniformlyOnFilter F f p p'；hff' : forallᶠ n : ι × α in p ×ˢ p', F
 n.fst n.snd = F' n.fst n.snd。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TendstoUniformlyOnFilter.congr_inseparable`：TendstoUniformlyOnFilter.con
gr_inseparable {F' : ι -> α -> β} (hf : TendstoUniformlyOnFilter F f p p') (hff'
 : forallᶠ n : ι × α in p ×ˢ p',…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Inseparable.of_eq`：of_eq (e : x = y) : Inseparable x y
-/
theorem TendstoUniformlyOnFilter.congr {F' : ι → α → β} (hf : TendstoUniformlyOnFilter F f p p')
    (hff' : ∀ᶠ n : ι × α in p ×ˢ p', F n.fst n.snd = F' n.fst n.snd) :
    TendstoUniformlyOnFilter F' f p p' :=
  hf.congr_inseparable (hff'.mono fun _ h => .of_eq h)
/-
**TendstoUniformlyOn.congr_inseparable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoUniformlyOn.congr_inseparable {F' : ι -> α -> β} (hf : TendstoUnifo
rmlyOn F f p s) (hff' : forallᶠ n in p, forall x in s, Inseparable (F n x) (F' n
 x)) : TendstoUniformlyOn F' f p s
参数：hf : TendstoUniformlyOn F f p s；hff' : forallᶠ n in p, forall x in s, Insepar
able (F n x) (F' n x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendstoUniformlyOn_iff_tendstoUniformlyOnFilter`：tendstoUniformlyOn_iff_
tendstoUniformlyOnFilter : TendstoUniformlyOn F f p s ↔ TendstoUniformlyOnFilter
 F f p (𝓟 s)
· 使用定理 `TendstoUniformlyOnFilter.congr_inseparable`：TendstoUniformlyOnFilter.con
gr_inseparable {F' : ι -> α -> β} (hf : TendstoUniformlyOnFilter F f p p') (hff'
 : forallᶠ n : ι × α in p ×ˢ p',…
· 使用定理 `Filter.eventually_prod_principal_iff`：eventually_prod_principal_iff {p :
 α × β -> Prop} {s : Set β} : (forallᶠ x : α × β in f ×ˢ 𝓟 s, p x) ↔ forallᶠ x :
 α in f, forall y : β, y i…
-/
theorem TendstoUniformlyOn.congr_inseparable {F' : ι → α → β} (hf : TendstoUniformlyOn F f p s)
    (hff' : ∀ᶠ n in p, ∀ x ∈ s, Inseparable (F n x) (F' n x)) : TendstoUniformlyOn F' f p s := by
  rw [tendstoUniformlyOn_iff_tendstoUniformlyOnFilter] at hf ⊢
  refine hf.congr_inseparable ?_
  rwa [eventually_prod_principal_iff]
/-
**TendstoUniformlyOn.congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoUniformlyOn.congr {F' : ι -> α -> β} (hf : TendstoUniformlyOn F f p
 s) (hff' : forallᶠ n in p, Set.EqOn (F n) (F' n) s) : TendstoUniformlyOn F' f p
 s
参数：hf : TendstoUniformlyOn F f p s；hff' : forallᶠ n in p, Set.EqOn (F n) (F' n) 
s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TendstoUniformlyOn.congr_inseparable`：TendstoUniformlyOn.congr_inseparab
le {F' : ι -> α -> β} (hf : TendstoUniformlyOn F f p s) (hff' : forallᶠ n in p, 
forall x in s, Inseparable…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Inseparable.of_eq`：of_eq (e : x = y) : Inseparable x y
-/
theorem TendstoUniformlyOn.congr {F' : ι → α → β} (hf : TendstoUniformlyOn F f p s)
    (hff' : ∀ᶠ n in p, Set.EqOn (F n) (F' n) s) : TendstoUniformlyOn F' f p s :=
  hf.congr_inseparable (hff'.mono fun _ h _ hx => .of_eq (h hx))
/-
**tendstoUniformly_congr_inseparable** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendstoUniformly_congr_inseparable {F' : ι -> α -> β} (hF : forallᶠ x in p
, forall y, Inseparable (F x y) (F' x y)) : TendstoUniformly F f p ↔ TendstoUnif
ormly F' f p
参数：hF : forallᶠ x in p, forall y, Inseparable (F x y) (F' x y)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tendstoUniformlyOn_univ`：tendstoUniformlyOn_univ : TendstoUniformlyOn F 
f p univ ↔ TendstoUniformly F f p
· 使用定理 `TendstoUniformlyOn.congr_inseparable`：TendstoUniformlyOn.congr_inseparab
le {F' : ι -> α -> β} (hf : TendstoUniformlyOn F f p s) (hff' : forallᶠ n in p, 
forall x in s, Inseparable…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Inseparable.symm`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X}
, Inseparable x y → Inseparable y x
-/
lemma tendstoUniformly_congr_inseparable {F' : ι → α → β}
    (hF : ∀ᶠ x in p, ∀ y, Inseparable (F x y) (F' x y)) :
    TendstoUniformly F f p ↔ TendstoUniformly F' f p := by
  rw [← tendstoUniformlyOn_univ, ← tendstoUniformlyOn_univ]
  exact ⟨fun h => h.congr_inseparable (hF.mono fun _ hx y _ => hx y),
    fun h => h.congr_inseparable (hF.mono fun _ hx y _ => (hx y).symm)⟩
/-
**tendstoUniformly_congr** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendstoUniformly_congr {F' : ι -> α -> β} (hF : F =ᶠ[p] F') : TendstoUnifo
rmly F f p ↔ TendstoUniformly F' f p
参数：hF : F =ᶠ[p] F'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `tendstoUniformly_congr_inseparable`：tendstoUniformly_congr_inseparable {
F' : ι -> α -> β} (hF : forallᶠ x in p, forall y, Inseparable (F x y) (F' x y)) 
: TendstoUniformly F f p…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Inseparable.of_eq`：of_eq (e : x = y) : Inseparable x y
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
-/
lemma tendstoUniformly_congr {F' : ι → α → β} (hF : F =ᶠ[p] F') :
    TendstoUniformly F f p ↔ TendstoUniformly F' f p :=
  tendstoUniformly_congr_inseparable (hF.mono fun _ hx y => .of_eq (congrFun hx y))
/-
**TendstoUniformlyOn.congr_inseparable_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoUniformlyOn.congr_inseparable_right {g : α -> β} (hf : TendstoUnifo
rmlyOn F f p s) (hfg : forall x in s, Inseparable (f x) (g x)) : TendstoUniforml
yOn F g p s
参数：hf : TendstoUniformlyOn F f p s；hfg : forall x in s, Inseparable (f x) (g x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendstoUniformlyOn_iff_tendsto`：tendstoUniformlyOn_iff_tendsto : Tendsto
UniformlyOn F f p s ↔ Tendsto (fun q : ι × α => (f q.2, F q.1 q.2)) (p ×ˢ 𝓟 s) (
𝓤 β)
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `uniformity_hasBasis_open`：uniformity_hasBasis_open : HasBasis (𝓤 α) (fun
 V : SetRel α α => V in 𝓤 α ∧ IsOpen V) id
· 使用定理 `forall₂_imp`：forall₂_imp {p q : forall a, β a -> Prop} (h : forall a b, 
p a b -> q a b) : (forall a b, p a b) -> forall a b, q a b
· 使用定理 `Filter.eventually_prod_principal_iff`：eventually_prod_principal_iff {p :
 α × β -> Prop} {s : Set β} : (forallᶠ x : α × β in f ×ˢ 𝓟 s, p x) ↔ forallᶠ x :
 α in f, forall y : β, y i…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Inseparable.mem_open_iff`：mem_open_iff (h : x ~ᵢ y) (hs : IsOpen s) : x 
in s ↔ y in s
· 使用定理 `Inseparable.prod`：Inseparable.prod {x₁ x₂ : X} {y₁ y₂ : Y} (hx : x₁ ~ᵢ x
₂) (hy : y₁ ~ᵢ y₂) : (x₁, y₁) ~ᵢ (x₂, y₂)
· 使用定理 `Inseparable.rfl`：rfl : x ~ᵢ x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem TendstoUniformlyOn.congr_inseparable_right {g : α → β} (hf : TendstoUniformlyOn F f p s)
    (hfg : ∀ x ∈ s, Inseparable (f x) (g x)) : TendstoUniformlyOn F g p s := by
  rw [tendstoUniformlyOn_iff_tendsto, uniformity_hasBasis_open.tendsto_right_iff] at hf ⊢
  refine forall₂_imp (fun i hi hf => ?_) hf
  rw [eventually_prod_principal_iff] at hf ⊢
  exact hf.mono fun x hx y hy => (((hfg y hy).prod .rfl).mem_open_iff hi.2).mp (hx y hy)
/-
**TendstoUniformlyOn.congr_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoUniformlyOn.congr_right {g : α -> β} (hf : TendstoUniformlyOn F f p
 s) (hfg : EqOn f g s) : TendstoUniformlyOn F g p s
参数：hf : TendstoUniformlyOn F f p s；hfg : EqOn f g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TendstoUniformlyOn.congr_inseparable_right`：TendstoUniformlyOn.congr_ins
eparable_right {g : α -> β} (hf : TendstoUniformlyOn F f p s) (hfg : forall x in
 s, Inseparable (f x) (g x)) : T…
· 使用定理 `Inseparable.of_eq`：of_eq (e : x = y) : Inseparable x y
-/
theorem TendstoUniformlyOn.congr_right {g : α → β} (hf : TendstoUniformlyOn F f p s)
    (hfg : EqOn f g s) : TendstoUniformlyOn F g p s :=
  hf.congr_inseparable_right fun _ hx => .of_eq (hfg hx)
/-
**TendstoUniformly.tendstoUniformlyOn** 是 Mathlib 中的一个定理，位于命名空间 `TendstoUniforml
y`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Type u_4} [inst : UniformSpace β] {F 
: ι → α → β} {f : α → β} {s : Set α}   {p : Filter ι}, TendstoUniformly F f p → 
TendstoUniformlyOn F f p s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TendstoUniformlyOn.mono`：TendstoUniformlyOn.mono (h : TendstoUniformlyOn
 F f p s) (h' : s' subseteq s) : TendstoUniformlyOn F f p s'
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendstoUniformlyOn_univ`：tendstoUniformlyOn_univ : TendstoUniformlyOn F 
f p univ ↔ TendstoUniformly F f p
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
protected theorem TendstoUniformly.tendstoUniformlyOn (h : TendstoUniformly F f p) :
    TendstoUniformlyOn F f p s :=
  (tendstoUniformlyOn_univ.2 h).mono (subset_univ s)

/-- Composing on the right by a function preserves uniform convergence on a filter -/
/-
**TendstoUniformlyOnFilter.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoUniformlyOnFilter.comp (h : TendstoUniformlyOnFilter F f p p') (g :
 γ -> α) : TendstoUniformlyOnFilter (fun n => F n ∘ g) (f ∘ g) p (p'.comap g)
参数：h : TendstoUniformlyOnFilter F f p p'；g : γ -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendstoUniformlyOnFilter_iff_tendsto`：tendstoUniformlyOnFilter_iff_tends
to : TendstoUniformlyOnFilter F f p p' ↔ Tendsto (fun q : ι × α => (f q.2, F q.1
 q.2)) (p ×ˢ p') (𝓤 β)
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.Tendsto.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {
δ : Type u_6} {f : α → γ} {g : β → δ} {a : Filter α} {b : Filter β}   {c : Filte
r γ} {d : Fi…
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `Filter.tendsto_comap`：tendsto_comap {f : α -> β} {x : Filter β} : Tendst
o f (comap f x) x

--- 原说明 ---
Composing on the right by a function preserves uniform convergence on a filter
-/
theorem TendstoUniformlyOnFilter.comp (h : TendstoUniformlyOnFilter F f p p') (g : γ → α) :
    TendstoUniformlyOnFilter (fun n => F n ∘ g) (f ∘ g) p (p'.comap g) := by
  rw [tendstoUniformlyOnFilter_iff_tendsto] at h ⊢
  exact h.comp (tendsto_id.prodMap tendsto_comap)

/-- Composing on the right by a function preserves uniform convergence on a set -/
/-
**TendstoUniformlyOn.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoUniformlyOn.comp (h : TendstoUniformlyOn F f p s) (g : γ -> α) : Te
ndstoUniformlyOn (fun n => F n ∘ g) (f ∘ g) p (g ⁻¹' s)
参数：h : TendstoUniformlyOn F f p s；g : γ -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendstoUniformlyOn_iff_tendstoUniformlyOnFilter`：tendstoUniformlyOn_iff_
tendstoUniformlyOnFilter : TendstoUniformlyOn F f p s ↔ TendstoUniformlyOnFilter
 F f p (𝓟 s)
· 使用定理 `Filter.comap_principal`：comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 
(m ⁻¹' t)
· 使用定理 `TendstoUniformlyOnFilter.comp`：TendstoUniformlyOnFilter.comp (h : Tendst
oUniformlyOnFilter F f p p') (g : γ -> α) : TendstoUniformlyOnFilter (fun n => F
 n ∘ g) (f ∘ g) p (…

--- 原说明 ---
Composing on the right by a function preserves uniform convergence on a set
-/
theorem TendstoUniformlyOn.comp (h : TendstoUniformlyOn F f p s) (g : γ → α) :
    TendstoUniformlyOn (fun n => F n ∘ g) (f ∘ g) p (g ⁻¹' s) := by
  rw [tendstoUniformlyOn_iff_tendstoUniformlyOnFilter] at h ⊢
  simpa [TendstoUniformlyOn, comap_principal] using TendstoUniformlyOnFilter.comp h g

/-- Composing on the right by a function preserves uniform convergence -/
/-
**TendstoUniformly.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoUniformly.comp (h : TendstoUniformly F f p) (g : γ -> α) : TendstoU
niformly (fun n => F n ∘ g) (f ∘ g) p
参数：h : TendstoUniformly F f p；g : γ -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendstoUniformly_iff_tendstoUniformlyOnFilter`：tendstoUniformly_iff_tend
stoUniformlyOnFilter : TendstoUniformly F f p ↔ TendstoUniformlyOnFilter F f p ⊤
· 使用定理 `Filter.comap_top`：∀ {α : Type u_1} {β : Type u_2} {m : α → β}, Filter.co
map m ⊤ = ⊤
· 使用定理 `TendstoUniformlyOnFilter.comp`：TendstoUniformlyOnFilter.comp (h : Tendst
oUniformlyOnFilter F f p p') (g : γ -> α) : TendstoUniformlyOnFilter (fun n => F
 n ∘ g) (f ∘ g) p (…

--- 原说明 ---
Composing on the right by a function preserves uniform convergence
-/
theorem TendstoUniformly.comp (h : TendstoUniformly F f p) (g : γ → α) :
    TendstoUniformly (fun n => F n ∘ g) (f ∘ g) p := by
  rw [tendstoUniformly_iff_tendstoUniformlyOnFilter] at h ⊢
  simpa [principal_univ, comap_principal] using h.comp g

/-- Composing on the left by a uniformly continuous function preserves
  uniform convergence on a filter -/
/-
**UniformContinuous.comp_tendstoUniformlyOnFilter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformContinuous.comp_tendstoUniformlyOnFilter [UniformSpace γ] {g : β ->
 γ} (hg : UniformContinuous g) (h : TendstoUniformlyOnFilter F f p p') : Tendsto
UniformlyOnFilter (fun i => g ∘ F i) (g ∘ f) p p'
参数：hg : UniformContinuous g；h : TendstoUniformlyOnFilter F f p p'。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing on the left by a uniformly continuous function preserves
  uniform convergence on a filter
-/
theorem UniformContinuous.comp_tendstoUniformlyOnFilter [UniformSpace γ] {g : β → γ}
    (hg : UniformContinuous g) (h : TendstoUniformlyOnFilter F f p p') :
    TendstoUniformlyOnFilter (fun i => g ∘ F i) (g ∘ f) p p' := fun _u hu => h _ (hg hu)

/-- Composing on the left by a uniformly continuous function preserves
  uniform convergence on a set -/
/-
**UniformContinuous.comp_tendstoUniformlyOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformContinuous.comp_tendstoUniformlyOn [UniformSpace γ] {g : β -> γ} (h
g : UniformContinuous g) (h : TendstoUniformlyOn F f p s) : TendstoUniformlyOn (
fun i => g ∘ F i) (g ∘ f) p s
参数：hg : UniformContinuous g；h : TendstoUniformlyOn F f p s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing on the left by a uniformly continuous function preserves
  uniform convergence on a set
-/
theorem UniformContinuous.comp_tendstoUniformlyOn [UniformSpace γ] {g : β → γ}
    (hg : UniformContinuous g) (h : TendstoUniformlyOn F f p s) :
    TendstoUniformlyOn (fun i => g ∘ F i) (g ∘ f) p s := fun _u hu => h _ (hg hu)

/-- Composing on the left by a uniformly continuous function preserves uniform convergence -/
/-
**UniformContinuous.comp_tendstoUniformly** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformContinuous.comp_tendstoUniformly [UniformSpace γ] {g : β -> γ} (hg 
: UniformContinuous g) (h : TendstoUniformly F f p) : TendstoUniformly (fun i =>
 g ∘ F i) (g ∘ f) p
参数：hg : UniformContinuous g；h : TendstoUniformly F f p。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing on the left by a uniformly continuous function preserves uniform conve
rgence
-/
theorem UniformContinuous.comp_tendstoUniformly [UniformSpace γ] {g : β → γ}
    (hg : UniformContinuous g) (h : TendstoUniformly F f p) :
    TendstoUniformly (fun i => g ∘ F i) (g ∘ f) p := fun _u hu => h _ (hg hu)
/-
**TendstoUniformlyOnFilter.prodMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoUniformlyOnFilter.prodMap {ι' α' β' : Type*} [UniformSpace β'] {F' 
: ι' -> α' -> β'} {f' : α' -> β'} {q : Filter ι'} {q' : Filter α'} (h : TendstoU
niformlyOnFilter F f p p') (h' : TendstoUniformlyOnFilter F' f' q q') : TendstoU
niformlyOnFilter (fun i : ι × ι' => Prod.map (F i.1) (F' i.2)) (Prod.map f f') (
p ×ˢ q) (p' ×ˢ q')
参数：h : TendstoUniformlyOnFilter F f p p'；h' : TendstoUniformlyOnFilter F' f' q q
'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendstoUniformlyOnFilter_iff_tendsto`：tendstoUniformlyOnFilter_iff_tends
to : TendstoUniformlyOnFilter F f p p' ↔ Tendsto (fun q : ι × α => (f q.2, F q.1
 q.2)) (p ×ˢ p') (𝓤 β)
· 使用定理 `uniformity_prod_eq_comap_prod`：uniformity_prod_eq_comap_prod [UniformSpa
ce α] [UniformSpace β] : 𝓤 (α × β) = comap (fun p : (α × β) × α × β => ((p.1.1, 
p.2.1), (p.1.2, p.2…
· 使用定理 `Filter.tendsto_comap_iff`：tendsto_comap_iff {f : α -> β} {g : β -> γ} {a
 : Filter α} {c : Filter γ} : Tendsto f a (c.comap g) ↔ Tendsto (g ∘ f) a c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.map_swap4_prod`：map_swap4_prod {h : Filter γ} {k : Filter δ} : ma
p (fun p : (α × β) × γ × δ => ((p.1.1, p.2.1), (p.1.2, p.2.2))) ((f ×ˢ g) ×ˢ (h 
×ˢ k)) = (f…
· 使用定理 `Filter.tendsto_map'_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{f : β → γ} {g : α → β} {x : Filter α} {y : Filter γ},   Filter.Tendsto f (Filte
r.map g x) y …
· 使用定理 `Filter.Tendsto.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {
δ : Type u_6} {f : α → γ} {g : β → δ} {a : Filter α} {b : Filter β}   {c : Filte
r γ} {d : Fi…
-/
theorem TendstoUniformlyOnFilter.prodMap {ι' α' β' : Type*} [UniformSpace β'] {F' : ι' → α' → β'}
    {f' : α' → β'} {q : Filter ι'} {q' : Filter α'} (h : TendstoUniformlyOnFilter F f p p')
    (h' : TendstoUniformlyOnFilter F' f' q q') :
    TendstoUniformlyOnFilter (fun i : ι × ι' => Prod.map (F i.1) (F' i.2)) (Prod.map f f') (p ×ˢ q)
      (p' ×ˢ q') := by
  rw [tendstoUniformlyOnFilter_iff_tendsto] at h h' ⊢
  rw [uniformity_prod_eq_comap_prod, tendsto_comap_iff, ← map_swap4_prod, tendsto_map'_iff]
  simpa using! h.prodMap h'
/-
**TendstoUniformlyOn.prodMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoUniformlyOn.prodMap {ι' α' β' : Type*} [UniformSpace β'] {F' : ι' -
> α' -> β'} {f' : α' -> β'} {p' : Filter ι'} {s' : Set α'} (h : TendstoUniformly
On F f p s) (h' : TendstoUniformlyOn F' f' p' s') : TendstoUniformlyOn (fun i : 
ι × ι' => Prod.map (F i.1) (F' i.2)) (Prod.map f f') (p ×ˢ p') (s ×ˢ s')
参数：h : TendstoUniformlyOn F f p s；h' : TendstoUniformlyOn F' f' p' s'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendstoUniformlyOn_iff_tendstoUniformlyOnFilter`：tendstoUniformlyOn_iff_
tendstoUniformlyOnFilter : TendstoUniformlyOn F f p s ↔ TendstoUniformlyOnFilter
 F f p (𝓟 s)
· 使用定理 `Filter.prod_principal_principal`：prod_principal_principal {s : Set α} {t
 : Set β} : 𝓟 s ×ˢ 𝓟 t = 𝓟 (s ×ˢ t)
· 使用定理 `TendstoUniformlyOnFilter.prodMap`：TendstoUniformlyOnFilter.prodMap {ι' α
' β' : Type*} [UniformSpace β'] {F' : ι' -> α' -> β'} {f' : α' -> β'} {q : Filte
r ι'} {q' : Filter α'}…
-/
theorem TendstoUniformlyOn.prodMap {ι' α' β' : Type*} [UniformSpace β'] {F' : ι' → α' → β'}
    {f' : α' → β'} {p' : Filter ι'} {s' : Set α'} (h : TendstoUniformlyOn F f p s)
    (h' : TendstoUniformlyOn F' f' p' s') :
    TendstoUniformlyOn (fun i : ι × ι' => Prod.map (F i.1) (F' i.2)) (Prod.map f f') (p ×ˢ p')
      (s ×ˢ s') := by
  rw [tendstoUniformlyOn_iff_tendstoUniformlyOnFilter] at h h' ⊢
  simpa only [prod_principal_principal] using h.prodMap h'
/-
**TendstoUniformly.prodMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoUniformly.prodMap {ι' α' β' : Type*} [UniformSpace β'] {F' : ι' -> 
α' -> β'} {f' : α' -> β'} {p' : Filter ι'} (h : TendstoUniformly F f p) (h' : Te
ndstoUniformly F' f' p') : TendstoUniformly (fun i : ι × ι' => Prod.map (F i.1) 
(F' i.2)) (Prod.map f f') (p ×ˢ p')
参数：h : TendstoUniformly F f p；h' : TendstoUniformly F' f' p'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tendstoUniformlyOn_univ`：tendstoUniformlyOn_univ : TendstoUniformlyOn F 
f p univ ↔ TendstoUniformly F f p
· 使用定理 `Set.univ_prod_univ`：univ_prod_univ : @univ α ×ˢ @univ β = univ
· 使用定理 `TendstoUniformlyOn.prodMap`：TendstoUniformlyOn.prodMap {ι' α' β' : Type*
} [UniformSpace β'] {F' : ι' -> α' -> β'} {f' : α' -> β'} {p' : Filter ι'} {s' :
 Set α'} (h : Te…
-/
theorem TendstoUniformly.prodMap {ι' α' β' : Type*} [UniformSpace β'] {F' : ι' → α' → β'}
    {f' : α' → β'} {p' : Filter ι'} (h : TendstoUniformly F f p) (h' : TendstoUniformly F' f' p') :
    TendstoUniformly (fun i : ι × ι' => Prod.map (F i.1) (F' i.2)) (Prod.map f f') (p ×ˢ p') := by
  rw [← tendstoUniformlyOn_univ, ← univ_prod_univ] at *
  exact h.prodMap h'
/-
**TendstoUniformlyOnFilter.prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoUniformlyOnFilter.prodMk {ι' β' : Type*} [UniformSpace β'] {F' : ι'
 -> α -> β'} {f' : α -> β'} {q : Filter ι'} (h : TendstoUniformlyOnFilter F f p 
p') (h' : TendstoUniformlyOnFilter F' f' q p') : TendstoUniformlyOnFilter (fun (
i : ι × ι') a => (F i.1 a, F' i.2 a)) (fun a => (f a, f' a)) (p ×ˢ q) p'
参数：h : TendstoUniformlyOnFilter F f p p'；h' : TendstoUniformlyOnFilter F' f' q p
'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.diag_of_prod_right`：∀ {α : Type u_1} {γ : Type u_3} {f
 : Filter α} {g : Filter γ} {p : α × γ × γ → Prop},   (∀ᶠ (x : α × γ × γ) in f ×
ˢ g ×ˢ g, p x) → ∀ᶠ (x : α…
· 使用定理 `TendstoUniformlyOnFilter.prodMap`：TendstoUniformlyOnFilter.prodMap {ι' α
' β' : Type*} [UniformSpace β'] {F' : ι' -> α' -> β'} {f' : α' -> β'} {q : Filte
r ι'} {q' : Filter α'}…
-/
theorem TendstoUniformlyOnFilter.prodMk {ι' β' : Type*} [UniformSpace β'] {F' : ι' → α → β'}
    {f' : α → β'} {q : Filter ι'} (h : TendstoUniformlyOnFilter F f p p')
    (h' : TendstoUniformlyOnFilter F' f' q p') :
    TendstoUniformlyOnFilter (fun (i : ι × ι') a => (F i.1 a, F' i.2 a)) (fun a => (f a, f' a))
      (p ×ˢ q) p' :=
  fun u hu => ((h.prodMap h') u hu).diag_of_prod_right
/-
**TendstoUniformlyOn.prodMk** 是 Mathlib 中的一个定理，位于命名空间 `TendstoUniformlyOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {ι : Type u_4} [inst : UniformSpace β] {F 
: ι → α → β} {f : α → β} {s : Set α}   {p : Filter ι} {ι' : Type u_5} {β' : Type
 u_6} [inst_1 : UniformSpace β'] {F' : ι' → α → β'} {f' : α → β'}   {p' : Filter
 ι'},   TendstoUniformlyOn F f p s →     TendstoUniformlyOn F' f' p' s →       T
endstoUniformlyOn (fun i a => (F i.1 a, F' i.2 a)) (fun a => (f a, f' a)) (p ×ˢ 
p') s
参数：fun i a => (F i.1 a, F' i.2 a)；fun a => (f a, f' a)；p ×ˢ p'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
· 使用定理 `TendstoUniformlyOn.comp`：TendstoUniformlyOn.comp (h : TendstoUniformlyOn
 F f p s) (g : γ -> α) : TendstoUniformlyOn (fun n => F n ∘ g) (f ∘ g) p (g ⁻¹' 
s)
· 使用定理 `TendstoUniformlyOn.prodMap`：TendstoUniformlyOn.prodMap {ι' α' β' : Type*
} [UniformSpace β'] {F' : ι' -> α' -> β'} {f' : α' -> β'} {p' : Filter ι'} {s' :
 Set α'} (h : Te…
-/
protected theorem TendstoUniformlyOn.prodMk {ι' β' : Type*} [UniformSpace β'] {F' : ι' → α → β'}
    {f' : α → β'} {p' : Filter ι'} (h : TendstoUniformlyOn F f p s)
    (h' : TendstoUniformlyOn F' f' p' s) :
    TendstoUniformlyOn (fun (i : ι × ι') a => (F i.1 a, F' i.2 a)) (fun a => (f a, f' a)) (p ×ˢ p')
      s :=
  (congr_arg _ s.inter_self).mp ((h.prodMap h').comp Function.diag)
/-
**TendstoUniformly.prodMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoUniformly.prodMk {ι' β' : Type*} [UniformSpace β'] {F' : ι' -> α ->
 β'} {f' : α -> β'} {p' : Filter ι'} (h : TendstoUniformly F f p) (h' : TendstoU
niformly F' f' p') : TendstoUniformly (fun (i : ι × ι') a => (F i.1 a, F' i.2 a)
) (fun a => (f a, f' a)) (p ×ˢ p')
参数：h : TendstoUniformly F f p；h' : TendstoUniformly F' f' p'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TendstoUniformly.comp`：TendstoUniformly.comp (h : TendstoUniformly F f p
) (g : γ -> α) : TendstoUniformly (fun n => F n ∘ g) (f ∘ g) p
· 使用定理 `TendstoUniformly.prodMap`：TendstoUniformly.prodMap {ι' α' β' : Type*} [U
niformSpace β'] {F' : ι' -> α' -> β'} {f' : α' -> β'} {p' : Filter ι'} (h : Tend
stoUniformly F…
-/
theorem TendstoUniformly.prodMk {ι' β' : Type*} [UniformSpace β'] {F' : ι' → α → β'} {f' : α → β'}
    {p' : Filter ι'} (h : TendstoUniformly F f p) (h' : TendstoUniformly F' f' p') :
    TendstoUniformly (fun (i : ι × ι') a => (F i.1 a, F' i.2 a)) (fun a => (f a, f' a)) (p ×ˢ p') :=
  (h.prodMap h').comp Function.diag

/-- Uniform convergence on a filter `p'` to a constant function is equivalent to convergence in
`p ×ˢ p'`. -/
/-
**tendsto_prod_filter_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_prod_filter_iff {c : β} : Tendsto ↿F (p ×ˢ p') (𝓝 c) ↔ TendstoUnif
ormlyOnFilter F (fun _ => c) p p'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_eq_comap_uniformity`：nhds_eq_comap_uniformity {x : α} : 𝓝 x = (𝓤 α)
.comap (Prod.mk x)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Uniform convergence on a filter `p'` to a constant function is equivalent to con
vergence in
`p ×ˢ p'`.
-/
theorem tendsto_prod_filter_iff {c : β} :
    Tendsto ↿F (p ×ˢ p') (𝓝 c) ↔ TendstoUniformlyOnFilter F (fun _ => c) p p' := by
  simp_rw [nhds_eq_comap_uniformity, tendsto_comap_iff]
  rfl

/-- Uniform convergence on a set `s` to a constant function is equivalent to convergence in
`p ×ˢ 𝓟 s`. -/
/-
**tendsto_prod_principal_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_prod_principal_iff {c : β} : Tendsto ↿F (p ×ˢ 𝓟 s) (𝓝 c) ↔ Tendsto
UniformlyOn F (fun _ => c) p s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendstoUniformlyOn_iff_tendstoUniformlyOnFilter`：tendstoUniformlyOn_iff_
tendstoUniformlyOnFilter : TendstoUniformlyOn F f p s ↔ TendstoUniformlyOnFilter
 F f p (𝓟 s)
· 使用定理 `tendsto_prod_filter_iff`：tendsto_prod_filter_iff {c : β} : Tendsto ↿F (p
 ×ˢ p') (𝓝 c) ↔ TendstoUniformlyOnFilter F (fun _ => c) p p'

--- 原说明 ---
Uniform convergence on a set `s` to a constant function is equivalent to converg
ence in
`p ×ˢ 𝓟 s`.
-/
theorem tendsto_prod_principal_iff {c : β} :
    Tendsto ↿F (p ×ˢ 𝓟 s) (𝓝 c) ↔ TendstoUniformlyOn F (fun _ => c) p s := by
  rw [tendstoUniformlyOn_iff_tendstoUniformlyOnFilter]
  exact tendsto_prod_filter_iff

/-- Uniform convergence to a constant function is equivalent to convergence in `p ×ˢ ⊤`. -/
/-
**tendsto_prod_top_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_prod_top_iff {c : β} : Tendsto ↿F (p ×ˢ ⊤) (𝓝 c) ↔ TendstoUniforml
y F (fun _ => c) p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendstoUniformly_iff_tendstoUniformlyOnFilter`：tendstoUniformly_iff_tend
stoUniformlyOnFilter : TendstoUniformly F f p ↔ TendstoUniformlyOnFilter F f p ⊤
· 使用定理 `tendsto_prod_filter_iff`：tendsto_prod_filter_iff {c : β} : Tendsto ↿F (p
 ×ˢ p') (𝓝 c) ↔ TendstoUniformlyOnFilter F (fun _ => c) p p'

--- 原说明 ---
Uniform convergence to a constant function is equivalent to convergence in `p ×ˢ
 ⊤`.
-/
theorem tendsto_prod_top_iff {c : β} :
    Tendsto ↿F (p ×ˢ ⊤) (𝓝 c) ↔ TendstoUniformly F (fun _ => c) p := by
  rw [tendstoUniformly_iff_tendstoUniformlyOnFilter]
  exact tendsto_prod_filter_iff

/-- Uniform convergence on the empty set is vacuously true -/
/-
**tendstoUniformlyOn_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendstoUniformlyOn_empty : TendstoUniformlyOn F f p ∅
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Uniform convergence on the empty set is vacuously true
-/
theorem tendstoUniformlyOn_empty : TendstoUniformlyOn F f p ∅ := fun u _ => by simp

/-- Uniform convergence on a singleton is equivalent to regular convergence -/
/-
**tendstoUniformlyOn_singleton_iff_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendstoUniformlyOn_singleton_iff_tendsto : TendstoUniformlyOn F f p {x} ↔ 
Tendsto (fun n : ι => F n x) p (𝓝 (f x))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.principal_singleton`：principal_singleton (a : α) : 𝓟 {a} = pure a
· 使用定理 `Filter.prod_pure`：prod_pure {b : β} : f ×ˢ pure b = map (fun a => (a, b)
) f
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Uniform convergence on a singleton is equivalent to regular convergence
-/
theorem tendstoUniformlyOn_singleton_iff_tendsto :
    TendstoUniformlyOn F f p {x} ↔ Tendsto (fun n : ι => F n x) p (𝓝 (f x)) := by
  simp_rw [tendstoUniformlyOn_iff_tendsto, Uniform.tendsto_nhds_right, tendsto_def]
  exact forall₂_congr fun u _ => by simp [preimage]

/-- If a sequence `g` converges to some `b`, then the sequence of constant functions
`fun n ↦ fun a ↦ g n` converges to the constant function `fun a ↦ b` on any set `s`. -/
/-
**Filter.Tendsto.tendstoUniformlyOnFilter_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.tendstoUniformlyOnFilter_const {g : ι -> β} {b : β} (hg : T
endsto g p (𝓝 b)) (p' : Filter α) : TendstoUniformlyOnFilter (fun n : ι => fun _
 : α => g n) (fun _ : α => b) p p'
参数：hg : Tendsto g p (𝓝 b)；p' : Filter α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_eq_comap_uniformity`：nhds_eq_comap_uniformity {x : α} : 𝓝 x = (𝓤 α)
.comap (Prod.mk x)
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.tendsto_fst`：tendsto_fst : Tendsto Prod.fst (f ×ˢ g) f

--- 原说明 ---
If a sequence `g` converges to some `b`, then the sequence of constant functions
`fun n ↦ fun a ↦ g n` converges to the constant function `fun a ↦ b` on any set 
`s`.
-/
theorem Filter.Tendsto.tendstoUniformlyOnFilter_const {g : ι → β} {b : β} (hg : Tendsto g p (𝓝 b))
    (p' : Filter α) :
    TendstoUniformlyOnFilter (fun n : ι => fun _ : α => g n) (fun _ : α => b) p p' := by
  simpa only [nhds_eq_comap_uniformity, tendsto_comap_iff] using! hg.comp (tendsto_fst (g := p'))

/-- If a sequence `g` converges to some `b`, then the sequence of constant functions
`fun n ↦ fun a ↦ g n` converges to the constant function `fun a ↦ b` on any set `s`. -/
/-
**Filter.Tendsto.tendstoUniformlyOn_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.tendstoUniformlyOn_const {g : ι -> β} {b : β} (hg : Tendsto
 g p (𝓝 b)) (s : Set α) : TendstoUniformlyOn (fun n : ι => fun _ : α => g n) (fu
n _ : α => b) p s
参数：hg : Tendsto g p (𝓝 b)；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendstoUniformlyOn_iff_tendstoUniformlyOnFilter`：tendstoUniformlyOn_iff_
tendstoUniformlyOnFilter : TendstoUniformlyOn F f p s ↔ TendstoUniformlyOnFilter
 F f p (𝓟 s)
· 使用定理 `Filter.Tendsto.tendstoUniformlyOnFilter_const`：Filter.Tendsto.tendstoUni
formlyOnFilter_const {g : ι -> β} {b : β} (hg : Tendsto g p (𝓝 b)) (p' : Filter 
α) : TendstoUniformlyOnFilter (fun …

--- 原说明 ---
If a sequence `g` converges to some `b`, then the sequence of constant functions
`fun n ↦ fun a ↦ g n` converges to the constant function `fun a ↦ b` on any set 
`s`.
-/
theorem Filter.Tendsto.tendstoUniformlyOn_const {g : ι → β} {b : β} (hg : Tendsto g p (𝓝 b))
    (s : Set α) : TendstoUniformlyOn (fun n : ι => fun _ : α => g n) (fun _ : α => b) p s :=
  tendstoUniformlyOn_iff_tendstoUniformlyOnFilter.mpr (hg.tendstoUniformlyOnFilter_const (𝓟 s))

/-- If a sequence `g` converges to some `b`, then the sequence of constant functions
`fun n ↦ fun a ↦ g n` converges to the constant function `fun a ↦ b`. -/
/-
**Filter.Tendsto.tendstoUniformly_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.tendstoUniformly_const {g : ι -> β} {b : β} (hg : Tendsto g
 p (𝓝 b)) : TendstoUniformly (fun n : ι => fun _ : α => g n) (fun _ : α => b) p
参数：hg : Tendsto g p (𝓝 b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendstoUniformly_iff_tendstoUniformlyOnFilter`：tendstoUniformly_iff_tend
stoUniformlyOnFilter : TendstoUniformly F f p ↔ TendstoUniformlyOnFilter F f p ⊤
· 使用定理 `Filter.Tendsto.tendstoUniformlyOnFilter_const`：Filter.Tendsto.tendstoUni
formlyOnFilter_const {g : ι -> β} {b : β} (hg : Tendsto g p (𝓝 b)) (p' : Filter 
α) : TendstoUniformlyOnFilter (fun …

--- 原说明 ---
If a sequence `g` converges to some `b`, then the sequence of constant functions
`fun n ↦ fun a ↦ g n` converges to the constant function `fun a ↦ b`.
-/
theorem Filter.Tendsto.tendstoUniformly_const {g : ι → β} {b : β} (hg : Tendsto g p (𝓝 b)) :
    TendstoUniformly (fun n : ι => fun _ : α => g n) (fun _ : α => b) p :=
  tendstoUniformly_iff_tendstoUniformlyOnFilter.mpr (hg.tendstoUniformlyOnFilter_const _)
/-
**UniformContinuousOn.tendstoUniformlyOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformContinuousOn.tendstoUniformlyOn [UniformSpace α] [UniformSpace γ] {
U : Set α} {V : Set β} {F : α -> β -> γ} (hF : UniformContinuousOn ↿F (U ×ˢ V)) 
(hU : x in U) : TendstoUniformlyOn F (F x) (𝓝[U] x) V
参数：hF : UniformContinuousOn ↿F (U ×ˢ V)；hU : x in U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendstoUniformlyOn_iff_tendsto`：tendstoUniformlyOn_iff_tendsto : Tendsto
UniformlyOn F f p s ↔ Tendsto (fun q : ι × α => (f q.2, F q.1 q.2)) (p ×ˢ 𝓟 s) (
𝓤 β)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Filter.comap_inf`：∀ {α : Type u_1} {β : Type u_2} {g₁ g₂ : Filter β} {m 
: α → β},   Filter.comap m (g₁ ⊓ g₂) = Filter.comap m g₁ ⊓ Filter.comap m g₂
· 使用定理 `Filter.comap_principal`：comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 
(m ⁻¹' t)
· 使用定理 `inf_assoc`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓ b ⊓
 c = a ⊓ (b ⊓ c)
· 使用定理 `Filter.inf_principal`：inf_principal {s t : Set α} : 𝓟 s ⊓ 𝓟 t = 𝓟 (s int
er t)
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.Tendsto.inf`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x₁ x₂ :
 Filter α} {y₁ y₂ : Filter β},   Filter.Tendsto f x₁ y₁ → Filter.Tendsto f x₂ y₂
 → Filte…
· 使用定理 `nhds_eq_comap_uniformity`：nhds_eq_comap_uniformity {x : α} : 𝓝 x = (𝓤 α)
.comap (Prod.mk x)
· 使用定理 `Filter.comap_comap`：comap_comap {m : γ -> β} {n : β -> α} : comap m (com
ap n f) = comap (n ∘ m) f
· 使用定理 `uniformity_prod_eq_comap_prod`：uniformity_prod_eq_comap_prod [UniformSpa
ce α] [UniformSpace β] : 𝓤 (α × β) = comap (fun p : (α × β) × α × β => ((p.1.1, 
p.2.1), (p.1.2, p.2…
· 使用定理 `Filter.Tendsto.prodMk`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f
 : Filter α} {g : Filter β} {h : Filter γ} {m₁ : α → β} {m₂ : α → γ},   Filter.T
endsto m₁ f…
· 使用定理 `Filter.tendsto_comap`：tendsto_comap {f : α -> β} {x : Filter β} : Tendst
o f (comap f x) x
· 使用定理 `tendsto_diag_uniformity`：tendsto_diag_uniformity (f : β -> α) (l : Filte
r β) : Tendsto (fun x => (f x, f x)) l (𝓤 α)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_principal_principal`：tendsto_principal_principal {f : α -
> β} {s : Set α} {t : Set β} : Tendsto f (𝓟 s) (𝓟 t) ↔ forall a in s, f a in t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem UniformContinuousOn.tendstoUniformlyOn [UniformSpace α] [UniformSpace γ] {U : Set α}
    {V : Set β} {F : α → β → γ} (hF : UniformContinuousOn ↿F (U ×ˢ V)) (hU : x ∈ U) :
    TendstoUniformlyOn F (F x) (𝓝[U] x) V := by
  set φ := fun q : α × β => ((x, q.2), q)
  rw [tendstoUniformlyOn_iff_tendsto]
  change Tendsto (Prod.map ↿F ↿F ∘ φ) (𝓝[U] x ×ˢ 𝓟 V) (𝓤 γ)
  simp only [nhdsWithin, Filter.prod_eq_inf, comap_inf, inf_assoc, comap_principal, inf_principal]
  refine Tendsto.comp hF
    (Tendsto.inf ?_ <| tendsto_principal_principal.2 fun x hx => ⟨⟨hU, hx.2⟩, hx⟩)
  simp only [uniformity_prod_eq_comap_prod, tendsto_comap_iff,
    nhds_eq_comap_uniformity, comap_comap]
  exact tendsto_comap.prodMk (tendsto_diag_uniformity _ _)
/-
**UniformContinuousOn.tendstoUniformly** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformContinuousOn.tendstoUniformly [UniformSpace α] [UniformSpace γ] {U 
: Set α} (hU : U in 𝓝 x) {F : α -> β -> γ} (hF : UniformContinuousOn ↿F (U ×ˢ (u
niv : Set β))) : TendstoUniformly F (F x) (𝓝 x)
参数：hU : U in 𝓝 x；hF : UniformContinuousOn ↿F (U ×ˢ (univ : Set β))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `nhdsWithin_eq_nhds`：∀ {α : Type u_1} [inst : TopologicalSpace α] {a : α}
 {s : Set α}, nhdsWithin a s = nhds a ↔ s ∈ nhds a
· 使用定理 `UniformContinuousOn.tendstoUniformlyOn`：UniformContinuousOn.tendstoUnifo
rmlyOn [UniformSpace α] [UniformSpace γ] {U : Set α} {V : Set β} {F : α -> β -> 
γ} (hF : UniformContinuousOn…
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
-/
theorem UniformContinuousOn.tendstoUniformly [UniformSpace α] [UniformSpace γ] {U : Set α}
    (hU : U ∈ 𝓝 x) {F : α → β → γ} (hF : UniformContinuousOn ↿F (U ×ˢ (univ : Set β))) :
    TendstoUniformly F (F x) (𝓝 x) := by
  simpa only [tendstoUniformlyOn_univ, nhdsWithin_eq_nhds.2 hU]
    using hF.tendstoUniformlyOn (mem_of_mem_nhds hU)
/-
**UniformContinuous** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：UniformContinuous (f : α -> β)
参数：f : α -> β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem UniformContinuous₂.tendstoUniformly [UniformSpace α] [UniformSpace γ] {f : α → β → γ}
    (h : UniformContinuous₂ f) : TendstoUniformly f (f x) (𝓝 x) :=
  UniformContinuousOn.tendstoUniformly univ_mem <| by rwa [univ_prod_univ, uniformContinuousOn_univ]

namespace Filter.HasBasis

variable {X ιX ια ιβ : Type*}

/-- An analogue of `Filter.HasBasis.tendsto_right_iff` for `TendstoUniformlyOnFilter`. -/
/-
**Filter.HasBasis.tendstoUniformlyOnFilter_iff_of_uniformity** 是 Mathlib 中的一个引理，
位于命名空间 `Filter.HasBasis`。
形式化陈述：tendstoUniformlyOnFilter_iff_of_uniformity {F : X -> α -> β} {f : α -> β} 
{l : Filter X} {l' : Filter α} {pβ : ιβ -> Prop} {sβ : ιβ -> Set (β × β)} (hβ : 
(uniformity β).HasBasis pβ sβ) : TendstoUniformlyOnFilter F f l l' ↔ (forall i, 
pβ i -> forallᶠ n in l ×ˢ l', (f n.2, F n.1 n.2) in sβ i)
参数：β × β；hβ : (uniformity β).HasBasis pβ sβ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendstoUniformlyOnFilter_iff_tendsto`：tendstoUniformlyOnFilter_iff_tends
to : TendstoUniformlyOnFilter F f p p' ↔ Tendsto (fun q : ι × α => (f q.2, F q.1
 q.2)) (p ×ˢ p') (𝓤 β)
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
An analogue of `Filter.HasBasis.tendsto_right_iff` for `TendstoUniformlyOnFilter
`.
-/
lemma tendstoUniformlyOnFilter_iff_of_uniformity {F : X → α → β} {f : α → β}
    {l : Filter X} {l' : Filter α} {pβ : ιβ → Prop} {sβ : ιβ → Set (β × β)}
    (hβ : (uniformity β).HasBasis pβ sβ) :
    TendstoUniformlyOnFilter F f l l' ↔
      (∀ i, pβ i → ∀ᶠ n in l ×ˢ l', (f n.2, F n.1 n.2) ∈ sβ i) := by
  rw [tendstoUniformlyOnFilter_iff_tendsto, hβ.tendsto_right_iff]

/-- An analogue of `Filter.HasBasis.tendsto_iff` for `TendstoUniformlyOnFilter`. -/
/-
**Filter.HasBasis.tendstoUniformlyOnFilter_iff** 是 Mathlib 中的一个引理，位于命名空间 `Filter
.HasBasis`。
形式化陈述：tendstoUniformlyOnFilter_iff {F : X -> α -> β} {f : α -> β} {l : Filter X}
 {l' : Filter α} {pX : ιX -> Prop} {sX : ιX -> Set X} {pα : ια -> Prop} {sα : ια
 -> Set α} {pβ : ιβ -> Prop} {sβ : ιβ -> Set (β × β)} (hl : l.HasBasis pX sX) (h
l' : l'.HasBasis pα sα) (hβ : (uniformity β).HasBasis pβ sβ) : TendstoUniformlyO
nFilter F f l l' ↔ (forall i, pβ i -> exists j k, (pX j ∧ pα k) ∧ forall x a, x 
in sX j -> a in sα k -> (f a, F x a) in sβ i)
参数：β × β；hl : l.HasBasis pX sX；hl' : l'.HasBasis pα sα；hβ : (uniformity β).HasBa
sis pβ sβ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Filter.HasBasis.tendstoUniformlyOnFilter_iff_of_uniformity`：tendstoUnifo
rmlyOnFilter_iff_of_uniformity {F : X -> α -> β} {f : α -> β} {l : Filter X} {l'
 : Filter α} {pβ : ιβ -> Prop} {sβ : ιβ -> Set (…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Filter.HasBasis.eventually_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fil
ter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : α → Prop}, (∀ᶠ 
(x : α) in l, q x) ↔…
· 使用定理 `Filter.HasBasis.prod`：∀ {α : Type u_1} {β : Type u_2} {la : Filter α} {l
b : Filter β} {ι : Type u_6} {ι' : Type u_7} {pa : ι → Prop}   {sa : ι → Set α} 
{pb : ι' →…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
An analogue of `Filter.HasBasis.tendsto_iff` for `TendstoUniformlyOnFilter`.
-/
lemma tendstoUniformlyOnFilter_iff {F : X → α → β} {f : α → β}
    {l : Filter X} {l' : Filter α} {pX : ιX → Prop} {sX : ιX → Set X}
    {pα : ια → Prop} {sα : ια → Set α} {pβ : ιβ → Prop} {sβ : ιβ → Set (β × β)}
    (hl : l.HasBasis pX sX) (hl' : l'.HasBasis pα sα)
    (hβ : (uniformity β).HasBasis pβ sβ) :
    TendstoUniformlyOnFilter F f l l' ↔
      (∀ i, pβ i → ∃ j k, (pX j ∧ pα k) ∧ ∀ x a, x ∈ sX j → a ∈ sα k → (f a, F x a) ∈ sβ i) := by
  simp [hβ.tendstoUniformlyOnFilter_iff_of_uniformity, (hl.prod hl').eventually_iff]

/-- An analogue of `Filter.HasBasis.tendsto_right_iff` for `TendstoUniformlyOn`. -/
/-
**Filter.HasBasis.tendstoUniformlyOn_iff_of_uniformity** 是 Mathlib 中的一个引理，位于命名空间
 `Filter.HasBasis`。
形式化陈述：tendstoUniformlyOn_iff_of_uniformity {F : X -> α -> β} {f : α -> β} {l : F
ilter X} {s : Set α} {pβ : ιβ -> Prop} {sβ : ιβ -> Set (β × β)} (hβ : (uniformit
y β).HasBasis pβ sβ) : TendstoUniformlyOn F f l s ↔ (forall i, pβ i -> forallᶠ n
 in l, forall x in s, (f x, F n x) in sβ i)
参数：β × β；hβ : (uniformity β).HasBasis pβ sβ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
An analogue of `Filter.HasBasis.tendsto_right_iff` for `TendstoUniformlyOn`.
-/
lemma tendstoUniformlyOn_iff_of_uniformity {F : X → α → β} {f : α → β}
    {l : Filter X} {s : Set α} {pβ : ιβ → Prop} {sβ : ιβ → Set (β × β)}
    (hβ : (uniformity β).HasBasis pβ sβ) :
    TendstoUniformlyOn F f l s ↔
      (∀ i, pβ i → ∀ᶠ n in l, ∀ x ∈ s, (f x, F n x) ∈ sβ i) := by
  simp_rw [tendstoUniformlyOn_iff_tendsto, hβ.tendsto_right_iff, eventually_prod_principal_iff]

/-- An analogue of `Filter.HasBasis.tendsto_iff` for `TendstoUniformlyOn`. -/
/-
**Filter.HasBasis.tendstoUniformlyOn_iff** 是 Mathlib 中的一个引理，位于命名空间 `Filter.HasBa
sis`。
形式化陈述：tendstoUniformlyOn_iff {F : X -> α -> β} {f : α -> β} {l : Filter X} {s : 
Set α} {pX : ιX -> Prop} {sX : ιX -> Set X} {pβ : ιβ -> Prop} {sβ : ιβ -> Set (β
 × β)} (hl : l.HasBasis pX sX) (hβ : (uniformity β).HasBasis pβ sβ) : TendstoUni
formlyOn F f l s ↔ (forall i, pβ i -> exists j, pX j ∧ forall ⦃x⦄, x in sX j -> 
forall a in s, (f a, F x a) in sβ i)
参数：β × β；hl : l.HasBasis pX sX；hβ : (uniformity β).HasBasis pβ sβ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Filter.HasBasis.tendstoUniformlyOn_iff_of_uniformity`：tendstoUniformlyOn
_iff_of_uniformity {F : X -> α -> β} {f : α -> β} {l : Filter X} {s : Set α} {pβ
 : ιβ -> Prop} {sβ : ιβ -> Set (β × β)} (h…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Filter.HasBasis.eventually_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fil
ter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : α → Prop}, (∀ᶠ 
(x : α) in l, q x) ↔…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
An analogue of `Filter.HasBasis.tendsto_iff` for `TendstoUniformlyOn`.
-/
lemma tendstoUniformlyOn_iff {F : X → α → β} {f : α → β}
    {l : Filter X} {s : Set α} {pX : ιX → Prop} {sX : ιX → Set X} {pβ : ιβ → Prop}
    {sβ : ιβ → Set (β × β)} (hl : l.HasBasis pX sX) (hβ : (uniformity β).HasBasis pβ sβ) :
    TendstoUniformlyOn F f l s ↔
      (∀ i, pβ i → ∃ j, pX j ∧ ∀ ⦃x⦄, x ∈ sX j → ∀ a ∈ s, (f a, F x a) ∈ sβ i) := by
  simp [hβ.tendstoUniformlyOn_iff_of_uniformity, hl.eventually_iff]

/-- An analogue of `Filter.HasBasis.tendsto_right_iff` for `TendstoUniformly`. -/
/-
**Filter.HasBasis.tendstoUniformly_iff_of_uniformity** 是 Mathlib 中的一个引理，位于命名空间 `
Filter.HasBasis`。
形式化陈述：tendstoUniformly_iff_of_uniformity {F : X -> α -> β} {f : α -> β} {l : Fil
ter X} {pβ : ιβ -> Prop} {sβ : ιβ -> Set (β × β)} (hβ : (uniformity β).HasBasis 
pβ sβ) : TendstoUniformly F f l ↔ (forall i, pβ i -> forallᶠ n in l, forall x, (
f x, F n x) in sβ i)
参数：β × β；hβ : (uniformity β).HasBasis pβ sβ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Filter.HasBasis.tendstoUniformlyOn_iff_of_uniformity`：tendstoUniformlyOn
_iff_of_uniformity {F : X -> α -> β} {f : α -> β} {l : Filter X} {s : Set α} {pβ
 : ιβ -> Prop} {sβ : ιβ -> Set (β × β)} (h…
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
An analogue of `Filter.HasBasis.tendsto_right_iff` for `TendstoUniformly`.
-/
lemma tendstoUniformly_iff_of_uniformity {F : X → α → β} {f : α → β}
    {l : Filter X} {pβ : ιβ → Prop} {sβ : ιβ → Set (β × β)}
    (hβ : (uniformity β).HasBasis pβ sβ) :
    TendstoUniformly F f l ↔
      (∀ i, pβ i → ∀ᶠ n in l, ∀ x, (f x, F n x) ∈ sβ i) := by
  simp_rw [← tendstoUniformlyOn_univ, hβ.tendstoUniformlyOn_iff_of_uniformity, mem_univ,
    true_imp_iff]

/-- An analogue of `Filter.HasBasis.tendsto_iff` for `TendstoUniformly`. -/
/-
**Filter.HasBasis.tendstoUniformly_iff** 是 Mathlib 中的一个引理，位于命名空间 `Filter.HasBasi
s`。
形式化陈述：tendstoUniformly_iff {F : X -> α -> β} {f : α -> β} {l : Filter X} {pX : ι
X -> Prop} {sX : ιX -> Set X} (hl : l.HasBasis pX sX) {pβ : ιβ -> Prop} {sβ : ιβ
 -> Set (β × β)} (hβ : (uniformity β).HasBasis pβ sβ) : TendstoUniformly F f l ↔
 (forall i, pβ i -> exists j, pX j ∧ forall ⦃x⦄, x in sX j -> forall a, (f a, F 
x a) in sβ i)
参数：hl : l.HasBasis pX sX；β × β；hβ : (uniformity β).HasBasis pβ sβ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Filter.HasBasis.tendstoUniformly_iff_of_uniformity`：tendstoUniformly_iff
_of_uniformity {F : X -> α -> β} {f : α -> β} {l : Filter X} {pβ : ιβ -> Prop} {
sβ : ιβ -> Set (β × β)} (hβ : (uniformit…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Filter.HasBasis.eventually_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fil
ter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : α → Prop}, (∀ᶠ 
(x : α) in l, q x) ↔…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
An analogue of `Filter.HasBasis.tendsto_iff` for `TendstoUniformly`.
-/
lemma tendstoUniformly_iff {F : X → α → β} {f : α → β}
    {l : Filter X} {pX : ιX → Prop} {sX : ιX → Set X} (hl : l.HasBasis pX sX)
    {pβ : ιβ → Prop} {sβ : ιβ → Set (β × β)} (hβ : (uniformity β).HasBasis pβ sβ) :
    TendstoUniformly F f l ↔
      (∀ i, pβ i → ∃ j, pX j ∧ ∀ ⦃x⦄, x ∈ sX j → ∀ a, (f a, F x a) ∈ sβ i) := by
  simp only [hβ.tendstoUniformly_iff_of_uniformity, hl.eventually_iff]

end Filter.HasBasis

/-- A sequence is uniformly Cauchy if eventually all of its pairwise differences are
uniformly bounded -/
/-
**UniformCauchySeqOnFilter** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：UniformCauchySeqOnFilter (F : ι -> α -> β) (p : Filter ι) (p' : Filter α) 
: Prop
参数：F : ι -> α -> β；p : Filter ι；p' : Filter α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sequence is uniformly Cauchy if eventually all of its pairwise differences are
uniformly bounded
-/
def UniformCauchySeqOnFilter (F : ι → α → β) (p : Filter ι) (p' : Filter α) : Prop :=
  ∀ u ∈ 𝓤 β, ∀ᶠ m : (ι × ι) × α in (p ×ˢ p) ×ˢ p', (F m.fst.fst m.snd, F m.fst.snd m.snd) ∈ u

/-- A sequence is uniformly Cauchy if eventually all of its pairwise differences are
uniformly bounded -/
/-
**UniformCauchySeqOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：UniformCauchySeqOn (F : ι -> α -> β) (p : Filter ι) (s : Set α) : Prop
参数：F : ι -> α -> β；p : Filter ι；s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sequence is uniformly Cauchy if eventually all of its pairwise differences are
uniformly bounded
-/
def UniformCauchySeqOn (F : ι → α → β) (p : Filter ι) (s : Set α) : Prop :=
  ∀ u ∈ 𝓤 β, ∀ᶠ m : ι × ι in p ×ˢ p, ∀ x : α, x ∈ s → (F m.fst x, F m.snd x) ∈ u
/-
**uniformCauchySeqOn_iff_uniformCauchySeqOnFilter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformCauchySeqOn_iff_uniformCauchySeqOnFilter : UniformCauchySeqOn F p s
 ↔ UniformCauchySeqOnFilter F p (𝓟 s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventually_prod_principal_iff`：eventually_prod_principal_iff {p :
 α × β -> Prop} {s : Set β} : (forallᶠ x : α × β in f ×ˢ 𝓟 s, p x) ↔ forallᶠ x :
 α in f, forall y : β, y i…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem uniformCauchySeqOn_iff_uniformCauchySeqOnFilter :
    UniformCauchySeqOn F p s ↔ UniformCauchySeqOnFilter F p (𝓟 s) := by
  simp only [UniformCauchySeqOn, UniformCauchySeqOnFilter]
  refine forall₂_congr fun u hu => ?_
  rw [eventually_prod_principal_iff]
/-
**UniformCauchySeqOn.uniformCauchySeqOnFilter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformCauchySeqOn.uniformCauchySeqOnFilter (hF : UniformCauchySeqOn F p s
) : UniformCauchySeqOnFilter F p (𝓟 s)
参数：hF : UniformCauchySeqOn F p s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `uniformCauchySeqOn_iff_uniformCauchySeqOnFilter`：uniformCauchySeqOn_iff_
uniformCauchySeqOnFilter : UniformCauchySeqOn F p s ↔ UniformCauchySeqOnFilter F
 p (𝓟 s)
-/
theorem UniformCauchySeqOn.uniformCauchySeqOnFilter (hF : UniformCauchySeqOn F p s) :
    UniformCauchySeqOnFilter F p (𝓟 s) := by rwa [← uniformCauchySeqOn_iff_uniformCauchySeqOnFilter]

/-- A sequence that converges uniformly is also uniformly Cauchy -/
/-
**TendstoUniformlyOnFilter.uniformCauchySeqOnFilter** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：TendstoUniformlyOnFilter.uniformCauchySeqOnFilter (hF : TendstoUniformlyOn
Filter F f p p') : UniformCauchySeqOnFilter F p p'
参数：hF : TendstoUniformlyOnFilter F f p p'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `comp_symm_of_uniformity`：comp_symm_of_uniformity {s : SetRel α α} (hs : 
s in 𝓤 α) : exists t in 𝓤 α, (forall {a b}, (a, b) in t -> (b, a) in t) ∧ t ○ t 
subseteq s
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.tendsto_swap4_prod`：tendsto_swap4_prod {h : Filter γ} {k : Filter
 δ} : Tendsto (fun p : (α × β) × γ × δ => ((p.1.1, p.2.1), (p.1.2, p.2.2))) ((f 
×ˢ g) ×ˢ (h ×ˢ …
· 使用定理 `Filter.Eventually.prod_mk`：∀ {α : Type u_1} {β : Type u_2} {la : Filter 
α} {pa : α → Prop},   (∀ᶠ (x : α) in la, pa x) →     ∀ {lb : Filter β} {pb : β →
 Prop}, (∀ᶠ (y …
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.diag_of_prod_right`：∀ {α : Type u_1} {γ : Type u_3} {f
 : Filter α} {g : Filter γ} {p : α × γ × γ → Prop},   (∀ᶠ (x : α × γ × γ) in f ×
ˢ g ×ˢ g, p x) → ∀ᶠ (x : α…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `SetRel.prodMk_mem_comp`：prodMk_mem_comp (hab : a ~[R] b) (hbc : b ~[S] c
) : a ~[R ○ S] c

--- 原说明 ---
A sequence that converges uniformly is also uniformly Cauchy
-/
theorem TendstoUniformlyOnFilter.uniformCauchySeqOnFilter (hF : TendstoUniformlyOnFilter F f p p') :
    UniformCauchySeqOnFilter F p p' := by
  intro u hu
  rcases comp_symm_of_uniformity hu with ⟨t, ht, htsymm, htmem⟩
  have := tendsto_swap4_prod.eventually ((hF t ht).prod_mk (hF t ht))
  apply this.diag_of_prod_right.mono
  simp only [and_imp, Prod.forall]
  intro n1 n2 x hl hr
  exact htmem <| SetRel.prodMk_mem_comp (htsymm hl) hr

/-- A sequence that converges uniformly is also uniformly Cauchy -/
/-
**TendstoUniformlyOn.uniformCauchySeqOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoUniformlyOn.uniformCauchySeqOn (hF : TendstoUniformlyOn F f p s) : 
UniformCauchySeqOn F p s
参数：hF : TendstoUniformlyOn F f p s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `uniformCauchySeqOn_iff_uniformCauchySeqOnFilter`：uniformCauchySeqOn_iff_
uniformCauchySeqOnFilter : UniformCauchySeqOn F p s ↔ UniformCauchySeqOnFilter F
 p (𝓟 s)
· 使用定理 `TendstoUniformlyOnFilter.uniformCauchySeqOnFilter`：TendstoUniformlyOnFil
ter.uniformCauchySeqOnFilter (hF : TendstoUniformlyOnFilter F f p p') : UniformC
auchySeqOnFilter F p p'
· 使用定理 `TendstoUniformlyOn.tendstoUniformlyOnFilter`：∀ {α : Type u_1} {β : Type 
u_2} {ι : Type u_4} [inst : UniformSpace β] {F : ι → α → β} {f : α → β} {s : Set
 α}   {p : Filter ι}, TendstoUnif…

--- 原说明 ---
A sequence that converges uniformly is also uniformly Cauchy
-/
theorem TendstoUniformlyOn.uniformCauchySeqOn (hF : TendstoUniformlyOn F f p s) :
    UniformCauchySeqOn F p s :=
  uniformCauchySeqOn_iff_uniformCauchySeqOnFilter.mpr
    hF.tendstoUniformlyOnFilter.uniformCauchySeqOnFilter

/-- A uniformly Cauchy sequence converges uniformly to its limit -/
/-
**UniformCauchySeqOnFilter.tendstoUniformlyOnFilter_of_tendsto** 是 Mathlib 中的一个定
理，位于命名空间 ``。
形式化陈述：UniformCauchySeqOnFilter.tendstoUniformlyOnFilter_of_tendsto (hF : Uniform
CauchySeqOnFilter F p p') (hF' : forallᶠ x : α in p', Tendsto (fun n => F n x) p
 (𝓝 (f x))) : TendstoUniformlyOnFilter F f p p'
参数：hF : UniformCauchySeqOnFilter F p p'；hF' : forallᶠ x : α in p', Tendsto (fun 
n => F n x) p (𝓝 (f x))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.bot_prod`：∀ {α : Type u_1} {β : Type u_2} {g : Filter β}, ⊥ ×ˢ g 
= ⊥
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `comp_symm_of_uniformity`：comp_symm_of_uniformity {s : SetRel α α} (hs : 
s in 𝓤 α) : exists t in 𝓤 α, (forall {a b}, (a, b) in t -> (b, a) in t) ∧ t ○ t 
subseteq s
· 使用定理 `Filter.eventually_prod_iff`：eventually_prod_iff {p : α × β -> Prop} : (f
orallᶠ x in f ×ˢ g, p x) ↔ exists pa : α -> Prop, (forallᶠ x in f, pa x) ∧ exist
s pb : β -> Prop…
· 使用定理 `Filter.eventually_swap_iff`：eventually_swap_iff {p : α × β -> Prop} : (f
orallᶠ x : α × β in f ×ˢ g, p x) ↔ forallᶠ y : β × α in g ×ˢ f, p y.swap
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.tendsto_prodAssoc`：tendsto_prodAssoc {h : Filter γ} : Tendsto (Eq
uiv.prodAssoc α β γ) ((f ×ˢ g) ×ˢ h) (f ×ˢ (g ×ˢ h))
· 使用定理 `Filter.tendsto_prod_swap`：tendsto_prod_swap : Tendsto (Prod.swap : α × β
 -> β × α) (f ×ˢ g) (g ×ˢ f)
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.curry`：∀ {α : Type u_1} {β : Type u_2} {la : Filter α}
 {lb : Filter β} {p : α × β → Prop},   (∀ᶠ (x : α × β) in la ×ˢ lb, p x) → ∀ᶠ (x
 : α) in la, …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.prodAssoc_apply`：∀ (α : Type u_9) (β : Type u_10) (γ : Type u_11) 
(p : (α × β) × γ), (Equiv.prodAssoc α β γ) p = (p.1.1, p.1.2, p.2)
· 使用定理 `Set.mem_of_mem_of_subset`：mem_of_mem_of_subset {x : α} {s t : Set α} (hx
 : x in s) (h : s subseteq t) : x in t
· 使用定理 `Uniform.tendsto_nhds_right`：tendsto_nhds_right {f : Filter β} {u : β -> 
α} {a : α} : Tendsto u f (𝓝 a) ↔ Tendsto (fun x => (a, u x)) f (𝓤 α)
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
A uniformly Cauchy sequence converges uniformly to its limit
-/
theorem UniformCauchySeqOnFilter.tendstoUniformlyOnFilter_of_tendsto
    (hF : UniformCauchySeqOnFilter F p p')
    (hF' : ∀ᶠ x : α in p', Tendsto (fun n => F n x) p (𝓝 (f x))) :
    TendstoUniformlyOnFilter F f p p' := by
  rcases p.eq_or_neBot with rfl | _
  · simp only [TendstoUniformlyOnFilter, bot_prod, eventually_bot, implies_true]
  -- Proof idea: |f_n(x) - f(x)| ≤ |f_n(x) - f_m(x)| + |f_m(x) - f(x)|. We choose `n`
  -- so that |f_n(x) - f_m(x)| is uniformly small across `s` whenever `m ≥ n`. Then for
  -- a fixed `x`, we choose `m` sufficiently large such that |f_m(x) - f(x)| is small.
  intro u hu
  rcases comp_symm_of_uniformity hu with ⟨t, ht, htsymm, htmem⟩
  -- We will choose n, x, and m simultaneously. n and x come from hF. m comes from hF'
  -- But we need to promote hF' to the full product filter to use it
  have hmc : ∀ᶠ x in (p ×ˢ p) ×ˢ p', Tendsto (fun n : ι => F n x.snd) p (𝓝 (f x.snd)) := by
    rw [eventually_prod_iff]
    exact ⟨fun _ => True, by simp, _, hF', by simp⟩
  -- To apply filter operations we'll need to do some order manipulation
  rw [Filter.eventually_swap_iff]
  have := tendsto_prodAssoc.eventually (tendsto_prod_swap.eventually ((hF t ht).and hmc))
  apply this.curry.mono
  simp only [Equiv.prodAssoc_apply, eventually_and, eventually_const, Prod.snd_swap, Prod.fst_swap,
    and_imp, Prod.forall]
  -- Complete the proof
  intro x n hx hm'
  refine Set.mem_of_mem_of_subset ?_ htmem
  rw [Uniform.tendsto_nhds_right] at hm'
  have := hx.and (hm' ht)
  obtain ⟨m, hm⟩ := this.exists
  exact ⟨F m x, ⟨hm.2, htsymm hm.1⟩⟩

/-- A uniformly Cauchy sequence converges uniformly to its limit -/
/-
**UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto (hF : UniformCauchySeqOn 
F p s) (hF' : forall x : α, x in s -> Tendsto (fun n => F n x) p (𝓝 (f x))) : Te
ndstoUniformlyOn F f p s
参数：hF : UniformCauchySeqOn F p s；hF' : forall x : α, x in s -> Tendsto (fun n =>
 F n x) p (𝓝 (f x))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendstoUniformlyOn_iff_tendstoUniformlyOnFilter`：tendstoUniformlyOn_iff_
tendstoUniformlyOnFilter : TendstoUniformlyOn F f p s ↔ TendstoUniformlyOnFilter
 F f p (𝓟 s)
· 使用定理 `UniformCauchySeqOnFilter.tendstoUniformlyOnFilter_of_tendsto`：UniformCau
chySeqOnFilter.tendstoUniformlyOnFilter_of_tendsto (hF : UniformCauchySeqOnFilte
r F p p') (hF' : forallᶠ x : α in p', Tendsto (fun…
· 使用定理 `UniformCauchySeqOn.uniformCauchySeqOnFilter`：UniformCauchySeqOn.uniformC
auchySeqOnFilter (hF : UniformCauchySeqOn F p s) : UniformCauchySeqOnFilter F p 
(𝓟 s)

--- 原说明 ---
A uniformly Cauchy sequence converges uniformly to its limit
-/
theorem UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto (hF : UniformCauchySeqOn F p s)
    (hF' : ∀ x : α, x ∈ s → Tendsto (fun n => F n x) p (𝓝 (f x))) : TendstoUniformlyOn F f p s :=
  tendstoUniformlyOn_iff_tendstoUniformlyOnFilter.mpr
    (hF.uniformCauchySeqOnFilter.tendstoUniformlyOnFilter_of_tendsto hF')
/-
**UniformCauchySeqOnFilter.mono_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformCauchySeqOnFilter.mono_left {p'' : Filter ι} (hf : UniformCauchySeq
OnFilter F p p') (hp : p'' <= p) : UniformCauchySeqOnFilter F p'' p'
参数：hf : UniformCauchySeqOnFilter F p p'；hp : p'' <= p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `Filter.prod_mono_left`：prod_mono_left (g : Filter β) {f₁ f₂ : Filter α} 
(hf : f₁ <= f₂) : f₁ ×ˢ g <= f₂ ×ˢ g
· 使用定理 `Filter.prod_mono`：prod_mono {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} (hf : 
f₁ <= f₂) (hg : g₁ <= g₂) : f₁ ×ˢ g₁ <= f₂ ×ˢ g₂
-/
theorem UniformCauchySeqOnFilter.mono_left {p'' : Filter ι} (hf : UniformCauchySeqOnFilter F p p')
    (hp : p'' ≤ p) : UniformCauchySeqOnFilter F p'' p' := fun u hu =>
  (hf u hu).filter_mono (p'.prod_mono_left (Filter.prod_mono hp hp))
/-
**UniformCauchySeqOnFilter.mono_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformCauchySeqOnFilter.mono_right {p'' : Filter α} (hf : UniformCauchySe
qOnFilter F p p') (hp : p'' <= p') : UniformCauchySeqOnFilter F p p''
参数：hf : UniformCauchySeqOnFilter F p p'；hp : p'' <= p'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `Filter.prod_mono_right`：prod_mono_right (f : Filter α) {g₁ g₂ : Filter β
} (hf : g₁ <= g₂) : f ×ˢ g₁ <= f ×ˢ g₂
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem UniformCauchySeqOnFilter.mono_right {p'' : Filter α} (hf : UniformCauchySeqOnFilter F p p')
    (hp : p'' ≤ p') : UniformCauchySeqOnFilter F p p'' := fun u hu =>
  have := (hf u hu).filter_mono ((p ×ˢ p).prod_mono_right hp)
  this.mono (by simp)
/-
**UniformCauchySeqOn.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformCauchySeqOn.mono (hf : UniformCauchySeqOn F p s) (hss' : s' subsete
q s) : UniformCauchySeqOn F p s'
参数：hf : UniformCauchySeqOn F p s；hss' : s' subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `uniformCauchySeqOn_iff_uniformCauchySeqOnFilter`：uniformCauchySeqOn_iff_
uniformCauchySeqOnFilter : UniformCauchySeqOn F p s ↔ UniformCauchySeqOnFilter F
 p (𝓟 s)
· 使用定理 `UniformCauchySeqOnFilter.mono_right`：UniformCauchySeqOnFilter.mono_right
 {p'' : Filter α} (hf : UniformCauchySeqOnFilter F p p') (hp : p'' <= p') : Unif
ormCauchySeqOnFilter F p …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `Filter.mem_principal`：∀ {α : Type u_1} {s t : Set α}, s ∈ Filter.princip
al t ↔ t ⊆ s
-/
theorem UniformCauchySeqOn.mono (hf : UniformCauchySeqOn F p s) (hss' : s' ⊆ s) :
    UniformCauchySeqOn F p s' := by
  rw [uniformCauchySeqOn_iff_uniformCauchySeqOnFilter] at hf ⊢
  exact hf.mono_right (le_principal_iff.mpr <| mem_principal.mpr hss')

/-- Composing on the right by a function preserves uniform Cauchy sequences -/
/-
**UniformCauchySeqOnFilter.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformCauchySeqOnFilter.comp {γ : Type*} (hf : UniformCauchySeqOnFilter F
 p p') (g : γ -> α) : UniformCauchySeqOnFilter (fun n => F n ∘ g) p (p'.comap g)
参数：hf : UniformCauchySeqOnFilter F p p'；g : γ -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.eventually_prod_iff`：eventually_prod_iff {p : α × β -> Prop} : (f
orallᶠ x in f ×ˢ g, p x) ↔ exists pa : α -> Prop, (forallᶠ x in f, pa x) ∧ exist
s pb : β -> Prop…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_comap`：eventually_comap : (forallᶠ a in comap f l, p a
) ↔ forallᶠ b in l, forall a, f a = b -> p a
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True

--- 原说明 ---
Composing on the right by a function preserves uniform Cauchy sequences
-/
theorem UniformCauchySeqOnFilter.comp {γ : Type*} (hf : UniformCauchySeqOnFilter F p p')
    (g : γ → α) : UniformCauchySeqOnFilter (fun n => F n ∘ g) p (p'.comap g) := fun u hu => by
  obtain ⟨pa, hpa, pb, hpb, hpapb⟩ := eventually_prod_iff.mp (hf u hu)
  rw [eventually_prod_iff]
  refine ⟨pa, hpa, pb ∘ g, ?_, fun hx _ hy => hpapb hx hy⟩
  exact eventually_comap.mpr (hpb.mono fun x hx y hy => by simp only [hx, hy, Function.comp_apply])

/-- Composing on the right by a function preserves uniform Cauchy sequences -/
/-
**UniformCauchySeqOn.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformCauchySeqOn.comp {γ : Type*} (hf : UniformCauchySeqOn F p s) (g : γ
 -> α) : UniformCauchySeqOn (fun n => F n ∘ g) p (g ⁻¹' s)
参数：hf : UniformCauchySeqOn F p s；g : γ -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `uniformCauchySeqOn_iff_uniformCauchySeqOnFilter`：uniformCauchySeqOn_iff_
uniformCauchySeqOnFilter : UniformCauchySeqOn F p s ↔ UniformCauchySeqOnFilter F
 p (𝓟 s)
· 使用定理 `Filter.comap_principal`：comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 
(m ⁻¹' t)
· 使用定理 `UniformCauchySeqOnFilter.comp`：UniformCauchySeqOnFilter.comp {γ : Type*}
 (hf : UniformCauchySeqOnFilter F p p') (g : γ -> α) : UniformCauchySeqOnFilter 
(fun n => F n ∘ g) …

--- 原说明 ---
Composing on the right by a function preserves uniform Cauchy sequences
-/
theorem UniformCauchySeqOn.comp {γ : Type*} (hf : UniformCauchySeqOn F p s) (g : γ → α) :
    UniformCauchySeqOn (fun n => F n ∘ g) p (g ⁻¹' s) := by
  rw [uniformCauchySeqOn_iff_uniformCauchySeqOnFilter] at hf ⊢
  simpa only [UniformCauchySeqOn, comap_principal] using hf.comp g

/-- Composing on the left by a uniformly continuous function preserves
uniform Cauchy sequences -/
/-
**UniformContinuous.comp_uniformCauchySeqOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformContinuous.comp_uniformCauchySeqOn [UniformSpace γ] {g : β -> γ} (h
g : UniformContinuous g) (hf : UniformCauchySeqOn F p s) : UniformCauchySeqOn (f
un n => g ∘ F n) p s
参数：hg : UniformContinuous g；hf : UniformCauchySeqOn F p s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing on the left by a uniformly continuous function preserves
uniform Cauchy sequences
-/
theorem UniformContinuous.comp_uniformCauchySeqOn [UniformSpace γ] {g : β → γ}
    (hg : UniformContinuous g) (hf : UniformCauchySeqOn F p s) :
    UniformCauchySeqOn (fun n => g ∘ F n) p s := fun _u hu => hf _ (hg hu)
/-
**UniformCauchySeqOn.prodMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformCauchySeqOn.prodMap {ι' α' β' : Type*} [UniformSpace β'] {F' : ι' -
> α' -> β'} {p' : Filter ι'} {s' : Set α'} (h : UniformCauchySeqOn F p s) (h' : 
UniformCauchySeqOn F' p' s') : UniformCauchySeqOn (fun i : ι × ι' => Prod.map (F
 i.1) (F' i.2)) (p ×ˢ p') (s ×ˢ s')
参数：h : UniformCauchySeqOn F p s；h' : UniformCauchySeqOn F' p' s'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mem_prod_iff`：mem_prod_iff {s : Set (α × β)} {f : Filter α} {g : 
Filter β} : s in f ×ˢ g ↔ exists t₁ in f, exists t₂ in g, t₁ ×ˢ t₂ subseteq s
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `uniformity_prod_eq_prod`：uniformity_prod_eq_prod [UniformSpace α] [Unifo
rmSpace β] : 𝓤 (α × β) = map (fun p : (α × α) × β × β => ((p.1.1, p.2.1), (p.1.2
, p.2.2))) (𝓤…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.tendsto_swap4_prod`：tendsto_swap4_prod {h : Filter γ} {k : Filter
 δ} : Tendsto (fun p : (α × β) × γ × δ => ((p.1.1, p.2.1), (p.1.2, p.2.2))) ((f 
×ˢ g) ×ˢ (h ×ˢ …
· 使用定理 `Filter.Eventually.prod_mk`：∀ {α : Type u_1} {β : Type u_2} {la : Filter 
α} {pa : α → Prop},   (∀ᶠ (x : α) in la, pa x) →     ∀ {lb : Filter β} {pb : β →
 Prop}, (∀ᶠ (y …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Set.mk_mem_prod`：mk_mem_prod (ha : a in s) (hb : b in t) : (a, b) in s ×
ˢ t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem UniformCauchySeqOn.prodMap {ι' α' β' : Type*} [UniformSpace β'] {F' : ι' → α' → β'}
    {p' : Filter ι'} {s' : Set α'} (h : UniformCauchySeqOn F p s)
    (h' : UniformCauchySeqOn F' p' s') :
    UniformCauchySeqOn (fun i : ι × ι' => Prod.map (F i.1) (F' i.2)) (p ×ˢ p') (s ×ˢ s') := by
  intro u hu
  rw [uniformity_prod_eq_prod, mem_map, mem_prod_iff] at hu
  obtain ⟨v, hv, w, hw, hvw⟩ := hu
  simp_rw [mem_prod, and_imp, Prod.forall, Prod.map_apply]
  rw [← Set.image_subset_iff] at hvw
  apply (tendsto_swap4_prod.eventually ((h v hv).prod_mk (h' w hw))).mono
  intro x hx a b ha hb
  exact hvw ⟨_, mk_mem_prod (hx.1 a ha) (hx.2 b hb), rfl⟩
/-
**UniformCauchySeqOn.prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformCauchySeqOn.prod {ι' β' : Type*} [UniformSpace β'] {F' : ι' -> α ->
 β'} {p' : Filter ι'} (h : UniformCauchySeqOn F p s) (h' : UniformCauchySeqOn F'
 p' s) : UniformCauchySeqOn (fun (i : ι × ι') a => (F i.fst a, F' i.snd a)) (p ×
ˢ p') s
参数：h : UniformCauchySeqOn F p s；h' : UniformCauchySeqOn F' p' s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
· 使用定理 `UniformCauchySeqOn.comp`：UniformCauchySeqOn.comp {γ : Type*} (hf : Unifo
rmCauchySeqOn F p s) (g : γ -> α) : UniformCauchySeqOn (fun n => F n ∘ g) p (g ⁻
¹' s)
· 使用定理 `UniformCauchySeqOn.prodMap`：UniformCauchySeqOn.prodMap {ι' α' β' : Type*
} [UniformSpace β'] {F' : ι' -> α' -> β'} {p' : Filter ι'} {s' : Set α'} (h : Un
iformCauchySeqOn…
-/
theorem UniformCauchySeqOn.prod {ι' β' : Type*} [UniformSpace β'] {F' : ι' → α → β'}
    {p' : Filter ι'} (h : UniformCauchySeqOn F p s) (h' : UniformCauchySeqOn F' p' s) :
    UniformCauchySeqOn (fun (i : ι × ι') a => (F i.fst a, F' i.snd a)) (p ×ˢ p') s :=
  (congr_arg _ s.inter_self).mp ((h.prodMap h').comp Function.diag)
/-
**UniformCauchySeqOn.prod'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformCauchySeqOn.prod' {β' : Type*} [UniformSpace β'] {F' : ι -> α -> β'
} (h : UniformCauchySeqOn F p s) (h' : UniformCauchySeqOn F' p s) : UniformCauch
ySeqOn (fun (i : ι) a => (F i a, F' i a)) p s
参数：h : UniformCauchySeqOn F p s；h' : UniformCauchySeqOn F' p s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_diag`：tendsto_diag : Tendsto Function.diag f (f ×ˢ f)
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Filter.Tendsto.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {
δ : Type u_6} {f : α → γ} {g : β → δ} {a : Filter α} {b : Filter β}   {c : Filte
r γ} {d : Fi…
· 使用定理 `UniformCauchySeqOn.prod`：UniformCauchySeqOn.prod {ι' β' : Type*} [Unifor
mSpace β'] {F' : ι' -> α -> β'} {p' : Filter ι'} (h : UniformCauchySeqOn F p s) 
(h' : Uniform…
-/
theorem UniformCauchySeqOn.prod' {β' : Type*} [UniformSpace β'] {F' : ι → α → β'}
    (h : UniformCauchySeqOn F p s) (h' : UniformCauchySeqOn F' p s) :
    UniformCauchySeqOn (fun (i : ι) a => (F i a, F' i a)) p s := fun u hu =>
  have hh : Tendsto (fun x : ι => (x, x)) p (p ×ˢ p) := tendsto_diag
  (hh.prodMap hh).eventually ((h.prod h') u hu)

/-- If a sequence of functions is uniformly Cauchy on a set, then the values at each point form
a Cauchy sequence. -/
/-
**UniformCauchySeqOn.cauchy_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformCauchySeqOn.cauchy_map [hp : NeBot p] (hf : UniformCauchySeqOn F p 
s) (hx : x in s) : Cauchy (map (fun i => F i x) p)
参数：hf : UniformCauchySeqOn F p s；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f

--- 原说明 ---
If a sequence of functions is uniformly Cauchy on a set, then the values at each
 point form
a Cauchy sequence.
-/
theorem UniformCauchySeqOn.cauchy_map [hp : NeBot p] (hf : UniformCauchySeqOn F p s) (hx : x ∈ s) :
    Cauchy (map (fun i => F i x) p) := by
  simp only [cauchy_map_iff, hp, true_and]
  intro u hu
  rw [mem_map]
  filter_upwards [hf u hu] with p hp using hp x hx

/-- If a sequence of functions is uniformly Cauchy on a set, then the values at each point form
a Cauchy sequence.  See `UniformCauchySeqOn.cauchy_map` for the non-`atTop` case. -/
/-
**UniformCauchySeqOn.cauchySeq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformCauchySeqOn.cauchySeq [Nonempty ι] [SemilatticeSup ι] (hf : Uniform
CauchySeqOn F atTop s) (hx : x in s) : CauchySeq fun i => F i x
参数：hf : UniformCauchySeqOn F atTop s；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformCauchySeqOn.cauchy_map`：UniformCauchySeqOn.cauchy_map [hp : NeBot
 p] (hf : UniformCauchySeqOn F p s) (hx : x in s) : Cauchy (map (fun i => F i x)
 p)
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α

--- 原说明 ---
If a sequence of functions is uniformly Cauchy on a set, then the values at each
 point form
a Cauchy sequence.  See `UniformCauchySeqOn.cauchy_map` for the non-`atTop` case
.
-/
theorem UniformCauchySeqOn.cauchySeq [Nonempty ι] [SemilatticeSup ι]
    (hf : UniformCauchySeqOn F atTop s) (hx : x ∈ s) :
    CauchySeq fun i ↦ F i x :=
  hf.cauchy_map (hp := atTop_neBot) hx

section SeqTendsto

/-
**tendstoUniformlyOn_of_seq_tendstoUniformlyOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendstoUniformlyOn_of_seq_tendstoUniformlyOn {l : Filter ι} [l.IsCountably
Generated] (h : forall u : Nat -> ι, Tendsto u atTop l -> TendstoUniformlyOn (fu
n n => F (u n)) f atTop s) : TendstoUniformlyOn F f l s
参数：h : forall u : Nat -> ι, Tendsto u atTop l -> TendstoUniformlyOn (fun n => F 
(u n)) f atTop s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendstoUniformlyOn_iff_tendsto`：tendstoUniformlyOn_iff_tendsto : Tendsto
UniformlyOn F f p s ↔ Tendsto (fun q : ι × α => (f q.2, F q.1 q.2)) (p ×ˢ 𝓟 s) (
𝓤 β)
· 使用定理 `Filter.tendsto_iff_seq_tendsto`：tendsto_iff_seq_tendsto {f : α -> β} {k 
: Filter α} {l : Filter β} [k.IsCountablyGenerated] : Tendsto f k l ↔ forall x :
 Nat -> α, Tendsto x…
· 使用定理 `Filter.prod.isCountablyGenerated`：∀ {α : Type u_1} {β : Type u_2} (la : 
Filter α) (lb : Filter β) [la.IsCountablyGenerated] [lb.IsCountablyGenerated],  
 (la ×ˢ lb).IsCountabl…
· 使用定理 `Filter.isCountablyGenerated_principal`：isCountablyGenerated_principal (s
 : Set α) : IsCountablyGenerated (𝓟 s)
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.tendsto_prod_iff'`：tendsto_prod_iff' {g' : Filter γ} {s : α -> β 
× γ} : Tendsto s f (g ×ˢ g') ↔ Tendsto (fun n => (s n).1) f g ∧ Tendsto (fun n =
> (s n).2) f g…
· 使用定理 `Filter.Tendsto.prodMk`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f
 : Filter α} {g : Filter β} {h : Filter γ} {m₁ : α → β} {m₂ : α → γ},   Filter.T
endsto m₁ f…
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem tendstoUniformlyOn_of_seq_tendstoUniformlyOn {l : Filter ι} [l.IsCountablyGenerated]
    (h : ∀ u : ℕ → ι, Tendsto u atTop l → TendstoUniformlyOn (fun n => F (u n)) f atTop s) :
    TendstoUniformlyOn F f l s := by
  rw [tendstoUniformlyOn_iff_tendsto, tendsto_iff_seq_tendsto]
  intro u hu
  rw [tendsto_prod_iff'] at hu
  specialize h (fun n => (u n).fst) hu.1
  rw [tendstoUniformlyOn_iff_tendsto] at h
  exact h.comp (tendsto_id.prodMk hu.2)
/-
**TendstoUniformlyOn.seq_tendstoUniformlyOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoUniformlyOn.seq_tendstoUniformlyOn {l : Filter ι} (h : TendstoUnifo
rmlyOn F f l s) (u : Nat -> ι) (hu : Tendsto u atTop l) : TendstoUniformlyOn (fu
n n => F (u n)) f atTop s
参数：h : TendstoUniformlyOn F f l s；u : Nat -> ι；hu : Tendsto u atTop l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendstoUniformlyOn_iff_tendsto`：tendstoUniformlyOn_iff_tendsto : Tendsto
UniformlyOn F f p s ↔ Tendsto (fun q : ι × α => (f q.2, F q.1 q.2)) (p ×ˢ 𝓟 s) (
𝓤 β)
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.Tendsto.prodMk`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f
 : Filter α} {g : Filter β} {h : Filter γ} {m₁ : α → β} {m₂ : α → γ},   Filter.T
endsto m₁ f…
· 使用定理 `Filter.tendsto_fst`：tendsto_fst : Tendsto Prod.fst (f ×ˢ g) f
· 使用定理 `Filter.tendsto_snd`：tendsto_snd : Tendsto Prod.snd (f ×ˢ g) g
-/
theorem TendstoUniformlyOn.seq_tendstoUniformlyOn {l : Filter ι} (h : TendstoUniformlyOn F f l s)
    (u : ℕ → ι) (hu : Tendsto u atTop l) : TendstoUniformlyOn (fun n => F (u n)) f atTop s := by
  rw [tendstoUniformlyOn_iff_tendsto] at h ⊢
  exact h.comp ((hu.comp tendsto_fst).prodMk tendsto_snd)
/-
**tendstoUniformlyOn_iff_seq_tendstoUniformlyOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendstoUniformlyOn_iff_seq_tendstoUniformlyOn {l : Filter ι} [l.IsCountabl
yGenerated] : TendstoUniformlyOn F f l s ↔ forall u : Nat -> ι, Tendsto u atTop 
l -> TendstoUniformlyOn (fun n => F (u n)) f atTop s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TendstoUniformlyOn.seq_tendstoUniformlyOn`：TendstoUniformlyOn.seq_tendst
oUniformlyOn {l : Filter ι} (h : TendstoUniformlyOn F f l s) (u : Nat -> ι) (hu 
: Tendsto u atTop l) : TendstoU…
· 使用定理 `tendstoUniformlyOn_of_seq_tendstoUniformlyOn`：tendstoUniformlyOn_of_seq_
tendstoUniformlyOn {l : Filter ι} [l.IsCountablyGenerated] (h : forall u : Nat -
> ι, Tendsto u atTop l -> TendstoU…
-/
theorem tendstoUniformlyOn_iff_seq_tendstoUniformlyOn {l : Filter ι} [l.IsCountablyGenerated] :
    TendstoUniformlyOn F f l s ↔
      ∀ u : ℕ → ι, Tendsto u atTop l → TendstoUniformlyOn (fun n => F (u n)) f atTop s :=
  ⟨TendstoUniformlyOn.seq_tendstoUniformlyOn, tendstoUniformlyOn_of_seq_tendstoUniformlyOn⟩
/-
**tendstoUniformly_iff_seq_tendstoUniformly** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendstoUniformly_iff_seq_tendstoUniformly {l : Filter ι} [l.IsCountablyGen
erated] : TendstoUniformly F f l ↔ forall u : Nat -> ι, Tendsto u atTop l -> Ten
dstoUniformly (fun n => F (u n)) f atTop
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `tendstoUniformlyOn_iff_seq_tendstoUniformlyOn`：tendstoUniformlyOn_iff_se
q_tendstoUniformlyOn {l : Filter ι} [l.IsCountablyGenerated] : TendstoUniformlyO
n F f l s ↔ forall u : Nat -> ι, Te…
-/
theorem tendstoUniformly_iff_seq_tendstoUniformly {l : Filter ι} [l.IsCountablyGenerated] :
    TendstoUniformly F f l ↔
      ∀ u : ℕ → ι, Tendsto u atTop l → TendstoUniformly (fun n => F (u n)) f atTop := by
  simp_rw [← tendstoUniformlyOn_univ]
  exact tendstoUniformlyOn_iff_seq_tendstoUniformlyOn

end SeqTendsto

section

variable [NeBot p] {L : ι → β} {ℓ : β}

/-
**TendstoUniformlyOnFilter.tendsto_of_eventually_tendsto** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：TendstoUniformlyOnFilter.tendsto_of_eventually_tendsto (h1 : TendstoUnifor
mlyOnFilter F f p p') (h2 : forallᶠ i in p, Tendsto (F i) p' (𝓝 (L i))) (h3 : Te
ndsto L p (𝓝 ℓ)) : Tendsto f p' (𝓝 ℓ)
参数：h1 : TendstoUniformlyOnFilter F f p p'；h2 : forallᶠ i in p, Tendsto (F i) p' 
(𝓝 (L i))；h3 : Tendsto L p (𝓝 ℓ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Uniform.tendsto_nhds_left`：tendsto_nhds_left {f : Filter β} {u : β -> α}
 {a : α} : Tendsto u f (𝓝 a) ↔ Tendsto (fun x => (u x, a)) f (𝓤 α)
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `Set.preimage.eq_1`：∀ {α : Type u} {β : Type v} (f : α → β) (s : Set β), 
f ⁻¹' s = {x | f x ∈ s}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.eventually_iff`：eventually_iff {f : Filter α} {P : α -> Prop} : (
forallᶠ x in f, P x) ↔ { x | P x } in f
· 使用定理 `comp3_mem_uniformity`：comp3_mem_uniformity {s : SetRel α α} (hs : s in 𝓤
 α) : exists t in 𝓤 α, t ○ (t ○ t) subseteq s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Filter.Eventually.curry`：∀ {α : Type u_1} {β : Type u_2} {la : Filter α}
 {lb : Filter β} {p : α × β → Prop},   (∀ᶠ (x : α × β) in la ×ˢ lb, p x) → ∀ᶠ (x
 : α) in la, …
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
-/
theorem TendstoUniformlyOnFilter.tendsto_of_eventually_tendsto
    (h1 : TendstoUniformlyOnFilter F f p p') (h2 : ∀ᶠ i in p, Tendsto (F i) p' (𝓝 (L i)))
    (h3 : Tendsto L p (𝓝 ℓ)) : Tendsto f p' (𝓝 ℓ) := by
  rw [tendsto_nhds_left]
  intro s hs
  rw [mem_map, Set.preimage, ← eventually_iff]
  obtain ⟨t, ht, hts⟩ := comp3_mem_uniformity hs
  have p1 : ∀ᶠ i in p, (L i, ℓ) ∈ t := tendsto_nhds_left.mp h3 ht
  have p2 : ∀ᶠ i in p, ∀ᶠ x in p', (F i x, L i) ∈ t := by
    filter_upwards [h2] with i h2 using tendsto_nhds_left.mp h2 ht
  have p3 : ∀ᶠ i in p, ∀ᶠ x in p', (f x, F i x) ∈ t := (h1 t ht).curry
  obtain ⟨i, p4, p5, p6⟩ := (p1.and (p2.and p3)).exists
  filter_upwards [p5, p6] with x p5 p6 using hts ⟨F i x, p6, L i, p5, p4⟩
/-
**TendstoUniformly.tendsto_of_eventually_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TendstoUniformly.tendsto_of_eventually_tendsto (h1 : TendstoUniformly F f 
p) (h2 : forallᶠ i in p, Tendsto (F i) p' (𝓝 (L i))) (h3 : Tendsto L p (𝓝 ℓ)) : 
Tendsto f p' (𝓝 ℓ)
参数：h1 : TendstoUniformly F f p；h2 : forallᶠ i in p, Tendsto (F i) p' (𝓝 (L i))；h
3 : Tendsto L p (𝓝 ℓ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TendstoUniformlyOnFilter.tendsto_of_eventually_tendsto`：TendstoUniformly
OnFilter.tendsto_of_eventually_tendsto (h1 : TendstoUniformlyOnFilter F f p p') 
(h2 : forallᶠ i in p, Tendsto (F i) p' (𝓝 (L…
· 使用定理 `TendstoUniformlyOnFilter.mono_right`：TendstoUniformlyOnFilter.mono_right
 {p'' : Filter α} (h : TendstoUniformlyOnFilter F f p p') (hp : p'' <= p') : Ten
dstoUniformlyOnFilter F f…
· 使用定理 `TendstoUniformly.tendstoUniformlyOnFilter`：TendstoUniformly.tendstoUnifo
rmlyOnFilter (h : TendstoUniformly F f p) : TendstoUniformlyOnFilter F f p ⊤
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem TendstoUniformly.tendsto_of_eventually_tendsto
    (h1 : TendstoUniformly F f p) (h2 : ∀ᶠ i in p, Tendsto (F i) p' (𝓝 (L i)))
    (h3 : Tendsto L p (𝓝 ℓ)) : Tendsto f p' (𝓝 ℓ) :=
  (h1.tendstoUniformlyOnFilter.mono_right le_top).tendsto_of_eventually_tendsto h2 h3

end

