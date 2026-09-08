/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Order.Filter.SmallSets
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Bases.Finite

/-!
# Convergence of intervals

## Motivation

If a function tends to infinity somewhere, then its derivative is not integrable around this place.
One should be careful about this statement: "somewhere" could mean a point, but also convergence
from the left or from the right, or it could also be infinity, and "around this place" will refer
to these directed neighborhoods. Therefore, the above theorem has many variants. Instead of stating
all these variants, one can look for the common abstraction and have a single version. One has to
be careful: if one considers convergence along a sequence, then the function may tend to infinity
but have a derivative which is small along the sequence (with big jumps in between), so in the end
the derivative may be integrable on a neighborhood of the sequence. What really matters for such
calculus issues in terms of derivatives is that whole intervals are included in the sets we
consider.

The right common abstraction is provided in this file, as the `TendstoIxxClass` typeclass.
It takes as parameters a class of bounded intervals and two real filters `l₁` and `l₂`.
An instance `TendstoIxxClass Icc l₁ l₂` registers that, if `aₙ` and `bₙ` are converging towards
the filter `l₁`, then the intervals `Icc aₙ bₙ` are eventually contained in any given set
belonging to `l₂`. For instance, for `l₁ = 𝓝[>] x` and `l₂ = 𝓝[≥] x`, the strict and large right
neighborhoods of `x` respectively, then given any large right neighborhood `s ∈ 𝓝[≥] x` and any two
sequences `xₙ` and `yₙ` converging strictly to the right of `x`,
then the interval `[xₙ, yₙ]` is eventually contained in `s`. Therefore, the instance
`TendstoIxxClass Icc (𝓝[>] x) (𝓝[≥] x)` holds. Note that one could have taken as
well `l₂ = 𝓝[>] x`, but that `l₁ = 𝓝[≥] x` and `l₂ = 𝓝[>] x` wouldn't work.

With this formalism, the above theorem would read: if `TendstoIxxClass Icc l l` and `f` tends
to infinity along `l`, then its derivative is not integrable on any element of `l`.
Beyond this simple example, this typeclass plays a prominent role in generic formulations of
the fundamental theorem of calculus.

## Main definition

If both `a` and `b` tend to some filter `l₁`, sometimes this implies that `Ixx a b` tends to
`l₂.smallSets`, i.e., for any `s ∈ l₂` eventually `Ixx a b` becomes a subset of `s`. Here and below
`Ixx` is one of `Set.Icc`, `Set.Ico`, `Set.Ioc`, and `Set.Ioo`.
We define `Filter.TendstoIxxClass Ixx l₁ l₂` to be a typeclass representing this property.

The instances provide the best `l₂` for a given `l₁`. In many cases `l₁ = l₂` but sometimes we can
drop an endpoint from an interval: e.g., we prove
`Filter.TendstoIxxClass Set.Ico (𝓟 (Set.Iic a)) (𝓟 (Set.Iio a))`, i.e., if `u₁ n` and `u₂ n` belong
eventually to `Set.Iic a`, then the interval `Set.Ico (u₁ n) (u₂ n)` is eventually included in
`Set.Iio a`.

The next table shows “output” filters `l₂` for different values of `Ixx` and `l₁`. The instances
that need topology are defined in `Mathlib/Topology/Algebra/Ordered`.

|     Input filter | `Ixx = Set.Icc`  | `Ixx = Set.Ico`  | `Ixx = Set.Ioc`  | `Ixx = Set.Ioo`  |
|-----------------:|:----------------:|:----------------:|:----------------:|:----------------:|
|   `Filter.atTop` | `Filter.atTop`   | `Filter.atTop`   | `Filter.atTop`   | `Filter.atTop`   |
|   `Filter.atBot` | `Filter.atBot`   | `Filter.atBot`   | `Filter.atBot`   | `Filter.atBot`   |
|         `pure a` | `pure a`         | `⊥`              | `⊥`              | `⊥`              |
|  `𝓟 (Set.Iic a)` | `𝓟 (Set.Iic a)`  | `𝓟 (Set.Iio a)`  | `𝓟 (Set.Iic a)`  | `𝓟 (Set.Iio a)`  |
|  `𝓟 (Set.Ici a)` | `𝓟 (Set.Ici a)`  | `𝓟 (Set.Ici a)`  | `𝓟 (Set.Ioi a)`  | `𝓟 (Set.Ioi a)`  |
|  `𝓟 (Set.Ioi a)` | `𝓟 (Set.Ioi a)`  | `𝓟 (Set.Ioi a)`  | `𝓟 (Set.Ioi a)`  | `𝓟 (Set.Ioi a)`  |
|  `𝓟 (Set.Iio a)` | `𝓟 (Set.Iio a)`  | `𝓟 (Set.Iio a)`  | `𝓟 (Set.Iio a)`  | `𝓟 (Set.Iio a)`  |
|            `𝓝 a` | `𝓝 a`            | `𝓝 a`            | `𝓝 a`            | `𝓝 a`            |
| `𝓝[Set.Iic a] b` | `𝓝[Set.Iic a] b` | `𝓝[Set.Iio a] b` | `𝓝[Set.Iic a] b` | `𝓝[Set.Iio a] b` |
| `𝓝[Set.Ici a] b` | `𝓝[Set.Ici a] b` | `𝓝[Set.Ici a] b` | `𝓝[Set.Ioi a] b` | `𝓝[Set.Ioi a] b` |
| `𝓝[Set.Ioi a] b` | `𝓝[Set.Ioi a] b` | `𝓝[Set.Ioi a] b` | `𝓝[Set.Ioi a] b` | `𝓝[Set.Ioi a] b` |
| `𝓝[Set.Iio a] b` | `𝓝[Set.Iio a] b` | `𝓝[Set.Iio a] b` | `𝓝[Set.Iio a] b` | `𝓝[Set.Iio a] b` |

-/

public section


variable {α β : Type*}

open Filter Set Function

namespace Filter

section Preorder

/-- A pair of filters `l₁`, `l₂` has `TendstoIxxClass Ixx` property if `Ixx a b` tends to
`l₂.small_sets` as `a` and `b` tend to `l₁`. In all instances `Ixx` is one of `Set.Icc`, `Set.Ico`,
`Set.Ioc`, or `Set.Ioo`. The instances provide the best `l₂` for a given `l₁`. In many cases
`l₁ = l₂` but sometimes we can drop an endpoint from an interval: e.g., we prove
`TendstoIxxClass Set.Ico (𝓟 (Set.Iic a)) (𝓟 (Set.Iio a))`, i.e., if `u₁ n` and `u₂ n` belong
eventually to `Set.Iic a`, then the interval `Set.Ico (u₁ n) (u₂ n)` is eventually included in
`Set.Iio a`.

We mark `l₂` as an `outParam` so that Lean can automatically find an appropriate `l₂` based on
`Ixx` and `l₁`. This way, e.g., `tendsto.Ico h₁ h₂` works without specifying explicitly `l₂`. -/
/-
**Filter.TendstoIxxClass** 是 Mathlib 中的一个归纳类型，位于命名空间 `Filter`。
形式化陈述：{α : Type u_1} → (α → α → Set α) → Filter α → outParam (Filter α) → Prop
参数：α → α → Set α；Filter α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pair of filters `l₁`, `l₂` has `TendstoIxxClass Ixx` property if `Ixx a b` ten
ds to
`l₂.small_sets` as `a` and `b` tend to `l₁`. In all instances `Ixx` is one of `S
et.Icc`, `Set.Ico`,
`Set.Ioc`, or `Set.Ioo`. The instances provide the best `l₂` for a given `l₁`. I
n many cases
`l₁ = l₂` but sometimes we can drop an endpoint from an interval: e.g., we prove
`TendstoIxxClass Set.Ico (𝓟 (Set.Iic a)) (𝓟 (Set.Iio a))`, i.e., if `u₁ n` and `
u₂ n` belong
eventually to `Set.Iic a`, then the interval `Set.Ico (u₁ n) (u₂ n)` is eventual
ly included in
`Set.Iio a`.

We mark `l₂` as an `outParam` so that Lean can automatically find an appropriate
 `l₂` based on
`Ixx` and `l₁`. This way, e.g., `tendsto.Ico h₁ h₂` works without specifying exp
licitly `l₂`.
-/
class TendstoIxxClass (Ixx : α → α → Set α) (l₁ : Filter α) (l₂ : outParam <| Filter α) : Prop where
  /-- `Function.uncurry Ixx` tends to `l₂.smallSets` along `l₁ ×ˢ l₁`. In other words, for any
  `s ∈ l₂` there exists `t ∈ l₁` such that `Ixx x y ⊆ s` whenever `x ∈ t` and `y ∈ t`.

  Use lemmas like `Filter.Tendsto.Icc` instead. -/
  tendsto_Ixx : Tendsto (fun p : α × α => Ixx p.1 p.2) (l₁ ×ˢ l₁) l₂.smallSets
/-
**Filter.tendstoIxxClass_principal** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendstoIxxClass_principal {s t : Set α} {Ixx : α -> α -> Set α} : TendstoI
xxClass Ixx (𝓟 s) (𝓟 t) ↔ forallᵉ (x in s) (y in s), Ixx x y subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.TendstoIxxClass.tendsto_Ixx`：∀ {α : Type u_1} {Ixx : α → α → Set 
α} {l₁ : Filter α} {l₂ : outParam (Filter α)}   [self : Filter.TendstoIxxClass I
xx l₁ l₂], Filter.Tendst…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Filter.prod_principal_principal`：prod_principal_principal {s : Set α} {t
 : Set β} : 𝓟 s ×ˢ 𝓟 t = 𝓟 (s ×ˢ t)
· 使用定理 `Filter.smallSets_principal`：smallSets_principal (s : Set α) : (𝓟 s).smal
lSets = 𝓟 (𝒫 s)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendstoIxxClass_principal {s t : Set α} {Ixx : α → α → Set α} :
    TendstoIxxClass Ixx (𝓟 s) (𝓟 t) ↔ ∀ᵉ (x ∈ s) (y ∈ s), Ixx x y ⊆ t :=
  Iff.trans ⟨fun h => h.1, fun h => ⟨h⟩⟩ <| by
    simp only [smallSets_principal, prod_principal_principal, tendsto_principal_principal,
      forall_prod_set, mem_powerset_iff]
/-
**Filter.tendstoIxxClass_inf** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendstoIxxClass_inf {l₁ l₁' l₂ l₂' : Filter α} {Ixx} [h : TendstoIxxClass 
Ixx l₁ l₂] [h' : TendstoIxxClass Ixx l₁' l₂'] : TendstoIxxClass Ixx (l₁ ⊓ l₁') (
l₂ ⊓ l₂')
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.smallSets_inf`：smallSets_inf (l₁ l₂ : Filter α) : (l₁ ⊓ l₂).small
Sets = l₁.smallSets ⊓ l₂.smallSets
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.prod_inf_prod`：prod_inf_prod {f₁ f₂ : Filter α} {g₁ g₂ : Filter β
} : (f₁ ×ˢ g₁) ⊓ (f₂ ×ˢ g₂) = (f₁ ⊓ f₂) ×ˢ (g₁ ⊓ g₂)
· 使用定理 `Filter.Tendsto.inf`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x₁ x₂ :
 Filter α} {y₁ y₂ : Filter β},   Filter.Tendsto f x₁ y₁ → Filter.Tendsto f x₂ y₂
 → Filte…
· 使用定理 `Filter.TendstoIxxClass.tendsto_Ixx`：∀ {α : Type u_1} {Ixx : α → α → Set 
α} {l₁ : Filter α} {l₂ : outParam (Filter α)}   [self : Filter.TendstoIxxClass I
xx l₁ l₂], Filter.Tendst…
-/
theorem tendstoIxxClass_inf {l₁ l₁' l₂ l₂' : Filter α} {Ixx} [h : TendstoIxxClass Ixx l₁ l₂]
    [h' : TendstoIxxClass Ixx l₁' l₂'] : TendstoIxxClass Ixx (l₁ ⊓ l₁') (l₂ ⊓ l₂') :=
  ⟨by simpa only [prod_inf_prod, smallSets_inf] using h.1.inf h'.1⟩
/-
**Filter.tendstoIxxClass_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：tendstoIxxClass_of_subset {l₁ l₂ : Filter α} {Ixx Ixx' : α -> α -> Set α} 
(h : forall a b, Ixx a b subseteq Ixx' a b) [h' : TendstoIxxClass Ixx' l₁ l₂] : 
TendstoIxxClass Ixx l₁ l₂
参数：h : forall a b, Ixx a b subseteq Ixx' a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.smallSets_mono`：∀ {α : Type u_1} {β : Type u_2} {la : Fil
ter α} {lb : Filter β} {s t : α → Set β},   Filter.Tendsto t la lb.smallSets → (
∀ᶠ (x : α) in la, s…
· 使用定理 `Filter.TendstoIxxClass.tendsto_Ixx`：∀ {α : Type u_1} {Ixx : α → α → Set 
α} {l₁ : Filter α} {l₂ : outParam (Filter α)}   [self : Filter.TendstoIxxClass I
xx l₁ l₂], Filter.Tendst…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Prod.forall`：∀ {α : Type u_1} {β : Type u_2} {p : α × β → Prop}, (∀ (x :
 α × β), p x) ↔ ∀ (a : α) (b : β), p (a, b)
-/
theorem tendstoIxxClass_of_subset {l₁ l₂ : Filter α} {Ixx Ixx' : α → α → Set α}
    (h : ∀ a b, Ixx a b ⊆ Ixx' a b) [h' : TendstoIxxClass Ixx' l₁ l₂] : TendstoIxxClass Ixx l₁ l₂ :=
  ⟨h'.1.smallSets_mono <| Eventually.of_forall <| Prod.forall.2 h⟩
/-
**Filter.HasBasis.tendstoIxxClass** 是 Mathlib 中的一个定理，位于命名空间 `Filter.HasBasis`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_3} {p : ι → Prop} {s : ι → Set α} {l : Filter
 α},   l.HasBasis p s →     ∀ {Ixx : α → α → Set α}, (∀ (i : ι), p i → ∀ x ∈ s i
, ∀ y ∈ s i, Ixx x y ⊆ s i) → Filter.TendstoIxxClass Ixx l l
参数：∀ (i : ι), p i → ∀ x ∈ s i, ∀ y ∈ s i, Ixx x y ⊆ s i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `Filter.HasBasis.prod_self`：∀ {α : Type u_1} {ι : Sort u_4} {la : Filter 
α} {pa : ι → Prop} {sa : ι → Set α},   la.HasBasis pa sa → (la ×ˢ la).HasBasis p
a fun i => sa i…
· 使用定理 `Filter.HasBasis.smallSets`：∀ {α : Type u_1} {ι : Sort u_3} {l : Filter α
} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → l.smallSets.HasBasis p fun 
i => 𝒫 s i
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem HasBasis.tendstoIxxClass {ι : Type*} {p : ι → Prop} {s} {l : Filter α}
    (hl : l.HasBasis p s) {Ixx : α → α → Set α}
    (H : ∀ i, p i → ∀ x ∈ s i, ∀ y ∈ s i, Ixx x y ⊆ s i) : TendstoIxxClass Ixx l l :=
  ⟨(hl.prod_self.tendsto_iff hl.smallSets).2 fun i hi => ⟨i, hi, fun _ h => H i hi _ h.1 _ h.2⟩⟩

variable [Preorder α]
/-
**Filter.Tendsto.Icc** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] {l₁ l₂ : Filter α} [Fi
lter.TendstoIxxClass Set.Icc l₁ l₂]   {lb : Filter β} {u₁ u₂ : β → α},   Filter.
Tendsto u₁ lb l₁ → Filter.Tendsto u₂ lb l₁ → Filter.Tendsto (fun x => Set.Icc (u
₁ x) (u₂ x)) lb l₂.smallSets
参数：fun x => Set.Icc (u₁ x) (u₂ x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.TendstoIxxClass.tendsto_Ixx`：∀ {α : Type u_1} {Ixx : α → α → Set 
α} {l₁ : Filter α} {l₂ : outParam (Filter α)}   [self : Filter.TendstoIxxClass I
xx l₁ l₂], Filter.Tendst…
· 使用定理 `Filter.Tendsto.prodMk`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f
 : Filter α} {g : Filter β} {h : Filter γ} {m₁ : α → β} {m₂ : α → γ},   Filter.T
endsto m₁ f…
-/
protected theorem Tendsto.Icc {l₁ l₂ : Filter α} [TendstoIxxClass Icc l₁ l₂] {lb : Filter β}
    {u₁ u₂ : β → α} (h₁ : Tendsto u₁ lb l₁) (h₂ : Tendsto u₂ lb l₁) :
    Tendsto (fun x => Icc (u₁ x) (u₂ x)) lb l₂.smallSets :=
  (@TendstoIxxClass.tendsto_Ixx α Set.Icc _ _ _).comp <| h₁.prodMk h₂
/-
**Filter.Tendsto.Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] {l₁ l₂ : Filter α} [Fi
lter.TendstoIxxClass Set.Ioc l₁ l₂]   {lb : Filter β} {u₁ u₂ : β → α},   Filter.
Tendsto u₁ lb l₁ → Filter.Tendsto u₂ lb l₁ → Filter.Tendsto (fun x => Set.Ioc (u
₁ x) (u₂ x)) lb l₂.smallSets
参数：fun x => Set.Ioc (u₁ x) (u₂ x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.TendstoIxxClass.tendsto_Ixx`：∀ {α : Type u_1} {Ixx : α → α → Set 
α} {l₁ : Filter α} {l₂ : outParam (Filter α)}   [self : Filter.TendstoIxxClass I
xx l₁ l₂], Filter.Tendst…
· 使用定理 `Filter.Tendsto.prodMk`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f
 : Filter α} {g : Filter β} {h : Filter γ} {m₁ : α → β} {m₂ : α → γ},   Filter.T
endsto m₁ f…
-/
protected theorem Tendsto.Ioc {l₁ l₂ : Filter α} [TendstoIxxClass Ioc l₁ l₂] {lb : Filter β}
    {u₁ u₂ : β → α} (h₁ : Tendsto u₁ lb l₁) (h₂ : Tendsto u₂ lb l₁) :
    Tendsto (fun x => Ioc (u₁ x) (u₂ x)) lb l₂.smallSets :=
  (@TendstoIxxClass.tendsto_Ixx α Set.Ioc _ _ _).comp <| h₁.prodMk h₂
/-
**Filter.Tendsto.Ico** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] {l₁ l₂ : Filter α} [Fi
lter.TendstoIxxClass Set.Ico l₁ l₂]   {lb : Filter β} {u₁ u₂ : β → α},   Filter.
Tendsto u₁ lb l₁ → Filter.Tendsto u₂ lb l₁ → Filter.Tendsto (fun x => Set.Ico (u
₁ x) (u₂ x)) lb l₂.smallSets
参数：fun x => Set.Ico (u₁ x) (u₂ x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.TendstoIxxClass.tendsto_Ixx`：∀ {α : Type u_1} {Ixx : α → α → Set 
α} {l₁ : Filter α} {l₂ : outParam (Filter α)}   [self : Filter.TendstoIxxClass I
xx l₁ l₂], Filter.Tendst…
· 使用定理 `Filter.Tendsto.prodMk`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f
 : Filter α} {g : Filter β} {h : Filter γ} {m₁ : α → β} {m₂ : α → γ},   Filter.T
endsto m₁ f…
-/
protected theorem Tendsto.Ico {l₁ l₂ : Filter α} [TendstoIxxClass Ico l₁ l₂] {lb : Filter β}
    {u₁ u₂ : β → α} (h₁ : Tendsto u₁ lb l₁) (h₂ : Tendsto u₂ lb l₁) :
    Tendsto (fun x => Ico (u₁ x) (u₂ x)) lb l₂.smallSets :=
  (@TendstoIxxClass.tendsto_Ixx α Set.Ico _ _ _).comp <| h₁.prodMk h₂
/-
**Filter.Tendsto.Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] {l₁ l₂ : Filter α} [Fi
lter.TendstoIxxClass Set.Ioo l₁ l₂]   {lb : Filter β} {u₁ u₂ : β → α},   Filter.
Tendsto u₁ lb l₁ → Filter.Tendsto u₂ lb l₁ → Filter.Tendsto (fun x => Set.Ioo (u
₁ x) (u₂ x)) lb l₂.smallSets
参数：fun x => Set.Ioo (u₁ x) (u₂ x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.TendstoIxxClass.tendsto_Ixx`：∀ {α : Type u_1} {Ixx : α → α → Set 
α} {l₁ : Filter α} {l₂ : outParam (Filter α)}   [self : Filter.TendstoIxxClass I
xx l₁ l₂], Filter.Tendst…
· 使用定理 `Filter.Tendsto.prodMk`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f
 : Filter α} {g : Filter β} {h : Filter γ} {m₁ : α → β} {m₂ : α → γ},   Filter.T
endsto m₁ f…
-/
protected theorem Tendsto.Ioo {l₁ l₂ : Filter α} [TendstoIxxClass Ioo l₁ l₂] {lb : Filter β}
    {u₁ u₂ : β → α} (h₁ : Tendsto u₁ lb l₁) (h₂ : Tendsto u₂ lb l₁) :
    Tendsto (fun x => Ioo (u₁ x) (u₂ x)) lb l₂.smallSets :=
  (@TendstoIxxClass.tendsto_Ixx α Set.Ioo _ _ _).comp <| h₁.prodMk h₂
/-
**Filter.tendsto_Icc_atTop_atTop** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：tendsto_Icc_atTop_atTop : TendstoIxxClass Icc (atTop : Filter α) atTop
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.tendstoIxxClass`：∀ {α : Type u_1} {ι : Type u_3} {p : ι 
→ Prop} {s : ι → Set α} {l : Filter α},   l.HasBasis p s →     ∀ {Ixx : α → α → 
Set α}, (∀ (i : ι), p…
· 使用定理 `Filter.hasBasis_iInf_principal_finite`：hasBasis_iInf_principal_finite {ι
 : Type*} (s : ι -> Set α) : (⨅ i, 𝓟 (s i)).HasBasis (fun t : Set ι => t.Finite)
 fun t => ⋂ i in t, s i
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
· 使用定理 `Set.ordConnected_biInter`：ordConnected_biInter {ι : Sort*} {p : ι -> Pro
p} {s : forall i, p i -> Set α} (hs : forall i hi, OrdConnected (s i hi)) : OrdC
onnected (⋂ (i…
-/
instance tendsto_Icc_atTop_atTop : TendstoIxxClass Icc (atTop : Filter α) atTop :=
  (hasBasis_iInf_principal_finite _).tendstoIxxClass fun _ _ =>
    Set.OrdConnected.out <| ordConnected_biInter fun _ _ => ordConnected_Ici
/-
**Filter.tendsto_Ico_atTop_atTop** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：tendsto_Ico_atTop_atTop : TendstoIxxClass Ico (atTop : Filter α) atTop
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendstoIxxClass_of_subset`：tendstoIxxClass_of_subset {l₁ l₂ : Fil
ter α} {Ixx Ixx' : α -> α -> Set α} (h : forall a b, Ixx a b subseteq Ixx' a b) 
[h' : TendstoIxxClass …
· 使用定理 `Set.Ico_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico b a ⊆ Set.Icc b a
-/
instance tendsto_Ico_atTop_atTop : TendstoIxxClass Ico (atTop : Filter α) atTop :=
  tendstoIxxClass_of_subset fun _ _ => Ico_subset_Icc_self
/-
**Filter.tendsto_Ioc_atTop_atTop** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：tendsto_Ioc_atTop_atTop : TendstoIxxClass Ioc (atTop : Filter α) atTop
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendstoIxxClass_of_subset`：tendstoIxxClass_of_subset {l₁ l₂ : Fil
ter α} {Ixx Ixx' : α -> α -> Set α} (h : forall a b, Ixx a b subseteq Ixx' a b) 
[h' : TendstoIxxClass …
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
-/
instance tendsto_Ioc_atTop_atTop : TendstoIxxClass Ioc (atTop : Filter α) atTop :=
  tendstoIxxClass_of_subset fun _ _ => Ioc_subset_Icc_self
/-
**Filter.tendsto_Ioo_atTop_atTop** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：tendsto_Ioo_atTop_atTop : TendstoIxxClass Ioo (atTop : Filter α) atTop
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendstoIxxClass_of_subset`：tendstoIxxClass_of_subset {l₁ l₂ : Fil
ter α} {Ixx Ixx' : α -> α -> Set α} (h : forall a b, Ixx a b subseteq Ixx' a b) 
[h' : TendstoIxxClass …
· 使用定理 `Set.Ioo_subset_Icc_self`：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b
-/
instance tendsto_Ioo_atTop_atTop : TendstoIxxClass Ioo (atTop : Filter α) atTop :=
  tendstoIxxClass_of_subset fun _ _ => Ioo_subset_Icc_self
/-
**Filter.tendsto_Icc_atBot_atBot** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：tendsto_Icc_atBot_atBot : TendstoIxxClass Icc (atBot : Filter α) atBot
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.tendstoIxxClass`：∀ {α : Type u_1} {ι : Type u_3} {p : ι 
→ Prop} {s : ι → Set α} {l : Filter α},   l.HasBasis p s →     ∀ {Ixx : α → α → 
Set α}, (∀ (i : ι), p…
· 使用定理 `Filter.hasBasis_iInf_principal_finite`：hasBasis_iInf_principal_finite {ι
 : Type*} (s : ι -> Set α) : (⨅ i, 𝓟 (s i)).HasBasis (fun t : Set ι => t.Finite)
 fun t => ⋂ i in t, s i
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
· 使用定理 `Set.ordConnected_biInter`：ordConnected_biInter {ι : Sort*} {p : ι -> Pro
p} {s : forall i, p i -> Set α} (hs : forall i hi, OrdConnected (s i hi)) : OrdC
onnected (⋂ (i…
· 使用定理 `Set.ordConnected_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, (Set
.Iic a).OrdConnected
-/
instance tendsto_Icc_atBot_atBot : TendstoIxxClass Icc (atBot : Filter α) atBot :=
  (hasBasis_iInf_principal_finite _).tendstoIxxClass fun _ _ =>
    Set.OrdConnected.out <| ordConnected_biInter fun _ _ => ordConnected_Iic
/-
**Filter.tendsto_Ico_atBot_atBot** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：tendsto_Ico_atBot_atBot : TendstoIxxClass Ico (atBot : Filter α) atBot
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendstoIxxClass_of_subset`：tendstoIxxClass_of_subset {l₁ l₂ : Fil
ter α} {Ixx Ixx' : α -> α -> Set α} (h : forall a b, Ixx a b subseteq Ixx' a b) 
[h' : TendstoIxxClass …
· 使用定理 `Set.Ico_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico b a ⊆ Set.Icc b a
-/
instance tendsto_Ico_atBot_atBot : TendstoIxxClass Ico (atBot : Filter α) atBot :=
  tendstoIxxClass_of_subset fun _ _ => Ico_subset_Icc_self
/-
**Filter.tendsto_Ioc_atBot_atBot** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：tendsto_Ioc_atBot_atBot : TendstoIxxClass Ioc (atBot : Filter α) atBot
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendstoIxxClass_of_subset`：tendstoIxxClass_of_subset {l₁ l₂ : Fil
ter α} {Ixx Ixx' : α -> α -> Set α} (h : forall a b, Ixx a b subseteq Ixx' a b) 
[h' : TendstoIxxClass …
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
-/
instance tendsto_Ioc_atBot_atBot : TendstoIxxClass Ioc (atBot : Filter α) atBot :=
  tendstoIxxClass_of_subset fun _ _ => Ioc_subset_Icc_self
/-
**Filter.tendsto_Ioo_atBot_atBot** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：tendsto_Ioo_atBot_atBot : TendstoIxxClass Ioo (atBot : Filter α) atBot
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendstoIxxClass_of_subset`：tendstoIxxClass_of_subset {l₁ l₂ : Fil
ter α} {Ixx Ixx' : α -> α -> Set α} (h : forall a b, Ixx a b subseteq Ixx' a b) 
[h' : TendstoIxxClass …
· 使用定理 `Set.Ioo_subset_Icc_self`：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b
-/
instance tendsto_Ioo_atBot_atBot : TendstoIxxClass Ioo (atBot : Filter α) atBot :=
  tendstoIxxClass_of_subset fun _ _ => Ioo_subset_Icc_self
/-
**Filter.OrdConnected.tendsto_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Filter.OrdConnected
`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} [hs : s.OrdConnected],   
Filter.TendstoIxxClass Set.Icc (Filter.principal s) (Filter.principal s)
参数：Filter.principal s；Filter.principal s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendstoIxxClass_principal`：tendstoIxxClass_principal {s t : Set α
} {Ixx : α -> α -> Set α} : TendstoIxxClass Ixx (𝓟 s) (𝓟 t) ↔ forallᵉ (x in s) (
y in s), Ixx x y subse…
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
-/
instance OrdConnected.tendsto_Icc {s : Set α} [hs : OrdConnected s] :
    TendstoIxxClass Icc (𝓟 s) (𝓟 s) :=
  tendstoIxxClass_principal.2 hs.out
/-
**Filter.tendsto_Ico_Ici_Ici** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：tendsto_Ico_Ici_Ici {a : α} : TendstoIxxClass Ico (𝓟 (Ici a)) (𝓟 (Ici a))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendstoIxxClass_of_subset`：tendstoIxxClass_of_subset {l₁ l₂ : Fil
ter α} {Ixx Ixx' : α -> α -> Set α} (h : forall a b, Ixx a b subseteq Ixx' a b) 
[h' : TendstoIxxClass …
· 使用定理 `Set.Ico_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico b a ⊆ Set.Icc b a
· 使用定理 `Filter.OrdConnected.tendsto_Icc`：∀ {α : Type u_1} [inst : Preorder α] {s
 : Set α} [hs : s.OrdConnected],   Filter.TendstoIxxClass Set.Icc (Filter.princi
pal s) (Filter.princi…
-/
instance tendsto_Ico_Ici_Ici {a : α} : TendstoIxxClass Ico (𝓟 (Ici a)) (𝓟 (Ici a)) :=
  tendstoIxxClass_of_subset fun _ _ => Ico_subset_Icc_self
/-
**Filter.tendsto_Ico_Ioi_Ioi** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：tendsto_Ico_Ioi_Ioi {a : α} : TendstoIxxClass Ico (𝓟 (Ioi a)) (𝓟 (Ioi a))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendstoIxxClass_of_subset`：tendstoIxxClass_of_subset {l₁ l₂ : Fil
ter α} {Ixx Ixx' : α -> α -> Set α} (h : forall a b, Ixx a b subseteq Ixx' a b) 
[h' : TendstoIxxClass …
· 使用定理 `Set.Ico_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico b a ⊆ Set.Icc b a
· 使用定理 `Filter.OrdConnected.tendsto_Icc`：∀ {α : Type u_1} [inst : Preorder α] {s
 : Set α} [hs : s.OrdConnected],   Filter.TendstoIxxClass Set.Icc (Filter.princi
pal s) (Filter.princi…
-/
instance tendsto_Ico_Ioi_Ioi {a : α} : TendstoIxxClass Ico (𝓟 (Ioi a)) (𝓟 (Ioi a)) :=
  tendstoIxxClass_of_subset fun _ _ => Ico_subset_Icc_self
/-
**Filter.tendsto_Ico_Iic_Iio** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：tendsto_Ico_Iic_Iio {a : α} : TendstoIxxClass Ico (𝓟 (Iic a)) (𝓟 (Iio a))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendstoIxxClass_principal`：tendstoIxxClass_principal {s t : Set α
} {Ixx : α -> α -> Set α} : TendstoIxxClass Ixx (𝓟 s) (𝓟 t) ↔ forallᵉ (x in s) (
y in s), Ixx x y subse…
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
instance tendsto_Ico_Iic_Iio {a : α} : TendstoIxxClass Ico (𝓟 (Iic a)) (𝓟 (Iio a)) :=
  tendstoIxxClass_principal.2 fun _ _ _ h₁ _ h₂ => lt_of_lt_of_le h₂.2 h₁
/-
**Filter.tendsto_Ico_Iio_Iio** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：tendsto_Ico_Iio_Iio {a : α} : TendstoIxxClass Ico (𝓟 (Iio a)) (𝓟 (Iio a))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendstoIxxClass_of_subset`：tendstoIxxClass_of_subset {l₁ l₂ : Fil
ter α} {Ixx Ixx' : α -> α -> Set α} (h : forall a b, Ixx a b subseteq Ixx' a b) 
[h' : TendstoIxxClass …
· 使用定理 `Set.Ico_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico b a ⊆ Set.Icc b a
· 使用定理 `Filter.OrdConnected.tendsto_Icc`：∀ {α : Type u_1} [inst : Preorder α] {s
 : Set α} [hs : s.OrdConnected],   Filter.TendstoIxxClass Set.Icc (Filter.princi
pal s) (Filter.princi…
· 使用定理 `Set.ordConnected_Iio`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, (Set
.Iio a).OrdConnected
-/
instance tendsto_Ico_Iio_Iio {a : α} : TendstoIxxClass Ico (𝓟 (Iio a)) (𝓟 (Iio a)) :=
  tendstoIxxClass_of_subset fun _ _ => Ico_subset_Icc_self
/-
**Filter.tendsto_Ioc_Ici_Ioi** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：tendsto_Ioc_Ici_Ioi {a : α} : TendstoIxxClass Ioc (𝓟 (Ici a)) (𝓟 (Ioi a))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendstoIxxClass_principal`：tendstoIxxClass_principal {s t : Set α
} {Ixx : α -> α -> Set α} : TendstoIxxClass Ixx (𝓟 s) (𝓟 t) ↔ forallᵉ (x in s) (
y in s), Ixx x y subse…
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
instance tendsto_Ioc_Ici_Ioi {a : α} : TendstoIxxClass Ioc (𝓟 (Ici a)) (𝓟 (Ioi a)) :=
  tendstoIxxClass_principal.2 fun _ h₁ _ _ _ h₂ => lt_of_le_of_lt h₁ h₂.1
/-
**Filter.tendsto_Ioc_Iic_Iic** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：tendsto_Ioc_Iic_Iic {a : α} : TendstoIxxClass Ioc (𝓟 (Iic a)) (𝓟 (Iic a))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendstoIxxClass_of_subset`：tendstoIxxClass_of_subset {l₁ l₂ : Fil
ter α} {Ixx Ixx' : α -> α -> Set α} (h : forall a b, Ixx a b subseteq Ixx' a b) 
[h' : TendstoIxxClass …
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
· 使用定理 `Filter.OrdConnected.tendsto_Icc`：∀ {α : Type u_1} [inst : Preorder α] {s
 : Set α} [hs : s.OrdConnected],   Filter.TendstoIxxClass Set.Icc (Filter.princi
pal s) (Filter.princi…
· 使用定理 `Set.ordConnected_Iic`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, (Set
.Iic a).OrdConnected
-/
instance tendsto_Ioc_Iic_Iic {a : α} : TendstoIxxClass Ioc (𝓟 (Iic a)) (𝓟 (Iic a)) :=
  tendstoIxxClass_of_subset fun _ _ => Ioc_subset_Icc_self
/-
**Filter.tendsto_Ioc_Iio_Iio** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：tendsto_Ioc_Iio_Iio {a : α} : TendstoIxxClass Ioc (𝓟 (Iio a)) (𝓟 (Iio a))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendstoIxxClass_of_subset`：tendstoIxxClass_of_subset {l₁ l₂ : Fil
ter α} {Ixx Ixx' : α -> α -> Set α} (h : forall a b, Ixx a b subseteq Ixx' a b) 
[h' : TendstoIxxClass …
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
· 使用定理 `Filter.OrdConnected.tendsto_Icc`：∀ {α : Type u_1} [inst : Preorder α] {s
 : Set α} [hs : s.OrdConnected],   Filter.TendstoIxxClass Set.Icc (Filter.princi
pal s) (Filter.princi…
· 使用定理 `Set.ordConnected_Iio`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, (Set
.Iio a).OrdConnected
-/
instance tendsto_Ioc_Iio_Iio {a : α} : TendstoIxxClass Ioc (𝓟 (Iio a)) (𝓟 (Iio a)) :=
  tendstoIxxClass_of_subset fun _ _ => Ioc_subset_Icc_self
/-
**Filter.tendsto_Ioc_Ioi_Ioi** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：tendsto_Ioc_Ioi_Ioi {a : α} : TendstoIxxClass Ioc (𝓟 (Ioi a)) (𝓟 (Ioi a))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendstoIxxClass_of_subset`：tendstoIxxClass_of_subset {l₁ l₂ : Fil
ter α} {Ixx Ixx' : α -> α -> Set α} (h : forall a b, Ixx a b subseteq Ixx' a b) 
[h' : TendstoIxxClass …
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
· 使用定理 `Filter.OrdConnected.tendsto_Icc`：∀ {α : Type u_1} [inst : Preorder α] {s
 : Set α} [hs : s.OrdConnected],   Filter.TendstoIxxClass Set.Icc (Filter.princi
pal s) (Filter.princi…
-/
instance tendsto_Ioc_Ioi_Ioi {a : α} : TendstoIxxClass Ioc (𝓟 (Ioi a)) (𝓟 (Ioi a)) :=
  tendstoIxxClass_of_subset fun _ _ => Ioc_subset_Icc_self
/-
**Filter.tendsto_Ioo_Ici_Ioi** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：tendsto_Ioo_Ici_Ioi {a : α} : TendstoIxxClass Ioo (𝓟 (Ici a)) (𝓟 (Ioi a))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendstoIxxClass_of_subset`：tendstoIxxClass_of_subset {l₁ l₂ : Fil
ter α} {Ixx Ixx' : α -> α -> Set α} (h : forall a b, Ixx a b subseteq Ixx' a b) 
[h' : TendstoIxxClass …
· 使用定理 `Set.Ioo_subset_Ioc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo b a ⊆ Set.Ioc b a
-/
instance tendsto_Ioo_Ici_Ioi {a : α} : TendstoIxxClass Ioo (𝓟 (Ici a)) (𝓟 (Ioi a)) :=
  tendstoIxxClass_of_subset fun _ _ => Ioo_subset_Ioc_self
/-
**Filter.tendsto_Ioo_Iic_Iio** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：tendsto_Ioo_Iic_Iio {a : α} : TendstoIxxClass Ioo (𝓟 (Iic a)) (𝓟 (Iio a))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendstoIxxClass_of_subset`：tendstoIxxClass_of_subset {l₁ l₂ : Fil
ter α} {Ixx Ixx' : α -> α -> Set α} (h : forall a b, Ixx a b subseteq Ixx' a b) 
[h' : TendstoIxxClass …
· 使用定理 `Set.Ioo_subset_Ico_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo a b ⊆ Set.Ico a b
-/
instance tendsto_Ioo_Iic_Iio {a : α} : TendstoIxxClass Ioo (𝓟 (Iic a)) (𝓟 (Iio a)) :=
  tendstoIxxClass_of_subset fun _ _ => Ioo_subset_Ico_self
/-
**Filter.tendsto_Ioo_Ioi_Ioi** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：tendsto_Ioo_Ioi_Ioi {a : α} : TendstoIxxClass Ioo (𝓟 (Ioi a)) (𝓟 (Ioi a))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendstoIxxClass_of_subset`：tendstoIxxClass_of_subset {l₁ l₂ : Fil
ter α} {Ixx Ixx' : α -> α -> Set α} (h : forall a b, Ixx a b subseteq Ixx' a b) 
[h' : TendstoIxxClass …
· 使用定理 `Set.Ioo_subset_Ioc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo b a ⊆ Set.Ioc b a
-/
instance tendsto_Ioo_Ioi_Ioi {a : α} : TendstoIxxClass Ioo (𝓟 (Ioi a)) (𝓟 (Ioi a)) :=
  tendstoIxxClass_of_subset fun _ _ => Ioo_subset_Ioc_self
/-
**Filter.tendsto_Ioo_Iio_Iio** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：tendsto_Ioo_Iio_Iio {a : α} : TendstoIxxClass Ioo (𝓟 (Iio a)) (𝓟 (Iio a))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendstoIxxClass_of_subset`：tendstoIxxClass_of_subset {l₁ l₂ : Fil
ter α} {Ixx Ixx' : α -> α -> Set α} (h : forall a b, Ixx a b subseteq Ixx' a b) 
[h' : TendstoIxxClass …
· 使用定理 `Set.Ioo_subset_Ioc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo b a ⊆ Set.Ioc b a
-/
instance tendsto_Ioo_Iio_Iio {a : α} : TendstoIxxClass Ioo (𝓟 (Iio a)) (𝓟 (Iio a)) :=
  tendstoIxxClass_of_subset fun _ _ => Ioo_subset_Ioc_self
/-
**Filter.tendsto_Icc_Icc_Icc** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：tendsto_Icc_Icc_Icc {a b : α} : TendstoIxxClass Icc (𝓟 (Icc a b)) (𝓟 (Icc 
a b))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendstoIxxClass_principal`：tendstoIxxClass_principal {s t : Set α
} {Ixx : α -> α -> Set α} : TendstoIxxClass Ixx (𝓟 s) (𝓟 t) ↔ forallᵉ (x in s) (
y in s), Ixx x y subse…
· 使用定理 `Set.Icc_subset_Icc`：Icc_subset_Icc (ha : a₂ <= a₁) (hb : b₁ <= b₂) : Icc
 a₁ b₁ subseteq Icc a₂ b₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
instance tendsto_Icc_Icc_Icc {a b : α} : TendstoIxxClass Icc (𝓟 (Icc a b)) (𝓟 (Icc a b)) :=
  tendstoIxxClass_principal.mpr fun _x hx _y hy => Icc_subset_Icc hx.1 hy.2
/-
**Filter.tendsto_Ioc_Icc_Icc** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：tendsto_Ioc_Icc_Icc {a b : α} : TendstoIxxClass Ioc (𝓟 (Icc a b)) (𝓟 (Icc 
a b))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendstoIxxClass_of_subset`：tendstoIxxClass_of_subset {l₁ l₂ : Fil
ter α} {Ixx Ixx' : α -> α -> Set α} (h : forall a b, Ixx a b subseteq Ixx' a b) 
[h' : TendstoIxxClass …
· 使用定理 `Set.Ioc_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Icc a b
-/
instance tendsto_Ioc_Icc_Icc {a b : α} : TendstoIxxClass Ioc (𝓟 (Icc a b)) (𝓟 (Icc a b)) :=
  tendstoIxxClass_of_subset fun _ _ => Ioc_subset_Icc_self

end Preorder

section PartialOrder

variable [PartialOrder α]

/-
**Filter.tendsto_Icc_pure_pure** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：tendsto_Icc_pure_pure {a : α} : TendstoIxxClass Icc (pure a) (pure a : Fil
ter α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.principal_singleton`：principal_singleton (a : α) : 𝓟 {a} = pure a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendstoIxxClass_principal`：tendstoIxxClass_principal {s t : Set α
} {Ixx : α -> α -> Set α} : TendstoIxxClass Ixx (𝓟 s) (𝓟 t) ↔ forallᵉ (x in s) (
y in s), Ixx x y subse…
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
· 使用定理 `Set.ordConnected_singleton`：ordConnected_singleton {α : Type*} [PartialO
rder α] {a : α} : OrdConnected ({a} : Set α)
-/
instance tendsto_Icc_pure_pure {a : α} : TendstoIxxClass Icc (pure a) (pure a : Filter α) := by
  rw [← principal_singleton]
  exact tendstoIxxClass_principal.2 ordConnected_singleton.out
/-
**Filter.tendsto_Ico_pure_bot** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：tendsto_Ico_pure_bot {a : α} : TendstoIxxClass Ico (pure a) ⊥
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.prod_pure`：prod_pure {b : β} : f ×ˢ pure b = map (fun a => (a, b)
) f
· 使用定理 `Filter.smallSets_bot`：smallSets_bot : (⊥ : Filter α).smallSets = pure ∅
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Ico_eq_empty`：Ico_eq_empty (h : ¬a < b) : Ico a b = ∅
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance tendsto_Ico_pure_bot {a : α} : TendstoIxxClass Ico (pure a) ⊥ :=
  ⟨by simp⟩
/-
**Filter.tendsto_Ioc_pure_bot** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：tendsto_Ioc_pure_bot {a : α} : TendstoIxxClass Ioc (pure a) ⊥
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.prod_pure`：prod_pure {b : β} : f ×ˢ pure b = map (fun a => (a, b)
) f
· 使用定理 `Filter.smallSets_bot`：smallSets_bot : (⊥ : Filter α).smallSets = pure ∅
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Ioc_eq_empty`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, ¬b < a
 → Set.Ioc b a = ∅
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance tendsto_Ioc_pure_bot {a : α} : TendstoIxxClass Ioc (pure a) ⊥ :=
  ⟨by simp⟩
/-
**Filter.tendsto_Ioo_pure_bot** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：tendsto_Ioo_pure_bot {a : α} : TendstoIxxClass Ioo (pure a) ⊥
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.prod_pure`：prod_pure {b : β} : f ×ˢ pure b = map (fun a => (a, b)
) f
· 使用定理 `Filter.smallSets_bot`：smallSets_bot : (⊥ : Filter α).smallSets = pure ∅
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Ioo_eq_empty`：Ioo_eq_empty (h : ¬a < b) : Ioo a b = ∅
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance tendsto_Ioo_pure_bot {a : α} : TendstoIxxClass Ioo (pure a) ⊥ :=
  ⟨by simp⟩

end PartialOrder

section LinearOrder

open Interval

variable [LinearOrder α]

/-
**Filter.tendsto_Icc_uIcc_uIcc** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：tendsto_Icc_uIcc_uIcc {a b : α} : TendstoIxxClass Icc (𝓟 [[a, b]]) (𝓟 [[a,
 b]])
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance tendsto_Icc_uIcc_uIcc {a b : α} : TendstoIxxClass Icc (𝓟 [[a, b]]) (𝓟 [[a, b]]) :=
  Filter.tendsto_Icc_Icc_Icc
/-
**Filter.tendsto_Ioc_uIcc_uIcc** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：tendsto_Ioc_uIcc_uIcc {a b : α} : TendstoIxxClass Ioc (𝓟 [[a, b]]) (𝓟 [[a,
 b]])
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance tendsto_Ioc_uIcc_uIcc {a b : α} : TendstoIxxClass Ioc (𝓟 [[a, b]]) (𝓟 [[a, b]]) :=
  Filter.tendsto_Ioc_Icc_Icc
/-
**Filter.tendsto_uIcc_of_Icc** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：tendsto_uIcc_of_Icc {l : Filter α} [TendstoIxxClass Icc l l] : TendstoIxxC
lass uIcc l l
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `Filter.mem_prod_self_iff`：mem_prod_self_iff {s} : s in la ×ˢ la ↔ exists
 t in la, t ×ˢ t subseteq s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.Tendsto.Icc`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] 
{l₁ l₂ : Filter α} [Filter.TendstoIxxClass Set.Icc l₁ l₂]   {lb : Filter β} {u₁ 
u₂ : β →…
· 使用定理 `Filter.tendsto_fst`：tendsto_fst : Tendsto Prod.fst (f ×ˢ g) f
· 使用定理 `Filter.tendsto_snd`：tendsto_snd : Tendsto Prod.snd (f ×ˢ g) g
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用引理 `Set.uIcc_of_ge`：uIcc_of_ge (h : b <= a) : [[a, b]] = Icc b a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
instance tendsto_uIcc_of_Icc {l : Filter α} [TendstoIxxClass Icc l l] :
    TendstoIxxClass uIcc l l := by
  refine ⟨fun s hs => mem_map.2 <| mem_prod_self_iff.2 ?_⟩
  obtain ⟨t, htl, hts⟩ : ∃ t ∈ l, ∀ p ∈ (t : Set α) ×ˢ t, Icc (p : α × α).1 p.2 ∈ s :=
    mem_prod_self_iff.1 (mem_map.1 (tendsto_fst.Icc tendsto_snd hs))
  refine ⟨t, htl, fun p hp => ?_⟩
  rcases le_total p.1 p.2 with h | h
  · rw [mem_preimage, uIcc_of_le h]
    exact hts p hp
  · rw [mem_preimage, uIcc_of_ge h]
    exact hts ⟨p.2, p.1⟩ ⟨hp.2, hp.1⟩
/-
**Filter.Tendsto.uIcc** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder α] {l : Filter α} [Fil
ter.TendstoIxxClass Set.Icc l l] {f g : β → α}   {lb : Filter β},   Filter.Tends
to f lb l → Filter.Tendsto g lb l → Filter.Tendsto (fun x => Set.uIcc (f x) (g x
)) lb l.smallSets
参数：fun x => Set.uIcc (f x) (g x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.TendstoIxxClass.tendsto_Ixx`：∀ {α : Type u_1} {Ixx : α → α → Set 
α} {l₁ : Filter α} {l₂ : outParam (Filter α)}   [self : Filter.TendstoIxxClass I
xx l₁ l₂], Filter.Tendst…
· 使用定理 `Filter.Tendsto.prodMk`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f
 : Filter α} {g : Filter β} {h : Filter γ} {m₁ : α → β} {m₂ : α → γ},   Filter.T
endsto m₁ f…
-/
protected theorem Tendsto.uIcc {l : Filter α} [TendstoIxxClass Icc l l] {f g : β → α}
    {lb : Filter β} (hf : Tendsto f lb l) (hg : Tendsto g lb l) :
    Tendsto (fun x => [[f x, g x]]) lb l.smallSets :=
  (@TendstoIxxClass.tendsto_Ixx α Set.uIcc _ _ _).comp <| hf.prodMk hg

end LinearOrder

end Filter

