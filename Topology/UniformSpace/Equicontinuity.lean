/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

/-!
# Equicontinuity of a family of functions

Let `X` be a topological space and `α` a `UniformSpace`. A family of functions `F : ι → X → α`
is said to be *equicontinuous at a point `x₀ : X`* when, for any entourage `U` in `α`, there is a
neighborhood `V` of `x₀` such that, for all `x ∈ V`, and *for all `i`*, `F i x` is `U`-close to
`F i x₀`. In other words, one has `∀ U ∈ 𝓤 α, ∀ᶠ x in 𝓝 x₀, ∀ i, (F i x₀, F i x) ∈ U`.
For maps between metric spaces, this corresponds to
`∀ ε > 0, ∃ δ > 0, ∀ x, ∀ i, dist x₀ x < δ → dist (F i x₀) (F i x) < ε`.

`F` is said to be *equicontinuous* if it is equicontinuous at each point.

A closely related concept is that of ***uniform*** *equicontinuity* of a family of functions
`F : ι → β → α` between uniform spaces, which means that, for any entourage `U` in `α`, there is an
entourage `V` in `β` such that, if `x` and `y` are `V`-close, then *for all `i`*, `F i x` and
`F i y` are `U`-close. In other words, one has
`∀ U ∈ 𝓤 α, ∀ᶠ xy in 𝓤 β, ∀ i, (F i xy.1, F i xy.2) ∈ U`.
For maps between metric spaces, this corresponds to
`∀ ε > 0, ∃ δ > 0, ∀ x y, ∀ i, dist x y < δ → dist (F i x₀) (F i x) < ε`.

## Main definitions

* `EquicontinuousAt`: equicontinuity of a family of functions at a point
* `Equicontinuous`: equicontinuity of a family of functions on the whole domain
* `UniformEquicontinuous`: uniform equicontinuity of a family of functions on the whole domain

We also introduce relative versions, namely `EquicontinuousWithinAt`, `EquicontinuousOn` and
`UniformEquicontinuousOn`, akin to `ContinuousWithinAt`, `ContinuousOn` and `UniformContinuousOn`
respectively.

## Main statements

* `equicontinuous_iff_continuous`: equicontinuity can be expressed as a simple continuity
  condition between well-chosen function spaces. This is really useful for building up the theory.
* `Equicontinuous.closure`: if a set of functions is equicontinuous, its closure
  *for the topology of pointwise convergence* is also equicontinuous.

## Notation

Throughout this file, we use :
- `ι`, `κ` for indexing types
- `X`, `Y`, `Z` for topological spaces
- `α`, `β`, `γ` for uniform spaces

## Implementation details

We choose to express equicontinuity as a properties of indexed families of functions rather
than sets of functions for the following reasons:
- it is really easy to express equicontinuity of `H : Set (X → α)` using our setup: it is just
  equicontinuity of the family `(↑) : ↥H → (X → α)`. On the other hand, going the other way around
  would require working with the range of the family, which is always annoying because it
  introduces useless existentials.
- in most applications, one doesn't work with bare functions but with a more specific hom type
  `hom`. Equicontinuity of a set `H : Set hom` would then have to be expressed as equicontinuity
  of `coe_fn '' H`, which is super annoying to work with. This is much simpler with families,
  because equicontinuity of a family `𝓕 : ι → hom` would simply be expressed as equicontinuity
  of `coe_fn ∘ 𝓕`, which doesn't introduce any nasty existentials.

To simplify statements, we do provide abbreviations `Set.EquicontinuousAt`, `Set.Equicontinuous`
and `Set.UniformEquicontinuous` asserting the corresponding fact about the family
`(↑) : ↥H → (X → α)` where `H : Set (X → α)`. Note however that these won't work for sets of hom
types, and in that case one should go back to the family definition rather than using `Set.image`.

## References

* [N. Bourbaki, *General Topology, Chapter X*][bourbaki1966]

## Tags

equicontinuity, uniform convergence, ascoli
-/

@[expose] public section


section

open UniformSpace Filter Set Uniformity Topology UniformConvergence Function

variable {ι κ X X' Y α α' β β' γ : Type*} [tX : TopologicalSpace X] [tY : TopologicalSpace Y]
  [uα : UniformSpace α] [uβ : UniformSpace β] [uγ : UniformSpace γ]

/-- A family `F : ι → X → α` of functions from a topological space to a uniform space is
*equicontinuous at `x₀ : X`* if, for all entourages `U ∈ 𝓤 α`, there is a neighborhood `V` of `x₀`
such that, for all `x ∈ V` and for all `i : ι`, `F i x` is `U`-close to `F i x₀`. -/
/-
**EquicontinuousAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：EquicontinuousAt (F : ι -> X -> α) (x₀ : X) : Prop
参数：F : ι -> X -> α；x₀ : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family `F : ι → X → α` of functions from a topological space to a uniform spac
e is
*equicontinuous at `x₀ : X`* if, for all entourages `U ∈ 𝓤 α`, there is a neighb
orhood `V` of `x₀`
such that, for all `x ∈ V` and for all `i : ι`, `F i x` is `U`-close to `F i x₀`
.
-/
def EquicontinuousAt (F : ι → X → α) (x₀ : X) : Prop :=
  ∀ U ∈ 𝓤 α, ∀ᶠ x in 𝓝 x₀, ∀ i, (F i x₀, F i x) ∈ U

/-- We say that a set `H : Set (X → α)` of functions is equicontinuous at a point if the family
`(↑) : ↥H → (X → α)` is equicontinuous at that point. -/
/-
**Set.EquicontinuousAt** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：{X : Type u_3} → {α : Type u_6} → [tX : TopologicalSpace X] → [uα : Unifor
mSpace α] → Set (X → α) → X → Prop
参数：X → α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a set `H : Set (X → α)` of functions is equicontinuous at a point if
 the family
`(↑) : ↥H → (X → α)` is equicontinuous at that point.
-/
protected abbrev Set.EquicontinuousAt (H : Set <| X → α) (x₀ : X) : Prop :=
  EquicontinuousAt ((↑) : H → X → α) x₀

/-- A family `F : ι → X → α` of functions from a topological space to a uniform space is
*equicontinuous at `x₀ : X` within `S : Set X`* if, for all entourages `U ∈ 𝓤 α`, there is a
neighborhood `V` of `x₀` within `S` such that, for all `x ∈ V` and for all `i : ι`, `F i x` is
`U`-close to `F i x₀`. -/
/-
**EquicontinuousWithinAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：EquicontinuousWithinAt (F : ι -> X -> α) (S : Set X) (x₀ : X) : Prop
参数：F : ι -> X -> α；S : Set X；x₀ : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family `F : ι → X → α` of functions from a topological space to a uniform spac
e is
*equicontinuous at `x₀ : X` within `S : Set X`* if, for all entourages `U ∈ 𝓤 α`
, there is a
neighborhood `V` of `x₀` within `S` such that, for all `x ∈ V` and for all `i : 
ι`, `F i x` is
`U`-close to `F i x₀`.
-/
def EquicontinuousWithinAt (F : ι → X → α) (S : Set X) (x₀ : X) : Prop :=
  ∀ U ∈ 𝓤 α, ∀ᶠ x in 𝓝[S] x₀, ∀ i, (F i x₀, F i x) ∈ U

/-- We say that a set `H : Set (X → α)` of functions is equicontinuous at a point within a subset
if the family `(↑) : ↥H → (X → α)` is equicontinuous at that point within that same subset. -/
/-
**Set.EquicontinuousWithinAt** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：{X : Type u_3} → {α : Type u_6} → [tX : TopologicalSpace X] → [uα : Unifor
mSpace α] → Set (X → α) → Set X → X → Prop
参数：X → α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a set `H : Set (X → α)` of functions is equicontinuous at a point wi
thin a subset
if the family `(↑) : ↥H → (X → α)` is equicontinuous at that point within that s
ame subset.
-/
protected abbrev Set.EquicontinuousWithinAt (H : Set <| X → α) (S : Set X) (x₀ : X) : Prop :=
  EquicontinuousWithinAt ((↑) : H → X → α) S x₀

/-- A family `F : ι → X → α` of functions from a topological space to a uniform space is
*equicontinuous* on all of `X` if it is equicontinuous at each point of `X`. -/
/-
**Equicontinuous** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Equicontinuous (F : ι -> X -> α) : Prop
参数：F : ι -> X -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family `F : ι → X → α` of functions from a topological space to a uniform spac
e is
*equicontinuous* on all of `X` if it is equicontinuous at each point of `X`.
-/
def Equicontinuous (F : ι → X → α) : Prop :=
  ∀ x₀, EquicontinuousAt F x₀

/-- We say that a set `H : Set (X → α)` of functions is equicontinuous if the family
`(↑) : ↥H → (X → α)` is equicontinuous. -/
/-
**Set.Equicontinuous** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：{X : Type u_3} → {α : Type u_6} → [tX : TopologicalSpace X] → [uα : Unifor
mSpace α] → Set (X → α) → Prop
参数：X → α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a set `H : Set (X → α)` of functions is equicontinuous if the family
`(↑) : ↥H → (X → α)` is equicontinuous.
-/
protected abbrev Set.Equicontinuous (H : Set <| X → α) : Prop :=
  Equicontinuous ((↑) : H → X → α)

/-- A family `F : ι → X → α` of functions from a topological space to a uniform space is
*equicontinuous on `S : Set X`* if it is equicontinuous *within `S`* at each point of `S`. -/
/-
**EquicontinuousOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：EquicontinuousOn (F : ι -> X -> α) (S : Set X) : Prop
参数：F : ι -> X -> α；S : Set X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family `F : ι → X → α` of functions from a topological space to a uniform spac
e is
*equicontinuous on `S : Set X`* if it is equicontinuous *within `S`* at each poi
nt of `S`.
-/
def EquicontinuousOn (F : ι → X → α) (S : Set X) : Prop :=
  ∀ x₀ ∈ S, EquicontinuousWithinAt F S x₀

/-- We say that a set `H : Set (X → α)` of functions is equicontinuous on a subset if the family
`(↑) : ↥H → (X → α)` is equicontinuous on that subset. -/
/-
**Set.EquicontinuousOn** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：{X : Type u_3} → {α : Type u_6} → [tX : TopologicalSpace X] → [uα : Unifor
mSpace α] → Set (X → α) → Set X → Prop
参数：X → α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a set `H : Set (X → α)` of functions is equicontinuous on a subset i
f the family
`(↑) : ↥H → (X → α)` is equicontinuous on that subset.
-/
protected abbrev Set.EquicontinuousOn (H : Set <| X → α) (S : Set X) : Prop :=
  EquicontinuousOn ((↑) : H → X → α) S

/-- A family `F : ι → β → α` of functions between uniform spaces is *uniformly equicontinuous* if,
for all entourages `U ∈ 𝓤 α`, there is an entourage `V ∈ 𝓤 β` such that, whenever `x` and `y` are
`V`-close, we have that, *for all `i : ι`*, `F i x` is `U`-close to `F i y`. -/
/-
**UniformEquicontinuous** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：UniformEquicontinuous (F : ι -> β -> α) : Prop
参数：F : ι -> β -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family `F : ι → β → α` of functions between uniform spaces is *uniformly equic
ontinuous* if,
for all entourages `U ∈ 𝓤 α`, there is an entourage `V ∈ 𝓤 β` such that, wheneve
r `x` and `y` are
`V`-close, we have that, *for all `i : ι`*, `F i x` is `U`-close to `F i y`.
-/
def UniformEquicontinuous (F : ι → β → α) : Prop :=
  ∀ U ∈ 𝓤 α, ∀ᶠ xy : β × β in 𝓤 β, ∀ i, (F i xy.1, F i xy.2) ∈ U

/-- We say that a set `H : Set (X → α)` of functions is uniformly equicontinuous if the family
`(↑) : ↥H → (X → α)` is uniformly equicontinuous. -/
/-
**Set.UniformEquicontinuous** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：{α : Type u_6} → {β : Type u_8} → [uα : UniformSpace α] → [uβ : UniformSpa
ce β] → Set (β → α) → Prop
参数：β → α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a set `H : Set (X → α)` of functions is uniformly equicontinuous if 
the family
`(↑) : ↥H → (X → α)` is uniformly equicontinuous.
-/
protected abbrev Set.UniformEquicontinuous (H : Set <| β → α) : Prop :=
  UniformEquicontinuous ((↑) : H → β → α)

/-- A family `F : ι → β → α` of functions between uniform spaces is
*uniformly equicontinuous on `S : Set β`* if, for all entourages `U ∈ 𝓤 α`, there is a relative
entourage `V ∈ 𝓤 β ⊓ 𝓟 (S ×ˢ S)` such that, whenever `x` and `y` are `V`-close, we have that,
*for all `i : ι`*, `F i x` is `U`-close to `F i y`. -/
/-
**UniformEquicontinuousOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：UniformEquicontinuousOn (F : ι -> β -> α) (S : Set β) : Prop
参数：F : ι -> β -> α；S : Set β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family `F : ι → β → α` of functions between uniform spaces is
*uniformly equicontinuous on `S : Set β`* if, for all entourages `U ∈ 𝓤 α`, ther
e is a relative
entourage `V ∈ 𝓤 β ⊓ 𝓟 (S ×ˢ S)` such that, whenever `x` and `y` are `V`-close, 
we have that,
*for all `i : ι`*, `F i x` is `U`-close to `F i y`.
-/
def UniformEquicontinuousOn (F : ι → β → α) (S : Set β) : Prop :=
  ∀ U ∈ 𝓤 α, ∀ᶠ xy : β × β in 𝓤 β ⊓ 𝓟 (S ×ˢ S), ∀ i, (F i xy.1, F i xy.2) ∈ U

/-- We say that a set `H : Set (X → α)` of functions is uniformly equicontinuous on a subset if the
family `(↑) : ↥H → (X → α)` is uniformly equicontinuous on that subset. -/
/-
**Set.UniformEquicontinuousOn** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：{α : Type u_6} → {β : Type u_8} → [uα : UniformSpace α] → [uβ : UniformSpa
ce β] → Set (β → α) → Set β → Prop
参数：β → α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a set `H : Set (X → α)` of functions is uniformly equicontinuous on 
a subset if the
family `(↑) : ↥H → (X → α)` is uniformly equicontinuous on that subset.
-/
protected abbrev Set.UniformEquicontinuousOn (H : Set <| β → α) (S : Set β) : Prop :=
  UniformEquicontinuousOn ((↑) : H → β → α) S
/-
**EquicontinuousAt.equicontinuousWithinAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：EquicontinuousAt.equicontinuousWithinAt {F : ι -> X -> α} {x₀ : X} (H : Eq
uicontinuousAt F x₀) (S : Set X) : EquicontinuousWithinAt F S x₀
参数：H : EquicontinuousAt F x₀；S : Set X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
lemma EquicontinuousAt.equicontinuousWithinAt {F : ι → X → α} {x₀ : X} (H : EquicontinuousAt F x₀)
    (S : Set X) : EquicontinuousWithinAt F S x₀ :=
  fun U hU ↦ (H U hU).filter_mono inf_le_left
/-
**EquicontinuousWithinAt.mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：EquicontinuousWithinAt.mono {F : ι -> X -> α} {x₀ : X} {S T : Set X} (H : 
EquicontinuousWithinAt F T x₀) (hST : S subseteq T) : EquicontinuousWithinAt F S
 x₀
参数：H : EquicontinuousWithinAt F T x₀；hST : S subseteq T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
-/
lemma EquicontinuousWithinAt.mono {F : ι → X → α} {x₀ : X} {S T : Set X}
    (H : EquicontinuousWithinAt F T x₀) (hST : S ⊆ T) : EquicontinuousWithinAt F S x₀ :=
  fun U hU ↦ (H U hU).filter_mono <| nhdsWithin_mono x₀ hST
/-
**equicontinuousWithinAt_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {ι : Type u_1} {X : Type u_3} {α : Type u_6} [tX : TopologicalSpace X] [
uα : UniformSpace α] (F : ι → X → α) (x₀ : X),   EquicontinuousWithinAt F Set.un
iv x₀ ↔ EquicontinuousAt F x₀
参数：F : ι → X → α；x₀ : X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EquicontinuousWithinAt.eq_1`：∀ {ι : Type u_1} {X : Type u_3} {α : Type u
_6} [tX : TopologicalSpace X] [uα : UniformSpace α] (F : ι → X → α)   (S : Set X
) (x₀ : X),   Equ…
· 使用定理 `EquicontinuousAt.eq_1`：∀ {ι : Type u_1} {X : Type u_3} {α : Type u_6} [t
X : TopologicalSpace X] [uα : UniformSpace α] (F : ι → X → α) (x₀ : X),   Equico
ntinuousAt …
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma equicontinuousWithinAt_univ (F : ι → X → α) (x₀ : X) :
    EquicontinuousWithinAt F univ x₀ ↔ EquicontinuousAt F x₀ := by
  rw [EquicontinuousWithinAt, EquicontinuousAt, nhdsWithin_univ]
/-
**equicontinuousAt_restrict_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：equicontinuousAt_restrict_iff (F : ι -> X -> α) {S : Set X} (x₀ : S) : Equ
icontinuousAt (S.domRestrict ∘ F) x₀ ↔ EquicontinuousWithinAt F S x₀
参数：F : ι -> X -> α；x₀ : S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma equicontinuousAt_restrict_iff (F : ι → X → α) {S : Set X} (x₀ : S) :
    EquicontinuousAt (S.domRestrict ∘ F) x₀ ↔ EquicontinuousWithinAt F S x₀ := by
  simp [EquicontinuousWithinAt, EquicontinuousAt,
    ← eventually_nhds_subtype_iff]
/-
**Equicontinuous.equicontinuousOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Equicontinuous.equicontinuousOn {F : ι -> X -> α} (H : Equicontinuous F) (
S : Set X) : EquicontinuousOn F S
参数：H : Equicontinuous F；S : Set X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `EquicontinuousAt.equicontinuousWithinAt`：EquicontinuousAt.equicontinuous
WithinAt {F : ι -> X -> α} {x₀ : X} (H : EquicontinuousAt F x₀) (S : Set X) : Eq
uicontinuousWithinAt F S x₀
-/
lemma Equicontinuous.equicontinuousOn {F : ι → X → α} (H : Equicontinuous F)
    (S : Set X) : EquicontinuousOn F S :=
  fun x _ ↦ (H x).equicontinuousWithinAt S
/-
**EquicontinuousOn.mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：EquicontinuousOn.mono {F : ι -> X -> α} {S T : Set X} (H : EquicontinuousO
n F T) (hST : S subseteq T) : EquicontinuousOn F S
参数：H : EquicontinuousOn F T；hST : S subseteq T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `EquicontinuousWithinAt.mono`：EquicontinuousWithinAt.mono {F : ι -> X -> 
α} {x₀ : X} {S T : Set X} (H : EquicontinuousWithinAt F T x₀) (hST : S subseteq 
T) : Equicontinuo…
-/
lemma EquicontinuousOn.mono {F : ι → X → α} {S T : Set X}
    (H : EquicontinuousOn F T) (hST : S ⊆ T) : EquicontinuousOn F S :=
  fun x hx ↦ (H x (hST hx)).mono hST
/-
**equicontinuousOn_univ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：equicontinuousOn_univ (F : ι -> X -> α) : EquicontinuousOn F univ ↔ Equico
ntinuous F
参数：F : ι -> X -> α。
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
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma equicontinuousOn_univ (F : ι → X → α) :
    EquicontinuousOn F univ ↔ Equicontinuous F := by
  simp [EquicontinuousOn, Equicontinuous]
/-
**equicontinuous_restrict_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：equicontinuous_restrict_iff (F : ι -> X -> α) {S : Set X} : Equicontinuous
 (S.domRestrict ∘ F) ↔ EquicontinuousOn F S
参数：F : ι -> X -> α。
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
lemma equicontinuous_restrict_iff (F : ι → X → α) {S : Set X} :
    Equicontinuous (S.domRestrict ∘ F) ↔ EquicontinuousOn F S := by
  simp [Equicontinuous, EquicontinuousOn, equicontinuousAt_restrict_iff]
/-
**UniformEquicontinuous.uniformEquicontinuousOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformEquicontinuous.uniformEquicontinuousOn {F : ι -> β -> α} (H : Unifo
rmEquicontinuous F) (S : Set β) : UniformEquicontinuousOn F S
参数：H : UniformEquicontinuous F；S : Set β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
lemma UniformEquicontinuous.uniformEquicontinuousOn {F : ι → β → α} (H : UniformEquicontinuous F)
    (S : Set β) : UniformEquicontinuousOn F S :=
  fun U hU ↦ (H U hU).filter_mono inf_le_left
/-
**UniformEquicontinuousOn.mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：UniformEquicontinuousOn.mono {F : ι -> β -> α} {S T : Set β} (H : UniformE
quicontinuousOn F T) (hST : S subseteq T) : UniformEquicontinuousOn F S
参数：H : UniformEquicontinuousOn F T；hST : S subseteq T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `inf_le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c d : α}, b ≤ 
a → d ≤ c → b ⊓ d ≤ a ⊓ c
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Filter.principal_mono._gcongr_1`：∀ {α : Type u} {s t : Set α}, s ⊆ t → F
ilter.principal s ≤ Filter.principal t
· 使用定理 `Set.prod_mono`：prod_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : s
₁ ×ˢ t₁ subseteq s₂ ×ˢ t₂
-/
lemma UniformEquicontinuousOn.mono {F : ι → β → α} {S T : Set β}
    (H : UniformEquicontinuousOn F T) (hST : S ⊆ T) : UniformEquicontinuousOn F S :=
  fun U hU ↦ (H U hU).filter_mono <| by gcongr
/-
**uniformEquicontinuousOn_univ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：uniformEquicontinuousOn_univ (F : ι -> β -> α) : UniformEquicontinuousOn F
 univ ↔ UniformEquicontinuous F
参数：F : ι -> β -> α。
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
· 使用定理 `Set.univ_prod_univ`：univ_prod_univ : @univ α ×ˢ @univ β = univ
· 使用定理 `Filter.principal_univ`：∀ {α : Type u}, Filter.principal Set.univ = ⊤
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma uniformEquicontinuousOn_univ (F : ι → β → α) :
    UniformEquicontinuousOn F univ ↔ UniformEquicontinuous F := by
  simp [UniformEquicontinuousOn, UniformEquicontinuous]
/-
**uniformEquicontinuous_restrict_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：uniformEquicontinuous_restrict_iff (F : ι -> β -> α) {S : Set β} : Uniform
Equicontinuous (S.domRestrict ∘ F) ↔ UniformEquicontinuousOn F S
参数：F : ι -> β -> α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformEquicontinuous.eq_1`：∀ {ι : Type u_1} {α : Type u_6} {β : Type u_
8} [uα : UniformSpace α] [uβ : UniformSpace β] (F : ι → β → α),   UniformEquicon
tinuous F = ∀ U …
· 使用定理 `UniformEquicontinuousOn.eq_1`：∀ {ι : Type u_1} {α : Type u_6} {β : Type 
u_8} [uα : UniformSpace α] [uβ : UniformSpace β] (F : ι → β → α) (S : Set β),   
UniformEquicontinu…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.range_val`：range_val {s : Set α} : range (Subtype.val : s -> α) 
= s
· 使用定理 `Set.range_prodMap`：range_prodMap {m₁ : α -> γ} {m₂ : β -> δ} : range (Pr
od.map m₁ m₂) = range m₁ ×ˢ range m₂
· 使用定理 `Filter.map_comap`：map_comap (f : Filter β) (m : α -> β) : (f.comap m).ma
p m = f ⊓ 𝓟 (range m)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma uniformEquicontinuous_restrict_iff (F : ι → β → α) {S : Set β} :
    UniformEquicontinuous (S.domRestrict ∘ F) ↔ UniformEquicontinuousOn F S := by
  rw [UniformEquicontinuous, UniformEquicontinuousOn]
  conv in _ ⊓ _ => rw [← Subtype.range_val (s := S), ← range_prodMap, ← map_comap]
  rfl

/-!
### Empty index type
-/

@[simp]
/-
**equicontinuousAt_empty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：equicontinuousAt_empty [h : IsEmpty ι] (F : ι -> X -> α) (x₀ : X) : Equico
ntinuousAt F x₀
参数：F : ι -> X -> α；x₀ : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x

--- 原说明 ---
### Empty index type
-/
lemma equicontinuousAt_empty [h : IsEmpty ι] (F : ι → X → α) (x₀ : X) :
    EquicontinuousAt F x₀ :=
  fun _ _ ↦ Eventually.of_forall (fun _ ↦ h.elim)

@[simp]
/-
**equicontinuousWithinAt_empty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：equicontinuousWithinAt_empty [h : IsEmpty ι] (F : ι -> X -> α) (S : Set X)
 (x₀ : X) : EquicontinuousWithinAt F S x₀
参数：F : ι -> X -> α；S : Set X；x₀ : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
lemma equicontinuousWithinAt_empty [h : IsEmpty ι] (F : ι → X → α) (S : Set X) (x₀ : X) :
    EquicontinuousWithinAt F S x₀ :=
  fun _ _ ↦ Eventually.of_forall (fun _ ↦ h.elim)

@[simp]
/-
**equicontinuous_empty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：equicontinuous_empty [IsEmpty ι] (F : ι -> X -> α) : Equicontinuous F
参数：F : ι -> X -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `equicontinuousAt_empty`：equicontinuousAt_empty [h : IsEmpty ι] (F : ι ->
 X -> α) (x₀ : X) : EquicontinuousAt F x₀
-/
lemma equicontinuous_empty [IsEmpty ι] (F : ι → X → α) :
    Equicontinuous F :=
  equicontinuousAt_empty F

@[simp]
/-
**equicontinuousOn_empty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：equicontinuousOn_empty [IsEmpty ι] (F : ι -> X -> α) (S : Set X) : Equicon
tinuousOn F S
参数：F : ι -> X -> α；S : Set X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `equicontinuousWithinAt_empty`：equicontinuousWithinAt_empty [h : IsEmpty 
ι] (F : ι -> X -> α) (S : Set X) (x₀ : X) : EquicontinuousWithinAt F S x₀
-/
lemma equicontinuousOn_empty [IsEmpty ι] (F : ι → X → α) (S : Set X) :
    EquicontinuousOn F S :=
  fun x₀ _ ↦ equicontinuousWithinAt_empty F S x₀

@[simp]
/-
**uniformEquicontinuous_empty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：uniformEquicontinuous_empty [h : IsEmpty ι] (F : ι -> β -> α) : UniformEqu
icontinuous F
参数：F : ι -> β -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
lemma uniformEquicontinuous_empty [h : IsEmpty ι] (F : ι → β → α) :
    UniformEquicontinuous F :=
  fun _ _ ↦ Eventually.of_forall (fun _ ↦ h.elim)

@[simp]
/-
**uniformEquicontinuousOn_empty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：uniformEquicontinuousOn_empty [h : IsEmpty ι] (F : ι -> β -> α) (S : Set β
) : UniformEquicontinuousOn F S
参数：F : ι -> β -> α；S : Set β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
lemma uniformEquicontinuousOn_empty [h : IsEmpty ι] (F : ι → β → α) (S : Set β) :
    UniformEquicontinuousOn F S :=
  fun _ _ ↦ Eventually.of_forall (fun _ ↦ h.elim)

/-!
### Finite index type
-/

/-
**equicontinuousAt_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：equicontinuousAt_finite [Finite ι] {F : ι -> X -> α} {x₀ : X} : Equicontin
uousAt F x₀ ↔ forall i, ContinuousAt (F i) x₀
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
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `nhds_basis_uniformity'`：nhds_basis_uniformity' {p : ι -> Prop} {s : ι ->
 SetRel α α} (h : (𝓤 α).HasBasis p s) {x : α} : (𝓝 x).HasBasis p fun i => ball x
 (s i)
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
### Finite index type
-/
theorem equicontinuousAt_finite [Finite ι] {F : ι → X → α} {x₀ : X} :
    EquicontinuousAt F x₀ ↔ ∀ i, ContinuousAt (F i) x₀ := by
  simp [EquicontinuousAt, ContinuousAt, (nhds_basis_uniformity' (𝓤 α).basis_sets).tendsto_right_iff,
    UniformSpace.ball, @forall_comm _ ι]
/-
**equicontinuousWithinAt_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：equicontinuousWithinAt_finite [Finite ι] {F : ι -> X -> α} {S : Set X} {x₀
 : X} : EquicontinuousWithinAt F S x₀ ↔ forall i, ContinuousWithinAt (F i) S x₀
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
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `nhds_basis_uniformity'`：nhds_basis_uniformity' {p : ι -> Prop} {s : ι ->
 SetRel α α} (h : (𝓤 α).HasBasis p s) {x : α} : (𝓝 x).HasBasis p fun i => ball x
 (s i)
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem equicontinuousWithinAt_finite [Finite ι] {F : ι → X → α} {S : Set X} {x₀ : X} :
    EquicontinuousWithinAt F S x₀ ↔ ∀ i, ContinuousWithinAt (F i) S x₀ := by
  simp [EquicontinuousWithinAt, ContinuousWithinAt,
    (nhds_basis_uniformity' (𝓤 α).basis_sets).tendsto_right_iff, UniformSpace.ball,
    @forall_comm _ ι]
/-
**equicontinuous_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：equicontinuous_finite [Finite ι] {F : ι -> X -> α} : Equicontinuous F ↔ fo
rall i, Continuous (F i)
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
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem equicontinuous_finite [Finite ι] {F : ι → X → α} :
    Equicontinuous F ↔ ∀ i, Continuous (F i) := by
  simp only [Equicontinuous, equicontinuousAt_finite, continuous_iff_continuousAt, @forall_comm ι]
/-
**equicontinuousOn_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：equicontinuousOn_finite [Finite ι] {F : ι -> X -> α} {S : Set X} : Equicon
tinuousOn F S ↔ forall i, ContinuousOn (F i) S
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
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem equicontinuousOn_finite [Finite ι] {F : ι → X → α} {S : Set X} :
    EquicontinuousOn F S ↔ ∀ i, ContinuousOn (F i) S := by
  simp only [EquicontinuousOn, equicontinuousWithinAt_finite, ContinuousOn, @forall_comm ι]
/-
**uniformEquicontinuous_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformEquicontinuous_finite [Finite ι] {F : ι -> β -> α} : UniformEquicon
tinuous F ↔ forall i, UniformContinuous (F i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem uniformEquicontinuous_finite [Finite ι] {F : ι → β → α} :
    UniformEquicontinuous F ↔ ∀ i, UniformContinuous (F i) := by
  simp only [UniformEquicontinuous, eventually_all, @forall_comm _ ι]; rfl
/-
**uniformEquicontinuousOn_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformEquicontinuousOn_finite [Finite ι] {F : ι -> β -> α} {S : Set β} : 
UniformEquicontinuousOn F S ↔ forall i, UniformContinuousOn (F i) S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem uniformEquicontinuousOn_finite [Finite ι] {F : ι → β → α} {S : Set β} :
    UniformEquicontinuousOn F S ↔ ∀ i, UniformContinuousOn (F i) S := by
  simp only [UniformEquicontinuousOn, eventually_all, @forall_comm _ ι]; rfl

/-!
### Index type with a unique element
-/

/-
**equicontinuousAt_unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：equicontinuousAt_unique [Unique ι] {F : ι -> X -> α} {x : X} : Equicontinu
ousAt F x ↔ ContinuousAt (F default) x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `equicontinuousAt_finite`：equicontinuousAt_finite [Finite ι] {F : ι -> X 
-> α} {x₀ : X} : EquicontinuousAt F x₀ ↔ forall i, ContinuousAt (F i) x₀
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Unique.forall_iff`：forall_iff {p : α -> Prop} : (forall a, p a) ↔ p defa
ult

--- 原说明 ---
### Index type with a unique element
-/
theorem equicontinuousAt_unique [Unique ι] {F : ι → X → α} {x : X} :
    EquicontinuousAt F x ↔ ContinuousAt (F default) x :=
  equicontinuousAt_finite.trans Unique.forall_iff
/-
**equicontinuousWithinAt_unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：equicontinuousWithinAt_unique [Unique ι] {F : ι -> X -> α} {S : Set X} {x 
: X} : EquicontinuousWithinAt F S x ↔ ContinuousWithinAt (F default) S x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `equicontinuousWithinAt_finite`：equicontinuousWithinAt_finite [Finite ι] 
{F : ι -> X -> α} {S : Set X} {x₀ : X} : EquicontinuousWithinAt F S x₀ ↔ forall 
i, ContinuousWithin…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Unique.forall_iff`：forall_iff {p : α -> Prop} : (forall a, p a) ↔ p defa
ult
-/
theorem equicontinuousWithinAt_unique [Unique ι] {F : ι → X → α} {S : Set X} {x : X} :
    EquicontinuousWithinAt F S x ↔ ContinuousWithinAt (F default) S x :=
  equicontinuousWithinAt_finite.trans Unique.forall_iff
/-
**equicontinuous_unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：equicontinuous_unique [Unique ι] {F : ι -> X -> α} : Equicontinuous F ↔ Co
ntinuous (F default)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `equicontinuous_finite`：equicontinuous_finite [Finite ι] {F : ι -> X -> α
} : Equicontinuous F ↔ forall i, Continuous (F i)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Unique.forall_iff`：forall_iff {p : α -> Prop} : (forall a, p a) ↔ p defa
ult
-/
theorem equicontinuous_unique [Unique ι] {F : ι → X → α} :
    Equicontinuous F ↔ Continuous (F default) :=
  equicontinuous_finite.trans Unique.forall_iff
/-
**equicontinuousOn_unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：equicontinuousOn_unique [Unique ι] {F : ι -> X -> α} {S : Set X} : Equicon
tinuousOn F S ↔ ContinuousOn (F default) S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `equicontinuousOn_finite`：equicontinuousOn_finite [Finite ι] {F : ι -> X 
-> α} {S : Set X} : EquicontinuousOn F S ↔ forall i, ContinuousOn (F i) S
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Unique.forall_iff`：forall_iff {p : α -> Prop} : (forall a, p a) ↔ p defa
ult
-/
theorem equicontinuousOn_unique [Unique ι] {F : ι → X → α} {S : Set X} :
    EquicontinuousOn F S ↔ ContinuousOn (F default) S :=
  equicontinuousOn_finite.trans Unique.forall_iff
/-
**uniformEquicontinuous_unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformEquicontinuous_unique [Unique ι] {F : ι -> β -> α} : UniformEquicon
tinuous F ↔ UniformContinuous (F default)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `uniformEquicontinuous_finite`：uniformEquicontinuous_finite [Finite ι] {F
 : ι -> β -> α} : UniformEquicontinuous F ↔ forall i, UniformContinuous (F i)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Unique.forall_iff`：forall_iff {p : α -> Prop} : (forall a, p a) ↔ p defa
ult
-/
theorem uniformEquicontinuous_unique [Unique ι] {F : ι → β → α} :
    UniformEquicontinuous F ↔ UniformContinuous (F default) :=
  uniformEquicontinuous_finite.trans Unique.forall_iff
/-
**uniformEquicontinuousOn_unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformEquicontinuousOn_unique [Unique ι] {F : ι -> β -> α} {S : Set β} : 
UniformEquicontinuousOn F S ↔ UniformContinuousOn (F default) S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `uniformEquicontinuousOn_finite`：uniformEquicontinuousOn_finite [Finite ι
] {F : ι -> β -> α} {S : Set β} : UniformEquicontinuousOn F S ↔ forall i, Unifor
mContinuousOn (F i) …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Unique.forall_iff`：forall_iff {p : α -> Prop} : (forall a, p a) ↔ p defa
ult
-/
theorem uniformEquicontinuousOn_unique [Unique ι] {F : ι → β → α} {S : Set β} :
    UniformEquicontinuousOn F S ↔ UniformContinuousOn (F default) S :=
  uniformEquicontinuousOn_finite.trans Unique.forall_iff

/-- Reformulation of equicontinuity at `x₀` within a set `S`, comparing two variables near `x₀`
instead of comparing only one with `x₀`. -/
/-
**equicontinuousWithinAt_iff_pair** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：equicontinuousWithinAt_iff_pair {F : ι -> X -> α} {S : Set X} {x₀ : X} (hx
₀ : x₀ in S) : EquicontinuousWithinAt F S x₀ ↔ forall U in 𝓤 α, exists V in 𝓝[S]
 x₀, forall x in V, forall y in V, forall i, (F i x, F i y) in U
参数：hx₀ : x₀ in S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `comp_symm_mem_uniformity_sets`：comp_symm_mem_uniformity_sets {s : SetRel
 α α} (hs : s in 𝓤 α) : exists t in 𝓤 α, SetRel.IsSymm t ∧ t ○ t subseteq s
· 使用引理 `SetRel.prodMk_mem_comp`：prodMk_mem_comp (hab : a ~[R] b) (hbc : b ~[S] c
) : a ~[R ○ S] c
· 使用定理 `SetRel.symm`：∀ {α : Type u_1} (R : SetRel α α) {a b : α} [R.IsSymm], (a,
 b) ∈ R → (b, a) ∈ R
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `mem_of_mem_nhdsWithin`：mem_of_mem_nhdsWithin {a : α} {s t : Set α} (ha :
 a in s) (ht : t in 𝓝[s] a) : a in t

--- 原说明 ---
Reformulation of equicontinuity at `x₀` within a set `S`, comparing two variable
s near `x₀`
instead of comparing only one with `x₀`.
-/
theorem equicontinuousWithinAt_iff_pair {F : ι → X → α} {S : Set X} {x₀ : X} (hx₀ : x₀ ∈ S) :
    EquicontinuousWithinAt F S x₀ ↔
      ∀ U ∈ 𝓤 α, ∃ V ∈ 𝓝[S] x₀, ∀ x ∈ V, ∀ y ∈ V, ∀ i, (F i x, F i y) ∈ U := by
  constructor <;> intro H U hU
  · rcases comp_symm_mem_uniformity_sets hU with ⟨V, hV, hVsymm, hVU⟩
    refine ⟨_, H V hV, fun x hx y hy i => hVU (SetRel.prodMk_mem_comp ?_ (hy i))⟩
    exact SetRel.symm V (hx i)
  · rcases H U hU with ⟨V, hV, hVU⟩
    filter_upwards [hV] using fun x hx i => hVU x₀ (mem_of_mem_nhdsWithin hx₀ hV) x hx i

/-- Reformulation of equicontinuity at `x₀` comparing two variables near `x₀` instead of comparing
only one with `x₀`. -/
/-
**equicontinuousAt_iff_pair** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：equicontinuousAt_iff_pair {F : ι -> X -> α} {x₀ : X} : EquicontinuousAt F 
x₀ ↔ forall U in 𝓤 α, exists V in 𝓝 x₀, forall x in V, forall y in V, forall i, 
(F i x, F i y) in U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `equicontinuousWithinAt_iff_pair`：equicontinuousWithinAt_iff_pair {F : ι 
-> X -> α} {S : Set X} {x₀ : X} (hx₀ : x₀ in S) : EquicontinuousWithinAt F S x₀ 
↔ forall U in 𝓤 α, ex…
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Reformulation of equicontinuity at `x₀` comparing two variables near `x₀` instea
d of comparing
only one with `x₀`.
-/
theorem equicontinuousAt_iff_pair {F : ι → X → α} {x₀ : X} :
    EquicontinuousAt F x₀ ↔
      ∀ U ∈ 𝓤 α, ∃ V ∈ 𝓝 x₀, ∀ x ∈ V, ∀ y ∈ V, ∀ i, (F i x, F i y) ∈ U := by
  simp_rw [← equicontinuousWithinAt_univ, equicontinuousWithinAt_iff_pair (mem_univ x₀),
    nhdsWithin_univ]

/-- Uniform equicontinuity implies equicontinuity. -/
/-
**UniformEquicontinuous.equicontinuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformEquicontinuous.equicontinuous {F : ι -> β -> α} (h : UniformEquicon
tinuous F) : Equicontinuous F
参数：h : UniformEquicontinuous F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `UniformSpace.ball_mem_nhds`：UniformSpace.ball_mem_nhds (x : α) ⦃V : SetR
el α α⦄ (V_in : V in 𝓤 α) : ball x V in 𝓝 x

--- 原说明 ---
Uniform equicontinuity implies equicontinuity.
-/
theorem UniformEquicontinuous.equicontinuous {F : ι → β → α} (h : UniformEquicontinuous F) :
    Equicontinuous F := fun x₀ U hU ↦
  mem_of_superset (ball_mem_nhds x₀ (h U hU)) fun _ hx i ↦ hx i

/-- Uniform equicontinuity on a subset implies equicontinuity on that subset. -/
/-
**UniformEquicontinuousOn.equicontinuousOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformEquicontinuousOn.equicontinuousOn {F : ι -> β -> α} {S : Set β} (h 
: UniformEquicontinuousOn F S) : EquicontinuousOn F S
参数：h : UniformEquicontinuousOn F S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `UniformSpace.ball_mem_nhdsWithin`：UniformSpace.ball_mem_nhdsWithin {x : 
α} {S : Set α} ⦃V : SetRel α α⦄ (x_in : x in S) (V_in : V in 𝓤 α ⊓ 𝓟 (S ×ˢ S)) :
 ball x V in 𝓝[S] x

--- 原说明 ---
Uniform equicontinuity on a subset implies equicontinuity on that subset.
-/
theorem UniformEquicontinuousOn.equicontinuousOn {F : ι → β → α} {S : Set β}
    (h : UniformEquicontinuousOn F S) :
    EquicontinuousOn F S := fun _ hx₀ U hU ↦
  mem_of_superset (ball_mem_nhdsWithin hx₀ (h U hU)) fun _ hx i ↦ hx i

/-- Each function of a family equicontinuous at `x₀` is continuous at `x₀`. -/
/-
**EquicontinuousAt.continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EquicontinuousAt.continuousAt {F : ι -> X -> α} {x₀ : X} (h : Equicontinuo
usAt F x₀) (i : ι) : ContinuousAt (F i) x₀
参数：h : EquicontinuousAt F x₀；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `UniformSpace.hasBasis_nhds`：UniformSpace.hasBasis_nhds (x : α) : HasBasi
s (𝓝 x) (fun s : SetRel α α => s in 𝓤 α ∧ SetRel.IsSymm s) fun s => ball x s
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x

--- 原说明 ---
Each function of a family equicontinuous at `x₀` is continuous at `x₀`.
-/
theorem EquicontinuousAt.continuousAt {F : ι → X → α} {x₀ : X} (h : EquicontinuousAt F x₀) (i : ι) :
    ContinuousAt (F i) x₀ :=
  (UniformSpace.hasBasis_nhds _).tendsto_right_iff.2 fun U ⟨hU, _⟩ ↦ (h U hU).mono fun _x hx ↦ hx i

/-- Each function of a family equicontinuous at `x₀` within `S` is continuous at `x₀` within `S`. -/
/-
**EquicontinuousWithinAt.continuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EquicontinuousWithinAt.continuousWithinAt {F : ι -> X -> α} {S : Set X} {x
₀ : X} (h : EquicontinuousWithinAt F S x₀) (i : ι) : ContinuousWithinAt (F i) S 
x₀
参数：h : EquicontinuousWithinAt F S x₀；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `UniformSpace.hasBasis_nhds`：UniformSpace.hasBasis_nhds (x : α) : HasBasi
s (𝓝 x) (fun s : SetRel α α => s in 𝓤 α ∧ SetRel.IsSymm s) fun s => ball x s
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x

--- 原说明 ---
Each function of a family equicontinuous at `x₀` within `S` is continuous at `x₀
` within `S`.
-/
theorem EquicontinuousWithinAt.continuousWithinAt {F : ι → X → α} {S : Set X} {x₀ : X}
    (h : EquicontinuousWithinAt F S x₀) (i : ι) :
    ContinuousWithinAt (F i) S x₀ :=
  (UniformSpace.hasBasis_nhds _).tendsto_right_iff.2 fun U ⟨hU, _⟩ ↦ (h U hU).mono fun _x hx ↦ hx i
/-
**Set.EquicontinuousAt.continuousAt_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set.Equico
ntinuousAt`。
形式化陈述：∀ {X : Type u_3} {α : Type u_6} [tX : TopologicalSpace X] [uα : UniformSpa
ce α] {H : Set (X → α)} {x₀ : X},   H.EquicontinuousAt x₀ → ∀ {f : X → α}, f ∈ H
 → ContinuousAt f x₀
参数：X → α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquicontinuousAt.continuousAt`：EquicontinuousAt.continuousAt {F : ι -> X
 -> α} {x₀ : X} (h : EquicontinuousAt F x₀) (i : ι) : ContinuousAt (F i) x₀
-/
protected theorem Set.EquicontinuousAt.continuousAt_of_mem {H : Set <| X → α} {x₀ : X}
    (h : H.EquicontinuousAt x₀) {f : X → α} (hf : f ∈ H) : ContinuousAt f x₀ :=
  h.continuousAt ⟨f, hf⟩
/-
**Set.EquicontinuousWithinAt.continuousWithinAt_of_mem** 是 Mathlib 中的一个定理，位于命名空间
 `Set.EquicontinuousWithinAt`。
形式化陈述：∀ {X : Type u_3} {α : Type u_6} [tX : TopologicalSpace X] [uα : UniformSpa
ce α] {H : Set (X → α)} {S : Set X} {x₀ : X},   H.EquicontinuousWithinAt S x₀ → 
∀ {f : X → α}, f ∈ H → ContinuousWithinAt f S x₀
参数：X → α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquicontinuousWithinAt.continuousWithinAt`：EquicontinuousWithinAt.contin
uousWithinAt {F : ι -> X -> α} {S : Set X} {x₀ : X} (h : EquicontinuousWithinAt 
F S x₀) (i : ι) : ContinuousWit…
-/
protected theorem Set.EquicontinuousWithinAt.continuousWithinAt_of_mem {H : Set <| X → α}
    {S : Set X} {x₀ : X} (h : H.EquicontinuousWithinAt S x₀) {f : X → α} (hf : f ∈ H) :
    ContinuousWithinAt f S x₀ :=
  h.continuousWithinAt ⟨f, hf⟩

/-- Each function of an equicontinuous family is continuous. -/
/-
**Equicontinuous.continuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equicontinuous.continuous {F : ι -> X -> α} (h : Equicontinuous F) (i : ι)
 : Continuous (F i)
参数：h : Equicontinuous F；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `EquicontinuousAt.continuousAt`：EquicontinuousAt.continuousAt {F : ι -> X
 -> α} {x₀ : X} (h : EquicontinuousAt F x₀) (i : ι) : ContinuousAt (F i) x₀

--- 原说明 ---
Each function of an equicontinuous family is continuous.
-/
theorem Equicontinuous.continuous {F : ι → X → α} (h : Equicontinuous F) (i : ι) :
    Continuous (F i) :=
  continuous_iff_continuousAt.mpr fun x => (h x).continuousAt i

/-- Each function of a family equicontinuous on `S` is continuous on `S`. -/
/-
**EquicontinuousOn.continuousOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EquicontinuousOn.continuousOn {F : ι -> X -> α} {S : Set X} (h : Equiconti
nuousOn F S) (i : ι) : ContinuousOn (F i) S
参数：h : EquicontinuousOn F S；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquicontinuousWithinAt.continuousWithinAt`：EquicontinuousWithinAt.contin
uousWithinAt {F : ι -> X -> α} {S : Set X} {x₀ : X} (h : EquicontinuousWithinAt 
F S x₀) (i : ι) : ContinuousWit…

--- 原说明 ---
Each function of a family equicontinuous on `S` is continuous on `S`.
-/
theorem EquicontinuousOn.continuousOn {F : ι → X → α} {S : Set X} (h : EquicontinuousOn F S)
    (i : ι) : ContinuousOn (F i) S :=
  fun x hx ↦ (h x hx).continuousWithinAt i
/-
**Set.Equicontinuous.continuous_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set.Equicontin
uous`。
形式化陈述：∀ {X : Type u_3} {α : Type u_6} [tX : TopologicalSpace X] [uα : UniformSpa
ce α] {H : Set (X → α)},   H.Equicontinuous → ∀ {f : X → α}, f ∈ H → Continuous 
f
参数：X → α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equicontinuous.continuous`：Equicontinuous.continuous {F : ι -> X -> α} (
h : Equicontinuous F) (i : ι) : Continuous (F i)
-/
protected theorem Set.Equicontinuous.continuous_of_mem {H : Set <| X → α} (h : H.Equicontinuous)
    {f : X → α} (hf : f ∈ H) : Continuous f :=
  h.continuous ⟨f, hf⟩
/-
**Set.EquicontinuousOn.continuousOn_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set.Equico
ntinuousOn`。
形式化陈述：∀ {X : Type u_3} {α : Type u_6} [tX : TopologicalSpace X] [uα : UniformSpa
ce α] {H : Set (X → α)} {S : Set X},   H.EquicontinuousOn S → ∀ {f : X → α}, f ∈
 H → ContinuousOn f S
参数：X → α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquicontinuousOn.continuousOn`：EquicontinuousOn.continuousOn {F : ι -> X
 -> α} {S : Set X} (h : EquicontinuousOn F S) (i : ι) : ContinuousOn (F i) S
-/
protected theorem Set.EquicontinuousOn.continuousOn_of_mem {H : Set <| X → α} {S : Set X}
    (h : H.EquicontinuousOn S) {f : X → α} (hf : f ∈ H) : ContinuousOn f S :=
  h.continuousOn ⟨f, hf⟩

/-- Each function of a uniformly equicontinuous family is uniformly continuous. -/
/-
**UniformEquicontinuous.uniformContinuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformEquicontinuous.uniformContinuous {F : ι -> β -> α} (h : UniformEqui
continuous F) (i : ι) : UniformContinuous (F i)
参数：h : UniformEquicontinuous F；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f

--- 原说明 ---
Each function of a uniformly equicontinuous family is uniformly continuous.
-/
theorem UniformEquicontinuous.uniformContinuous {F : ι → β → α} (h : UniformEquicontinuous F)
    (i : ι) : UniformContinuous (F i) := fun U hU =>
  mem_map.mpr (mem_of_superset (h U hU) fun _ hxy => hxy i)

/-- Each function of a family uniformly equicontinuous on `S` is uniformly continuous on `S`. -/
/-
**UniformEquicontinuousOn.uniformContinuousOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformEquicontinuousOn.uniformContinuousOn {F : ι -> β -> α} {S : Set β} 
(h : UniformEquicontinuousOn F S) (i : ι) : UniformContinuousOn (F i) S
参数：h : UniformEquicontinuousOn F S；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f

--- 原说明 ---
Each function of a family uniformly equicontinuous on `S` is uniformly continuou
s on `S`.
-/
theorem UniformEquicontinuousOn.uniformContinuousOn {F : ι → β → α} {S : Set β}
    (h : UniformEquicontinuousOn F S) (i : ι) :
    UniformContinuousOn (F i) S := fun U hU =>
  mem_map.mpr (mem_of_superset (h U hU) fun _ hxy => hxy i)
/-
**Set.UniformEquicontinuous.uniformContinuous_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `
Set.UniformEquicontinuous`。
形式化陈述：∀ {α : Type u_6} {β : Type u_8} [uα : UniformSpace α] [uβ : UniformSpace β
] {H : Set (β → α)},   H.UniformEquicontinuous → ∀ {f : β → α}, f ∈ H → UniformC
ontinuous f
参数：β → α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformEquicontinuous.uniformContinuous`：UniformEquicontinuous.uniformCo
ntinuous {F : ι -> β -> α} (h : UniformEquicontinuous F) (i : ι) : UniformContin
uous (F i)
-/
protected theorem Set.UniformEquicontinuous.uniformContinuous_of_mem {H : Set <| β → α}
    (h : H.UniformEquicontinuous) {f : β → α} (hf : f ∈ H) : UniformContinuous f :=
  h.uniformContinuous ⟨f, hf⟩
/-
**Set.UniformEquicontinuousOn.uniformContinuousOn_of_mem** 是 Mathlib 中的一个定理，位于命名
空间 `Set.UniformEquicontinuousOn`。
形式化陈述：∀ {α : Type u_6} {β : Type u_8} [uα : UniformSpace α] [uβ : UniformSpace β
] {H : Set (β → α)} {S : Set β},   H.UniformEquicontinuousOn S → ∀ {f : β → α}, 
f ∈ H → UniformContinuousOn f S
参数：β → α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformEquicontinuousOn.uniformContinuousOn`：UniformEquicontinuousOn.uni
formContinuousOn {F : ι -> β -> α} {S : Set β} (h : UniformEquicontinuousOn F S)
 (i : ι) : UniformContinuousOn (F…
-/
protected theorem Set.UniformEquicontinuousOn.uniformContinuousOn_of_mem {H : Set <| β → α}
    {S : Set β} (h : H.UniformEquicontinuousOn S) {f : β → α} (hf : f ∈ H) :
    UniformContinuousOn f S :=
  h.uniformContinuousOn ⟨f, hf⟩

/-- Taking sub-families preserves equicontinuity at a point. -/
/-
**EquicontinuousAt.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EquicontinuousAt.comp {F : ι -> X -> α} {x₀ : X} (h : EquicontinuousAt F x
₀) (u : κ -> ι) : EquicontinuousAt (F ∘ u) x₀
参数：h : EquicontinuousAt F x₀；u : κ -> ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x

--- 原说明 ---
Taking sub-families preserves equicontinuity at a point.
-/
theorem EquicontinuousAt.comp {F : ι → X → α} {x₀ : X} (h : EquicontinuousAt F x₀) (u : κ → ι) :
    EquicontinuousAt (F ∘ u) x₀ := fun U hU => (h U hU).mono fun _ H k => H (u k)

/-- Taking sub-families preserves equicontinuity at a point within a subset. -/
/-
**EquicontinuousWithinAt.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EquicontinuousWithinAt.comp {F : ι -> X -> α} {S : Set X} {x₀ : X} (h : Eq
uicontinuousWithinAt F S x₀) (u : κ -> ι) : EquicontinuousWithinAt (F ∘ u) S x₀
参数：h : EquicontinuousWithinAt F S x₀；u : κ -> ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x

--- 原说明 ---
Taking sub-families preserves equicontinuity at a point within a subset.
-/
theorem EquicontinuousWithinAt.comp {F : ι → X → α} {S : Set X} {x₀ : X}
    (h : EquicontinuousWithinAt F S x₀) (u : κ → ι) :
    EquicontinuousWithinAt (F ∘ u) S x₀ :=
  fun U hU ↦ (h U hU).mono fun _ H k => H (u k)
/-
**Set.EquicontinuousAt.mono** 是 Mathlib 中的一个定理，位于命名空间 `Set.EquicontinuousAt`。
形式化陈述：∀ {X : Type u_3} {α : Type u_6} [tX : TopologicalSpace X] [uα : UniformSpa
ce α] {H H' : Set (X → α)} {x₀ : X},   H.EquicontinuousAt x₀ → H' ⊆ H → H'.Equic
ontinuousAt x₀
参数：X → α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquicontinuousAt.comp`：EquicontinuousAt.comp {F : ι -> X -> α} {x₀ : X} 
(h : EquicontinuousAt F x₀) (u : κ -> ι) : EquicontinuousAt (F ∘ u) x₀
-/
protected theorem Set.EquicontinuousAt.mono {H H' : Set <| X → α} {x₀ : X}
    (h : H.EquicontinuousAt x₀) (hH : H' ⊆ H) : H'.EquicontinuousAt x₀ :=
  h.comp (inclusion hH)
/-
**Set.EquicontinuousWithinAt.mono** 是 Mathlib 中的一个定理，位于命名空间 `Set.EquicontinuousW
ithinAt`。
形式化陈述：∀ {X : Type u_3} {α : Type u_6} [tX : TopologicalSpace X] [uα : UniformSpa
ce α] {H H' : Set (X → α)} {S : Set X}   {x₀ : X}, H.EquicontinuousWithinAt S x₀
 → H' ⊆ H → H'.EquicontinuousWithinAt S x₀
参数：X → α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquicontinuousWithinAt.comp`：EquicontinuousWithinAt.comp {F : ι -> X -> 
α} {S : Set X} {x₀ : X} (h : EquicontinuousWithinAt F S x₀) (u : κ -> ι) : Equic
ontinuousWithinAt…
-/
protected theorem Set.EquicontinuousWithinAt.mono {H H' : Set <| X → α} {S : Set X} {x₀ : X}
    (h : H.EquicontinuousWithinAt S x₀) (hH : H' ⊆ H) : H'.EquicontinuousWithinAt S x₀ :=
  h.comp (inclusion hH)

/-- Taking sub-families preserves equicontinuity. -/
/-
**Equicontinuous.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equicontinuous.comp {F : ι -> X -> α} (h : Equicontinuous F) (u : κ -> ι) 
: Equicontinuous (F ∘ u)
参数：h : Equicontinuous F；u : κ -> ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquicontinuousAt.comp`：EquicontinuousAt.comp {F : ι -> X -> α} {x₀ : X} 
(h : EquicontinuousAt F x₀) (u : κ -> ι) : EquicontinuousAt (F ∘ u) x₀

--- 原说明 ---
Taking sub-families preserves equicontinuity.
-/
theorem Equicontinuous.comp {F : ι → X → α} (h : Equicontinuous F) (u : κ → ι) :
    Equicontinuous (F ∘ u) := fun x => (h x).comp u

/-- Taking sub-families preserves equicontinuity on a subset. -/
/-
**EquicontinuousOn.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EquicontinuousOn.comp {F : ι -> X -> α} {S : Set X} (h : EquicontinuousOn 
F S) (u : κ -> ι) : EquicontinuousOn (F ∘ u) S
参数：h : EquicontinuousOn F S；u : κ -> ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquicontinuousWithinAt.comp`：EquicontinuousWithinAt.comp {F : ι -> X -> 
α} {S : Set X} {x₀ : X} (h : EquicontinuousWithinAt F S x₀) (u : κ -> ι) : Equic
ontinuousWithinAt…

--- 原说明 ---
Taking sub-families preserves equicontinuity on a subset.
-/
theorem EquicontinuousOn.comp {F : ι → X → α} {S : Set X} (h : EquicontinuousOn F S) (u : κ → ι) :
    EquicontinuousOn (F ∘ u) S := fun x hx ↦ (h x hx).comp u
/-
**Set.Equicontinuous.mono** 是 Mathlib 中的一个定理，位于命名空间 `Set.Equicontinuous`。
形式化陈述：∀ {X : Type u_3} {α : Type u_6} [tX : TopologicalSpace X] [uα : UniformSpa
ce α] {H H' : Set (X → α)},   H.Equicontinuous → H' ⊆ H → H'.Equicontinuous
参数：X → α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equicontinuous.comp`：Equicontinuous.comp {F : ι -> X -> α} (h : Equicont
inuous F) (u : κ -> ι) : Equicontinuous (F ∘ u)
-/
protected theorem Set.Equicontinuous.mono {H H' : Set <| X → α} (h : H.Equicontinuous)
    (hH : H' ⊆ H) : H'.Equicontinuous :=
  h.comp (inclusion hH)
/-
**Set.EquicontinuousOn.mono** 是 Mathlib 中的一个定理，位于命名空间 `Set.EquicontinuousOn`。
形式化陈述：∀ {X : Type u_3} {α : Type u_6} [tX : TopologicalSpace X] [uα : UniformSpa
ce α] {H H' : Set (X → α)} {S : Set X},   H.EquicontinuousOn S → H' ⊆ H → H'.Equ
icontinuousOn S
参数：X → α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquicontinuousOn.comp`：EquicontinuousOn.comp {F : ι -> X -> α} {S : Set 
X} (h : EquicontinuousOn F S) (u : κ -> ι) : EquicontinuousOn (F ∘ u) S
-/
protected theorem Set.EquicontinuousOn.mono {H H' : Set <| X → α} {S : Set X}
    (h : H.EquicontinuousOn S) (hH : H' ⊆ H) : H'.EquicontinuousOn S :=
  h.comp (inclusion hH)

/-- Taking sub-families preserves uniform equicontinuity. -/
/-
**UniformEquicontinuous.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformEquicontinuous.comp {F : ι -> β -> α} (h : UniformEquicontinuous F)
 (u : κ -> ι) : UniformEquicontinuous (F ∘ u)
参数：h : UniformEquicontinuous F；u : κ -> ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x

--- 原说明 ---
Taking sub-families preserves uniform equicontinuity.
-/
theorem UniformEquicontinuous.comp {F : ι → β → α} (h : UniformEquicontinuous F) (u : κ → ι) :
    UniformEquicontinuous (F ∘ u) := fun U hU => (h U hU).mono fun _ H k => H (u k)

/-- Taking sub-families preserves uniform equicontinuity on a subset. -/
/-
**UniformEquicontinuousOn.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformEquicontinuousOn.comp {F : ι -> β -> α} {S : Set β} (h : UniformEqu
icontinuousOn F S) (u : κ -> ι) : UniformEquicontinuousOn (F ∘ u) S
参数：h : UniformEquicontinuousOn F S；u : κ -> ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x

--- 原说明 ---
Taking sub-families preserves uniform equicontinuity on a subset.
-/
theorem UniformEquicontinuousOn.comp {F : ι → β → α} {S : Set β} (h : UniformEquicontinuousOn F S)
    (u : κ → ι) : UniformEquicontinuousOn (F ∘ u) S :=
  fun U hU ↦ (h U hU).mono fun _ H k => H (u k)
/-
**Set.UniformEquicontinuous.mono** 是 Mathlib 中的一个定理，位于命名空间 `Set.UniformEquiconti
nuous`。
形式化陈述：∀ {α : Type u_6} {β : Type u_8} [uα : UniformSpace α] [uβ : UniformSpace β
] {H H' : Set (β → α)},   H.UniformEquicontinuous → H' ⊆ H → H'.UniformEquiconti
nuous
参数：β → α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformEquicontinuous.comp`：UniformEquicontinuous.comp {F : ι -> β -> α}
 (h : UniformEquicontinuous F) (u : κ -> ι) : UniformEquicontinuous (F ∘ u)
-/
protected theorem Set.UniformEquicontinuous.mono {H H' : Set <| β → α} (h : H.UniformEquicontinuous)
    (hH : H' ⊆ H) : H'.UniformEquicontinuous :=
  h.comp (inclusion hH)
/-
**Set.UniformEquicontinuousOn.mono** 是 Mathlib 中的一个定理，位于命名空间 `Set.UniformEquicon
tinuousOn`。
形式化陈述：∀ {α : Type u_6} {β : Type u_8} [uα : UniformSpace α] [uβ : UniformSpace β
] {H H' : Set (β → α)} {S : Set β},   H.UniformEquicontinuousOn S → H' ⊆ H → H'.
UniformEquicontinuousOn S
参数：β → α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformEquicontinuousOn.comp`：UniformEquicontinuousOn.comp {F : ι -> β -
> α} {S : Set β} (h : UniformEquicontinuousOn F S) (u : κ -> ι) : UniformEquicon
tinuousOn (F ∘ u) …
-/
protected theorem Set.UniformEquicontinuousOn.mono {H H' : Set <| β → α} {S : Set β}
    (h : H.UniformEquicontinuousOn S) (hH : H' ⊆ H) : H'.UniformEquicontinuousOn S :=
  h.comp (inclusion hH)

/-- A family `𝓕 : ι → X → α` is equicontinuous at `x₀` iff `range 𝓕` is equicontinuous at `x₀`,
i.e the family `(↑) : range F → X → α` is equicontinuous at `x₀`. -/
/-
**equicontinuousAt_iff_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：equicontinuousAt_iff_range {F : ι -> X -> α} {x₀ : X} : EquicontinuousAt F
 x₀ ↔ EquicontinuousAt ((↑) : range F -> X -> α) x₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A family `𝓕 : ι → X → α` is equicontinuous at `x₀` iff `range 𝓕` is equicontinuo
us at `x₀`,
i.e the family `(↑) : range F → X → α` is equicontinuous at `x₀`.
-/
theorem equicontinuousAt_iff_range {F : ι → X → α} {x₀ : X} :
    EquicontinuousAt F x₀ ↔ EquicontinuousAt ((↑) : range F → X → α) x₀ := by
  simp only [EquicontinuousAt, forall_subtype_range_iff]

/-- A family `𝓕 : ι → X → α` is equicontinuous at `x₀` within `S` iff `range 𝓕` is equicontinuous
at `x₀` within `S`, i.e the family `(↑) : range F → X → α` is equicontinuous at `x₀` within `S`. -/
/-
**equicontinuousWithinAt_iff_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：equicontinuousWithinAt_iff_range {F : ι -> X -> α} {S : Set X} {x₀ : X} : 
EquicontinuousWithinAt F S x₀ ↔ EquicontinuousWithinAt ((↑) : range F -> X -> α)
 S x₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A family `𝓕 : ι → X → α` is equicontinuous at `x₀` within `S` iff `range 𝓕` is e
quicontinuous
at `x₀` within `S`, i.e the family `(↑) : range F → X → α` is equicontinuous at 
`x₀` within `S`.
-/
theorem equicontinuousWithinAt_iff_range {F : ι → X → α} {S : Set X} {x₀ : X} :
    EquicontinuousWithinAt F S x₀ ↔ EquicontinuousWithinAt ((↑) : range F → X → α) S x₀ := by
  simp only [EquicontinuousWithinAt, forall_subtype_range_iff]

/-- A family `𝓕 : ι → X → α` is equicontinuous iff `range 𝓕` is equicontinuous,
i.e the family `(↑) : range F → X → α` is equicontinuous. -/
/-
**equicontinuous_iff_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：equicontinuous_iff_range {F : ι -> X -> α} : Equicontinuous F ↔ Equicontin
uous ((↑) : range F -> X -> α)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `equicontinuousAt_iff_range`：equicontinuousAt_iff_range {F : ι -> X -> α}
 {x₀ : X} : EquicontinuousAt F x₀ ↔ EquicontinuousAt ((↑) : range F -> X -> α) x
₀

--- 原说明 ---
A family `𝓕 : ι → X → α` is equicontinuous iff `range 𝓕` is equicontinuous,
i.e the family `(↑) : range F → X → α` is equicontinuous.
-/
theorem equicontinuous_iff_range {F : ι → X → α} :
    Equicontinuous F ↔ Equicontinuous ((↑) : range F → X → α) :=
  forall_congr' fun _ => equicontinuousAt_iff_range

/-- A family `𝓕 : ι → X → α` is equicontinuous on `S` iff `range 𝓕` is equicontinuous on `S`,
i.e the family `(↑) : range F → X → α` is equicontinuous on `S`. -/
/-
**equicontinuousOn_iff_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：equicontinuousOn_iff_range {F : ι -> X -> α} {S : Set X} : EquicontinuousO
n F S ↔ EquicontinuousOn ((↑) : range F -> X -> α) S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `equicontinuousWithinAt_iff_range`：equicontinuousWithinAt_iff_range {F : 
ι -> X -> α} {S : Set X} {x₀ : X} : EquicontinuousWithinAt F S x₀ ↔ Equicontinuo
usWithinAt ((↑) : rang…

--- 原说明 ---
A family `𝓕 : ι → X → α` is equicontinuous on `S` iff `range 𝓕` is equicontinuou
s on `S`,
i.e the family `(↑) : range F → X → α` is equicontinuous on `S`.
-/
theorem equicontinuousOn_iff_range {F : ι → X → α} {S : Set X} :
    EquicontinuousOn F S ↔ EquicontinuousOn ((↑) : range F → X → α) S :=
  forall_congr' fun _ ↦ forall_congr' fun _ ↦ equicontinuousWithinAt_iff_range

/-- A family `𝓕 : ι → β → α` is uniformly equicontinuous iff `range 𝓕` is uniformly equicontinuous,
i.e the family `(↑) : range F → β → α` is uniformly equicontinuous. -/
/-
**uniformEquicontinuous_iff_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformEquicontinuous_iff_range {F : ι -> β -> α} : UniformEquicontinuous 
F ↔ UniformEquicontinuous ((↑) : range F -> β -> α)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.comp_rangeSplitting`：comp_rangeSplitting (f : α -> β) : f ∘ rangeSpl
itting f = Subtype.val
· 使用定理 `UniformEquicontinuous.comp`：UniformEquicontinuous.comp {F : ι -> β -> α}
 (h : UniformEquicontinuous F) (u : κ -> ι) : UniformEquicontinuous (F ∘ u)

--- 原说明 ---
A family `𝓕 : ι → β → α` is uniformly equicontinuous iff `range 𝓕` is uniformly 
equicontinuous,
i.e the family `(↑) : range F → β → α` is uniformly equicontinuous.
-/
theorem uniformEquicontinuous_iff_range {F : ι → β → α} :
    UniformEquicontinuous F ↔ UniformEquicontinuous ((↑) : range F → β → α) :=
  ⟨fun h => by rw [← comp_rangeSplitting F]; exact h.comp _, fun h =>
    h.comp (rangeFactorization F)⟩

/-- A family `𝓕 : ι → β → α` is uniformly equicontinuous on `S` iff `range 𝓕` is uniformly
equicontinuous on `S`, i.e the family `(↑) : range F → β → α` is uniformly equicontinuous on `S`. -/
/-
**uniformEquicontinuousOn_iff_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformEquicontinuousOn_iff_range {F : ι -> β -> α} {S : Set β} : UniformE
quicontinuousOn F S ↔ UniformEquicontinuousOn ((↑) : range F -> β -> α) S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.comp_rangeSplitting`：comp_rangeSplitting (f : α -> β) : f ∘ rangeSpl
itting f = Subtype.val
· 使用定理 `UniformEquicontinuousOn.comp`：UniformEquicontinuousOn.comp {F : ι -> β -
> α} {S : Set β} (h : UniformEquicontinuousOn F S) (u : κ -> ι) : UniformEquicon
tinuousOn (F ∘ u) …

--- 原说明 ---
A family `𝓕 : ι → β → α` is uniformly equicontinuous on `S` iff `range 𝓕` is uni
formly
equicontinuous on `S`, i.e the family `(↑) : range F → β → α` is uniformly equic
ontinuous on `S`.
-/
theorem uniformEquicontinuousOn_iff_range {F : ι → β → α} {S : Set β} :
    UniformEquicontinuousOn F S ↔ UniformEquicontinuousOn ((↑) : range F → β → α) S :=
  ⟨fun h => by rw [← comp_rangeSplitting F]; exact h.comp _, fun h =>
    h.comp (rangeFactorization F)⟩

section

open UniformFun

/-- A family `𝓕 : ι → X → α` is equicontinuous at `x₀` iff the function `swap 𝓕 : X → ι → α` is
continuous at `x₀` *when `ι → α` is equipped with the topology of uniform convergence*. This is
very useful for developing the equicontinuity API, but it should not be used directly for other
purposes. -/
/-
**equicontinuousAt_iff_continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：equicontinuousAt_iff_continuousAt {F : ι -> X -> α} {x₀ : X} : Equicontinu
ousAt F x₀ ↔ ContinuousAt (ofFun ∘ Function.swap F : X -> ι ->ᵤ α) x₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (x : X),   ContinuousAt f x = F
ilter.T…
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `UniformFun.hasBasis_nhds`：∀ (α : Type u_1) (β : Type u_2) [inst : Unifor
mSpace β] (f : UniformFun α β),   (nhds f).HasBasis (fun V => V ∈ uniformity β) 
fun V => {g | …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A family `𝓕 : ι → X → α` is equicontinuous at `x₀` iff the function `swap 𝓕 : X 
→ ι → α` is
continuous at `x₀` *when `ι → α` is equipped with the topology of uniform conver
gence*. This is
very useful for developing the equicontinuity API, but it should not be used dir
ectly for other
purposes.
-/
theorem equicontinuousAt_iff_continuousAt {F : ι → X → α} {x₀ : X} :
    EquicontinuousAt F x₀ ↔ ContinuousAt (ofFun ∘ Function.swap F : X → ι →ᵤ α) x₀ := by
  rw [ContinuousAt, (UniformFun.hasBasis_nhds ι α _).tendsto_right_iff]
  rfl

/-- A family `𝓕 : ι → X → α` is equicontinuous at `x₀` within `S` iff the function
`swap 𝓕 : X → ι → α` is continuous at `x₀` within `S`
*when `ι → α` is equipped with the topology of uniform convergence*. This is very useful for
developing the equicontinuity API, but it should not be used directly for other purposes. -/
/-
**equicontinuousWithinAt_iff_continuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：equicontinuousWithinAt_iff_continuousWithinAt {F : ι -> X -> α} {S : Set X
} {x₀ : X} : EquicontinuousWithinAt F S x₀ ↔ ContinuousWithinAt (ofFun ∘ Functio
n.swap F : X -> ι ->ᵤ α) S x₀
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousWithinAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (s : Set X)   (x : X), Co
ntinuousWithi…
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `UniformFun.hasBasis_nhds`：∀ (α : Type u_1) (β : Type u_2) [inst : Unifor
mSpace β] (f : UniformFun α β),   (nhds f).HasBasis (fun V => V ∈ uniformity β) 
fun V => {g | …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A family `𝓕 : ι → X → α` is equicontinuous at `x₀` within `S` iff the function
`swap 𝓕 : X → ι → α` is continuous at `x₀` within `S`
*when `ι → α` is equipped with the topology of uniform convergence*. This is ver
y useful for
developing the equicontinuity API, but it should not be used directly for other 
purposes.
-/
theorem equicontinuousWithinAt_iff_continuousWithinAt {F : ι → X → α} {S : Set X} {x₀ : X} :
    EquicontinuousWithinAt F S x₀ ↔
    ContinuousWithinAt (ofFun ∘ Function.swap F : X → ι →ᵤ α) S x₀ := by
  rw [ContinuousWithinAt, (UniformFun.hasBasis_nhds ι α _).tendsto_right_iff]
  rfl

/-- A family `𝓕 : ι → X → α` is equicontinuous iff the function `swap 𝓕 : X → ι → α` is
continuous *when `ι → α` is equipped with the topology of uniform convergence*. This is
very useful for developing the equicontinuity API, but it should not be used directly for other
purposes. -/
/-
**equicontinuous_iff_continuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：equicontinuous_iff_continuous {F : ι -> X -> α} : Equicontinuous F ↔ Conti
nuous (ofFun ∘ Function.swap F : X -> ι ->ᵤ α)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A family `𝓕 : ι → X → α` is equicontinuous iff the function `swap 𝓕 : X → ι → α`
 is
continuous *when `ι → α` is equipped with the topology of uniform convergence*. 
This is
very useful for developing the equicontinuity API, but it should not be used dir
ectly for other
purposes.
-/
theorem equicontinuous_iff_continuous {F : ι → X → α} :
    Equicontinuous F ↔ Continuous (ofFun ∘ Function.swap F : X → ι →ᵤ α) := by
  simp_rw [Equicontinuous, continuous_iff_continuousAt, equicontinuousAt_iff_continuousAt]

/-- A family `𝓕 : ι → X → α` is equicontinuous on `S` iff the function `swap 𝓕 : X → ι → α` is
continuous on `S` *when `ι → α` is equipped with the topology of uniform convergence*. This is
very useful for developing the equicontinuity API, but it should not be used directly for other
purposes. -/
/-
**equicontinuousOn_iff_continuousOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：equicontinuousOn_iff_continuousOn {F : ι -> X -> α} {S : Set X} : Equicont
inuousOn F S ↔ ContinuousOn (ofFun ∘ Function.swap F : X -> ι ->ᵤ α) S
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
A family `𝓕 : ι → X → α` is equicontinuous on `S` iff the function `swap 𝓕 : X →
 ι → α` is
continuous on `S` *when `ι → α` is equipped with the topology of uniform converg
ence*. This is
very useful for developing the equicontinuity API, but it should not be used dir
ectly for other
purposes.
-/
theorem equicontinuousOn_iff_continuousOn {F : ι → X → α} {S : Set X} :
    EquicontinuousOn F S ↔ ContinuousOn (ofFun ∘ Function.swap F : X → ι →ᵤ α) S := by
  simp_rw [EquicontinuousOn, ContinuousOn, equicontinuousWithinAt_iff_continuousWithinAt]

/-- A family `𝓕 : ι → β → α` is uniformly equicontinuous iff the function `swap 𝓕 : β → ι → α` is
uniformly continuous *when `ι → α` is equipped with the uniform structure of uniform convergence*.
This is very useful for developing the equicontinuity API, but it should not be used directly
for other purposes. -/
/-
**uniformEquicontinuous_iff_uniformContinuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformEquicontinuous_iff_uniformContinuous {F : ι -> β -> α} : UniformEqu
icontinuous F ↔ UniformContinuous (ofFun ∘ Function.swap F : β -> ι ->ᵤ α)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformContinuous.eq_1`：∀ {α : Type ua} {β : Type ub} [inst : UniformSpa
ce α] [inst_1 : UniformSpace β] (f : α → β),   UniformContinuous f = Filter.Tend
sto (fun x =…
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `UniformFun.hasBasis_uniformity`：∀ (α : Type u_1) (β : Type u_2) [inst : 
UniformSpace β],   (uniformity (UniformFun α β)).HasBasis (fun x => x ∈ uniformi
ty β) (UniformFun.ge…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A family `𝓕 : ι → β → α` is uniformly equicontinuous iff the function `swap 𝓕 : 
β → ι → α` is
uniformly continuous *when `ι → α` is equipped with the uniform structure of uni
form convergence*.
This is very useful for developing the equicontinuity API, but it should not be 
used directly
for other purposes.
-/
theorem uniformEquicontinuous_iff_uniformContinuous {F : ι → β → α} :
    UniformEquicontinuous F ↔ UniformContinuous (ofFun ∘ Function.swap F : β → ι →ᵤ α) := by
  rw [UniformContinuous, (UniformFun.hasBasis_uniformity ι α).tendsto_right_iff]
  rfl

/-- A family `𝓕 : ι → β → α` is uniformly equicontinuous on `S` iff the function
`swap 𝓕 : β → ι → α` is uniformly continuous on `S`
*when `ι → α` is equipped with the uniform structure of uniform convergence*. This is very useful
for developing the equicontinuity API, but it should not be used directly for other purposes. -/
/-
**uniformEquicontinuousOn_iff_uniformContinuousOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformEquicontinuousOn_iff_uniformContinuousOn {F : ι -> β -> α} {S : Set
 β} : UniformEquicontinuousOn F S ↔ UniformContinuousOn (ofFun ∘ Function.swap F
 : β -> ι ->ᵤ α) S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniformContinuousOn.eq_1`：∀ {α : Type ua} {β : Type ub} [inst : UniformS
pace α] [inst_1 : UniformSpace β] (f : α → β) (s : Set α),   UniformContinuousOn
 f s =     Fil…
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `UniformFun.hasBasis_uniformity`：∀ (α : Type u_1) (β : Type u_2) [inst : 
UniformSpace β],   (uniformity (UniformFun α β)).HasBasis (fun x => x ∈ uniformi
ty β) (UniformFun.ge…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A family `𝓕 : ι → β → α` is uniformly equicontinuous on `S` iff the function
`swap 𝓕 : β → ι → α` is uniformly continuous on `S`
*when `ι → α` is equipped with the uniform structure of uniform convergence*. Th
is is very useful
for developing the equicontinuity API, but it should not be used directly for ot
her purposes.
-/
theorem uniformEquicontinuousOn_iff_uniformContinuousOn {F : ι → β → α} {S : Set β} :
    UniformEquicontinuousOn F S ↔ UniformContinuousOn (ofFun ∘ Function.swap F : β → ι →ᵤ α) S := by
  rw [UniformContinuousOn, (UniformFun.hasBasis_uniformity ι α).tendsto_right_iff]
  rfl
/-
**equicontinuousWithinAt_iInf_rng** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：equicontinuousWithinAt_iInf_rng {u : κ -> UniformSpace α'} {F : ι -> X -> 
α'} {S : Set X} {x₀ : X} : EquicontinuousWithinAt (uα
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `equicontinuousWithinAt_iff_continuousWithinAt`：equicontinuousWithinAt_if
f_continuousWithinAt {F : ι -> X -> α} {S : Set X} {x₀ : X} : EquicontinuousWith
inAt F S x₀ ↔ ContinuousWithinAt (o…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `UniformFun.iInf_eq`：∀ {α : Type u_1} {γ : Type u_3} {ι : Type u_4} {u : 
ι → UniformSpace γ},   UniformFun.uniformSpace α γ = ⨅ i, UniformFun.uniformSpac
e α γ
· 使用定理 `UniformSpace.toTopologicalSpace_iInf`：toTopologicalSpace_iInf {ι : Sort*
} {u : ι -> UniformSpace α} : (iInf u).toTopologicalSpace = ⨅ i, (u i).toTopolog
icalSpace
· 使用定理 `nhds_iInf`：nhds_iInf {ι : Sort*} {t : ι -> TopologicalSpace α} {a : α} :
 @nhds α (iInf t) a = ⨅ i, @nhds α (t i) a
· 使用定理 `Filter.tendsto_iInf`：tendsto_iInf {f : α -> β} {x : Filter α} {y : ι -> 
Filter β} : Tendsto f x (⨅ i, y i) ↔ forall i, Tendsto f x (y i)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem equicontinuousWithinAt_iInf_rng {u : κ → UniformSpace α'} {F : ι → X → α'}
    {S : Set X} {x₀ : X} : EquicontinuousWithinAt (uα := ⨅ k, u k) F S x₀ ↔
      ∀ k, EquicontinuousWithinAt (uα := u k) F S x₀ := by
  simp +instances only [equicontinuousWithinAt_iff_continuousWithinAt (uα := _), topologicalSpace]
  unfold ContinuousWithinAt
  rw [UniformFun.iInf_eq, toTopologicalSpace_iInf, nhds_iInf, tendsto_iInf]
/-
**equicontinuousAt_iInf_rng** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：equicontinuousAt_iInf_rng {u : κ -> UniformSpace α'} {F : ι -> X -> α'} {x
₀ : X} : EquicontinuousAt (uα
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `equicontinuousWithinAt_univ`：∀ {ι : Type u_1} {X : Type u_3} {α : Type u
_6} [tX : TopologicalSpace X] [uα : UniformSpace α] (F : ι → X → α) (x₀ : X),   
EquicontinuousWit…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem equicontinuousAt_iInf_rng {u : κ → UniformSpace α'} {F : ι → X → α'}
    {x₀ : X} :
    EquicontinuousAt (uα := ⨅ k, u k) F x₀ ↔ ∀ k, EquicontinuousAt (uα := u k) F x₀ := by
  simp only [← equicontinuousWithinAt_univ (uα := _), equicontinuousWithinAt_iInf_rng]
/-
**equicontinuous_iInf_rng** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：equicontinuous_iInf_rng {u : κ -> UniformSpace α'} {F : ι -> X -> α'} : Eq
uicontinuous (uα
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `equicontinuous_iff_continuous`：equicontinuous_iff_continuous {F : ι -> X
 -> α} : Equicontinuous F ↔ Continuous (ofFun ∘ Function.swap F : X -> ι ->ᵤ α)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `UniformFun.iInf_eq`：∀ {α : Type u_1} {γ : Type u_3} {ι : Type u_4} {u : 
ι → UniformSpace γ},   UniformFun.uniformSpace α γ = ⨅ i, UniformFun.uniformSpac
e α γ
· 使用定理 `UniformSpace.toTopologicalSpace_iInf`：toTopologicalSpace_iInf {ι : Sort*
} {u : ι -> UniformSpace α} : (iInf u).toTopologicalSpace = ⨅ i, (u i).toTopolog
icalSpace
· 使用定理 `continuous_iInf_rng`：continuous_iInf_rng {t₁ : TopologicalSpace α} {t₂ :
 ι -> TopologicalSpace β} : Continuous[t₁, iInf t₂] f ↔ forall i, Continuous[t₁,
 t₂ i] f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem equicontinuous_iInf_rng {u : κ → UniformSpace α'} {F : ι → X → α'} :
    Equicontinuous (uα := ⨅ k, u k) F ↔ ∀ k, Equicontinuous (uα := u k) F := by
  simp_rw +instances [equicontinuous_iff_continuous (uα := _), UniformFun.topologicalSpace]
  rw [UniformFun.iInf_eq, toTopologicalSpace_iInf, continuous_iInf_rng]
/-
**equicontinuousOn_iInf_rng** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：equicontinuousOn_iInf_rng {u : κ -> UniformSpace α'} {F : ι -> X -> α'} {S
 : Set X} : EquicontinuousOn (uα
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem equicontinuousOn_iInf_rng {u : κ → UniformSpace α'} {F : ι → X → α'}
    {S : Set X} :
    EquicontinuousOn (uα := ⨅ k, u k) F S ↔ ∀ k, EquicontinuousOn (uα := u k) F S := by
  simp_rw [EquicontinuousOn, equicontinuousWithinAt_iInf_rng, @forall_comm _ κ]
/-
**uniformEquicontinuous_iInf_rng** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformEquicontinuous_iInf_rng {u : κ -> UniformSpace α'} {F : ι -> β -> α
'} : UniformEquicontinuous (uα
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `uniformEquicontinuous_iff_uniformContinuous`：uniformEquicontinuous_iff_u
niformContinuous {F : ι -> β -> α} : UniformEquicontinuous F ↔ UniformContinuous
 (ofFun ∘ Function.swap F : β -> …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `UniformFun.iInf_eq`：∀ {α : Type u_1} {γ : Type u_3} {ι : Type u_4} {u : 
ι → UniformSpace γ},   UniformFun.uniformSpace α γ = ⨅ i, UniformFun.uniformSpac
e α γ
· 使用定理 `uniformContinuous_iInf_rng`：uniformContinuous_iInf_rng {f : α -> β} {u₁ 
: UniformSpace α} {u₂ : ι -> UniformSpace β} : UniformContinuous[u₁, iInf u₂] f 
↔ forall i, Unif…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem uniformEquicontinuous_iInf_rng {u : κ → UniformSpace α'} {F : ι → β → α'} :
    UniformEquicontinuous (uα := ⨅ k, u k) F ↔ ∀ k, UniformEquicontinuous (uα := u k) F := by
  simp_rw [uniformEquicontinuous_iff_uniformContinuous (uα := _)]
  rw [UniformFun.iInf_eq, uniformContinuous_iInf_rng]
/-
**uniformEquicontinuousOn_iInf_rng** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformEquicontinuousOn_iInf_rng {u : κ -> UniformSpace α'} {F : ι -> β ->
 α'} {S : Set β} : UniformEquicontinuousOn (uα
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `uniformEquicontinuousOn_iff_uniformContinuousOn`：uniformEquicontinuousOn
_iff_uniformContinuousOn {F : ι -> β -> α} {S : Set β} : UniformEquicontinuousOn
 F S ↔ UniformContinuousOn (ofFun ∘ F…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `UniformFun.iInf_eq`：∀ {α : Type u_1} {γ : Type u_3} {ι : Type u_4} {u : 
ι → UniformSpace γ},   UniformFun.uniformSpace α γ = ⨅ i, UniformFun.uniformSpac
e α γ
· 使用定理 `iInf_uniformity`：iInf_uniformity {ι : Sort*} {u : ι -> UniformSpace α} :
 𝓤[iInf u] = ⨅ i, 𝓤[u i]
· 使用定理 `Filter.tendsto_iInf`：tendsto_iInf {f : α -> β} {x : Filter α} {y : ι -> 
Filter β} : Tendsto f x (⨅ i, y i) ↔ forall i, Tendsto f x (y i)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem uniformEquicontinuousOn_iInf_rng {u : κ → UniformSpace α'} {F : ι → β → α'}
    {S : Set β} : UniformEquicontinuousOn (uα := ⨅ k, u k) F S ↔
      ∀ k, UniformEquicontinuousOn (uα := u k) F S := by
  simp_rw [uniformEquicontinuousOn_iff_uniformContinuousOn (uα := _)]
  unfold UniformContinuousOn
  rw [UniformFun.iInf_eq, iInf_uniformity, tendsto_iInf]
/-
**equicontinuousWithinAt_iInf_dom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：equicontinuousWithinAt_iInf_dom {t : κ -> TopologicalSpace X'} {F : ι -> X
' -> α} {S : Set X'} {x₀ : X'} {k : κ} (hk : EquicontinuousWithinAt (tX
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `equicontinuousWithinAt_iff_continuousWithinAt`：equicontinuousWithinAt_if
f_continuousWithinAt {F : ι -> X -> α} {S : Set X} {x₀ : X} : EquicontinuousWith
inAt F S x₀ ↔ ContinuousWithinAt (o…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhds_iInf`：nhds_iInf {ι : Sort*} {t : ι -> TopologicalSpace α} {a : α} :
 @nhds α (iInf t) a = ⨅ i, @nhds α (t i) a
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `inf_le_inf_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α} (c 
: α), b ≤ a → b ⊓ c ≤ a ⊓ c
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
-/
theorem equicontinuousWithinAt_iInf_dom {t : κ → TopologicalSpace X'} {F : ι → X' → α}
    {S : Set X'} {x₀ : X'} {k : κ} (hk : EquicontinuousWithinAt (tX := t k) F S x₀) :
    EquicontinuousWithinAt (tX := ⨅ k, t k) F S x₀ := by
  simp only [equicontinuousWithinAt_iff_continuousWithinAt (tX := _)] at hk ⊢
  unfold ContinuousWithinAt nhdsWithin at hk ⊢
  rw [nhds_iInf]
  exact hk.mono_left <| inf_le_inf_right _ <| iInf_le _ k
/-
**equicontinuousAt_iInf_dom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：equicontinuousAt_iInf_dom {t : κ -> TopologicalSpace X'} {F : ι -> X' -> α
} {x₀ : X'} {k : κ} (hk : EquicontinuousAt (tX
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `equicontinuousWithinAt_univ`：∀ {ι : Type u_1} {X : Type u_3} {α : Type u
_6} [tX : TopologicalSpace X] [uα : UniformSpace α] (F : ι → X → α) (x₀ : X),   
EquicontinuousWit…
· 使用定理 `equicontinuousWithinAt_iInf_dom`：equicontinuousWithinAt_iInf_dom {t : κ 
-> TopologicalSpace X'} {F : ι -> X' -> α} {S : Set X'} {x₀ : X'} {k : κ} (hk : 
EquicontinuousWithinA…
-/
theorem equicontinuousAt_iInf_dom {t : κ → TopologicalSpace X'} {F : ι → X' → α}
    {x₀ : X'} {k : κ} (hk : EquicontinuousAt (tX := t k) F x₀) :
    EquicontinuousAt (tX := ⨅ k, t k) F x₀ := by
  rw [← equicontinuousWithinAt_univ (tX := _)] at hk ⊢
  exact equicontinuousWithinAt_iInf_dom hk
/-
**equicontinuous_iInf_dom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：equicontinuous_iInf_dom {t : κ -> TopologicalSpace X'} {F : ι -> X' -> α} 
{k : κ} (hk : Equicontinuous (tX
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `equicontinuousAt_iInf_dom`：equicontinuousAt_iInf_dom {t : κ -> Topologic
alSpace X'} {F : ι -> X' -> α} {x₀ : X'} {k : κ} (hk : EquicontinuousAt (tX
-/
theorem equicontinuous_iInf_dom {t : κ → TopologicalSpace X'} {F : ι → X' → α}
    {k : κ} (hk : Equicontinuous (tX := t k) F) :
    Equicontinuous (tX := ⨅ k, t k) F :=
  fun x ↦ equicontinuousAt_iInf_dom (hk x)
/-
**equicontinuousOn_iInf_dom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：equicontinuousOn_iInf_dom {t : κ -> TopologicalSpace X'} {F : ι -> X' -> α
} {S : Set X'} {k : κ} (hk : EquicontinuousOn (tX
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `equicontinuousWithinAt_iInf_dom`：equicontinuousWithinAt_iInf_dom {t : κ 
-> TopologicalSpace X'} {F : ι -> X' -> α} {S : Set X'} {x₀ : X'} {k : κ} (hk : 
EquicontinuousWithinA…
-/
theorem equicontinuousOn_iInf_dom {t : κ → TopologicalSpace X'} {F : ι → X' → α}
    {S : Set X'} {k : κ} (hk : EquicontinuousOn (tX := t k) F S) :
    EquicontinuousOn (tX := ⨅ k, t k) F S :=
  fun x hx ↦ equicontinuousWithinAt_iInf_dom (hk x hx)
/-
**uniformEquicontinuous_iInf_dom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformEquicontinuous_iInf_dom {u : κ -> UniformSpace β'} {F : ι -> β' -> 
α} {k : κ} (hk : UniformEquicontinuous (uβ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniformEquicontinuous_iff_uniformContinuous`：uniformEquicontinuous_iff_u
niformContinuous {F : ι -> β -> α} : UniformEquicontinuous F ↔ UniformContinuous
 (ofFun ∘ Function.swap F : β -> …
· 使用定理 `uniformContinuous_iInf_dom`：uniformContinuous_iInf_dom {f : α -> β} {u₁ 
: ι -> UniformSpace α} {u₂ : UniformSpace β} {i : ι} (hf : UniformContinuous[u₁ 
i, u₂] f) : Unif…
-/
theorem uniformEquicontinuous_iInf_dom {u : κ → UniformSpace β'} {F : ι → β' → α}
    {k : κ} (hk : UniformEquicontinuous (uβ := u k) F) :
    UniformEquicontinuous (uβ := ⨅ k, u k) F := by
  simp_rw [uniformEquicontinuous_iff_uniformContinuous (uβ := _)] at hk ⊢
  exact uniformContinuous_iInf_dom hk
/-
**uniformEquicontinuousOn_iInf_dom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniformEquicontinuousOn_iInf_dom {u : κ -> UniformSpace β'} {F : ι -> β' -
> α} {S : Set β'} {k : κ} (hk : UniformEquicontinuousOn (uβ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniformEquicontinuousOn_iff_uniformContinuousOn`：uniformEquicontinuousOn
_iff_uniformContinuousOn {F : ι -> β -> α} {S : Set β} : UniformEquicontinuousOn
 F S ↔ UniformContinuousOn (ofFun ∘ F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf_uniformity`：iInf_uniformity {ι : Sort*} {u : ι -> UniformSpace α} :
 𝓤[iInf u] = ⨅ i, 𝓤[u i]
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `inf_le_inf_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α} (c 
: α), b ≤ a → b ⊓ c ≤ a ⊓ c
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
-/
theorem uniformEquicontinuousOn_iInf_dom {u : κ → UniformSpace β'} {F : ι → β' → α}
    {S : Set β'} {k : κ} (hk : UniformEquicontinuousOn (uβ := u k) F S) :
    UniformEquicontinuousOn (uβ := ⨅ k, u k) F S := by
  simp_rw [uniformEquicontinuousOn_iff_uniformContinuousOn (uβ := _)] at hk ⊢
  unfold UniformContinuousOn
  rw [iInf_uniformity]
  exact hk.mono_left <| inf_le_inf_right _ <| iInf_le _ k
/-
**Filter.HasBasis.equicontinuousAt_iff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.equicontinuousAt_iff_left {p : κ -> Prop} {s : κ -> Set X}
 {F : ι -> X -> α} {x₀ : X} (hX : (𝓝 x₀).HasBasis p s) : EquicontinuousAt F x₀ ↔
 forall U in 𝓤 α, exists k, p k ∧ forall x in s k, forall i, (F i x₀, F i x) in 
U
参数：hX : (𝓝 x₀).HasBasis p s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `equicontinuousAt_iff_continuousAt`：equicontinuousAt_iff_continuousAt {F 
: ι -> X -> α} {x₀ : X} : EquicontinuousAt F x₀ ↔ ContinuousAt (ofFun ∘ Function
.swap F : X -> ι ->ᵤ α)…
· 使用定理 `ContinuousAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (x : X),   ContinuousAt f x = F
ilter.T…
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `UniformFun.hasBasis_nhds`：∀ (α : Type u_1) (β : Type u_2) [inst : Unifor
mSpace β] (f : UniformFun α β),   (nhds f).HasBasis (fun V => V ∈ uniformity β) 
fun V => {g | …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Filter.HasBasis.equicontinuousAt_iff_left {p : κ → Prop} {s : κ → Set X}
    {F : ι → X → α} {x₀ : X} (hX : (𝓝 x₀).HasBasis p s) :
    EquicontinuousAt F x₀ ↔ ∀ U ∈ 𝓤 α, ∃ k, p k ∧ ∀ x ∈ s k, ∀ i, (F i x₀, F i x) ∈ U := by
  rw [equicontinuousAt_iff_continuousAt, ContinuousAt,
    hX.tendsto_iff (UniformFun.hasBasis_nhds ι α _)]
  rfl
/-
**Filter.HasBasis.equicontinuousWithinAt_iff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.equicontinuousWithinAt_iff_left {p : κ -> Prop} {s : κ -> 
Set X} {F : ι -> X -> α} {S : Set X} {x₀ : X} (hX : (𝓝[S] x₀).HasBasis p s) : Eq
uicontinuousWithinAt F S x₀ ↔ forall U in 𝓤 α, exists k, p k ∧ forall x in s k, 
forall i, (F i x₀, F i x) in U
参数：hX : (𝓝[S] x₀).HasBasis p s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `equicontinuousWithinAt_iff_continuousWithinAt`：equicontinuousWithinAt_if
f_continuousWithinAt {F : ι -> X -> α} {S : Set X} {x₀ : X} : EquicontinuousWith
inAt F S x₀ ↔ ContinuousWithinAt (o…
· 使用定理 `ContinuousWithinAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (s : Set X)   (x : X), Co
ntinuousWithi…
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `UniformFun.hasBasis_nhds`：∀ (α : Type u_1) (β : Type u_2) [inst : Unifor
mSpace β] (f : UniformFun α β),   (nhds f).HasBasis (fun V => V ∈ uniformity β) 
fun V => {g | …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Filter.HasBasis.equicontinuousWithinAt_iff_left {p : κ → Prop} {s : κ → Set X}
    {F : ι → X → α} {S : Set X} {x₀ : X} (hX : (𝓝[S] x₀).HasBasis p s) :
    EquicontinuousWithinAt F S x₀ ↔ ∀ U ∈ 𝓤 α, ∃ k, p k ∧ ∀ x ∈ s k, ∀ i, (F i x₀, F i x) ∈ U := by
  rw [equicontinuousWithinAt_iff_continuousWithinAt, ContinuousWithinAt,
    hX.tendsto_iff (UniformFun.hasBasis_nhds ι α _)]
  rfl
/-
**Filter.HasBasis.equicontinuousAt_iff_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.equicontinuousAt_iff_right {p : κ -> Prop} {s : κ -> Set (
α × α)} {F : ι -> X -> α} {x₀ : X} (hα : (𝓤 α).HasBasis p s) : EquicontinuousAt 
F x₀ ↔ forall k, p k -> forallᶠ x in 𝓝 x₀, forall i, (F i x₀, F i x) in s k
参数：α × α；hα : (𝓤 α).HasBasis p s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `equicontinuousAt_iff_continuousAt`：equicontinuousAt_iff_continuousAt {F 
: ι -> X -> α} {x₀ : X} : EquicontinuousAt F x₀ ↔ ContinuousAt (ofFun ∘ Function
.swap F : X -> ι ->ᵤ α)…
· 使用定理 `ContinuousAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (x : X),   ContinuousAt f x = F
ilter.T…
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `UniformFun.hasBasis_nhds_of_basis`：∀ (α : Type u_1) (β : Type u_2) {ι : 
Type u_4} [inst : UniformSpace β] (f : UniformFun α β) {p : ι → Prop}   {s : ι →
 Set (β × β)},   (unifo…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Filter.HasBasis.equicontinuousAt_iff_right {p : κ → Prop} {s : κ → Set (α × α)}
    {F : ι → X → α} {x₀ : X} (hα : (𝓤 α).HasBasis p s) :
    EquicontinuousAt F x₀ ↔ ∀ k, p k → ∀ᶠ x in 𝓝 x₀, ∀ i, (F i x₀, F i x) ∈ s k := by
  rw [equicontinuousAt_iff_continuousAt, ContinuousAt,
    (UniformFun.hasBasis_nhds_of_basis ι α _ hα).tendsto_right_iff]
  rfl
/-
**Filter.HasBasis.equicontinuousWithinAt_iff_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.equicontinuousWithinAt_iff_right {p : κ -> Prop} {s : κ ->
 Set (α × α)} {F : ι -> X -> α} {S : Set X} {x₀ : X} (hα : (𝓤 α).HasBasis p s) :
 EquicontinuousWithinAt F S x₀ ↔ forall k, p k -> forallᶠ x in 𝓝[S] x₀, forall i
, (F i x₀, F i x) in s k
参数：α × α；hα : (𝓤 α).HasBasis p s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `equicontinuousWithinAt_iff_continuousWithinAt`：equicontinuousWithinAt_if
f_continuousWithinAt {F : ι -> X -> α} {S : Set X} {x₀ : X} : EquicontinuousWith
inAt F S x₀ ↔ ContinuousWithinAt (o…
· 使用定理 `ContinuousWithinAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (s : Set X)   (x : X), Co
ntinuousWithi…
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `UniformFun.hasBasis_nhds_of_basis`：∀ (α : Type u_1) (β : Type u_2) {ι : 
Type u_4} [inst : UniformSpace β] (f : UniformFun α β) {p : ι → Prop}   {s : ι →
 Set (β × β)},   (unifo…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Filter.HasBasis.equicontinuousWithinAt_iff_right {p : κ → Prop}
    {s : κ → Set (α × α)} {F : ι → X → α} {S : Set X} {x₀ : X} (hα : (𝓤 α).HasBasis p s) :
    EquicontinuousWithinAt F S x₀ ↔ ∀ k, p k → ∀ᶠ x in 𝓝[S] x₀, ∀ i, (F i x₀, F i x) ∈ s k := by
  rw [equicontinuousWithinAt_iff_continuousWithinAt, ContinuousWithinAt,
    (UniformFun.hasBasis_nhds_of_basis ι α _ hα).tendsto_right_iff]
  rfl
/-
**Filter.HasBasis.equicontinuousAt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.equicontinuousAt_iff {κ₁ κ₂ : Type*} {p₁ : κ₁ -> Prop} {s₁
 : κ₁ -> Set X} {p₂ : κ₂ -> Prop} {s₂ : κ₂ -> Set (α × α)} {F : ι -> X -> α} {x₀
 : X} (hX : (𝓝 x₀).HasBasis p₁ s₁) (hα : (𝓤 α).HasBasis p₂ s₂) : EquicontinuousA
t F x₀ ↔ forall k₂, p₂ k₂ -> exists k₁, p₁ k₁ ∧ forall x in s₁ k₁, forall i, (F 
i x₀, F i x) in s₂ k₂
参数：α × α；hX : (𝓝 x₀).HasBasis p₁ s₁；hα : (𝓤 α).HasBasis p₂ s₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `equicontinuousAt_iff_continuousAt`：equicontinuousAt_iff_continuousAt {F 
: ι -> X -> α} {x₀ : X} : EquicontinuousAt F x₀ ↔ ContinuousAt (ofFun ∘ Function
.swap F : X -> ι ->ᵤ α)…
· 使用定理 `ContinuousAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (x : X),   ContinuousAt f x = F
ilter.T…
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `UniformFun.hasBasis_nhds_of_basis`：∀ (α : Type u_1) (β : Type u_2) {ι : 
Type u_4} [inst : UniformSpace β] (f : UniformFun α β) {p : ι → Prop}   {s : ι →
 Set (β × β)},   (unifo…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Filter.HasBasis.equicontinuousAt_iff {κ₁ κ₂ : Type*} {p₁ : κ₁ → Prop} {s₁ : κ₁ → Set X}
    {p₂ : κ₂ → Prop} {s₂ : κ₂ → Set (α × α)} {F : ι → X → α} {x₀ : X} (hX : (𝓝 x₀).HasBasis p₁ s₁)
    (hα : (𝓤 α).HasBasis p₂ s₂) :
    EquicontinuousAt F x₀ ↔
      ∀ k₂, p₂ k₂ → ∃ k₁, p₁ k₁ ∧ ∀ x ∈ s₁ k₁, ∀ i, (F i x₀, F i x) ∈ s₂ k₂ := by
  rw [equicontinuousAt_iff_continuousAt, ContinuousAt,
    hX.tendsto_iff (UniformFun.hasBasis_nhds_of_basis ι α _ hα)]
  rfl
/-
**Filter.HasBasis.equicontinuousWithinAt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.equicontinuousWithinAt_iff {κ₁ κ₂ : Type*} {p₁ : κ₁ -> Pro
p} {s₁ : κ₁ -> Set X} {p₂ : κ₂ -> Prop} {s₂ : κ₂ -> Set (α × α)} {F : ι -> X -> 
α} {S : Set X} {x₀ : X} (hX : (𝓝[S] x₀).HasBasis p₁ s₁) (hα : (𝓤 α).HasBasis p₂ 
s₂) : EquicontinuousWithinAt F S x₀ ↔ forall k₂, p₂ k₂ -> exists k₁, p₁ k₁ ∧ for
all x in s₁ k₁, forall i, (F i x₀, F i x) in s₂ k₂
参数：α × α；hX : (𝓝[S] x₀).HasBasis p₁ s₁；hα : (𝓤 α).HasBasis p₂ s₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `equicontinuousWithinAt_iff_continuousWithinAt`：equicontinuousWithinAt_if
f_continuousWithinAt {F : ι -> X -> α} {S : Set X} {x₀ : X} : EquicontinuousWith
inAt F S x₀ ↔ ContinuousWithinAt (o…
· 使用定理 `ContinuousWithinAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (s : Set X)   (x : X), Co
ntinuousWithi…
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `UniformFun.hasBasis_nhds_of_basis`：∀ (α : Type u_1) (β : Type u_2) {ι : 
Type u_4} [inst : UniformSpace β] (f : UniformFun α β) {p : ι → Prop}   {s : ι →
 Set (β × β)},   (unifo…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Filter.HasBasis.equicontinuousWithinAt_iff {κ₁ κ₂ : Type*} {p₁ : κ₁ → Prop}
    {s₁ : κ₁ → Set X} {p₂ : κ₂ → Prop} {s₂ : κ₂ → Set (α × α)} {F : ι → X → α} {S : Set X} {x₀ : X}
    (hX : (𝓝[S] x₀).HasBasis p₁ s₁) (hα : (𝓤 α).HasBasis p₂ s₂) :
    EquicontinuousWithinAt F S x₀ ↔
      ∀ k₂, p₂ k₂ → ∃ k₁, p₁ k₁ ∧ ∀ x ∈ s₁ k₁, ∀ i, (F i x₀, F i x) ∈ s₂ k₂ := by
  rw [equicontinuousWithinAt_iff_continuousWithinAt, ContinuousWithinAt,
    hX.tendsto_iff (UniformFun.hasBasis_nhds_of_basis ι α _ hα)]
  rfl
/-
**Filter.HasBasis.uniformEquicontinuous_iff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.uniformEquicontinuous_iff_left {p : κ -> Prop} {s : κ -> S
et (β × β)} {F : ι -> β -> α} (hβ : (𝓤 β).HasBasis p s) : UniformEquicontinuous 
F ↔ forall U in 𝓤 α, exists k, p k ∧ forall x y, (x, y) in s k -> forall i, (F i
 x, F i y) in U
参数：β × β；hβ : (𝓤 β).HasBasis p s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `uniformEquicontinuous_iff_uniformContinuous`：uniformEquicontinuous_iff_u
niformContinuous {F : ι -> β -> α} : UniformEquicontinuous F ↔ UniformContinuous
 (ofFun ∘ Function.swap F : β -> …
· 使用定理 `UniformContinuous.eq_1`：∀ {α : Type ua} {β : Type ub} [inst : UniformSpa
ce α] [inst_1 : UniformSpace β] (f : α → β),   UniformContinuous f = Filter.Tend
sto (fun x =…
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `UniformFun.hasBasis_uniformity`：∀ (α : Type u_1) (β : Type u_2) [inst : 
UniformSpace β],   (uniformity (UniformFun α β)).HasBasis (fun x => x ∈ uniformi
ty β) (UniformFun.ge…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Filter.HasBasis.uniformEquicontinuous_iff_left {p : κ → Prop}
    {s : κ → Set (β × β)} {F : ι → β → α} (hβ : (𝓤 β).HasBasis p s) :
    UniformEquicontinuous F ↔
      ∀ U ∈ 𝓤 α, ∃ k, p k ∧ ∀ x y, (x, y) ∈ s k → ∀ i, (F i x, F i y) ∈ U := by
  rw [uniformEquicontinuous_iff_uniformContinuous, UniformContinuous,
    hβ.tendsto_iff (UniformFun.hasBasis_uniformity ι α)]
  simp only [Prod.forall]
  rfl
/-
**Filter.HasBasis.uniformEquicontinuousOn_iff_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.uniformEquicontinuousOn_iff_left {p : κ -> Prop} {s : κ ->
 Set (β × β)} {F : ι -> β -> α} {S : Set β} (hβ : (𝓤 β ⊓ 𝓟 (S ×ˢ S)).HasBasis p 
s) : UniformEquicontinuousOn F S ↔ forall U in 𝓤 α, exists k, p k ∧ forall x y, 
(x, y) in s k -> forall i, (F i x, F i y) in U
参数：β × β；hβ : (𝓤 β ⊓ 𝓟 (S ×ˢ S)).HasBasis p s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `uniformEquicontinuousOn_iff_uniformContinuousOn`：uniformEquicontinuousOn
_iff_uniformContinuousOn {F : ι -> β -> α} {S : Set β} : UniformEquicontinuousOn
 F S ↔ UniformContinuousOn (ofFun ∘ F…
· 使用定理 `UniformContinuousOn.eq_1`：∀ {α : Type ua} {β : Type ub} [inst : UniformS
pace α] [inst_1 : UniformSpace β] (f : α → β) (s : Set α),   UniformContinuousOn
 f s =     Fil…
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `UniformFun.hasBasis_uniformity`：∀ (α : Type u_1) (β : Type u_2) [inst : 
UniformSpace β],   (uniformity (UniformFun α β)).HasBasis (fun x => x ∈ uniformi
ty β) (UniformFun.ge…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Filter.HasBasis.uniformEquicontinuousOn_iff_left {p : κ → Prop}
    {s : κ → Set (β × β)} {F : ι → β → α} {S : Set β} (hβ : (𝓤 β ⊓ 𝓟 (S ×ˢ S)).HasBasis p s) :
    UniformEquicontinuousOn F S ↔
      ∀ U ∈ 𝓤 α, ∃ k, p k ∧ ∀ x y, (x, y) ∈ s k → ∀ i, (F i x, F i y) ∈ U := by
  rw [uniformEquicontinuousOn_iff_uniformContinuousOn, UniformContinuousOn,
    hβ.tendsto_iff (UniformFun.hasBasis_uniformity ι α)]
  simp only [Prod.forall]
  rfl
/-
**Filter.HasBasis.uniformEquicontinuous_iff_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.uniformEquicontinuous_iff_right {p : κ -> Prop} {s : κ -> 
Set (α × α)} {F : ι -> β -> α} (hα : (𝓤 α).HasBasis p s) : UniformEquicontinuous
 F ↔ forall k, p k -> forallᶠ xy : β × β in 𝓤 β, forall i, (F i xy.1, F i xy.2) 
in s k
参数：α × α；hα : (𝓤 α).HasBasis p s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `uniformEquicontinuous_iff_uniformContinuous`：uniformEquicontinuous_iff_u
niformContinuous {F : ι -> β -> α} : UniformEquicontinuous F ↔ UniformContinuous
 (ofFun ∘ Function.swap F : β -> …
· 使用定理 `UniformContinuous.eq_1`：∀ {α : Type ua} {β : Type ub} [inst : UniformSpa
ce α] [inst_1 : UniformSpace β] (f : α → β),   UniformContinuous f = Filter.Tend
sto (fun x =…
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `UniformFun.hasBasis_uniformity_of_basis`：∀ (α : Type u_1) (β : Type u_2)
 [inst : UniformSpace β] {ι : Sort u_5} {p : ι → Prop} {s : ι → Set (β × β)},   
(uniformity β).HasBasis p s →…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Filter.HasBasis.uniformEquicontinuous_iff_right {p : κ → Prop}
    {s : κ → Set (α × α)} {F : ι → β → α} (hα : (𝓤 α).HasBasis p s) :
    UniformEquicontinuous F ↔ ∀ k, p k → ∀ᶠ xy : β × β in 𝓤 β, ∀ i, (F i xy.1, F i xy.2) ∈ s k := by
  rw [uniformEquicontinuous_iff_uniformContinuous, UniformContinuous,
    (UniformFun.hasBasis_uniformity_of_basis ι α hα).tendsto_right_iff]
  rfl
/-
**Filter.HasBasis.uniformEquicontinuousOn_iff_right** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：Filter.HasBasis.uniformEquicontinuousOn_iff_right {p : κ -> Prop} {s : κ -
> Set (α × α)} {F : ι -> β -> α} {S : Set β} (hα : (𝓤 α).HasBasis p s) : Uniform
EquicontinuousOn F S ↔ forall k, p k -> forallᶠ xy : β × β in 𝓤 β ⊓ 𝓟 (S ×ˢ S), 
forall i, (F i xy.1, F i xy.2) in s k
参数：α × α；hα : (𝓤 α).HasBasis p s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `uniformEquicontinuousOn_iff_uniformContinuousOn`：uniformEquicontinuousOn
_iff_uniformContinuousOn {F : ι -> β -> α} {S : Set β} : UniformEquicontinuousOn
 F S ↔ UniformContinuousOn (ofFun ∘ F…
· 使用定理 `UniformContinuousOn.eq_1`：∀ {α : Type ua} {β : Type ub} [inst : UniformS
pace α] [inst_1 : UniformSpace β] (f : α → β) (s : Set α),   UniformContinuousOn
 f s =     Fil…
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `UniformFun.hasBasis_uniformity_of_basis`：∀ (α : Type u_1) (β : Type u_2)
 [inst : UniformSpace β] {ι : Sort u_5} {p : ι → Prop} {s : ι → Set (β × β)},   
(uniformity β).HasBasis p s →…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Filter.HasBasis.uniformEquicontinuousOn_iff_right {p : κ → Prop}
    {s : κ → Set (α × α)} {F : ι → β → α} {S : Set β} (hα : (𝓤 α).HasBasis p s) :
    UniformEquicontinuousOn F S ↔
      ∀ k, p k → ∀ᶠ xy : β × β in 𝓤 β ⊓ 𝓟 (S ×ˢ S), ∀ i, (F i xy.1, F i xy.2) ∈ s k := by
  rw [uniformEquicontinuousOn_iff_uniformContinuousOn, UniformContinuousOn,
    (UniformFun.hasBasis_uniformity_of_basis ι α hα).tendsto_right_iff]
  rfl
/-
**Filter.HasBasis.uniformEquicontinuous_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.uniformEquicontinuous_iff {κ₁ κ₂ : Type*} {p₁ : κ₁ -> Prop
} {s₁ : κ₁ -> Set (β × β)} {p₂ : κ₂ -> Prop} {s₂ : κ₂ -> Set (α × α)} {F : ι -> 
β -> α} (hβ : (𝓤 β).HasBasis p₁ s₁) (hα : (𝓤 α).HasBasis p₂ s₂) : UniformEquicon
tinuous F ↔ forall k₂, p₂ k₂ -> exists k₁, p₁ k₁ ∧ forall x y, (x, y) in s₁ k₁ -
> forall i, (F i x, F i y) in s₂ k₂
参数：β × β；α × α；hβ : (𝓤 β).HasBasis p₁ s₁；hα : (𝓤 α).HasBasis p₂ s₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `uniformEquicontinuous_iff_uniformContinuous`：uniformEquicontinuous_iff_u
niformContinuous {F : ι -> β -> α} : UniformEquicontinuous F ↔ UniformContinuous
 (ofFun ∘ Function.swap F : β -> …
· 使用定理 `UniformContinuous.eq_1`：∀ {α : Type ua} {β : Type ub} [inst : UniformSpa
ce α] [inst_1 : UniformSpace β] (f : α → β),   UniformContinuous f = Filter.Tend
sto (fun x =…
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `UniformFun.hasBasis_uniformity_of_basis`：∀ (α : Type u_1) (β : Type u_2)
 [inst : UniformSpace β] {ι : Sort u_5} {p : ι → Prop} {s : ι → Set (β × β)},   
(uniformity β).HasBasis p s →…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Filter.HasBasis.uniformEquicontinuous_iff {κ₁ κ₂ : Type*} {p₁ : κ₁ → Prop}
    {s₁ : κ₁ → Set (β × β)} {p₂ : κ₂ → Prop} {s₂ : κ₂ → Set (α × α)} {F : ι → β → α}
    (hβ : (𝓤 β).HasBasis p₁ s₁) (hα : (𝓤 α).HasBasis p₂ s₂) :
    UniformEquicontinuous F ↔
      ∀ k₂, p₂ k₂ → ∃ k₁, p₁ k₁ ∧ ∀ x y, (x, y) ∈ s₁ k₁ → ∀ i, (F i x, F i y) ∈ s₂ k₂ := by
  rw [uniformEquicontinuous_iff_uniformContinuous, UniformContinuous,
    hβ.tendsto_iff (UniformFun.hasBasis_uniformity_of_basis ι α hα)]
  simp only [Prod.forall]
  rfl
/-
**Filter.HasBasis.uniformEquicontinuousOn_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.HasBasis.uniformEquicontinuousOn_iff {κ₁ κ₂ : Type*} {p₁ : κ₁ -> Pr
op} {s₁ : κ₁ -> Set (β × β)} {p₂ : κ₂ -> Prop} {s₂ : κ₂ -> Set (α × α)} {F : ι -
> β -> α} {S : Set β} (hβ : (𝓤 β ⊓ 𝓟 (S ×ˢ S)).HasBasis p₁ s₁) (hα : (𝓤 α).HasBa
sis p₂ s₂) : UniformEquicontinuousOn F S ↔ forall k₂, p₂ k₂ -> exists k₁, p₁ k₁ 
∧ forall x y, (x, y) in s₁ k₁ -> forall i, (F i x, F i y) in s₂ k₂
参数：β × β；α × α；hβ : (𝓤 β ⊓ 𝓟 (S ×ˢ S)).HasBasis p₁ s₁；hα : (𝓤 α).HasBasis p₂ s₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `uniformEquicontinuousOn_iff_uniformContinuousOn`：uniformEquicontinuousOn
_iff_uniformContinuousOn {F : ι -> β -> α} {S : Set β} : UniformEquicontinuousOn
 F S ↔ UniformContinuousOn (ofFun ∘ F…
· 使用定理 `UniformContinuousOn.eq_1`：∀ {α : Type ua} {β : Type ub} [inst : UniformS
pace α] [inst_1 : UniformSpace β] (f : α → β) (s : Set α),   UniformContinuousOn
 f s =     Fil…
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `UniformFun.hasBasis_uniformity_of_basis`：∀ (α : Type u_1) (β : Type u_2)
 [inst : UniformSpace β] {ι : Sort u_5} {p : ι → Prop} {s : ι → Set (β × β)},   
(uniformity β).HasBasis p s →…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Filter.HasBasis.uniformEquicontinuousOn_iff {κ₁ κ₂ : Type*} {p₁ : κ₁ → Prop}
    {s₁ : κ₁ → Set (β × β)} {p₂ : κ₂ → Prop} {s₂ : κ₂ → Set (α × α)} {F : ι → β → α}
    {S : Set β} (hβ : (𝓤 β ⊓ 𝓟 (S ×ˢ S)).HasBasis p₁ s₁) (hα : (𝓤 α).HasBasis p₂ s₂) :
    UniformEquicontinuousOn F S ↔
      ∀ k₂, p₂ k₂ → ∃ k₁, p₁ k₁ ∧ ∀ x y, (x, y) ∈ s₁ k₁ → ∀ i, (F i x, F i y) ∈ s₂ k₂ := by
  rw [uniformEquicontinuousOn_iff_uniformContinuousOn, UniformContinuousOn,
    hβ.tendsto_iff (UniformFun.hasBasis_uniformity_of_basis ι α hα)]
  simp only [Prod.forall]
  rfl

/-- Given `u : α → β` a uniform inducing map, a family `𝓕 : ι → X → α` is equicontinuous at a point
`x₀ : X` iff the family `𝓕'`, obtained by composing each function of `𝓕` by `u`, is
equicontinuous at `x₀`. -/
/-
**IsUniformInducing.equicontinuousAt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUniformInducing.equicontinuousAt_iff {F : ι -> X -> α} {x₀ : X} {u : α -
> β} (hu : IsUniformInducing u) : EquicontinuousAt F x₀ ↔ EquicontinuousAt ((u ∘
 ·) ∘ F) x₀
参数：hu : IsUniformInducing u。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformInducing.isInducing`：IsUniformInducing.isInducing {f : α -> β} 
(h : IsUniformInducing f) : IsInducing f
· 使用引理 `UniformFun.postcomp_isUniformInducing`：postcomp_isUniformInducing [Unifo
rmSpace γ] {f : γ -> β} (hf : IsUniformInducing f) : IsUniformInducing (ofFun ∘ 
(f ∘ ·) ∘ toFun : (α ->ᵤ γ)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `equicontinuousAt_iff_continuousAt`：equicontinuousAt_iff_continuousAt {F 
: ι -> X -> α} {x₀ : X} : EquicontinuousAt F x₀ ↔ ContinuousAt (ofFun ∘ Function
.swap F : X -> ι ->ᵤ α)…
· 使用引理 `Topology.IsInducing.continuousAt_iff`：continuousAt_iff (hg : IsInducing 
g) {x : X} : ContinuousAt f x ↔ ContinuousAt (g ∘ f) x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Given `u : α → β` a uniform inducing map, a family `𝓕 : ι → X → α` is equicontin
uous at a point
`x₀ : X` iff the family `𝓕'`, obtained by composing each function of `𝓕` by `u`,
 is
equicontinuous at `x₀`.
-/
theorem IsUniformInducing.equicontinuousAt_iff {F : ι → X → α} {x₀ : X} {u : α → β}
    (hu : IsUniformInducing u) : EquicontinuousAt F x₀ ↔ EquicontinuousAt ((u ∘ ·) ∘ F) x₀ := by
  have := (UniformFun.postcomp_isUniformInducing (α := ι) hu).isInducing
  rw [equicontinuousAt_iff_continuousAt, equicontinuousAt_iff_continuousAt, this.continuousAt_iff]
  rfl

/-- Given `u : α → β` a uniform inducing map, a family `𝓕 : ι → X → α` is equicontinuous at a point
`x₀ : X` within a subset `S : Set X` iff the family `𝓕'`, obtained by composing each function
of `𝓕` by `u`, is equicontinuous at `x₀` within `S`. -/
/-
**IsUniformInducing.equicontinuousWithinAt_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsUniformInducing.equicontinuousWithinAt_iff {F : ι -> X -> α} {S : Set X}
 {x₀ : X} {u : α -> β} (hu : IsUniformInducing u) : EquicontinuousWithinAt F S x
₀ ↔ EquicontinuousWithinAt ((u ∘ ·) ∘ F) S x₀
参数：hu : IsUniformInducing u。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformInducing.isInducing`：IsUniformInducing.isInducing {f : α -> β} 
(h : IsUniformInducing f) : IsInducing f
· 使用引理 `UniformFun.postcomp_isUniformInducing`：postcomp_isUniformInducing [Unifo
rmSpace γ] {f : γ -> β} (hf : IsUniformInducing f) : IsUniformInducing (ofFun ∘ 
(f ∘ ·) ∘ toFun : (α ->ᵤ γ)…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Topology.IsInducing.continuousWithinAt_iff`：Topology.IsInducing.continuo
usWithinAt_iff {f : α -> β} {g : β -> γ} (hg : IsInducing g) {s : Set α} {x : α}
 : ContinuousWithinAt f s x ↔ Co…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Given `u : α → β` a uniform inducing map, a family `𝓕 : ι → X → α` is equicontin
uous at a point
`x₀ : X` within a subset `S : Set X` iff the family `𝓕'`, obtained by composing 
each function
of `𝓕` by `u`, is equicontinuous at `x₀` within `S`.
-/
lemma IsUniformInducing.equicontinuousWithinAt_iff {F : ι → X → α} {S : Set X} {x₀ : X} {u : α → β}
    (hu : IsUniformInducing u) : EquicontinuousWithinAt F S x₀ ↔
      EquicontinuousWithinAt ((u ∘ ·) ∘ F) S x₀ := by
  have := (UniformFun.postcomp_isUniformInducing (α := ι) hu).isInducing
  simp only [equicontinuousWithinAt_iff_continuousWithinAt, this.continuousWithinAt_iff]
  rfl

/-- Given `u : α → β` a uniform inducing map, a family `𝓕 : ι → X → α` is equicontinuous iff the
family `𝓕'`, obtained by composing each function of `𝓕` by `u`, is equicontinuous. -/
/-
**IsUniformInducing.equicontinuous_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsUniformInducing.equicontinuous_iff {F : ι -> X -> α} {u : α -> β} (hu : 
IsUniformInducing u) : Equicontinuous F ↔ Equicontinuous ((u ∘ ·) ∘ F)
参数：hu : IsUniformInducing u。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsUniformInducing.equicontinuousAt_iff`：IsUniformInducing.equicontinuous
At_iff {F : ι -> X -> α} {x₀ : X} {u : α -> β} (hu : IsUniformInducing u) : Equi
continuousAt F x₀ ↔ Equicont…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Given `u : α → β` a uniform inducing map, a family `𝓕 : ι → X → α` is equicontin
uous iff the
family `𝓕'`, obtained by composing each function of `𝓕` by `u`, is equicontinuou
s.
-/
lemma IsUniformInducing.equicontinuous_iff {F : ι → X → α} {u : α → β} (hu : IsUniformInducing u) :
    Equicontinuous F ↔ Equicontinuous ((u ∘ ·) ∘ F) := by
  congrm ∀ x, ?_
  rw [hu.equicontinuousAt_iff]

/-- Given `u : α → β` a uniform inducing map, a family `𝓕 : ι → X → α` is equicontinuous on a
subset `S : Set X` iff the family `𝓕'`, obtained by composing each function of `𝓕` by `u`, is
equicontinuous on `S`. -/
/-
**IsUniformInducing.equicontinuousOn_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUniformInducing.equicontinuousOn_iff {F : ι -> X -> α} {S : Set X} {u : 
α -> β} (hu : IsUniformInducing u) : EquicontinuousOn F S ↔ EquicontinuousOn ((u
 ∘ ·) ∘ F) S
参数：hu : IsUniformInducing u。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsUniformInducing.equicontinuousWithinAt_iff`：IsUniformInducing.equicont
inuousWithinAt_iff {F : ι -> X -> α} {S : Set X} {x₀ : X} {u : α -> β} (hu : IsU
niformInducing u) : Equicontinuous…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Given `u : α → β` a uniform inducing map, a family `𝓕 : ι → X → α` is equicontin
uous on a
subset `S : Set X` iff the family `𝓕'`, obtained by composing each function of `
𝓕` by `u`, is
equicontinuous on `S`.
-/
theorem IsUniformInducing.equicontinuousOn_iff {F : ι → X → α} {S : Set X} {u : α → β}
    (hu : IsUniformInducing u) : EquicontinuousOn F S ↔ EquicontinuousOn ((u ∘ ·) ∘ F) S := by
  congrm ∀ x ∈ S, ?_
  rw [hu.equicontinuousWithinAt_iff]

/-- Given `u : α → γ` a uniform inducing map, a family `𝓕 : ι → β → α` is uniformly equicontinuous
iff the family `𝓕'`, obtained by composing each function of `𝓕` by `u`, is uniformly
equicontinuous. -/
/-
**IsUniformInducing.uniformEquicontinuous_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUniformInducing.uniformEquicontinuous_iff {F : ι -> β -> α} {u : α -> γ}
 (hu : IsUniformInducing u) : UniformEquicontinuous F ↔ UniformEquicontinuous ((
u ∘ ·) ∘ F)
参数：hu : IsUniformInducing u。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `UniformFun.postcomp_isUniformInducing`：postcomp_isUniformInducing [Unifo
rmSpace γ] {f : γ -> β} (hf : IsUniformInducing f) : IsUniformInducing (ofFun ∘ 
(f ∘ ·) ∘ toFun : (α ->ᵤ γ)…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsUniformInducing.uniformContinuous_iff`：IsUniformInducing.uniformContin
uous_iff {f : α -> β} {g : β -> γ} (hg : IsUniformInducing g) : UniformContinuou
s f ↔ UniformContinuous (g ∘ …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Given `u : α → γ` a uniform inducing map, a family `𝓕 : ι → β → α` is uniformly 
equicontinuous
iff the family `𝓕'`, obtained by composing each function of `𝓕` by `u`, is unifo
rmly
equicontinuous.
-/
theorem IsUniformInducing.uniformEquicontinuous_iff {F : ι → β → α} {u : α → γ}
    (hu : IsUniformInducing u) : UniformEquicontinuous F ↔ UniformEquicontinuous ((u ∘ ·) ∘ F) := by
  have := UniformFun.postcomp_isUniformInducing (α := ι) hu
  simp only [uniformEquicontinuous_iff_uniformContinuous, this.uniformContinuous_iff]
  rfl

/-- Given `u : α → γ` a uniform inducing map, a family `𝓕 : ι → β → α` is uniformly equicontinuous
on a subset `S : Set β` iff the family `𝓕'`, obtained by composing each function of `𝓕` by `u`,
is uniformly equicontinuous on `S`. -/
/-
**IsUniformInducing.uniformEquicontinuousOn_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUniformInducing.uniformEquicontinuousOn_iff {F : ι -> β -> α} {S : Set β
} {u : α -> γ} (hu : IsUniformInducing u) : UniformEquicontinuousOn F S ↔ Unifor
mEquicontinuousOn ((u ∘ ·) ∘ F) S
参数：hu : IsUniformInducing u。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `UniformFun.postcomp_isUniformInducing`：postcomp_isUniformInducing [Unifo
rmSpace γ] {f : γ -> β} (hf : IsUniformInducing f) : IsUniformInducing (ofFun ∘ 
(f ∘ ·) ∘ toFun : (α ->ᵤ γ)…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsUniformInducing.uniformContinuousOn_iff`：IsUniformInducing.uniformCont
inuousOn_iff {f : α -> β} {g : β -> γ} {S : Set α} (hg : IsUniformInducing g) : 
UniformContinuousOn f S ↔ Unifo…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Given `u : α → γ` a uniform inducing map, a family `𝓕 : ι → β → α` is uniformly 
equicontinuous
on a subset `S : Set β` iff the family `𝓕'`, obtained by composing each function
 of `𝓕` by `u`,
is uniformly equicontinuous on `S`.
-/
theorem IsUniformInducing.uniformEquicontinuousOn_iff {F : ι → β → α} {S : Set β} {u : α → γ}
    (hu : IsUniformInducing u) :
    UniformEquicontinuousOn F S ↔ UniformEquicontinuousOn ((u ∘ ·) ∘ F) S := by
  have := UniformFun.postcomp_isUniformInducing (α := ι) hu
  simp only [uniformEquicontinuousOn_iff_uniformContinuousOn, this.uniformContinuousOn_iff]
  rfl

/-- If a set of functions is equicontinuous at some `x₀` within a set `S`, the same is true for its
closure in *any* topology for which evaluation at any `x ∈ S ∪ {x₀}` is continuous. Since
this will be applied to `DFunLike` types, we state it for any topological space with a map
to `X → α` satisfying the right continuity conditions. See also `Set.EquicontinuousWithinAt.closure`
for a more familiar (but weaker) statement.

Note: This could *technically* be called `EquicontinuousWithinAt.closure` without name clashes
with `Set.EquicontinuousWithinAt.closure`, but we don't do it because, even with a `protected`
marker, it would introduce ambiguities while working in namespace `Set` (e.g, in the proof of
any theorem called `Set.something`). -/
/-
**EquicontinuousWithinAt.closure'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EquicontinuousWithinAt.closure' {A : Set Y} {u : Y -> X -> α} {S : Set X} 
{x₀ : X} (hA : EquicontinuousWithinAt (u ∘ (↑) : A -> X -> α) S x₀) (hu₁ : Conti
nuous (S.domRestrict ∘ u)) (hu₂ : Continuous (eval x₀ ∘ u)) : EquicontinuousWith
inAt (u ∘ (↑) : closure A -> X -> α) S x₀
参数：hA : EquicontinuousWithinAt (u ∘ (↑) : A -> X -> α) S x₀；hu₁ : Continuous (S.
domRestrict ∘ u)；hu₂ : Continuous (eval x₀ ∘ u)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_uniformity_isClosed`：mem_uniformity_isClosed {s : SetRel α α} (h : s
 in 𝓤 α) : exists t in 𝓤 α, IsClosed t ∧ t subseteq s
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `eventually_mem_nhdsWithin`：eventually_mem_nhdsWithin {a : α} {s : Set α}
 : forallᶠ x in 𝓝[s] a, x in s
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetCoe.forall`：SetCoe.forall {s : Set α} {p : s -> Prop} : (forall x : s
, p x) ↔ forall (x) (h : x in s), p ⟨x, h⟩
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t

--- 原说明 ---
If a set of functions is equicontinuous at some `x₀` within a set `S`, the same 
is true for its
closure in *any* topology for which evaluation at any `x ∈ S ∪ {x₀}` is continuo
us. Since
this will be applied to `DFunLike` types, we state it for any topological space 
with a map
to `X → α` satisfying the right continuity conditions. See also `Set.Equicontinu
ousWithinAt.closure`
for a more familiar (but weaker) statement.

Note: This could *technically* be called `EquicontinuousWithinAt.closure` withou
t name clashes
with `Set.EquicontinuousWithinAt.closure`, but we don't do it because, even with
 a `protected`
marker, it would introduce ambiguities while working in namespace `Set` (e.g, in
 the proof of
any theorem called `Set.something`).
-/
theorem EquicontinuousWithinAt.closure' {A : Set Y} {u : Y → X → α} {S : Set X} {x₀ : X}
    (hA : EquicontinuousWithinAt (u ∘ (↑) : A → X → α) S x₀) (hu₁ : Continuous (S.domRestrict ∘ u))
    (hu₂ : Continuous (eval x₀ ∘ u)) :
    EquicontinuousWithinAt (u ∘ (↑) : closure A → X → α) S x₀ := by
  intro U hU
  rcases mem_uniformity_isClosed hU with ⟨V, hV, hVclosed, hVU⟩
  filter_upwards [hA V hV, eventually_mem_nhdsWithin] with x hx hxS
  rw [SetCoe.forall] at *
  change A ⊆ (fun f => (u f x₀, u f x)) ⁻¹' V at hx
  refine (closure_minimal hx <| hVclosed.preimage <| hu₂.prodMk ?_).trans (preimage_mono hVU)
  exact (continuous_apply ⟨x, hxS⟩).comp hu₁

/-- If a set of functions is equicontinuous at some `x₀`, the same is true for its closure in *any*
topology for which evaluation at any point is continuous. Since this will be applied to
`DFunLike` types, we state it for any topological space with a map to `X → α` satisfying the right
continuity conditions. See also `Set.EquicontinuousAt.closure` for a more familiar statement. -/
/-
**EquicontinuousAt.closure'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EquicontinuousAt.closure' {A : Set Y} {u : Y -> X -> α} {x₀ : X} (hA : Equ
icontinuousAt (u ∘ (↑) : A -> X -> α) x₀) (hu : Continuous u) : EquicontinuousAt
 (u ∘ (↑) : closure A -> X -> α) x₀
参数：hA : EquicontinuousAt (u ∘ (↑) : A -> X -> α) x₀；hu : Continuous u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `equicontinuousWithinAt_univ`：∀ {ι : Type u_1} {X : Type u_3} {α : Type u
_6} [tX : TopologicalSpace X] [uα : UniformSpace α] (F : ι → X → α) (x₀ : X),   
EquicontinuousWit…
· 使用定理 `EquicontinuousWithinAt.closure'`：EquicontinuousWithinAt.closure' {A : Se
t Y} {u : Y -> X -> α} {S : Set X} {x₀ : X} (hA : EquicontinuousWithinAt (u ∘ (↑
) : A -> X -> α) S x₀…
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用引理 `Pi.continuous_domRestrict`：Pi.continuous_domRestrict (S : Set ι) : Conti
nuous (S.domRestrict : (forall i : ι, A i) -> (forall i : S, A i))
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)

--- 原说明 ---
If a set of functions is equicontinuous at some `x₀`, the same is true for its c
losure in *any*
topology for which evaluation at any point is continuous. Since this will be app
lied to
`DFunLike` types, we state it for any topological space with a map to `X → α` sa
tisfying the right
continuity conditions. See also `Set.EquicontinuousAt.closure` for a more famili
ar statement.
-/
theorem EquicontinuousAt.closure' {A : Set Y} {u : Y → X → α} {x₀ : X}
    (hA : EquicontinuousAt (u ∘ (↑) : A → X → α) x₀) (hu : Continuous u) :
    EquicontinuousAt (u ∘ (↑) : closure A → X → α) x₀ := by
  rw [← equicontinuousWithinAt_univ] at hA ⊢
  exact hA.closure' (Pi.continuous_domRestrict _ |>.comp hu) (continuous_apply x₀ |>.comp hu)

/-- If a set of functions is equicontinuous at some `x₀`, its closure for the product topology is
also equicontinuous at `x₀`. -/
/-
**Set.EquicontinuousAt.closure** 是 Mathlib 中的一个定理，位于命名空间 `Set.EquicontinuousAt`。
形式化陈述：∀ {X : Type u_3} {α : Type u_6} [tX : TopologicalSpace X] [uα : UniformSpa
ce α] {A : Set (X → α)} {x₀ : X},   A.EquicontinuousAt x₀ → (closure A).Equicont
inuousAt x₀
参数：X → α；closure A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquicontinuousAt.closure'`：EquicontinuousAt.closure' {A : Set Y} {u : Y 
-> X -> α} {x₀ : X} (hA : EquicontinuousAt (u ∘ (↑) : A -> X -> α) x₀) (hu : Con
tinuous u) : Eq…
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)

--- 原说明 ---
If a set of functions is equicontinuous at some `x₀`, its closure for the produc
t topology is
also equicontinuous at `x₀`.
-/
protected theorem Set.EquicontinuousAt.closure {A : Set (X → α)} {x₀ : X}
    (hA : A.EquicontinuousAt x₀) : (closure A).EquicontinuousAt x₀ :=
  hA.closure' (u := id) continuous_id

/-- If a set of functions is equicontinuous at some `x₀` within a set `S`, its closure for the
product topology is also equicontinuous at `x₀` within `S`. This would also be true for the coarser
topology of pointwise convergence on `S ∪ {x₀}`, see `Set.EquicontinuousWithinAt.closure'`. -/
/-
**Set.EquicontinuousWithinAt.closure** 是 Mathlib 中的一个定理，位于命名空间 `Set.Equicontinuo
usWithinAt`。
形式化陈述：∀ {X : Type u_3} {α : Type u_6} [tX : TopologicalSpace X] [uα : UniformSpa
ce α] {A : Set (X → α)} {S : Set X} {x₀ : X},   A.EquicontinuousWithinAt S x₀ → 
(closure A).EquicontinuousWithinAt S x₀
参数：X → α；closure A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquicontinuousWithinAt.closure'`：EquicontinuousWithinAt.closure' {A : Se
t Y} {u : Y -> X -> α} {S : Set X} {x₀ : X} (hA : EquicontinuousWithinAt (u ∘ (↑
) : A -> X -> α) S x₀…
· 使用引理 `Pi.continuous_domRestrict`：Pi.continuous_domRestrict (S : Set ι) : Conti
nuous (S.domRestrict : (forall i : ι, A i) -> (forall i : S, A i))
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)

--- 原说明 ---
If a set of functions is equicontinuous at some `x₀` within a set `S`, its closu
re for the
product topology is also equicontinuous at `x₀` within `S`. This would also be t
rue for the coarser
topology of pointwise convergence on `S ∪ {x₀}`, see `Set.EquicontinuousWithinAt
.closure'`.
-/
protected theorem Set.EquicontinuousWithinAt.closure {A : Set (X → α)} {S : Set X} {x₀ : X}
    (hA : A.EquicontinuousWithinAt S x₀) :
    (closure A).EquicontinuousWithinAt S x₀ :=
  hA.closure' (u := id) (Pi.continuous_domRestrict _) (continuous_apply _)

/-- If a set of functions is equicontinuous, the same is true for its closure in *any*
topology for which evaluation at any point is continuous. Since this will be applied to
`DFunLike` types, we state it for any topological space with a map to `X → α` satisfying the right
continuity conditions. See also `Set.Equicontinuous.closure` for a more familiar statement. -/
/-
**Equicontinuous.closure'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equicontinuous.closure' {A : Set Y} {u : Y -> X -> α} (hA : Equicontinuous
 (u ∘ (↑) : A -> X -> α)) (hu : Continuous u) : Equicontinuous (u ∘ (↑) : closur
e A -> X -> α)
参数：hA : Equicontinuous (u ∘ (↑) : A -> X -> α)；hu : Continuous u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquicontinuousAt.closure'`：EquicontinuousAt.closure' {A : Set Y} {u : Y 
-> X -> α} {x₀ : X} (hA : EquicontinuousAt (u ∘ (↑) : A -> X -> α) x₀) (hu : Con
tinuous u) : Eq…

--- 原说明 ---
If a set of functions is equicontinuous, the same is true for its closure in *an
y*
topology for which evaluation at any point is continuous. Since this will be app
lied to
`DFunLike` types, we state it for any topological space with a map to `X → α` sa
tisfying the right
continuity conditions. See also `Set.Equicontinuous.closure` for a more familiar
 statement.
-/
theorem Equicontinuous.closure' {A : Set Y} {u : Y → X → α}
    (hA : Equicontinuous (u ∘ (↑) : A → X → α)) (hu : Continuous u) :
    Equicontinuous (u ∘ (↑) : closure A → X → α) := fun x ↦ (hA x).closure' hu

/-- If a set of functions is equicontinuous on a set `S`, the same is true for its closure in *any*
topology for which evaluation at any `x ∈ S` is continuous. Since this will be applied to
`DFunLike` types, we state it for any topological space with a map to `X → α` satisfying the right
continuity conditions. See also `Set.EquicontinuousOn.closure` for a more familiar
(but weaker) statement. -/
/-
**EquicontinuousOn.closure'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EquicontinuousOn.closure' {A : Set Y} {u : Y -> X -> α} {S : Set X} (hA : 
EquicontinuousOn (u ∘ (↑) : A -> X -> α) S) (hu : Continuous (S.domRestrict ∘ u)
) : EquicontinuousOn (u ∘ (↑) : closure A -> X -> α) S
参数：hA : EquicontinuousOn (u ∘ (↑) : A -> X -> α) S；hu : Continuous (S.domRestric
t ∘ u)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquicontinuousWithinAt.closure'`：EquicontinuousWithinAt.closure' {A : Se
t Y} {u : Y -> X -> α} {S : Set X} {x₀ : X} (hA : EquicontinuousWithinAt (u ∘ (↑
) : A -> X -> α) S x₀…
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)

--- 原说明 ---
If a set of functions is equicontinuous on a set `S`, the same is true for its c
losure in *any*
topology for which evaluation at any `x ∈ S` is continuous. Since this will be a
pplied to
`DFunLike` types, we state it for any topological space with a map to `X → α` sa
tisfying the right
continuity conditions. See also `Set.EquicontinuousOn.closure` for a more famili
ar
(but weaker) statement.
-/
theorem EquicontinuousOn.closure' {A : Set Y} {u : Y → X → α} {S : Set X}
    (hA : EquicontinuousOn (u ∘ (↑) : A → X → α) S) (hu : Continuous (S.domRestrict ∘ u)) :
    EquicontinuousOn (u ∘ (↑) : closure A → X → α) S :=
  fun x hx ↦ (hA x hx).closure' hu <| by exact continuous_apply ⟨x, hx⟩ |>.comp hu

/-- If a set of functions is equicontinuous, its closure for the product topology is also
equicontinuous. -/
/-
**Set.Equicontinuous.closure** 是 Mathlib 中的一个定理，位于命名空间 `Set.Equicontinuous`。
形式化陈述：∀ {X : Type u_3} {α : Type u_6} [tX : TopologicalSpace X] [uα : UniformSpa
ce α] {A : Set (X → α)},   A.Equicontinuous → (closure A).Equicontinuous
参数：X → α；closure A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.EquicontinuousAt.closure`：∀ {X : Type u_3} {α : Type u_6} [tX : Topo
logicalSpace X] [uα : UniformSpace α] {A : Set (X → α)} {x₀ : X},   A.Equicontin
uousAt x₀ → (closu…

--- 原说明 ---
If a set of functions is equicontinuous, its closure for the product topology is
 also
equicontinuous.
-/
protected theorem Set.Equicontinuous.closure {A : Set <| X → α} (hA : A.Equicontinuous) :
    (closure A).Equicontinuous := fun x ↦ Set.EquicontinuousAt.closure (hA x)

/-- If a set of functions is equicontinuous, its closure for the product topology is also
equicontinuous. This would also be true for the coarser topology of pointwise convergence on `S`,
see `EquicontinuousOn.closure'`. -/
/-
**Set.EquicontinuousOn.closure** 是 Mathlib 中的一个定理，位于命名空间 `Set.EquicontinuousOn`。
形式化陈述：∀ {X : Type u_3} {α : Type u_6} [tX : TopologicalSpace X] [uα : UniformSpa
ce α] {A : Set (X → α)} {S : Set X},   A.EquicontinuousOn S → (closure A).Equico
ntinuousOn S
参数：X → α；closure A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.EquicontinuousWithinAt.closure`：∀ {X : Type u_3} {α : Type u_6} [tX 
: TopologicalSpace X] [uα : UniformSpace α] {A : Set (X → α)} {S : Set X} {x₀ : 
X},   A.EquicontinuousWi…

--- 原说明 ---
If a set of functions is equicontinuous, its closure for the product topology is
 also
equicontinuous. This would also be true for the coarser topology of pointwise co
nvergence on `S`,
see `EquicontinuousOn.closure'`.
-/
protected theorem Set.EquicontinuousOn.closure {A : Set <| X → α} {S : Set X}
    (hA : A.EquicontinuousOn S) : (closure A).EquicontinuousOn S :=
  fun x hx ↦ Set.EquicontinuousWithinAt.closure (hA x hx)

/-- If a set of functions is uniformly equicontinuous on a set `S`, the same is true for its
closure in *any* topology for which evaluation at any `x ∈ S` i continuous. Since this will be
applied to `DFunLike` types, we state it for any topological space with a map to `β → α` satisfying
the right continuity conditions. See also `Set.UniformEquicontinuousOn.closure` for a more familiar
(but weaker) statement. -/
/-
**UniformEquicontinuousOn.closure'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformEquicontinuousOn.closure' {A : Set Y} {u : Y -> β -> α} {S : Set β}
 (hA : UniformEquicontinuousOn (u ∘ (↑) : A -> β -> α) S) (hu : Continuous (S.do
mRestrict ∘ u)) : UniformEquicontinuousOn (u ∘ (↑) : closure A -> β -> α) S
参数：hA : UniformEquicontinuousOn (u ∘ (↑) : A -> β -> α) S；hu : Continuous (S.dom
Restrict ∘ u)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_uniformity_isClosed`：mem_uniformity_isClosed {s : SetRel α α} (h : s
 in 𝓤 α) : exists t in 𝓤 α, IsClosed t ∧ t subseteq s
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.mem_inf_of_right`：mem_inf_of_right {f g : Filter α} {s : Set α} (
h : s in g) : s in f ⊓ g
· 使用定理 `Filter.mem_principal_self`：mem_principal_self (s : Set α) : s in 𝓟 s
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetCoe.forall`：SetCoe.forall {s : Set α} {p : s -> Prop} : (forall x : s
, p x) ↔ forall (x) (h : x in s), p ⟨x, h⟩
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t

--- 原说明 ---
If a set of functions is uniformly equicontinuous on a set `S`, the same is true
 for its
closure in *any* topology for which evaluation at any `x ∈ S` i continuous. Sinc
e this will be
applied to `DFunLike` types, we state it for any topological space with a map to
 `β → α` satisfying
the right continuity conditions. See also `Set.UniformEquicontinuousOn.closure` 
for a more familiar
(but weaker) statement.
-/
theorem UniformEquicontinuousOn.closure' {A : Set Y} {u : Y → β → α} {S : Set β}
    (hA : UniformEquicontinuousOn (u ∘ (↑) : A → β → α) S) (hu : Continuous (S.domRestrict ∘ u)) :
    UniformEquicontinuousOn (u ∘ (↑) : closure A → β → α) S := by
  intro U hU
  rcases mem_uniformity_isClosed hU with ⟨V, hV, hVclosed, hVU⟩
  filter_upwards [hA V hV, mem_inf_of_right (mem_principal_self _)]
  rintro ⟨x, y⟩ hxy ⟨hxS, hyS⟩
  rw [SetCoe.forall] at *
  change A ⊆ (fun f => (u f x, u f y)) ⁻¹' V at hxy
  refine (closure_minimal hxy <| hVclosed.preimage <| .prodMk ?_ ?_).trans (preimage_mono hVU)
  · exact (continuous_apply ⟨x, hxS⟩).comp hu
  · exact (continuous_apply ⟨y, hyS⟩).comp hu

/-- If a set of functions is uniformly equicontinuous, the same is true for its closure in *any*
topology for which evaluation at any point is continuous. Since this will be applied to
`DFunLike` types, we state it for any topological space with a map to `β → α` satisfying the right
continuity conditions. See also `Set.UniformEquicontinuous.closure` for a more familiar statement.
-/
/-
**UniformEquicontinuous.closure'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniformEquicontinuous.closure' {A : Set Y} {u : Y -> β -> α} (hA : Uniform
Equicontinuous (u ∘ (↑) : A -> β -> α)) (hu : Continuous u) : UniformEquicontinu
ous (u ∘ (↑) : closure A -> β -> α)
参数：hA : UniformEquicontinuous (u ∘ (↑) : A -> β -> α)；hu : Continuous u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `uniformEquicontinuousOn_univ`：uniformEquicontinuousOn_univ (F : ι -> β -
> α) : UniformEquicontinuousOn F univ ↔ UniformEquicontinuous F
· 使用定理 `UniformEquicontinuousOn.closure'`：UniformEquicontinuousOn.closure' {A : 
Set Y} {u : Y -> β -> α} {S : Set β} (hA : UniformEquicontinuousOn (u ∘ (↑) : A 
-> β -> α) S) (hu : Co…
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用引理 `Pi.continuous_domRestrict`：Pi.continuous_domRestrict (S : Set ι) : Conti
nuous (S.domRestrict : (forall i : ι, A i) -> (forall i : S, A i))

--- 原说明 ---
If a set of functions is uniformly equicontinuous, the same is true for its clos
ure in *any*
topology for which evaluation at any point is continuous. Since this will be app
lied to
`DFunLike` types, we state it for any topological space with a map to `β → α` sa
tisfying the right
continuity conditions. See also `Set.UniformEquicontinuous.closure` for a more f
amiliar statement.
-/
theorem UniformEquicontinuous.closure' {A : Set Y} {u : Y → β → α}
    (hA : UniformEquicontinuous (u ∘ (↑) : A → β → α)) (hu : Continuous u) :
    UniformEquicontinuous (u ∘ (↑) : closure A → β → α) := by
  rw [← uniformEquicontinuousOn_univ] at hA ⊢
  exact hA.closure' (Pi.continuous_domRestrict _ |>.comp hu)

/-- If a set of functions is uniformly equicontinuous, its closure for the product topology is also
uniformly equicontinuous. -/
/-
**Set.UniformEquicontinuous.closure** 是 Mathlib 中的一个定理，位于命名空间 `Set.UniformEquico
ntinuous`。
形式化陈述：∀ {α : Type u_6} {β : Type u_8} [uα : UniformSpace α] [uβ : UniformSpace β
] {A : Set (β → α)},   A.UniformEquicontinuous → (closure A).UniformEquicontinuo
us
参数：β → α；closure A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformEquicontinuous.closure'`：UniformEquicontinuous.closure' {A : Set 
Y} {u : Y -> β -> α} (hA : UniformEquicontinuous (u ∘ (↑) : A -> β -> α)) (hu : 
Continuous u) : Unif…
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)

--- 原说明 ---
If a set of functions is uniformly equicontinuous, its closure for the product t
opology is also
uniformly equicontinuous.
-/
protected theorem Set.UniformEquicontinuous.closure {A : Set <| β → α}
    (hA : A.UniformEquicontinuous) : (closure A).UniformEquicontinuous :=
  UniformEquicontinuous.closure' (u := id) hA continuous_id

/-- If a set of functions is uniformly equicontinuous on a set `S`, its closure for the product
topology is also uniformly equicontinuous. This would also be true for the coarser topology of
pointwise convergence on `S`, see `UniformEquicontinuousOn.closure'`. -/
/-
**Set.UniformEquicontinuousOn.closure** 是 Mathlib 中的一个定理，位于命名空间 `Set.UniformEqui
continuousOn`。
形式化陈述：∀ {α : Type u_6} {β : Type u_8} [uα : UniformSpace α] [uβ : UniformSpace β
] {A : Set (β → α)} {S : Set β},   A.UniformEquicontinuousOn S → (closure A).Uni
formEquicontinuousOn S
参数：β → α；closure A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformEquicontinuousOn.closure'`：UniformEquicontinuousOn.closure' {A : 
Set Y} {u : Y -> β -> α} {S : Set β} (hA : UniformEquicontinuousOn (u ∘ (↑) : A 
-> β -> α) S) (hu : Co…
· 使用引理 `Pi.continuous_domRestrict`：Pi.continuous_domRestrict (S : Set ι) : Conti
nuous (S.domRestrict : (forall i : ι, A i) -> (forall i : S, A i))

--- 原说明 ---
If a set of functions is uniformly equicontinuous on a set `S`, its closure for 
the product
topology is also uniformly equicontinuous. This would also be true for the coars
er topology of
pointwise convergence on `S`, see `UniformEquicontinuousOn.closure'`.
-/
protected theorem Set.UniformEquicontinuousOn.closure {A : Set <| β → α} {S : Set β}
    (hA : A.UniformEquicontinuousOn S) : (closure A).UniformEquicontinuousOn S :=
  UniformEquicontinuousOn.closure' (u := id) hA (Pi.continuous_domRestrict _)

/-
Implementation note: The following lemma (as well as all the following variations) could
theoretically be deduced from the "closure" statements above. For example, we could do:
```lean
theorem Filter.Tendsto.continuousAt_of_equicontinuousAt {l : Filter ι} [l.NeBot] {F : ι → X → α}
    {f : X → α} {x₀ : X} (h₁ : Tendsto F l (𝓝 f)) (h₂ : EquicontinuousAt F x₀) :
    ContinuousAt f x₀ :=
  (equicontinuousAt_iff_range.mp h₂).closure.continuousAt
    ⟨f, mem_closure_of_tendsto h₁ <| Eventually.of_forall mem_range_self⟩

theorem Filter.Tendsto.uniformContinuous_of_uniformEquicontinuous {l : Filter ι} [l.NeBot]
    {F : ι → β → α} {f : β → α} (h₁ : Tendsto F l (𝓝 f)) (h₂ : UniformEquicontinuous F) :
    UniformContinuous f :=
  (uniformEquicontinuous_iff_range.mp h₂).closure.uniformContinuous
    ⟨f, mem_closure_of_tendsto h₁ <| Eventually.of_forall mem_range_self⟩
```

Unfortunately, the proofs get painful when dealing with the relative case as one needs to change
the ambient topology. So it turns out to be easier to re-do the proof by hand.
-/

/-- If `𝓕 : ι → X → α` tends to `f : X → α` *pointwise on `S ∪ {x₀} : Set X`* along some nontrivial
filter, and if the family `𝓕` is equicontinuous at `x₀ : X` within `S`, then the limit is
continuous at `x₀` within `S`. -/
/-
**Filter.Tendsto.continuousWithinAt_of_equicontinuousWithinAt** 是 Mathlib 中的一个定理
，位于命名空间 ``。
形式化陈述：Filter.Tendsto.continuousWithinAt_of_equicontinuousWithinAt {l : Filter ι}
 [l.NeBot] {F : ι -> X -> α} {f : X -> α} {S : Set X} {x₀ : X} (h₁ : forall x in
 S, Tendsto (F · x) l (𝓝 (f x))) (h₂ : Tendsto (F · x₀) l (𝓝 (f x₀))) (h₃ : Equi
continuousWithinAt F S x₀) : ContinuousWithinAt f S x₀
参数：h₁ : forall x in S, Tendsto (F · x) l (𝓝 (f x))；h₂ : Tendsto (F · x₀) l (𝓝 (f
 x₀))；h₃ : EquicontinuousWithinAt F S x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `UniformSpace.mem_nhds_iff`：UniformSpace.mem_nhds_iff {x : α} {s : Set α}
 : s in 𝓝 x ↔ exists V in 𝓤 α, ball x V subseteq s
· 使用定理 `mem_uniformity_isClosed`：mem_uniformity_isClosed {s : SetRel α α} (h : s
 in 𝓤 α) : exists t in 𝓤 α, IsClosed t ∧ t subseteq s
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `eventually_mem_nhdsWithin`：eventually_mem_nhdsWithin {a : α} {s : Set α}
 : forallᶠ x in 𝓝[s] a, x in s
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `UniformSpace.ball_mono`：ball_mono {V W : Set (β × β)} (h : V subseteq W)
 (x : β) : ball x V subseteq ball x W
· 使用定理 `IsClosed.mem_of_tendsto`：IsClosed.mem_of_tendsto {f : α -> X} {b : Filte
r α} [NeBot b] (hs : IsClosed s) (hf : Tendsto f b (𝓝 x)) (h : forallᶠ x in b, f
 x in s) : x …
· 使用定理 `Filter.Tendsto.prodMk_nhds`：Filter.Tendsto.prodMk_nhds {γ} {x : X} {y : 
Y} {f : Filter γ} {mx : γ -> X} {my : γ -> Y} (hx : Tendsto mx f (𝓝 x)) (hy : Te
ndsto my f (𝓝 y)…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x

--- 原说明 ---
If `𝓕 : ι → X → α` tends to `f : X → α` *pointwise on `S ∪ {x₀} : Set X`* along 
some nontrivial
filter, and if the family `𝓕` is equicontinuous at `x₀ : X` within `S`, then the
 limit is
continuous at `x₀` within `S`.
-/
theorem Filter.Tendsto.continuousWithinAt_of_equicontinuousWithinAt {l : Filter ι} [l.NeBot]
    {F : ι → X → α} {f : X → α} {S : Set X} {x₀ : X} (h₁ : ∀ x ∈ S, Tendsto (F · x) l (𝓝 (f x)))
    (h₂ : Tendsto (F · x₀) l (𝓝 (f x₀))) (h₃ : EquicontinuousWithinAt F S x₀) :
    ContinuousWithinAt f S x₀ := by
  intro U hU; rw [mem_map]
  rcases UniformSpace.mem_nhds_iff.mp hU with ⟨V, hV, hVU⟩
  rcases mem_uniformity_isClosed hV with ⟨W, hW, hWclosed, hWV⟩
  filter_upwards [h₃ W hW, eventually_mem_nhdsWithin] with x hx hxS using
    hVU <| ball_mono hWV (f x₀) <| hWclosed.mem_of_tendsto (h₂.prodMk_nhds (h₁ x hxS)) <|
    Eventually.of_forall hx

/-- If `𝓕 : ι → X → α` tends to `f : X → α` *pointwise* along some nontrivial filter, and if the
family `𝓕` is equicontinuous at some `x₀ : X`, then the limit is continuous at `x₀`. -/
/-
**Filter.Tendsto.continuousAt_of_equicontinuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.continuousAt_of_equicontinuousAt {l : Filter ι} [l.NeBot] {
F : ι → X → α} {f : X → α} {x₀ : X} (h₁ : Tendsto F l (𝓝 f)) (h₂ : Equicontinuou
sAt F x₀) : ContinuousAt f x₀
参数：h₁ : Tendsto F l (𝓝 f)；h₂ : EquicontinuousAt F x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuousWithinAt_univ`：continuousWithinAt_univ (f : α -> β) (x : α) : 
ContinuousWithinAt f Set.univ x ↔ ContinuousAt f x
· 使用定理 `Filter.Tendsto.continuousWithinAt_of_equicontinuousWithinAt`：Filter.Tend
sto.continuousWithinAt_of_equicontinuousWithinAt {l : Filter ι} [l.NeBot] {F : ι
 -> X -> α} {f : X -> α} {S : Set X} {x₀ : X} (h₁…
· 使用定理 `tendsto_pi_nhds`：tendsto_pi_nhds {f : Y -> forall i, A i} {g : forall i,
 A i} {u : Filter Y} : Tendsto f u (𝓝 g) ↔ forall x, Tendsto (fun i => f i x) u 
(𝓝 (g…
· 使用定理 `equicontinuousWithinAt_univ`：∀ {ι : Type u_1} {X : Type u_3} {α : Type u
_6} [tX : TopologicalSpace X] [uα : UniformSpace α] (F : ι → X → α) (x₀ : X),   
EquicontinuousWit…

--- 原说明 ---
If `𝓕 : ι → X → α` tends to `f : X → α` *pointwise* along some nontrivial filter
, and if the
family `𝓕` is equicontinuous at some `x₀ : X`, then the limit is continuous at `
x₀`.
-/
theorem Filter.Tendsto.continuousAt_of_equicontinuousAt {l : Filter ι} [l.NeBot] {F : ι → X → α}
    {f : X → α} {x₀ : X} (h₁ : Tendsto F l (𝓝 f)) (h₂ : EquicontinuousAt F x₀) :
    ContinuousAt f x₀ := by
  rw [← continuousWithinAt_univ, ← equicontinuousWithinAt_univ, tendsto_pi_nhds] at *
  exact continuousWithinAt_of_equicontinuousWithinAt (fun x _ ↦ h₁ x) (h₁ x₀) h₂

/-- If `𝓕 : ι → X → α` tends to `f : X → α` *pointwise* along some nontrivial filter, and if the
family `𝓕` is equicontinuous, then the limit is continuous. -/
/-
**Filter.Tendsto.continuous_of_equicontinuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.continuous_of_equicontinuous {l : Filter ι} [l.NeBot] {F : 
ι -> X -> α} {f : X -> α} (h₁ : Tendsto F l (𝓝 f)) (h₂ : Equicontinuous F) : Con
tinuous f
参数：h₁ : Tendsto F l (𝓝 f)；h₂ : Equicontinuous F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `Filter.Tendsto.continuousAt_of_equicontinuousAt`：Filter.Tendsto.continuo
usAt_of_equicontinuousAt {l : Filter ι} [l.NeBot] {F : ι → X → α} {f : X → α} {x
₀ : X} (h₁ : Tendsto F l (𝓝 f)) (h₂ :…

--- 原说明 ---
If `𝓕 : ι → X → α` tends to `f : X → α` *pointwise* along some nontrivial filter
, and if the
family `𝓕` is equicontinuous, then the limit is continuous.
-/
theorem Filter.Tendsto.continuous_of_equicontinuous {l : Filter ι} [l.NeBot] {F : ι → X → α}
    {f : X → α} (h₁ : Tendsto F l (𝓝 f)) (h₂ : Equicontinuous F) : Continuous f :=
  continuous_iff_continuousAt.mpr fun x => h₁.continuousAt_of_equicontinuousAt (h₂ x)

/-- If `𝓕 : ι → X → α` tends to `f : X → α` *pointwise on `S : Set X`* along some nontrivial
filter, and if the family `𝓕` is equicontinuous, then the limit is continuous on `S`. -/
/-
**Filter.Tendsto.continuousOn_of_equicontinuousOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.continuousOn_of_equicontinuousOn {l : Filter ι} [l.NeBot] {
F : ι -> X -> α} {f : X -> α} {S : Set X} (h₁ : forall x in S, Tendsto (F · x) l
 (𝓝 (f x))) (h₂ : EquicontinuousOn F S) : ContinuousOn f S
参数：h₁ : forall x in S, Tendsto (F · x) l (𝓝 (f x))；h₂ : EquicontinuousOn F S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.continuousWithinAt_of_equicontinuousWithinAt`：Filter.Tend
sto.continuousWithinAt_of_equicontinuousWithinAt {l : Filter ι} [l.NeBot] {F : ι
 -> X -> α} {f : X -> α} {S : Set X} {x₀ : X} (h₁…

--- 原说明 ---
If `𝓕 : ι → X → α` tends to `f : X → α` *pointwise on `S : Set X`* along some no
ntrivial
filter, and if the family `𝓕` is equicontinuous, then the limit is continuous on
 `S`.
-/
theorem Filter.Tendsto.continuousOn_of_equicontinuousOn {l : Filter ι} [l.NeBot] {F : ι → X → α}
    {f : X → α} {S : Set X} (h₁ : ∀ x ∈ S, Tendsto (F · x) l (𝓝 (f x)))
    (h₂ : EquicontinuousOn F S) : ContinuousOn f S :=
  fun x hx ↦ Filter.Tendsto.continuousWithinAt_of_equicontinuousWithinAt h₁ (h₁ x hx) (h₂ x hx)

/-- If `𝓕 : ι → β → α` tends to `f : β → α` *pointwise on `S : Set β`* along some nontrivial
filter, and if the family `𝓕` is uniformly equicontinuous on `S`, then the limit is uniformly
continuous on `S`. -/
/-
**Filter.Tendsto.uniformContinuousOn_of_uniformEquicontinuousOn** 是 Mathlib 中的一个
定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.uniformContinuousOn_of_uniformEquicontinuousOn {l : Filter 
ι} [l.NeBot] {F : ι -> β -> α} {f : β -> α} {S : Set β} (h₁ : forall x in S, Ten
dsto (F · x) l (𝓝 (f x))) (h₂ : UniformEquicontinuousOn F S) : UniformContinuous
On f S
参数：h₁ : forall x in S, Tendsto (F · x) l (𝓝 (f x))；h₂ : UniformEquicontinuousOn 
F S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `mem_uniformity_isClosed`：mem_uniformity_isClosed {s : SetRel α α} (h : s
 in 𝓤 α) : exists t in 𝓤 α, IsClosed t ∧ t subseteq s
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.mem_inf_of_right`：mem_inf_of_right {f g : Filter α} {s : Set α} (
h : s in g) : s in f ⊓ g
· 使用定理 `Filter.mem_principal_self`：mem_principal_self (s : Set α) : s in 𝓟 s
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `IsClosed.mem_of_tendsto`：IsClosed.mem_of_tendsto {f : α -> X} {b : Filte
r α} [NeBot b] (hs : IsClosed s) (hf : Tendsto f b (𝓝 x)) (h : forallᶠ x in b, f
 x in s) : x …
· 使用定理 `Filter.Tendsto.prodMk_nhds`：Filter.Tendsto.prodMk_nhds {γ} {x : X} {y : 
Y} {f : Filter γ} {mx : γ -> X} {my : γ -> Y} (hx : Tendsto mx f (𝓝 x)) (hy : Te
ndsto my f (𝓝 y)…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x

--- 原说明 ---
If `𝓕 : ι → β → α` tends to `f : β → α` *pointwise on `S : Set β`* along some no
ntrivial
filter, and if the family `𝓕` is uniformly equicontinuous on `S`, then the limit
 is uniformly
continuous on `S`.
-/
theorem Filter.Tendsto.uniformContinuousOn_of_uniformEquicontinuousOn {l : Filter ι} [l.NeBot]
    {F : ι → β → α} {f : β → α} {S : Set β} (h₁ : ∀ x ∈ S, Tendsto (F · x) l (𝓝 (f x)))
    (h₂ : UniformEquicontinuousOn F S) :
    UniformContinuousOn f S := by
  intro U hU; rw [mem_map]
  rcases mem_uniformity_isClosed hU with ⟨V, hV, hVclosed, hVU⟩
  filter_upwards [h₂ V hV, mem_inf_of_right (mem_principal_self _)]
  rintro ⟨x, y⟩ hxy ⟨hxS, hyS⟩
  exact hVU <| hVclosed.mem_of_tendsto ((h₁ x hxS).prodMk_nhds (h₁ y hyS)) <|
    Eventually.of_forall hxy

/-- If `𝓕 : ι → β → α` tends to `f : β → α` *pointwise* along some nontrivial filter, and if the
family `𝓕` is uniformly equicontinuous, then the limit is uniformly continuous. -/
/-
**Filter.Tendsto.uniformContinuous_of_uniformEquicontinuous** 是 Mathlib 中的一个定理，位
于命名空间 ``。
形式化陈述：Filter.Tendsto.uniformContinuous_of_uniformEquicontinuous {l : Filter ι} [
l.NeBot] {F : ι → β → α} {f : β → α} (h₁ : Tendsto F l (𝓝 f)) (h₂ : UniformEquic
ontinuous F) : UniformContinuous f
参数：h₁ : Tendsto F l (𝓝 f)；h₂ : UniformEquicontinuous F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `uniformContinuousOn_univ`：uniformContinuousOn_univ {f : α -> β} : Unifor
mContinuousOn f univ ↔ UniformContinuous f
· 使用定理 `Filter.Tendsto.uniformContinuousOn_of_uniformEquicontinuousOn`：Filter.Te
ndsto.uniformContinuousOn_of_uniformEquicontinuousOn {l : Filter ι} [l.NeBot] {F
 : ι -> β -> α} {f : β -> α} {S : Set β} (h₁ : fora…
· 使用定理 `tendsto_pi_nhds`：tendsto_pi_nhds {f : Y -> forall i, A i} {g : forall i,
 A i} {u : Filter Y} : Tendsto f u (𝓝 g) ↔ forall x, Tendsto (fun i => f i x) u 
(𝓝 (g…
· 使用引理 `uniformEquicontinuousOn_univ`：uniformEquicontinuousOn_univ (F : ι -> β -
> α) : UniformEquicontinuousOn F univ ↔ UniformEquicontinuous F

--- 原说明 ---
If `𝓕 : ι → β → α` tends to `f : β → α` *pointwise* along some nontrivial filter
, and if the
family `𝓕` is uniformly equicontinuous, then the limit is uniformly continuous.
-/
theorem Filter.Tendsto.uniformContinuous_of_uniformEquicontinuous {l : Filter ι} [l.NeBot]
    {F : ι → β → α} {f : β → α} (h₁ : Tendsto F l (𝓝 f)) (h₂ : UniformEquicontinuous F) :
    UniformContinuous f := by
  rw [← uniformContinuousOn_univ, ← uniformEquicontinuousOn_univ, tendsto_pi_nhds] at *
  exact uniformContinuousOn_of_uniformEquicontinuousOn (fun x _ ↦ h₁ x) h₂

/-- If `F : ι → X → α` is a family of functions equicontinuous at `x`,
it tends to `f y` along a filter `l` for any `y ∈ s`,
the limit function `f` tends to `z` along `𝓝[s] x`, and `x ∈ closure s`,
then `(F · x)` tends to `z` along `l`.

In some sense, this is a converse of `EquicontinuousAt.closure`. -/
/-
**EquicontinuousAt.tendsto_of_mem_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EquicontinuousAt.tendsto_of_mem_closure {l : Filter ι} {F : ι -> X -> α} {
f : X -> α} {s : Set X} {x : X} {z : α} (hF : EquicontinuousAt F x) (hf : Tendst
o f (𝓝[s] x) (𝓝 z)) (hs : forall y in s, Tendsto (F · y) l (𝓝 (f y))) (hx : x in
 closure s) : Tendsto (F · x) l (𝓝 z)
参数：hF : EquicontinuousAt F x；hf : Tendsto f (𝓝[s] x) (𝓝 z)；hs : forall y in s, T
endsto (F · y) l (𝓝 (f y))；hx : x in closure s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `nhds_basis_uniformity`：nhds_basis_uniformity {p : ι -> Prop} {s : ι -> S
etRel α α} (h : (𝓤 α).HasBasis p s) {x : α} : (𝓝 x).HasBasis p fun i => { y | (y
, x) in s i…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `comp_comp_symm_mem_uniformity_sets`：comp_comp_symm_mem_uniformity_sets {
s : SetRel α α} (hs : s in 𝓤 α) : exists t in 𝓤 α, SetRel.IsSymm t ∧ t ○ t ○ t s
ubseteq s
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `eventually_mem_nhdsWithin`：eventually_mem_nhdsWithin {a : α} {s : Set α}
 : forallᶠ x in 𝓝[s] a, x in s
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `mem_closure_iff_nhdsWithin_neBot`：mem_closure_iff_nhdsWithin_neBot : x i
n closure s ↔ NeBot (𝓝[s] x)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `UniformSpace.ball_mem_nhds`：UniformSpace.ball_mem_nhds (x : α) ⦃V : SetR
el α α⦄ (V_in : V in 𝓤 α) : ball x V in 𝓝 x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `UniformSpace.mem_ball_symmetry`：mem_ball_symmetry {V : SetRel β β} [V.Is
Symm] {x y} : x in ball y V ↔ y in ball x V

--- 原说明 ---
If `F : ι → X → α` is a family of functions equicontinuous at `x`,
it tends to `f y` along a filter `l` for any `y ∈ s`,
the limit function `f` tends to `z` along `𝓝[s] x`, and `x ∈ closure s`,
then `(F · x)` tends to `z` along `l`.

In some sense, this is a converse of `EquicontinuousAt.closure`.
-/
theorem EquicontinuousAt.tendsto_of_mem_closure {l : Filter ι} {F : ι → X → α} {f : X → α}
    {s : Set X} {x : X} {z : α} (hF : EquicontinuousAt F x) (hf : Tendsto f (𝓝[s] x) (𝓝 z))
    (hs : ∀ y ∈ s, Tendsto (F · y) l (𝓝 (f y))) (hx : x ∈ closure s) :
    Tendsto (F · x) l (𝓝 z) := by
  rw [(nhds_basis_uniformity (𝓤 α).basis_sets).tendsto_right_iff] at hf ⊢
  intro U hU
  rcases comp_comp_symm_mem_uniformity_sets hU with ⟨V, hV, hVs, hVU⟩
  rw [mem_closure_iff_nhdsWithin_neBot] at hx
  have : ∀ᶠ y in 𝓝[s] x, y ∈ s ∧ (∀ i, (F i x, F i y) ∈ V) ∧ (f y, z) ∈ V :=
    eventually_mem_nhdsWithin.and <| ((hF V hV).filter_mono nhdsWithin_le_nhds).and (hf V hV)
  rcases this.exists with ⟨y, hys, hFy, hfy⟩
  filter_upwards [hs y hys (ball_mem_nhds _ hV)] with i hi
  exact hVU ⟨_, ⟨_, hFy i, mem_ball_symmetry.2 hi⟩, hfy⟩

/-- If `F : ι → X → α` is an equicontinuous family of functions,
`f : X → α` is a continuous function, and `l` is a filter on `ι`,
then `{x | Filter.Tendsto (F · x) l (𝓝 (f x))}` is a closed set. -/
/-
**Equicontinuous.isClosed_setOfPred_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equicontinuous.isClosed_setOfPred_tendsto {l : Filter ι} {F : ι -> X -> α}
 {f : X -> α} (hF : Equicontinuous F) (hf : Continuous f) : IsClosed {x | Tendst
o (F · x) l (𝓝 (f x))}
参数：hF : Equicontinuous F；hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `closure_subset_iff_isClosed`：closure_subset_iff_isClosed : closure s sub
seteq s ↔ IsClosed s
· 使用定理 `EquicontinuousAt.tendsto_of_mem_closure`：EquicontinuousAt.tendsto_of_mem
_closure {l : Filter ι} {F : ι -> X -> α} {f : X -> α} {s : Set X} {x : X} {z : 
α} (hF : EquicontinuousAt F x…
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a

--- 原说明 ---
If `F : ι → X → α` is an equicontinuous family of functions,
`f : X → α` is a continuous function, and `l` is a filter on `ι`,
then `{x | Filter.Tendsto (F · x) l (𝓝 (f x))}` is a closed set.
-/
theorem Equicontinuous.isClosed_setOfPred_tendsto {l : Filter ι} {F : ι → X → α} {f : X → α}
    (hF : Equicontinuous F) (hf : Continuous f) :
    IsClosed {x | Tendsto (F · x) l (𝓝 (f x))} :=
  closure_subset_iff_isClosed.mp fun x hx ↦
    (hF x).tendsto_of_mem_closure (hf.continuousAt.mono_left inf_le_left) (fun _ ↦ id) hx

@[deprecated (since := "2026-07-09")]
alias Equicontinuous.isClosed_setOf_tendsto := Equicontinuous.isClosed_setOfPred_tendsto

end

end

