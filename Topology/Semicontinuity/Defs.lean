/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Antoine Chambert-Loir, Anatole Dedecker, Jireh Loreaux
-/
module

public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.ContinuousOn

/-!
# Semicontinuous maps

A function `f` from a topological space `α` to an ordered space `β` is *lower semicontinuous* at a
point `x` if, for any `y < f x`, for any `x'` close enough to `x`, one has `f x' > y`. In other
words, `f` can jump up, but it cannot jump down.

*Upper semicontinuous* functions are defined similarly. Upper and lower hemicontinuity (of
functions `f : α → Set β`) are often defined in terms of sequential characterizations, but
here we take an equivalent approach. `f : α → Set β` is *upper hemicontinuous* at `x` if for any
neighborhood of `f x`, `f x'` is included in this neighborhood for all `x'` close enough to `x`.

Of course, one can see a superficial similarity between upper semicontinuity and upper
hemicontinuity. In fact, we can unify all of upper and lower semicontinuity and also upper and
lower hemicontinuity under one umbrella, by considering a general relation `r : α → β → Prop` and
defining semicontinuity of this relation.

This file introduces these notions, and a basic API around them mimicking the API for continuous
functions.

## Main definitions and results

We introduce 4 generic definitions related to semicontinuity:
* `SemicontinuousWithinAt r s x`
* `SemicontinuousAt r x`
* `SemicontinuousOn r s`
* `Semicontinuous r`

We build a basic API using dot notation around these notions, and we prove that
* constant functions are semicontinuous;
* right composition with continuous functions preserves semicontinuity;

We also define lower and upper semicontinuity as abbreviations of these generic definitions
and transfer the generic results to these notions.

We also define two useful notions for set-valued functions: `HasOpenLowerSections` (which says that
for `f : α → β` and for all `y ∈ β`, the set `{x | y ∈ f x}` is open. Similarly, we define
`HasOpenCGraph` which says that the set of all pairs `(x, y) : α × β` with `y ∈ f x` is open.
We show that `HasOpenCGraph` implies `HasOpenLowerSections` (`HasOpenCGraph.hasOpenLowerSections`)
which implies `LowerHemicontinuous` (`HasOpenLowerSections.lowerHemicontinuous`).

We also define variants of these two notions for `On`/`At`/`WithinAt`.

## References

* <https://en.wikipedia.org/wiki/Semi-continuity>
* <https://en.wikipedia.org/wiki/Hemicontinuity>

-/

@[expose] public section

open scoped Topology

open Set Function Filter

variable {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace γ]

/-! ## Main definitions -/

section Semicontinuous

/-- A relation `r : α → β → Prop` is semicontinuous within `s` at `x : α`, if whenever `r x y`
is true, it is also true for all `x'` sufficiently close to `x` within `s`.

This notion generalizes lower and upper semicontinuity of functions, as well as
lower and upper hemicontinuity of set-valued correspondences. -/
/-
**SemicontinuousWithinAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SemicontinuousWithinAt (r : α -> β -> Prop) (s : Set α) (x : α)
参数：r : α -> β -> Prop；s : Set α；x : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A relation `r : α → β → Prop` is semicontinuous within `s` at `x : α`, if whenev
er `r x y`
is true, it is also true for all `x'` sufficiently close to `x` within `s`.

This notion generalizes lower and upper semicontinuity of functions, as well as
lower and upper hemicontinuity of set-valued correspondences.
-/
def SemicontinuousWithinAt (r : α → β → Prop) (s : Set α) (x : α) :=
  ∀ y, r x y → ∀ᶠ x' in 𝓝[s] x, r x' y

/-- A relation `r : α → β → Prop` is semicontinuous on `s` if it is semicontinuous within `s` at
each `x ∈ s`. -/
/-
**SemicontinuousOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SemicontinuousOn (r : α -> β -> Prop) (s : Set α)
参数：r : α -> β -> Prop；s : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A relation `r : α → β → Prop` is semicontinuous on `s` if it is semicontinuous w
ithin `s` at
each `x ∈ s`.
-/
def SemicontinuousOn (r : α → β → Prop) (s : Set α) :=
  ∀ x ∈ s, SemicontinuousWithinAt r s x

/-- A relation `r : α → β → Prop` is semicontinuous at `x : α`, if whenever `r x y`
is true, it is also true for all `x'` sufficiently close to `x`.

This notion generalizes lower and upper semicontinuity of functions, as well as
lower and upper hemicontinuity of set-valued correspondences. -/
/-
**SemicontinuousAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SemicontinuousAt (r : α -> β -> Prop) (x : α) : Prop
参数：r : α -> β -> Prop；x : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A relation `r : α → β → Prop` is semicontinuous at `x : α`, if whenever `r x y`
is true, it is also true for all `x'` sufficiently close to `x`.

This notion generalizes lower and upper semicontinuity of functions, as well as
lower and upper hemicontinuity of set-valued correspondences.
-/
def SemicontinuousAt (r : α → β → Prop) (x : α) : Prop :=
  ∀ y, r x y → ∀ᶠ x' in 𝓝 x, r x' y

/-- A relation `r : α → β → Prop` is semicontinuous if it is semicontinuous within `s` at each
`x : α`. -/
/-
**Semicontinuous** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Semicontinuous (r : α -> β -> Prop) : Prop
参数：r : α -> β -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A relation `r : α → β → Prop` is semicontinuous if it is semicontinuous within `
s` at each
`x : α`.
-/
def Semicontinuous (r : α → β → Prop) : Prop :=
  ∀ x, SemicontinuousAt r x

variable {r r' : α → β → Prop} {x : α} {s t : Set α}
/-
**semicontinuousWithinAt_iff_frequently** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：semicontinuousWithinAt_iff_frequently : SemicontinuousWithinAt r s x ↔ for
all y, (existsᶠ x' in 𝓝[s] x, ¬ r x' y) -> ¬ r x y
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
lemma semicontinuousWithinAt_iff_frequently :
    SemicontinuousWithinAt r s x ↔ ∀ y, (∃ᶠ x' in 𝓝[s] x, ¬ r x' y) → ¬ r x y := by
  simp only [← not_eventually, not_imp_not, SemicontinuousWithinAt]
/-
**semicontinuousOn_iff_frequently** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：semicontinuousOn_iff_frequently : SemicontinuousOn r s ↔ forall x in s, fo
rall y, (existsᶠ x' in 𝓝[s] x, ¬ r x' y) -> ¬ r x y
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
lemma semicontinuousOn_iff_frequently :
    SemicontinuousOn r s ↔ ∀ x ∈ s, ∀ y, (∃ᶠ x' in 𝓝[s] x, ¬ r x' y) → ¬ r x y := by
  simp only [← not_eventually, not_imp_not, SemicontinuousWithinAt, SemicontinuousOn]
/-
**semicontinuousAt_iff_frequently** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：semicontinuousAt_iff_frequently : SemicontinuousAt r x ↔ forall y, (exists
ᶠ x' in 𝓝 x, ¬ r x' y) -> ¬ r x y
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
lemma semicontinuousAt_iff_frequently :
    SemicontinuousAt r x ↔ ∀ y, (∃ᶠ x' in 𝓝 x, ¬ r x' y) → ¬ r x y := by
  simp only [← not_eventually, not_imp_not, SemicontinuousAt]
/-
**semicontinuous_iff_frequently** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：semicontinuous_iff_frequently : Semicontinuous r ↔ forall x y, (existsᶠ x'
 in 𝓝 x, ¬ r x' y) -> ¬ r x y
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
lemma semicontinuous_iff_frequently :
    Semicontinuous r ↔ ∀ x y, (∃ᶠ x' in 𝓝 x, ¬ r x' y) → ¬ r x y := by
  simp only [← not_eventually, not_imp_not, Semicontinuous, SemicontinuousAt]
/-
**SemicontinuousWithinAt.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SemicontinuousWithinAt.mono (h : SemicontinuousWithinAt r s x) (hst : t su
bseteq s) : SemicontinuousWithinAt r t x
参数：h : SemicontinuousWithinAt r s x；hst : t subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
-/
theorem SemicontinuousWithinAt.mono (h : SemicontinuousWithinAt r s x) (hst : t ⊆ s) :
    SemicontinuousWithinAt r t x := fun y hy =>
  Filter.Eventually.filter_mono (nhdsWithin_mono _ hst) (h y hy)
/-
**SemicontinuousWithinAt.congr_of_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SemicontinuousWithinAt.congr_of_eventuallyEq {a : α} (h : SemicontinuousWi
thinAt r s a) (has : a in s) (hfg : forallᶠ x in 𝓝[s] a, forall y, r x y ↔ r' x 
y) : SemicontinuousWithinAt r' s a
参数：h : SemicontinuousWithinAt r s a；has : a in s；hfg : forallᶠ x in 𝓝[s] a, fora
ll y, r x y ↔ r' x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.EventuallyEq.eq_of_nhdsWithin`：Filter.EventuallyEq.eq_of_nhdsWith
in {s : Set α} {f g : α -> β} {a : α} (h : f =ᶠ[𝓝[s] a] g) (hmem : a in s) : f a
 = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
theorem SemicontinuousWithinAt.congr_of_eventuallyEq {a : α}
    (h : SemicontinuousWithinAt r s a)
    (has : a ∈ s) (hfg : ∀ᶠ x in 𝓝[s] a, ∀ y, r x y ↔ r' x y) :
    SemicontinuousWithinAt r' s a := by
  intro b hb
  simp_rw [← propext_iff, ← funext_iff] at hfg
  rw [← Filter.EventuallyEq.eq_of_nhdsWithin hfg has] at hb
  filter_upwards [hfg, h b hb] with x hx hxb
  exact hx ▸ hxb
/-
**semicontinuousWithinAt_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：semicontinuousWithinAt_univ_iff : SemicontinuousWithinAt r univ x ↔ Semico
ntinuousAt r x
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
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem semicontinuousWithinAt_univ_iff :
    SemicontinuousWithinAt r univ x ↔ SemicontinuousAt r x := by
  simp [SemicontinuousWithinAt, SemicontinuousAt, nhdsWithin_univ]
/-
**SemicontinuousAt.semicontinuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SemicontinuousAt.semicontinuousWithinAt (s : Set α) (h : SemicontinuousAt 
r x) : SemicontinuousWithinAt r s x
参数：s : Set α；h : SemicontinuousAt r x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
-/
theorem SemicontinuousAt.semicontinuousWithinAt (s : Set α)
    (h : SemicontinuousAt r x) : SemicontinuousWithinAt r s x := fun y hy =>
  Filter.Eventually.filter_mono nhdsWithin_le_nhds (h y hy)
/-
**SemicontinuousOn.semicontinuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SemicontinuousOn.semicontinuousWithinAt (h : SemicontinuousOn r s) (hx : x
 in s) : SemicontinuousWithinAt r s x
参数：h : SemicontinuousOn r s；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem SemicontinuousOn.semicontinuousWithinAt (h : SemicontinuousOn r s)
    (hx : x ∈ s) : SemicontinuousWithinAt r s x :=
  h x hx
/-
**SemicontinuousOn.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SemicontinuousOn.mono (h : SemicontinuousOn r s) (hst : t subseteq s) : Se
micontinuousOn r t
参数：h : SemicontinuousOn r s；hst : t subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousWithinAt.mono`：SemicontinuousWithinAt.mono (h : Semicontin
uousWithinAt r s x) (hst : t subseteq s) : SemicontinuousWithinAt r t x
-/
theorem SemicontinuousOn.mono (h : SemicontinuousOn r s) (hst : t ⊆ s) :
    SemicontinuousOn r t := fun x hx => (h x (hst hx)).mono hst
/-
**semicontinuousOn_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：semicontinuousOn_univ_iff : SemicontinuousOn r univ ↔ Semicontinuous r
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
theorem semicontinuousOn_univ_iff : SemicontinuousOn r univ ↔ Semicontinuous r := by
  simp [SemicontinuousOn, Semicontinuous, semicontinuousWithinAt_univ_iff]
/-
**semicontinuous_restrict_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace α] {r : α → β → P
rop} {s : Set α},   Semicontinuous (s.domRestrict r) ↔ SemicontinuousOn r s
参数：s.domRestrict r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SemicontinuousOn.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : Topologic
alSpace α] (r : α → β → Prop) (s : Set α),   SemicontinuousOn r s = ∀ x ∈ s, Sem
icontinuous…
· 使用定理 `Semicontinuous.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : Topological
Space α] (r : α → β → Prop),   Semicontinuous r = ∀ (x : α), SemicontinuousAt r 
x
· 使用定理 `SetCoe.forall`：SetCoe.forall {s : Set α} {p : s -> Prop} : (forall x : s
, p x) ↔ forall (x) (h : x in s), p ⟨x, h⟩
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `nhdsWithin_eq_map_subtype_coe`：nhdsWithin_eq_map_subtype_coe {s : Set α}
 {a : α} (h : a in s) : 𝓝[s] a = map ((↑) : s -> α) (𝓝 ⟨a, h⟩)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem semicontinuous_restrict_iff :
    Semicontinuous (s.domRestrict r) ↔ SemicontinuousOn r s := by
  rw [SemicontinuousOn, Semicontinuous, SetCoe.forall]
  refine forall₂_congr fun a ha ↦ forall₂_congr fun b _ ↦ ?_
  simp only [nhdsWithin_eq_map_subtype_coe ha, eventually_map, domRestrict]
/-
**Semicontinuous.semicontinuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Semicontinuous.semicontinuousAt (h : Semicontinuous r) (x : α) : Semiconti
nuousAt r x
参数：h : Semicontinuous r；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Semicontinuous.semicontinuousAt (h : Semicontinuous r) (x : α) :
    SemicontinuousAt r x :=
  h x
/-
**Semicontinuous.semicontinuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Semicontinuous.semicontinuousWithinAt (h : Semicontinuous r) (s : Set α) (
x : α) : SemicontinuousWithinAt r s x
参数：h : Semicontinuous r；s : Set α；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousAt.semicontinuousWithinAt`：SemicontinuousAt.semicontinuous
WithinAt (s : Set α) (h : SemicontinuousAt r x) : SemicontinuousWithinAt r s x
-/
theorem Semicontinuous.semicontinuousWithinAt (h : Semicontinuous r) (s : Set α)
    (x : α) : SemicontinuousWithinAt r s x :=
  (h x).semicontinuousWithinAt s
/-
**Semicontinuous.semicontinuousOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Semicontinuous.semicontinuousOn (h : Semicontinuous r) (s : Set α) : Semic
ontinuousOn r s
参数：h : Semicontinuous r；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Semicontinuous.semicontinuousWithinAt`：Semicontinuous.semicontinuousWith
inAt (h : Semicontinuous r) (s : Set α) (x : α) : SemicontinuousWithinAt r s x
-/
theorem Semicontinuous.semicontinuousOn (h : Semicontinuous r) (s : Set α) :
    SemicontinuousOn r s := fun x _hx => h.semicontinuousWithinAt s x
/-
**semicontinuous_iff_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：semicontinuous_iff_isOpen : Semicontinuous r ↔ forall b, IsOpen {x | r x b
}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
-/
theorem semicontinuous_iff_isOpen : Semicontinuous r ↔ ∀ b, IsOpen {x | r x b} := by
  exact ⟨fun h b ↦ by simpa [isOpen_iff_mem_nhds, Filter.Eventually] using fun x hx ↦ h x b hx,
    fun h x b hbx ↦ (h b).mem_nhds hbx⟩
/-
**Semicontinuous.isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Semicontinuous.isOpen (h : Semicontinuous r) (b : β) : IsOpen {x | r x b}
参数：h : Semicontinuous r；b : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `semicontinuous_iff_isOpen`：semicontinuous_iff_isOpen : Semicontinuous r 
↔ forall b, IsOpen {x | r x b}
-/
theorem Semicontinuous.isOpen (h : Semicontinuous r) (b : β) : IsOpen {x | r x b} :=
  semicontinuous_iff_isOpen.mp h b
/-
**SemicontinuousWithinAt.inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SemicontinuousWithinAt.inf {r' : α -> β -> Prop} (h : SemicontinuousWithin
At r s x) (h' : SemicontinuousWithinAt r' s x) : SemicontinuousWithinAt (r ⊓ r')
 s x
参数：h : SemicontinuousWithinAt r s x；h' : SemicontinuousWithinAt r' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
-/
theorem SemicontinuousWithinAt.inf {r' : α → β → Prop}
    (h : SemicontinuousWithinAt r s x) (h' : SemicontinuousWithinAt r' s x) :
    SemicontinuousWithinAt (r ⊓ r') s x := fun b ⟨hb, hb'⟩ ↦
  (h b hb).and (h' b hb')
/-
**SemicontinuousWithinAt.sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SemicontinuousWithinAt.sup {r' : α -> β -> Prop} (h : SemicontinuousWithin
At r s x) (h' : SemicontinuousWithinAt r' s x) : SemicontinuousWithinAt (r ⊔ r')
 s x
参数：h : SemicontinuousWithinAt r s x；h' : SemicontinuousWithinAt r' s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
-/
theorem SemicontinuousWithinAt.sup {r' : α → β → Prop}
    (h : SemicontinuousWithinAt r s x) (h' : SemicontinuousWithinAt r' s x) :
    SemicontinuousWithinAt (r ⊔ r') s x := by
  intro b hab
  obtain hb | hb' := hab
  · exact (h b hb).mono fun _ hx ↦ Or.inl hx
  · exact (h' b hb').mono fun _ hx ↦ Or.inr hx
/-
**SemicontinuousAt.inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SemicontinuousAt.inf {r' : α -> β -> Prop} (h : SemicontinuousAt r x) (h' 
: SemicontinuousAt r' x) : SemicontinuousAt (r ⊓ r') x
参数：h : SemicontinuousAt r x；h' : SemicontinuousAt r' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
-/
theorem SemicontinuousAt.inf {r' : α → β → Prop}
    (h : SemicontinuousAt r x) (h' : SemicontinuousAt r' x) :
    SemicontinuousAt (r ⊓ r') x := fun b ⟨hb, hb'⟩ ↦
  (h b hb).and (h' b hb')
/-
**SemicontinuousAt.sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SemicontinuousAt.sup {r' : α -> β -> Prop} (h : SemicontinuousAt r x) (h' 
: SemicontinuousAt r' x) : SemicontinuousAt (r ⊔ r') x
参数：h : SemicontinuousAt r x；h' : SemicontinuousAt r' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
-/
theorem SemicontinuousAt.sup {r' : α → β → Prop}
    (h : SemicontinuousAt r x) (h' : SemicontinuousAt r' x) :
    SemicontinuousAt (r ⊔ r') x := by
  intro b hab
  obtain hb | hb' := hab
  · exact (h b hb).mono fun _ hx ↦ Or.inl hx
  · exact (h' b hb').mono fun _ hx ↦ Or.inr hx
/-
**SemicontinuousOn.inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SemicontinuousOn.inf {r' : α -> β -> Prop} (h : SemicontinuousOn r s) (h' 
: SemicontinuousOn r' s) : SemicontinuousOn (r ⊓ r') s
参数：h : SemicontinuousOn r s；h' : SemicontinuousOn r' s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousWithinAt.inf`：SemicontinuousWithinAt.inf {r' : α -> β -> P
rop} (h : SemicontinuousWithinAt r s x) (h' : SemicontinuousWithinAt r' s x) : S
emicontinuousWit…
-/
theorem SemicontinuousOn.inf {r' : α → β → Prop}
    (h : SemicontinuousOn r s) (h' : SemicontinuousOn r' s) :
    SemicontinuousOn (r ⊓ r') s := fun x hx ↦ (h x hx).inf (h' x hx)
/-
**SemicontinuousOn.sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SemicontinuousOn.sup {r' : α -> β -> Prop} (h : SemicontinuousOn r s) (h' 
: SemicontinuousOn r' s) : SemicontinuousOn (r ⊔ r') s
参数：h : SemicontinuousOn r s；h' : SemicontinuousOn r' s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousWithinAt.sup`：SemicontinuousWithinAt.sup {r' : α -> β -> P
rop} (h : SemicontinuousWithinAt r s x) (h' : SemicontinuousWithinAt r' s x) : S
emicontinuousWit…
-/
theorem SemicontinuousOn.sup {r' : α → β → Prop}
    (h : SemicontinuousOn r s) (h' : SemicontinuousOn r' s) :
    SemicontinuousOn (r ⊔ r') s := fun x hx ↦ (h x hx).sup (h' x hx)
/-
**Semicontinuous.inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Semicontinuous.inf {r' : α -> β -> Prop} (h : Semicontinuous r) (h' : Semi
continuous r') : Semicontinuous (r ⊓ r')
参数：h : Semicontinuous r；h' : Semicontinuous r'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousAt.inf`：SemicontinuousAt.inf {r' : α -> β -> Prop} (h : Se
micontinuousAt r x) (h' : SemicontinuousAt r' x) : SemicontinuousAt (r ⊓ r') x
-/
theorem Semicontinuous.inf {r' : α → β → Prop} (h : Semicontinuous r) (h' : Semicontinuous r') :
    Semicontinuous (r ⊓ r') := fun a ↦ (h a).inf (h' a)
/-
**Semicontinuous.sup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Semicontinuous.sup {r' : α -> β -> Prop} (h : Semicontinuous r) (h' : Semi
continuous r') : Semicontinuous (r ⊔ r')
参数：h : Semicontinuous r；h' : Semicontinuous r'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousAt.sup`：SemicontinuousAt.sup {r' : α -> β -> Prop} (h : Se
micontinuousAt r x) (h' : SemicontinuousAt r' x) : SemicontinuousAt (r ⊔ r') x
-/
theorem Semicontinuous.sup {r' : α → β → Prop} (h : Semicontinuous r) (h' : Semicontinuous r') :
    Semicontinuous (r ⊔ r') := fun a ↦ (h a).sup (h' a)

/-! #### Constants -/

/-
**SemicontinuousWithinAt.const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SemicontinuousWithinAt.const {f : β -> Prop} : SemicontinuousWithinAt (fun
 _x => f) s x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x

--- 原说明 ---
#### Constants
-/
theorem SemicontinuousWithinAt.const {f : β → Prop} : SemicontinuousWithinAt (fun _x => f) s x :=
  fun _y hy => Filter.Eventually.of_forall fun _x => hy
/-
**SemicontinuousAt.const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SemicontinuousAt.const {f : β -> Prop} : SemicontinuousAt (fun _x => f) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
theorem SemicontinuousAt.const {f : β → Prop} : SemicontinuousAt (fun _x => f) x := fun _y hy =>
  Filter.Eventually.of_forall fun _x => hy
/-
**SemicontinuousOn.const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SemicontinuousOn.const {f : β -> Prop} : SemicontinuousOn (fun _x => f) s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousWithinAt.const`：SemicontinuousWithinAt.const {f : β -> Pro
p} : SemicontinuousWithinAt (fun _x => f) s x
-/
theorem SemicontinuousOn.const {f : β → Prop} : SemicontinuousOn (fun _x => f) s := fun _x _hx =>
  SemicontinuousWithinAt.const
/-
**Semicontinuous.const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Semicontinuous.const {f : β -> Prop} : Semicontinuous fun _x : α => f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousAt.const`：SemicontinuousAt.const {f : β -> Prop} : Semicon
tinuousAt (fun _x => f) x
-/
theorem Semicontinuous.const {f : β → Prop} : Semicontinuous fun _x : α => f := fun _x =>
  SemicontinuousAt.const

/-! ### Precomposition with a continuous map -/

variable {x : γ} {g : γ → α} {s : Set γ} {t : Set α}

/-
**SemicontinuousWithinAt.comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SemicontinuousWithinAt.comp (h : SemicontinuousWithinAt r t (g x)) (hg : C
ontinuousWithinAt g s x) (hst : Set.MapsTo g s t) : SemicontinuousWithinAt (r ∘ 
g) s x
参数：h : SemicontinuousWithinAt r t (g x)；hg : ContinuousWithinAt g s x；hst : Set.
MapsTo g s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.tendsto_nhdsWithin`：ContinuousWithinAt.tendsto_nhdsWi
thin {t : Set β} (h : ContinuousWithinAt f s x) (ht : MapsTo f s t) : Tendsto f 
(𝓝[s] x) (𝓝[t] f x)
-/
lemma SemicontinuousWithinAt.comp (h : SemicontinuousWithinAt r t (g x))
    (hg : ContinuousWithinAt g s x) (hst : Set.MapsTo g s t) :
    SemicontinuousWithinAt (r ∘ g) s x :=
  (hg.tendsto_nhdsWithin hst <| h · ·)
/-
**SemicontinuousOn.comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SemicontinuousOn.comp {r : α -> β -> Prop} {γ : Type*} [TopologicalSpace γ
] {g : γ -> α} {s : Set γ} {t : Set α} (h : SemicontinuousOn r t) (hg : Continuo
usOn g s) (hst : Set.MapsTo g s t) : SemicontinuousOn (r ∘ g) s
参数：h : SemicontinuousOn r t；hg : ContinuousOn g s；hst : Set.MapsTo g s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SemicontinuousWithinAt.comp`：SemicontinuousWithinAt.comp (h : Semicontin
uousWithinAt r t (g x)) (hg : ContinuousWithinAt g s x) (hst : Set.MapsTo g s t)
 : Semicontinuous…
-/
lemma SemicontinuousOn.comp {r : α → β → Prop} {γ : Type*}
    [TopologicalSpace γ] {g : γ → α} {s : Set γ} {t : Set α}
    (h : SemicontinuousOn r t) (hg : ContinuousOn g s)
    (hst : Set.MapsTo g s t) :
    SemicontinuousOn (r ∘ g) s :=
  fun x hx ↦ h (g x) (hst hx) |>.comp (hg x hx) hst
/-
**SemicontinuousAt.comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SemicontinuousAt.comp {r : α -> β -> Prop} {γ : Type*} [TopologicalSpace γ
] {x : γ} {g : γ -> α} (h : SemicontinuousAt r (g x)) (hg : ContinuousAt g x) : 
SemicontinuousAt (r ∘ g) x
参数：h : SemicontinuousAt r (g x)；hg : ContinuousAt g x。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma SemicontinuousAt.comp {r : α → β → Prop} {γ : Type*} [TopologicalSpace γ]
    {x : γ} {g : γ → α} (h : SemicontinuousAt r (g x)) (hg : ContinuousAt g x) :
    SemicontinuousAt (r ∘ g) x :=
  (hg <| h · ·)
/-
**Semicontinuous.comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Semicontinuous.comp {r : α -> β -> Prop} {γ : Type*} [TopologicalSpace γ] 
{g : γ -> α} (h : Semicontinuous r) (hg : Continuous g) : Semicontinuous (r ∘ g)
参数：h : Semicontinuous r；hg : Continuous g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SemicontinuousAt.comp`：SemicontinuousAt.comp {r : α -> β -> Prop} {γ : T
ype*} [TopologicalSpace γ] {x : γ} {g : γ -> α} (h : SemicontinuousAt r (g x)) (
hg : Contin…
· 使用定理 `Semicontinuous.semicontinuousAt`：Semicontinuous.semicontinuousAt (h : Se
micontinuous r) (x : α) : SemicontinuousAt r x
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
lemma Semicontinuous.comp {r : α → β → Prop} {γ : Type*} [TopologicalSpace γ]
    {g : γ → α} (h : Semicontinuous r) (hg : Continuous g) :
    Semicontinuous (r ∘ g) :=
  fun _ ↦ (h.semicontinuousAt _).comp hg.continuousAt

end Semicontinuous

section Preorder

/-! ## Lower and Upper Semicontinuity -/

variable [Preorder β] {f g : α → β} {x : α} {s t : Set α} {y z : β}

section Definitions

/- In https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/Semicontinuity.20definition.20for.20non-linear.20orders/with/436241797
it was suggested to redefine `LowerSemicontinuous` in a way that works better for partial orders.
The following example shows that this redefinition can still take place even in light of the
refactor in terms of `Semicontinuous`. -/

/-
**** 是 Mathlib 中的一个示例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/Semiconti
nuity.20definition.20for.20non-linear.20orders/with/436241797
it was suggested to redefine `LowerSemicontinuous` in a way that works better fo
r partial orders.
The following example shows that this redefinition can still take place even in 
light of the
refactor in terms of `Semicontinuous`.
-/
example : Semicontinuous (¬ f · ≤ ·) ↔ ∀ x y, (∃ᶠ x' in 𝓝 x, f x' ≤ y) → f x ≤ y := by
  simp_rw [Semicontinuous, SemicontinuousAt, ← not_frequently, not_imp_not]

/-- A real function `f` is lower semicontinuous at `x` within a set `s` if, for any `ε > 0`, for all
`x'` close enough to `x` in `s`, then `f x'` is at least `f x - ε`. We formulate this in a general
preordered space, using an arbitrary `y < f x` instead of `f x - ε`. -/
/-
**LowerSemicontinuousWithinAt** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：LowerSemicontinuousWithinAt (f : α -> β) (s : Set α) (x : α)
参数：f : α -> β；s : Set α；x : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A real function `f` is lower semicontinuous at `x` within a set `s` if, for any 
`ε > 0`, for all
`x'` close enough to `x` in `s`, then `f x'` is at least `f x - ε`. We formulate
 this in a general
preordered space, using an arbitrary `y < f x` instead of `f x - ε`.
-/
abbrev LowerSemicontinuousWithinAt (f : α → β) (s : Set α) (x : α) :=
  SemicontinuousWithinAt (f · > ·) s x

/-- A real function `f` is lower semicontinuous on a set `s` if, for any `ε > 0`, for any `x ∈ s`,
for all `x'` close enough to `x` in `s`, then `f x'` is at least `f x - ε`. We formulate this in
a general preordered space, using an arbitrary `y < f x` instead of `f x - ε`. -/
/-
**LowerSemicontinuousOn** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：LowerSemicontinuousOn (f : α -> β) (s : Set α)
参数：f : α -> β；s : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A real function `f` is lower semicontinuous on a set `s` if, for any `ε > 0`, fo
r any `x ∈ s`,
for all `x'` close enough to `x` in `s`, then `f x'` is at least `f x - ε`. We f
ormulate this in
a general preordered space, using an arbitrary `y < f x` instead of `f x - ε`.
-/
abbrev LowerSemicontinuousOn (f : α → β) (s : Set α) :=
  SemicontinuousOn (f · > ·) s

/-- A real function `f` is lower semicontinuous at `x` if, for any `ε > 0`, for all `x'` close
enough to `x`, then `f x'` is at least `f x - ε`. We formulate this in a general preordered space,
using an arbitrary `y < f x` instead of `f x - ε`. -/
/-
**LowerSemicontinuousAt** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：LowerSemicontinuousAt (f : α -> β) (x : α)
参数：f : α -> β；x : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A real function `f` is lower semicontinuous at `x` if, for any `ε > 0`, for all 
`x'` close
enough to `x`, then `f x'` is at least `f x - ε`. We formulate this in a general
 preordered space,
using an arbitrary `y < f x` instead of `f x - ε`.
-/
abbrev LowerSemicontinuousAt (f : α → β) (x : α) :=
  SemicontinuousAt (f · > ·) x

/-- A real function `f` is lower semicontinuous if, for any `ε > 0`, for any `x`, for all `x'` close
enough to `x`, then `f x'` is at least `f x - ε`. We formulate this in a general preordered space,
using an arbitrary `y < f x` instead of `f x - ε`. -/
/-
**LowerSemicontinuous** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：LowerSemicontinuous (f : α -> β)
参数：f : α -> β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A real function `f` is lower semicontinuous if, for any `ε > 0`, for any `x`, fo
r all `x'` close
enough to `x`, then `f x'` is at least `f x - ε`. We formulate this in a general
 preordered space,
using an arbitrary `y < f x` instead of `f x - ε`.
-/
abbrev LowerSemicontinuous (f : α → β) :=
  Semicontinuous (f · > ·)

/-- A real function `f` is upper semicontinuous at `x` within a set `s` if, for any `ε > 0`, for all
`x'` close enough to `x` in `s`, then `f x'` is at most `f x + ε`. We formulate this in a general
preordered space, using an arbitrary `y > f x` instead of `f x + ε`. -/
/-
**UpperSemicontinuousWithinAt** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：UpperSemicontinuousWithinAt (f : α -> β) (s : Set α) (x : α)
参数：f : α -> β；s : Set α；x : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A real function `f` is upper semicontinuous at `x` within a set `s` if, for any 
`ε > 0`, for all
`x'` close enough to `x` in `s`, then `f x'` is at most `f x + ε`. We formulate 
this in a general
preordered space, using an arbitrary `y > f x` instead of `f x + ε`.
-/
abbrev UpperSemicontinuousWithinAt (f : α → β) (s : Set α) (x : α) :=
  SemicontinuousWithinAt (f · < ·) s x

/-- A real function `f` is upper semicontinuous on a set `s` if, for any `ε > 0`, for any `x ∈ s`,
for all `x'` close enough to `x` in `s`, then `f x'` is at most `f x + ε`. We formulate this in a
general preordered space, using an arbitrary `y > f x` instead of `f x + ε`. -/
/-
**UpperSemicontinuousOn** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：UpperSemicontinuousOn (f : α -> β) (s : Set α)
参数：f : α -> β；s : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A real function `f` is upper semicontinuous on a set `s` if, for any `ε > 0`, fo
r any `x ∈ s`,
for all `x'` close enough to `x` in `s`, then `f x'` is at most `f x + ε`. We fo
rmulate this in a
general preordered space, using an arbitrary `y > f x` instead of `f x + ε`.
-/
abbrev UpperSemicontinuousOn (f : α → β) (s : Set α) :=
  SemicontinuousOn (f · < ·) s

/-- A real function `f` is upper semicontinuous at `x` if, for any `ε > 0`, for all `x'` close
enough to `x`, then `f x'` is at most `f x + ε`. We formulate this in a general preordered space,
using an arbitrary `y > f x` instead of `f x + ε`. -/
/-
**UpperSemicontinuousAt** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：UpperSemicontinuousAt (f : α -> β) (x : α)
参数：f : α -> β；x : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A real function `f` is upper semicontinuous at `x` if, for any `ε > 0`, for all 
`x'` close
enough to `x`, then `f x'` is at most `f x + ε`. We formulate this in a general 
preordered space,
using an arbitrary `y > f x` instead of `f x + ε`.
-/
abbrev UpperSemicontinuousAt (f : α → β) (x : α) :=
  SemicontinuousAt (f · < ·) x

/-- A real function `f` is upper semicontinuous if, for any `ε > 0`, for any `x`, for all `x'`
close enough to `x`, then `f x'` is at most `f x + ε`. We formulate this in a general preordered
space, using an arbitrary `y > f x` instead of `f x + ε`. -/
/-
**UpperSemicontinuous** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：UpperSemicontinuous (f : α -> β)
参数：f : α -> β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A real function `f` is upper semicontinuous if, for any `ε > 0`, for any `x`, fo
r all `x'`
close enough to `x`, then `f x'` is at most `f x + ε`. We formulate this in a ge
neral preordered
space, using an arbitrary `y > f x` instead of `f x + ε`.
-/
abbrev UpperSemicontinuous (f : α → β) :=
  Semicontinuous (f · < ·)
/-
**lowerSemicontinuousWithinAt_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lowerSemicontinuousWithinAt_iff {f : α -> β} {s : Set α} {x : α} : LowerSe
micontinuousWithinAt f s x ↔ forall y, y < f x -> forallᶠ x' in 𝓝[s] x, y < f x'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma lowerSemicontinuousWithinAt_iff {f : α → β} {s : Set α} {x : α} :
    LowerSemicontinuousWithinAt f s x ↔ ∀ y, y < f x → ∀ᶠ x' in 𝓝[s] x, y < f x' :=
  Iff.rfl
/-
**lowerSemicontinuousOn_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lowerSemicontinuousOn_iff {f : α -> β} {s : Set α} : LowerSemicontinuousOn
 f s ↔ forall x in s, LowerSemicontinuousWithinAt f s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma lowerSemicontinuousOn_iff {f : α → β} {s : Set α} :
    LowerSemicontinuousOn f s ↔ ∀ x ∈ s, LowerSemicontinuousWithinAt f s x :=
  Iff.rfl
/-
**lowerSemicontinuousAt_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lowerSemicontinuousAt_iff {f : α -> β} {x : α} : LowerSemicontinuousAt f x
 ↔ forall y, y < f x -> forallᶠ x' in 𝓝 x, y < f x'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma lowerSemicontinuousAt_iff {f : α → β} {x : α} :
    LowerSemicontinuousAt f x ↔ ∀ y, y < f x → ∀ᶠ x' in 𝓝 x, y < f x' :=
  Iff.rfl
/-
**lowerSemicontinuous_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lowerSemicontinuous_iff {f : α -> β} : LowerSemicontinuous f ↔ forall x, L
owerSemicontinuousAt f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma lowerSemicontinuous_iff {f : α → β} :
    LowerSemicontinuous f ↔ ∀ x, LowerSemicontinuousAt f x :=
  Iff.rfl
/-
**upperSemicontinuousWithinAt_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：upperSemicontinuousWithinAt_iff {f : α -> β} {s : Set α} {x : α} : UpperSe
micontinuousWithinAt f s x ↔ forall y, f x < y -> forallᶠ x' in 𝓝[s] x, f x' < y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma upperSemicontinuousWithinAt_iff {f : α → β} {s : Set α} {x : α} :
    UpperSemicontinuousWithinAt f s x ↔ ∀ y, f x < y → ∀ᶠ x' in 𝓝[s] x, f x' < y :=
  Iff.rfl
/-
**upperSemicontinuousOn_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：upperSemicontinuousOn_iff {f : α -> β} {s : Set α} : UpperSemicontinuousOn
 f s ↔ forall x in s, UpperSemicontinuousWithinAt f s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma upperSemicontinuousOn_iff {f : α → β} {s : Set α} :
    UpperSemicontinuousOn f s ↔ ∀ x ∈ s, UpperSemicontinuousWithinAt f s x :=
  Iff.rfl
/-
**upperSemicontinuousAt_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：upperSemicontinuousAt_iff {f : α -> β} {x : α} : UpperSemicontinuousAt f x
 ↔ forall y, f x < y -> forallᶠ x' in 𝓝 x, f x' < y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma upperSemicontinuousAt_iff {f : α → β} {x : α} :
    UpperSemicontinuousAt f x ↔ ∀ y, f x < y → ∀ᶠ x' in 𝓝 x, f x' < y :=
  Iff.rfl
/-
**upperSemicontinuous_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：upperSemicontinuous_iff {f : α -> β} : UpperSemicontinuous f ↔ forall x, U
pperSemicontinuousAt f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma upperSemicontinuous_iff {f : α → β} :
    UpperSemicontinuous f ↔ ∀ x, UpperSemicontinuousAt f x :=
  Iff.rfl

end Definitions

/-!
### Lower semicontinuous functions
-/

/-! #### Basic dot notation interface for lower semicontinuity -/

/-
**LowerSemicontinuousWithinAt.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LowerSemicontinuousWithinAt.mono (h : LowerSemicontinuousWithinAt f s x) (
hst : t subseteq s) : LowerSemicontinuousWithinAt f t x
参数：h : LowerSemicontinuousWithinAt f s x；hst : t subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousWithinAt.mono`：SemicontinuousWithinAt.mono (h : Semicontin
uousWithinAt r s x) (hst : t subseteq s) : SemicontinuousWithinAt r t x

--- 原说明 ---
#### Basic dot notation interface for lower semicontinuity
-/
theorem LowerSemicontinuousWithinAt.mono (h : LowerSemicontinuousWithinAt f s x) (hst : t ⊆ s) :
    LowerSemicontinuousWithinAt f t x :=
  SemicontinuousWithinAt.mono h hst
/-
**LowerSemicontinuousWithinAt.congr_of_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：LowerSemicontinuousWithinAt.congr_of_eventuallyEq {a : α} (h : LowerSemico
ntinuousWithinAt f s a) (has : a in s) (hfg : f =ᶠ[𝓝[s] a] g) : LowerSemicontinu
ousWithinAt g s a
参数：h : LowerSemicontinuousWithinAt f s a；has : a in s；hfg : f =ᶠ[𝓝[s] a] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousWithinAt.congr_of_eventuallyEq`：SemicontinuousWithinAt.con
gr_of_eventuallyEq {a : α} (h : SemicontinuousWithinAt r s a) (has : a in s) (hf
g : forallᶠ x in 𝓝[s] a, forall y,…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem LowerSemicontinuousWithinAt.congr_of_eventuallyEq {a : α}
    (h : LowerSemicontinuousWithinAt f s a)
    (has : a ∈ s) (hfg : f =ᶠ[𝓝[s] a] g) :
    LowerSemicontinuousWithinAt g s a :=
  SemicontinuousWithinAt.congr_of_eventuallyEq h has <| by
    filter_upwards [hfg] with x hx
    simp [hx]
/-
**lowerSemicontinuousWithinAt_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerSemicontinuousWithinAt_univ_iff : LowerSemicontinuousWithinAt f univ 
x ↔ LowerSemicontinuousAt f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `semicontinuousWithinAt_univ_iff`：semicontinuousWithinAt_univ_iff : Semic
ontinuousWithinAt r univ x ↔ SemicontinuousAt r x
-/
theorem lowerSemicontinuousWithinAt_univ_iff :
    LowerSemicontinuousWithinAt f univ x ↔ LowerSemicontinuousAt f x :=
  semicontinuousWithinAt_univ_iff
/-
**LowerSemicontinuousAt.lowerSemicontinuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：LowerSemicontinuousAt.lowerSemicontinuousWithinAt (s : Set α) (h : LowerSe
micontinuousAt f x) : LowerSemicontinuousWithinAt f s x
参数：s : Set α；h : LowerSemicontinuousAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousAt.semicontinuousWithinAt`：SemicontinuousAt.semicontinuous
WithinAt (s : Set α) (h : SemicontinuousAt r x) : SemicontinuousWithinAt r s x
-/
theorem LowerSemicontinuousAt.lowerSemicontinuousWithinAt (s : Set α)
    (h : LowerSemicontinuousAt f x) : LowerSemicontinuousWithinAt f s x :=
  h.semicontinuousWithinAt s
/-
**LowerSemicontinuousOn.lowerSemicontinuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：LowerSemicontinuousOn.lowerSemicontinuousWithinAt (h : LowerSemicontinuous
On f s) (hx : x in s) : LowerSemicontinuousWithinAt f s x
参数：h : LowerSemicontinuousOn f s；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousOn.semicontinuousWithinAt`：SemicontinuousOn.semicontinuous
WithinAt (h : SemicontinuousOn r s) (hx : x in s) : SemicontinuousWithinAt r s x
-/
theorem LowerSemicontinuousOn.lowerSemicontinuousWithinAt (h : LowerSemicontinuousOn f s)
    (hx : x ∈ s) : LowerSemicontinuousWithinAt f s x :=
  h.semicontinuousWithinAt hx
/-
**LowerSemicontinuousOn.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LowerSemicontinuousOn.mono (h : LowerSemicontinuousOn f s) (hst : t subset
eq s) : LowerSemicontinuousOn f t
参数：h : LowerSemicontinuousOn f s；hst : t subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousOn.mono`：SemicontinuousOn.mono (h : SemicontinuousOn r s) 
(hst : t subseteq s) : SemicontinuousOn r t
-/
theorem LowerSemicontinuousOn.mono (h : LowerSemicontinuousOn f s) (hst : t ⊆ s) :
    LowerSemicontinuousOn f t :=
  SemicontinuousOn.mono h hst
/-
**lowerSemicontinuousOn_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerSemicontinuousOn_univ_iff : LowerSemicontinuousOn f univ ↔ LowerSemic
ontinuous f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `semicontinuousOn_univ_iff`：semicontinuousOn_univ_iff : SemicontinuousOn 
r univ ↔ Semicontinuous r
-/
theorem lowerSemicontinuousOn_univ_iff : LowerSemicontinuousOn f univ ↔ LowerSemicontinuous f :=
  semicontinuousOn_univ_iff
/-
**lowerSemicontinuous_restrict_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace α] [inst_1 : Preo
rder β] {f : α → β} {s : Set α},   LowerSemicontinuous (s.domRestrict f) ↔ Lower
SemicontinuousOn f s
参数：s.domRestrict f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `semicontinuous_restrict_iff`：∀ {α : Type u_1} {β : Type u_2} [inst : Top
ologicalSpace α] {r : α → β → Prop} {s : Set α},   Semicontinuous (s.domRestrict
 r) ↔ Semicontinu…
-/
@[simp] theorem lowerSemicontinuous_restrict_iff :
    LowerSemicontinuous (s.domRestrict f) ↔ LowerSemicontinuousOn f s :=
  semicontinuous_restrict_iff (r := (f · > ·))
/-
**LowerSemicontinuous.lowerSemicontinuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LowerSemicontinuous.lowerSemicontinuousAt (h : LowerSemicontinuous f) (x :
 α) : LowerSemicontinuousAt f x
参数：h : LowerSemicontinuous f；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LowerSemicontinuous.lowerSemicontinuousAt (h : LowerSemicontinuous f) (x : α) :
    LowerSemicontinuousAt f x :=
  h x
/-
**LowerSemicontinuous.lowerSemicontinuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LowerSemicontinuous.lowerSemicontinuousWithinAt (h : LowerSemicontinuous f
) (s : Set α) (x : α) : LowerSemicontinuousWithinAt f s x
参数：h : LowerSemicontinuous f；s : Set α；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousAt.semicontinuousWithinAt`：SemicontinuousAt.semicontinuous
WithinAt (s : Set α) (h : SemicontinuousAt r x) : SemicontinuousWithinAt r s x
-/
theorem LowerSemicontinuous.lowerSemicontinuousWithinAt (h : LowerSemicontinuous f) (s : Set α)
    (x : α) : LowerSemicontinuousWithinAt f s x :=
  (h x).semicontinuousWithinAt s
/-
**LowerSemicontinuous.lowerSemicontinuousOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LowerSemicontinuous.lowerSemicontinuousOn (h : LowerSemicontinuous f) (s :
 Set α) : LowerSemicontinuousOn f s
参数：h : LowerSemicontinuous f；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Semicontinuous.semicontinuousOn`：Semicontinuous.semicontinuousOn (h : Se
micontinuous r) (s : Set α) : SemicontinuousOn r s
-/
theorem LowerSemicontinuous.lowerSemicontinuousOn (h : LowerSemicontinuous f) (s : Set α) :
    LowerSemicontinuousOn f s :=
  h.semicontinuousOn s

/-! #### Constants -/

/-
**lowerSemicontinuousWithinAt_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerSemicontinuousWithinAt_const : LowerSemicontinuousWithinAt (fun _x =>
 z) s x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousWithinAt.const`：SemicontinuousWithinAt.const {f : β -> Pro
p} : SemicontinuousWithinAt (fun _x => f) s x

--- 原说明 ---
#### Constants
-/
theorem lowerSemicontinuousWithinAt_const : LowerSemicontinuousWithinAt (fun _x => z) s x :=
  SemicontinuousWithinAt.const
/-
**lowerSemicontinuousAt_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerSemicontinuousAt_const : LowerSemicontinuousAt (fun _x => z) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousAt.const`：SemicontinuousAt.const {f : β -> Prop} : Semicon
tinuousAt (fun _x => f) x
-/
theorem lowerSemicontinuousAt_const : LowerSemicontinuousAt (fun _x => z) x :=
  SemicontinuousAt.const
/-
**lowerSemicontinuousOn_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerSemicontinuousOn_const : LowerSemicontinuousOn (fun _x => z) s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousOn.const`：SemicontinuousOn.const {f : β -> Prop} : Semicon
tinuousOn (fun _x => f) s
-/
theorem lowerSemicontinuousOn_const : LowerSemicontinuousOn (fun _x => z) s :=
  SemicontinuousOn.const
/-
**lowerSemicontinuous_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerSemicontinuous_const : LowerSemicontinuous fun _x : α => z
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Semicontinuous.const`：Semicontinuous.const {f : β -> Prop} : Semicontinu
ous fun _x : α => f
-/
theorem lowerSemicontinuous_const : LowerSemicontinuous fun _x : α => z :=
  Semicontinuous.const

/-! #### Composition -/
section

variable {g : γ → α} {x : γ} {t : Set γ}

/-
**LowerSemicontinuousWithinAt.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LowerSemicontinuousWithinAt.comp (hf : LowerSemicontinuousWithinAt f s (g 
x)) (hg : ContinuousWithinAt g t x) (hg' : MapsTo g t s) : LowerSemicontinuousWi
thinAt (f ∘ g) t x
参数：hf : LowerSemicontinuousWithinAt f s (g x)；hg : ContinuousWithinAt g t x；hg' 
: MapsTo g t s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SemicontinuousWithinAt.comp`：SemicontinuousWithinAt.comp (h : Semicontin
uousWithinAt r t (g x)) (hg : ContinuousWithinAt g s x) (hst : Set.MapsTo g s t)
 : Semicontinuous…
-/
theorem LowerSemicontinuousWithinAt.comp
    (hf : LowerSemicontinuousWithinAt f s (g x)) (hg : ContinuousWithinAt g t x)
    (hg' : MapsTo g t s) :
    LowerSemicontinuousWithinAt (f ∘ g) t x :=
  SemicontinuousWithinAt.comp hf hg hg'
/-
**LowerSemicontinuousAt.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LowerSemicontinuousAt.comp (hf : LowerSemicontinuousAt f (g x)) (hg : Cont
inuousAt g x) : LowerSemicontinuousAt (f ∘ g) x
参数：hf : LowerSemicontinuousAt f (g x)；hg : ContinuousAt g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SemicontinuousAt.comp`：SemicontinuousAt.comp {r : α -> β -> Prop} {γ : T
ype*} [TopologicalSpace γ] {x : γ} {g : γ -> α} (h : SemicontinuousAt r (g x)) (
hg : Contin…
-/
theorem LowerSemicontinuousAt.comp
    (hf : LowerSemicontinuousAt f (g x)) (hg : ContinuousAt g x) :
    LowerSemicontinuousAt (f ∘ g) x :=
  SemicontinuousAt.comp hf hg
/-
**LowerSemicontinuousOn.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LowerSemicontinuousOn.comp (hf : LowerSemicontinuousOn f s) (hg : Continuo
usOn g t) (hg' : MapsTo g t s) : LowerSemicontinuousOn (f ∘ g) t
参数：hf : LowerSemicontinuousOn f s；hg : ContinuousOn g t；hg' : MapsTo g t s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SemicontinuousOn.comp`：SemicontinuousOn.comp {r : α -> β -> Prop} {γ : T
ype*} [TopologicalSpace γ] {g : γ -> α} {s : Set γ} {t : Set α} (h : Semicontinu
ousOn r t) …
-/
theorem LowerSemicontinuousOn.comp
    (hf : LowerSemicontinuousOn f s) (hg : ContinuousOn g t) (hg' : MapsTo g t s) :
    LowerSemicontinuousOn (f ∘ g) t :=
  SemicontinuousOn.comp hf hg hg'
/-
**LowerSemicontinuous.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LowerSemicontinuous.comp (hf : LowerSemicontinuous f) (hg : Continuous g) 
: LowerSemicontinuous (f ∘ g)
参数：hf : LowerSemicontinuous f；hg : Continuous g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Semicontinuous.comp`：Semicontinuous.comp {r : α -> β -> Prop} {γ : Type*
} [TopologicalSpace γ] {g : γ -> α} (h : Semicontinuous r) (hg : Continuous g) :
 Semicont…
-/
theorem LowerSemicontinuous.comp
    (hf : LowerSemicontinuous f) (hg : Continuous g) : LowerSemicontinuous (f ∘ g) :=
  Semicontinuous.comp hf hg

end

/-!
### Upper semicontinuous functions
-/


/-! #### Basic dot notation interface for upper semicontinuity -/


/-
**UpperSemicontinuousWithinAt.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UpperSemicontinuousWithinAt.mono (h : UpperSemicontinuousWithinAt f s x) (
hst : t subseteq s) : UpperSemicontinuousWithinAt f t x
参数：h : UpperSemicontinuousWithinAt f s x；hst : t subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousWithinAt.mono`：SemicontinuousWithinAt.mono (h : Semicontin
uousWithinAt r s x) (hst : t subseteq s) : SemicontinuousWithinAt r t x

--- 原说明 ---
#### Basic dot notation interface for upper semicontinuity
-/
theorem UpperSemicontinuousWithinAt.mono (h : UpperSemicontinuousWithinAt f s x) (hst : t ⊆ s) :
    UpperSemicontinuousWithinAt f t x :=
  SemicontinuousWithinAt.mono h hst
/-
**UpperSemicontinuousWithinAt.congr_of_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：UpperSemicontinuousWithinAt.congr_of_eventuallyEq {a : α} (h : UpperSemico
ntinuousWithinAt f s a) (has : a in s) (hfg : forallᶠ x in nhdsWithin a s, f x =
 g x) : UpperSemicontinuousWithinAt g s a
参数：h : UpperSemicontinuousWithinAt f s a；has : a in s；hfg : forallᶠ x in nhdsWit
hin a s, f x = g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSemicontinuousWithinAt.congr_of_eventuallyEq`：LowerSemicontinuousWi
thinAt.congr_of_eventuallyEq {a : α} (h : LowerSemicontinuousWithinAt f s a) (ha
s : a in s) (hfg : f =ᶠ[𝓝[s] a] g) : Lo…
-/
theorem UpperSemicontinuousWithinAt.congr_of_eventuallyEq {a : α}
    (h : UpperSemicontinuousWithinAt f s a)
    (has : a ∈ s) (hfg : ∀ᶠ x in nhdsWithin a s, f x = g x) :
    UpperSemicontinuousWithinAt g s a :=
  LowerSemicontinuousWithinAt.congr_of_eventuallyEq (β := βᵒᵈ) h has hfg
/-
**upperSemicontinuousWithinAt_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperSemicontinuousWithinAt_univ_iff : UpperSemicontinuousWithinAt f univ 
x ↔ UpperSemicontinuousAt f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `semicontinuousWithinAt_univ_iff`：semicontinuousWithinAt_univ_iff : Semic
ontinuousWithinAt r univ x ↔ SemicontinuousAt r x
-/
theorem upperSemicontinuousWithinAt_univ_iff :
    UpperSemicontinuousWithinAt f univ x ↔ UpperSemicontinuousAt f x :=
  semicontinuousWithinAt_univ_iff
/-
**upperSemicontinuousOn_iff_restrict** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace α] [inst_1 : Preo
rder β] {f : α → β} {s : Set α},   UpperSemicontinuous (s.domRestrict f) ↔ Upper
SemicontinuousOn f s
参数：s.domRestrict f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lowerSemicontinuous_restrict_iff`：∀ {α : Type u_1} {β : Type u_2} [inst 
: TopologicalSpace α] [inst_1 : Preorder β] {f : α → β} {s : Set α},   LowerSemi
continuous (s.domRestr…
-/
@[simp] theorem upperSemicontinuousOn_iff_restrict {s : Set α} :
    UpperSemicontinuous (s.domRestrict f) ↔ UpperSemicontinuousOn f s :=
  lowerSemicontinuous_restrict_iff (β := βᵒᵈ)
/-
**UpperSemicontinuousAt.upperSemicontinuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：UpperSemicontinuousAt.upperSemicontinuousWithinAt (s : Set α) (h : UpperSe
micontinuousAt f x) : UpperSemicontinuousWithinAt f s x
参数：s : Set α；h : UpperSemicontinuousAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousAt.semicontinuousWithinAt`：SemicontinuousAt.semicontinuous
WithinAt (s : Set α) (h : SemicontinuousAt r x) : SemicontinuousWithinAt r s x
-/
theorem UpperSemicontinuousAt.upperSemicontinuousWithinAt (s : Set α)
    (h : UpperSemicontinuousAt f x) : UpperSemicontinuousWithinAt f s x :=
  h.semicontinuousWithinAt s
/-
**UpperSemicontinuousOn.upperSemicontinuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：UpperSemicontinuousOn.upperSemicontinuousWithinAt (h : UpperSemicontinuous
On f s) (hx : x in s) : UpperSemicontinuousWithinAt f s x
参数：h : UpperSemicontinuousOn f s；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem UpperSemicontinuousOn.upperSemicontinuousWithinAt (h : UpperSemicontinuousOn f s)
    (hx : x ∈ s) : UpperSemicontinuousWithinAt f s x :=
  h x hx
/-
**UpperSemicontinuousOn.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UpperSemicontinuousOn.mono (h : UpperSemicontinuousOn f s) (hst : t subset
eq s) : UpperSemicontinuousOn f t
参数：h : UpperSemicontinuousOn f s；hst : t subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousOn.mono`：SemicontinuousOn.mono (h : SemicontinuousOn r s) 
(hst : t subseteq s) : SemicontinuousOn r t
-/
theorem UpperSemicontinuousOn.mono (h : UpperSemicontinuousOn f s) (hst : t ⊆ s) :
    UpperSemicontinuousOn f t :=
  SemicontinuousOn.mono h hst
/-
**upperSemicontinuousOn_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperSemicontinuousOn_univ_iff : UpperSemicontinuousOn f univ ↔ UpperSemic
ontinuous f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `semicontinuousOn_univ_iff`：semicontinuousOn_univ_iff : SemicontinuousOn 
r univ ↔ Semicontinuous r
-/
theorem upperSemicontinuousOn_univ_iff : UpperSemicontinuousOn f univ ↔ UpperSemicontinuous f :=
  semicontinuousOn_univ_iff
/-
**UpperSemicontinuous.upperSemicontinuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UpperSemicontinuous.upperSemicontinuousAt (h : UpperSemicontinuous f) (x :
 α) : UpperSemicontinuousAt f x
参数：h : UpperSemicontinuous f；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem UpperSemicontinuous.upperSemicontinuousAt (h : UpperSemicontinuous f) (x : α) :
    UpperSemicontinuousAt f x :=
  h x
/-
**UpperSemicontinuous.upperSemicontinuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UpperSemicontinuous.upperSemicontinuousWithinAt (h : UpperSemicontinuous f
) (s : Set α) (x : α) : UpperSemicontinuousWithinAt f s x
参数：h : UpperSemicontinuous f；s : Set α；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousAt.semicontinuousWithinAt`：SemicontinuousAt.semicontinuous
WithinAt (s : Set α) (h : SemicontinuousAt r x) : SemicontinuousWithinAt r s x
-/
theorem UpperSemicontinuous.upperSemicontinuousWithinAt (h : UpperSemicontinuous f) (s : Set α)
    (x : α) : UpperSemicontinuousWithinAt f s x :=
  (h x).semicontinuousWithinAt s
/-
**UpperSemicontinuous.upperSemicontinuousOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UpperSemicontinuous.upperSemicontinuousOn (h : UpperSemicontinuous f) (s :
 Set α) : UpperSemicontinuousOn f s
参数：h : UpperSemicontinuous f；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Semicontinuous.semicontinuousOn`：Semicontinuous.semicontinuousOn (h : Se
micontinuous r) (s : Set α) : SemicontinuousOn r s
-/
theorem UpperSemicontinuous.upperSemicontinuousOn (h : UpperSemicontinuous f) (s : Set α) :
    UpperSemicontinuousOn f s :=
  h.semicontinuousOn s

/-! #### Constants -/

/-
**upperSemicontinuousWithinAt_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperSemicontinuousWithinAt_const : UpperSemicontinuousWithinAt (fun _x =>
 z) s x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousWithinAt.const`：SemicontinuousWithinAt.const {f : β -> Pro
p} : SemicontinuousWithinAt (fun _x => f) s x

--- 原说明 ---
#### Constants
-/
theorem upperSemicontinuousWithinAt_const : UpperSemicontinuousWithinAt (fun _x => z) s x :=
  SemicontinuousWithinAt.const
/-
**upperSemicontinuousAt_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperSemicontinuousAt_const : UpperSemicontinuousAt (fun _x => z) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousAt.const`：SemicontinuousAt.const {f : β -> Prop} : Semicon
tinuousAt (fun _x => f) x
-/
theorem upperSemicontinuousAt_const : UpperSemicontinuousAt (fun _x => z) x :=
  SemicontinuousAt.const
/-
**upperSemicontinuousOn_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperSemicontinuousOn_const : UpperSemicontinuousOn (fun _x => z) s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousOn.const`：SemicontinuousOn.const {f : β -> Prop} : Semicon
tinuousOn (fun _x => f) s
-/
theorem upperSemicontinuousOn_const : UpperSemicontinuousOn (fun _x => z) s :=
  SemicontinuousOn.const
/-
**upperSemicontinuous_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperSemicontinuous_const : UpperSemicontinuous fun _x : α => z
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Semicontinuous.const`：Semicontinuous.const {f : β -> Prop} : Semicontinu
ous fun _x : α => f
-/
theorem upperSemicontinuous_const : UpperSemicontinuous fun _x : α => z :=
  Semicontinuous.const

/-! #### Composition -/

section

variable {g : γ → α} {c : γ} {t : Set γ}

/-
**UpperSemicontinuousWithinAt.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UpperSemicontinuousWithinAt.comp (hf : UpperSemicontinuousWithinAt f s (g 
c)) (hg : ContinuousWithinAt g t c) (hg' : MapsTo g t s) : UpperSemicontinuousWi
thinAt (f ∘ g) t c
参数：hf : UpperSemicontinuousWithinAt f s (g c)；hg : ContinuousWithinAt g t c；hg' 
: MapsTo g t s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SemicontinuousWithinAt.comp`：SemicontinuousWithinAt.comp (h : Semicontin
uousWithinAt r t (g x)) (hg : ContinuousWithinAt g s x) (hst : Set.MapsTo g s t)
 : Semicontinuous…
-/
theorem UpperSemicontinuousWithinAt.comp
    (hf : UpperSemicontinuousWithinAt f s (g c)) (hg : ContinuousWithinAt g t c)
    (hg' : MapsTo g t s) :
    UpperSemicontinuousWithinAt (f ∘ g) t c :=
  SemicontinuousWithinAt.comp (r := (f · < ·)) hf hg hg' -- the elaboration aid is necessary.
/-
**UpperSemicontinuousAt.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UpperSemicontinuousAt.comp (hf : UpperSemicontinuousAt f (g c)) (hg : Cont
inuousAt g c) : UpperSemicontinuousAt (f ∘ g) c
参数：hf : UpperSemicontinuousAt f (g c)；hg : ContinuousAt g c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SemicontinuousAt.comp`：SemicontinuousAt.comp {r : α -> β -> Prop} {γ : T
ype*} [TopologicalSpace γ] {x : γ} {g : γ -> α} (h : SemicontinuousAt r (g x)) (
hg : Contin…
-/
theorem UpperSemicontinuousAt.comp
    (hf : UpperSemicontinuousAt f (g c)) (hg : ContinuousAt g c) :
    UpperSemicontinuousAt (f ∘ g) c :=
  SemicontinuousAt.comp (r := (f · < ·)) hf hg
/-
**UpperSemicontinuousOn.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UpperSemicontinuousOn.comp (hf : UpperSemicontinuousOn f s) (hg : Continuo
usOn g t) (hg' : MapsTo g t s) : UpperSemicontinuousOn (f ∘ g) t
参数：hf : UpperSemicontinuousOn f s；hg : ContinuousOn g t；hg' : MapsTo g t s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SemicontinuousOn.comp`：SemicontinuousOn.comp {r : α -> β -> Prop} {γ : T
ype*} [TopologicalSpace γ] {g : γ -> α} {s : Set γ} {t : Set α} (h : Semicontinu
ousOn r t) …
-/
theorem UpperSemicontinuousOn.comp
    (hf : UpperSemicontinuousOn f s) (hg : ContinuousOn g t) (hg' : MapsTo g t s) :
    UpperSemicontinuousOn (f ∘ g) t :=
  SemicontinuousOn.comp (r := (f · < ·)) hf hg hg'
/-
**UpperSemicontinuous.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UpperSemicontinuous.comp (hf : UpperSemicontinuous f) (hg : Continuous g) 
: UpperSemicontinuous (f ∘ g)
参数：hf : UpperSemicontinuous f；hg : Continuous g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Semicontinuous.comp`：Semicontinuous.comp {r : α -> β -> Prop} {γ : Type*
} [TopologicalSpace γ] {g : γ -> α} (h : Semicontinuous r) (hg : Continuous g) :
 Semicont…
-/
theorem UpperSemicontinuous.comp
    (hf : UpperSemicontinuous f) (hg : Continuous g) : UpperSemicontinuous (f ∘ g) :=
  Semicontinuous.comp (r := (f · < ·)) hf hg

end

end Preorder

section LinearOrder

variable [LinearOrder β] {f g : α → β} {x : α} {s : Set α}

/-
**lowerSemicontinuousWithinAt_iff_frequently** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lowerSemicontinuousWithinAt_iff_frequently : LowerSemicontinuousWithinAt f
 s x ↔ forall y, (existsᶠ x' in 𝓝[s] x, f x' <= y) -> f x <= y
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
lemma lowerSemicontinuousWithinAt_iff_frequently :
    LowerSemicontinuousWithinAt f s x ↔ ∀ y, (∃ᶠ x' in 𝓝[s] x, f x' ≤ y) → f x ≤ y := by
  simp [semicontinuousWithinAt_iff_frequently]

alias ⟨LowerSemicontinuousWithinAt.frequently, LowerSemicontinuousWithinAt.of_frequently⟩ :=
  lowerSemicontinuousWithinAt_iff_frequently
/-
**lowerSemicontinuousOn_iff_frequently** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lowerSemicontinuousOn_iff_frequently : LowerSemicontinuousOn f s ↔ forall 
x in s, forall y, (existsᶠ x' in 𝓝[s] x, f x' <= y) -> f x <= y
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
lemma lowerSemicontinuousOn_iff_frequently :
    LowerSemicontinuousOn f s ↔ ∀ x ∈ s, ∀ y, (∃ᶠ x' in 𝓝[s] x, f x' ≤ y) → f x ≤ y := by
  simp [semicontinuousOn_iff_frequently]

alias ⟨LowerSemicontinuousOn.frequently, LowerSemicontinuousOn.of_frequently⟩ :=
  lowerSemicontinuousOn_iff_frequently
/-
**lowerSemicontinuousAt_iff_frequently** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lowerSemicontinuousAt_iff_frequently : LowerSemicontinuousAt f x ↔ forall 
y, (existsᶠ x' in 𝓝 x, f x' <= y) -> f x <= y
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
lemma lowerSemicontinuousAt_iff_frequently :
    LowerSemicontinuousAt f x ↔ ∀ y, (∃ᶠ x' in 𝓝 x, f x' ≤ y) → f x ≤ y := by
  simp [semicontinuousAt_iff_frequently]

alias ⟨LowerSemicontinuousAt.frequently, LowerSemicontinuousAt.of_frequently⟩ :=
  lowerSemicontinuousAt_iff_frequently
/-
**lowerSemicontinuous_iff_frequently** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lowerSemicontinuous_iff_frequently : LowerSemicontinuous f ↔ forall x y, (
existsᶠ x' in 𝓝 x, f x' <= y) -> f x <= y
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
lemma lowerSemicontinuous_iff_frequently :
    LowerSemicontinuous f ↔ ∀ x y, (∃ᶠ x' in 𝓝 x, f x' ≤ y) → f x ≤ y := by
  simp [semicontinuous_iff_frequently]

alias ⟨LowerSemicontinuous.frequently, LowerSemicontinuous.of_frequently⟩ :=
  lowerSemicontinuous_iff_frequently
/-
**upperSemicontinuousWithinAt_iff_frequently** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：upperSemicontinuousWithinAt_iff_frequently : UpperSemicontinuousWithinAt f
 s x ↔ forall y, (existsᶠ x' in 𝓝[s] x, f x' >= y) -> f x >= y
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma upperSemicontinuousWithinAt_iff_frequently :
    UpperSemicontinuousWithinAt f s x ↔ ∀ y, (∃ᶠ x' in 𝓝[s] x, f x' ≥ y) → f x ≥ y := by
  simp [semicontinuousWithinAt_iff_frequently]

alias ⟨UpperSemicontinuousWithinAt.frequently, UpperSemicontinuousWithinAt.of_frequently⟩ :=
  upperSemicontinuousWithinAt_iff_frequently
/-
**upperSemicontinuousOn_iff_frequently** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：upperSemicontinuousOn_iff_frequently : UpperSemicontinuousOn f s ↔ forall 
x in s, forall y, (existsᶠ x' in 𝓝[s] x, f x' >= y) -> f x >= y
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma upperSemicontinuousOn_iff_frequently :
    UpperSemicontinuousOn f s ↔ ∀ x ∈ s, ∀ y, (∃ᶠ x' in 𝓝[s] x, f x' ≥ y) → f x ≥ y := by
  simp [semicontinuousOn_iff_frequently]

alias ⟨UpperSemicontinuousOn.frequently, UpperSemicontinuousOn.of_frequently⟩ :=
  upperSemicontinuousOn_iff_frequently
/-
**upperSemicontinuousAt_iff_frequently** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：upperSemicontinuousAt_iff_frequently : UpperSemicontinuousAt f x ↔ forall 
y, (existsᶠ x' in 𝓝 x, f x' >= y) -> f x >= y
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma upperSemicontinuousAt_iff_frequently :
    UpperSemicontinuousAt f x ↔ ∀ y, (∃ᶠ x' in 𝓝 x, f x' ≥ y) → f x ≥ y := by
  simp [semicontinuousAt_iff_frequently]

alias ⟨UpperSemicontinuousAt.frequently, UpperSemicontinuousAt.of_frequently⟩ :=
  upperSemicontinuousAt_iff_frequently
/-
**upperSemicontinuous_iff_frequently** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：upperSemicontinuous_iff_frequently : UpperSemicontinuous f ↔ forall x y, (
existsᶠ x' in 𝓝 x, f x' >= y) -> f x >= y
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma upperSemicontinuous_iff_frequently :
    UpperSemicontinuous f ↔ ∀ x y, (∃ᶠ x' in 𝓝 x, f x' ≥ y) → f x ≥ y := by
  simp [semicontinuous_iff_frequently]

alias ⟨UpperSemicontinuous.frequently, UpperSemicontinuous.of_frequently⟩ :=
  upperSemicontinuous_iff_frequently

end LinearOrder

section Hemi

/-! ## Lower and Upper Hemicontinuity -/

variable [TopologicalSpace β]

section Definitions

/-- A function `f : α → Set β` is lower hemicontinuous at `x` within a set `s` if, whenever `t` is
an open set intersecting `f x`, then `t` also intersects `f x'` for all `x'` sufficiently close to
`x` within `s`. -/
/-
**LowerHemicontinuousWithinAt** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：LowerHemicontinuousWithinAt (f : α -> Set β) (s : Set α) (x : α)
参数：f : α -> Set β；s : Set α；x : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f : α → Set β` is lower hemicontinuous at `x` within a set `s` if, w
henever `t` is
an open set intersecting `f x`, then `t` also intersects `f x'` for all `x'` suf
ficiently close to
`x` within `s`.
-/
abbrev LowerHemicontinuousWithinAt (f : α → Set β) (s : Set α) (x : α) :=
  SemicontinuousWithinAt (fun x t ↦ IsOpen t ∧ ((f x) ∩ t).Nonempty) s x

/-- A function `f : α → Set β` is lower hemicontinuous on a set `s` if, whenever `x ∈ s` and `t` is
an open set intersecting `f x`, then `t` also intersects `f x'` for all `x'` sufficiently close to
`x` within `s`. -/
/-
**LowerHemicontinuousOn** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：LowerHemicontinuousOn (f : α -> Set β) (s : Set α)
参数：f : α -> Set β；s : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f : α → Set β` is lower hemicontinuous on a set `s` if, whenever `x 
∈ s` and `t` is
an open set intersecting `f x`, then `t` also intersects `f x'` for all `x'` suf
ficiently close to
`x` within `s`.
-/
abbrev LowerHemicontinuousOn (f : α → Set β) (s : Set α) :=
  SemicontinuousOn (fun x t ↦ IsOpen t ∧ ((f x) ∩ t).Nonempty) s

/-- A function `f : α → Set β` is lower hemicontinuous at `x` if, whenever `t` is an open set
intersecting `f x`, then `t` also intersects `f x'` for all `x'` sufficiently close to `x`. -/
/-
**LowerHemicontinuousAt** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：LowerHemicontinuousAt (f : α -> Set β) (x : α)
参数：f : α -> Set β；x : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f : α → Set β` is lower hemicontinuous at `x` if, whenever `t` is an
 open set
intersecting `f x`, then `t` also intersects `f x'` for all `x'` sufficiently cl
ose to `x`.
-/
abbrev LowerHemicontinuousAt (f : α → Set β) (x : α) :=
  SemicontinuousAt (fun x t ↦ IsOpen t ∧ ((f x) ∩ t).Nonempty) x

/-- A function `f : α → Set β` is lower hemicontinuous if, for any `x`, whenever `t` is an open set
intersecting `f x`, then `t` also intersects `f x'` for all `x'` sufficiently close to `x`. -/
/-
**LowerHemicontinuous** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：LowerHemicontinuous (f : α -> Set β)
参数：f : α -> Set β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f : α → Set β` is lower hemicontinuous if, for any `x`, whenever `t`
 is an open set
intersecting `f x`, then `t` also intersects `f x'` for all `x'` sufficiently cl
ose to `x`.
-/
abbrev LowerHemicontinuous (f : α → Set β) :=
  Semicontinuous (fun x t ↦ IsOpen t ∧ ((f x) ∩ t).Nonempty)

open scoped Topology

/-- A function `f : α → Set β` is upper hemicontinuous at `x` within a set `s` if, whenever `t` is
a neighborhood of `f x`, then `t` is a neighborhood of `f x'` for all `x'` sufficiently close to
`x` within `s`. -/
/-
**UpperHemicontinuousWithinAt** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：UpperHemicontinuousWithinAt (f : α -> Set β) (s : Set α) (x : α)
参数：f : α -> Set β；s : Set α；x : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f : α → Set β` is upper hemicontinuous at `x` within a set `s` if, w
henever `t` is
a neighborhood of `f x`, then `t` is a neighborhood of `f x'` for all `x'` suffi
ciently close to
`x` within `s`.
-/
abbrev UpperHemicontinuousWithinAt (f : α → Set β) (s : Set α) (x : α) :=
  SemicontinuousWithinAt (fun x t ↦ t ∈ 𝓝ˢ (f x)) s x

/-- A function `f : α → Set β` is upper hemicontinuous on a set `s` if, whenever `x ∈ s` and `t` is
a neighborhood of `f x`, then `t` is a neighborhood of `f x'` for all `x'` sufficiently close to
`x` within `s`. -/
/-
**UpperHemicontinuousOn** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：UpperHemicontinuousOn (f : α -> Set β) (s : Set α)
参数：f : α -> Set β；s : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f : α → Set β` is upper hemicontinuous on a set `s` if, whenever `x 
∈ s` and `t` is
a neighborhood of `f x`, then `t` is a neighborhood of `f x'` for all `x'` suffi
ciently close to
`x` within `s`.
-/
abbrev UpperHemicontinuousOn (f : α → Set β) (s : Set α) :=
  SemicontinuousOn (fun x t ↦ t ∈ 𝓝ˢ (f x)) s

/-- A function `f : α → Set β` is upper hemicontinuous at `x` if, whenever `t` is a neighborhood of
`f x`, then `t` is a neighborhood of `f x'` for all `x'` sufficiently close to `x`. -/
/-
**UpperHemicontinuousAt** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：UpperHemicontinuousAt (f : α -> Set β) (x : α)
参数：f : α -> Set β；x : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f : α → Set β` is upper hemicontinuous at `x` if, whenever `t` is a 
neighborhood of
`f x`, then `t` is a neighborhood of `f x'` for all `x'` sufficiently close to `
x`.
-/
abbrev UpperHemicontinuousAt (f : α → Set β) (x : α) :=
  SemicontinuousAt (fun x t ↦ t ∈ 𝓝ˢ (f x)) x

/-- A function `f : α → Set β` is upper hemicontinuous if, for all `x`, whenever `t` is a
neighborhood of `f x`, then `t` is a neighborhood of `f x'` for all `x'` sufficiently close
to `x`. -/
/-
**UpperHemicontinuous** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：UpperHemicontinuous (f : α -> Set β)
参数：f : α -> Set β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f : α → Set β` is upper hemicontinuous if, for all `x`, whenever `t`
 is a
neighborhood of `f x`, then `t` is a neighborhood of `f x'` for all `x'` suffici
ently close
to `x`.
-/
abbrev UpperHemicontinuous (f : α → Set β) :=
  Semicontinuous (fun x t ↦ t ∈ 𝓝ˢ (f x))
/-
**lowerHemicontinuousWithinAt_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lowerHemicontinuousWithinAt_iff {f : α -> Set β} {s : Set α} {x : α} : Low
erHemicontinuousWithinAt f s x ↔ forall u, IsOpen u -> ((f x) inter u).Nonempty 
-> forallᶠ x' in 𝓝[s] x, ((f x') inter u).Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SemicontinuousWithinAt.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : Top
ologicalSpace α] (r : α → β → Prop) (s : Set α) (x : α),   SemicontinuousWithinA
t r s x = ∀ (y : …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma lowerHemicontinuousWithinAt_iff {f : α → Set β} {s : Set α} {x : α} :
    LowerHemicontinuousWithinAt f s x ↔
      ∀ u, IsOpen u → ((f x) ∩ u).Nonempty → ∀ᶠ x' in 𝓝[s] x, ((f x') ∩ u).Nonempty := by
  simp +contextual [SemicontinuousWithinAt]
/-
**lowerHemicontinuousOn_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lowerHemicontinuousOn_iff {f : α -> Set β} {s : Set α} : LowerHemicontinuo
usOn f s ↔ forall x in s, LowerHemicontinuousWithinAt f s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma lowerHemicontinuousOn_iff {f : α → Set β} {s : Set α} :
    LowerHemicontinuousOn f s ↔ ∀ x ∈ s, LowerHemicontinuousWithinAt f s x :=
  Iff.rfl
/-
**lowerHemicontinuousAt_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lowerHemicontinuousAt_iff {f : α -> Set β} {x : α} : LowerHemicontinuousAt
 f x ↔ forall u, IsOpen u -> ((f x) inter u).Nonempty -> forallᶠ x' in 𝓝 x, ((f 
x') inter u).Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SemicontinuousAt.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : Topologic
alSpace α] (r : α → β → Prop) (x : α),   SemicontinuousAt r x = ∀ (y : β), r x y
 → ∀ᶠ (x' :…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma lowerHemicontinuousAt_iff {f : α → Set β} {x : α} :
    LowerHemicontinuousAt f x ↔
      ∀ u, IsOpen u → ((f x) ∩ u).Nonempty → ∀ᶠ x' in 𝓝 x, ((f x') ∩ u).Nonempty := by
  simp +contextual [SemicontinuousAt]
/-
**lowerHemicontinuous_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lowerHemicontinuous_iff {f : α -> Set β} : LowerHemicontinuous f ↔ forall 
x, LowerHemicontinuousAt f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma lowerHemicontinuous_iff {f : α → Set β} :
    LowerHemicontinuous f ↔ ∀ x, LowerHemicontinuousAt f x :=
  Iff.rfl
/-
**upperHemicontinuousWithinAt_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：upperHemicontinuousWithinAt_iff {f : α -> Set β} {s : Set α} {x : α} : Upp
erHemicontinuousWithinAt f s x ↔ forall t, t in 𝓝ˢ (f x) -> forallᶠ x' in 𝓝[s] x
, t in 𝓝ˢ (f x')
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma upperHemicontinuousWithinAt_iff {f : α → Set β} {s : Set α} {x : α} :
    UpperHemicontinuousWithinAt f s x ↔ ∀ t, t ∈ 𝓝ˢ (f x) → ∀ᶠ x' in 𝓝[s] x, t ∈ 𝓝ˢ (f x') :=
  Iff.rfl
/-
**upperHemicontinuousOn_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：upperHemicontinuousOn_iff {f : α -> Set β} {s : Set α} : UpperHemicontinuo
usOn f s ↔ forall x in s, UpperHemicontinuousWithinAt f s x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma upperHemicontinuousOn_iff {f : α → Set β} {s : Set α} :
    UpperHemicontinuousOn f s ↔ ∀ x ∈ s, UpperHemicontinuousWithinAt f s x :=
  Iff.rfl
/-
**upperHemicontinuousAt_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：upperHemicontinuousAt_iff {f : α -> Set β} {x : α} : UpperHemicontinuousAt
 f x ↔ forall t, t in 𝓝ˢ (f x) -> forallᶠ x' in 𝓝 x, t in 𝓝ˢ (f x')
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma upperHemicontinuousAt_iff {f : α → Set β} {x : α} :
    UpperHemicontinuousAt f x ↔ ∀ t, t ∈ 𝓝ˢ (f x) → ∀ᶠ x' in 𝓝 x, t ∈ 𝓝ˢ (f x') :=
  Iff.rfl
/-
**upperHemicontinuous_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：upperHemicontinuous_iff {f : α -> Set β} : UpperHemicontinuous f ↔ forall 
x, UpperHemicontinuousAt f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma upperHemicontinuous_iff {f : α → Set β} :
    UpperHemicontinuous f ↔ ∀ x, UpperHemicontinuousAt f x :=
  Iff.rfl

end Definitions

/-!
### Lower hemicontinuous functions
-/

/-! #### Basic dot notation interface for lower hemicontinuity -/

variable {f g : α → Set β} {x : α} {s t : Set α} {y z : Set β}

/-
**LowerHemicontinuousWithinAt.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LowerHemicontinuousWithinAt.mono (h : LowerHemicontinuousWithinAt f s x) (
hst : t subseteq s) : LowerHemicontinuousWithinAt f t x
参数：h : LowerHemicontinuousWithinAt f s x；hst : t subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousWithinAt.mono`：SemicontinuousWithinAt.mono (h : Semicontin
uousWithinAt r s x) (hst : t subseteq s) : SemicontinuousWithinAt r t x
-/
theorem LowerHemicontinuousWithinAt.mono (h : LowerHemicontinuousWithinAt f s x) (hst : t ⊆ s) :
    LowerHemicontinuousWithinAt f t x :=
  SemicontinuousWithinAt.mono h hst
/-
**LowerHemicontinuousWithinAt.congr_of_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：LowerHemicontinuousWithinAt.congr_of_eventuallyEq {a : α} (h : LowerHemico
ntinuousWithinAt f s a) (has : a in s) (hfg : f =ᶠ[𝓝[s] a] g) : LowerHemicontinu
ousWithinAt g s a
参数：h : LowerHemicontinuousWithinAt f s a；has : a in s；hfg : f =ᶠ[𝓝[s] a] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousWithinAt.congr_of_eventuallyEq`：SemicontinuousWithinAt.con
gr_of_eventuallyEq {a : α} (h : SemicontinuousWithinAt r s a) (has : a in s) (hf
g : forallᶠ x in 𝓝[s] a, forall y,…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem LowerHemicontinuousWithinAt.congr_of_eventuallyEq {a : α}
    (h : LowerHemicontinuousWithinAt f s a)
    (has : a ∈ s) (hfg : f =ᶠ[𝓝[s] a] g) :
    LowerHemicontinuousWithinAt g s a :=
  SemicontinuousWithinAt.congr_of_eventuallyEq h has <| by
    filter_upwards [hfg] with x hx
    simp [hx]
/-
**lowerHemicontinuousWithinAt_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerHemicontinuousWithinAt_univ_iff : LowerHemicontinuousWithinAt f univ 
x ↔ LowerHemicontinuousAt f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `semicontinuousWithinAt_univ_iff`：semicontinuousWithinAt_univ_iff : Semic
ontinuousWithinAt r univ x ↔ SemicontinuousAt r x
-/
theorem lowerHemicontinuousWithinAt_univ_iff :
    LowerHemicontinuousWithinAt f univ x ↔ LowerHemicontinuousAt f x :=
  semicontinuousWithinAt_univ_iff
/-
**LowerHemicontinuousAt.lowerHemicontinuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：LowerHemicontinuousAt.lowerHemicontinuousWithinAt (s : Set α) (h : LowerHe
micontinuousAt f x) : LowerHemicontinuousWithinAt f s x
参数：s : Set α；h : LowerHemicontinuousAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousAt.semicontinuousWithinAt`：SemicontinuousAt.semicontinuous
WithinAt (s : Set α) (h : SemicontinuousAt r x) : SemicontinuousWithinAt r s x
-/
theorem LowerHemicontinuousAt.lowerHemicontinuousWithinAt (s : Set α)
    (h : LowerHemicontinuousAt f x) : LowerHemicontinuousWithinAt f s x :=
  h.semicontinuousWithinAt s
/-
**LowerHemicontinuousOn.lowerHemicontinuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：LowerHemicontinuousOn.lowerHemicontinuousWithinAt (h : LowerHemicontinuous
On f s) (hx : x in s) : LowerHemicontinuousWithinAt f s x
参数：h : LowerHemicontinuousOn f s；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousOn.semicontinuousWithinAt`：SemicontinuousOn.semicontinuous
WithinAt (h : SemicontinuousOn r s) (hx : x in s) : SemicontinuousWithinAt r s x
-/
theorem LowerHemicontinuousOn.lowerHemicontinuousWithinAt (h : LowerHemicontinuousOn f s)
    (hx : x ∈ s) : LowerHemicontinuousWithinAt f s x :=
  h.semicontinuousWithinAt hx
/-
**LowerHemicontinuousOn.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LowerHemicontinuousOn.mono (h : LowerHemicontinuousOn f s) (hst : t subset
eq s) : LowerHemicontinuousOn f t
参数：h : LowerHemicontinuousOn f s；hst : t subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousOn.mono`：SemicontinuousOn.mono (h : SemicontinuousOn r s) 
(hst : t subseteq s) : SemicontinuousOn r t
-/
theorem LowerHemicontinuousOn.mono (h : LowerHemicontinuousOn f s) (hst : t ⊆ s) :
    LowerHemicontinuousOn f t :=
  SemicontinuousOn.mono h hst
/-
**lowerHemicontinuousOn_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lowerHemicontinuousOn_univ_iff : LowerHemicontinuousOn f univ ↔ LowerHemic
ontinuous f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `semicontinuousOn_univ_iff`：semicontinuousOn_univ_iff : SemicontinuousOn 
r univ ↔ Semicontinuous r
-/
theorem lowerHemicontinuousOn_univ_iff : LowerHemicontinuousOn f univ ↔ LowerHemicontinuous f :=
  semicontinuousOn_univ_iff
/-
**lowerHemicontinuous_restrict_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace α] [inst_1 : Topo
logicalSpace β] {f : α → Set β} {s : Set α},   LowerHemicontinuous (s.domRestric
t f) ↔ LowerHemicontinuousOn f s
参数：s.domRestrict f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `semicontinuous_restrict_iff`：∀ {α : Type u_1} {β : Type u_2} [inst : Top
ologicalSpace α] {r : α → β → Prop} {s : Set α},   Semicontinuous (s.domRestrict
 r) ↔ Semicontinu…
-/
@[simp] theorem lowerHemicontinuous_restrict_iff :
    LowerHemicontinuous (s.domRestrict f) ↔ LowerHemicontinuousOn f s :=
  semicontinuous_restrict_iff (r := (fun x t ↦ IsOpen t ∧ ((f x) ∩ t).Nonempty))
/-
**LowerHemicontinuous.lowerHemicontinuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LowerHemicontinuous.lowerHemicontinuousAt (h : LowerHemicontinuous f) (x :
 α) : LowerHemicontinuousAt f x
参数：h : LowerHemicontinuous f；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LowerHemicontinuous.lowerHemicontinuousAt (h : LowerHemicontinuous f) (x : α) :
    LowerHemicontinuousAt f x :=
  h x
/-
**LowerHemicontinuous.lowerHemicontinuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LowerHemicontinuous.lowerHemicontinuousWithinAt (h : LowerHemicontinuous f
) (s : Set α) (x : α) : LowerHemicontinuousWithinAt f s x
参数：h : LowerHemicontinuous f；s : Set α；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousAt.semicontinuousWithinAt`：SemicontinuousAt.semicontinuous
WithinAt (s : Set α) (h : SemicontinuousAt r x) : SemicontinuousWithinAt r s x
-/
theorem LowerHemicontinuous.lowerHemicontinuousWithinAt (h : LowerHemicontinuous f) (s : Set α)
    (x : α) : LowerHemicontinuousWithinAt f s x :=
  (h x).semicontinuousWithinAt s
/-
**LowerHemicontinuous.lowerHemicontinuousOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LowerHemicontinuous.lowerHemicontinuousOn (h : LowerHemicontinuous f) (s :
 Set α) : LowerHemicontinuousOn f s
参数：h : LowerHemicontinuous f；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Semicontinuous.semicontinuousOn`：Semicontinuous.semicontinuousOn (h : Se
micontinuous r) (s : Set α) : SemicontinuousOn r s
-/
theorem LowerHemicontinuous.lowerHemicontinuousOn (h : LowerHemicontinuous f) (s : Set α) :
    LowerHemicontinuousOn f s :=
  h.semicontinuousOn s
/-
**lowerHemicontinuousWithinAt_iff_frequently** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lowerHemicontinuousWithinAt_iff_frequently : LowerHemicontinuousWithinAt f
 s x ↔ forall t, IsClosed t -> (existsᶠ x' in 𝓝[s] x, f x' subseteq t) -> f x su
bseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `lowerHemicontinuousWithinAt_iff`：lowerHemicontinuousWithinAt_iff {f : α 
-> Set β} {s : Set α} {x : α} : LowerHemicontinuousWithinAt f s x ↔ forall u, Is
Open u -> ((f x) inte…
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `compl_surjective`：compl_surjective : Function.Surjective (compl : α -> α
)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma lowerHemicontinuousWithinAt_iff_frequently :
    LowerHemicontinuousWithinAt f s x ↔
      ∀ t, IsClosed t → (∃ᶠ x' in 𝓝[s] x, f x' ⊆ t) → f x ⊆ t := by
  rw [lowerHemicontinuousWithinAt_iff, compl_surjective.forall]
  simp only [isOpen_compl_iff]
  refine forall₂_congr fun t ht ↦ ?_
  rw [← not_imp_not]
  simp [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty, disjoint_compl_right_iff_subset]

alias ⟨LowerHemicontinuousWithinAt.frequently, LowerHemicontinuousWithinAt.of_frequently⟩ :=
  lowerHemicontinuousWithinAt_iff_frequently
/-
**lowerHemicontinuousOn_iff_frequently** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lowerHemicontinuousOn_iff_frequently : LowerHemicontinuousOn f s ↔ forall 
x in s, forall t, IsClosed t -> (existsᶠ x' in 𝓝[s] x, f x' subseteq t) -> f x s
ubseteq t
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
lemma lowerHemicontinuousOn_iff_frequently :
    LowerHemicontinuousOn f s ↔
      ∀ x ∈ s, ∀ t, IsClosed t → (∃ᶠ x' in 𝓝[s] x, f x' ⊆ t) → f x ⊆ t := by
  simp_rw [lowerHemicontinuousOn_iff, lowerHemicontinuousWithinAt_iff_frequently]

alias ⟨LowerHemicontinuousOn.frequently, LowerHemicontinuousOn.of_frequently⟩ :=
  lowerHemicontinuousOn_iff_frequently
/-
**lowerHemicontinuousAt_iff_frequently** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lowerHemicontinuousAt_iff_frequently : LowerHemicontinuousAt f x ↔ forall 
t, IsClosed t -> (existsᶠ x' in 𝓝 x, f x' subseteq t) -> f x subseteq t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lowerHemicontinuousWithinAt_univ_iff`：lowerHemicontinuousWithinAt_univ_i
ff : LowerHemicontinuousWithinAt f univ x ↔ LowerHemicontinuousAt f x
· 使用引理 `lowerHemicontinuousWithinAt_iff_frequently`：lowerHemicontinuousWithinAt_
iff_frequently : LowerHemicontinuousWithinAt f s x ↔ forall t, IsClosed t -> (ex
istsᶠ x' in 𝓝[s] x, f x' subsete…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma lowerHemicontinuousAt_iff_frequently :
    LowerHemicontinuousAt f x ↔ ∀ t, IsClosed t → (∃ᶠ x' in 𝓝 x, f x' ⊆ t) → f x ⊆ t := by
  rw [← lowerHemicontinuousWithinAt_univ_iff, lowerHemicontinuousWithinAt_iff_frequently]
  simp

alias ⟨LowerHemicontinuousAt.frequently, LowerHemicontinuousAt.of_frequently⟩ :=
  lowerHemicontinuousAt_iff_frequently
/-
**lowerHemicontinuous_iff_frequently** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lowerHemicontinuous_iff_frequently : LowerHemicontinuous f ↔ forall x t, I
sClosed t -> (existsᶠ x' in 𝓝 x, f x' subseteq t) -> f x subseteq t
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma lowerHemicontinuous_iff_frequently :
    LowerHemicontinuous f ↔ ∀ x t, IsClosed t → (∃ᶠ x' in 𝓝 x, f x' ⊆ t) → f x ⊆ t := by
  simp_rw [lowerHemicontinuous_iff, lowerHemicontinuousAt_iff_frequently]

alias ⟨LowerHemicontinuous.frequently, LowerHemicontinuous.of_frequently⟩ :=
  lowerHemicontinuous_iff_frequently

/-! #### Constants -/

/-
**LowerHemicontinuousWithinAt.const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LowerHemicontinuousWithinAt.const : LowerHemicontinuousWithinAt (fun _x =>
 z) s x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousWithinAt.const`：SemicontinuousWithinAt.const {f : β -> Pro
p} : SemicontinuousWithinAt (fun _x => f) s x

--- 原说明 ---
#### Constants
-/
theorem LowerHemicontinuousWithinAt.const : LowerHemicontinuousWithinAt (fun _x => z) s x :=
  SemicontinuousWithinAt.const
/-
**LowerHemicontinuousAt.const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LowerHemicontinuousAt.const : LowerHemicontinuousAt (fun _x => z) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousAt.const`：SemicontinuousAt.const {f : β -> Prop} : Semicon
tinuousAt (fun _x => f) x
-/
theorem LowerHemicontinuousAt.const : LowerHemicontinuousAt (fun _x => z) x :=
  SemicontinuousAt.const
/-
**LowerHemicontinuousOn.const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LowerHemicontinuousOn.const : LowerHemicontinuousOn (fun _x => z) s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousOn.const`：SemicontinuousOn.const {f : β -> Prop} : Semicon
tinuousOn (fun _x => f) s
-/
theorem LowerHemicontinuousOn.const : LowerHemicontinuousOn (fun _x => z) s :=
  SemicontinuousOn.const
/-
**LowerHemicontinuous.const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LowerHemicontinuous.const : LowerHemicontinuous fun _x : α => z
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Semicontinuous.const`：Semicontinuous.const {f : β -> Prop} : Semicontinu
ous fun _x : α => f
-/
theorem LowerHemicontinuous.const : LowerHemicontinuous fun _x : α => z :=
  Semicontinuous.const

/-! #### Composition -/
section

variable {g : γ → α} {x : γ} {t : Set γ}

/-
**LowerHemicontinuousWithinAt.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LowerHemicontinuousWithinAt.comp (hf : LowerHemicontinuousWithinAt f s (g 
x)) (hg : ContinuousWithinAt g t x) (hg' : MapsTo g t s) : LowerHemicontinuousWi
thinAt (f ∘ g) t x
参数：hf : LowerHemicontinuousWithinAt f s (g x)；hg : ContinuousWithinAt g t x；hg' 
: MapsTo g t s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SemicontinuousWithinAt.comp`：SemicontinuousWithinAt.comp (h : Semicontin
uousWithinAt r t (g x)) (hg : ContinuousWithinAt g s x) (hst : Set.MapsTo g s t)
 : Semicontinuous…
-/
theorem LowerHemicontinuousWithinAt.comp
    (hf : LowerHemicontinuousWithinAt f s (g x)) (hg : ContinuousWithinAt g t x)
    (hg' : MapsTo g t s) :
    LowerHemicontinuousWithinAt (f ∘ g) t x :=
  SemicontinuousWithinAt.comp hf hg hg'
/-
**LowerHemicontinuousAt.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LowerHemicontinuousAt.comp (hf : LowerHemicontinuousAt f (g x)) (hg : Cont
inuousAt g x) : LowerHemicontinuousAt (f ∘ g) x
参数：hf : LowerHemicontinuousAt f (g x)；hg : ContinuousAt g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SemicontinuousAt.comp`：SemicontinuousAt.comp {r : α -> β -> Prop} {γ : T
ype*} [TopologicalSpace γ] {x : γ} {g : γ -> α} (h : SemicontinuousAt r (g x)) (
hg : Contin…
-/
theorem LowerHemicontinuousAt.comp
    (hf : LowerHemicontinuousAt f (g x)) (hg : ContinuousAt g x) :
    LowerHemicontinuousAt (f ∘ g) x :=
  SemicontinuousAt.comp hf hg
/-
**LowerHemicontinuousOn.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LowerHemicontinuousOn.comp (hf : LowerHemicontinuousOn f s) (hg : Continuo
usOn g t) (hg' : MapsTo g t s) : LowerHemicontinuousOn (f ∘ g) t
参数：hf : LowerHemicontinuousOn f s；hg : ContinuousOn g t；hg' : MapsTo g t s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SemicontinuousOn.comp`：SemicontinuousOn.comp {r : α -> β -> Prop} {γ : T
ype*} [TopologicalSpace γ] {g : γ -> α} {s : Set γ} {t : Set α} (h : Semicontinu
ousOn r t) …
-/
theorem LowerHemicontinuousOn.comp
    (hf : LowerHemicontinuousOn f s) (hg : ContinuousOn g t) (hg' : MapsTo g t s) :
    LowerHemicontinuousOn (f ∘ g) t :=
  SemicontinuousOn.comp hf hg hg'
/-
**LowerHemicontinuous.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LowerHemicontinuous.comp (hf : LowerHemicontinuous f) (hg : Continuous g) 
: LowerHemicontinuous (f ∘ g)
参数：hf : LowerHemicontinuous f；hg : Continuous g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Semicontinuous.comp`：Semicontinuous.comp {r : α -> β -> Prop} {γ : Type*
} [TopologicalSpace γ] {g : γ -> α} (h : Semicontinuous r) (hg : Continuous g) :
 Semicont…
-/
theorem LowerHemicontinuous.comp
    (hf : LowerHemicontinuous f) (hg : Continuous g) : LowerHemicontinuous (f ∘ g) :=
  Semicontinuous.comp hf hg

end

/-!
### Upper hemicontinuous functions
-/

/-! #### Basic dot notation interface for upper hemicontinuity -/

/-
**UpperHemicontinuousWithinAt.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UpperHemicontinuousWithinAt.mono (h : UpperHemicontinuousWithinAt f s x) (
hst : t subseteq s) : UpperHemicontinuousWithinAt f t x
参数：h : UpperHemicontinuousWithinAt f s x；hst : t subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousWithinAt.mono`：SemicontinuousWithinAt.mono (h : Semicontin
uousWithinAt r s x) (hst : t subseteq s) : SemicontinuousWithinAt r t x

--- 原说明 ---
#### Basic dot notation interface for upper hemicontinuity
-/
theorem UpperHemicontinuousWithinAt.mono (h : UpperHemicontinuousWithinAt f s x) (hst : t ⊆ s) :
    UpperHemicontinuousWithinAt f t x :=
  SemicontinuousWithinAt.mono h hst
/-
**UpperHemicontinuousWithinAt.congr_of_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：UpperHemicontinuousWithinAt.congr_of_eventuallyEq {a : α} (h : UpperHemico
ntinuousWithinAt f s a) (has : a in s) (hfg : forallᶠ x in nhdsWithin a s, f x =
 g x) : UpperHemicontinuousWithinAt g s a
参数：h : UpperHemicontinuousWithinAt f s a；has : a in s；hfg : forallᶠ x in nhdsWit
hin a s, f x = g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousWithinAt.congr_of_eventuallyEq`：SemicontinuousWithinAt.con
gr_of_eventuallyEq {a : α} (h : SemicontinuousWithinAt r s a) (has : a in s) (hf
g : forallᶠ x in 𝓝[s] a, forall y,…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem UpperHemicontinuousWithinAt.congr_of_eventuallyEq {a : α}
    (h : UpperHemicontinuousWithinAt f s a)
    (has : a ∈ s) (hfg : ∀ᶠ x in nhdsWithin a s, f x = g x) :
    UpperHemicontinuousWithinAt g s a :=
  SemicontinuousWithinAt.congr_of_eventuallyEq h has <| by
    filter_upwards [hfg] with x hx
    simp [hx]
/-
**upperHemicontinuousWithinAt_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperHemicontinuousWithinAt_univ_iff : UpperHemicontinuousWithinAt f univ 
x ↔ UpperHemicontinuousAt f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `semicontinuousWithinAt_univ_iff`：semicontinuousWithinAt_univ_iff : Semic
ontinuousWithinAt r univ x ↔ SemicontinuousAt r x
-/
theorem upperHemicontinuousWithinAt_univ_iff :
    UpperHemicontinuousWithinAt f univ x ↔ UpperHemicontinuousAt f x :=
  semicontinuousWithinAt_univ_iff
/-
**upperHemicontinuousOn_iff_restrict** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace α] [inst_1 : Topo
logicalSpace β] {f : α → Set β} {s : Set α},   UpperHemicontinuous (s.domRestric
t f) ↔ UpperHemicontinuousOn f s
参数：s.domRestrict f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `semicontinuous_restrict_iff`：∀ {α : Type u_1} {β : Type u_2} [inst : Top
ologicalSpace α] {r : α → β → Prop} {s : Set α},   Semicontinuous (s.domRestrict
 r) ↔ Semicontinu…
-/
@[simp] theorem upperHemicontinuousOn_iff_restrict {s : Set α} :
    UpperHemicontinuous (s.domRestrict f) ↔ UpperHemicontinuousOn f s :=
  semicontinuous_restrict_iff (r := (fun x t ↦ t ∈ 𝓝ˢ (f x)))
/-
**UpperHemicontinuousAt.upperHemicontinuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：UpperHemicontinuousAt.upperHemicontinuousWithinAt (s : Set α) (h : UpperHe
micontinuousAt f x) : UpperHemicontinuousWithinAt f s x
参数：s : Set α；h : UpperHemicontinuousAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousAt.semicontinuousWithinAt`：SemicontinuousAt.semicontinuous
WithinAt (s : Set α) (h : SemicontinuousAt r x) : SemicontinuousWithinAt r s x
-/
theorem UpperHemicontinuousAt.upperHemicontinuousWithinAt (s : Set α)
    (h : UpperHemicontinuousAt f x) : UpperHemicontinuousWithinAt f s x :=
  h.semicontinuousWithinAt s
/-
**UpperHemicontinuousOn.upperHemicontinuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：UpperHemicontinuousOn.upperHemicontinuousWithinAt (h : UpperHemicontinuous
On f s) (hx : x in s) : UpperHemicontinuousWithinAt f s x
参数：h : UpperHemicontinuousOn f s；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem UpperHemicontinuousOn.upperHemicontinuousWithinAt (h : UpperHemicontinuousOn f s)
    (hx : x ∈ s) : UpperHemicontinuousWithinAt f s x :=
  h x hx
/-
**UpperHemicontinuousOn.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UpperHemicontinuousOn.mono (h : UpperHemicontinuousOn f s) (hst : t subset
eq s) : UpperHemicontinuousOn f t
参数：h : UpperHemicontinuousOn f s；hst : t subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousOn.mono`：SemicontinuousOn.mono (h : SemicontinuousOn r s) 
(hst : t subseteq s) : SemicontinuousOn r t
-/
theorem UpperHemicontinuousOn.mono (h : UpperHemicontinuousOn f s) (hst : t ⊆ s) :
    UpperHemicontinuousOn f t :=
  SemicontinuousOn.mono h hst
/-
**upperHemicontinuousOn_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：upperHemicontinuousOn_univ_iff : UpperHemicontinuousOn f univ ↔ UpperHemic
ontinuous f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `semicontinuousOn_univ_iff`：semicontinuousOn_univ_iff : SemicontinuousOn 
r univ ↔ Semicontinuous r
-/
theorem upperHemicontinuousOn_univ_iff : UpperHemicontinuousOn f univ ↔ UpperHemicontinuous f :=
  semicontinuousOn_univ_iff
/-
**UpperHemicontinuous.upperHemicontinuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UpperHemicontinuous.upperHemicontinuousAt (h : UpperHemicontinuous f) (x :
 α) : UpperHemicontinuousAt f x
参数：h : UpperHemicontinuous f；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem UpperHemicontinuous.upperHemicontinuousAt (h : UpperHemicontinuous f) (x : α) :
    UpperHemicontinuousAt f x :=
  h x
/-
**UpperHemicontinuous.upperHemicontinuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UpperHemicontinuous.upperHemicontinuousWithinAt (h : UpperHemicontinuous f
) (s : Set α) (x : α) : UpperHemicontinuousWithinAt f s x
参数：h : UpperHemicontinuous f；s : Set α；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousAt.semicontinuousWithinAt`：SemicontinuousAt.semicontinuous
WithinAt (s : Set α) (h : SemicontinuousAt r x) : SemicontinuousWithinAt r s x
-/
theorem UpperHemicontinuous.upperHemicontinuousWithinAt (h : UpperHemicontinuous f) (s : Set α)
    (x : α) : UpperHemicontinuousWithinAt f s x :=
  (h x).semicontinuousWithinAt s
/-
**UpperHemicontinuous.upperHemicontinuousOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UpperHemicontinuous.upperHemicontinuousOn (h : UpperHemicontinuous f) (s :
 Set α) : UpperHemicontinuousOn f s
参数：h : UpperHemicontinuous f；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Semicontinuous.semicontinuousOn`：Semicontinuous.semicontinuousOn (h : Se
micontinuous r) (s : Set α) : SemicontinuousOn r s
-/
theorem UpperHemicontinuous.upperHemicontinuousOn (h : UpperHemicontinuous f) (s : Set α) :
    UpperHemicontinuousOn f s :=
  h.semicontinuousOn s
/-
**upperHemicontinuousWithinAt_iff_frequently** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：upperHemicontinuousWithinAt_iff_frequently : UpperHemicontinuousWithinAt f
 s x ↔ forall t, IsClosed t -> (existsᶠ x' in 𝓝[s] x, ((f x') inter t).Nonempty)
 -> ((f x) inter t).Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UpperHemicontinuousWithinAt.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst 
: TopologicalSpace α] [inst_1 : TopologicalSpace β] (f : α → Set β) (s : Set α) 
  (x : α), UpperHemico…
· 使用引理 `semicontinuousWithinAt_iff_frequently`：semicontinuousWithinAt_iff_freque
ntly : SemicontinuousWithinAt r s x ↔ forall y, (existsᶠ x' in 𝓝[s] x, ¬ r x' y)
 -> ¬ r x y
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `compl_surjective`：compl_surjective : Function.Surjective (compl : α -> α
)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `interior_compl`：interior_compl : interior sᶜ = (closure s)ᶜ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma upperHemicontinuousWithinAt_iff_frequently :
    UpperHemicontinuousWithinAt f s x ↔
      ∀ t, IsClosed t → (∃ᶠ x' in 𝓝[s] x, ((f x') ∩ t).Nonempty) → ((f x) ∩ t).Nonempty := by
  rw [UpperHemicontinuousWithinAt, semicontinuousWithinAt_iff_frequently, compl_surjective.forall]
  simp [← subset_interior_iff_mem_nhdsSet, not_subset, forall_isClosed_iff, inter_nonempty]

alias ⟨UpperHemicontinuousWithinAt.frequently, UpperHemicontinuousWithinAt.of_frequently⟩ :=
  upperHemicontinuousWithinAt_iff_frequently
/-
**upperHemicontinuousOn_iff_frequently** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：upperHemicontinuousOn_iff_frequently : UpperHemicontinuousOn f s ↔ forall 
x in s, forall t, IsClosed t -> (existsᶠ x' in 𝓝[s] x, ((f x') inter t).Nonempty
) -> ((f x) inter t).Nonempty
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
lemma upperHemicontinuousOn_iff_frequently :
    UpperHemicontinuousOn f s ↔ ∀ x ∈ s, ∀ t, IsClosed t →
      (∃ᶠ x' in 𝓝[s] x, ((f x') ∩ t).Nonempty) → ((f x) ∩ t).Nonempty := by
  simp_rw [upperHemicontinuousOn_iff, upperHemicontinuousWithinAt_iff_frequently]

alias ⟨UpperHemicontinuousOn.frequently, UpperHemicontinuousOn.of_frequently⟩ :=
  upperHemicontinuousOn_iff_frequently
/-
**upperHemicontinuousAt_iff_frequently** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：upperHemicontinuousAt_iff_frequently : UpperHemicontinuousAt f x ↔ forall 
t, IsClosed t -> (existsᶠ x' in 𝓝 x, ((f x') inter t).Nonempty) -> ((f x) inter 
t).Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `upperHemicontinuousWithinAt_univ_iff`：upperHemicontinuousWithinAt_univ_i
ff : UpperHemicontinuousWithinAt f univ x ↔ UpperHemicontinuousAt f x
· 使用引理 `upperHemicontinuousWithinAt_iff_frequently`：upperHemicontinuousWithinAt_
iff_frequently : UpperHemicontinuousWithinAt f s x ↔ forall t, IsClosed t -> (ex
istsᶠ x' in 𝓝[s] x, ((f x') inte…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma upperHemicontinuousAt_iff_frequently :
    UpperHemicontinuousAt f x ↔
      ∀ t, IsClosed t → (∃ᶠ x' in 𝓝 x, ((f x') ∩ t).Nonempty) → ((f x) ∩ t).Nonempty := by
  rw [← upperHemicontinuousWithinAt_univ_iff, upperHemicontinuousWithinAt_iff_frequently]
  simp

alias ⟨UpperHemicontinuousAt.frequently, UpperHemicontinuousAt.of_frequently⟩ :=
  upperHemicontinuousAt_iff_frequently
/-
**upperHemicontinuous_iff_frequently** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：upperHemicontinuous_iff_frequently : UpperHemicontinuous f ↔ forall x t, I
sClosed t -> (existsᶠ x' in 𝓝 x, ((f x') inter t).Nonempty) -> ((f x) inter t).N
onempty
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma upperHemicontinuous_iff_frequently :
    UpperHemicontinuous f ↔
      ∀ x t, IsClosed t → (∃ᶠ x' in 𝓝 x, ((f x') ∩ t).Nonempty) → ((f x) ∩ t).Nonempty := by
  simp_rw [upperHemicontinuous_iff, upperHemicontinuousAt_iff_frequently]

alias ⟨UpperHemicontinuous.frequently, UpperHemicontinuous.of_frequently⟩ :=
  upperHemicontinuous_iff_frequently

/-! #### Constants -/

/-
**UpperHemicontinuousWithinAt.const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UpperHemicontinuousWithinAt.const : UpperHemicontinuousWithinAt (fun _x =>
 z) s x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousWithinAt.const`：SemicontinuousWithinAt.const {f : β -> Pro
p} : SemicontinuousWithinAt (fun _x => f) s x

--- 原说明 ---
#### Constants
-/
theorem UpperHemicontinuousWithinAt.const : UpperHemicontinuousWithinAt (fun _x => z) s x :=
  SemicontinuousWithinAt.const
/-
**UpperHemicontinuousAt.const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UpperHemicontinuousAt.const : UpperHemicontinuousAt (fun _x => z) x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousAt.const`：SemicontinuousAt.const {f : β -> Prop} : Semicon
tinuousAt (fun _x => f) x
-/
theorem UpperHemicontinuousAt.const : UpperHemicontinuousAt (fun _x => z) x :=
  SemicontinuousAt.const
/-
**UpperHemicontinuousOn.const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UpperHemicontinuousOn.const : UpperHemicontinuousOn (fun _x => z) s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousOn.const`：SemicontinuousOn.const {f : β -> Prop} : Semicon
tinuousOn (fun _x => f) s
-/
theorem UpperHemicontinuousOn.const : UpperHemicontinuousOn (fun _x => z) s :=
  SemicontinuousOn.const
/-
**UpperHemicontinuous.const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UpperHemicontinuous.const : UpperHemicontinuous fun _x : α => z
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Semicontinuous.const`：Semicontinuous.const {f : β -> Prop} : Semicontinu
ous fun _x : α => f
-/
theorem UpperHemicontinuous.const : UpperHemicontinuous fun _x : α => z :=
  Semicontinuous.const

/-! #### Composition -/

section

variable {g : γ → α} {c : γ} {t : Set γ}

/-
**UpperHemicontinuousWithinAt.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UpperHemicontinuousWithinAt.comp (hf : UpperHemicontinuousWithinAt f s (g 
c)) (hg : ContinuousWithinAt g t c) (hg' : MapsTo g t s) : UpperHemicontinuousWi
thinAt (f ∘ g) t c
参数：hf : UpperHemicontinuousWithinAt f s (g c)；hg : ContinuousWithinAt g t c；hg' 
: MapsTo g t s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SemicontinuousWithinAt.comp`：SemicontinuousWithinAt.comp (h : Semicontin
uousWithinAt r t (g x)) (hg : ContinuousWithinAt g s x) (hst : Set.MapsTo g s t)
 : Semicontinuous…
-/
theorem UpperHemicontinuousWithinAt.comp
    (hf : UpperHemicontinuousWithinAt f s (g c)) (hg : ContinuousWithinAt g t c)
    (hg' : MapsTo g t s) :
    UpperHemicontinuousWithinAt (f ∘ g) t c :=
  -- the elaboration aid is necessary.
  SemicontinuousWithinAt.comp (r := (fun x t ↦ t ∈ 𝓝ˢ (f x))) hf hg hg'
/-
**UpperHemicontinuousAt.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UpperHemicontinuousAt.comp (hf : UpperHemicontinuousAt f (g c)) (hg : Cont
inuousAt g c) : UpperHemicontinuousAt (f ∘ g) c
参数：hf : UpperHemicontinuousAt f (g c)；hg : ContinuousAt g c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SemicontinuousAt.comp`：SemicontinuousAt.comp {r : α -> β -> Prop} {γ : T
ype*} [TopologicalSpace γ] {x : γ} {g : γ -> α} (h : SemicontinuousAt r (g x)) (
hg : Contin…
-/
theorem UpperHemicontinuousAt.comp
    (hf : UpperHemicontinuousAt f (g c)) (hg : ContinuousAt g c) :
    UpperHemicontinuousAt (f ∘ g) c :=
  SemicontinuousAt.comp (r := (fun x t ↦ t ∈ 𝓝ˢ (f x))) hf hg
/-
**UpperHemicontinuousOn.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UpperHemicontinuousOn.comp (hf : UpperHemicontinuousOn f s) (hg : Continuo
usOn g t) (hg' : MapsTo g t s) : UpperHemicontinuousOn (f ∘ g) t
参数：hf : UpperHemicontinuousOn f s；hg : ContinuousOn g t；hg' : MapsTo g t s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SemicontinuousOn.comp`：SemicontinuousOn.comp {r : α -> β -> Prop} {γ : T
ype*} [TopologicalSpace γ] {g : γ -> α} {s : Set γ} {t : Set α} (h : Semicontinu
ousOn r t) …
-/
theorem UpperHemicontinuousOn.comp
    (hf : UpperHemicontinuousOn f s) (hg : ContinuousOn g t) (hg' : MapsTo g t s) :
    UpperHemicontinuousOn (f ∘ g) t :=
  SemicontinuousOn.comp (r := (fun x t ↦ t ∈ 𝓝ˢ (f x))) hf hg hg'
/-
**UpperHemicontinuous.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UpperHemicontinuous.comp (hf : UpperHemicontinuous f) (hg : Continuous g) 
: UpperHemicontinuous (f ∘ g)
参数：hf : UpperHemicontinuous f；hg : Continuous g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Semicontinuous.comp`：Semicontinuous.comp {r : α -> β -> Prop} {γ : Type*
} [TopologicalSpace γ] {g : γ -> α} (h : Semicontinuous r) (hg : Continuous g) :
 Semicont…
-/
theorem UpperHemicontinuous.comp
    (hf : UpperHemicontinuous f) (hg : Continuous g) : UpperHemicontinuous (f ∘ g) :=
  Semicontinuous.comp (r := (fun x t ↦ t ∈ 𝓝ˢ (f x))) hf hg

end

end Hemi

section Sections

/-! ## Open lower sections -/

/-! ### Definitions -/

/-- A function `f : α → Set β` has open lower sections on `s` if it has open lower sections within
`s` at every `x ∈ s`. -/
/-
**HasOpenLowerSectionsOn** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：HasOpenLowerSectionsOn (f : α -> Set β) (s : Set α)
参数：f : α -> Set β；s : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f : α → Set β` has open lower sections on `s` if it has open lower s
ections within
`s` at every `x ∈ s`.
-/
abbrev HasOpenLowerSectionsOn (f : α → Set β) (s : Set α) :=
  SemicontinuousOn (fun x b ↦ b ∈ f x) s

/-- A function `f : α → Set β` has open lower sections if, for every `b`, the set `{x | b ∈ f x}`
is open. Equivalently, whenever `b ∈ f x`, then `b ∈ f x'` for all `x'` sufficiently close to
`x`. -/
/-
**HasOpenLowerSections** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：HasOpenLowerSections (f : α -> Set β)
参数：f : α -> Set β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f : α → Set β` has open lower sections if, for every `b`, the set `{
x | b ∈ f x}`
is open. Equivalently, whenever `b ∈ f x`, then `b ∈ f x'` for all `x'` sufficie
ntly close to
`x`.
-/
abbrev HasOpenLowerSections (f : α → Set β) :=
  Semicontinuous (fun x b ↦ b ∈ f x)

variable {f g : α → Set β} {x : α} {s t : Set α} {z : Set β}
/-
**hasOpenLowerSections_iff_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasOpenLowerSections_iff_isOpen : HasOpenLowerSections f ↔ forall b, IsOpe
n {x | b in f x}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem hasOpenLowerSections_iff_isOpen : HasOpenLowerSections f ↔ ∀ b, IsOpen {x | b ∈ f x} := by
  simp [semicontinuous_iff_isOpen]

/-! ### Basic dot notation interface -/

/-
**HasOpenLowerSectionsOn.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasOpenLowerSectionsOn.mono (h : HasOpenLowerSectionsOn f s) (hst : t subs
eteq s) : HasOpenLowerSectionsOn f t
参数：h : HasOpenLowerSectionsOn f s；hst : t subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousOn.mono`：SemicontinuousOn.mono (h : SemicontinuousOn r s) 
(hst : t subseteq s) : SemicontinuousOn r t

--- 原说明 ---
### Basic dot notation interface
-/
theorem HasOpenLowerSectionsOn.mono (h : HasOpenLowerSectionsOn f s) (hst : t ⊆ s) :
    HasOpenLowerSectionsOn f t :=
  SemicontinuousOn.mono h hst
/-
**hasOpenLowerSectionsOn_univ_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasOpenLowerSectionsOn_univ_iff : HasOpenLowerSectionsOn f univ ↔ HasOpenL
owerSections f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `semicontinuousOn_univ_iff`：semicontinuousOn_univ_iff : SemicontinuousOn 
r univ ↔ Semicontinuous r
-/
theorem hasOpenLowerSectionsOn_univ_iff :
    HasOpenLowerSectionsOn f univ ↔ HasOpenLowerSections f :=
  semicontinuousOn_univ_iff
/-
**hasOpenLowerSections_restrict_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace α] {f : α → Set β
} {s : Set α},   HasOpenLowerSections (s.domRestrict f) ↔ HasOpenLowerSectionsOn
 f s
参数：s.domRestrict f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `semicontinuous_restrict_iff`：∀ {α : Type u_1} {β : Type u_2} [inst : Top
ologicalSpace α] {r : α → β → Prop} {s : Set α},   Semicontinuous (s.domRestrict
 r) ↔ Semicontinu…
-/
@[simp] theorem hasOpenLowerSections_restrict_iff :
    HasOpenLowerSections (s.domRestrict f) ↔ HasOpenLowerSectionsOn f s :=
  semicontinuous_restrict_iff (r := (fun x b ↦ b ∈ f x))
/-
**HasOpenLowerSections.hasOpenLowerSectionsOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasOpenLowerSections.hasOpenLowerSectionsOn (h : HasOpenLowerSections f) (
s : Set α) : HasOpenLowerSectionsOn f s
参数：h : HasOpenLowerSections f；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Semicontinuous.semicontinuousOn`：Semicontinuous.semicontinuousOn (h : Se
micontinuous r) (s : Set α) : SemicontinuousOn r s
-/
theorem HasOpenLowerSections.hasOpenLowerSectionsOn (h : HasOpenLowerSections f) (s : Set α) :
    HasOpenLowerSectionsOn f s :=
  h.semicontinuousOn s

/-! ### Constants -/

/-
**HasOpenLowerSectionsOn.const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasOpenLowerSectionsOn.const : HasOpenLowerSectionsOn (fun _x => z) s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousOn.const`：SemicontinuousOn.const {f : β -> Prop} : Semicon
tinuousOn (fun _x => f) s

--- 原说明 ---
### Constants
-/
theorem HasOpenLowerSectionsOn.const : HasOpenLowerSectionsOn (fun _x => z) s :=
  SemicontinuousOn.const
/-
**HasOpenLowerSections.const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasOpenLowerSections.const : HasOpenLowerSections fun _x : α => z
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Semicontinuous.const`：Semicontinuous.const {f : β -> Prop} : Semicontinu
ous fun _x : α => f
-/
theorem HasOpenLowerSections.const : HasOpenLowerSections fun _x : α => z :=
  Semicontinuous.const

/-! ### Intersection and Union -/

/-
**HasOpenLowerSectionsOn.inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasOpenLowerSectionsOn.inter {f g : α -> Set β} {s : Set α} (hf : HasOpenL
owerSectionsOn f s) (hg : HasOpenLowerSectionsOn g s) : HasOpenLowerSectionsOn (
fun x => f x inter g x) s
参数：hf : HasOpenLowerSectionsOn f s；hg : HasOpenLowerSectionsOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousOn.inf`：SemicontinuousOn.inf {r' : α -> β -> Prop} (h : Se
micontinuousOn r s) (h' : SemicontinuousOn r' s) : SemicontinuousOn (r ⊓ r') s

--- 原说明 ---
### Intersection and Union
-/
theorem HasOpenLowerSectionsOn.inter {f g : α → Set β} {s : Set α} (hf : HasOpenLowerSectionsOn f s)
  (hg : HasOpenLowerSectionsOn g s) : HasOpenLowerSectionsOn (fun x ↦ f x ∩ g x) s := hf.inf hg
/-
**HasOpenLowerSectionsOn.union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasOpenLowerSectionsOn.union {f g : α -> Set β} {s : Set α} (hf : HasOpenL
owerSectionsOn f s) (hg : HasOpenLowerSectionsOn g s) : HasOpenLowerSectionsOn (
fun x => f x union g x) s
参数：hf : HasOpenLowerSectionsOn f s；hg : HasOpenLowerSectionsOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemicontinuousOn.sup`：SemicontinuousOn.sup {r' : α -> β -> Prop} (h : Se
micontinuousOn r s) (h' : SemicontinuousOn r' s) : SemicontinuousOn (r ⊔ r') s
-/
theorem HasOpenLowerSectionsOn.union {f g : α → Set β} {s : Set α} (hf : HasOpenLowerSectionsOn f s)
  (hg : HasOpenLowerSectionsOn g s) : HasOpenLowerSectionsOn (fun x ↦ f x ∪ g x) s := hf.sup hg
/-
**HasOpenLowerSections.inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasOpenLowerSections.inter {f g : α -> Set β} (hf : HasOpenLowerSections f
) (hg : HasOpenLowerSections g) : HasOpenLowerSections (fun x => f x inter g x)
参数：hf : HasOpenLowerSections f；hg : HasOpenLowerSections g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Semicontinuous.inf`：Semicontinuous.inf {r' : α -> β -> Prop} (h : Semico
ntinuous r) (h' : Semicontinuous r') : Semicontinuous (r ⊓ r')
-/
theorem HasOpenLowerSections.inter {f g : α → Set β} (hf : HasOpenLowerSections f)
  (hg : HasOpenLowerSections g) : HasOpenLowerSections (fun x ↦ f x ∩ g x) := hf.inf hg
/-
**HasOpenLowerSections.union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasOpenLowerSections.union {f g : α -> Set β} (hf : HasOpenLowerSections f
) (hg : HasOpenLowerSections g) : HasOpenLowerSections (fun x => f x union g x)
参数：hf : HasOpenLowerSections f；hg : HasOpenLowerSections g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Semicontinuous.sup`：Semicontinuous.sup {r' : α -> β -> Prop} (h : Semico
ntinuous r) (h' : Semicontinuous r') : Semicontinuous (r ⊔ r')
-/
theorem HasOpenLowerSections.union {f g : α → Set β} (hf : HasOpenLowerSections f)
  (hg : HasOpenLowerSections g) : HasOpenLowerSections (fun x ↦ f x ∪ g x) := hf.sup hg

/-! ### Composition -/

section

variable {γ : Type*} [TopologicalSpace γ] {g : γ → α} {c : γ} {t : Set γ}

/-
**HasOpenLowerSectionsOn.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasOpenLowerSectionsOn.comp (hf : HasOpenLowerSectionsOn f s) (hg : Contin
uousOn g t) (hg' : MapsTo g t s) : HasOpenLowerSectionsOn (f ∘ g) t
参数：hf : HasOpenLowerSectionsOn f s；hg : ContinuousOn g t；hg' : MapsTo g t s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SemicontinuousOn.comp`：SemicontinuousOn.comp {r : α -> β -> Prop} {γ : T
ype*} [TopologicalSpace γ] {g : γ -> α} {s : Set γ} {t : Set α} (h : Semicontinu
ousOn r t) …
-/
theorem HasOpenLowerSectionsOn.comp
    (hf : HasOpenLowerSectionsOn f s) (hg : ContinuousOn g t) (hg' : MapsTo g t s) :
    HasOpenLowerSectionsOn (f ∘ g) t :=
  SemicontinuousOn.comp (r := (fun x b ↦ b ∈ f x)) hf hg hg'
/-
**HasOpenLowerSections.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasOpenLowerSections.comp (hf : HasOpenLowerSections f) (hg : Continuous g
) : HasOpenLowerSections (f ∘ g)
参数：hf : HasOpenLowerSections f；hg : Continuous g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Semicontinuous.comp`：Semicontinuous.comp {r : α -> β -> Prop} {γ : Type*
} [TopologicalSpace γ] {g : γ -> α} (h : Semicontinuous r) (hg : Continuous g) :
 Semicont…
-/
theorem HasOpenLowerSections.comp
    (hf : HasOpenLowerSections f) (hg : Continuous g) : HasOpenLowerSections (f ∘ g) :=
  Semicontinuous.comp (r := (fun x b ↦ b ∈ f x)) hf hg

end

end Sections

section Graph

/-! ## Correspondence Graphs (CGraph)

We define the graph of a correspondence `f : α → Set β` to be the set of all pairs
`(x, y) : α × β` such that `y ∈ f x`. We use the term `CGraph` to refer to this construct.
-/

variable [TopologicalSpace β]

/-- A function `f : α → Set β` has an open cgraph if the set of all `x` such that `x.2 ∈ f x.1`
is open in `α × β`. -/
/-
**HasOpenCGraph** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：HasOpenCGraph (f : α -> Set β)
参数：f : α -> Set β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f : α → Set β` has an open cgraph if the set of all `x` such that `x
.2 ∈ f x.1`
is open in `α × β`.
-/
abbrev HasOpenCGraph (f : α → Set β) := IsOpen {x : α × β | x.2 ∈ f x.1}
/-
**HasOpenCGraph.const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasOpenCGraph.const {z : Set β} (hz : IsOpen z) : HasOpenCGraph (fun _x : 
α => z)
参数：hz : IsOpen z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
-/
theorem HasOpenCGraph.const {z : Set β} (hz : IsOpen z) : HasOpenCGraph (fun _x : α => z) :=
  hz.preimage continuous_snd
/-
**HasOpenCGraph.inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasOpenCGraph.inter {f g : α -> Set β} (hf : HasOpenCGraph f) (hg : HasOpe
nCGraph g) : HasOpenCGraph (fun x => f x inter g x)
参数：hf : HasOpenCGraph f；hg : HasOpenCGraph g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `HasOpenCGraph.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalS
pace α] [inst_1 : TopologicalSpace β] (f : α → Set β),   HasOpenCGraph f = IsOpe
n {x | x…
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
-/
theorem HasOpenCGraph.inter {f g : α → Set β} (hf : HasOpenCGraph f)
    (hg : HasOpenCGraph g) : HasOpenCGraph (fun x ↦ f x ∩ g x) := by
  have : {x : α × β | x.2 ∈ f x.1 ∩ g x.1} =
      {x | x.2 ∈ f x.1} ∩ {x | x.2 ∈ g x.1} := by ext; simp
  rw [HasOpenCGraph, this]
  exact IsOpen.inter hf hg

section

variable {γ : Type*} [TopologicalSpace γ] {g' : γ → α} {c : γ × β}
    {u : Set (γ × β)} {v : Set (α × β)}

/-
**HasOpenCGraph.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasOpenCGraph.comp {f : α -> Set β} (hf : HasOpenCGraph f) (hg : Continuou
s g') : HasOpenCGraph (f ∘ g')
参数：hf : HasOpenCGraph f；hg : Continuous g'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `Continuous.prodMap`：Continuous.prodMap {f : Z -> X} {g : W -> Y} (hf : C
ontinuous f) (hg : Continuous g) : Continuous (Prod.map f g)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem HasOpenCGraph.comp {f : α → Set β} (hf : HasOpenCGraph f) (hg : Continuous g') :
    HasOpenCGraph (f ∘ g') :=
  hf.preimage (hg.prodMap continuous_id)

end

/-! ### Implications

A correspondence with an open graph has open lower sections. And a correspondence
with open lower sections is lower hemicontinuous.
-/

/-
**HasOpenLowerSections.lowerHemicontinuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasOpenLowerSections.lowerHemicontinuous {f : α -> Set β} (hf : HasOpenLow
erSections f) : LowerHemicontinuous f
参数：hf : HasOpenLowerSections f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x

--- 原说明 ---
### Implications

A correspondence with an open graph has open lower sections. And a correspondenc
e
with open lower sections is lower hemicontinuous.
-/
theorem HasOpenLowerSections.lowerHemicontinuous {f : α → Set β} (hf : HasOpenLowerSections f) :
    LowerHemicontinuous f := fun x _ ⟨hopen, y, hyfx, hyt⟩ ↦
      (hf x y hyfx).mono fun _ hy' ↦ ⟨hopen, y, hy', hyt⟩
/-
**HasOpenCGraph.hasOpenLowerSections** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasOpenCGraph.hasOpenLowerSections {f : α -> Set β} (h : HasOpenCGraph f) 
: HasOpenLowerSections f
参数：h : HasOpenCGraph f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
-/
theorem HasOpenCGraph.hasOpenLowerSections
    {f : α → Set β} (h : HasOpenCGraph f) :
    HasOpenLowerSections f := by
  intro x b hb
  have hopen : IsOpen {x' : α | b ∈ f x'} := by
    simpa using h.preimage (continuous_id.prodMk continuous_const)
  simpa [Filter.Eventually] using hopen.mem_nhds hb

end Graph

