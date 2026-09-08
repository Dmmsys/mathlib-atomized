/-
Copyright (c) 2022 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson
-/
module

public import Mathlib.Order.Filter.Prod

/-!
# Curried Filters

This file provides an operation (`Filter.curry`) on filters which provides the equivalence
`∀ᶠ a in l, ∀ᶠ b in l', p (a, b) ↔ ∀ᶠ c in (l.curry l'), p c` (see `Filter.eventually_curry_iff`).

To understand when this operation might arise, it is helpful to think of `∀ᶠ` as a combination of
the quantifiers `∃ ∀`. For instance, `∀ᶠ n in atTop, p n ↔ ∃ N, ∀ n ≥ N, p n`. A curried filter
yields the quantifier order `∃ ∀ ∃ ∀`. For instance,
`∀ᶠ n in atTop.curry atTop, p n ↔ ∃ M, ∀ m ≥ M, ∃ N, ∀ n ≥ N, p (m, n)`.

This is different from a product filter, which instead yields a quantifier order `∃ ∃ ∀ ∀`. For
instance, `∀ᶠ n in atTop ×ˢ atTop, p n ↔ ∃ M, ∃ N, ∀ m ≥ M, ∀ n ≥ N, p (m, n)`. This makes it
clear that if something eventually occurs on the product filter, it eventually occurs on the curried
filter (see `Filter.curry_le_prod` and `Filter.Eventually.curry`), but the converse is not true.

Another way to think about the curried versus the product filter is that tending to some limit on
the product filter is a version of uniform convergence (see `tendsto_prod_filter_iff`) whereas
tending to some limit on a curried filter is just iterated limits (see `Filter.Tendsto.curry`).

In the "generalized set" intuition, a product filter and `Filter.curry` correspond to two ways
of describing the product of two sets:

* `f ×ˢ g = comap fst f ⊓ comap snd g` corresponds to `s ×ˢ t = fst ⁻¹' s ∩ snd ⁻¹' t`
* `f.curry g = bind f (fun x ↦ map (x, ·) g)` corresponds to `s ×ˢ t = ⋃ x ∈ s, (x, ·) '' t`

## Main definitions

* `Filter.curry`: A binary operation on filters which represents iterated limits

## Main statements

* `Filter.eventually_curry_iff`: An alternative definition of a curried filter
* `Filter.curry_le_prod`: Something that is eventually true on the a product filter is eventually
  true on the curried filter

## Tags

uniform convergence, curried filters, product filters
-/

public section


namespace Filter

variable {α β γ : Type*} {l : Filter α} {m : Filter β} {s : Set α} {t : Set β}

/-
**Filter.eventually_curry_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_curry_iff {p : α × β -> Prop} : (forallᶠ x : α × β in l.curry m
, p x) ↔ forallᶠ x : α in l, forallᶠ y : β in m, p (x, y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eventually_curry_iff {p : α × β → Prop} :
    (∀ᶠ x : α × β in l.curry m, p x) ↔ ∀ᶠ x : α in l, ∀ᶠ y : β in m, p (x, y) :=
  Iff.rfl
/-
**Filter.frequently_curry_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：frequently_curry_iff (p : (α × β) -> Prop) : (existsᶠ x in l.curry m, p x)
 ↔ existsᶠ x in l, existsᶠ y in m, p (x, y)
参数：p : (α × β) -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem frequently_curry_iff
    (p : (α × β) → Prop) : (∃ᶠ x in l.curry m, p x) ↔ ∃ᶠ x in l, ∃ᶠ y in m, p (x, y) := by
  simp_rw [Filter.Frequently, not_iff_not, not_not, eventually_curry_iff]
/-
**Filter.mem_curry_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_curry_iff {s : Set (α × β)} : s in l.curry m ↔ forallᶠ x : α in l, for
allᶠ y : β in m, (x, y) in s
参数：α × β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_curry_iff {s : Set (α × β)} :
    s ∈ l.curry m ↔ ∀ᶠ x : α in l, ∀ᶠ y : β in m, (x, y) ∈ s := Iff.rfl
/-
**Filter.curry_le_prod** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：curry_le_prod : l.curry m <= l ×ˢ m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.curry`：∀ {α : Type u_1} {β : Type u_2} {la : Filter α}
 {lb : Filter β} {p : α × β → Prop},   (∀ᶠ (x : α × β) in la ×ˢ lb, p x) → ∀ᶠ (x
 : α) in la, …
-/
theorem curry_le_prod : l.curry m ≤ l ×ˢ m := fun _ => Eventually.curry
/-
**Filter.Tendsto.curry** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Tendsto`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : α → β → γ} {la : Filte
r α} {lb : Filter β} {lc : Filter γ},   (∀ᶠ (a : α) in la, Filter.Tendsto (fun b
 => f a b) lb lc) → Filter.Tendsto (↿f) (la.curry lb) lc
参数：∀ᶠ (a : α) in la, Filter.Tendsto (fun b => f a b) lb lc；↿f；la.curry lb。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
-/
theorem Tendsto.curry {f : α → β → γ} {la : Filter α} {lb : Filter β} {lc : Filter γ}
    (h : ∀ᶠ a in la, Tendsto (fun b : β => f a b) lb lc) : Tendsto ↿f (la.curry lb) lc :=
  fun _s hs => h.mono fun _a ha => ha hs
/-
**Filter.frequently_curry_prod_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：frequently_curry_prod_iff : (existsᶠ x in l.curry m, x in s ×ˢ t) ↔ (exist
sᶠ x in l, x in s) ∧ existsᶠ y in m, y in t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem frequently_curry_prod_iff :
    (∃ᶠ x in l.curry m, x ∈ s ×ˢ t) ↔ (∃ᶠ x in l, x ∈ s) ∧ ∃ᶠ y in m, y ∈ t := by
  simp [frequently_curry_iff]
/-
**Filter.eventually_curry_prod_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_curry_prod_iff [NeBot l] [NeBot m] : (forallᶠ x in l.curry m, x
 in s ×ˢ t) ↔ s in l ∧ t in m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eventually_curry_prod_iff [NeBot l] [NeBot m] :
    (∀ᶠ x in l.curry m, x ∈ s ×ˢ t) ↔ s ∈ l ∧ t ∈ m := by
  simp [eventually_curry_iff]
/-
**Filter.prod_mem_curry** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：prod_mem_curry (hs : s in l) (ht : t in m) : s ×ˢ t in l.curry m
参数：hs : s in l；ht : t in m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.curry_le_prod`：curry_le_prod : l.curry m <= l ×ˢ m
· 使用定理 `Filter.prod_mem_prod`：prod_mem_prod (hs : s in f) (ht : t in g) : s ×ˢ t
 in f ×ˢ g
-/
theorem prod_mem_curry (hs : s ∈ l) (ht : t ∈ m) : s ×ˢ t ∈ l.curry m :=
  curry_le_prod <| prod_mem_prod hs ht

end Filter

