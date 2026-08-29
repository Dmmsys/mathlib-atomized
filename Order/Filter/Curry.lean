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

/--
theorem `eventually_curry_iff` / 定理 `eventually_curry_iff`

English:
theorem eventually_curry_iff
  given: {p : α × β -> Prop}
  proof: Iff.rfl

中文:
定理 eventually_curry_iff
  条件: {p : α × β -> 命题}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem eventually_curry_iff {p : α × β -> Prop} :
    (forallᶠ x : α × β in l.curry m, p x) ↔ forallᶠ x : α in l, forallᶠ y : β in m, p (x, y) :=
  Iff.rfl

/--
theorem `frequently_curry_iff` / 定理 `frequently_curry_iff`

English:
theorem frequently_curry_iff
  proof: by
  simp_rw [Filter.Frequently, not_iff_not, not_not, eventually_curry_iff]

中文:
定理 frequently_curry_iff
  证明: by
  simp_rw [Filter.Frequently, not_iff_not, not_not, eventually_curry_iff]

Depends on / 依赖: Filter, Filter.Frequently, Frequently, eventually_curry_iff, not_iff_not, not_not, simp_rw
-/
theorem frequently_curry_iff
    (p : (α × β) -> Prop) : (existsᶠ x in l.curry m, p x) ↔ existsᶠ x in l, existsᶠ y in m, p (x, y) := by
  simp_rw [Filter.Frequently, not_iff_not, not_not, eventually_curry_iff]

/--
theorem `mem_curry_iff` / 定理 `mem_curry_iff`

English:
theorem mem_curry_iff
  given: {s : Set (α × β)}
  proof: Iff.rfl

中文:
定理 mem_curry_iff
  条件: {s : 集合 (α × β)}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_curry_iff {s : Set (α × β)} :
    s in l.curry m ↔ forallᶠ x : α in l, forallᶠ y : β in m, (x, y) in s := Iff.rfl

/--
theorem `curry_le_prod` / 定理 `curry_le_prod`

English:
theorem curry_le_prod
  statement: l.curry m <= l ×ˢ m
  proof: fun _ => Eventually.curry

中文:
定理 curry_le_prod
  结论: l.curry m <= l ×ˢ m
  证明: fun _ => Eventually.curry

Depends on / 依赖: Eventually, Eventually.curry
-/
theorem curry_le_prod : l.curry m <= l ×ˢ m := fun _ => Eventually.curry

/--
theorem `Tendsto.curry` / 定理 `Tendsto.curry`

English:
theorem Tendsto.curry
  statement: {f : α -> β -> γ} {la : Filter α} {lb : Filter β} {lc : Filter γ}
  proof: fun _s hs => h.mono fun _a ha => ha hs

中文:
定理 收敛.curry
  结论: {f : α -> β -> γ} {la : 滤子 α} {lb : 滤子 β} {lc : 滤子 γ}
  证明: fun _s hs => h.mono fun _a ha => ha hs

Depends on / 依赖: h.mono
-/
theorem Tendsto.curry {f : α -> β -> γ} {la : Filter α} {lb : Filter β} {lc : Filter γ}
    (h : forallᶠ a in la, Tendsto (fun b : β => f a b) lb lc) : Tendsto ↿f (la.curry lb) lc :=
  fun _s hs => h.mono fun _a ha => ha hs

/--
theorem `frequently_curry_prod_iff` / 定理 `frequently_curry_prod_iff`

English:
theorem frequently_curry_prod_iff
  proof: by
  simp [frequently_curry_iff]

中文:
定理 frequently_curry_prod_iff
  证明: by
  simp [frequently_curry_iff]

Depends on / 依赖: frequently_curry_iff
-/
theorem frequently_curry_prod_iff :
    (existsᶠ x in l.curry m, x in s ×ˢ t) ↔ (existsᶠ x in l, x in s) ∧ existsᶠ y in m, y in t := by
  simp [frequently_curry_iff]

/--
theorem `eventually_curry_prod_iff` / 定理 `eventually_curry_prod_iff`

English:
theorem eventually_curry_prod_iff
  given: [NeBot l] [NeBot m]
  proof: by
  simp [eventually_curry_iff]

中文:
定理 eventually_curry_prod_iff
  条件: [NeBot l] [NeBot m]
  证明: by
  simp [eventually_curry_iff]

Depends on / 依赖: eventually_curry_iff
-/
theorem eventually_curry_prod_iff [NeBot l] [NeBot m] :
    (forallᶠ x in l.curry m, x in s ×ˢ t) ↔ s in l ∧ t in m := by
  simp [eventually_curry_iff]

/--
theorem `prod_mem_curry` / 定理 `prod_mem_curry`

English:
theorem prod_mem_curry
  given: (hs : s in l) (ht : t in m)
  statement: s ×ˢ t in l.curry m
  proof: curry_le_prod prod_mem_prod hs ht

中文:
定理 prod_mem_curry
  条件: (hs : s in l) (ht : t in m)
  结论: s ×ˢ t in l.curry m
  证明: curry_le_prod prod_mem_prod hs ht

Depends on / 依赖: curry_le_prod, prod_mem_prod
-/
theorem prod_mem_curry (hs : s in l) (ht : t in m) : s ×ˢ t in l.curry m :=
curry_le_prod prod_mem_prod hs ht

end Filter
