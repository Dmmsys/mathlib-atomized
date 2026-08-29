/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Order.Filter.CountableInter

/-!
# Filters with countable intersections and countable separating families

In this file we prove some facts about a filter with countable intersections property on a type with
a countable family of sets that separates points of the space. The main use case is the
`MeasureTheory.ae` filter and a space with countably generated σ-algebra but lemmas apply,
e.g., to the `residual` filter and a T₀ topological space with second countable topology.

To avoid repetition of lemmas for different families of separating sets (measurable sets, open sets,
closed sets), all theorems in this file take a predicate `p : Set α → Prop` as an argument and prove
existence of a countable separating family satisfying this predicate by searching for a
`HasCountableSeparatingOn` typeclass instance.

## Main definitions

- `HasCountableSeparatingOn α p t`: a typeclass saying that there exists a countable set family
  `S : Set (Set α)` such that all `s ∈ S` satisfy the predicate `p` and any two distinct points
  `x y ∈ t`, `x ≠ y`, can be separated by a set `s ∈ S`. For technical reasons, we formulate the
  latter property as "for all `x y ∈ t`, if `x ∈ s ↔ y ∈ s` for all `s ∈ S`, then `x = y`".

This typeclass is used in all lemmas in this file to avoid repeating them for open sets, closed
sets, and measurable sets.

### Main results

#### Filters supported on a (sub)singleton

Let `l : Filter α` be a filter with countable intersections property. Let `p : Set α → Prop` be a
property such that there exists a countable family of sets satisfying `p` and separating points of
`α`. Then `l` is supported on a subsingleton: there exists a subsingleton `t` such that
`t ∈ l`.

We formalize various versions of this theorem in
`Filter.exists_subset_subsingleton_mem_of_forall_separating`,
`Filter.exists_mem_singleton_mem_of_mem_of_nonempty_of_forall_separating`,
`Filter.exists_singleton_mem_of_mem_of_forall_separating`,
`Filter.exists_subsingleton_mem_of_forall_separating`, and
`Filter.exists_singleton_mem_of_forall_separating`.

#### Eventually constant functions

Consider a function `f : α → β`, a filter `l` with countable intersections property, and a countable
separating family of sets of `β`. Suppose that for every `U` from the family, either
`∀ᶠ x in l, f x ∈ U` or `∀ᶠ x in l, f x ∉ U`. Then `f` is eventually constant along `l`.

We formalize three versions of this theorem in
`Filter.exists_mem_eventuallyEq_const_of_eventually_mem_of_forall_separating`,
`Filter.exists_eventuallyEq_const_of_eventually_mem_of_forall_separating`, and
`Filer.exists_eventuallyEq_const_of_forall_separating`.

#### Eventually equal functions

Two functions are equal along a filter with countable intersections property if the preimages of all
sets from a countable separating family of sets are equal along the filter.

We formalize several versions of this theorem in
`Filter.of_eventually_mem_of_forall_separating_mem_iff`, `Filter.of_forall_separating_mem_iff`,
`Filter.of_eventually_mem_of_forall_separating_preimage`, and
`Filter.of_forall_separating_preimage`.

## Keywords

filter, countable
-/

public section

open Function Set Filter

/--
Definition of `HasCountableSeparatingOn` / `HasCountableSeparatingOn` 的定义

English:
class HasCountableSeparatingOn
  parameters: (α : Type*) (p : Set α -> Prop) (t : Set α)
  axioms and operations (1):
    - exists_countable_separating : exists S : Set (Set α), S.Countable ∧ (forall s in S, p s) ∧ forall x in t, forall y in t, (forall s in S, x in s ↔ y in s) -> x = y

中文:
类 有余untableSeparatingOn
  参数: (α : 类型) (p : 集合 α -> 命题) (t : 集合 α)
  公理与运算 (1 个):
    - exists_countable_separating : 存在 S : 集合 (集合 α), S.可数 ∧ (对任意 s in S, p s) ∧ 对任意 x in t, 对任意 y in t, (对任意 s in S, x in s ↔ y in s) -> x = y
-/
class HasCountableSeparatingOn (α : Type*) (p : Set α -> Prop) (t : Set α) : Prop where
  exists_countable_separating : exists S : Set (Set α), S.Countable ∧ (forall s in S, p s) ∧
    forall x in t, forall y in t, (forall s in S, x in s ↔ y in s) -> x = y

/--
theorem `exists_countable_separating` / 定理 `exists_countable_separating`

English:
theorem exists_countable_separating
  statement: (α : Type*) (p : Set α -> Prop) (t : Set α)
  proof: h.1

中文:
定理 存在_countable_separating
  结论: (α : 类型) (p : 集合 α -> 命题) (t : 集合 α)
  证明: h.1
-/
theorem exists_countable_separating (α : Type*) (p : Set α -> Prop) (t : Set α)
    [h : HasCountableSeparatingOn α p t] :
    exists S : Set (Set α), S.Countable ∧ (forall s in S, p s) ∧
      forall x in t, forall y in t, (forall s in S, x in s ↔ y in s) -> x = y :=
  h.1

/--
theorem `exists_nonempty_countable_separating` / 定理 `exists_nonempty_countable_separating`

English:
theorem exists_nonempty_countable_separating
  statement: (α : Type*) {p : Set α -> Prop} {s₀} (hp : p s₀)
  proof: let ⟨S, hSc, hSp, hSt⟩ := exists_countable_separating α p t
  ⟨insert s₀ S, insert_nonempty _ _, hSc.insert _, forall_insert_of_forall hSp hp,
fun x hx y hy hxy => hSt x hx y hy forall_of_forall_insert hxy⟩

中文:
定理 存在_nonempty_countable_separating
  结论: (α : 类型) {p : 集合 α -> 命题} {s₀} (hp : p s₀)
  证明: let ⟨S, hSc, hSp, hSt⟩ := exists_countable_separating α p t
  ⟨insert s₀ S, insert_nonempty _ _, hSc.insert _, forall_insert_of_forall hSp hp,
fun x hx y hy hxy => hSt x hx y hy forall_of_forall_insert hxy⟩

Depends on / 依赖: exists_countable_separating, forall_insert_of_forall, forall_of_forall_insert, hSc.insert, insert, insert_nonempty
-/
theorem exists_nonempty_countable_separating (α : Type*) {p : Set α -> Prop} {s₀} (hp : p s₀)
    (t : Set α) [HasCountableSeparatingOn α p t] :
    exists S : Set (Set α), S.Nonempty ∧ S.Countable ∧ (forall s in S, p s) ∧
      forall x in t, forall y in t, (forall s in S, x in s ↔ y in s) -> x = y :=
  let ⟨S, hSc, hSp, hSt⟩ := exists_countable_separating α p t
  ⟨insert s₀ S, insert_nonempty _ _, hSc.insert _, forall_insert_of_forall hSp hp,
fun x hx y hy hxy => hSt x hx y hy forall_of_forall_insert hxy⟩

/--
theorem `exists_seq_separating` / 定理 `exists_seq_separating`

English:
theorem exists_seq_separating
  statement: (α : Type*) {p : Set α -> Prop} {s₀} (hp : p s₀) (t : Set α)
  proof: by
  rcases exists_nonempty_countable_separating α hp t with ⟨S, hSne, hSc, hS⟩
  rcases hSc.exists_eq_range hSne with ⟨S, rfl⟩
  use S
  simpa only [forall_mem_range] using hS

中文:
定理 存在_seq_separating
  结论: (α : 类型) {p : 集合 α -> 命题} {s₀} (hp : p s₀) (t : 集合 α)
  证明: by
  rcases exists_nonempty_countable_separating α hp t with ⟨S, hSne, hSc, hS⟩
  rcases hSc.exists_eq_range hSne with ⟨S, rfl⟩
  use S
  simpa only [forall_mem_range] using hS

Depends on / 依赖: exists_eq_range, exists_nonempty_countable_separating, forall_mem_range, hSc.exists_eq_range
-/
theorem exists_seq_separating (α : Type*) {p : Set α -> Prop} {s₀} (hp : p s₀) (t : Set α)
    [HasCountableSeparatingOn α p t] :
    exists S : Nat -> Set α, (forall n, p (S n)) ∧ forall x in t, forall y in t, (forall n, x in S n ↔ y in S n) -> x = y := by
  rcases exists_nonempty_countable_separating α hp t with ⟨S, hSne, hSc, hS⟩
  rcases hSc.exists_eq_range hSne with ⟨S, rfl⟩
  use S
  simpa only [forall_mem_range] using hS

/--
theorem `HasCountableSeparatingOn.mono` / 定理 `HasCountableSeparatingOn.mono`

English:
theorem HasCountableSeparatingOn.mono
  statement: {α} {p₁ p₂ : Set α -> Prop} {t₁ t₂ : Set α}
  proof: let ⟨S, hSc, hSp, hSt⟩ := h.1
    ⟨S, hSc, fun s hs => hp s (hSp s hs), fun x hx y hy => hSt x (ht hx) y (ht hy)⟩

中文:
定理 有余untableSeparatingOn.mono
  结论: {α} {p₁ p₂ : 集合 α -> 命题} {t₁ t₂ : 集合 α}
  证明: let ⟨S, hSc, hSp, hSt⟩ := h.1
    ⟨S, hSc, fun s hs => hp s (hSp s hs), fun x hx y hy => hSt x (ht hx) y (ht hy)⟩
-/
theorem HasCountableSeparatingOn.mono {α} {p₁ p₂ : Set α -> Prop} {t₁ t₂ : Set α}
    [h : HasCountableSeparatingOn α p₁ t₁] (hp : forall s, p₁ s -> p₂ s) (ht : t₂ subseteq t₁) :
    HasCountableSeparatingOn α p₂ t₂ where
  exists_countable_separating :=
    let ⟨S, hSc, hSp, hSt⟩ := h.1
    ⟨S, hSc, fun s hs => hp s (hSp s hs), fun x hx y hy => hSt x (ht hx) y (ht hy)⟩

/--
theorem `HasCountableSeparatingOn.of_subtype` / 定理 `HasCountableSeparatingOn.of_subtype`

English:
theorem HasCountableSeparatingOn.of_subtype
  statement: {α : Type*} {p : Set α -> Prop} {t : Set α}
  proof: by
  rcases h.1 with ⟨S, hSc, hSq, hS⟩
  choose! V hpV hV using fun s hs => hpq s (hSq s hs)
  refine ⟨⟨V '' S, hSc.image _, forall_mem_image.2 hpV, fun x hx y hy h => ?_⟩⟩
  refine congr_arg Subtype.val (hS ⟨x, hx⟩ trivial ⟨y, hy⟩ trivial fun U hU => ?_)
  rw [← hV U hU]
  exact h _ (mem_image_of_mem _ hU)

中文:
定理 有余untableSeparatingOn.of_subtype
  结论: {α : 类型} {p : 集合 α -> 命题} {t : 集合 α}
  证明: by
  rcases h.1 with ⟨S, hSc, hSq, hS⟩
  choose! V hpV hV using fun s hs => hpq s (hSq s hs)
  refine ⟨⟨V '' S, hSc.image _, forall_mem_image.2 hpV, fun x hx y hy h => ?_⟩⟩
  refine congr_arg Subtype.val (hS ⟨x, hx⟩ trivial ⟨y, hy⟩ trivial fun U hU => ?_)
  rw [← hV U hU]
  exact h _ (mem_image_of_mem _ hU)

Depends on / 依赖: Subtype, Subtype.val, congr_arg, forall_mem_image, hSc.image, mem_image_of_mem
-/
theorem HasCountableSeparatingOn.of_subtype {α : Type*} {p : Set α -> Prop} {t : Set α}
    {q : Set t -> Prop} [h : HasCountableSeparatingOn t q univ]
    (hpq : forall U, q U -> exists V, p V ∧ (↑) ⁻¹' V = U) : HasCountableSeparatingOn α p t := by
  rcases h.1 with ⟨S, hSc, hSq, hS⟩
  choose! V hpV hV using fun s hs => hpq s (hSq s hs)
  refine ⟨⟨V '' S, hSc.image _, forall_mem_image.2 hpV, fun x hx y hy h => ?_⟩⟩
  refine congr_arg Subtype.val (hS ⟨x, hx⟩ trivial ⟨y, hy⟩ trivial fun U hU => ?_)
  rw [← hV U hU]
  exact h _ (mem_image_of_mem _ hU)

/--
theorem `HasCountableSeparatingOn.subtype_iff` / 定理 `HasCountableSeparatingOn.subtype_iff`

English:
theorem HasCountableSeparatingOn.subtype_iff
  given: {α : Type*} {p : Set α -> Prop} {t : Set α}
  proof: by
  constructor <;> intro h
· exact h.of_subtype fun s => id
  rcases h with ⟨S, Sct, Sp, hS⟩
  use {Subtype.val ⁻¹' s | s in S}, Sct.image _, ?_, ?_
  · rintro u ⟨t, tS, rfl⟩
    exact ⟨t, Sp _ tS, rfl⟩
  rintro x - y - hxy
exact Subtype.val_injective hS _ (Subtype.coe_prop _) _ (Subtype.coe_prop _)
    fun s hs => hxy (Subtype.val ⁻¹' s) ⟨s, hs, rfl⟩

中文:
定理 有余untableSeparatingOn.subtype_iff
  条件: {α : 类型} {p : 集合 α -> 命题} {t : 集合 α}
  证明: by
  constructor <;> intro h
· exact h.of_subtype fun s => id
  rcases h with ⟨S, Sct, Sp, hS⟩
  use {Subtype.val ⁻¹' s | s in S}, Sct.image _, ?_, ?_
  · rintro u ⟨t, tS, rfl⟩
    exact ⟨t, Sp _ tS, rfl⟩
  rintro x - y - hxy
exact Subtype.val_injective hS _ (Subtype.coe_prop _) _ (Subtype.coe_prop _)
    fun s hs => hxy (Subtype.val ⁻¹' s) ⟨s, hs, rfl⟩

Depends on / 依赖: Sct.image, Subtype, Subtype.coe_prop, Subtype.val, Subtype.val_injective, coe_prop, h.of_subtype, of_subtype, val_injective
-/
theorem HasCountableSeparatingOn.subtype_iff {α : Type*} {p : Set α -> Prop} {t : Set α} :
    HasCountableSeparatingOn t (fun u => exists v, p v ∧ (↑) ⁻¹' v = u) univ ↔
    HasCountableSeparatingOn α p t := by
  constructor <;> intro h
· exact h.of_subtype fun s => id
  rcases h with ⟨S, Sct, Sp, hS⟩
  use {Subtype.val ⁻¹' s | s in S}, Sct.image _, ?_, ?_
  · rintro u ⟨t, tS, rfl⟩
    exact ⟨t, Sp _ tS, rfl⟩
  rintro x - y - hxy
exact Subtype.val_injective hS _ (Subtype.coe_prop _) _ (Subtype.coe_prop _)
    fun s hs => hxy (Subtype.val ⁻¹' s) ⟨s, hs, rfl⟩

namespace Filter

variable {α β : Type*} {l : Filter α} [CountableInterFilter l] {f g : α -> β}


/--
theorem `exists_subset_subsingleton_mem_of_forall_separating` / 定理 `exists_subset_subsingleton_mem_of_forall_separating`

English:
theorem exists_subset_subsingleton_mem_of_forall_separating
  statement: (p : Set α -> Prop)
  proof: by
  rcases h.1 with ⟨S, hSc, hSp, hS⟩
  refine ⟨s inter ⋂₀ (S inter l.sets) inter ⋂ (U in S) (_ : Uᶜ in l), Uᶜ, ?_, ?_, ?_⟩
  · exact fun _ h => h.1.1
  · intro x hx y hy
    simp only [mem_sInter, mem_inter_iff, mem_iInter, mem_compl_iff] at hx hy
    refine hS x hx.1.1 y hy.1.1 (fun s hsS => ?_)
    cases hl s (hSp s hsS) with
    | inl hsl => simp only [hx.1.2 s ⟨hsS, hsl⟩, hy.1.2 s ⟨hsS, hsl⟩]
    | inr hsl => simp only [hx.2 s hsS hsl, hy.2 s hsS hsl]
  · exact inter_mem
      (inter_mem hs ((countable_sInter_mem (hSc.mono inter_subset_left)).2 fun _ h => h.2))
      ((countable_bInter_mem hSc).2 fun U hU => iInter_mem'.2 id)

中文:
定理 存在_subset_subsingleton_mem_of_对任意_separating
  结论: (p : 集合 α -> 命题)
  证明: by
  rcases h.1 with ⟨S, hSc, hSp, hS⟩
  refine ⟨s inter ⋂₀ (S inter l.sets) inter ⋂ (U in S) (_ : Uᶜ in l), Uᶜ, ?_, ?_, ?_⟩
  · exact fun _ h => h.1.1
  · intro x hx y hy
    simp only [mem_sInter, mem_inter_iff, mem_iInter, mem_compl_iff] at hx hy
    refine hS x hx.1.1 y hy.1.1 (fun s hsS => ?_)
    cases hl s (hSp s hsS) with
    | inl hsl => simp only [hx.1.2 s ⟨hsS, hsl⟩, hy.1.2 s ⟨hsS, hsl⟩]
    | inr hsl => simp only [hx.2 s hsS hsl, hy.2 s hsS hsl]
  · exact inter_mem
      (inter_mem hs ((countable_sInter_mem (hSc.mono inter_subset_left)).2 fun _ h => h.2))
      ((countable_bInter_mem hSc).2 fun U hU => iInter_mem'.2 id)

Depends on / 依赖: countable_sInter_mem, hSc.mono, inter_mem, l.sets, mem_compl_iff, mem_iInter, mem_inter_iff, mem_sInter
-/
theorem exists_subset_subsingleton_mem_of_forall_separating (p : Set α -> Prop)
    {s : Set α} [h : HasCountableSeparatingOn α p s] (hs : s in l)
    (hl : forall U, p U -> U in l ∨ Uᶜ in l) : exists t, t subseteq s ∧ t.Subsingleton ∧ t in l := by
  rcases h.1 with ⟨S, hSc, hSp, hS⟩
  refine ⟨s inter ⋂₀ (S inter l.sets) inter ⋂ (U in S) (_ : Uᶜ in l), Uᶜ, ?_, ?_, ?_⟩
  · exact fun _ h => h.1.1
  · intro x hx y hy
    simp only [mem_sInter, mem_inter_iff, mem_iInter, mem_compl_iff] at hx hy
    refine hS x hx.1.1 y hy.1.1 (fun s hsS => ?_)
    cases hl s (hSp s hsS) with
    | inl hsl => simp only [hx.1.2 s ⟨hsS, hsl⟩, hy.1.2 s ⟨hsS, hsl⟩]
    | inr hsl => simp only [hx.2 s hsS hsl, hy.2 s hsS hsl]
  · exact inter_mem
      (inter_mem hs ((countable_sInter_mem (hSc.mono inter_subset_left)).2 fun _ h => h.2))
      ((countable_bInter_mem hSc).2 fun U hU => iInter_mem'.2 id)

/--
theorem `exists_mem_singleton_mem_of_mem_of_nonempty_of_forall_separating` / 定理 `exists_mem_singleton_mem_of_mem_of_nonempty_of_forall_separating`

English:
theorem exists_mem_singleton_mem_of_mem_of_nonempty_of_forall_separating
  statement: (p : Set α -> Prop)
  proof: by
  rcases exists_subset_subsingleton_mem_of_forall_separating p hs hl with ⟨t, hts, ht, htl⟩
  rcases ht.eq_empty_or_singleton with rfl | ⟨x, rfl⟩
  · exact hne.imp fun a ha => ⟨ha, mem_of_superset htl (empty_subset _)⟩
  · exact ⟨x, hts rfl, htl⟩

中文:
定理 存在_mem_singleton_mem_of_mem_of_nonempty_of_对任意_separating
  结论: (p : 集合 α -> 命题)
  证明: by
  rcases exists_subset_subsingleton_mem_of_forall_separating p hs hl with ⟨t, hts, ht, htl⟩
  rcases ht.eq_empty_or_singleton with rfl | ⟨x, rfl⟩
  · exact hne.imp fun a ha => ⟨ha, mem_of_superset htl (empty_subset _)⟩
  · exact ⟨x, hts rfl, htl⟩

Depends on / 依赖: empty_subset, eq_empty_or_singleton, exists_subset_subsingleton_mem_of_forall_separating, hne.imp, ht.eq_empty_or_singleton, mem_of_superset
-/
theorem exists_mem_singleton_mem_of_mem_of_nonempty_of_forall_separating (p : Set α -> Prop)
    {s : Set α} [HasCountableSeparatingOn α p s] (hs : s in l) (hne : s.Nonempty)
    (hl : forall U, p U -> U in l ∨ Uᶜ in l) : exists a in s, {a} in l := by
  rcases exists_subset_subsingleton_mem_of_forall_separating p hs hl with ⟨t, hts, ht, htl⟩
  rcases ht.eq_empty_or_singleton with rfl | ⟨x, rfl⟩
  · exact hne.imp fun a ha => ⟨ha, mem_of_superset htl (empty_subset _)⟩
  · exact ⟨x, hts rfl, htl⟩

/--
theorem `exists_singleton_mem_of_mem_of_forall_separating` / 定理 `exists_singleton_mem_of_mem_of_forall_separating`

English:
theorem exists_singleton_mem_of_mem_of_forall_separating
  statement: [Nonempty α] (p : Set α -> Prop)
  proof: by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact ‹Nonempty α›.elim fun a => ⟨a, mem_of_superset hs (empty_subset _)⟩
  · exact (exists_mem_singleton_mem_of_mem_of_nonempty_of_forall_separating p hs hne hl).imp fun _ =>
      And.right

中文:
定理 存在_singleton_mem_of_mem_of_对任意_separating
  结论: [非空 α] (p : 集合 α -> 命题)
  证明: by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact ‹Nonempty α›.elim fun a => ⟨a, mem_of_superset hs (empty_subset _)⟩
  · exact (exists_mem_singleton_mem_of_mem_of_nonempty_of_forall_separating p hs hne hl).imp fun _ =>
      And.right

Depends on / 依赖: And.right, Nonempty, empty_subset, eq_empty_or_nonempty, exists_mem_singleton_mem_of_mem_of_nonempty_of_forall_separating, mem_of_superset, s.eq_empty_or_nonempty
-/
theorem exists_singleton_mem_of_mem_of_forall_separating [Nonempty α] (p : Set α -> Prop)
    {s : Set α} [HasCountableSeparatingOn α p s] (hs : s in l) (hl : forall U, p U -> U in l ∨ Uᶜ in l) :
    exists a, {a} in l := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact ‹Nonempty α›.elim fun a => ⟨a, mem_of_superset hs (empty_subset _)⟩
  · exact (exists_mem_singleton_mem_of_mem_of_nonempty_of_forall_separating p hs hne hl).imp fun _ =>
      And.right

/--
theorem `exists_subsingleton_mem_of_forall_separating` / 定理 `exists_subsingleton_mem_of_forall_separating`

English:
theorem exists_subsingleton_mem_of_forall_separating
  statement: (p : Set α -> Prop)
  proof: let ⟨t, _, hts, htl⟩ := exists_subset_subsingleton_mem_of_forall_separating p univ_mem hl
  ⟨t, hts, htl⟩

中文:
定理 存在_subsingleton_mem_of_对任意_separating
  结论: (p : 集合 α -> 命题)
  证明: let ⟨t, _, hts, htl⟩ := exists_subset_subsingleton_mem_of_forall_separating p univ_mem hl
  ⟨t, hts, htl⟩

Depends on / 依赖: exists_subset_subsingleton_mem_of_forall_separating, univ_mem
-/
theorem exists_subsingleton_mem_of_forall_separating (p : Set α -> Prop)
    [HasCountableSeparatingOn α p univ] (hl : forall U, p U -> U in l ∨ Uᶜ in l) :
    exists s : Set α, s.Subsingleton ∧ s in l :=
  let ⟨t, _, hts, htl⟩ := exists_subset_subsingleton_mem_of_forall_separating p univ_mem hl
  ⟨t, hts, htl⟩

/--
theorem `exists_singleton_mem_of_forall_separating` / 定理 `exists_singleton_mem_of_forall_separating`

English:
theorem exists_singleton_mem_of_forall_separating
  statement: [Nonempty α] (p : Set α -> Prop)
  proof: exists_singleton_mem_of_mem_of_forall_separating p univ_mem hl

中文:
定理 存在_singleton_mem_of_对任意_separating
  结论: [非空 α] (p : 集合 α -> 命题)
  证明: exists_singleton_mem_of_mem_of_forall_separating p univ_mem hl

Depends on / 依赖: exists_singleton_mem_of_mem_of_forall_separating, univ_mem
-/
theorem exists_singleton_mem_of_forall_separating [Nonempty α] (p : Set α -> Prop)
    [HasCountableSeparatingOn α p univ] (hl : forall U, p U -> U in l ∨ Uᶜ in l) :
    exists x : α, {x} in l :=
  exists_singleton_mem_of_mem_of_forall_separating p univ_mem hl


/--
theorem `exists_mem_eventuallyEq_const_of_eventually_mem_of_forall_separating` / 定理 `exists_mem_eventuallyEq_const_of_eventually_mem_of_forall_separating`

English:
theorem exists_mem_eventuallyEq_const_of_eventually_mem_of_forall_separating
  statement: (p : Set β -> Prop)
  proof: exists_mem_singleton_mem_of_mem_of_nonempty_of_forall_separating p (l := map f l) hs hne h

中文:
定理 存在_mem_eventuallyEq_const_of_eventually_mem_of_对任意_separating
  结论: (p : 集合 β -> 命题)
  证明: exists_mem_singleton_mem_of_mem_of_nonempty_of_forall_separating p (l := map f l) hs hne h

Depends on / 依赖: exists_mem_singleton_mem_of_mem_of_nonempty_of_forall_separating
-/
theorem exists_mem_eventuallyEq_const_of_eventually_mem_of_forall_separating (p : Set β -> Prop)
    {s : Set β} [HasCountableSeparatingOn β p s] (hs : forallᶠ x in l, f x in s) (hne : s.Nonempty)
    (h : forall U, p U -> (forallᶠ x in l, f x in U) ∨ (forallᶠ x in l, f x ∉ U)) :
    exists a in s, f =ᶠ[l] const α a :=
  exists_mem_singleton_mem_of_mem_of_nonempty_of_forall_separating p (l := map f l) hs hne h

/--
theorem `exists_eventuallyEq_const_of_eventually_mem_of_forall_separating` / 定理 `exists_eventuallyEq_const_of_eventually_mem_of_forall_separating`

English:
theorem exists_eventuallyEq_const_of_eventually_mem_of_forall_separating
  statement: [Nonempty β]
  proof: exists_singleton_mem_of_mem_of_forall_separating (l := map f l) p hs h

中文:
定理 存在_eventuallyEq_const_of_eventually_mem_of_对任意_separating
  结论: [非空 β]
  证明: exists_singleton_mem_of_mem_of_forall_separating (l := map f l) p hs h

Depends on / 依赖: exists_singleton_mem_of_mem_of_forall_separating
-/
theorem exists_eventuallyEq_const_of_eventually_mem_of_forall_separating [Nonempty β]
    (p : Set β -> Prop) {s : Set β} [HasCountableSeparatingOn β p s] (hs : forallᶠ x in l, f x in s)
    (h : forall U, p U -> (forallᶠ x in l, f x in U) ∨ (forallᶠ x in l, f x ∉ U)) :
    exists a, f =ᶠ[l] const α a :=
  exists_singleton_mem_of_mem_of_forall_separating (l := map f l) p hs h

/--
theorem `exists_eventuallyEq_const_of_forall_separating` / 定理 `exists_eventuallyEq_const_of_forall_separating`

English:
theorem exists_eventuallyEq_const_of_forall_separating
  statement: [Nonempty β] (p : Set β -> Prop)
  proof: exists_singleton_mem_of_forall_separating (l := map f l) p h

中文:
定理 存在_eventuallyEq_const_of_对任意_separating
  结论: [非空 β] (p : 集合 β -> 命题)
  证明: exists_singleton_mem_of_forall_separating (l := map f l) p h

Depends on / 依赖: exists_singleton_mem_of_forall_separating
-/
theorem exists_eventuallyEq_const_of_forall_separating [Nonempty β] (p : Set β -> Prop)
    [HasCountableSeparatingOn β p univ]
    (h : forall U, p U -> (forallᶠ x in l, f x in U) ∨ (forallᶠ x in l, f x ∉ U)) :
    exists a, f =ᶠ[l] const α a :=
  exists_singleton_mem_of_forall_separating (l := map f l) p h

namespace EventuallyEq


/--
theorem `of_eventually_mem_of_forall_separating_mem_iff` / 定理 `of_eventually_mem_of_forall_separating_mem_iff`

English:
theorem of_eventually_mem_of_forall_separating_mem_iff
  statement: (p : Set β -> Prop) {s : Set β}
  proof: by
  rcases h'.1 with ⟨S, hSc, hSp, hS⟩
  have H : forallᶠ x in l, forall s in S, f x in s ↔ g x in s :=
    (eventually_countable_ball hSc).2 fun s hs => (h _ (hSp _ hs))
  filter_upwards [H, hf, hg] with x hx hxf hxg using hS _ hxf _ hxg hx

中文:
定理 of_eventually_mem_of_对任意_separating_mem_iff
  结论: (p : 集合 β -> 命题) {s : 集合 β}
  证明: by
  rcases h'.1 with ⟨S, hSc, hSp, hS⟩
  have H : forallᶠ x in l, forall s in S, f x in s ↔ g x in s :=
    (eventually_countable_ball hSc).2 fun s hs => (h _ (hSp _ hs))
  filter_upwards [H, hf, hg] with x hx hxf hxg using hS _ hxf _ hxg hx

Depends on / 依赖: eventually_countable_ball, filter_upwards
-/
theorem of_eventually_mem_of_forall_separating_mem_iff (p : Set β -> Prop) {s : Set β}
    [h' : HasCountableSeparatingOn β p s] (hf : forallᶠ x in l, f x in s) (hg : forallᶠ x in l, g x in s)
    (h : forall U : Set β, p U -> forallᶠ x in l, f x in U ↔ g x in U) : f =ᶠ[l] g := by
  rcases h'.1 with ⟨S, hSc, hSp, hS⟩
  have H : forallᶠ x in l, forall s in S, f x in s ↔ g x in s :=
    (eventually_countable_ball hSc).2 fun s hs => (h _ (hSp _ hs))
  filter_upwards [H, hf, hg] with x hx hxf hxg using hS _ hxf _ hxg hx

/--
theorem `of_forall_separating_mem_iff` / 定理 `of_forall_separating_mem_iff`

English:
theorem of_forall_separating_mem_iff
  statement: (p : Set β -> Prop)
  proof: of_eventually_mem_of_forall_separating_mem_iff p (s := univ) univ_mem univ_mem h

中文:
定理 of_对任意_separating_mem_iff
  结论: (p : 集合 β -> 命题)
  证明: of_eventually_mem_of_forall_separating_mem_iff p (s := univ) univ_mem univ_mem h

Depends on / 依赖: of_eventually_mem_of_forall_separating_mem_iff, univ_mem
-/
theorem of_forall_separating_mem_iff (p : Set β -> Prop)
    [HasCountableSeparatingOn β p univ] (h : forall U : Set β, p U -> forallᶠ x in l, f x in U ↔ g x in U) :
    f =ᶠ[l] g :=
  of_eventually_mem_of_forall_separating_mem_iff p (s := univ) univ_mem univ_mem h

/--
theorem `of_eventually_mem_of_forall_separating_preimage` / 定理 `of_eventually_mem_of_forall_separating_preimage`

English:
theorem of_eventually_mem_of_forall_separating_preimage
  statement: (p : Set β -> Prop) {s : Set β}
  proof: of_eventually_mem_of_forall_separating_mem_iff p hf hg fun U hU => (h U hU).mem_iff

中文:
定理 of_eventually_mem_of_对任意_separating_preimage
  结论: (p : 集合 β -> 命题) {s : 集合 β}
  证明: of_eventually_mem_of_forall_separating_mem_iff p hf hg fun U hU => (h U hU).mem_iff

Depends on / 依赖: mem_iff, of_eventually_mem_of_forall_separating_mem_iff
-/
theorem of_eventually_mem_of_forall_separating_preimage (p : Set β -> Prop) {s : Set β}
    [HasCountableSeparatingOn β p s] (hf : forallᶠ x in l, f x in s) (hg : forallᶠ x in l, g x in s)
    (h : forall U : Set β, p U -> f ⁻¹' U =ᶠ[l] g ⁻¹' U) : f =ᶠ[l] g :=
  of_eventually_mem_of_forall_separating_mem_iff p hf hg fun U hU => (h U hU).mem_iff

/--
theorem `of_forall_separating_preimage` / 定理 `of_forall_separating_preimage`

English:
theorem of_forall_separating_preimage
  statement: (p : Set β -> Prop) [HasCountableSeparatingOn β p univ]
  proof: of_eventually_mem_of_forall_separating_preimage p (s := univ) univ_mem univ_mem h

中文:
定理 of_对任意_separating_preimage
  结论: (p : 集合 β -> 命题) [有余untableSeparatingOn β p univ]
  证明: of_eventually_mem_of_forall_separating_preimage p (s := univ) univ_mem univ_mem h

Depends on / 依赖: of_eventually_mem_of_forall_separating_preimage, univ_mem
-/
theorem of_forall_separating_preimage (p : Set β -> Prop) [HasCountableSeparatingOn β p univ]
    (h : forall U : Set β, p U -> f ⁻¹' U =ᶠ[l] g ⁻¹' U) : f =ᶠ[l] g :=
  of_eventually_mem_of_forall_separating_preimage p (s := univ) univ_mem univ_mem h

end EventuallyEq

end Filter
