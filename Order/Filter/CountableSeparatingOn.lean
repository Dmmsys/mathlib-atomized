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

/-- We say that a type `α` has a *countable separating family of sets* satisfying a predicate
`p : Set α → Prop` on a set `t` if there exists a countable family of sets `S : Set (Set α)` such
that all sets `s ∈ S` satisfy `p` and any two distinct points `x y ∈ t`, `x ≠ y`, can be separated
by `s ∈ S`: there exists `s ∈ S` such that exactly one of `x` and `y` belongs to `s`.

E.g., if `α` is a `T₀` topological space with second countable topology, then it has a countable
separating family of open sets and a countable separating family of closed sets.
-/
/-
**HasCountableSeparatingOn** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → (Set α → Prop) → Set α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a type `α` has a *countable separating family of sets* satisfying a 
predicate
`p : Set α → Prop` on a set `t` if there exists a countable family of sets `S : 
Set (Set α)` such
that all sets `s ∈ S` satisfy `p` and any two distinct points `x y ∈ t`, `x ≠ y`
, can be separated
by `s ∈ S`: there exists `s ∈ S` such that exactly one of `x` and `y` belongs to
 `s`.

E.g., if `α` is a `T₀` topological space with second countable topology, then it
 has a countable
separating family of open sets and a countable separating family of closed sets.
-/
class HasCountableSeparatingOn (α : Type*) (p : Set α → Prop) (t : Set α) : Prop where
  exists_countable_separating : ∃ S : Set (Set α), S.Countable ∧ (∀ s ∈ S, p s) ∧
    ∀ x ∈ t, ∀ y ∈ t, (∀ s ∈ S, x ∈ s ↔ y ∈ s) → x = y
/-
**exists_countable_separating** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_countable_separating (α : Type*) (p : Set α -> Prop) (t : Set α) [h
 : HasCountableSeparatingOn α p t] : exists S : Set (Set α), S.Countable ∧ (fora
ll s in S, p s) ∧ forall x in t, forall y in t, (forall s in S, x in s ↔ y in s)
 -> x = y
参数：α : Type*；p : Set α -> Prop；t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasCountableSeparatingOn.exists_countable_separating`：∀ {α : Type u_1} {
p : Set α → Prop} {t : Set α} [self : HasCountableSeparatingOn α p t],   ∃ S, S.
Countable ∧ (∀ s ∈ S, p s) ∧ ∀ x ∈ t, ∀ y …
-/
theorem exists_countable_separating (α : Type*) (p : Set α → Prop) (t : Set α)
    [h : HasCountableSeparatingOn α p t] :
    ∃ S : Set (Set α), S.Countable ∧ (∀ s ∈ S, p s) ∧
      ∀ x ∈ t, ∀ y ∈ t, (∀ s ∈ S, x ∈ s ↔ y ∈ s) → x = y :=
  h.1
/-
**exists_nonempty_countable_separating** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_nonempty_countable_separating (α : Type*) {p : Set α -> Prop} {s₀} 
(hp : p s₀) (t : Set α) [HasCountableSeparatingOn α p t] : exists S : Set (Set α
), S.Nonempty ∧ S.Countable ∧ (forall s in S, p s) ∧ forall x in t, forall y in 
t, (forall s in S, x in s ↔ y in s) -> x = y
参数：α : Type*；hp : p s₀；t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_countable_separating`：exists_countable_separating (α : Type*) (p 
: Set α -> Prop) (t : Set α) [h : HasCountableSeparatingOn α p t] : exists S : S
et (Set α), S.Cou…
· 使用定理 `Set.insert_nonempty`：insert_nonempty (a : α) (s : Set α) : (insert a s).
Nonempty
· 使用定理 `Set.Countable.insert`：∀ {α : Type u} {s : Set α} (a : α), s.Countable → 
(insert a s).Countable
· 使用定理 `Set.forall_insert_of_forall`：forall_insert_of_forall {P : α -> Prop} {a 
: α} {s : Set α} (H : forall x, x in s -> P x) (ha : P a) (x) (h : x in insert a
 s) : P x
· 使用定理 `Set.forall_of_forall_insert`：forall_of_forall_insert {P : α -> Prop} {a 
: α} {s : Set α} (H : forall x, x in insert a s -> P x) (x) (h : x in s) : P x
-/
theorem exists_nonempty_countable_separating (α : Type*) {p : Set α → Prop} {s₀} (hp : p s₀)
    (t : Set α) [HasCountableSeparatingOn α p t] :
    ∃ S : Set (Set α), S.Nonempty ∧ S.Countable ∧ (∀ s ∈ S, p s) ∧
      ∀ x ∈ t, ∀ y ∈ t, (∀ s ∈ S, x ∈ s ↔ y ∈ s) → x = y :=
  let ⟨S, hSc, hSp, hSt⟩ := exists_countable_separating α p t
  ⟨insert s₀ S, insert_nonempty _ _, hSc.insert _, forall_insert_of_forall hSp hp,
    fun x hx y hy hxy ↦ hSt x hx y hy <| forall_of_forall_insert hxy⟩
/-
**exists_seq_separating** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_seq_separating (α : Type*) {p : Set α -> Prop} {s₀} (hp : p s₀) (t 
: Set α) [HasCountableSeparatingOn α p t] : exists S : Nat -> Set α, (forall n, 
p (S n)) ∧ forall x in t, forall y in t, (forall n, x in S n ↔ y in S n) -> x = 
y
参数：α : Type*；hp : p s₀；t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_nonempty_countable_separating`：exists_nonempty_countable_separati
ng (α : Type*) {p : Set α -> Prop} {s₀} (hp : p s₀) (t : Set α) [HasCountableSep
aratingOn α p t] : exists …
· 使用定理 `Set.Countable.exists_eq_range`：∀ {α : Type u} {s : Set α}, s.Countable →
 s.Nonempty → ∃ f, s = Set.range f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem exists_seq_separating (α : Type*) {p : Set α → Prop} {s₀} (hp : p s₀) (t : Set α)
    [HasCountableSeparatingOn α p t] :
    ∃ S : ℕ → Set α, (∀ n, p (S n)) ∧ ∀ x ∈ t, ∀ y ∈ t, (∀ n, x ∈ S n ↔ y ∈ S n) → x = y := by
  rcases exists_nonempty_countable_separating α hp t with ⟨S, hSne, hSc, hS⟩
  rcases hSc.exists_eq_range hSne with ⟨S, rfl⟩
  use S
  simpa only [forall_mem_range] using hS
/-
**HasCountableSeparatingOn.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasCountableSeparatingOn.mono {α} {p₁ p₂ : Set α -> Prop} {t₁ t₂ : Set α} 
[h : HasCountableSeparatingOn α p₁ t₁] (hp : forall s, p₁ s -> p₂ s) (ht : t₂ su
bseteq t₁) : HasCountableSeparatingOn α p₂ t₂ where exists_countable_separating
参数：hp : forall s, p₁ s -> p₂ s；ht : t₂ subseteq t₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasCountableSeparatingOn.exists_countable_separating`：∀ {α : Type u_1} {
p : Set α → Prop} {t : Set α} [self : HasCountableSeparatingOn α p t],   ∃ S, S.
Countable ∧ (∀ s ∈ S, p s) ∧ ∀ x ∈ t, ∀ y …
-/
theorem HasCountableSeparatingOn.mono {α} {p₁ p₂ : Set α → Prop} {t₁ t₂ : Set α}
    [h : HasCountableSeparatingOn α p₁ t₁] (hp : ∀ s, p₁ s → p₂ s) (ht : t₂ ⊆ t₁) :
    HasCountableSeparatingOn α p₂ t₂ where
  exists_countable_separating :=
    let ⟨S, hSc, hSp, hSt⟩ := h.1
    ⟨S, hSc, fun s hs ↦ hp s (hSp s hs), fun x hx y hy ↦ hSt x (ht hx) y (ht hy)⟩
/-
**HasCountableSeparatingOn.of_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasCountableSeparatingOn.of_subtype {α : Type*} {p : Set α -> Prop} {t : S
et α} {q : Set t -> Prop} [h : HasCountableSeparatingOn t q univ] (hpq : forall 
U, q U -> exists V, p V ∧ (↑) ⁻¹' V = U) : HasCountableSeparatingOn α p t
参数：hpq : forall U, q U -> exists V, p V ∧ (↑) ⁻¹' V = U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasCountableSeparatingOn.exists_countable_separating`：∀ {α : Type u_1} {
p : Set α → Prop} {t : Set α} [self : HasCountableSeparatingOn α p t],   ∃ S, S.
Countable ∧ (∀ s ∈ S, p s) ∧ ∀ x ∈ t, ∀ y …
· 使用定理 `Set.Countable.image`：∀ {α : Type u} {β : Type v} {s : Set α}, s.Countabl
e → ∀ (f : α → β), (f '' s).Countable
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_image`：forall_mem_image {f : α -> β} {s : Set α} {p : β -
> Prop} : (forall y in f '' s, p y) ↔ forall ⦃x⦄, x in s -> p (f x)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `trivial`：True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Function.sometimes_spec`：sometimes_spec {p : Prop} {α} [Nonempty α] (P :
 α -> Prop) (f : p -> α) (a : p) (h : P (f a)) : P (sometimes f)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem HasCountableSeparatingOn.of_subtype {α : Type*} {p : Set α → Prop} {t : Set α}
    {q : Set t → Prop} [h : HasCountableSeparatingOn t q univ]
    (hpq : ∀ U, q U → ∃ V, p V ∧ (↑) ⁻¹' V = U) : HasCountableSeparatingOn α p t := by
  rcases h.1 with ⟨S, hSc, hSq, hS⟩
  choose! V hpV hV using fun s hs ↦ hpq s (hSq s hs)
  refine ⟨⟨V '' S, hSc.image _, forall_mem_image.2 hpV, fun x hx y hy h ↦ ?_⟩⟩
  refine congr_arg Subtype.val (hS ⟨x, hx⟩ trivial ⟨y, hy⟩ trivial fun U hU ↦ ?_)
  rw [← hV U hU]
  exact h _ (mem_image_of_mem _ hU)
/-
**HasCountableSeparatingOn.subtype_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasCountableSeparatingOn.subtype_iff {α : Type*} {p : Set α -> Prop} {t : 
Set α} : HasCountableSeparatingOn t (fun u => exists v, p v ∧ (↑) ⁻¹' v = u) uni
v ↔ HasCountableSeparatingOn α p t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasCountableSeparatingOn.of_subtype`：HasCountableSeparatingOn.of_subtype
 {α : Type*} {p : Set α -> Prop} {t : Set α} {q : Set t -> Prop} [h : HasCountab
leSeparatingOn t q univ] …
· 使用定理 `Set.Countable.image`：∀ {α : Type u} {β : Type v} {s : Set α}, s.Countabl
e → ∀ (f : α → β), (f '' s).Countable
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Subtype.coe_prop`：coe_prop {S : Set α} (a : { a // a in S }) : ↑a in S
-/
theorem HasCountableSeparatingOn.subtype_iff {α : Type*} {p : Set α → Prop} {t : Set α} :
    HasCountableSeparatingOn t (fun u ↦ ∃ v, p v ∧ (↑) ⁻¹' v = u) univ ↔
    HasCountableSeparatingOn α p t := by
  constructor <;> intro h
  · exact h.of_subtype <| fun s ↦ id
  rcases h with ⟨S, Sct, Sp, hS⟩
  use {Subtype.val ⁻¹' s | s ∈ S}, Sct.image _, ?_, ?_
  · rintro u ⟨t, tS, rfl⟩
    exact ⟨t, Sp _ tS, rfl⟩
  rintro x - y - hxy
  exact Subtype.val_injective <| hS _ (Subtype.coe_prop _) _ (Subtype.coe_prop _)
    fun s hs ↦ hxy (Subtype.val ⁻¹' s) ⟨s, hs, rfl⟩

namespace Filter

variable {α β : Type*} {l : Filter α} [CountableInterFilter l] {f g : α → β}

/-!
### Filters supported on a (sub)singleton

In this section we prove several versions of the following theorem. Let `l : Filter α` be a filter
with countable intersections property. Let `p : Set α → Prop` be a property such that there exists a
countable family of sets satisfying `p` and separating points of `α`. Then `l` is supported on
a subsingleton: there exists a subsingleton `t` such that `t ∈ l`.

With extra `Nonempty`/`Set.Nonempty` assumptions one can ensure that `t` is a singleton `{x}`.

If `s ∈ l`, then it suffices to assume that the countable family separates only points of `s`.
-/

/-
**Filter.exists_subset_subsingleton_mem_of_forall_separating** 是 Mathlib 中的一个定理，
位于命名空间 `Filter`。
形式化陈述：exists_subset_subsingleton_mem_of_forall_separating (p : Set α -> Prop) {s
 : Set α} [h : HasCountableSeparatingOn α p s] (hs : s in l) (hl : forall U, p U
 -> U in l ∨ Uᶜ in l) : exists t, t subseteq s ∧ t.Subsingleton ∧ t in l
参数：p : Set α -> Prop；hs : s in l；hl : forall U, p U -> U in l ∨ Uᶜ in l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasCountableSeparatingOn.exists_countable_separating`：∀ {α : Type u_1} {
p : Set α → Prop} {t : Set α} [self : HasCountableSeparatingOn α p t],   ∃ S, S.
Countable ∧ (∀ s ∈ S, p s) ∧ ∀ x ∈ t, ∀ y …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `countable_sInter_mem`：countable_sInter_mem {S : Set (Set α)} (hSc : S.Co
untable) : ⋂₀ S in l ↔ forall s in S, s in l
· 使用定理 `Set.Countable.mono`：∀ {α : Type u} {s₁ s₂ : Set α}, s₁ ⊆ s₂ → s₂.Countab
le → s₁.Countable
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `countable_bInter_mem`：countable_bInter_mem {ι : Type*} {S : Set ι} (hS :
 S.Countable) {s : forall i in S, Set α} : (⋂ i, ⋂ hi : i in S, s i ‹_›) in l ↔ 
forall i, …
· 使用定理 `Filter.iInter_mem'`：iInter_mem' {β : Sort v} {s : β -> Set α} [Subsingle
ton β] : (⋂ i, s i) in f ↔ forall i, s i in f
· 使用定理 `instSubsingleton`：∀ (p : Prop), Subsingleton p

--- 原说明 ---
### Filters supported on a (sub)singleton

In this section we prove several versions of the following theorem. Let `l : Fil
ter α` be a filter
with countable intersections property. Let `p : Set α → Prop` be a property such
 that there exists a
countable family of sets satisfying `p` and separating points of `α`. Then `l` i
s supported on
a subsingleton: there exists a subsingleton `t` such that `t ∈ l`.

With extra `Nonempty`/`Set.Nonempty` assumptions one can ensure that `t` is a si
ngleton `{x}`.

If `s ∈ l`, then it suffices to assume that the countable family separates only 
points of `s`.
-/
theorem exists_subset_subsingleton_mem_of_forall_separating (p : Set α → Prop)
    {s : Set α} [h : HasCountableSeparatingOn α p s] (hs : s ∈ l)
    (hl : ∀ U, p U → U ∈ l ∨ Uᶜ ∈ l) : ∃ t, t ⊆ s ∧ t.Subsingleton ∧ t ∈ l := by
  rcases h.1 with ⟨S, hSc, hSp, hS⟩
  refine ⟨s ∩ ⋂₀ (S ∩ l.sets) ∩ ⋂ (U ∈ S) (_ : Uᶜ ∈ l), Uᶜ, ?_, ?_, ?_⟩
  · exact fun _ h ↦ h.1.1
  · intro x hx y hy
    simp only [mem_sInter, mem_inter_iff, mem_iInter, mem_compl_iff] at hx hy
    refine hS x hx.1.1 y hy.1.1 (fun s hsS ↦ ?_)
    cases hl s (hSp s hsS) with
    | inl hsl => simp only [hx.1.2 s ⟨hsS, hsl⟩, hy.1.2 s ⟨hsS, hsl⟩]
    | inr hsl => simp only [hx.2 s hsS hsl, hy.2 s hsS hsl]
  · exact inter_mem
      (inter_mem hs ((countable_sInter_mem (hSc.mono inter_subset_left)).2 fun _ h ↦ h.2))
      ((countable_bInter_mem hSc).2 fun U hU ↦ iInter_mem'.2 id)
/-
**Filter.exists_mem_singleton_mem_of_mem_of_nonempty_of_forall_separating** 是 Ma
thlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：exists_mem_singleton_mem_of_mem_of_nonempty_of_forall_separating (p : Set 
α -> Prop) {s : Set α} [HasCountableSeparatingOn α p s] (hs : s in l) (hne : s.N
onempty) (hl : forall U, p U -> U in l ∨ Uᶜ in l) : exists a in s, {a} in l
参数：p : Set α -> Prop；hs : s in l；hne : s.Nonempty；hl : forall U, p U -> U in l ∨
 Uᶜ in l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.exists_subset_subsingleton_mem_of_forall_separating`：exists_subse
t_subsingleton_mem_of_forall_separating (p : Set α -> Prop) {s : Set α} [h : Has
CountableSeparatingOn α p s] (hs : s in l) (hl :…
· 使用定理 `Set.Subsingleton.eq_empty_or_singleton`：∀ {α : Type u} {s : Set α}, s.Su
bsingleton → s = ∅ ∨ ∃ x, s = {x}
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem exists_mem_singleton_mem_of_mem_of_nonempty_of_forall_separating (p : Set α → Prop)
    {s : Set α} [HasCountableSeparatingOn α p s] (hs : s ∈ l) (hne : s.Nonempty)
    (hl : ∀ U, p U → U ∈ l ∨ Uᶜ ∈ l) : ∃ a ∈ s, {a} ∈ l := by
  rcases exists_subset_subsingleton_mem_of_forall_separating p hs hl with ⟨t, hts, ht, htl⟩
  rcases ht.eq_empty_or_singleton with rfl | ⟨x, rfl⟩
  · exact hne.imp fun a ha ↦ ⟨ha, mem_of_superset htl (empty_subset _)⟩
  · exact ⟨x, hts rfl, htl⟩
/-
**Filter.exists_singleton_mem_of_mem_of_forall_separating** 是 Mathlib 中的一个定理，位于命
名空间 `Filter`。
形式化陈述：exists_singleton_mem_of_mem_of_forall_separating [Nonempty α] (p : Set α -
> Prop) {s : Set α} [HasCountableSeparatingOn α p s] (hs : s in l) (hl : forall 
U, p U -> U in l ∨ Uᶜ in l) : exists a, {a} in l
参数：p : Set α -> Prop；hs : s in l；hl : forall U, p U -> U in l ∨ Uᶜ in l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.exists_mem_singleton_mem_of_mem_of_nonempty_of_forall_separating`
：exists_mem_singleton_mem_of_mem_of_nonempty_of_forall_separating (p : Set α -> 
Prop) {s : Set α} [HasCountableSeparatingOn α p s] (hs : s in…
-/
theorem exists_singleton_mem_of_mem_of_forall_separating [Nonempty α] (p : Set α → Prop)
    {s : Set α} [HasCountableSeparatingOn α p s] (hs : s ∈ l) (hl : ∀ U, p U → U ∈ l ∨ Uᶜ ∈ l) :
    ∃ a, {a} ∈ l := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact ‹Nonempty α›.elim fun a ↦ ⟨a, mem_of_superset hs (empty_subset _)⟩
  · exact (exists_mem_singleton_mem_of_mem_of_nonempty_of_forall_separating p hs hne hl).imp fun _ ↦
      And.right
/-
**Filter.exists_subsingleton_mem_of_forall_separating** 是 Mathlib 中的一个定理，位于命名空间 
`Filter`。
形式化陈述：exists_subsingleton_mem_of_forall_separating (p : Set α -> Prop) [HasCount
ableSeparatingOn α p univ] (hl : forall U, p U -> U in l ∨ Uᶜ in l) : exists s :
 Set α, s.Subsingleton ∧ s in l
参数：p : Set α -> Prop；hl : forall U, p U -> U in l ∨ Uᶜ in l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.exists_subset_subsingleton_mem_of_forall_separating`：exists_subse
t_subsingleton_mem_of_forall_separating (p : Set α -> Prop) {s : Set α} [h : Has
CountableSeparatingOn α p s] (hs : s in l) (hl :…
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
-/
theorem exists_subsingleton_mem_of_forall_separating (p : Set α → Prop)
    [HasCountableSeparatingOn α p univ] (hl : ∀ U, p U → U ∈ l ∨ Uᶜ ∈ l) :
    ∃ s : Set α, s.Subsingleton ∧ s ∈ l :=
  let ⟨t, _, hts, htl⟩ := exists_subset_subsingleton_mem_of_forall_separating p univ_mem hl
  ⟨t, hts, htl⟩
/-
**Filter.exists_singleton_mem_of_forall_separating** 是 Mathlib 中的一个定理，位于命名空间 `Fi
lter`。
形式化陈述：exists_singleton_mem_of_forall_separating [Nonempty α] (p : Set α -> Prop)
 [HasCountableSeparatingOn α p univ] (hl : forall U, p U -> U in l ∨ Uᶜ in l) : 
exists x : α, {x} in l
参数：p : Set α -> Prop；hl : forall U, p U -> U in l ∨ Uᶜ in l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.exists_singleton_mem_of_mem_of_forall_separating`：exists_singleto
n_mem_of_mem_of_forall_separating [Nonempty α] (p : Set α -> Prop) {s : Set α} [
HasCountableSeparatingOn α p s] (hs : s in l)…
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
-/
theorem exists_singleton_mem_of_forall_separating [Nonempty α] (p : Set α → Prop)
    [HasCountableSeparatingOn α p univ] (hl : ∀ U, p U → U ∈ l ∨ Uᶜ ∈ l) :
    ∃ x : α, {x} ∈ l :=
  exists_singleton_mem_of_mem_of_forall_separating p univ_mem hl

/-!
### Eventually constant functions

In this section we apply theorems from the previous section to the filter `Filter.map f l` to show
that `f : α → β` is eventually constant along `l` if for every `U` from the separating family,
either `∀ᶠ x in l, f x ∈ U` or `∀ᶠ x in l, f x ∉ U`.
-/

/-
**Filter.exists_mem_eventuallyEq_const_of_eventually_mem_of_forall_separating** 
是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：exists_mem_eventuallyEq_const_of_eventually_mem_of_forall_separating (p : 
Set β -> Prop) {s : Set β} [HasCountableSeparatingOn β p s] (hs : forallᶠ x in l
, f x in s) (hne : s.Nonempty) (h : forall U, p U -> (forallᶠ x in l, f x in U) 
∨ (forallᶠ x in l, f x ∉ U)) : exists a in s, f =ᶠ[l] const α a
参数：p : Set β -> Prop；hs : forallᶠ x in l, f x in s；hne : s.Nonempty；h : forall U
, p U -> (forallᶠ x in l, f x in U) ∨ (forallᶠ x in l, f x ∉ U)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.exists_mem_singleton_mem_of_mem_of_nonempty_of_forall_separating`
：exists_mem_singleton_mem_of_mem_of_nonempty_of_forall_separating (p : Set α -> 
Prop) {s : Set α} [HasCountableSeparatingOn α p s] (hs : s in…
· 使用定理 `instCountableInterFilterMap`：∀ {α : Type u_2} {β : Type u_3} (l : Filter
 α) [CountableInterFilter l] (f : α → β),   CountableInterFilter (Filter.map f l
)

--- 原说明 ---
### Eventually constant functions

In this section we apply theorems from the previous section to the filter `Filte
r.map f l` to show
that `f : α → β` is eventually constant along `l` if for every `U` from the sepa
rating family,
either `∀ᶠ x in l, f x ∈ U` or `∀ᶠ x in l, f x ∉ U`.
-/
theorem exists_mem_eventuallyEq_const_of_eventually_mem_of_forall_separating (p : Set β → Prop)
    {s : Set β} [HasCountableSeparatingOn β p s] (hs : ∀ᶠ x in l, f x ∈ s) (hne : s.Nonempty)
    (h : ∀ U, p U → (∀ᶠ x in l, f x ∈ U) ∨ (∀ᶠ x in l, f x ∉ U)) :
    ∃ a ∈ s, f =ᶠ[l] const α a :=
  exists_mem_singleton_mem_of_mem_of_nonempty_of_forall_separating p (l := map f l) hs hne h
/-
**Filter.exists_eventuallyEq_const_of_eventually_mem_of_forall_separating** 是 Ma
thlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：exists_eventuallyEq_const_of_eventually_mem_of_forall_separating [Nonempty
 β] (p : Set β -> Prop) {s : Set β} [HasCountableSeparatingOn β p s] (hs : foral
lᶠ x in l, f x in s) (h : forall U, p U -> (forallᶠ x in l, f x in U) ∨ (forallᶠ
 x in l, f x ∉ U)) : exists a, f =ᶠ[l] const α a
参数：p : Set β -> Prop；hs : forallᶠ x in l, f x in s；h : forall U, p U -> (forallᶠ
 x in l, f x in U) ∨ (forallᶠ x in l, f x ∉ U)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.exists_singleton_mem_of_mem_of_forall_separating`：exists_singleto
n_mem_of_mem_of_forall_separating [Nonempty α] (p : Set α -> Prop) {s : Set α} [
HasCountableSeparatingOn α p s] (hs : s in l)…
· 使用定理 `instCountableInterFilterMap`：∀ {α : Type u_2} {β : Type u_3} (l : Filter
 α) [CountableInterFilter l] (f : α → β),   CountableInterFilter (Filter.map f l
)
-/
theorem exists_eventuallyEq_const_of_eventually_mem_of_forall_separating [Nonempty β]
    (p : Set β → Prop) {s : Set β} [HasCountableSeparatingOn β p s] (hs : ∀ᶠ x in l, f x ∈ s)
    (h : ∀ U, p U → (∀ᶠ x in l, f x ∈ U) ∨ (∀ᶠ x in l, f x ∉ U)) :
    ∃ a, f =ᶠ[l] const α a :=
  exists_singleton_mem_of_mem_of_forall_separating (l := map f l) p hs h
/-
**Filter.exists_eventuallyEq_const_of_forall_separating** 是 Mathlib 中的一个定理，位于命名空
间 `Filter`。
形式化陈述：exists_eventuallyEq_const_of_forall_separating [Nonempty β] (p : Set β -> 
Prop) [HasCountableSeparatingOn β p univ] (h : forall U, p U -> (forallᶠ x in l,
 f x in U) ∨ (forallᶠ x in l, f x ∉ U)) : exists a, f =ᶠ[l] const α a
参数：p : Set β -> Prop；h : forall U, p U -> (forallᶠ x in l, f x in U) ∨ (forallᶠ 
x in l, f x ∉ U)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.exists_singleton_mem_of_forall_separating`：exists_singleton_mem_o
f_forall_separating [Nonempty α] (p : Set α -> Prop) [HasCountableSeparatingOn α
 p univ] (hl : forall U, p U -> U in l…
· 使用定理 `instCountableInterFilterMap`：∀ {α : Type u_2} {β : Type u_3} (l : Filter
 α) [CountableInterFilter l] (f : α → β),   CountableInterFilter (Filter.map f l
)
-/
theorem exists_eventuallyEq_const_of_forall_separating [Nonempty β] (p : Set β → Prop)
    [HasCountableSeparatingOn β p univ]
    (h : ∀ U, p U → (∀ᶠ x in l, f x ∈ U) ∨ (∀ᶠ x in l, f x ∉ U)) :
    ∃ a, f =ᶠ[l] const α a :=
  exists_singleton_mem_of_forall_separating (l := map f l) p h

namespace EventuallyEq

/-!
### Eventually equal functions

In this section we show that two functions are equal along a filter with countable intersections
property if the preimages of all sets from a countable separating family of sets are equal along
the filter.
-/

/-
**Filter.EventuallyEq.of_eventually_mem_of_forall_separating_mem_iff** 是 Mathlib
 中的一个定理，位于命名空间 `Filter.EventuallyEq`。
形式化陈述：of_eventually_mem_of_forall_separating_mem_iff (p : Set β -> Prop) {s : Se
t β} [h' : HasCountableSeparatingOn β p s] (hf : forallᶠ x in l, f x in s) (hg :
 forallᶠ x in l, g x in s) (h : forall U : Set β, p U -> forallᶠ x in l, f x in 
U ↔ g x in U) : f =ᶠ[l] g
参数：p : Set β -> Prop；hf : forallᶠ x in l, f x in s；hg : forallᶠ x in l, g x in s
；h : forall U : Set β, p U -> forallᶠ x in l, f x in U ↔ g x in U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasCountableSeparatingOn.exists_countable_separating`：∀ {α : Type u_1} {
p : Set α → Prop} {t : Set α} [self : HasCountableSeparatingOn α p t],   ∃ S, S.
Countable ∧ (∀ s ∈ S, p s) ∧ ∀ x ∈ t, ∀ y …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eventually_countable_ball`：eventually_countable_ball {ι : Type*} {S : Se
t ι} (hS : S.Countable) {p : α -> forall i in S, Prop} : (forallᶠ x in l, forall
 i hi, p x i hi…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f

--- 原说明 ---
### Eventually equal functions

In this section we show that two functions are equal along a filter with countab
le intersections
property if the preimages of all sets from a countable separating family of sets
 are equal along
the filter.
-/
theorem of_eventually_mem_of_forall_separating_mem_iff (p : Set β → Prop) {s : Set β}
    [h' : HasCountableSeparatingOn β p s] (hf : ∀ᶠ x in l, f x ∈ s) (hg : ∀ᶠ x in l, g x ∈ s)
    (h : ∀ U : Set β, p U → ∀ᶠ x in l, f x ∈ U ↔ g x ∈ U) : f =ᶠ[l] g := by
  rcases h'.1 with ⟨S, hSc, hSp, hS⟩
  have H : ∀ᶠ x in l, ∀ s ∈ S, f x ∈ s ↔ g x ∈ s :=
    (eventually_countable_ball hSc).2 fun s hs ↦ (h _ (hSp _ hs))
  filter_upwards [H, hf, hg] with x hx hxf hxg using hS _ hxf _ hxg hx
/-
**Filter.EventuallyEq.of_forall_separating_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fi
lter.EventuallyEq`。
形式化陈述：of_forall_separating_mem_iff (p : Set β -> Prop) [HasCountableSeparatingOn
 β p univ] (h : forall U : Set β, p U -> forallᶠ x in l, f x in U ↔ g x in U) : 
f =ᶠ[l] g
参数：p : Set β -> Prop；h : forall U : Set β, p U -> forallᶠ x in l, f x in U ↔ g x
 in U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.of_eventually_mem_of_forall_separating_mem_iff`：of_e
ventually_mem_of_forall_separating_mem_iff (p : Set β -> Prop) {s : Set β} [h' :
 HasCountableSeparatingOn β p s] (hf : forallᶠ x in l, f…
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
-/
theorem of_forall_separating_mem_iff (p : Set β → Prop)
    [HasCountableSeparatingOn β p univ] (h : ∀ U : Set β, p U → ∀ᶠ x in l, f x ∈ U ↔ g x ∈ U) :
    f =ᶠ[l] g :=
  of_eventually_mem_of_forall_separating_mem_iff p (s := univ) univ_mem univ_mem h
/-
**Filter.EventuallyEq.of_eventually_mem_of_forall_separating_preimage** 是 Mathli
b 中的一个定理，位于命名空间 `Filter.EventuallyEq`。
形式化陈述：of_eventually_mem_of_forall_separating_preimage (p : Set β -> Prop) {s : S
et β} [HasCountableSeparatingOn β p s] (hf : forallᶠ x in l, f x in s) (hg : for
allᶠ x in l, g x in s) (h : forall U : Set β, p U -> f ⁻¹' U =ᶠ[l] g ⁻¹' U) : f 
=ᶠ[l] g
参数：p : Set β -> Prop；hf : forallᶠ x in l, f x in s；hg : forallᶠ x in l, g x in s
；h : forall U : Set β, p U -> f ⁻¹' U =ᶠ[l] g ⁻¹' U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.of_eventually_mem_of_forall_separating_mem_iff`：of_e
ventually_mem_of_forall_separating_mem_iff (p : Set β -> Prop) {s : Set β} [h' :
 HasCountableSeparatingOn β p s] (hf : forallᶠ x in l, f…
· 使用定理 `Filter.EventuallyEq.mem_iff`：∀ {α : Type u} {s t : Set α} {l : Filter α}
, s =ᶠ[l] t → ∀ᶠ (x : α) in l, x ∈ s ↔ x ∈ t
-/
theorem of_eventually_mem_of_forall_separating_preimage (p : Set β → Prop) {s : Set β}
    [HasCountableSeparatingOn β p s] (hf : ∀ᶠ x in l, f x ∈ s) (hg : ∀ᶠ x in l, g x ∈ s)
    (h : ∀ U : Set β, p U → f ⁻¹' U =ᶠ[l] g ⁻¹' U) : f =ᶠ[l] g :=
  of_eventually_mem_of_forall_separating_mem_iff p hf hg fun U hU ↦ (h U hU).mem_iff
/-
**Filter.EventuallyEq.of_forall_separating_preimage** 是 Mathlib 中的一个定理，位于命名空间 `F
ilter.EventuallyEq`。
形式化陈述：of_forall_separating_preimage (p : Set β -> Prop) [HasCountableSeparatingO
n β p univ] (h : forall U : Set β, p U -> f ⁻¹' U =ᶠ[l] g ⁻¹' U) : f =ᶠ[l] g
参数：p : Set β -> Prop；h : forall U : Set β, p U -> f ⁻¹' U =ᶠ[l] g ⁻¹' U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.of_eventually_mem_of_forall_separating_preimage`：of_
eventually_mem_of_forall_separating_preimage (p : Set β -> Prop) {s : Set β} [Ha
sCountableSeparatingOn β p s] (hf : forallᶠ x in l, f x i…
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
-/
theorem of_forall_separating_preimage (p : Set β → Prop) [HasCountableSeparatingOn β p univ]
    (h : ∀ U : Set β, p U → f ⁻¹' U =ᶠ[l] g ⁻¹' U) : f =ᶠ[l] g :=
  of_eventually_mem_of_forall_separating_preimage p (s := univ) univ_mem univ_mem h

end EventuallyEq

end Filter

