/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
module

public import Mathlib.Data.Set.Insert
public import Mathlib.Tactic.ByContra

/-!
# Subsingleton

Defines the predicate `Subsingleton s : Prop`, saying that `s` has at most one element.

Also defines `Nontrivial s : Prop` : the predicate saying that `s` has at least two distinct
elements.

-/

@[expose] public section

assert_not_exists HeytingAlgebra RelIso

open Function

universe u v

namespace Set

/-! ### Subsingleton -/

section Subsingleton

variable {α : Type u} {a : α} {s t : Set α}

/--
Definition of `Subsingleton` / `Subsingleton` 的定义

English:
definition Subsingleton
  signature: (s : Set α)
  body: forall ⦃x⦄ (_ : x in s) ⦃y⦄ (_ : y in s), x = y

中文:
定义 Subsingleton
  签名: (s : Set α)
  定义体: forall ⦃x⦄ (_ : x in s) ⦃y⦄ (_ : y in s), x = y
-/
protected def Subsingleton (s : Set α) : Prop :=
  forall ⦃x⦄ (_ : x in s) ⦃y⦄ (_ : y in s), x = y

/--
theorem `Subsingleton.anti` / 定理 `Subsingleton.anti`

English:
theorem Subsingleton.anti
  given: (ht : t.Subsingleton) (hst : s subseteq t)
  statement: s.Subsingleton
  proof: fun _ hx _ hy =>
  ht (hst hx) (hst hy)

中文:
定理 Subsingleton.anti
  条件: (ht : t.Subsingleton) (hst : s subseteq t)
  结论: s.Subsingleton
  证明: fun _ hx _ hy =>
  ht (hst hx) (hst hy)
-/
theorem Subsingleton.anti (ht : t.Subsingleton) (hst : s subseteq t) : s.Subsingleton := fun _ hx _ hy =>
  ht (hst hx) (hst hy)

/--
theorem `Subsingleton.eq_singleton_of_mem` / 定理 `Subsingleton.eq_singleton_of_mem`

English:
theorem Subsingleton.eq_singleton_of_mem
  given: (hs : s.Subsingleton) {x : α} (hx : x in s)
  statement: s = {x}
  proof: ext fun _ => ⟨fun hy => hs hx hy ▸ mem_singleton _, fun hy => (eq_of_mem_singleton hy).symm ▸ hx⟩

@[simp]

中文:
定理 Subsingleton.eq_singleton_of_mem
  条件: (hs : s.Subsingleton) {x : α} (hx : x in s)
  结论: s = {x}
  证明: ext fun _ => ⟨fun hy => hs hx hy ▸ mem_singleton _, fun hy => (eq_of_mem_singleton hy).symm ▸ hx⟩

@[simp]

Depends on / 依赖: eq_of_mem_singleton, mem_singleton
-/
theorem Subsingleton.eq_singleton_of_mem (hs : s.Subsingleton) {x : α} (hx : x in s) : s = {x} :=
  ext fun _ => ⟨fun hy => hs hx hy ▸ mem_singleton _, fun hy => (eq_of_mem_singleton hy).symm ▸ hx⟩

@[simp]
/--
theorem `subsingleton_empty` / 定理 `subsingleton_empty`

English:
theorem subsingleton_empty
  statement: (∅ : Set α).Subsingleton
  proof: fun _ => False.elim

@[simp]

中文:
定理 subsingleton_empty
  结论: (∅ : Set α).Subsingleton
  证明: fun _ => False.elim

@[simp]

Depends on / 依赖: False.elim
-/
theorem subsingleton_empty : (∅ : Set α).Subsingleton := fun _ => False.elim

@[simp]
/--
theorem `subsingleton_singleton` / 定理 `subsingleton_singleton`

English:
theorem subsingleton_singleton
  given: {a}
  statement: ({a} : Set α).Subsingleton
  proof: fun _ hx _ hy =>
  (eq_of_mem_singleton hx).symm ▸ (eq_of_mem_singleton hy).symm ▸ rfl

中文:
定理 subsingleton_singleton
  条件: {a}
  结论: ({a} : Set α).Subsingleton
  证明: fun _ hx _ hy =>
  (eq_of_mem_singleton hx).symm ▸ (eq_of_mem_singleton hy).symm ▸ rfl
-/
theorem subsingleton_singleton {a} : ({a} : Set α).Subsingleton := fun _ hx _ hy =>
  (eq_of_mem_singleton hx).symm ▸ (eq_of_mem_singleton hy).symm ▸ rfl

/--
theorem `subsingleton_of_subset_singleton` / 定理 `subsingleton_of_subset_singleton`

English:
theorem subsingleton_of_subset_singleton
  given: (h : s subseteq {a})
  statement: s.Subsingleton
  proof: subsingleton_singleton.anti h

中文:
定理 subsingleton_of_subset_singleton
  条件: (h : s subseteq {a})
  结论: s.Subsingleton
  证明: subsingleton_singleton.anti h

Depends on / 依赖: subsingleton_singleton, subsingleton_singleton.anti
-/
theorem subsingleton_of_subset_singleton (h : s subseteq {a}) : s.Subsingleton :=
  subsingleton_singleton.anti h

/--
theorem `subsingleton_of_forall_eq` / 定理 `subsingleton_of_forall_eq`

English:
theorem subsingleton_of_forall_eq
  given: (a : α) (h : forall b in s, b = a)
  statement: s.Subsingleton
  proof: fun _ hb _ hc =>
  (h _ hb).trans (h _ hc).symm

中文:
定理 subsingleton_of_forall_eq
  条件: (a : α) (h : 对任意 b in s, b = a)
  结论: s.Subsingleton
  证明: fun _ hb _ hc =>
  (h _ hb).trans (h _ hc).symm
-/
theorem subsingleton_of_forall_eq (a : α) (h : forall b in s, b = a) : s.Subsingleton := fun _ hb _ hc =>
  (h _ hb).trans (h _ hc).symm

/--
theorem `subsingleton_iff_singleton` / 定理 `subsingleton_iff_singleton`

English:
theorem subsingleton_iff_singleton
  given: {x} (hx : x in s)
  statement: s.Subsingleton ↔ s = {x}
  proof: ⟨fun h => h.eq_singleton_of_mem hx, fun h => h.symm ▸ subsingleton_singleton⟩

中文:
定理 subsingleton_iff_singleton
  条件: {x} (hx : x in s)
  结论: s.Subsingleton ↔ s = {x}
  证明: ⟨fun h => h.eq_singleton_of_mem hx, fun h => h.symm ▸ subsingleton_singleton⟩

Depends on / 依赖: eq_singleton_of_mem, h.eq_singleton_of_mem, h.symm, subsingleton_singleton
-/
theorem subsingleton_iff_singleton {x} (hx : x in s) : s.Subsingleton ↔ s = {x} :=
  ⟨fun h => h.eq_singleton_of_mem hx, fun h => h.symm ▸ subsingleton_singleton⟩

/--
theorem `Subsingleton.eq_empty_or_singleton` / 定理 `Subsingleton.eq_empty_or_singleton`

English:
theorem Subsingleton.eq_empty_or_singleton
  given: (hs : s.Subsingleton)
  statement: s = ∅ ∨ exists x, s = {x}
  proof: s.eq_empty_or_nonempty.elim Or.inl fun ⟨x, hx⟩ => Or.inr ⟨x, hs.eq_singleton_of_mem hx⟩

中文:
定理 Subsingleton.eq_empty_or_singleton
  条件: (hs : s.Subsingleton)
  结论: s = ∅ ∨ 存在 x, s = {x}
  证明: s.eq_empty_or_nonempty.elim Or.inl fun ⟨x, hx⟩ => Or.inr ⟨x, hs.eq_singleton_of_mem hx⟩

Depends on / 依赖: Or.inl, Or.inr, eq_empty_or_nonempty, eq_singleton_of_mem, hs.eq_singleton_of_mem, s.eq_empty_or_nonempty.elim
-/
theorem Subsingleton.eq_empty_or_singleton (hs : s.Subsingleton) : s = ∅ ∨ exists x, s = {x} :=
  s.eq_empty_or_nonempty.elim Or.inl fun ⟨x, hx⟩ => Or.inr ⟨x, hs.eq_singleton_of_mem hx⟩

/--
theorem `subsingleton_iff_eq_empty_or_singleton` / 定理 `subsingleton_iff_eq_empty_or_singleton`

English:
theorem subsingleton_iff_eq_empty_or_singleton
  statement: s.Subsingleton ↔ s = ∅ ∨ exists x, s = {x}
  proof: ⟨Subsingleton.eq_empty_or_singleton, by rintro (_ | ⟨_, rfl⟩) <;> simp_all⟩

中文:
定理 subsingleton_iff_eq_empty_or_singleton
  结论: s.Subsingleton ↔ s = ∅ ∨ 存在 x, s = {x}
  证明: ⟨Subsingleton.eq_empty_or_singleton, by rintro (_ | ⟨_, rfl⟩) <;> simp_all⟩

Depends on / 依赖: Subsingleton, Subsingleton.eq_empty_or_singleton, eq_empty_or_singleton
-/
theorem subsingleton_iff_eq_empty_or_singleton : s.Subsingleton ↔ s = ∅ ∨ exists x, s = {x} :=
  ⟨Subsingleton.eq_empty_or_singleton, by rintro (_ | ⟨_, rfl⟩) <;> simp_all⟩

/--
theorem `Subsingleton.induction_on` / 定理 `Subsingleton.induction_on`

English:
theorem Subsingleton.induction_on
  statement: {p : Set α -> Prop} (hs : s.Subsingleton) (he : p ∅)
  proof: by
  rcases hs.eq_empty_or_singleton with (rfl | ⟨x, rfl⟩)
  exacts [he, h₁ _]

中文:
定理 Subsingleton.induction_on
  结论: {p : Set α -> 命题} (hs : s.Subsingleton) (he : p ∅)
  证明: by
  rcases hs.eq_empty_or_singleton with (rfl | ⟨x, rfl⟩)
  exacts [he, h₁ _]

Depends on / 依赖: eq_empty_or_singleton, exacts, hs.eq_empty_or_singleton
-/
theorem Subsingleton.induction_on {p : Set α -> Prop} (hs : s.Subsingleton) (he : p ∅)
    (h₁ : forall x, p {x}) : p s := by
  rcases hs.eq_empty_or_singleton with (rfl | ⟨x, rfl⟩)
  exacts [he, h₁ _]

/--
theorem `subsingleton_univ` / 定理 `subsingleton_univ`

English:
theorem subsingleton_univ
  given: [Subsingleton α]
  statement: (univ : Set α).Subsingleton
  proof: fun x _ y _ =>
  Subsingleton.elim x y

中文:
定理 subsingleton_univ
  条件: [Subsingleton α]
  结论: (univ : Set α).Subsingleton
  证明: fun x _ y _ =>
  Subsingleton.elim x y
-/
theorem subsingleton_univ [Subsingleton α] : (univ : Set α).Subsingleton := fun x _ y _ =>
  Subsingleton.elim x y

/--
theorem `subsingleton_of_univ_subsingleton` / 定理 `subsingleton_of_univ_subsingleton`

English:
theorem subsingleton_of_univ_subsingleton
  given: (h : (univ : Set α).Subsingleton)
  statement: Subsingleton α
  proof: ⟨fun a b => h (mem_univ a) (mem_univ b)⟩

@[simp]

中文:
定理 subsingleton_of_univ_subsingleton
  条件: (h : (univ : Set α).Subsingleton)
  结论: Subsingleton α
  证明: ⟨fun a b => h (mem_univ a) (mem_univ b)⟩

@[simp]

Depends on / 依赖: mem_univ
-/
theorem subsingleton_of_univ_subsingleton (h : (univ : Set α).Subsingleton) : Subsingleton α :=
  ⟨fun a b => h (mem_univ a) (mem_univ b)⟩

@[simp]
/--
theorem `subsingleton_univ_iff` / 定理 `subsingleton_univ_iff`

English:
theorem subsingleton_univ_iff
  statement: (univ : Set α).Subsingleton ↔ Subsingleton α
  proof: ⟨subsingleton_of_univ_subsingleton, fun h => @subsingleton_univ _ h⟩

中文:
定理 subsingleton_univ_iff
  结论: (univ : Set α).Subsingleton ↔ Subsingleton α
  证明: ⟨subsingleton_of_univ_subsingleton, fun h => @subsingleton_univ _ h⟩

Depends on / 依赖: subsingleton_of_univ_subsingleton, subsingleton_univ
-/
theorem subsingleton_univ_iff : (univ : Set α).Subsingleton ↔ Subsingleton α :=
  ⟨subsingleton_of_univ_subsingleton, fun h => @subsingleton_univ _ h⟩

/--
lemma `Subsingleton.inter_singleton` / 引理 `Subsingleton.inter_singleton`

English:
lemma Subsingleton.inter_singleton
  statement: (s inter {a}).Subsingleton
  proof: Set.subsingleton_of_subset_singleton Set.inter_subset_right

中文:
引理 Subsingleton.inter_singleton
  结论: (s inter {a}).Subsingleton
  证明: Set.subsingleton_of_subset_singleton Set.inter_subset_right

Depends on / 依赖: Set.inter_subset_right, Set.subsingleton_of_subset_singleton, inter_subset_right, subsingleton_of_subset_singleton
-/
lemma Subsingleton.inter_singleton : (s inter {a}).Subsingleton :=
  Set.subsingleton_of_subset_singleton Set.inter_subset_right

/--
lemma `Subsingleton.singleton_inter` / 引理 `Subsingleton.singleton_inter`

English:
lemma Subsingleton.singleton_inter
  statement: ({a} inter s).Subsingleton
  proof: Set.subsingleton_of_subset_singleton Set.inter_subset_left

中文:
引理 Subsingleton.singleton_inter
  结论: ({a} inter s).Subsingleton
  证明: Set.subsingleton_of_subset_singleton Set.inter_subset_left

Depends on / 依赖: Set.inter_subset_left, Set.subsingleton_of_subset_singleton, inter_subset_left, subsingleton_of_subset_singleton
-/
lemma Subsingleton.singleton_inter : ({a} inter s).Subsingleton :=
  Set.subsingleton_of_subset_singleton Set.inter_subset_left

/--
lemma `subsingleton_of_subsingleton_inter_left` / 引理 `subsingleton_of_subsingleton_inter_left`

English:
lemma subsingleton_of_subsingleton_inter_left
  given: (h : (s union t).Subsingleton)
  proof: fun _ h₁ _ h₂ => h (.inl h₁) (.inl h₂)

中文:
引理 subsingleton_of_subsingleton_inter_left
  条件: (h : (s union t).Subsingleton)
  证明: fun _ h₁ _ h₂ => h (.inl h₁) (.inl h₂)
-/
lemma subsingleton_of_subsingleton_inter_left (h : (s union t).Subsingleton) :
    s.Subsingleton :=
  fun _ h₁ _ h₂ => h (.inl h₁) (.inl h₂)

/--
lemma `subsingleton_of_subsingleton_inter_right` / 引理 `subsingleton_of_subsingleton_inter_right`

English:
lemma subsingleton_of_subsingleton_inter_right
  given: (h : (s union t).Subsingleton)
  proof: fun _ h₁ _ h₂ => h (.inr h₁) (.inr h₂)

中文:
引理 subsingleton_of_subsingleton_inter_right
  条件: (h : (s union t).Subsingleton)
  证明: fun _ h₁ _ h₂ => h (.inr h₁) (.inr h₂)
-/
lemma subsingleton_of_subsingleton_inter_right (h : (s union t).Subsingleton) :
    t.Subsingleton :=
  fun _ h₁ _ h₂ => h (.inr h₁) (.inr h₂)

/--
theorem `subsingleton_of_subsingleton` / 定理 `subsingleton_of_subsingleton`

English:
theorem subsingleton_of_subsingleton
  given: [Subsingleton α] {s : Set α}
  statement: s.Subsingleton
  proof: subsingleton_univ.anti (subset_univ s)

@[to_dual]

中文:
定理 subsingleton_of_subsingleton
  条件: [Subsingleton α] {s : Set α}
  结论: s.Subsingleton
  证明: subsingleton_univ.anti (subset_univ s)

@[to_dual]

Depends on / 依赖: subset_univ, subsingleton_univ, subsingleton_univ.anti
-/
theorem subsingleton_of_subsingleton [Subsingleton α] {s : Set α} : s.Subsingleton :=
  subsingleton_univ.anti (subset_univ s)

@[to_dual]
/--
theorem `subsingleton_isTop` / 定理 `subsingleton_isTop`

English:
theorem subsingleton_isTop
  given: (α : Type*) [PartialOrder α]
  statement: { x : α | IsTop x }.Subsingleton
  proof: fun x hx _ hy => hx.isMax.eq_of_le (hy x)

中文:
定理 subsingleton_isTop
  条件: (α : 类型) [PartialOrder α]
  结论: { x : α | IsTop x }.Subsingleton
  证明: fun x hx _ hy => hx.isMax.eq_of_le (hy x)

Depends on / 依赖: eq_of_le, hx.isMax.eq_of_le
-/
theorem subsingleton_isTop (α : Type*) [PartialOrder α] : { x : α | IsTop x }.Subsingleton :=
  fun x hx _ hy => hx.isMax.eq_of_le (hy x)

/--
theorem `exists_eq_singleton_iff_nonempty_subsingleton` / 定理 `exists_eq_singleton_iff_nonempty_subsingleton`

English:
theorem exists_eq_singleton_iff_nonempty_subsingleton
  proof: by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨a, rfl⟩
    exact ⟨singleton_nonempty a, subsingleton_singleton⟩
  · exact h.2.eq_empty_or_singleton.resolve_left h.1.ne_empty

中文:
定理 exists_eq_singleton_iff_nonempty_subsingleton
  证明: by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨a, rfl⟩
    exact ⟨singleton_nonempty a, subsingleton_singleton⟩
  · exact h.2.eq_empty_or_singleton.resolve_left h.1.ne_empty

Depends on / 依赖: eq_empty_or_singleton, eq_empty_or_singleton.resolve_left, ne_empty, resolve_left, singleton_nonempty, subsingleton_singleton
-/
theorem exists_eq_singleton_iff_nonempty_subsingleton :
    (exists a : α, s = {a}) ↔ s.Nonempty ∧ s.Subsingleton := by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨a, rfl⟩
    exact ⟨singleton_nonempty a, subsingleton_singleton⟩
  · exact h.2.eq_empty_or_singleton.resolve_left h.1.ne_empty

/--
theorem `eq_empty_or_singleton_of_subsingleton` / 定理 `eq_empty_or_singleton_of_subsingleton`

English:
theorem eq_empty_or_singleton_of_subsingleton
  given: [Subsingleton α] (s : Set α)
  proof: subsingleton_of_subsingleton.eq_empty_or_singleton

中文:
定理 eq_empty_or_singleton_of_subsingleton
  条件: [Subsingleton α] (s : Set α)
  证明: subsingleton_of_subsingleton.eq_empty_or_singleton

Depends on / 依赖: eq_empty_or_singleton, subsingleton_of_subsingleton, subsingleton_of_subsingleton.eq_empty_or_singleton
-/
theorem eq_empty_or_singleton_of_subsingleton [Subsingleton α] (s : Set α) :
    s = ∅ ∨ exists a, s = {a} :=
  subsingleton_of_subsingleton.eq_empty_or_singleton

/--
theorem `eq_empty_or_singleton_of_unique` / 定理 `eq_empty_or_singleton_of_unique`

English:
theorem eq_empty_or_singleton_of_unique
  given: [Unique α] (s : Set α)
  proof: s.eq_empty_or_singleton_of_subsingleton.imp_right fun ⟨a, ha⟩ => Unique.eq_default a ▸ ha

中文:
定理 eq_empty_or_singleton_of_unique
  条件: [Unique α] (s : Set α)
  证明: s.eq_empty_or_singleton_of_subsingleton.imp_right fun ⟨a, ha⟩ => Unique.eq_default a ▸ ha

Depends on / 依赖: Unique, Unique.eq_default, eq_default, eq_empty_or_singleton_of_subsingleton, imp_right, s.eq_empty_or_singleton_of_subsingleton.imp_right
-/
theorem eq_empty_or_singleton_of_unique [Unique α] (s : Set α) :
    s = ∅ ∨ s = {default} :=
  s.eq_empty_or_singleton_of_subsingleton.imp_right fun ⟨a, ha⟩ => Unique.eq_default a ▸ ha

/-- `s`, coerced to a type, is a subsingleton type if and only if `s` is a subsingleton set. -/
@[simp, norm_cast]
/--
theorem `subsingleton_coe` / 定理 `subsingleton_coe`

English:
theorem subsingleton_coe
  given: (s : Set α)
  statement: Subsingleton s ↔ s.Subsingleton
  proof: by
  constructor
  · intro h a ha b hb
    exact SetCoe.ext_iff.2 (@Subsingleton.elim s h ⟨a, ha⟩ ⟨b, hb⟩)
  · exact fun h => Subsingleton.intro fun a b => SetCoe.ext (h a.property b.property)

中文:
定理 subsingleton_coe
  条件: (s : Set α)
  结论: Subsingleton s ↔ s.Subsingleton
  证明: by
  constructor
  · intro h a ha b hb
    exact SetCoe.ext_iff.2 (@Subsingleton.elim s h ⟨a, ha⟩ ⟨b, hb⟩)
  · exact fun h => Subsingleton.intro fun a b => SetCoe.ext (h a.property b.property)

Depends on / 依赖: SetCoe, SetCoe.ext, SetCoe.ext_iff, Subsingleton, Subsingleton.elim, Subsingleton.intro, a.property, b.property, ext_iff, property
-/
theorem subsingleton_coe (s : Set α) : Subsingleton s ↔ s.Subsingleton := by
  constructor
  · intro h a ha b hb
    exact SetCoe.ext_iff.2 (@Subsingleton.elim s h ⟨a, ha⟩ ⟨b, hb⟩)
  · exact fun h => Subsingleton.intro fun a b => SetCoe.ext (h a.property b.property)

/--
theorem `Subsingleton.coe_sort` / 定理 `Subsingleton.coe_sort`

English:
theorem Subsingleton.coe_sort
  given: {s : Set α}
  statement: s.Subsingleton -> Subsingleton s
  proof: s.subsingleton_coe.2

中文:
定理 Subsingleton.coe_sort
  条件: {s : Set α}
  结论: s.Subsingleton -> Subsingleton s
  证明: s.subsingleton_coe.2

Depends on / 依赖: s.subsingleton_coe, subsingleton_coe
-/
theorem Subsingleton.coe_sort {s : Set α} : s.Subsingleton -> Subsingleton s :=
  s.subsingleton_coe.2

/--
Instance `subsingleton_coe_of_subsingleton` / 实例 `subsingleton_coe_of_subsingleton`

English:
instance subsingleton_coe_of_subsingleton
  signature: [Subsingleton α] {s : Set α}
  body: by
  rw [s.subsingleton_coe]
  exact subsingleton_of_subsingleton

中文:
实例 subsingleton_coe_of_subsingleton
  签名: [Subsingleton α] {s : Set α}
  定义体: by
  rw [s.subsingleton_coe]
  exact subsingleton_of_subsingleton

Depends on / 依赖: s.subsingleton_coe, subsingleton_coe, subsingleton_of_subsingleton
-/
instance subsingleton_coe_of_subsingleton [Subsingleton α] {s : Set α} : Subsingleton s := by
  rw [s.subsingleton_coe]
  exact subsingleton_of_subsingleton

/--
lemma `Subsingleton.denselyOrdered` / 引理 `Subsingleton.denselyOrdered`

English:
lemma Subsingleton.denselyOrdered
  given: {s : Set α} [LT α] (hs : s.Subsingleton)
  proof: have := (subsingleton_coe _).mpr hs
  ⟨fun _ _ h => ⟨_, h.trans_eq (Subsingleton.elim _ _), h⟩⟩

中文:
引理 Subsingleton.denselyOrdered
  条件: {s : Set α} [LT α] (hs : s.Subsingleton)
  证明: have := (subsingleton_coe _).mpr hs
  ⟨fun _ _ h => ⟨_, h.trans_eq (Subsingleton.elim _ _), h⟩⟩

Depends on / 依赖: Subsingleton, Subsingleton.elim, h.trans_eq, subsingleton_coe, trans_eq
-/
lemma Subsingleton.denselyOrdered {s : Set α} [LT α] (hs : s.Subsingleton) :
    DenselyOrdered s :=
  have := (subsingleton_coe _).mpr hs
  ⟨fun _ _ h => ⟨_, h.trans_eq (Subsingleton.elim _ _), h⟩⟩

/--
theorem `_root_.ExistsUnique.setSubsingleton` / 定理 `_root_.ExistsUnique.setSubsingleton`

English:
theorem _root_.ExistsUnique.setSubsingleton
  given: {α : Type*} {p : α -> Prop} (h : ExistsUnique p)
  proof: fun _ hx _ hy => h.unique hx hy

中文:
定理 _root_.ExistsUnique.setSubsingleton
  条件: {α : 类型} {p : α -> 命题} (h : ExistsUnique p)
  证明: fun _ hx _ hy => h.unique hx hy

Depends on / 依赖: h.unique, unique
-/
theorem _root_.ExistsUnique.setSubsingleton {α : Type*} {p : α -> Prop} (h : ExistsUnique p) :
    {x | p x}.Subsingleton :=
  fun _ hx _ hy => h.unique hx hy

end Subsingleton

/-! ### Nontrivial -/

section Nontrivial

variable {α : Type u} {a : α} {s t : Set α}

/--
Definition of `Nontrivial` / `Nontrivial` 的定义

English:
definition Nontrivial
  signature: (s : Set α)
  body: exists x in s, exists y in s, x != y

中文:
定义 Nontrivial
  签名: (s : Set α)
  定义体: exists x in s, exists y in s, x != y
-/
protected def Nontrivial (s : Set α) : Prop :=
  exists x in s, exists y in s, x != y

/--
theorem `nontrivial_of_mem_mem_ne` / 定理 `nontrivial_of_mem_mem_ne`

English:
theorem nontrivial_of_mem_mem_ne
  given: {x y} (hx : x in s) (hy : y in s) (hxy : x != y)
  statement: s.Nontrivial
  proof: ⟨x, hx, y, hy, hxy⟩

中文:
定理 nontrivial_of_mem_mem_ne
  条件: {x y} (hx : x in s) (hy : y in s) (hxy : x != y)
  结论: s.Nontrivial
  证明: ⟨x, hx, y, hy, hxy⟩
-/
theorem nontrivial_of_mem_mem_ne {x y} (hx : x in s) (hy : y in s) (hxy : x != y) : s.Nontrivial :=
  ⟨x, hx, y, hy, hxy⟩

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def Nontrivial.choose (hs : s.Nontrivial)
  body: (Exists.choose hs, hs.choose_spec.right.choose)

中文:
定义 noncomputable
  签名: def Nontrivial.choose (hs : s.Nontrivial)
  定义体: (Exists.choose hs, hs.choose_spec.right.choose)
-/
protected noncomputable def Nontrivial.choose (hs : s.Nontrivial) : α × α :=
  (Exists.choose hs, hs.choose_spec.right.choose)

/--
theorem `Nontrivial.choose_fst_mem` / 定理 `Nontrivial.choose_fst_mem`

English:
theorem Nontrivial.choose_fst_mem
  given: (hs : s.Nontrivial)
  statement: hs.choose.fst in s
  proof: hs.choose_spec.left

中文:
定理 Nontrivial.choose_fst_mem
  条件: (hs : s.Nontrivial)
  结论: hs.choose.fst in s
  证明: hs.choose_spec.left
-/
protected theorem Nontrivial.choose_fst_mem (hs : s.Nontrivial) : hs.choose.fst in s :=
  hs.choose_spec.left

/--
theorem `Nontrivial.choose_snd_mem` / 定理 `Nontrivial.choose_snd_mem`

English:
theorem Nontrivial.choose_snd_mem
  given: (hs : s.Nontrivial)
  statement: hs.choose.snd in s
  proof: hs.choose_spec.right.choose_spec.left

中文:
定理 Nontrivial.choose_snd_mem
  条件: (hs : s.Nontrivial)
  结论: hs.choose.snd in s
  证明: hs.choose_spec.right.choose_spec.left
-/
protected theorem Nontrivial.choose_snd_mem (hs : s.Nontrivial) : hs.choose.snd in s :=
  hs.choose_spec.right.choose_spec.left

/--
theorem `Nontrivial.choose_fst_ne_choose_snd` / 定理 `Nontrivial.choose_fst_ne_choose_snd`

English:
theorem Nontrivial.choose_fst_ne_choose_snd
  given: (hs : s.Nontrivial)
  proof: hs.choose_spec.right.choose_spec.right

中文:
定理 Nontrivial.choose_fst_ne_choose_snd
  条件: (hs : s.Nontrivial)
  证明: hs.choose_spec.right.choose_spec.right
-/
protected theorem Nontrivial.choose_fst_ne_choose_snd (hs : s.Nontrivial) :
    hs.choose.fst != hs.choose.snd :=
  hs.choose_spec.right.choose_spec.right

/--
theorem `Nontrivial.mono` / 定理 `Nontrivial.mono`

English:
theorem Nontrivial.mono
  given: (hs : s.Nontrivial) (hst : s subseteq t)
  statement: t.Nontrivial
  proof: let ⟨x, hx, y, hy, hxy⟩ := hs
  ⟨x, hst hx, y, hst hy, hxy⟩

中文:
定理 Nontrivial.mono
  条件: (hs : s.Nontrivial) (hst : s subseteq t)
  结论: t.Nontrivial
  证明: let ⟨x, hx, y, hy, hxy⟩ := hs
  ⟨x, hst hx, y, hst hy, hxy⟩
-/
theorem Nontrivial.mono (hs : s.Nontrivial) (hst : s subseteq t) : t.Nontrivial :=
  let ⟨x, hx, y, hy, hxy⟩ := hs
  ⟨x, hst hx, y, hst hy, hxy⟩

/--
theorem `nontrivial_pair` / 定理 `nontrivial_pair`

English:
theorem nontrivial_pair
  given: {x y} (hxy : x != y)
  statement: ({x, y} : Set α).Nontrivial
  proof: ⟨x, mem_insert _ _, y, mem_insert_of_mem _ (mem_singleton _), hxy⟩

中文:
定理 nontrivial_pair
  条件: {x y} (hxy : x != y)
  结论: ({x, y} : Set α).Nontrivial
  证明: ⟨x, mem_insert _ _, y, mem_insert_of_mem _ (mem_singleton _), hxy⟩

Depends on / 依赖: mem_insert, mem_insert_of_mem, mem_singleton
-/
theorem nontrivial_pair {x y} (hxy : x != y) : ({x, y} : Set α).Nontrivial :=
  ⟨x, mem_insert _ _, y, mem_insert_of_mem _ (mem_singleton _), hxy⟩

/--
theorem `nontrivial_of_pair_subset` / 定理 `nontrivial_of_pair_subset`

English:
theorem nontrivial_of_pair_subset
  given: {x y} (hxy : x != y) (h : {x, y} subseteq s)
  statement: s.Nontrivial
  proof: (nontrivial_pair hxy).mono h

中文:
定理 nontrivial_of_pair_subset
  条件: {x y} (hxy : x != y) (h : {x, y} subseteq s)
  结论: s.Nontrivial
  证明: (nontrivial_pair hxy).mono h

Depends on / 依赖: nontrivial_pair
-/
theorem nontrivial_of_pair_subset {x y} (hxy : x != y) (h : {x, y} subseteq s) : s.Nontrivial :=
  (nontrivial_pair hxy).mono h

/--
theorem `Nontrivial.pair_subset` / 定理 `Nontrivial.pair_subset`

English:
theorem Nontrivial.pair_subset
  given: (hs : s.Nontrivial)
  statement: exists x y, x != y ∧ {x, y} subseteq s
  proof: let ⟨x, hx, y, hy, hxy⟩ := hs
⟨x, y, hxy, insert_subset hx singleton_subset_iff.2 hy⟩

中文:
定理 Nontrivial.pair_subset
  条件: (hs : s.Nontrivial)
  结论: 存在 x y, x != y ∧ {x, y} subseteq s
  证明: let ⟨x, hx, y, hy, hxy⟩ := hs
⟨x, y, hxy, insert_subset hx singleton_subset_iff.2 hy⟩

Depends on / 依赖: insert_subset, singleton_subset_iff
-/
theorem Nontrivial.pair_subset (hs : s.Nontrivial) : exists x y, x != y ∧ {x, y} subseteq s :=
  let ⟨x, hx, y, hy, hxy⟩ := hs
⟨x, y, hxy, insert_subset hx singleton_subset_iff.2 hy⟩

/--
theorem `nontrivial_iff_pair_subset` / 定理 `nontrivial_iff_pair_subset`

English:
theorem nontrivial_iff_pair_subset
  statement: s.Nontrivial ↔ exists x y, x != y ∧ {x, y} subseteq s
  proof: ⟨Nontrivial.pair_subset, fun H =>
    let ⟨_, _, hxy, h⟩ := H
    nontrivial_of_pair_subset hxy h⟩

中文:
定理 nontrivial_iff_pair_subset
  结论: s.Nontrivial ↔ 存在 x y, x != y ∧ {x, y} subseteq s
  证明: ⟨Nontrivial.pair_subset, fun H =>
    let ⟨_, _, hxy, h⟩ := H
    nontrivial_of_pair_subset hxy h⟩

Depends on / 依赖: Nontrivial, Nontrivial.pair_subset, nontrivial_of_pair_subset, pair_subset
-/
theorem nontrivial_iff_pair_subset : s.Nontrivial ↔ exists x y, x != y ∧ {x, y} subseteq s :=
  ⟨Nontrivial.pair_subset, fun H =>
    let ⟨_, _, hxy, h⟩ := H
    nontrivial_of_pair_subset hxy h⟩

/--
theorem `nontrivial_of_exists_ne` / 定理 `nontrivial_of_exists_ne`

English:
theorem nontrivial_of_exists_ne
  given: {x} (hx : x in s) (h : exists y in s, y != x)
  statement: s.Nontrivial
  proof: let ⟨y, hy, hyx⟩ := h
  ⟨y, hy, x, hx, hyx⟩

中文:
定理 nontrivial_of_exists_ne
  条件: {x} (hx : x in s) (h : 存在 y in s, y != x)
  结论: s.Nontrivial
  证明: let ⟨y, hy, hyx⟩ := h
  ⟨y, hy, x, hx, hyx⟩
-/
theorem nontrivial_of_exists_ne {x} (hx : x in s) (h : exists y in s, y != x) : s.Nontrivial :=
  let ⟨y, hy, hyx⟩ := h
  ⟨y, hy, x, hx, hyx⟩

/--
theorem `Nontrivial.exists_ne` / 定理 `Nontrivial.exists_ne`

English:
theorem Nontrivial.exists_ne
  given: (hs : s.Nontrivial) (z)
  statement: exists x in s, x != z
  proof: by
  by_contra! H
  rcases hs with ⟨x, hx, y, hy, hxy⟩
  rw [H x hx]; rw [H y hy] at hxy
  exact hxy rfl

中文:
定理 Nontrivial.exists_ne
  条件: (hs : s.Nontrivial) (z)
  结论: 存在 x in s, x != z
  证明: by
  by_contra! H
  rcases hs with ⟨x, hx, y, hy, hxy⟩
  rw [H x hx]; rw [H y hy] at hxy
  exact hxy rfl
-/
theorem Nontrivial.exists_ne (hs : s.Nontrivial) (z) : exists x in s, x != z := by
  by_contra! H
  rcases hs with ⟨x, hx, y, hy, hxy⟩
  rw [H x hx]; rw [H y hy] at hxy
  exact hxy rfl

/--
theorem `nontrivial_iff_exists_ne` / 定理 `nontrivial_iff_exists_ne`

English:
theorem nontrivial_iff_exists_ne
  given: {x} (hx : x in s)
  statement: s.Nontrivial ↔ exists y in s, y != x
  proof: ⟨fun H => H.exists_ne _, nontrivial_of_exists_ne hx⟩

中文:
定理 nontrivial_iff_exists_ne
  条件: {x} (hx : x in s)
  结论: s.Nontrivial ↔ 存在 y in s, y != x
  证明: ⟨fun H => H.exists_ne _, nontrivial_of_exists_ne hx⟩

Depends on / 依赖: H.exists_ne, exists_ne, nontrivial_of_exists_ne
-/
theorem nontrivial_iff_exists_ne {x} (hx : x in s) : s.Nontrivial ↔ exists y in s, y != x :=
  ⟨fun H => H.exists_ne _, nontrivial_of_exists_ne hx⟩

/--
theorem `nontrivial_of_lt` / 定理 `nontrivial_of_lt`

English:
theorem nontrivial_of_lt
  given: [Preorder α] {x y} (hx : x in s) (hy : y in s) (hxy : x < y)
  proof: ⟨x, hx, y, hy, ne_of_lt hxy⟩

中文:
定理 nontrivial_of_lt
  条件: [Preorder α] {x y} (hx : x in s) (hy : y in s) (hxy : x < y)
  证明: ⟨x, hx, y, hy, ne_of_lt hxy⟩

Depends on / 依赖: ne_of_lt
-/
theorem nontrivial_of_lt [Preorder α] {x y} (hx : x in s) (hy : y in s) (hxy : x < y) :
    s.Nontrivial :=
  ⟨x, hx, y, hy, ne_of_lt hxy⟩

/--
theorem `nontrivial_of_exists_lt` / 定理 `nontrivial_of_exists_lt`

English:
theorem nontrivial_of_exists_lt
  statement: [Preorder α]
  proof: let ⟨_, hx, _, hy, hxy⟩ := H
  nontrivial_of_lt hx hy hxy

中文:
定理 nontrivial_of_exists_lt
  结论: [Preorder α]
  证明: let ⟨_, hx, _, hy, hxy⟩ := H
  nontrivial_of_lt hx hy hxy

Depends on / 依赖: nontrivial_of_lt
-/
theorem nontrivial_of_exists_lt [Preorder α]
    (H : existsᵉ (x in s) (y in s), x < y) : s.Nontrivial :=
  let ⟨_, hx, _, hy, hxy⟩ := H
  nontrivial_of_lt hx hy hxy

/--
theorem `Nontrivial.exists_lt` / 定理 `Nontrivial.exists_lt`

English:
theorem Nontrivial.exists_lt
  given: [LinearOrder α] (hs : s.Nontrivial)
  statement: existsᵉ (x in s) (y in s), x < y
  proof: let ⟨x, hx, y, hy, hxy⟩ := hs
  Or.elim (lt_or_gt_of_ne hxy) (fun H => ⟨x, hx, y, hy, H⟩) fun H => ⟨y, hy, x, hx, H⟩

中文:
定理 Nontrivial.exists_lt
  条件: [LinearOrder α] (hs : s.Nontrivial)
  结论: 存在ᵉ (x in s) (y in s), x < y
  证明: let ⟨x, hx, y, hy, hxy⟩ := hs
  Or.elim (lt_or_gt_of_ne hxy) (fun H => ⟨x, hx, y, hy, H⟩) fun H => ⟨y, hy, x, hx, H⟩

Depends on / 依赖: Or.elim, lt_or_gt_of_ne
-/
theorem Nontrivial.exists_lt [LinearOrder α] (hs : s.Nontrivial) : existsᵉ (x in s) (y in s), x < y :=
  let ⟨x, hx, y, hy, hxy⟩ := hs
  Or.elim (lt_or_gt_of_ne hxy) (fun H => ⟨x, hx, y, hy, H⟩) fun H => ⟨y, hy, x, hx, H⟩

/--
theorem `nontrivial_iff_exists_lt` / 定理 `nontrivial_iff_exists_lt`

English:
theorem nontrivial_iff_exists_lt
  given: [LinearOrder α]
  proof: ⟨Nontrivial.exists_lt, nontrivial_of_exists_lt⟩

中文:
定理 nontrivial_iff_exists_lt
  条件: [LinearOrder α]
  证明: ⟨Nontrivial.exists_lt, nontrivial_of_exists_lt⟩

Depends on / 依赖: Nontrivial, Nontrivial.exists_lt, exists_lt, nontrivial_of_exists_lt
-/
theorem nontrivial_iff_exists_lt [LinearOrder α] :
    s.Nontrivial ↔ existsᵉ (x in s) (y in s), x < y :=
  ⟨Nontrivial.exists_lt, nontrivial_of_exists_lt⟩

/--
theorem `Nontrivial.nonempty` / 定理 `Nontrivial.nonempty`

English:
theorem Nontrivial.nonempty
  given: (hs : s.Nontrivial)
  statement: s.Nonempty
  proof: let ⟨x, hx, _⟩ := hs
  ⟨x, hx⟩

中文:
定理 Nontrivial.nonempty
  条件: (hs : s.Nontrivial)
  结论: s.Nonempty
  证明: let ⟨x, hx, _⟩ := hs
  ⟨x, hx⟩
-/
protected theorem Nontrivial.nonempty (hs : s.Nontrivial) : s.Nonempty :=
  let ⟨x, hx, _⟩ := hs
  ⟨x, hx⟩

/--
theorem `Nontrivial.ne_empty` / 定理 `Nontrivial.ne_empty`

English:
theorem Nontrivial.ne_empty
  given: (hs : s.Nontrivial)
  statement: s != ∅
  proof: hs.nonempty.ne_empty

中文:
定理 Nontrivial.ne_empty
  条件: (hs : s.Nontrivial)
  结论: s != ∅
  证明: hs.nonempty.ne_empty
-/
protected theorem Nontrivial.ne_empty (hs : s.Nontrivial) : s != ∅ :=
  hs.nonempty.ne_empty

/--
theorem `Nontrivial.not_subset_empty` / 定理 `Nontrivial.not_subset_empty`

English:
theorem Nontrivial.not_subset_empty
  given: (hs : s.Nontrivial)
  statement: ¬s subseteq ∅
  proof: hs.nonempty.not_subset_empty

@[simp]

中文:
定理 Nontrivial.not_subset_empty
  条件: (hs : s.Nontrivial)
  结论: ¬s subseteq ∅
  证明: hs.nonempty.not_subset_empty

@[simp]

Depends on / 依赖: hs.nonempty.not_subset_empty, nonempty, not_subset_empty
-/
theorem Nontrivial.not_subset_empty (hs : s.Nontrivial) : ¬s subseteq ∅ :=
  hs.nonempty.not_subset_empty

@[simp]
/--
theorem `not_nontrivial_empty` / 定理 `not_nontrivial_empty`

English:
theorem not_nontrivial_empty
  statement: ¬(∅ : Set α).Nontrivial
  proof: fun h => h.ne_empty rfl

@[simp]

中文:
定理 not_nontrivial_empty
  结论: ¬(∅ : Set α).Nontrivial
  证明: fun h => h.ne_empty rfl

@[simp]

Depends on / 依赖: h.ne_empty, ne_empty
-/
theorem not_nontrivial_empty : ¬(∅ : Set α).Nontrivial := fun h => h.ne_empty rfl

@[simp]
/--
theorem `not_nontrivial_singleton` / 定理 `not_nontrivial_singleton`

English:
theorem not_nontrivial_singleton
  given: {x}
  statement: ¬({x} : Set α).Nontrivial
  proof: fun H => by
  rw [nontrivial_iff_exists_ne (mem_singleton x)] at H
  let ⟨y, hy, hya⟩ := H
  exact hya (mem_singleton_iff.1 hy)

中文:
定理 not_nontrivial_singleton
  条件: {x}
  结论: ¬({x} : Set α).Nontrivial
  证明: fun H => by
  rw [nontrivial_iff_exists_ne (mem_singleton x)] at H
  let ⟨y, hy, hya⟩ := H
  exact hya (mem_singleton_iff.1 hy)

Depends on / 依赖: mem_singleton, mem_singleton_iff, nontrivial_iff_exists_ne
-/
theorem not_nontrivial_singleton {x} : ¬({x} : Set α).Nontrivial := fun H => by
  rw [nontrivial_iff_exists_ne (mem_singleton x)] at H
  let ⟨y, hy, hya⟩ := H
  exact hya (mem_singleton_iff.1 hy)

/--
theorem `Nontrivial.ne_singleton` / 定理 `Nontrivial.ne_singleton`

English:
theorem Nontrivial.ne_singleton
  given: {x} (hs : s.Nontrivial)
  statement: s != {x}
  proof: fun H => by
  rw [H] at hs
  exact not_nontrivial_singleton hs

中文:
定理 Nontrivial.ne_singleton
  条件: {x} (hs : s.Nontrivial)
  结论: s != {x}
  证明: fun H => by
  rw [H] at hs
  exact not_nontrivial_singleton hs
-/
theorem Nontrivial.ne_singleton {x} (hs : s.Nontrivial) : s != {x} := fun H => by
  rw [H] at hs
  exact not_nontrivial_singleton hs

/--
theorem `Nontrivial.not_subset_singleton` / 定理 `Nontrivial.not_subset_singleton`

English:
theorem Nontrivial.not_subset_singleton
  given: {x} (hs : s.Nontrivial)
  statement: ¬s subseteq {x}
  proof: (not_congr subset_singleton_iff_eq).2 (not_or_intro hs.ne_empty hs.ne_singleton)

中文:
定理 Nontrivial.not_subset_singleton
  条件: {x} (hs : s.Nontrivial)
  结论: ¬s subseteq {x}
  证明: (not_congr subset_singleton_iff_eq).2 (not_or_intro hs.ne_empty hs.ne_singleton)

Depends on / 依赖: H.isNormal, isNormal
-/
theorem Nontrivial.not_subset_singleton {x} (hs : s.Nontrivial) : ¬s subseteq {x} :=
  (not_congr subset_singleton_iff_eq).2 (not_or_intro hs.ne_empty hs.ne_singleton)

/--
theorem `nontrivial_univ` / 定理 `nontrivial_univ`

English:
theorem nontrivial_univ
  given: [Nontrivial α]
  statement: (univ : Set α).Nontrivial
  proof: let ⟨x, y, hxy⟩ := exists_pair_ne α
  ⟨x, mem_univ _, y, mem_univ _, hxy⟩

中文:
定理 nontrivial_univ
  条件: [Nontrivial α]
  结论: (univ : Set α).Nontrivial
  证明: let ⟨x, y, hxy⟩ := exists_pair_ne α
  ⟨x, mem_univ _, y, mem_univ _, hxy⟩

Depends on / 依赖: H.isFiniteIndex, exists_pair_ne, isFiniteIndex, mem_univ
-/
theorem nontrivial_univ [Nontrivial α] : (univ : Set α).Nontrivial :=
  let ⟨x, y, hxy⟩ := exists_pair_ne α
  ⟨x, mem_univ _, y, mem_univ _, hxy⟩

/--
theorem `nontrivial_of_univ_nontrivial` / 定理 `nontrivial_of_univ_nontrivial`

English:
theorem nontrivial_of_univ_nontrivial
  given: (h : (univ : Set α).Nontrivial)
  statement: Nontrivial α
  proof: let ⟨x, _, y, _, hxy⟩ := h
  ⟨⟨x, y, hxy⟩⟩

@[simp]

中文:
定理 nontrivial_of_univ_nontrivial
  条件: (h : (univ : Set α).Nontrivial)
  结论: Nontrivial α
  证明: let ⟨x, _, y, _, hxy⟩ := h
  ⟨⟨x, y, hxy⟩⟩

@[simp]
-/
theorem nontrivial_of_univ_nontrivial (h : (univ : Set α).Nontrivial) : Nontrivial α :=
  let ⟨x, _, y, _, hxy⟩ := h
  ⟨⟨x, y, hxy⟩⟩

@[simp]
/--
theorem `nontrivial_univ_iff` / 定理 `nontrivial_univ_iff`

English:
theorem nontrivial_univ_iff
  statement: (univ : Set α).Nontrivial ↔ Nontrivial α
  proof: ⟨nontrivial_of_univ_nontrivial, fun h => @nontrivial_univ _ h⟩

@[simp]

中文:
定理 nontrivial_univ_iff
  结论: (univ : Set α).Nontrivial ↔ Nontrivial α
  证明: ⟨nontrivial_of_univ_nontrivial, fun h => @nontrivial_univ _ h⟩

@[simp]

Depends on / 依赖: nontrivial_of_univ_nontrivial, nontrivial_univ
-/
theorem nontrivial_univ_iff : (univ : Set α).Nontrivial ↔ Nontrivial α :=
  ⟨nontrivial_of_univ_nontrivial, fun h => @nontrivial_univ _ h⟩

@[simp]
/--
theorem `singleton_ne_univ` / 定理 `singleton_ne_univ`

English:
theorem singleton_ne_univ
  given: [Nontrivial α] (a : α)
  statement: {a} != univ
  proof: fun h => nontrivial_univ.not_subset_singleton h.superset

@[simp]

中文:
定理 singleton_ne_univ
  条件: [Nontrivial α] (a : α)
  结论: {a} != univ
  证明: fun h => nontrivial_univ.not_subset_singleton h.superset

@[simp]

Depends on / 依赖: h.superset, nontrivial_univ, nontrivial_univ.not_subset_singleton, not_subset_singleton, superset
-/
theorem singleton_ne_univ [Nontrivial α] (a : α) : {a} != univ :=
  fun h => nontrivial_univ.not_subset_singleton h.superset

@[simp]
/--
theorem `singleton_ssubset_univ` / 定理 `singleton_ssubset_univ`

English:
theorem singleton_ssubset_univ
  given: [Nontrivial α] (a : α)
  statement: {a} ⊂ univ
  proof: ssubset_univ_iff.mpr singleton_ne_univ a

中文:
定理 singleton_ssubset_univ
  条件: [Nontrivial α] (a : α)
  结论: {a} ⊂ univ
  证明: ssubset_univ_iff.mpr singleton_ne_univ a

Depends on / 依赖: singleton_ne_univ, ssubset_univ_iff, ssubset_univ_iff.mpr
-/
theorem singleton_ssubset_univ [Nontrivial α] (a : α) : {a} ⊂ univ :=
ssubset_univ_iff.mpr singleton_ne_univ a

/--
theorem `nontrivial_of_nontrivial` / 定理 `nontrivial_of_nontrivial`

English:
theorem nontrivial_of_nontrivial
  given: (hs : s.Nontrivial)
  statement: Nontrivial α
  proof: let ⟨x, _, y, _, hxy⟩ := hs
  ⟨⟨x, y, hxy⟩⟩

中文:
定理 nontrivial_of_nontrivial
  条件: (hs : s.Nontrivial)
  结论: Nontrivial α
  证明: let ⟨x, _, y, _, hxy⟩ := hs
  ⟨⟨x, y, hxy⟩⟩
-/
theorem nontrivial_of_nontrivial (hs : s.Nontrivial) : Nontrivial α :=
  let ⟨x, _, y, _, hxy⟩ := hs
  ⟨⟨x, y, hxy⟩⟩

/-- `s`, coerced to a type, is a nontrivial type if and only if `s` is a nontrivial set. -/
@[simp, norm_cast]
/--
theorem `nontrivial_coe_sort` / 定理 `nontrivial_coe_sort`

English:
theorem nontrivial_coe_sort
  given: {s : Set α}
  statement: Nontrivial s ↔ s.Nontrivial
  proof: by
  simp [← nontrivial_univ_iff, Set.Nontrivial]

alias ⟨_, Nontrivial.coe_sort⟩ := nontrivial_coe_sort

中文:
定理 nontrivial_coe_sort
  条件: {s : Set α}
  结论: Nontrivial s ↔ s.Nontrivial
  证明: by
  simp [← nontrivial_univ_iff, Set.Nontrivial]

alias ⟨_, Nontrivial.coe_sort⟩ := nontrivial_coe_sort

Depends on / 依赖: Nontrivial, Set.Nontrivial, nontrivial_univ_iff
-/
theorem nontrivial_coe_sort {s : Set α} : Nontrivial s ↔ s.Nontrivial := by
  simp [← nontrivial_univ_iff, Set.Nontrivial]

alias ⟨_, Nontrivial.coe_sort⟩ := nontrivial_coe_sort

/--
theorem `nontrivial_of_nontrivial_coe` / 定理 `nontrivial_of_nontrivial_coe`

English:
theorem nontrivial_of_nontrivial_coe
  given: (hs : Nontrivial s)
  statement: Nontrivial α
  proof: nontrivial_of_nontrivial nontrivial_coe_sort.1 hs

中文:
定理 nontrivial_of_nontrivial_coe
  条件: (hs : Nontrivial s)
  结论: Nontrivial α
  证明: nontrivial_of_nontrivial nontrivial_coe_sort.1 hs

Depends on / 依赖: nontrivial_coe_sort, nontrivial_of_nontrivial
-/
theorem nontrivial_of_nontrivial_coe (hs : Nontrivial s) : Nontrivial α :=
nontrivial_of_nontrivial nontrivial_coe_sort.1 hs

/--
theorem `nontrivial_mono` / 定理 `nontrivial_mono`

English:
theorem nontrivial_mono
  given: {α : Type*} {s t : Set α} (hst : s subseteq t) (hs : Nontrivial s)
  proof: Nontrivial.coe_sort (nontrivial_coe_sort.1 hs).mono hst

@[simp, push]

中文:
定理 nontrivial_mono
  条件: {α : 类型} {s t : Set α} (hst : s subseteq t) (hs : Nontrivial s)
  证明: Nontrivial.coe_sort (nontrivial_coe_sort.1 hs).mono hst

@[simp, push]

Depends on / 依赖: Nontrivial, Nontrivial.coe_sort, coe_sort, nontrivial_coe_sort
-/
theorem nontrivial_mono {α : Type*} {s t : Set α} (hst : s subseteq t) (hs : Nontrivial s) :
    Nontrivial t :=
Nontrivial.coe_sort (nontrivial_coe_sort.1 hs).mono hst

@[simp, push]
/--
theorem `not_subsingleton_iff` / 定理 `not_subsingleton_iff`

English:
theorem not_subsingleton_iff
  statement: ¬s.Subsingleton ↔ s.Nontrivial
  proof: by
  simp_rw [Set.Subsingleton, Set.Nontrivial, not_forall, exists_prop]

@[simp, push]

中文:
定理 not_subsingleton_iff
  结论: ¬s.Subsingleton ↔ s.Nontrivial
  证明: by
  simp_rw [Set.Subsingleton, Set.Nontrivial, not_forall, exists_prop]

@[simp, push]

Depends on / 依赖: Nontrivial, Set.Nontrivial, Set.Subsingleton, Subsingleton, exists_prop, not_forall, simp_rw
-/
theorem not_subsingleton_iff : ¬s.Subsingleton ↔ s.Nontrivial := by
  simp_rw [Set.Subsingleton, Set.Nontrivial, not_forall, exists_prop]

@[simp, push]
/--
theorem `not_nontrivial_iff` / 定理 `not_nontrivial_iff`

English:
theorem not_nontrivial_iff
  statement: ¬s.Nontrivial ↔ s.Subsingleton
  proof: Iff.not_left not_subsingleton_iff.symm

alias ⟨_, Subsingleton.not_nontrivial⟩ := not_nontrivial_iff

alias ⟨_, Nontrivial.not_subsingleton⟩ := not_subsingleton_iff

中文:
定理 not_nontrivial_iff
  结论: ¬s.Nontrivial ↔ s.Subsingleton
  证明: Iff.not_left not_subsingleton_iff.symm

alias ⟨_, Subsingleton.not_nontrivial⟩ := not_nontrivial_iff

alias ⟨_, Nontrivial.not_subsingleton⟩ := not_subsingleton_iff

Depends on / 依赖: Iff.not_left, not_left, not_subsingleton_iff, not_subsingleton_iff.symm
-/
theorem not_nontrivial_iff : ¬s.Nontrivial ↔ s.Subsingleton :=
  Iff.not_left not_subsingleton_iff.symm

alias ⟨_, Subsingleton.not_nontrivial⟩ := not_nontrivial_iff

alias ⟨_, Nontrivial.not_subsingleton⟩ := not_subsingleton_iff

/--
lemma `subsingleton_or_nontrivial` / 引理 `subsingleton_or_nontrivial`

English:
lemma subsingleton_or_nontrivial
  given: (s : Set α)
  statement: s.Subsingleton ∨ s.Nontrivial
  proof: by
  simp [or_iff_not_imp_right]

中文:
引理 subsingleton_or_nontrivial
  条件: (s : Set α)
  结论: s.Subsingleton ∨ s.Nontrivial
  证明: by
  simp [or_iff_not_imp_right]
-/
protected lemma subsingleton_or_nontrivial (s : Set α) : s.Subsingleton ∨ s.Nontrivial := by
  simp [or_iff_not_imp_right]

/--
lemma `eq_singleton_or_nontrivial` / 引理 `eq_singleton_or_nontrivial`

English:
lemma eq_singleton_or_nontrivial
  given: (ha : a in s)
  statement: s = {a} ∨ s.Nontrivial
  proof: by
  rw [← subsingleton_iff_singleton ha]; exact s.subsingleton_or_nontrivial

中文:
引理 eq_singleton_or_nontrivial
  条件: (ha : a in s)
  结论: s = {a} ∨ s.Nontrivial
  证明: by
  rw [← subsingleton_iff_singleton ha]; exact s.subsingleton_or_nontrivial

Depends on / 依赖: s.subsingleton_or_nontrivial, subsingleton_iff_singleton, subsingleton_or_nontrivial
-/
lemma eq_singleton_or_nontrivial (ha : a in s) : s = {a} ∨ s.Nontrivial := by
  rw [← subsingleton_iff_singleton ha]; exact s.subsingleton_or_nontrivial

/--
lemma `nontrivial_iff_ne_singleton` / 引理 `nontrivial_iff_ne_singleton`

English:
lemma nontrivial_iff_ne_singleton
  given: (ha : a in s)
  statement: s.Nontrivial ↔ s != {a}
  proof: ⟨Nontrivial.ne_singleton, (eq_singleton_or_nontrivial ha).resolve_left⟩

中文:
引理 nontrivial_iff_ne_singleton
  条件: (ha : a in s)
  结论: s.Nontrivial ↔ s != {a}
  证明: ⟨Nontrivial.ne_singleton, (eq_singleton_or_nontrivial ha).resolve_left⟩

Depends on / 依赖: Nontrivial, Nontrivial.ne_singleton, eq_singleton_or_nontrivial, ne_singleton, resolve_left
-/
lemma nontrivial_iff_ne_singleton (ha : a in s) : s.Nontrivial ↔ s != {a} :=
  ⟨Nontrivial.ne_singleton, (eq_singleton_or_nontrivial ha).resolve_left⟩

/--
lemma `Nonempty.exists_eq_singleton_or_nontrivial` / 引理 `Nonempty.exists_eq_singleton_or_nontrivial`

English:
lemma Nonempty.exists_eq_singleton_or_nontrivial
  statement: s.Nonempty -> (exists a, s = {a}) ∨ s.Nontrivial
  proof: fun ⟨a, ha⟩ => (eq_singleton_or_nontrivial ha).imp_left Exists.intro a

中文:
引理 Nonempty.exists_eq_singleton_or_nontrivial
  结论: s.Nonempty -> (存在 a, s = {a}) ∨ s.Nontrivial
  证明: fun ⟨a, ha⟩ => (eq_singleton_or_nontrivial ha).imp_left Exists.intro a
-/
lemma Nonempty.exists_eq_singleton_or_nontrivial : s.Nonempty -> (exists a, s = {a}) ∨ s.Nontrivial :=
fun ⟨a, ha⟩ => (eq_singleton_or_nontrivial ha).imp_left Exists.intro a

/--
theorem `univ_eq_true_false` / 定理 `univ_eq_true_false`

English:
theorem univ_eq_true_false
  statement: univ = ({True, False} : Set Prop)
  proof: Eq.symm eq_univ_of_forall fun x => by
    rw [mem_insert_iff]; rw [mem_singleton_iff]
    exact Classical.propComplete x

@[simp]

中文:
定理 univ_eq_true_false
  结论: univ = ({True, False} : Set 命题)
  证明: Eq.symm eq_univ_of_forall fun x => by
    rw [mem_insert_iff]; rw [mem_singleton_iff]
    exact Classical.propComplete x

@[simp]

Depends on / 依赖: Classical, Classical.propComplete, Eq.symm, eq_univ_of_forall, mem_insert_iff, mem_singleton_iff, propComplete
-/
theorem univ_eq_true_false : univ = ({True, False} : Set Prop) :=
Eq.symm eq_univ_of_forall fun x => by
    rw [mem_insert_iff]; rw [mem_singleton_iff]
    exact Classical.propComplete x

@[simp]
/--
theorem `univ_set_of_isEmpty` / 定理 `univ_set_of_isEmpty`

English:
theorem univ_set_of_isEmpty
  given: [IsEmpty α]
  statement: @univ (Set α) = {∅}
  proof: subset_antisymm (fun S hS => by simp [Set.eq_empty_of_isEmpty S]) (by simp)

@[simp]

中文:
定理 univ_set_of_isEmpty
  条件: [IsEmpty α]
  结论: @univ (Set α) = {∅}
  证明: subset_antisymm (fun S hS => by simp [Set.eq_empty_of_isEmpty S]) (by simp)

@[simp]

Depends on / 依赖: Set.eq_empty_of_isEmpty, eq_empty_of_isEmpty, subset_antisymm
-/
theorem univ_set_of_isEmpty [IsEmpty α] : @univ (Set α) = {∅} :=
  subset_antisymm (fun S hS => by simp [Set.eq_empty_of_isEmpty S]) (by simp)

@[simp]
/--
theorem `univ_set_eq_singleton_empty_iff` / 定理 `univ_set_eq_singleton_empty_iff`

English:
theorem univ_set_eq_singleton_empty_iff
  statement: @Set.univ (Set α) = {∅} ↔ IsEmpty α
  proof: by
  refine ⟨fun h => ?_, fun _ => by simp⟩
  suffices @univ α in univ by aesop
  simp

中文:
定理 univ_set_eq_singleton_empty_iff
  结论: @Set.univ (Set α) = {∅} ↔ IsEmpty α
  证明: by
  refine ⟨fun h => ?_, fun _ => by simp⟩
  suffices @univ α in univ by aesop
  simp
-/
theorem univ_set_eq_singleton_empty_iff : @Set.univ (Set α) = {∅} ↔ IsEmpty α := by
  refine ⟨fun h => ?_, fun _ => by simp⟩
  suffices @univ α in univ by aesop
  simp

end Nontrivial
section Monotonicity

/-! ### Monotonicity on singletons -/

variable {α : Type u} {β : Type v} {a : α} {s : Set α} [Preorder α] [Preorder β] (f : α -> β)

/--
theorem `Subsingleton.monotoneOn` / 定理 `Subsingleton.monotoneOn`

English:
theorem Subsingleton.monotoneOn
  given: (h : s.Subsingleton)
  statement: MonotoneOn f s
  proof: fun _ ha _ hb _ => (congr_arg _ (h ha hb)).le

中文:
定理 Subsingleton.monotoneOn
  条件: (h : s.Subsingleton)
  结论: MonotoneOn f s
  证明: fun _ ha _ hb _ => (congr_arg _ (h ha hb)).le
-/
protected theorem Subsingleton.monotoneOn (h : s.Subsingleton) : MonotoneOn f s :=
  fun _ ha _ hb _ => (congr_arg _ (h ha hb)).le

/--
theorem `Subsingleton.antitoneOn` / 定理 `Subsingleton.antitoneOn`

English:
theorem Subsingleton.antitoneOn
  given: (h : s.Subsingleton)
  statement: AntitoneOn f s
  proof: fun _ ha _ hb _ => (congr_arg _ (h hb ha)).le

中文:
定理 Subsingleton.antitoneOn
  条件: (h : s.Subsingleton)
  结论: AntitoneOn f s
  证明: fun _ ha _ hb _ => (congr_arg _ (h hb ha)).le
-/
protected theorem Subsingleton.antitoneOn (h : s.Subsingleton) : AntitoneOn f s :=
  fun _ ha _ hb _ => (congr_arg _ (h hb ha)).le

/--
theorem `Subsingleton.strictMonoOn` / 定理 `Subsingleton.strictMonoOn`

English:
theorem Subsingleton.strictMonoOn
  given: (h : s.Subsingleton)
  statement: StrictMonoOn f s
  proof: fun _ ha _ hb hlt => (hlt.ne (h ha hb)).elim

中文:
定理 Subsingleton.strictMonoOn
  条件: (h : s.Subsingleton)
  结论: StrictMonoOn f s
  证明: fun _ ha _ hb hlt => (hlt.ne (h ha hb)).elim
-/
protected theorem Subsingleton.strictMonoOn (h : s.Subsingleton) : StrictMonoOn f s :=
  fun _ ha _ hb hlt => (hlt.ne (h ha hb)).elim

/--
theorem `Subsingleton.strictAntiOn` / 定理 `Subsingleton.strictAntiOn`

English:
theorem Subsingleton.strictAntiOn
  given: (h : s.Subsingleton)
  statement: StrictAntiOn f s
  proof: fun _ ha _ hb hlt => (hlt.ne (h ha hb)).elim

@[simp]

中文:
定理 Subsingleton.strictAntiOn
  条件: (h : s.Subsingleton)
  结论: StrictAntiOn f s
  证明: fun _ ha _ hb hlt => (hlt.ne (h ha hb)).elim

@[simp]
-/
protected theorem Subsingleton.strictAntiOn (h : s.Subsingleton) : StrictAntiOn f s :=
  fun _ ha _ hb hlt => (hlt.ne (h ha hb)).elim

@[simp]
/--
theorem `monotoneOn_singleton` / 定理 `monotoneOn_singleton`

English:
theorem monotoneOn_singleton
  statement: MonotoneOn f {a}
  proof: subsingleton_singleton.monotoneOn f

@[simp]

中文:
定理 monotoneOn_singleton
  结论: MonotoneOn f {a}
  证明: subsingleton_singleton.monotoneOn f

@[simp]

Depends on / 依赖: monotoneOn, subsingleton_singleton, subsingleton_singleton.monotoneOn
-/
theorem monotoneOn_singleton : MonotoneOn f {a} :=
  subsingleton_singleton.monotoneOn f

@[simp]
/--
theorem `antitoneOn_singleton` / 定理 `antitoneOn_singleton`

English:
theorem antitoneOn_singleton
  statement: AntitoneOn f {a}
  proof: subsingleton_singleton.antitoneOn f

@[simp]

中文:
定理 antitoneOn_singleton
  结论: AntitoneOn f {a}
  证明: subsingleton_singleton.antitoneOn f

@[simp]

Depends on / 依赖: antitoneOn, subsingleton_singleton, subsingleton_singleton.antitoneOn
-/
theorem antitoneOn_singleton : AntitoneOn f {a} :=
  subsingleton_singleton.antitoneOn f

@[simp]
/--
theorem `strictMonoOn_singleton` / 定理 `strictMonoOn_singleton`

English:
theorem strictMonoOn_singleton
  statement: StrictMonoOn f {a}
  proof: subsingleton_singleton.strictMonoOn f

@[simp]

中文:
定理 strictMonoOn_singleton
  结论: StrictMonoOn f {a}
  证明: subsingleton_singleton.strictMonoOn f

@[simp]

Depends on / 依赖: strictMonoOn, subsingleton_singleton, subsingleton_singleton.strictMonoOn
-/
theorem strictMonoOn_singleton : StrictMonoOn f {a} :=
  subsingleton_singleton.strictMonoOn f

@[simp]
/--
theorem `strictAntiOn_singleton` / 定理 `strictAntiOn_singleton`

English:
theorem strictAntiOn_singleton
  statement: StrictAntiOn f {a}
  proof: subsingleton_singleton.strictAntiOn f

中文:
定理 strictAntiOn_singleton
  结论: StrictAntiOn f {a}
  证明: subsingleton_singleton.strictAntiOn f

Depends on / 依赖: strictAntiOn, subsingleton_singleton, subsingleton_singleton.strictAntiOn
-/
theorem strictAntiOn_singleton : StrictAntiOn f {a} :=
  subsingleton_singleton.strictAntiOn f

end Monotonicity

end Set
