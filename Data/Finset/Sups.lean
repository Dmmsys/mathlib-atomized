/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Finset.NAry
public import Mathlib.Data.Finset.Slice
public import Mathlib.Data.Set.Sups

/-!
# Set family operations

This file defines a few binary operations on `Finset α` for use in set family combinatorics.

## Main declarations

* `Finset.sups s t`: Finset of elements of the form `a ⊔ b` where `a ∈ s`, `b ∈ t`.
* `Finset.infs s t`: Finset of elements of the form `a ⊓ b` where `a ∈ s`, `b ∈ t`.
* `Finset.disjSups s t`: Finset of elements of the form `a ⊔ b` where `a ∈ s`, `b ∈ t` and `a`
  and `b` are disjoint.
* `Finset.diffs`: Finset of elements of the form `a \ b` where `a ∈ s`, `b ∈ t`.
* `Finset.compls`: Finset of elements of the form `aᶜ` where `a ∈ s`.

## Notation

We define the following notation in scope `FinsetFamily`:
* `s ⊻ t` for `Finset.sups`
* `s ⊼ t` for `Finset.infs`
* `s ○ t` for `Finset.disjSups s t`
* `s \\ t` for `Finset.diffs`
* `sᶜˢ` for `Finset.compls`

## References

[B. Bollobás, *Combinatorics*][bollobas1986]
-/

@[expose] public section

open Function

open SetFamily

variable {F α β : Type*}

namespace Finset

section Sups
variable [DecidableEq α] [DecidableEq β]
variable [SemilatticeSup α] [SemilatticeSup β] [FunLike F α β] [SupHomClass F α β]
variable (s s₁ s₂ t t₁ t₂ u v : Finset α)

/-- `s ⊻ t` is the finset of elements of the form `a ⊔ b` where `a ∈ s`, `b ∈ t`. -/
@[instance_reducible]
/--
Definition of `hasSups` / `hasSups` 的定义

English:
definition hasSups
  signature: : HasSups (Finset α)
  body: ⟨image₂ (· ⊔ ·)⟩

scoped[FinsetFamily] attribute [instance] Finset.hasSups

中文:
定义 hasSups
  签名: : 有Sups (有限集 α)
  定义体: ⟨image₂ (· ⊔ ·)⟩

scoped[FinsetFamily] attribute [instance] Finset.hasSups
-/
protected def hasSups : HasSups (Finset α) :=
  ⟨image₂ (· ⊔ ·)⟩

scoped[FinsetFamily] attribute [instance] Finset.hasSups

open FinsetFamily

variable {s t} {a b c : α}

@[simp]
/--
theorem `mem_sups` / 定理 `mem_sups`

English:
theorem mem_sups
  statement: c in s ⊻ t ↔ exists a in s, exists b in t, a ⊔ b = c
  proof: by simp [(· ⊻ ·)]

中文:
定理 mem_sups
  结论: c in s ⊻ t ↔ 存在 a in s, 存在 b in t, a ⊔ b = c
  证明: by simp [(· ⊻ ·)]
-/
theorem mem_sups : c in s ⊻ t ↔ exists a in s, exists b in t, a ⊔ b = c := by simp [(· ⊻ ·)]

variable (s t)

@[simp, norm_cast]
/--
theorem `coe_sups` / 定理 `coe_sups`

English:
theorem coe_sups
  statement: (↑(s ⊻ t) : Set α) = ↑s ⊻ ↑t
  proof: coe_image₂ _ _ _

中文:
定理 coe_sups
  结论: (↑(s ⊻ t) : 集合 α) = ↑s ⊻ ↑t
  证明: coe_image₂ _ _ _
-/
theorem coe_sups : (↑(s ⊻ t) : Set α) = ↑s ⊻ ↑t :=
  coe_image₂ _ _ _

/--
theorem `card_sups_le` / 定理 `card_sups_le`

English:
theorem card_sups_le
  statement: #(s ⊻ t) <= #s * #t
  proof: card_image₂_le _ _ _

中文:
定理 card_sups_le
  结论: #(s ⊻ t) <= #s * #t
  证明: card_image₂_le _ _ _
-/
theorem card_sups_le : #(s ⊻ t) <= #s * #t := card_image₂_le _ _ _

/--
theorem `card_sups_iff` / 定理 `card_sups_iff`

English:
theorem card_sups_iff
  statement: #(s ⊻ t) = #s * #t ↔ (s ×ˢ t : Set (α × α)).InjOn fun x => x.1 ⊔ x.2
  proof: card_image₂_iff

中文:
定理 card_sups_iff
  结论: #(s ⊻ t) = #s * #t ↔ (s ×ˢ t : 集合 (α × α)).单射限制 fun x => x.1 ⊔ x.2
  证明: card_image₂_iff
-/
theorem card_sups_iff : #(s ⊻ t) = #s * #t ↔ (s ×ˢ t : Set (α × α)).InjOn fun x => x.1 ⊔ x.2 :=
  card_image₂_iff

variable {s s₁ s₂ t t₁ t₂ u}

/--
theorem `sup_mem_sups` / 定理 `sup_mem_sups`

English:
theorem sup_mem_sups
  statement: a in s -> b in t -> a ⊔ b in s ⊻ t
  proof: mem_image₂_of_mem

中文:
定理 sup_mem_sups
  结论: a in s -> b in t -> a ⊔ b in s ⊻ t
  证明: mem_image₂_of_mem
-/
theorem sup_mem_sups : a in s -> b in t -> a ⊔ b in s ⊻ t :=
  mem_image₂_of_mem

/--
theorem `sups_subset` / 定理 `sups_subset`

English:
theorem sups_subset
  statement: s₁ subseteq s₂ -> t₁ subseteq t₂ -> s₁ ⊻ t₁ subseteq s₂ ⊻ t₂
  proof: image₂_subset

中文:
定理 sups_subset
  结论: s₁ subseteq s₂ -> t₁ subseteq t₂ -> s₁ ⊻ t₁ subseteq s₂ ⊻ t₂
  证明: image₂_subset
-/
theorem sups_subset : s₁ subseteq s₂ -> t₁ subseteq t₂ -> s₁ ⊻ t₁ subseteq s₂ ⊻ t₂ :=
  image₂_subset

/--
theorem `sups_subset_left` / 定理 `sups_subset_left`

English:
theorem sups_subset_left
  statement: t₁ subseteq t₂ -> s ⊻ t₁ subseteq s ⊻ t₂
  proof: image₂_subset_left

中文:
定理 sups_subset_left
  结论: t₁ subseteq t₂ -> s ⊻ t₁ subseteq s ⊻ t₂
  证明: image₂_subset_left
-/
theorem sups_subset_left : t₁ subseteq t₂ -> s ⊻ t₁ subseteq s ⊻ t₂ :=
  image₂_subset_left

/--
theorem `sups_subset_right` / 定理 `sups_subset_right`

English:
theorem sups_subset_right
  statement: s₁ subseteq s₂ -> s₁ ⊻ t subseteq s₂ ⊻ t
  proof: image₂_subset_right

中文:
定理 sups_subset_right
  结论: s₁ subseteq s₂ -> s₁ ⊻ t subseteq s₂ ⊻ t
  证明: image₂_subset_right
-/
theorem sups_subset_right : s₁ subseteq s₂ -> s₁ ⊻ t subseteq s₂ ⊻ t :=
  image₂_subset_right

/--
lemma `image_subset_sups_left` / 引理 `image_subset_sups_left`

English:
lemma image_subset_sups_left
  statement: b in t -> s.image (· ⊔ b) subseteq s ⊻ t
  proof: image_subset_image₂_left

中文:
引理 image_subset_sups_left
  结论: b in t -> s.像 (· ⊔ b) subseteq s ⊻ t
  证明: image_subset_image₂_left
-/
lemma image_subset_sups_left : b in t -> s.image (· ⊔ b) subseteq s ⊻ t := image_subset_image₂_left

/--
lemma `image_subset_sups_right` / 引理 `image_subset_sups_right`

English:
lemma image_subset_sups_right
  statement: a in s -> t.image (a ⊔ ·) subseteq s ⊻ t
  proof: image_subset_image₂_right

中文:
引理 image_subset_sups_right
  结论: a in s -> t.像 (a ⊔ ·) subseteq s ⊻ t
  证明: image_subset_image₂_right
-/
lemma image_subset_sups_right : a in s -> t.image (a ⊔ ·) subseteq s ⊻ t := image_subset_image₂_right

/--
theorem `forall_sups_iff` / 定理 `forall_sups_iff`

English:
theorem forall_sups_iff
  given: {p : α -> Prop}
  statement: (forall c in s ⊻ t, p c) ↔ forall a in s, forall b in t, p (a ⊔ b)
  proof: forall_mem_image₂

@[simp]

中文:
定理 对任意_sups_iff
  条件: {p : α -> 命题}
  结论: (对任意 c in s ⊻ t, p c) ↔ 对任意 a in s, 对任意 b in t, p (a ⊔ b)
  证明: forall_mem_image₂

@[simp]
-/
theorem forall_sups_iff {p : α -> Prop} : (forall c in s ⊻ t, p c) ↔ forall a in s, forall b in t, p (a ⊔ b) :=
  forall_mem_image₂

@[simp]
/--
theorem `sups_subset_iff` / 定理 `sups_subset_iff`

English:
theorem sups_subset_iff
  statement: s ⊻ t subseteq u ↔ forall a in s, forall b in t, a ⊔ b in u
  proof: image₂_subset_iff

@[simp]

中文:
定理 sups_subset_iff
  结论: s ⊻ t subseteq u ↔ 对任意 a in s, 对任意 b in t, a ⊔ b in u
  证明: image₂_subset_iff

@[simp]
-/
theorem sups_subset_iff : s ⊻ t subseteq u ↔ forall a in s, forall b in t, a ⊔ b in u :=
  image₂_subset_iff

@[simp]
/--
theorem `sups_nonempty` / 定理 `sups_nonempty`

English:
theorem sups_nonempty
  statement: (s ⊻ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty
  proof: image₂_nonempty_iff

@[aesop safe apply (rule_sets := [finsetNonempty])]

中文:
定理 sups_nonempty
  结论: (s ⊻ t).非空 ↔ s.非空 ∧ t.非空
  证明: image₂_nonempty_iff

@[aesop safe apply (rule_sets := [finsetNonempty])]
-/
theorem sups_nonempty : (s ⊻ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image₂_nonempty_iff

@[aesop safe apply (rule_sets := [finsetNonempty])]
/--
theorem `Nonempty.sups` / 定理 `Nonempty.sups`

English:
theorem Nonempty.sups
  statement: s.Nonempty -> t.Nonempty -> (s ⊻ t).Nonempty
  proof: Nonempty.image₂

中文:
定理 非空.sups
  结论: s.非空 -> t.非空 -> (s ⊻ t).非空
  证明: Nonempty.image₂
-/
protected theorem Nonempty.sups : s.Nonempty -> t.Nonempty -> (s ⊻ t).Nonempty :=
  Nonempty.image₂

/--
theorem `Nonempty.of_sups_left` / 定理 `Nonempty.of_sups_left`

English:
theorem Nonempty.of_sups_left
  statement: (s ⊻ t).Nonempty -> s.Nonempty
  proof: Nonempty.of_image₂_left

中文:
定理 非空.of_sups_left
  结论: (s ⊻ t).非空 -> s.非空
  证明: Nonempty.of_image₂_left

Depends on / 依赖: Nonempty, Nonempty.of_image
-/
theorem Nonempty.of_sups_left : (s ⊻ t).Nonempty -> s.Nonempty :=
  Nonempty.of_image₂_left

/--
theorem `Nonempty.of_sups_right` / 定理 `Nonempty.of_sups_right`

English:
theorem Nonempty.of_sups_right
  statement: (s ⊻ t).Nonempty -> t.Nonempty
  proof: Nonempty.of_image₂_right

@[simp]

中文:
定理 非空.of_sups_right
  结论: (s ⊻ t).非空 -> t.非空
  证明: Nonempty.of_image₂_right

@[simp]

Depends on / 依赖: Nonempty, Nonempty.of_image
-/
theorem Nonempty.of_sups_right : (s ⊻ t).Nonempty -> t.Nonempty :=
  Nonempty.of_image₂_right

@[simp]
/--
theorem `empty_sups` / 定理 `empty_sups`

English:
theorem empty_sups
  statement: ∅ ⊻ t = ∅
  proof: image₂_empty_left

@[simp]

中文:
定理 empty_sups
  结论: ∅ ⊻ t = ∅
  证明: image₂_empty_left

@[simp]
-/
theorem empty_sups : ∅ ⊻ t = ∅ :=
  image₂_empty_left

@[simp]
/--
theorem `sups_empty` / 定理 `sups_empty`

English:
theorem sups_empty
  statement: s ⊻ ∅ = ∅
  proof: image₂_empty_right

@[simp]

中文:
定理 sups_empty
  结论: s ⊻ ∅ = ∅
  证明: image₂_empty_right

@[simp]
-/
theorem sups_empty : s ⊻ ∅ = ∅ :=
  image₂_empty_right

@[simp]
/--
theorem `sups_eq_empty` / 定理 `sups_eq_empty`

English:
theorem sups_eq_empty
  statement: s ⊻ t = ∅ ↔ s = ∅ ∨ t = ∅
  proof: image₂_eq_empty_iff

中文:
定理 sups_eq_empty
  结论: s ⊻ t = ∅ ↔ s = ∅ ∨ t = ∅
  证明: image₂_eq_empty_iff
-/
theorem sups_eq_empty : s ⊻ t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image₂_eq_empty_iff

/--
lemma `singleton_sups` / 引理 `singleton_sups`

English:
lemma singleton_sups
  statement: {a} ⊻ t = t.image (a ⊔ ·)
  proof: image₂_singleton_left

中文:
引理 singleton_sups
  结论: {a} ⊻ t = t.像 (a ⊔ ·)
  证明: image₂_singleton_left
-/
@[simp] lemma singleton_sups : {a} ⊻ t = t.image (a ⊔ ·) := image₂_singleton_left

/--
lemma `sups_singleton` / 引理 `sups_singleton`

English:
lemma sups_singleton
  statement: s ⊻ {b} = s.image (· ⊔ b)
  proof: image₂_singleton_right

中文:
引理 sups_singleton
  结论: s ⊻ {b} = s.像 (· ⊔ b)
  证明: image₂_singleton_right
-/
@[simp] lemma sups_singleton : s ⊻ {b} = s.image (· ⊔ b) := image₂_singleton_right

/--
theorem `singleton_sups_singleton` / 定理 `singleton_sups_singleton`

English:
theorem singleton_sups_singleton
  statement: ({a} ⊻ {b} : Finset α) = {a ⊔ b}
  proof: image₂_singleton

中文:
定理 singleton_sups_singleton
  结论: ({a} ⊻ {b} : 有限集 α) = {a ⊔ b}
  证明: image₂_singleton
-/
theorem singleton_sups_singleton : ({a} ⊻ {b} : Finset α) = {a ⊔ b} :=
  image₂_singleton

/--
theorem `sups_union_left` / 定理 `sups_union_left`

English:
theorem sups_union_left
  statement: (s₁ union s₂) ⊻ t = s₁ ⊻ t union s₂ ⊻ t
  proof: image₂_union_left

中文:
定理 sups_union_left
  结论: (s₁ union s₂) ⊻ t = s₁ ⊻ t union s₂ ⊻ t
  证明: image₂_union_left
-/
theorem sups_union_left : (s₁ union s₂) ⊻ t = s₁ ⊻ t union s₂ ⊻ t :=
  image₂_union_left

/--
theorem `sups_union_right` / 定理 `sups_union_right`

English:
theorem sups_union_right
  statement: s ⊻ (t₁ union t₂) = s ⊻ t₁ union s ⊻ t₂
  proof: image₂_union_right

中文:
定理 sups_union_right
  结论: s ⊻ (t₁ union t₂) = s ⊻ t₁ union s ⊻ t₂
  证明: image₂_union_right
-/
theorem sups_union_right : s ⊻ (t₁ union t₂) = s ⊻ t₁ union s ⊻ t₂ :=
  image₂_union_right

/--
theorem `sups_inter_subset_left` / 定理 `sups_inter_subset_left`

English:
theorem sups_inter_subset_left
  statement: (s₁ inter s₂) ⊻ t subseteq s₁ ⊻ t inter s₂ ⊻ t
  proof: image₂_inter_subset_left

中文:
定理 sups_inter_subset_left
  结论: (s₁ inter s₂) ⊻ t subseteq s₁ ⊻ t inter s₂ ⊻ t
  证明: image₂_inter_subset_left
-/
theorem sups_inter_subset_left : (s₁ inter s₂) ⊻ t subseteq s₁ ⊻ t inter s₂ ⊻ t :=
  image₂_inter_subset_left

/--
theorem `sups_inter_subset_right` / 定理 `sups_inter_subset_right`

English:
theorem sups_inter_subset_right
  statement: s ⊻ (t₁ inter t₂) subseteq s ⊻ t₁ inter s ⊻ t₂
  proof: image₂_inter_subset_right

中文:
定理 sups_inter_subset_right
  结论: s ⊻ (t₁ inter t₂) subseteq s ⊻ t₁ inter s ⊻ t₂
  证明: image₂_inter_subset_right
-/
theorem sups_inter_subset_right : s ⊻ (t₁ inter t₂) subseteq s ⊻ t₁ inter s ⊻ t₂ :=
  image₂_inter_subset_right

/--
theorem `subset_sups` / 定理 `subset_sups`

English:
theorem subset_sups
  given: {s t : Set α}
  proof: subset_set_image₂

中文:
定理 subset_sups
  条件: {s t : 集合 α}
  证明: subset_set_image₂
-/
theorem subset_sups {s t : Set α} :
    ↑u subseteq s ⊻ t -> exists s' t' : Finset α, ↑s' subseteq s ∧ ↑t' subseteq t ∧ u subseteq s' ⊻ t' :=
  subset_set_image₂

/--
lemma `image_sups` / 引理 `image_sups`

English:
lemma image_sups
  given: (f : F) (s t : Finset α)
  statement: image f (s ⊻ t) = image f s ⊻ image f t
  proof: image_image₂_distrib map_sup f

中文:
引理 image_sups
  条件: (f : F) (s t : 有限集 α)
  结论: 像 f (s ⊻ t) = 像 f s ⊻ 像 f t
  证明: image_image₂_distrib map_sup f

Depends on / 依赖: map_sup
-/
lemma image_sups (f : F) (s t : Finset α) : image f (s ⊻ t) = image f s ⊻ image f t :=
image_image₂_distrib map_sup f

/--
lemma `map_sups` / 引理 `map_sups`

English:
lemma map_sups
  given: (f : F) (hf) (s t : Finset α)
  proof: by
  simpa [map_eq_image] using image_sups f s t

中文:
引理 map_sups
  条件: (f : F) (hf) (s t : 有限集 α)
  证明: by
  simpa [map_eq_image] using image_sups f s t

Depends on / 依赖: image_sups, map_eq_image
-/
lemma map_sups (f : F) (hf) (s t : Finset α) :
    map ⟨f, hf⟩ (s ⊻ t) = map ⟨f, hf⟩ s ⊻ map ⟨f, hf⟩ t := by
  simpa [map_eq_image] using image_sups f s t

/--
lemma `subset_sups_self` / 引理 `subset_sups_self`

English:
lemma subset_sups_self
  statement: s subseteq s ⊻ s
  proof: fun _a ha => mem_sups.2 ⟨_, ha, _, ha, sup_idem _⟩

中文:
引理 subset_sups_self
  结论: s subseteq s ⊻ s
  证明: fun _a ha => mem_sups.2 ⟨_, ha, _, ha, sup_idem _⟩

Depends on / 依赖: mem_sups, sup_idem
-/
lemma subset_sups_self : s subseteq s ⊻ s := fun _a ha => mem_sups.2 ⟨_, ha, _, ha, sup_idem _⟩
/--
lemma `sups_subset_self` / 引理 `sups_subset_self`

English:
lemma sups_subset_self
  statement: s ⊻ s subseteq s ↔ SupClosed (s : Set α)
  proof: sups_subset_iff

中文:
引理 sups_subset_self
  结论: s ⊻ s subseteq s ↔ SupClosed (s : 集合 α)
  证明: sups_subset_iff

Depends on / 依赖: sups_subset_iff
-/
lemma sups_subset_self : s ⊻ s subseteq s ↔ SupClosed (s : Set α) := sups_subset_iff
/--
lemma `sups_eq_self` / 引理 `sups_eq_self`

English:
lemma sups_eq_self
  statement: s ⊻ s = s ↔ SupClosed (s : Set α)
  proof: by simp [← coe_inj]

中文:
引理 sups_eq_self
  结论: s ⊻ s = s ↔ SupClosed (s : 集合 α)
  证明: by simp [← coe_inj]
-/
@[simp] lemma sups_eq_self : s ⊻ s = s ↔ SupClosed (s : Set α) := by simp [← coe_inj]

/--
lemma `univ_sups_univ` / 引理 `univ_sups_univ`

English:
lemma univ_sups_univ
  given: [Fintype α]
  statement: (univ : Finset α) ⊻ univ = univ
  proof: by simp

中文:
引理 univ_sups_univ
  条件: [有限类型 α]
  结论: (univ : 有限集 α) ⊻ univ = univ
  证明: by simp
-/
@[simp] lemma univ_sups_univ [Fintype α] : (univ : Finset α) ⊻ univ = univ := by simp

/--
lemma `filter_sups_le` / 引理 `filter_sups_le`

English:
lemma filter_sups_le
  given: [DecidableLE α] (s t : Finset α) (a : α)
  proof: by
  simp only [← coe_inj, coe_filter, coe_sups, ← mem_coe, Set.sep_sups_le]

中文:
引理 filter_sups_le
  条件: [DecidableLE α] (s t : 有限集 α) (a : α)
  证明: by
  simp only [← coe_inj, coe_filter, coe_sups, ← mem_coe, Set.sep_sups_le]

Depends on / 依赖: Set.sep_sups_le, coe_filter, coe_inj, coe_sups, mem_coe, sep_sups_le
-/
lemma filter_sups_le [DecidableLE α] (s t : Finset α) (a : α) :
    {b in s ⊻ t | b <= a} = {b in s | b <= a} ⊻ {b in t | b <= a} := by
  simp only [← coe_inj, coe_filter, coe_sups, ← mem_coe, Set.sep_sups_le]

variable (s t u)

/--
lemma `biUnion_image_sup_left` / 引理 `biUnion_image_sup_left`

English:
lemma biUnion_image_sup_left
  statement: s.biUnion (fun a => t.image (a ⊔ ·)) = s ⊻ t
  proof: biUnion_image_left

中文:
引理 biUnion_image_sup_left
  结论: s.biUnion (fun a => t.像 (a ⊔ ·)) = s ⊻ t
  证明: biUnion_image_left

Depends on / 依赖: biUnion_image_left
-/
lemma biUnion_image_sup_left : s.biUnion (fun a => t.image (a ⊔ ·)) = s ⊻ t := biUnion_image_left

/--
lemma `biUnion_image_sup_right` / 引理 `biUnion_image_sup_right`

English:
lemma biUnion_image_sup_right
  statement: t.biUnion (fun b => s.image (· ⊔ b)) = s ⊻ t
  proof: biUnion_image_right

中文:
引理 biUnion_image_sup_right
  结论: t.biUnion (fun b => s.像 (· ⊔ b)) = s ⊻ t
  证明: biUnion_image_right

Depends on / 依赖: biUnion_image_right
-/
lemma biUnion_image_sup_right : t.biUnion (fun b => s.image (· ⊔ b)) = s ⊻ t := biUnion_image_right

/--
theorem `image_sup_product` / 定理 `image_sup_product`

English:
theorem image_sup_product
  given: (s t : Finset α)
  statement: (s ×ˢ t).image (uncurry (· ⊔ ·)) = s ⊻ t
  proof: image_uncurry_product _ _ _

中文:
定理 image_sup_product
  条件: (s t : 有限集 α)
  结论: (s ×ˢ t).像 (uncurry (· ⊔ ·)) = s ⊻ t
  证明: image_uncurry_product _ _ _

Depends on / 依赖: image_uncurry_product
-/
theorem image_sup_product (s t : Finset α) : (s ×ˢ t).image (uncurry (· ⊔ ·)) = s ⊻ t :=
  image_uncurry_product _ _ _

/--
theorem `sups_assoc` / 定理 `sups_assoc`

English:
theorem sups_assoc
  statement: s ⊻ t ⊻ u = s ⊻ (t ⊻ u)
  proof: image₂_assoc sup_assoc

中文:
定理 sups_assoc
  结论: s ⊻ t ⊻ u = s ⊻ (t ⊻ u)
  证明: image₂_assoc sup_assoc

Depends on / 依赖: sup_assoc
-/
theorem sups_assoc : s ⊻ t ⊻ u = s ⊻ (t ⊻ u) := image₂_assoc sup_assoc

/--
theorem `sups_comm` / 定理 `sups_comm`

English:
theorem sups_comm
  statement: s ⊻ t = t ⊻ s
  proof: image₂_comm sup_comm

中文:
定理 sups_comm
  结论: s ⊻ t = t ⊻ s
  证明: image₂_comm sup_comm

Depends on / 依赖: sup_comm
-/
theorem sups_comm : s ⊻ t = t ⊻ s := image₂_comm sup_comm

/--
theorem `sups_left_comm` / 定理 `sups_left_comm`

English:
theorem sups_left_comm
  statement: s ⊻ (t ⊻ u) = t ⊻ (s ⊻ u)
  proof: image₂_left_comm sup_left_comm

中文:
定理 sups_left_comm
  结论: s ⊻ (t ⊻ u) = t ⊻ (s ⊻ u)
  证明: image₂_left_comm sup_left_comm

Depends on / 依赖: sup_left_comm
-/
theorem sups_left_comm : s ⊻ (t ⊻ u) = t ⊻ (s ⊻ u) :=
  image₂_left_comm sup_left_comm

/--
theorem `sups_right_comm` / 定理 `sups_right_comm`

English:
theorem sups_right_comm
  statement: s ⊻ t ⊻ u = s ⊻ u ⊻ t
  proof: image₂_right_comm sup_right_comm

中文:
定理 sups_right_comm
  结论: s ⊻ t ⊻ u = s ⊻ u ⊻ t
  证明: image₂_right_comm sup_right_comm

Depends on / 依赖: sup_right_comm
-/
theorem sups_right_comm : s ⊻ t ⊻ u = s ⊻ u ⊻ t :=
  image₂_right_comm sup_right_comm

/--
theorem `sups_sups_sups_comm` / 定理 `sups_sups_sups_comm`

English:
theorem sups_sups_sups_comm
  statement: s ⊻ t ⊻ (u ⊻ v) = s ⊻ u ⊻ (t ⊻ v)
  proof: image₂_image₂_image₂_comm sup_sup_sup_comm

中文:
定理 sups_sups_sups_comm
  结论: s ⊻ t ⊻ (u ⊻ v) = s ⊻ u ⊻ (t ⊻ v)
  证明: image₂_image₂_image₂_comm sup_sup_sup_comm

Depends on / 依赖: sup_sup_sup_comm
-/
theorem sups_sups_sups_comm : s ⊻ t ⊻ (u ⊻ v) = s ⊻ u ⊻ (t ⊻ v) :=
  image₂_image₂_image₂_comm sup_sup_sup_comm

end Sups

section Infs
variable [DecidableEq α] [DecidableEq β]
variable [SemilatticeInf α] [SemilatticeInf β] [FunLike F α β] [InfHomClass F α β]
variable (s s₁ s₂ t t₁ t₂ u v : Finset α)

/-- `s ⊼ t` is the finset of elements of the form `a ⊓ b` where `a ∈ s`, `b ∈ t`. -/
@[instance_reducible]
/--
Definition of `hasInfs` / `hasInfs` 的定义

English:
definition hasInfs
  signature: : HasInfs (Finset α)
  body: ⟨image₂ (· ⊓ ·)⟩

scoped[FinsetFamily] attribute [instance] Finset.hasInfs

中文:
定义 hasInfs
  签名: : 有Infs (有限集 α)
  定义体: ⟨image₂ (· ⊓ ·)⟩

scoped[FinsetFamily] attribute [instance] Finset.hasInfs
-/
protected def hasInfs : HasInfs (Finset α) :=
  ⟨image₂ (· ⊓ ·)⟩

scoped[FinsetFamily] attribute [instance] Finset.hasInfs

open FinsetFamily

variable {s t} {a b c : α}

@[simp]
/--
theorem `mem_infs` / 定理 `mem_infs`

English:
theorem mem_infs
  statement: c in s ⊼ t ↔ exists a in s, exists b in t, a ⊓ b = c
  proof: by simp [(· ⊼ ·)]

中文:
定理 mem_infs
  结论: c in s ⊼ t ↔ 存在 a in s, 存在 b in t, a ⊓ b = c
  证明: by simp [(· ⊼ ·)]
-/
theorem mem_infs : c in s ⊼ t ↔ exists a in s, exists b in t, a ⊓ b = c := by simp [(· ⊼ ·)]

variable (s t)

@[simp, norm_cast]
/--
theorem `coe_infs` / 定理 `coe_infs`

English:
theorem coe_infs
  statement: (↑(s ⊼ t) : Set α) = ↑s ⊼ ↑t
  proof: coe_image₂ _ _ _

中文:
定理 coe_infs
  结论: (↑(s ⊼ t) : 集合 α) = ↑s ⊼ ↑t
  证明: coe_image₂ _ _ _
-/
theorem coe_infs : (↑(s ⊼ t) : Set α) = ↑s ⊼ ↑t :=
  coe_image₂ _ _ _

/--
theorem `card_infs_le` / 定理 `card_infs_le`

English:
theorem card_infs_le
  statement: #(s ⊼ t) <= #s * #t
  proof: card_image₂_le _ _ _

中文:
定理 card_infs_le
  结论: #(s ⊼ t) <= #s * #t
  证明: card_image₂_le _ _ _
-/
theorem card_infs_le : #(s ⊼ t) <= #s * #t := card_image₂_le _ _ _

/--
theorem `card_infs_iff` / 定理 `card_infs_iff`

English:
theorem card_infs_iff
  statement: #(s ⊼ t) = #s * #t ↔ (s ×ˢ t : Set (α × α)).InjOn fun x => x.1 ⊓ x.2
  proof: card_image₂_iff

中文:
定理 card_infs_iff
  结论: #(s ⊼ t) = #s * #t ↔ (s ×ˢ t : 集合 (α × α)).单射限制 fun x => x.1 ⊓ x.2
  证明: card_image₂_iff
-/
theorem card_infs_iff : #(s ⊼ t) = #s * #t ↔ (s ×ˢ t : Set (α × α)).InjOn fun x => x.1 ⊓ x.2 :=
  card_image₂_iff

variable {s s₁ s₂ t t₁ t₂ u}

/--
theorem `inf_mem_infs` / 定理 `inf_mem_infs`

English:
theorem inf_mem_infs
  statement: a in s -> b in t -> a ⊓ b in s ⊼ t
  proof: mem_image₂_of_mem

中文:
定理 inf_mem_infs
  结论: a in s -> b in t -> a ⊓ b in s ⊼ t
  证明: mem_image₂_of_mem
-/
theorem inf_mem_infs : a in s -> b in t -> a ⊓ b in s ⊼ t :=
  mem_image₂_of_mem

/--
theorem `infs_subset` / 定理 `infs_subset`

English:
theorem infs_subset
  statement: s₁ subseteq s₂ -> t₁ subseteq t₂ -> s₁ ⊼ t₁ subseteq s₂ ⊼ t₂
  proof: image₂_subset

中文:
定理 infs_subset
  结论: s₁ subseteq s₂ -> t₁ subseteq t₂ -> s₁ ⊼ t₁ subseteq s₂ ⊼ t₂
  证明: image₂_subset
-/
theorem infs_subset : s₁ subseteq s₂ -> t₁ subseteq t₂ -> s₁ ⊼ t₁ subseteq s₂ ⊼ t₂ :=
  image₂_subset

/--
theorem `infs_subset_left` / 定理 `infs_subset_left`

English:
theorem infs_subset_left
  statement: t₁ subseteq t₂ -> s ⊼ t₁ subseteq s ⊼ t₂
  proof: image₂_subset_left

中文:
定理 infs_subset_left
  结论: t₁ subseteq t₂ -> s ⊼ t₁ subseteq s ⊼ t₂
  证明: image₂_subset_left
-/
theorem infs_subset_left : t₁ subseteq t₂ -> s ⊼ t₁ subseteq s ⊼ t₂ :=
  image₂_subset_left

/--
theorem `infs_subset_right` / 定理 `infs_subset_right`

English:
theorem infs_subset_right
  statement: s₁ subseteq s₂ -> s₁ ⊼ t subseteq s₂ ⊼ t
  proof: image₂_subset_right

中文:
定理 infs_subset_right
  结论: s₁ subseteq s₂ -> s₁ ⊼ t subseteq s₂ ⊼ t
  证明: image₂_subset_right
-/
theorem infs_subset_right : s₁ subseteq s₂ -> s₁ ⊼ t subseteq s₂ ⊼ t :=
  image₂_subset_right

/--
lemma `image_subset_infs_left` / 引理 `image_subset_infs_left`

English:
lemma image_subset_infs_left
  statement: b in t -> s.image (· ⊓ b) subseteq s ⊼ t
  proof: image_subset_image₂_left

中文:
引理 image_subset_infs_left
  结论: b in t -> s.像 (· ⊓ b) subseteq s ⊼ t
  证明: image_subset_image₂_left
-/
lemma image_subset_infs_left : b in t -> s.image (· ⊓ b) subseteq s ⊼ t := image_subset_image₂_left

/--
lemma `image_subset_infs_right` / 引理 `image_subset_infs_right`

English:
lemma image_subset_infs_right
  statement: a in s -> t.image (a ⊓ ·) subseteq s ⊼ t
  proof: image_subset_image₂_right

中文:
引理 image_subset_infs_right
  结论: a in s -> t.像 (a ⊓ ·) subseteq s ⊼ t
  证明: image_subset_image₂_right
-/
lemma image_subset_infs_right : a in s -> t.image (a ⊓ ·) subseteq s ⊼ t := image_subset_image₂_right

/--
theorem `forall_infs_iff` / 定理 `forall_infs_iff`

English:
theorem forall_infs_iff
  given: {p : α -> Prop}
  statement: (forall c in s ⊼ t, p c) ↔ forall a in s, forall b in t, p (a ⊓ b)
  proof: forall_mem_image₂

@[simp]

中文:
定理 对任意_infs_iff
  条件: {p : α -> 命题}
  结论: (对任意 c in s ⊼ t, p c) ↔ 对任意 a in s, 对任意 b in t, p (a ⊓ b)
  证明: forall_mem_image₂

@[simp]
-/
theorem forall_infs_iff {p : α -> Prop} : (forall c in s ⊼ t, p c) ↔ forall a in s, forall b in t, p (a ⊓ b) :=
  forall_mem_image₂

@[simp]
/--
theorem `infs_subset_iff` / 定理 `infs_subset_iff`

English:
theorem infs_subset_iff
  statement: s ⊼ t subseteq u ↔ forall a in s, forall b in t, a ⊓ b in u
  proof: image₂_subset_iff

@[simp]

中文:
定理 infs_subset_iff
  结论: s ⊼ t subseteq u ↔ 对任意 a in s, 对任意 b in t, a ⊓ b in u
  证明: image₂_subset_iff

@[simp]
-/
theorem infs_subset_iff : s ⊼ t subseteq u ↔ forall a in s, forall b in t, a ⊓ b in u :=
  image₂_subset_iff

@[simp]
/--
theorem `infs_nonempty` / 定理 `infs_nonempty`

English:
theorem infs_nonempty
  statement: (s ⊼ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty
  proof: image₂_nonempty_iff

@[aesop safe apply (rule_sets := [finsetNonempty])]

中文:
定理 infs_nonempty
  结论: (s ⊼ t).非空 ↔ s.非空 ∧ t.非空
  证明: image₂_nonempty_iff

@[aesop safe apply (rule_sets := [finsetNonempty])]
-/
theorem infs_nonempty : (s ⊼ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image₂_nonempty_iff

@[aesop safe apply (rule_sets := [finsetNonempty])]
/--
theorem `Nonempty.infs` / 定理 `Nonempty.infs`

English:
theorem Nonempty.infs
  statement: s.Nonempty -> t.Nonempty -> (s ⊼ t).Nonempty
  proof: Nonempty.image₂

中文:
定理 非空.infs
  结论: s.非空 -> t.非空 -> (s ⊼ t).非空
  证明: Nonempty.image₂
-/
protected theorem Nonempty.infs : s.Nonempty -> t.Nonempty -> (s ⊼ t).Nonempty :=
  Nonempty.image₂

/--
theorem `Nonempty.of_infs_left` / 定理 `Nonempty.of_infs_left`

English:
theorem Nonempty.of_infs_left
  statement: (s ⊼ t).Nonempty -> s.Nonempty
  proof: Nonempty.of_image₂_left

中文:
定理 非空.of_infs_left
  结论: (s ⊼ t).非空 -> s.非空
  证明: Nonempty.of_image₂_left

Depends on / 依赖: Nonempty, Nonempty.of_image
-/
theorem Nonempty.of_infs_left : (s ⊼ t).Nonempty -> s.Nonempty :=
  Nonempty.of_image₂_left

/--
theorem `Nonempty.of_infs_right` / 定理 `Nonempty.of_infs_right`

English:
theorem Nonempty.of_infs_right
  statement: (s ⊼ t).Nonempty -> t.Nonempty
  proof: Nonempty.of_image₂_right

@[simp]

中文:
定理 非空.of_infs_right
  结论: (s ⊼ t).非空 -> t.非空
  证明: Nonempty.of_image₂_right

@[simp]

Depends on / 依赖: Nonempty, Nonempty.of_image
-/
theorem Nonempty.of_infs_right : (s ⊼ t).Nonempty -> t.Nonempty :=
  Nonempty.of_image₂_right

@[simp]
/--
theorem `empty_infs` / 定理 `empty_infs`

English:
theorem empty_infs
  statement: ∅ ⊼ t = ∅
  proof: image₂_empty_left

@[simp]

中文:
定理 empty_infs
  结论: ∅ ⊼ t = ∅
  证明: image₂_empty_left

@[simp]
-/
theorem empty_infs : ∅ ⊼ t = ∅ :=
  image₂_empty_left

@[simp]
/--
theorem `infs_empty` / 定理 `infs_empty`

English:
theorem infs_empty
  statement: s ⊼ ∅ = ∅
  proof: image₂_empty_right

@[simp]

中文:
定理 infs_empty
  结论: s ⊼ ∅ = ∅
  证明: image₂_empty_right

@[simp]
-/
theorem infs_empty : s ⊼ ∅ = ∅ :=
  image₂_empty_right

@[simp]
/--
theorem `infs_eq_empty` / 定理 `infs_eq_empty`

English:
theorem infs_eq_empty
  statement: s ⊼ t = ∅ ↔ s = ∅ ∨ t = ∅
  proof: image₂_eq_empty_iff

中文:
定理 infs_eq_empty
  结论: s ⊼ t = ∅ ↔ s = ∅ ∨ t = ∅
  证明: image₂_eq_empty_iff
-/
theorem infs_eq_empty : s ⊼ t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image₂_eq_empty_iff

/--
lemma `singleton_infs` / 引理 `singleton_infs`

English:
lemma singleton_infs
  statement: {a} ⊼ t = t.image (a ⊓ ·)
  proof: image₂_singleton_left

中文:
引理 singleton_infs
  结论: {a} ⊼ t = t.像 (a ⊓ ·)
  证明: image₂_singleton_left
-/
@[simp] lemma singleton_infs : {a} ⊼ t = t.image (a ⊓ ·) := image₂_singleton_left

/--
lemma `infs_singleton` / 引理 `infs_singleton`

English:
lemma infs_singleton
  statement: s ⊼ {b} = s.image (· ⊓ b)
  proof: image₂_singleton_right

中文:
引理 infs_singleton
  结论: s ⊼ {b} = s.像 (· ⊓ b)
  证明: image₂_singleton_right
-/
@[simp] lemma infs_singleton : s ⊼ {b} = s.image (· ⊓ b) := image₂_singleton_right

/--
theorem `singleton_infs_singleton` / 定理 `singleton_infs_singleton`

English:
theorem singleton_infs_singleton
  statement: ({a} ⊼ {b} : Finset α) = {a ⊓ b}
  proof: image₂_singleton

中文:
定理 singleton_infs_singleton
  结论: ({a} ⊼ {b} : 有限集 α) = {a ⊓ b}
  证明: image₂_singleton
-/
theorem singleton_infs_singleton : ({a} ⊼ {b} : Finset α) = {a ⊓ b} :=
  image₂_singleton

/--
theorem `infs_union_left` / 定理 `infs_union_left`

English:
theorem infs_union_left
  statement: (s₁ union s₂) ⊼ t = s₁ ⊼ t union s₂ ⊼ t
  proof: image₂_union_left

中文:
定理 infs_union_left
  结论: (s₁ union s₂) ⊼ t = s₁ ⊼ t union s₂ ⊼ t
  证明: image₂_union_left
-/
theorem infs_union_left : (s₁ union s₂) ⊼ t = s₁ ⊼ t union s₂ ⊼ t :=
  image₂_union_left

/--
theorem `infs_union_right` / 定理 `infs_union_right`

English:
theorem infs_union_right
  statement: s ⊼ (t₁ union t₂) = s ⊼ t₁ union s ⊼ t₂
  proof: image₂_union_right

中文:
定理 infs_union_right
  结论: s ⊼ (t₁ union t₂) = s ⊼ t₁ union s ⊼ t₂
  证明: image₂_union_right
-/
theorem infs_union_right : s ⊼ (t₁ union t₂) = s ⊼ t₁ union s ⊼ t₂ :=
  image₂_union_right

/--
theorem `infs_inter_subset_left` / 定理 `infs_inter_subset_left`

English:
theorem infs_inter_subset_left
  statement: (s₁ inter s₂) ⊼ t subseteq s₁ ⊼ t inter s₂ ⊼ t
  proof: image₂_inter_subset_left

中文:
定理 infs_inter_subset_left
  结论: (s₁ inter s₂) ⊼ t subseteq s₁ ⊼ t inter s₂ ⊼ t
  证明: image₂_inter_subset_left
-/
theorem infs_inter_subset_left : (s₁ inter s₂) ⊼ t subseteq s₁ ⊼ t inter s₂ ⊼ t :=
  image₂_inter_subset_left

/--
theorem `infs_inter_subset_right` / 定理 `infs_inter_subset_right`

English:
theorem infs_inter_subset_right
  statement: s ⊼ (t₁ inter t₂) subseteq s ⊼ t₁ inter s ⊼ t₂
  proof: image₂_inter_subset_right

中文:
定理 infs_inter_subset_right
  结论: s ⊼ (t₁ inter t₂) subseteq s ⊼ t₁ inter s ⊼ t₂
  证明: image₂_inter_subset_right
-/
theorem infs_inter_subset_right : s ⊼ (t₁ inter t₂) subseteq s ⊼ t₁ inter s ⊼ t₂ :=
  image₂_inter_subset_right

/--
theorem `subset_infs` / 定理 `subset_infs`

English:
theorem subset_infs
  given: {s t : Set α}
  proof: subset_set_image₂

中文:
定理 subset_infs
  条件: {s t : 集合 α}
  证明: subset_set_image₂
-/
theorem subset_infs {s t : Set α} :
    ↑u subseteq s ⊼ t -> exists s' t' : Finset α, ↑s' subseteq s ∧ ↑t' subseteq t ∧ u subseteq s' ⊼ t' :=
  subset_set_image₂

/--
lemma `image_infs` / 引理 `image_infs`

English:
lemma image_infs
  given: (f : F) (s t : Finset α)
  statement: image f (s ⊼ t) = image f s ⊼ image f t
  proof: image_image₂_distrib map_inf f

中文:
引理 image_infs
  条件: (f : F) (s t : 有限集 α)
  结论: 像 f (s ⊼ t) = 像 f s ⊼ 像 f t
  证明: image_image₂_distrib map_inf f

Depends on / 依赖: map_inf
-/
lemma image_infs (f : F) (s t : Finset α) : image f (s ⊼ t) = image f s ⊼ image f t :=
image_image₂_distrib map_inf f

/--
lemma `map_infs` / 引理 `map_infs`

English:
lemma map_infs
  given: (f : F) (hf) (s t : Finset α)
  proof: by
  simpa [map_eq_image] using image_infs f s t

中文:
引理 map_infs
  条件: (f : F) (hf) (s t : 有限集 α)
  证明: by
  simpa [map_eq_image] using image_infs f s t

Depends on / 依赖: image_infs, map_eq_image
-/
lemma map_infs (f : F) (hf) (s t : Finset α) :
    map ⟨f, hf⟩ (s ⊼ t) = map ⟨f, hf⟩ s ⊼ map ⟨f, hf⟩ t := by
  simpa [map_eq_image] using image_infs f s t

/--
lemma `subset_infs_self` / 引理 `subset_infs_self`

English:
lemma subset_infs_self
  statement: s subseteq s ⊼ s
  proof: fun _a ha => mem_infs.2 ⟨_, ha, _, ha, inf_idem _⟩

中文:
引理 subset_infs_self
  结论: s subseteq s ⊼ s
  证明: fun _a ha => mem_infs.2 ⟨_, ha, _, ha, inf_idem _⟩

Depends on / 依赖: inf_idem, mem_infs
-/
lemma subset_infs_self : s subseteq s ⊼ s := fun _a ha => mem_infs.2 ⟨_, ha, _, ha, inf_idem _⟩
/--
lemma `infs_self_subset` / 引理 `infs_self_subset`

English:
lemma infs_self_subset
  statement: s ⊼ s subseteq s ↔ InfClosed (s : Set α)
  proof: infs_subset_iff

中文:
引理 infs_self_subset
  结论: s ⊼ s subseteq s ↔ InfClosed (s : 集合 α)
  证明: infs_subset_iff

Depends on / 依赖: infs_subset_iff
-/
lemma infs_self_subset : s ⊼ s subseteq s ↔ InfClosed (s : Set α) := infs_subset_iff
/--
lemma `infs_self` / 引理 `infs_self`

English:
lemma infs_self
  statement: s ⊼ s = s ↔ InfClosed (s : Set α)
  proof: by simp [← coe_inj]

中文:
引理 infs_self
  结论: s ⊼ s = s ↔ InfClosed (s : 集合 α)
  证明: by simp [← coe_inj]
-/
@[simp] lemma infs_self : s ⊼ s = s ↔ InfClosed (s : Set α) := by simp [← coe_inj]

/--
lemma `univ_infs_univ` / 引理 `univ_infs_univ`

English:
lemma univ_infs_univ
  given: [Fintype α]
  statement: (univ : Finset α) ⊼ univ = univ
  proof: by simp

中文:
引理 univ_infs_univ
  条件: [有限类型 α]
  结论: (univ : 有限集 α) ⊼ univ = univ
  证明: by simp
-/
@[simp] lemma univ_infs_univ [Fintype α] : (univ : Finset α) ⊼ univ = univ := by simp

/--
lemma `filter_infs_le` / 引理 `filter_infs_le`

English:
lemma filter_infs_le
  given: [DecidableLE α] (s t : Finset α) (a : α)
  proof: by
  simp only [← coe_inj, coe_filter, coe_infs, ← mem_coe, Set.sep_infs_le]

中文:
引理 filter_infs_le
  条件: [DecidableLE α] (s t : 有限集 α) (a : α)
  证明: by
  simp only [← coe_inj, coe_filter, coe_infs, ← mem_coe, Set.sep_infs_le]

Depends on / 依赖: Set.sep_infs_le, coe_filter, coe_infs, coe_inj, mem_coe, sep_infs_le
-/
lemma filter_infs_le [DecidableLE α] (s t : Finset α) (a : α) :
    {b in s ⊼ t | a <= b} = {b in s | a <= b} ⊼ {b in t | a <= b} := by
  simp only [← coe_inj, coe_filter, coe_infs, ← mem_coe, Set.sep_infs_le]

variable (s t u)

/--
lemma `biUnion_image_inf_left` / 引理 `biUnion_image_inf_left`

English:
lemma biUnion_image_inf_left
  statement: s.biUnion (fun a => t.image (a ⊓ ·)) = s ⊼ t
  proof: biUnion_image_left

中文:
引理 biUnion_image_inf_left
  结论: s.biUnion (fun a => t.像 (a ⊓ ·)) = s ⊼ t
  证明: biUnion_image_left

Depends on / 依赖: biUnion_image_left
-/
lemma biUnion_image_inf_left : s.biUnion (fun a => t.image (a ⊓ ·)) = s ⊼ t := biUnion_image_left

/--
lemma `biUnion_image_inf_right` / 引理 `biUnion_image_inf_right`

English:
lemma biUnion_image_inf_right
  statement: t.biUnion (fun b => s.image (· ⊓ b)) = s ⊼ t
  proof: biUnion_image_right

中文:
引理 biUnion_image_inf_right
  结论: t.biUnion (fun b => s.像 (· ⊓ b)) = s ⊼ t
  证明: biUnion_image_right

Depends on / 依赖: biUnion_image_right
-/
lemma biUnion_image_inf_right : t.biUnion (fun b => s.image (· ⊓ b)) = s ⊼ t := biUnion_image_right

/--
theorem `image_inf_product` / 定理 `image_inf_product`

English:
theorem image_inf_product
  given: (s t : Finset α)
  statement: (s ×ˢ t).image (uncurry (· ⊓ ·)) = s ⊼ t
  proof: image_uncurry_product _ _ _

中文:
定理 image_inf_product
  条件: (s t : 有限集 α)
  结论: (s ×ˢ t).像 (uncurry (· ⊓ ·)) = s ⊼ t
  证明: image_uncurry_product _ _ _

Depends on / 依赖: image_uncurry_product
-/
theorem image_inf_product (s t : Finset α) : (s ×ˢ t).image (uncurry (· ⊓ ·)) = s ⊼ t :=
  image_uncurry_product _ _ _

/--
theorem `infs_assoc` / 定理 `infs_assoc`

English:
theorem infs_assoc
  statement: s ⊼ t ⊼ u = s ⊼ (t ⊼ u)
  proof: image₂_assoc inf_assoc

中文:
定理 infs_assoc
  结论: s ⊼ t ⊼ u = s ⊼ (t ⊼ u)
  证明: image₂_assoc inf_assoc

Depends on / 依赖: inf_assoc
-/
theorem infs_assoc : s ⊼ t ⊼ u = s ⊼ (t ⊼ u) := image₂_assoc inf_assoc

/--
theorem `infs_comm` / 定理 `infs_comm`

English:
theorem infs_comm
  statement: s ⊼ t = t ⊼ s
  proof: image₂_comm inf_comm

中文:
定理 infs_comm
  结论: s ⊼ t = t ⊼ s
  证明: image₂_comm inf_comm

Depends on / 依赖: inf_comm
-/
theorem infs_comm : s ⊼ t = t ⊼ s := image₂_comm inf_comm

/--
theorem `infs_left_comm` / 定理 `infs_left_comm`

English:
theorem infs_left_comm
  statement: s ⊼ (t ⊼ u) = t ⊼ (s ⊼ u)
  proof: image₂_left_comm inf_left_comm

中文:
定理 infs_left_comm
  结论: s ⊼ (t ⊼ u) = t ⊼ (s ⊼ u)
  证明: image₂_left_comm inf_left_comm

Depends on / 依赖: inf_left_comm
-/
theorem infs_left_comm : s ⊼ (t ⊼ u) = t ⊼ (s ⊼ u) :=
  image₂_left_comm inf_left_comm

/--
theorem `infs_right_comm` / 定理 `infs_right_comm`

English:
theorem infs_right_comm
  statement: s ⊼ t ⊼ u = s ⊼ u ⊼ t
  proof: image₂_right_comm inf_right_comm

中文:
定理 infs_right_comm
  结论: s ⊼ t ⊼ u = s ⊼ u ⊼ t
  证明: image₂_right_comm inf_right_comm

Depends on / 依赖: inf_right_comm
-/
theorem infs_right_comm : s ⊼ t ⊼ u = s ⊼ u ⊼ t :=
  image₂_right_comm inf_right_comm

/--
theorem `infs_infs_infs_comm` / 定理 `infs_infs_infs_comm`

English:
theorem infs_infs_infs_comm
  statement: s ⊼ t ⊼ (u ⊼ v) = s ⊼ u ⊼ (t ⊼ v)
  proof: image₂_image₂_image₂_comm inf_inf_inf_comm

中文:
定理 infs_infs_infs_comm
  结论: s ⊼ t ⊼ (u ⊼ v) = s ⊼ u ⊼ (t ⊼ v)
  证明: image₂_image₂_image₂_comm inf_inf_inf_comm

Depends on / 依赖: inf_inf_inf_comm
-/
theorem infs_infs_infs_comm : s ⊼ t ⊼ (u ⊼ v) = s ⊼ u ⊼ (t ⊼ v) :=
  image₂_image₂_image₂_comm inf_inf_inf_comm

end Infs

open FinsetFamily

section DistribLattice

variable [DecidableEq α]
variable [DistribLattice α] (s t u : Finset α)

/--
theorem `sups_infs_subset_left` / 定理 `sups_infs_subset_left`

English:
theorem sups_infs_subset_left
  statement: s ⊻ t ⊼ u subseteq (s ⊻ t) ⊼ (s ⊻ u)
  proof: image₂_distrib_subset_left sup_inf_left

中文:
定理 sups_infs_subset_left
  结论: s ⊻ t ⊼ u subseteq (s ⊻ t) ⊼ (s ⊻ u)
  证明: image₂_distrib_subset_left sup_inf_left

Depends on / 依赖: sup_inf_left
-/
theorem sups_infs_subset_left : s ⊻ t ⊼ u subseteq (s ⊻ t) ⊼ (s ⊻ u) :=
  image₂_distrib_subset_left sup_inf_left

/--
theorem `sups_infs_subset_right` / 定理 `sups_infs_subset_right`

English:
theorem sups_infs_subset_right
  statement: t ⊼ u ⊻ s subseteq (t ⊻ s) ⊼ (u ⊻ s)
  proof: image₂_distrib_subset_right sup_inf_right

中文:
定理 sups_infs_subset_right
  结论: t ⊼ u ⊻ s subseteq (t ⊻ s) ⊼ (u ⊻ s)
  证明: image₂_distrib_subset_right sup_inf_right

Depends on / 依赖: sup_inf_right
-/
theorem sups_infs_subset_right : t ⊼ u ⊻ s subseteq (t ⊻ s) ⊼ (u ⊻ s) :=
  image₂_distrib_subset_right sup_inf_right

/--
theorem `infs_sups_subset_left` / 定理 `infs_sups_subset_left`

English:
theorem infs_sups_subset_left
  statement: s ⊼ (t ⊻ u) subseteq s ⊼ t ⊻ s ⊼ u
  proof: image₂_distrib_subset_left inf_sup_left

中文:
定理 infs_sups_subset_left
  结论: s ⊼ (t ⊻ u) subseteq s ⊼ t ⊻ s ⊼ u
  证明: image₂_distrib_subset_left inf_sup_left

Depends on / 依赖: inf_sup_left
-/
theorem infs_sups_subset_left : s ⊼ (t ⊻ u) subseteq s ⊼ t ⊻ s ⊼ u :=
  image₂_distrib_subset_left inf_sup_left

/--
theorem `infs_sups_subset_right` / 定理 `infs_sups_subset_right`

English:
theorem infs_sups_subset_right
  statement: (t ⊻ u) ⊼ s subseteq t ⊼ s ⊻ u ⊼ s
  proof: image₂_distrib_subset_right inf_sup_right

中文:
定理 infs_sups_subset_right
  结论: (t ⊻ u) ⊼ s subseteq t ⊼ s ⊻ u ⊼ s
  证明: image₂_distrib_subset_right inf_sup_right

Depends on / 依赖: inf_sup_right
-/
theorem infs_sups_subset_right : (t ⊻ u) ⊼ s subseteq t ⊼ s ⊻ u ⊼ s :=
  image₂_distrib_subset_right inf_sup_right

end DistribLattice

section Finset
variable [DecidableEq α]
variable {𝒜 ℬ : Finset (Finset α)} {s t : Finset α}

/--
lemma `powerset_union` / 引理 `powerset_union`

English:
lemma powerset_union
  given: (s t : Finset α)
  statement: (s union t).powerset = s.powerset ⊻ t.powerset
  proof: by
  ext u
  simp only [mem_sups, mem_powerset, sup_eq_union]
  refine ⟨fun h => ⟨_, inter_subset_left (s₂ := u), _, inter_subset_left (s₂ := u), ?_⟩, ?_⟩
  · rwa [← union_inter_distrib_right, inter_eq_right]
  · rintro ⟨v, hv, w, hw, rfl⟩
    exact union_subset_union hv hw

中文:
引理 powerset_union
  条件: (s t : 有限集 α)
  结论: (s union t).powerset = s.powerset ⊻ t.powerset
  证明: by
  ext u
  simp only [mem_sups, mem_powerset, sup_eq_union]
  refine ⟨fun h => ⟨_, inter_subset_left (s₂ := u), _, inter_subset_left (s₂ := u), ?_⟩, ?_⟩
  · rwa [← union_inter_distrib_right, inter_eq_right]
  · rintro ⟨v, hv, w, hw, rfl⟩
    exact union_subset_union hv hw
-/
@[simp] lemma powerset_union (s t : Finset α) : (s union t).powerset = s.powerset ⊻ t.powerset := by
  ext u
  simp only [mem_sups, mem_powerset, sup_eq_union]
  refine ⟨fun h => ⟨_, inter_subset_left (s₂ := u), _, inter_subset_left (s₂ := u), ?_⟩, ?_⟩
  · rwa [← union_inter_distrib_right, inter_eq_right]
  · rintro ⟨v, hv, w, hw, rfl⟩
    exact union_subset_union hv hw

/--
lemma `powerset_inter` / 引理 `powerset_inter`

English:
lemma powerset_inter
  given: (s t : Finset α)
  statement: (s inter t).powerset = s.powerset ⊼ t.powerset
  proof: by
  ext u
  simp only [mem_infs, mem_powerset, inf_eq_inter]
  refine ⟨fun h => ⟨_, inter_subset_left (s₂ := u), _, inter_subset_left (s₂ := u), ?_⟩, ?_⟩
  · rwa [← inter_inter_distrib_right, inter_eq_right]
  · rintro ⟨v, hv, w, hw, rfl⟩
    exact inter_subset_inter hv hw

中文:
引理 powerset_inter
  条件: (s t : 有限集 α)
  结论: (s inter t).powerset = s.powerset ⊼ t.powerset
  证明: by
  ext u
  simp only [mem_infs, mem_powerset, inf_eq_inter]
  refine ⟨fun h => ⟨_, inter_subset_left (s₂ := u), _, inter_subset_left (s₂ := u), ?_⟩, ?_⟩
  · rwa [← inter_inter_distrib_right, inter_eq_right]
  · rintro ⟨v, hv, w, hw, rfl⟩
    exact inter_subset_inter hv hw
-/
@[simp] lemma powerset_inter (s t : Finset α) : (s inter t).powerset = s.powerset ⊼ t.powerset := by
  ext u
  simp only [mem_infs, mem_powerset, inf_eq_inter]
  refine ⟨fun h => ⟨_, inter_subset_left (s₂ := u), _, inter_subset_left (s₂ := u), ?_⟩, ?_⟩
  · rwa [← inter_inter_distrib_right, inter_eq_right]
  · rintro ⟨v, hv, w, hw, rfl⟩
    exact inter_subset_inter hv hw

/--
lemma `powerset_sups_powerset_self` / 引理 `powerset_sups_powerset_self`

English:
lemma powerset_sups_powerset_self
  given: (s : Finset α)
  proof: by simp [← powerset_union]

中文:
引理 powerset_sups_powerset_self
  条件: (s : 有限集 α)
  证明: by simp [← powerset_union]
-/
@[simp] lemma powerset_sups_powerset_self (s : Finset α) :
    s.powerset ⊻ s.powerset = s.powerset := by simp [← powerset_union]

/--
lemma `powerset_infs_powerset_self` / 引理 `powerset_infs_powerset_self`

English:
lemma powerset_infs_powerset_self
  given: (s : Finset α)
  proof: by simp [← powerset_inter]

中文:
引理 powerset_infs_powerset_self
  条件: (s : 有限集 α)
  证明: by simp [← powerset_inter]
-/
@[simp] lemma powerset_infs_powerset_self (s : Finset α) :
    s.powerset ⊼ s.powerset = s.powerset := by simp [← powerset_inter]

/--
lemma `union_mem_sups` / 引理 `union_mem_sups`

English:
lemma union_mem_sups
  statement: s in 𝒜 -> t in ℬ -> s union t in 𝒜 ⊻ ℬ
  proof: sup_mem_sups

中文:
引理 union_mem_sups
  结论: s in 𝒜 -> t in ℬ -> s union t in 𝒜 ⊻ ℬ
  证明: sup_mem_sups

Depends on / 依赖: sup_mem_sups
-/
lemma union_mem_sups : s in 𝒜 -> t in ℬ -> s union t in 𝒜 ⊻ ℬ := sup_mem_sups
/--
lemma `inter_mem_infs` / 引理 `inter_mem_infs`

English:
lemma inter_mem_infs
  statement: s in 𝒜 -> t in ℬ -> s inter t in 𝒜 ⊼ ℬ
  proof: inf_mem_infs

中文:
引理 inter_mem_infs
  结论: s in 𝒜 -> t in ℬ -> s inter t in 𝒜 ⊼ ℬ
  证明: inf_mem_infs

Depends on / 依赖: inf_mem_infs
-/
lemma inter_mem_infs : s in 𝒜 -> t in ℬ -> s inter t in 𝒜 ⊼ ℬ := inf_mem_infs

end Finset

section DisjSups

variable [DecidableEq α]
variable [SemilatticeSup α] [OrderBot α] [DecidableRel (α := α) Disjoint]
  (s s₁ s₂ t t₁ t₂ u : Finset α)

/--
Definition of `disjSups` / `disjSups` 的定义

English:
definition disjSups
  signature: : Finset α
  body: {ab in s ×ˢ t | Disjoint ab.1 ab.2}.image fun ab => ab.1 ⊔ ab.2

@[inherit_doc]
scoped[FinsetFamily] infixl:74 " ○ " => Finset.disjSups

中文:
定义 disjSups
  签名: : 有限集 α
  定义体: {ab in s ×ˢ t | Disjoint ab.1 ab.2}.image fun ab => ab.1 ⊔ ab.2

@[inherit_doc]
scoped[FinsetFamily] infixl:74 " ○ " => Finset.disjSups

Depends on / 依赖: Disjoint
-/
def disjSups : Finset α := {ab in s ×ˢ t | Disjoint ab.1 ab.2}.image fun ab => ab.1 ⊔ ab.2

@[inherit_doc]
scoped[FinsetFamily] infixl:74 " ○ " => Finset.disjSups

variable {s t u} {a b c : α}

@[simp]
/--
theorem `mem_disjSups` / 定理 `mem_disjSups`

English:
theorem mem_disjSups
  statement: c in s ○ t ↔ exists a in s, exists b in t, Disjoint a b ∧ a ⊔ b = c
  proof: by
  simp [disjSups, and_assoc]

中文:
定理 mem_disjSups
  结论: c in s ○ t ↔ 存在 a in s, 存在 b in t, Disjoint a b ∧ a ⊔ b = c
  证明: by
  simp [disjSups, and_assoc]

Depends on / 依赖: and_assoc, disjSups
-/
theorem mem_disjSups : c in s ○ t ↔ exists a in s, exists b in t, Disjoint a b ∧ a ⊔ b = c := by
  simp [disjSups, and_assoc]

/--
theorem `disjSups_subset_sups` / 定理 `disjSups_subset_sups`

English:
theorem disjSups_subset_sups
  statement: s ○ t subseteq s ⊻ t
  proof: by
  simp_rw [subset_iff, mem_sups, mem_disjSups]
  exact fun c ⟨a, b, ha, hb, _, hc⟩ => ⟨a, b, ha, hb, hc⟩

中文:
定理 disjSups_subset_sups
  结论: s ○ t subseteq s ⊻ t
  证明: by
  simp_rw [subset_iff, mem_sups, mem_disjSups]
  exact fun c ⟨a, b, ha, hb, _, hc⟩ => ⟨a, b, ha, hb, hc⟩

Depends on / 依赖: mem_disjSups, mem_sups, simp_rw, subset_iff
-/
theorem disjSups_subset_sups : s ○ t subseteq s ⊻ t := by
  simp_rw [subset_iff, mem_sups, mem_disjSups]
  exact fun c ⟨a, b, ha, hb, _, hc⟩ => ⟨a, b, ha, hb, hc⟩

variable (s t)

/--
theorem `card_disjSups_le` / 定理 `card_disjSups_le`

English:
theorem card_disjSups_le
  statement: #(s ○ t) <= #s * #t
  proof: (card_le_card disjSups_subset_sups).trans card_sups_le _ _

中文:
定理 card_disjSups_le
  结论: #(s ○ t) <= #s * #t
  证明: (card_le_card disjSups_subset_sups).trans card_sups_le _ _

Depends on / 依赖: card_le_card, card_sups_le, disjSups_subset_sups
-/
theorem card_disjSups_le : #(s ○ t) <= #s * #t :=
(card_le_card disjSups_subset_sups).trans card_sups_le _ _

variable {s s₁ s₂ t t₁ t₂}

/--
theorem `disjSups_subset` / 定理 `disjSups_subset`

English:
theorem disjSups_subset
  given: (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂)
  statement: s₁ ○ t₁ subseteq s₂ ○ t₂
  proof: image_subset_image filter_subset_filter _ product_subset_product hs ht

中文:
定理 disjSups_subset
  条件: (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂)
  结论: s₁ ○ t₁ subseteq s₂ ○ t₂
  证明: image_subset_image filter_subset_filter _ product_subset_product hs ht

Depends on / 依赖: filter_subset_filter, image_subset_image, product_subset_product
-/
theorem disjSups_subset (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : s₁ ○ t₁ subseteq s₂ ○ t₂ :=
image_subset_image filter_subset_filter _ product_subset_product hs ht

/--
theorem `disjSups_subset_left` / 定理 `disjSups_subset_left`

English:
theorem disjSups_subset_left
  given: (ht : t₁ subseteq t₂)
  statement: s ○ t₁ subseteq s ○ t₂
  proof: disjSups_subset Subset.rfl ht

中文:
定理 disjSups_subset_left
  条件: (ht : t₁ subseteq t₂)
  结论: s ○ t₁ subseteq s ○ t₂
  证明: disjSups_subset Subset.rfl ht

Depends on / 依赖: Subset, Subset.rfl, disjSups_subset
-/
theorem disjSups_subset_left (ht : t₁ subseteq t₂) : s ○ t₁ subseteq s ○ t₂ :=
  disjSups_subset Subset.rfl ht

/--
theorem `disjSups_subset_right` / 定理 `disjSups_subset_right`

English:
theorem disjSups_subset_right
  given: (hs : s₁ subseteq s₂)
  statement: s₁ ○ t subseteq s₂ ○ t
  proof: disjSups_subset hs Subset.rfl

中文:
定理 disjSups_subset_right
  条件: (hs : s₁ subseteq s₂)
  结论: s₁ ○ t subseteq s₂ ○ t
  证明: disjSups_subset hs Subset.rfl

Depends on / 依赖: Subset, Subset.rfl, disjSups_subset
-/
theorem disjSups_subset_right (hs : s₁ subseteq s₂) : s₁ ○ t subseteq s₂ ○ t :=
  disjSups_subset hs Subset.rfl

/--
theorem `forall_disjSups_iff` / 定理 `forall_disjSups_iff`

English:
theorem forall_disjSups_iff
  given: {p : α -> Prop}
  proof: by
  simp_rw [mem_disjSups]
  refine ⟨fun h a ha b hb hab => h _ ⟨_, ha, _, hb, hab, rfl⟩, ?_⟩
  rintro h _ ⟨a, ha, b, hb, hab, rfl⟩
  exact h _ ha _ hb hab

@[simp]

中文:
定理 对任意_disjSups_iff
  条件: {p : α -> 命题}
  证明: by
  simp_rw [mem_disjSups]
  refine ⟨fun h a ha b hb hab => h _ ⟨_, ha, _, hb, hab, rfl⟩, ?_⟩
  rintro h _ ⟨a, ha, b, hb, hab, rfl⟩
  exact h _ ha _ hb hab

@[simp]

Depends on / 依赖: mem_disjSups, simp_rw
-/
theorem forall_disjSups_iff {p : α -> Prop} :
    (forall c in s ○ t, p c) ↔ forall a in s, forall b in t, Disjoint a b -> p (a ⊔ b) := by
  simp_rw [mem_disjSups]
  refine ⟨fun h a ha b hb hab => h _ ⟨_, ha, _, hb, hab, rfl⟩, ?_⟩
  rintro h _ ⟨a, ha, b, hb, hab, rfl⟩
  exact h _ ha _ hb hab

@[simp]
/--
theorem `disjSups_subset_iff` / 定理 `disjSups_subset_iff`

English:
theorem disjSups_subset_iff
  statement: s ○ t subseteq u ↔ forall a in s, forall b in t, Disjoint a b -> a ⊔ b in u
  proof: forall_disjSups_iff

中文:
定理 disjSups_subset_iff
  结论: s ○ t subseteq u ↔ 对任意 a in s, 对任意 b in t, Disjoint a b -> a ⊔ b in u
  证明: forall_disjSups_iff

Depends on / 依赖: forall_disjSups_iff
-/
theorem disjSups_subset_iff : s ○ t subseteq u ↔ forall a in s, forall b in t, Disjoint a b -> a ⊔ b in u :=
  forall_disjSups_iff

/--
theorem `Nonempty.of_disjSups_left` / 定理 `Nonempty.of_disjSups_left`

English:
theorem Nonempty.of_disjSups_left
  statement: (s ○ t).Nonempty -> s.Nonempty
  proof: by
  simp_rw [Finset.Nonempty, mem_disjSups]
  exact fun ⟨_, a, ha, _⟩ => ⟨a, ha⟩

中文:
定理 非空.of_disjSups_left
  结论: (s ○ t).非空 -> s.非空
  证明: by
  simp_rw [Finset.Nonempty, mem_disjSups]
  exact fun ⟨_, a, ha, _⟩ => ⟨a, ha⟩

Depends on / 依赖: Finset, Finset.Nonempty, Nonempty, mem_disjSups, mono_right, simp_rw
-/
theorem Nonempty.of_disjSups_left : (s ○ t).Nonempty -> s.Nonempty := by
  simp_rw [Finset.Nonempty, mem_disjSups]
  exact fun ⟨_, a, ha, _⟩ => ⟨a, ha⟩

/--
theorem `Nonempty.of_disjSups_right` / 定理 `Nonempty.of_disjSups_right`

English:
theorem Nonempty.of_disjSups_right
  statement: (s ○ t).Nonempty -> t.Nonempty
  proof: by
  simp_rw [Finset.Nonempty, mem_disjSups]
  exact fun ⟨_, _, _, b, hb, _⟩ => ⟨b, hb⟩

@[simp]

中文:
定理 非空.of_disjSups_right
  结论: (s ○ t).非空 -> t.非空
  证明: by
  simp_rw [Finset.Nonempty, mem_disjSups]
  exact fun ⟨_, _, _, b, hb, _⟩ => ⟨b, hb⟩

@[simp]

Depends on / 依赖: Finset, Finset.Nonempty, Nonempty, h.trans_left, mem_disjSups, simp_rw, trans_left
-/
theorem Nonempty.of_disjSups_right : (s ○ t).Nonempty -> t.Nonempty := by
  simp_rw [Finset.Nonempty, mem_disjSups]
  exact fun ⟨_, _, _, b, hb, _⟩ => ⟨b, hb⟩

@[simp]
/--
theorem `disjSups_empty_left` / 定理 `disjSups_empty_left`

English:
theorem disjSups_empty_left
  statement: ∅ ○ t = ∅
  proof: by simp [disjSups]

@[simp]

中文:
定理 disjSups_empty_left
  结论: ∅ ○ t = ∅
  证明: by simp [disjSups]

@[simp]

Depends on / 依赖: disjSups, trans_right
-/
theorem disjSups_empty_left : ∅ ○ t = ∅ := by simp [disjSups]

@[simp]
/--
theorem `disjSups_empty_right` / 定理 `disjSups_empty_right`

English:
theorem disjSups_empty_right
  statement: s ○ ∅ = ∅
  proof: by simp [disjSups]

中文:
定理 disjSups_empty_right
  结论: s ○ ∅ = ∅
  证明: by simp [disjSups]

Depends on / 依赖: disjSups, of_lt
-/
theorem disjSups_empty_right : s ○ ∅ = ∅ := by simp [disjSups]

/--
theorem `disjSups_singleton` / 定理 `disjSups_singleton`

English:
theorem disjSups_singleton
  statement: ({a} ○ {b} : Finset α) = if Disjoint a b then {a ⊔ b} else ∅
  proof: by
  split_ifs with h <;> simp [disjSups, filter_singleton, h]

中文:
定理 disjSups_singleton
  结论: ({a} ○ {b} : 有限集 α) = if Disjoint a b then {a ⊔ b} else ∅
  证明: by
  split_ifs with h <;> simp [disjSups, filter_singleton, h]

Depends on / 依赖: disjSups, filter_singleton, of_gt, split_ifs
-/
theorem disjSups_singleton : ({a} ○ {b} : Finset α) = if Disjoint a b then {a ⊔ b} else ∅ := by
  split_ifs with h <;> simp [disjSups, filter_singleton, h]

/--
theorem `disjSups_union_left` / 定理 `disjSups_union_left`

English:
theorem disjSups_union_left
  statement: (s₁ union s₂) ○ t = s₁ ○ t union s₂ ○ t
  proof: by
  simp [disjSups, filter_union, image_union]

中文:
定理 disjSups_union_left
  结论: (s₁ union s₂) ○ t = s₁ ○ t union s₂ ○ t
  证明: by
  simp [disjSups, filter_union, image_union]

Depends on / 依赖: disjSups, filter_union, image_union
-/
theorem disjSups_union_left : (s₁ union s₂) ○ t = s₁ ○ t union s₂ ○ t := by
  simp [disjSups, filter_union, image_union]

/--
theorem `disjSups_union_right` / 定理 `disjSups_union_right`

English:
theorem disjSups_union_right
  statement: s ○ (t₁ union t₂) = s ○ t₁ union s ○ t₂
  proof: by
  simp [disjSups, filter_union, image_union]

中文:
定理 disjSups_union_right
  结论: s ○ (t₁ union t₂) = s ○ t₁ union s ○ t₂
  证明: by
  simp [disjSups, filter_union, image_union]

Depends on / 依赖: disjSups, filter_union, image_union
-/
theorem disjSups_union_right : s ○ (t₁ union t₂) = s ○ t₁ union s ○ t₂ := by
  simp [disjSups, filter_union, image_union]

/--
theorem `disjSups_inter_subset_left` / 定理 `disjSups_inter_subset_left`

English:
theorem disjSups_inter_subset_left
  statement: (s₁ inter s₂) ○ t subseteq s₁ ○ t inter s₂ ○ t
  proof: by
  simpa only [disjSups, inter_product, filter_inter_distrib] using image_inter_subset _ _ _

中文:
定理 disjSups_inter_subset_left
  结论: (s₁ inter s₂) ○ t subseteq s₁ ○ t inter s₂ ○ t
  证明: by
  simpa only [disjSups, inter_product, filter_inter_distrib] using image_inter_subset _ _ _

Depends on / 依赖: disjSups, filter_inter_distrib, image_inter_subset, inter_product
-/
theorem disjSups_inter_subset_left : (s₁ inter s₂) ○ t subseteq s₁ ○ t inter s₂ ○ t := by
  simpa only [disjSups, inter_product, filter_inter_distrib] using image_inter_subset _ _ _

/--
theorem `disjSups_inter_subset_right` / 定理 `disjSups_inter_subset_right`

English:
theorem disjSups_inter_subset_right
  statement: s ○ (t₁ inter t₂) subseteq s ○ t₁ inter s ○ t₂
  proof: by
  simpa only [disjSups, product_inter, filter_inter_distrib] using image_inter_subset _ _ _

中文:
定理 disjSups_inter_subset_right
  结论: s ○ (t₁ inter t₂) subseteq s ○ t₁ inter s ○ t₂
  证明: by
  simpa only [disjSups, product_inter, filter_inter_distrib] using image_inter_subset _ _ _

Depends on / 依赖: disjSups, filter_inter_distrib, image_inter_subset, product_inter
-/
theorem disjSups_inter_subset_right : s ○ (t₁ inter t₂) subseteq s ○ t₁ inter s ○ t₂ := by
  simpa only [disjSups, product_inter, filter_inter_distrib] using image_inter_subset _ _ _

variable (s t)

/--
theorem `disjSups_comm` / 定理 `disjSups_comm`

English:
theorem disjSups_comm
  statement: s ○ t = t ○ s
  proof: by
  aesop (add simp disjoint_comm, simp sup_comm)

中文:
定理 disjSups_comm
  结论: s ○ t = t ○ s
  证明: by
  aesop (add simp disjoint_comm, simp sup_comm)

Depends on / 依赖: disjoint_comm, sup_comm
-/
theorem disjSups_comm : s ○ t = t ○ s := by
  aesop (add simp disjoint_comm, simp sup_comm)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: @Std.Commutative (Finset α) (· ○ ·)
  body: ⟨disjSups_comm⟩

中文:
实例 :
  签名: @Std.交换 (有限集 α) (· ○ ·)
  定义体: ⟨disjSups_comm⟩

Depends on / 依赖: OrderDual, OrderDual.Preorder.dual_dual, Preorder, disjSups_comm, dual_dual
-/
instance : @Std.Commutative (Finset α) (· ○ ·) := ⟨disjSups_comm⟩

end DisjSups

section DistribLattice

variable [DecidableEq α]
variable [DistribLattice α] [OrderBot α] [DecidableRel (α := α) Disjoint] (s t u v : Finset α)

/--
theorem `disjSups_assoc` / 定理 `disjSups_assoc`

English:
theorem disjSups_assoc
  statement: forall s t u : Finset α, s ○ t ○ u = s ○ (t ○ u)
  proof: by
  refine (associative_of_commutative_of_le inferInstance ?_).assoc
  simp only [disjSups_subset_iff, mem_disjSups]
  rintro s t u _ ⟨a, ha, b, hb, hab, rfl⟩ c hc habc
  rw [disjoint_sup_left] at habc
  exact ⟨a, ha, _, ⟨b, hb, c, hc, habc.2, rfl⟩, hab.sup_right habc.1, (sup_assoc ..).symm⟩

中文:
定理 disjSups_assoc
  结论: 对任意 s t u : 有限集 α, s ○ t ○ u = s ○ (t ○ u)
  证明: by
  refine (associative_of_commutative_of_le inferInstance ?_).assoc
  simp only [disjSups_subset_iff, mem_disjSups]
  rintro s t u _ ⟨a, ha, b, hb, hab, rfl⟩ c hc habc
  rw [disjoint_sup_left] at habc
  exact ⟨a, ha, _, ⟨b, hb, c, hc, habc.2, rfl⟩, hab.sup_right habc.1, (sup_assoc ..).symm⟩

Depends on / 依赖: associative_of_commutative_of_le, disjSups_subset_iff, disjoint_sup_left, hab.sup_right, mem_disjSups, sup_assoc, sup_right
-/
theorem disjSups_assoc : forall s t u : Finset α, s ○ t ○ u = s ○ (t ○ u) := by
  refine (associative_of_commutative_of_le inferInstance ?_).assoc
  simp only [disjSups_subset_iff, mem_disjSups]
  rintro s t u _ ⟨a, ha, b, hb, hab, rfl⟩ c hc habc
  rw [disjoint_sup_left] at habc
  exact ⟨a, ha, _, ⟨b, hb, c, hc, habc.2, rfl⟩, hab.sup_right habc.1, (sup_assoc ..).symm⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: @Std.Associative (Finset α) (· ○ ·)
  body: ⟨disjSups_assoc⟩

中文:
实例 :
  签名: @Std.结合 (有限集 α) (· ○ ·)
  定义体: ⟨disjSups_assoc⟩

Depends on / 依赖: disjSups_assoc
-/
instance : @Std.Associative (Finset α) (· ○ ·) := ⟨disjSups_assoc⟩

/--
theorem `disjSups_left_comm` / 定理 `disjSups_left_comm`

English:
theorem disjSups_left_comm
  statement: s ○ (t ○ u) = t ○ (s ○ u)
  proof: by
  simp_rw [← disjSups_assoc, disjSups_comm s]

中文:
定理 disjSups_left_comm
  结论: s ○ (t ○ u) = t ○ (s ○ u)
  证明: by
  simp_rw [← disjSups_assoc, disjSups_comm s]

Depends on / 依赖: disjSups_assoc, disjSups_comm, simp_rw
-/
theorem disjSups_left_comm : s ○ (t ○ u) = t ○ (s ○ u) := by
  simp_rw [← disjSups_assoc, disjSups_comm s]

/--
theorem `disjSups_right_comm` / 定理 `disjSups_right_comm`

English:
theorem disjSups_right_comm
  statement: s ○ t ○ u = s ○ u ○ t
  proof: by simp_rw [disjSups_assoc, disjSups_comm]

中文:
定理 disjSups_right_comm
  结论: s ○ t ○ u = s ○ u ○ t
  证明: by simp_rw [disjSups_assoc, disjSups_comm]

Depends on / 依赖: disjSups_assoc, disjSups_comm, simp_rw
-/
theorem disjSups_right_comm : s ○ t ○ u = s ○ u ○ t := by simp_rw [disjSups_assoc, disjSups_comm]

/--
theorem `disjSups_disjSups_disjSups_comm` / 定理 `disjSups_disjSups_disjSups_comm`

English:
theorem disjSups_disjSups_disjSups_comm
  statement: s ○ t ○ (u ○ v) = s ○ u ○ (t ○ v)
  proof: by
  simp_rw [← disjSups_assoc, disjSups_right_comm]

中文:
定理 disjSups_disjSups_disjSups_comm
  结论: s ○ t ○ (u ○ v) = s ○ u ○ (t ○ v)
  证明: by
  simp_rw [← disjSups_assoc, disjSups_right_comm]

Depends on / 依赖: disjSups_assoc, disjSups_right_comm, simp_rw
-/
theorem disjSups_disjSups_disjSups_comm : s ○ t ○ (u ○ v) = s ○ u ○ (t ○ v) := by
  simp_rw [← disjSups_assoc, disjSups_right_comm]

end DistribLattice
section Diffs
variable [DecidableEq α]
variable [GeneralizedBooleanAlgebra α] (s s₁ s₂ t t₁ t₂ u : Finset α)

/--
Definition of `diffs` / `diffs` 的定义

English:
definition diffs
  signature: : Finset α -> Finset α -> Finset α
  body: image₂ (· \ ·)

@[inherit_doc]
scoped[FinsetFamily] infixl:74 " \\\\ " => Finset.diffs
  -- This notation is meant to have higher precedence than `\` and `⊓`, but still within the
  -- realm of other binary notation

中文:
定义 diffs
  签名: : 有限集 α -> 有限集 α -> 有限集 α
  定义体: image₂ (· \ ·)

@[inherit_doc]
scoped[FinsetFamily] infixl:74 " \\\\ " => Finset.diffs
  -- This notation is meant to have higher precedence than `\` and `⊓`, but still within the
  -- realm of other binary notation

Depends on / 依赖: hl.node
-/
def diffs : Finset α -> Finset α -> Finset α := image₂ (· \ ·)

@[inherit_doc]
scoped[FinsetFamily] infixl:74 " \\\\ " => Finset.diffs
  -- This notation is meant to have higher precedence than `\` and `⊓`, but still within the
  -- realm of other binary notation

variable {s t} {a b c : α}

/--
lemma `mem_diffs` / 引理 `mem_diffs`

English:
lemma mem_diffs
  statement: c in s \\ t ↔ exists a in s, exists b in t, a \ b = c
  proof: by simp [(· \\ ·)]

中文:
引理 mem_diffs
  结论: c in s \\ t ↔ 存在 a in s, 存在 b in t, a \ b = c
  证明: by simp [(· \\ ·)]

Depends on / 依赖: Or.inl, _nil, zero_le_one
-/
@[simp] lemma mem_diffs : c in s \\ t ↔ exists a in s, exists b in t, a \ b = c := by simp [(· \\ ·)]

variable (s t)

/--
lemma `coe_diffs` / 引理 `coe_diffs`

English:
lemma coe_diffs
  statement: (↑(s \\ t) : Set α) = Set.image2 (· \ ·) s t
  proof: coe_image₂ _ _ _

中文:
引理 coe_diffs
  结论: (↑(s \\ t) : 集合 α) = 集合.image2 (· \ ·) s t
  证明: coe_image₂ _ _ _
-/
@[simp, norm_cast] lemma coe_diffs : (↑(s \\ t) : Set α) = Set.image2 (· \ ·) s t :=
  coe_image₂ _ _ _

/--
lemma `card_diffs_le` / 引理 `card_diffs_le`

English:
lemma card_diffs_le
  statement: #(s \\ t) <= #s * #t
  proof: card_image₂_le _ _ _

中文:
引理 card_diffs_le
  结论: #(s \\ t) <= #s * #t
  证明: card_image₂_le _ _ _

Depends on / 依赖: hl.node
-/
lemma card_diffs_le : #(s \\ t) <= #s * #t := card_image₂_le _ _ _

/--
lemma `card_diffs_iff` / 引理 `card_diffs_iff`

English:
lemma card_diffs_iff
  statement: #(s \\ t) = #s * #t ↔ (s ×ˢ t : Set (α × α)).InjOn fun x => x.1 \ x.2
  proof: card_image₂_iff

中文:
引理 card_diffs_iff
  结论: #(s \\ t) = #s * #t ↔ (s ×ˢ t : 集合 (α × α)).单射限制 fun x => x.1 \ x.2
  证明: card_image₂_iff

Depends on / 依赖: hl.node, hm.node
-/
lemma card_diffs_iff : #(s \\ t) = #s * #t ↔ (s ×ˢ t : Set (α × α)).InjOn fun x => x.1 \ x.2 :=
  card_image₂_iff

variable {s s₁ s₂ t t₁ t₂ u}

/--
lemma `sdiff_mem_diffs` / 引理 `sdiff_mem_diffs`

English:
lemma sdiff_mem_diffs
  statement: a in s -> b in t -> a \ b in s \\ t
  proof: mem_image₂_of_mem

中文:
引理 sdiff_mem_diffs
  结论: a in s -> b in t -> a \ b in s \\ t
  证明: mem_image₂_of_mem
-/
lemma sdiff_mem_diffs : a in s -> b in t -> a \ b in s \\ t := mem_image₂_of_mem

/--
lemma `diffs_subset` / 引理 `diffs_subset`

English:
lemma diffs_subset
  statement: s₁ subseteq s₂ -> t₁ subseteq t₂ -> s₁ \\ t₁ subseteq s₂ \\ t₂
  proof: image₂_subset

中文:
引理 diffs_subset
  结论: s₁ subseteq s₂ -> t₁ subseteq t₂ -> s₁ \\ t₁ subseteq s₂ \\ t₂
  证明: image₂_subset
-/
lemma diffs_subset : s₁ subseteq s₂ -> t₁ subseteq t₂ -> s₁ \\ t₁ subseteq s₂ \\ t₂ := image₂_subset
/--
lemma `diffs_subset_left` / 引理 `diffs_subset_left`

English:
lemma diffs_subset_left
  statement: t₁ subseteq t₂ -> s \\ t₁ subseteq s \\ t₂
  proof: image₂_subset_left

中文:
引理 diffs_subset_left
  结论: t₁ subseteq t₂ -> s \\ t₁ subseteq s \\ t₂
  证明: image₂_subset_left
-/
lemma diffs_subset_left : t₁ subseteq t₂ -> s \\ t₁ subseteq s \\ t₂ := image₂_subset_left
/--
lemma `diffs_subset_right` / 引理 `diffs_subset_right`

English:
lemma diffs_subset_right
  statement: s₁ subseteq s₂ -> s₁ \\ t subseteq s₂ \\ t
  proof: image₂_subset_right

中文:
引理 diffs_subset_right
  结论: s₁ subseteq s₂ -> s₁ \\ t subseteq s₂ \\ t
  证明: image₂_subset_right
-/
lemma diffs_subset_right : s₁ subseteq s₂ -> s₁ \\ t subseteq s₂ \\ t := image₂_subset_right

/--
lemma `image_subset_diffs_left` / 引理 `image_subset_diffs_left`

English:
lemma image_subset_diffs_left
  statement: b in t -> s.image (· \ b) subseteq s \\ t
  proof: image_subset_image₂_left

中文:
引理 image_subset_diffs_left
  结论: b in t -> s.像 (· \ b) subseteq s \\ t
  证明: image_subset_image₂_left
-/
lemma image_subset_diffs_left : b in t -> s.image (· \ b) subseteq s \\ t := image_subset_image₂_left

/--
lemma `image_subset_diffs_right` / 引理 `image_subset_diffs_right`

English:
lemma image_subset_diffs_right
  statement: a in s -> t.image (a \ ·) subseteq s \\ t
  proof: image_subset_image₂_right

中文:
引理 image_subset_diffs_right
  结论: a in s -> t.像 (a \ ·) subseteq s \\ t
  证明: image_subset_image₂_right

Depends on / 依赖: BalancedSz, Nat.succ_inj, add_eq_zero, hl.node, hm.left, hm.right.node, revert, size_eq, succ_inj
-/
lemma image_subset_diffs_right : a in s -> t.image (a \ ·) subseteq s \\ t := image_subset_image₂_right

/--
lemma `forall_mem_diffs` / 引理 `forall_mem_diffs`

English:
lemma forall_mem_diffs
  given: {p : α -> Prop}
  statement: (forall c in s \\ t, p c) ↔ forall a in s, forall b in t, p (a \ b)
  proof: forall_mem_image₂

中文:
引理 对任意_mem_diffs
  条件: {p : α -> 命题}
  结论: (对任意 c in s \\ t, p c) ↔ 对任意 a in s, 对任意 b in t, p (a \ b)
  证明: forall_mem_image₂
-/
lemma forall_mem_diffs {p : α -> Prop} : (forall c in s \\ t, p c) ↔ forall a in s, forall b in t, p (a \ b) :=
  forall_mem_image₂

/--
lemma `diffs_subset_iff` / 引理 `diffs_subset_iff`

English:
lemma diffs_subset_iff
  statement: s \\ t subseteq u ↔ forall a in s, forall b in t, a \ b in u
  proof: image₂_subset_iff

@[simp]

中文:
引理 diffs_subset_iff
  结论: s \\ t subseteq u ↔ 对任意 a in s, 对任意 b in t, a \ b in u
  证明: image₂_subset_iff

@[simp]
-/
@[simp] lemma diffs_subset_iff : s \\ t subseteq u ↔ forall a in s, forall b in t, a \ b in u := image₂_subset_iff

@[simp]
/--
lemma `diffs_nonempty` / 引理 `diffs_nonempty`

English:
lemma diffs_nonempty
  statement: (s \\ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty
  proof: image₂_nonempty_iff

@[aesop safe apply (rule_sets := [finsetNonempty])]

中文:
引理 diffs_nonempty
  结论: (s \\ t).非空 ↔ s.非空 ∧ t.非空
  证明: image₂_nonempty_iff

@[aesop safe apply (rule_sets := [finsetNonempty])]
-/
lemma diffs_nonempty : (s \\ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty := image₂_nonempty_iff

@[aesop safe apply (rule_sets := [finsetNonempty])]
/--
lemma `Nonempty.diffs` / 引理 `Nonempty.diffs`

English:
lemma Nonempty.diffs
  statement: s.Nonempty -> t.Nonempty -> (s \\ t).Nonempty
  proof: Nonempty.image₂

中文:
引理 非空.diffs
  结论: s.非空 -> t.非空 -> (s \\ t).非空
  证明: Nonempty.image₂
-/
protected lemma Nonempty.diffs : s.Nonempty -> t.Nonempty -> (s \\ t).Nonempty := Nonempty.image₂

/--
lemma `Nonempty.of_diffs_left` / 引理 `Nonempty.of_diffs_left`

English:
lemma Nonempty.of_diffs_left
  statement: (s \\ t).Nonempty -> s.Nonempty
  proof: Nonempty.of_image₂_left

中文:
引理 非空.of_diffs_left
  结论: (s \\ t).非空 -> s.非空
  证明: Nonempty.of_image₂_left

Depends on / 依赖: H3.imp, H3_0, Nat.le_of_add_le_add_right, Nat.le_of_succ_le_succ, Nat.lt_succ_iff, Nonempty, Nonempty.of_image, le_of_add_le_add_right, le_of_succ_le_succ, lt_succ_iff, or_iff_left_of_imp, replace, size_eq
-/
lemma Nonempty.of_diffs_left : (s \\ t).Nonempty -> s.Nonempty := Nonempty.of_image₂_left
/--
lemma `Nonempty.of_diffs_right` / 引理 `Nonempty.of_diffs_right`

English:
lemma Nonempty.of_diffs_right
  statement: (s \\ t).Nonempty -> t.Nonempty
  proof: Nonempty.of_image₂_right

中文:
引理 非空.of_diffs_right
  结论: (s \\ t).非空 -> t.非空
  证明: Nonempty.of_image₂_right

Depends on / 依赖: Nonempty, Nonempty.of_image, add_comm, dual_iff, dual_rotateR, hl.dual, hr.dual.rotateL, rotateL, size_dual
-/
lemma Nonempty.of_diffs_right : (s \\ t).Nonempty -> t.Nonempty := Nonempty.of_image₂_right

/--
lemma `empty_sdiffs` / 引理 `empty_sdiffs`

English:
lemma empty_sdiffs
  statement: ∅ \\ t = ∅
  proof: image₂_empty_left

中文:
引理 empty_sdiffs
  结论: ∅ \\ t = ∅
  证明: image₂_empty_left

Depends on / 依赖: Or.inl, Or.inr, balance, hl.node, hl.rotateL, hl.rotateR, not_lt, rotateL, rotateR, split_ifs
-/
@[simp] lemma empty_sdiffs : ∅ \\ t = ∅ := image₂_empty_left
/--
lemma `diffs_empty` / 引理 `diffs_empty`

English:
lemma diffs_empty
  statement: s \\ ∅ = ∅
  proof: image₂_empty_right

中文:
引理 diffs_empty
  结论: s \\ ∅ = ∅
  证明: image₂_empty_right

Depends on / 依赖: Nat.add_le_add_left, Nat.dist_tri_left, Nat.dist_tri_right, Nat.le_add_left, Nat.mul_le_mul_left, Nat.mul_succ, add_le_add, add_le_add_left, dist_tri_left, dist_tri_right, le_add_left, le_tran, le_trans, mul_le_mul_left, mul_succ
-/
@[simp] lemma diffs_empty : s \\ ∅ = ∅ := image₂_empty_right
/--
lemma `diffs_eq_empty` / 引理 `diffs_eq_empty`

English:
lemma diffs_eq_empty
  statement: s \\ t = ∅ ↔ s = ∅ ∨ t = ∅
  proof: image₂_eq_empty_iff

@[deprecated (since := "2026-06-03")] alias empty_diffs := empty_sdiffs

中文:
引理 diffs_eq_empty
  结论: s \\ t = ∅ ↔ s = ∅ ∨ t = ∅
  证明: image₂_eq_empty_iff

@[deprecated (since := "2026-06-03")] alias empty_diffs := empty_sdiffs

Depends on / 依赖: H1.symm, H2.symm, _aux, _lemma, balance
-/
@[simp] lemma diffs_eq_empty : s \\ t = ∅ ↔ s = ∅ ∨ t = ∅ := image₂_eq_empty_iff

@[deprecated (since := "2026-06-03")] alias empty_diffs := empty_sdiffs

/--
lemma `singleton_diffs` / 引理 `singleton_diffs`

English:
lemma singleton_diffs
  statement: {a} \\ t = t.image (a \ ·)
  proof: image₂_singleton_left

中文:
引理 singleton_diffs
  结论: {a} \\ t = t.像 (a \ ·)
  证明: image₂_singleton_left

Depends on / 依赖: balance, balance_eq_balance, hl.balance
-/
@[simp] lemma singleton_diffs : {a} \\ t = t.image (a \ ·) := image₂_singleton_left
/--
lemma `diffs_singleton` / 引理 `diffs_singleton`

English:
lemma diffs_singleton
  statement: s \\ {b} = s.image (· \ b)
  proof: image₂_singleton_right

中文:
引理 diffs_singleton
  结论: s \\ {b} = s.像 (· \ b)
  证明: image₂_singleton_right

Depends on / 依赖: Nat.eq_zero_or_pos, Nat.mul_le_mul_left, Nat.zero_le, Or.inl, _aux, balance, balanceL_eq_balance, balance_eq_balance, eq_zero_or_pos, hl.balance, le_trans, mul_le_mul_left, replace, zero_le
-/
@[simp] lemma diffs_singleton : s \\ {b} = s.image (· \ b) := image₂_singleton_right
/--
lemma `singleton_diffs_singleton` / 引理 `singleton_diffs_singleton`

English:
lemma singleton_diffs_singleton
  statement: ({a} \\ {b} : Finset α) = {a \ b}
  proof: image₂_singleton

中文:
引理 singleton_diffs_singleton
  结论: ({a} \\ {b} : 有限集 α) = {a \ b}
  证明: image₂_singleton

Depends on / 依赖: Or.inl, Or.inr, balance, balanceL_eq_balance, dist_le, e.dist_le, hl.balance
-/
lemma singleton_diffs_singleton : ({a} \\ {b} : Finset α) = {a \ b} := image₂_singleton

/--
lemma `diffs_union_left` / 引理 `diffs_union_left`

English:
lemma diffs_union_left
  statement: (s₁ union s₂) \\ t = s₁ \\ t union s₂ \\ t
  proof: image₂_union_left

中文:
引理 diffs_union_left
  结论: (s₁ union s₂) \\ t = s₁ \\ t union s₂ \\ t
  证明: image₂_union_left

Depends on / 依赖: balanceL_aux, dual_balanceR, dual_iff, hl.dual, hr.dual.balanceL_aux, size_dual
-/
lemma diffs_union_left : (s₁ union s₂) \\ t = s₁ \\ t union s₂ \\ t := image₂_union_left
/--
lemma `diffs_union_right` / 引理 `diffs_union_right`

English:
lemma diffs_union_right
  statement: s \\ (t₁ union t₂) = s \\ t₁ union s \\ t₂
  proof: image₂_union_right

中文:
引理 diffs_union_right
  结论: s \\ (t₁ union t₂) = s \\ t₁ union s \\ t₂
  证明: image₂_union_right

Depends on / 依赖: balanceL, balance_sz_dual, dual_balanceR, dual_iff, hl.dual, hr.dual.balanceL
-/
lemma diffs_union_right : s \\ (t₁ union t₂) = s \\ t₁ union s \\ t₂ := image₂_union_right

/--
lemma `diffs_inter_subset_left` / 引理 `diffs_inter_subset_left`

English:
lemma diffs_inter_subset_left
  statement: (s₁ inter s₂) \\ t subseteq s₁ \\ t inter s₂ \\ t
  proof: image₂_inter_subset_left

中文:
引理 diffs_inter_subset_left
  结论: (s₁ inter s₂) \\ t subseteq s₁ \\ t inter s₂ \\ t
  证明: image₂_inter_subset_left

Depends on / 依赖: H.left, H.right, Or.inr, balanceL, eq_node, eraseMax, generalizing, size_balanceL, size_node
-/
lemma diffs_inter_subset_left : (s₁ inter s₂) \\ t subseteq s₁ \\ t inter s₂ \\ t := image₂_inter_subset_left
/--
lemma `diffs_inter_subset_right` / 引理 `diffs_inter_subset_right`

English:
lemma diffs_inter_subset_right
  statement: s \\ (t₁ inter t₂) subseteq s \\ t₁ inter s \\ t₂
  proof: image₂_inter_subset_right

中文:
引理 diffs_inter_subset_right
  结论: s \\ (t₁ inter t₂) subseteq s \\ t₁ inter s \\ t₂
  证明: image₂_inter_subset_right

Depends on / 依赖: H.dual.eraseMax_aux, _dual, dual_eraseMin, dual_iff, dual_node, eraseMax_aux, findMax, size_dual
-/
lemma diffs_inter_subset_right : s \\ (t₁ inter t₂) subseteq s \\ t₁ inter s \\ t₂ := image₂_inter_subset_right

/--
lemma `subset_diffs` / 引理 `subset_diffs`

English:
lemma subset_diffs
  given: {s t : Set α}
  proof: subset_set_image₂

中文:
引理 subset_diffs
  条件: {s t : 集合 α}
  证明: subset_set_image₂
-/
lemma subset_diffs {s t : Set α} :
    ↑u subseteq Set.image2 (· \ ·) s t -> exists s' t' : Finset α, ↑s' subseteq s ∧ ↑t' subseteq t ∧ u subseteq s' \\ t' :=
  subset_set_image₂

variable (s t u)

/--
lemma `biUnion_image_sdiff_left` / 引理 `biUnion_image_sdiff_left`

English:
lemma biUnion_image_sdiff_left
  statement: s.biUnion (fun a => t.image (a \ ·)) = s \\ t
  proof: biUnion_image_left

中文:
引理 biUnion_image_sdiff_left
  结论: s.biUnion (fun a => t.像 (a \ ·)) = s \\ t
  证明: biUnion_image_left

Depends on / 依赖: Bounded, WithTop, _all, balanceR, biUnion_image_left, eraseMax_aux, findMax, hr.of_gt, le_of_lt, mono_left, of_gt, splitMax_eq, split_ifs, to_nil, to_nil.mono_left, zero_add
-/
lemma biUnion_image_sdiff_left : s.biUnion (fun a => t.image (a \ ·)) = s \\ t := biUnion_image_left
/--
lemma `biUnion_image_sdiff_right` / 引理 `biUnion_image_sdiff_right`

English:
lemma biUnion_image_sdiff_right
  statement: t.biUnion (fun b => s.image (· \ b)) = s \\ t
  proof: biUnion_image_right

中文:
引理 biUnion_image_sdiff_right
  结论: t.biUnion (fun b => s.像 (· \ b)) = s \\ t
  证明: biUnion_image_right

Depends on / 依赖: biUnion_image_right, glue_aux, hl.trans_right, hr.trans_left, to_sep, trans_left, trans_right
-/
lemma biUnion_image_sdiff_right : t.biUnion (fun b => s.image (· \ b)) = s \\ t :=
  biUnion_image_right

/--
lemma `image_sdiff_product` / 引理 `image_sdiff_product`

English:
lemma image_sdiff_product
  given: (s t : Finset α)
  statement: (s ×ˢ t).image (uncurry (· \ ·)) = s \\ t
  proof: image_uncurry_product _ _ _

中文:
引理 image_sdiff_product
  条件: (s t : 有限集 α)
  结论: (s ×ˢ t).像 (uncurry (· \ ·)) = s \\ t
  证明: image_uncurry_product _ _ _

Depends on / 依赖: image_uncurry_product
-/
lemma image_sdiff_product (s t : Finset α) : (s ×ˢ t).image (uncurry (· \ ·)) = s \\ t :=
  image_uncurry_product _ _ _

/--
lemma `diffs_right_comm` / 引理 `diffs_right_comm`

English:
lemma diffs_right_comm
  statement: s \\ t \\ u = s \\ u \\ t
  proof: image₂_right_comm sdiff_right_comm

中文:
引理 diffs_right_comm
  结论: s \\ t \\ u = s \\ u \\ t
  证明: image₂_right_comm sdiff_right_comm

Depends on / 依赖: Or.inl, add_right_comm, balanceL_aux, balanceL_eq_balance, balance_eq_balance, hr.right, merge_lemma, sdiff_right_comm, size_balance
-/
lemma diffs_right_comm : s \\ t \\ u = s \\ u \\ t := image₂_right_comm sdiff_right_comm

end Diffs

section Compls
variable [BooleanAlgebra α] (s s₁ s₂ t : Finset α)

/--
Definition of `compls` / `compls` 的定义

English:
definition compls
  signature: : Finset α -> Finset α
  body: map ⟨compl, compl_injective⟩

@[inherit_doc]
scoped[FinsetFamily] postfix:max "ᶜˢ" => Finset.compls

中文:
定义 compls
  签名: : 有限集 α -> 有限集 α
  定义体: map ⟨compl, compl_injective⟩

@[inherit_doc]
scoped[FinsetFamily] postfix:max "ᶜˢ" => Finset.compls

Depends on / 依赖: compl_injective, generalizing, hl.of_lt, hl.right, hr.dual, hr.left, hr.of_gt, merge_node, of_gt, of_lt, sep.imp, split_ifs, to_nil, zero_add
-/
def compls : Finset α -> Finset α := map ⟨compl, compl_injective⟩

@[inherit_doc]
scoped[FinsetFamily] postfix:max "ᶜˢ" => Finset.compls

variable {s t} {a : α}

/--
lemma `mem_compls` / 引理 `mem_compls`

English:
lemma mem_compls
  statement: a in sᶜˢ ↔ aᶜ in s
  proof: by
  rw [Iff.comm]; rw [← mem_map' ⟨compl]; rw [compl_injective⟩]; rw [Embedding.coeFn_mk]; rw [compl_compl]; rw [compls]

中文:
引理 mem_compls
  结论: a in sᶜˢ ↔ aᶜ in s
  证明: by
  rw [Iff.comm]; rw [← mem_map' ⟨compl]; rw [compl_injective⟩]; rw [Embedding.coeFn_mk]; rw [compl_compl]; rw [compls]
-/
@[simp] lemma mem_compls : a in sᶜˢ ↔ aᶜ in s := by
  rw [Iff.comm]; rw [← mem_map' ⟨compl]; rw [compl_injective⟩]; rw [Embedding.coeFn_mk]; rw [compl_compl]; rw [compls]

variable (s t)

/--
lemma `image_compl` / 引理 `image_compl`

English:
lemma image_compl
  given: [DecidableEq α]
  statement: s.image compl = sᶜˢ
  proof: by simp [compls, map_eq_image]

中文:
引理 image_compl
  条件: [DecidableEq α]
  结论: s.像 compl = sᶜˢ
  证明: by simp [compls, map_eq_image]
-/
@[simp] lemma image_compl [DecidableEq α] : s.image compl = sᶜˢ := by simp [compls, map_eq_image]

/--
lemma `coe_compls` / 引理 `coe_compls`

English:
lemma coe_compls
  statement: (↑sᶜˢ : Set α) = compl '' ↑s
  proof: coe_map _ _

中文:
引理 coe_compls
  结论: (↑sᶜˢ : 集合 α) = compl '' ↑s
  证明: coe_map _ _
-/
@[simp, norm_cast] lemma coe_compls : (↑sᶜˢ : Set α) = compl '' ↑s := coe_map _ _

/--
lemma `card_compls` / 引理 `card_compls`

English:
lemma card_compls
  statement: #sᶜˢ = #s
  proof: card_map _

中文:
引理 card_compls
  结论: #sᶜˢ = #s
  证明: card_map _
-/
@[simp] lemma card_compls : #sᶜˢ = #s := card_map _

variable {s s₁ s₂ t}

/--
lemma `compl_mem_compls` / 引理 `compl_mem_compls`

English:
lemma compl_mem_compls
  statement: a in s -> aᶜ in sᶜˢ
  proof: mem_map_of_mem _

中文:
引理 compl_mem_compls
  结论: a in s -> aᶜ in sᶜˢ
  证明: mem_map_of_mem _

Depends on / 依赖: mem_map_of_mem
-/
lemma compl_mem_compls : a in s -> aᶜ in sᶜˢ := mem_map_of_mem _
/--
lemma `compls_subset_compls` / 引理 `compls_subset_compls`

English:
lemma compls_subset_compls
  statement: s₁ᶜˢ subseteq s₂ᶜˢ ↔ s₁ subseteq s₂
  proof: map_subset_map

中文:
引理 compls_subset_compls
  结论: s₁ᶜˢ subseteq s₂ᶜˢ ↔ s₁ subseteq s₂
  证明: map_subset_map

Depends on / 依赖: And.intro, Bounded, Option.map, _nil, and_true, constructo, f_strict_mono, generalizing, h.left, h.ord, h.right, size_nil, size_node, t_ih_l, t_ih_r, t_l_size, t_l_valid, t_l_valid.ord, t_r_size, t_r_valid
-/
@[simp] lemma compls_subset_compls : s₁ᶜˢ subseteq s₂ᶜˢ ↔ s₁ subseteq s₂ := map_subset_map
/--
lemma `forall_mem_compls` / 引理 `forall_mem_compls`

English:
lemma forall_mem_compls
  given: {p : α -> Prop}
  statement: (forall a in sᶜˢ, p a) ↔ forall a in s, p aᶜ
  proof: forall_mem_map

中文:
引理 对任意_mem_compls
  条件: {p : α -> 命题}
  结论: (对任意 a in sᶜˢ, p a) ↔ 对任意 a in s, p aᶜ
  证明: forall_mem_map

Depends on / 依赖: forall_mem_map
-/
lemma forall_mem_compls {p : α -> Prop} : (forall a in sᶜˢ, p a) ↔ forall a in s, p aᶜ := forall_mem_map
/--
lemma `exists_compls_iff` / 引理 `exists_compls_iff`

English:
lemma exists_compls_iff
  given: {p : α -> Prop}
  statement: (exists a in sᶜˢ, p a) ↔ exists a in s, p aᶜ
  proof: by aesop

中文:
引理 存在_compls_iff
  条件: {p : α -> 命题}
  结论: (存在 a in sᶜˢ, p a) ↔ 存在 a in s, p aᶜ
  证明: by aesop

Depends on / 依赖: Raised, balanceR, generalizing, h.left, h.right, h.right.bal, h.right.s, h.sz, h_balanceable, size_balanceR, size_node, t_ih_l, t_ih_r, t_l_size, t_l_valid, t_l_valid.bal, t_l_valid.sz, t_r_size, t_r_valid
-/
lemma exists_compls_iff {p : α -> Prop} : (exists a in sᶜˢ, p a) ↔ exists a in s, p aᶜ := by aesop

/--
lemma `compls_compls` / 引理 `compls_compls`

English:
lemma compls_compls
  given: (s : Finset α)
  statement: sᶜˢᶜˢ = s
  proof: by ext; simp

中文:
引理 compls_compls
  条件: (s : 有限集 α)
  结论: sᶜˢᶜˢ = s
  证明: by ext; simp
-/
@[simp] lemma compls_compls (s : Finset α) : sᶜˢᶜˢ = s := by ext; simp

/--
lemma `compls_subset_iff` / 引理 `compls_subset_iff`

English:
lemma compls_subset_iff
  statement: sᶜˢ subseteq t ↔ s subseteq tᶜˢ
  proof: by rw [← compls_subset_compls, compls_compls]

@[simp]

中文:
引理 compls_subset_iff
  结论: sᶜˢ subseteq t ↔ s subseteq tᶜˢ
  证明: by rw [← compls_subset_compls, compls_compls]

@[simp]

Depends on / 依赖: compls_compls, compls_subset_compls
-/
lemma compls_subset_iff : sᶜˢ subseteq t ↔ s subseteq tᶜˢ := by rw [← compls_subset_compls, compls_compls]

@[simp]
/--
lemma `compls_nonempty` / 引理 `compls_nonempty`

English:
lemma compls_nonempty
  statement: sᶜˢ.Nonempty ↔ s.Nonempty
  proof: map_nonempty

protected alias ⟨Nonempty.of_compls, Nonempty.compls⟩ := compls_nonempty

中文:
引理 compls_nonempty
  结论: sᶜˢ.非空 ↔ s.非空
  证明: map_nonempty

protected alias ⟨Nonempty.of_compls, Nonempty.compls⟩ := compls_nonempty

Depends on / 依赖: map_nonempty
-/
lemma compls_nonempty : sᶜˢ.Nonempty ↔ s.Nonempty := map_nonempty

protected alias ⟨Nonempty.of_compls, Nonempty.compls⟩ := compls_nonempty
attribute [aesop safe apply (rule_sets := [finsetNonempty])] Nonempty.compls

/--
lemma `compls_empty` / 引理 `compls_empty`

English:
lemma compls_empty
  statement: (∅ : Finset α)ᶜˢ = ∅
  proof: map_empty _

中文:
引理 compls_empty
  结论: (∅ : 有限集 α)ᶜˢ = ∅
  证明: map_empty _
-/
@[simp] lemma compls_empty : (∅ : Finset α)ᶜˢ = ∅ := map_empty _
/--
lemma `compls_eq_empty` / 引理 `compls_eq_empty`

English:
lemma compls_eq_empty
  statement: sᶜˢ = ∅ ↔ s = ∅
  proof: map_eq_empty

中文:
引理 compls_eq_empty
  结论: sᶜˢ = ∅ ↔ s = ∅
  证明: map_eq_empty
-/
@[simp] lemma compls_eq_empty : sᶜˢ = ∅ ↔ s = ∅ := map_eq_empty
/--
lemma `compls_singleton` / 引理 `compls_singleton`

English:
lemma compls_singleton
  given: (a : α)
  statement: {a}ᶜˢ = {aᶜ}
  proof: map_singleton _ _

中文:
引理 compls_singleton
  条件: (a : α)
  结论: {a}ᶜˢ = {aᶜ}
  证明: map_singleton _ _
-/
@[simp] lemma compls_singleton (a : α) : {a}ᶜˢ = {aᶜ} := map_singleton _ _
/--
lemma `compls_univ` / 引理 `compls_univ`

English:
lemma compls_univ
  given: [Fintype α]
  statement: (univ : Finset α)ᶜˢ = univ
  proof: by ext; simp

中文:
引理 compls_univ
  条件: [有限类型 α]
  结论: (univ : 有限集 α)ᶜˢ = univ
  证明: by ext; simp
-/
@[simp] lemma compls_univ [Fintype α] : (univ : Finset α)ᶜˢ = univ := by ext; simp

variable [DecidableEq α]

/--
lemma `compls_union` / 引理 `compls_union`

English:
lemma compls_union
  given: (s t : Finset α)
  statement: (s union t)ᶜˢ = sᶜˢ union tᶜˢ
  proof: map_union _ _

中文:
引理 compls_union
  条件: (s t : 有限集 α)
  结论: (s union t)ᶜˢ = sᶜˢ union tᶜˢ
  证明: map_union _ _
-/
@[simp] lemma compls_union (s t : Finset α) : (s union t)ᶜˢ = sᶜˢ union tᶜˢ := map_union _ _
/--
lemma `compls_inter` / 引理 `compls_inter`

English:
lemma compls_inter
  given: (s t : Finset α)
  statement: (s inter t)ᶜˢ = sᶜˢ inter tᶜˢ
  proof: map_inter _ _

中文:
引理 compls_inter
  条件: (s t : 有限集 α)
  结论: (s inter t)ᶜˢ = sᶜˢ inter tᶜˢ
  证明: map_inter _ _
-/
@[simp] lemma compls_inter (s t : Finset α) : (s inter t)ᶜˢ = sᶜˢ inter tᶜˢ := map_inter _ _

/--
lemma `compls_infs` / 引理 `compls_infs`

English:
lemma compls_infs
  given: (s t : Finset α)
  statement: (s ⊼ t)ᶜˢ = sᶜˢ ⊻ tᶜˢ
  proof: by
  simp_rw [← image_compl]; exact image_image₂_distrib fun _ _ => compl_inf

中文:
引理 compls_infs
  条件: (s t : 有限集 α)
  结论: (s ⊼ t)ᶜˢ = sᶜˢ ⊻ tᶜˢ
  证明: by
  simp_rw [← image_compl]; exact image_image₂_distrib fun _ _ => compl_inf
-/
@[simp] lemma compls_infs (s t : Finset α) : (s ⊼ t)ᶜˢ = sᶜˢ ⊻ tᶜˢ := by
  simp_rw [← image_compl]; exact image_image₂_distrib fun _ _ => compl_inf

/--
lemma `compls_sups` / 引理 `compls_sups`

English:
lemma compls_sups
  given: (s t : Finset α)
  statement: (s ⊻ t)ᶜˢ = sᶜˢ ⊼ tᶜˢ
  proof: by
  simp_rw [← image_compl]; exact image_image₂_distrib fun _ _ => compl_sup

中文:
引理 compls_sups
  条件: (s t : 有限集 α)
  结论: (s ⊻ t)ᶜˢ = sᶜˢ ⊼ tᶜˢ
  证明: by
  simp_rw [← image_compl]; exact image_image₂_distrib fun _ _ => compl_sup
-/
@[simp] lemma compls_sups (s t : Finset α) : (s ⊻ t)ᶜˢ = sᶜˢ ⊼ tᶜˢ := by
  simp_rw [← image_compl]; exact image_image₂_distrib fun _ _ => compl_sup

/--
lemma `infs_compls_eq_diffs` / 引理 `infs_compls_eq_diffs`

English:
lemma infs_compls_eq_diffs
  given: (s t : Finset α)
  statement: s ⊼ tᶜˢ = s \\ t
  proof: by
  ext; simp [sdiff_eq]; aesop

中文:
引理 infs_compls_eq_diffs
  条件: (s t : 有限集 α)
  结论: s ⊼ tᶜˢ = s \\ t
  证明: by
  ext; simp [sdiff_eq]; aesop
-/
@[simp] lemma infs_compls_eq_diffs (s t : Finset α) : s ⊼ tᶜˢ = s \\ t := by
  ext; simp [sdiff_eq]; aesop

/--
lemma `compls_infs_eq_diffs` / 引理 `compls_infs_eq_diffs`

English:
lemma compls_infs_eq_diffs
  given: (s t : Finset α)
  statement: sᶜˢ ⊼ t = t \\ s
  proof: by
  rw [infs_comm]; rw [infs_compls_eq_diffs]

中文:
引理 compls_infs_eq_diffs
  条件: (s t : 有限集 α)
  结论: sᶜˢ ⊼ t = t \\ s
  证明: by
  rw [infs_comm]; rw [infs_compls_eq_diffs]
-/
@[simp] lemma compls_infs_eq_diffs (s t : Finset α) : sᶜˢ ⊼ t = t \\ s := by
  rw [infs_comm]; rw [infs_compls_eq_diffs]

/--
lemma `diffs_compls_eq_infs` / 引理 `diffs_compls_eq_infs`

English:
lemma diffs_compls_eq_infs
  given: (s t : Finset α)
  statement: s \\ tᶜˢ = s ⊼ t
  proof: by
  rw [← infs_compls_eq_diffs]; rw [compls_compls]

中文:
引理 diffs_compls_eq_infs
  条件: (s t : 有限集 α)
  结论: s \\ tᶜˢ = s ⊼ t
  证明: by
  rw [← infs_compls_eq_diffs]; rw [compls_compls]
-/
@[simp] lemma diffs_compls_eq_infs (s t : Finset α) : s \\ tᶜˢ = s ⊼ t := by
  rw [← infs_compls_eq_diffs]; rw [compls_compls]

variable {α : Type*} [DecidableEq α] [Fintype α] {𝒜 : Finset (Finset α)} {n : Nat}

/--
lemma `_root_.Set.Sized.compls` / 引理 `_root_.Set.Sized.compls`

English:
lemma _root_.Set.Sized.compls
  given: (h𝒜 : (𝒜 : Set (Finset α)).Sized n)
  proof: Finset.forall_mem_compls.2 fun s hs => by rw [Finset.card_compl, h𝒜 hs]

中文:
引理 _root_.集合.Sized.compls
  条件: (h𝒜 : (𝒜 : 集合 (有限集 α)).Sized n)
  证明: Finset.forall_mem_compls.2 fun s hs => by rw [Finset.card_compl, h𝒜 hs]

Depends on / 依赖: instDecidableEqBool
-/
protected lemma _root_.Set.Sized.compls (h𝒜 : (𝒜 : Set (Finset α)).Sized n) :
    (𝒜ᶜˢ : Set (Finset α)).Sized (Fintype.card α - n) :=
Finset.forall_mem_compls.2 fun s hs => by rw [Finset.card_compl, h𝒜 hs]

/--
lemma `sized_compls` / 引理 `sized_compls`

English:
lemma sized_compls
  given: (hn : n <= Fintype.card α)
  proof: by simpa using h𝒜.compls
  mpr h𝒜 := by simpa only [Nat.sub_sub_self hn] using h𝒜.compls

中文:
引理 sized_compls
  条件: (hn : n <= 有限类型.card α)
  证明: by simpa using h𝒜.compls
  mpr h𝒜 := by simpa only [Nat.sub_sub_self hn] using h𝒜.compls

Depends on / 依赖: Nat.sub_sub_self, compls, sub_sub_self
-/
lemma sized_compls (hn : n <= Fintype.card α) :
    (𝒜ᶜˢ : Set (Finset α)).Sized n ↔ (𝒜 : Set (Finset α)).Sized (Fintype.card α - n) where
  mp h𝒜 := by simpa using h𝒜.compls
  mpr h𝒜 := by simpa only [Nat.sub_sub_self hn] using h𝒜.compls

end Compls
end Finset
