/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Patrick Massot
-/
module

public import Mathlib.Data.Set.Image
public import Mathlib.Data.SProd
public import Mathlib.Data.Sum.Basic

/-!
# Sets in product and pi types

This file proves basic properties of product of sets in `α × β` and in `Π i, α i`, and of the
diagonal of a type.

## Main declarations

This file contains basic results on the following notions, which are defined in `Set.Operations`.

* `Set.prod`: Binary product of sets. For `s : Set α`, `t : Set β`, we have
  `s.prod t : Set (α × β)`. Denoted by `s ×ˢ t`.
* `Set.diagonal`: Diagonal of a type. `Set.diagonal α = {(x, x) | x : α}`.
* `Set.offDiag`: Off-diagonal. `s ×ˢ s` without the diagonal.
* `Set.pi`: Arbitrary product of sets.
-/

@[expose] public section


open Function

namespace Set

/-! ### Cartesian binary product of sets -/


section Prod

variable {α β γ δ : Type*} {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {a : α} {b : β}

/--
theorem `Subsingleton.prod` / 定理 `Subsingleton.prod`

English:
theorem Subsingleton.prod
  given: (hs : s.Subsingleton) (ht : t.Subsingleton)
  proof: fun _x hx _y hy =>
  Prod.ext (hs hx.1 hy.1) (ht hx.2 hy.2)

中文:
定理 Subsingleton.prod
  条件: (hs : s.Subsingleton) (ht : t.Subsingleton)
  证明: fun _x hx _y hy =>
  Prod.ext (hs hx.1 hy.1) (ht hx.2 hy.2)
-/
theorem Subsingleton.prod (hs : s.Subsingleton) (ht : t.Subsingleton) :
    (s ×ˢ t).Subsingleton := fun _x hx _y hy =>
  Prod.ext (hs hx.1 hy.1) (ht hx.2 hy.2)

/--
Instance `decidableMemProd` / 实例 `decidableMemProd`

English:
instance decidableMemProd
  signature: [DecidablePred (· in s)] [DecidablePred (· in t)]
  body: fun x => inferInstanceAs (Decidable (x.1 in s ∧ x.2 in t))

@[gcongr]

中文:
实例 decidableMemProd
  签名: [DecidablePred (· in s)] [DecidablePred (· in t)]
  定义体: fun x => inferInstanceAs (Decidable (x.1 in s ∧ x.2 in t))

@[gcongr]

Depends on / 依赖: Decidable
-/
instance decidableMemProd [DecidablePred (· in s)] [DecidablePred (· in t)] :
    DecidablePred (· in s ×ˢ t) := fun x => inferInstanceAs (Decidable (x.1 in s ∧ x.2 in t))

@[gcongr]
/--
theorem `prod_mono` / 定理 `prod_mono`

English:
theorem prod_mono
  given: (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂)
  statement: s₁ ×ˢ t₁ subseteq s₂ ×ˢ t₂
  proof: fun _ ⟨h₁, h₂⟩ => ⟨hs h₁, ht h₂⟩

中文:
定理 prod_mono
  条件: (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂)
  结论: s₁ ×ˢ t₁ subseteq s₂ ×ˢ t₂
  证明: fun _ ⟨h₁, h₂⟩ => ⟨hs h₁, ht h₂⟩
-/
theorem prod_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : s₁ ×ˢ t₁ subseteq s₂ ×ˢ t₂ :=
  fun _ ⟨h₁, h₂⟩ => ⟨hs h₁, ht h₂⟩

/--
theorem `prod_mono_left` / 定理 `prod_mono_left`

English:
theorem prod_mono_left
  given: (hs : s₁ subseteq s₂)
  statement: s₁ ×ˢ t subseteq s₂ ×ˢ t
  proof: prod_mono hs Subset.rfl

alias prod_subset_prod_left := prod_mono_left

中文:
定理 prod_mono_left
  条件: (hs : s₁ subseteq s₂)
  结论: s₁ ×ˢ t subseteq s₂ ×ˢ t
  证明: prod_mono hs Subset.rfl

alias prod_subset_prod_left := prod_mono_left

Depends on / 依赖: Subset, Subset.rfl, prod_mono
-/
theorem prod_mono_left (hs : s₁ subseteq s₂) : s₁ ×ˢ t subseteq s₂ ×ˢ t :=
  prod_mono hs Subset.rfl

alias prod_subset_prod_left := prod_mono_left

/--
theorem `prod_mono_right` / 定理 `prod_mono_right`

English:
theorem prod_mono_right
  given: (ht : t₁ subseteq t₂)
  statement: s ×ˢ t₁ subseteq s ×ˢ t₂
  proof: prod_mono Subset.rfl ht

alias prod_subset_prod_right := prod_mono_right

@[simp]

中文:
定理 prod_mono_right
  条件: (ht : t₁ subseteq t₂)
  结论: s ×ˢ t₁ subseteq s ×ˢ t₂
  证明: prod_mono Subset.rfl ht

alias prod_subset_prod_right := prod_mono_right

@[simp]

Depends on / 依赖: Subset, Subset.rfl, prod_mono
-/
theorem prod_mono_right (ht : t₁ subseteq t₂) : s ×ˢ t₁ subseteq s ×ˢ t₂ :=
  prod_mono Subset.rfl ht

alias prod_subset_prod_right := prod_mono_right

@[simp]
/--
theorem `prod_self_subset_prod_self` / 定理 `prod_self_subset_prod_self`

English:
theorem prod_self_subset_prod_self
  statement: s₁ ×ˢ s₁ subseteq s₂ ×ˢ s₂ ↔ s₁ subseteq s₂
  proof: ⟨fun h _ hx => (h (mk_mem_prod hx hx)).1, fun h _ hx => ⟨h hx.1, h hx.2⟩⟩

@[simp]

中文:
定理 prod_self_subset_prod_self
  结论: s₁ ×ˢ s₁ subseteq s₂ ×ˢ s₂ ↔ s₁ subseteq s₂
  证明: ⟨fun h _ hx => (h (mk_mem_prod hx hx)).1, fun h _ hx => ⟨h hx.1, h hx.2⟩⟩

@[simp]

Depends on / 依赖: mk_mem_prod
-/
theorem prod_self_subset_prod_self : s₁ ×ˢ s₁ subseteq s₂ ×ˢ s₂ ↔ s₁ subseteq s₂ :=
  ⟨fun h _ hx => (h (mk_mem_prod hx hx)).1, fun h _ hx => ⟨h hx.1, h hx.2⟩⟩

@[simp]
/--
theorem `prod_self_ssubset_prod_self` / 定理 `prod_self_ssubset_prod_self`

English:
theorem prod_self_ssubset_prod_self
  statement: s₁ ×ˢ s₁ ⊂ s₂ ×ˢ s₂ ↔ s₁ ⊂ s₂
  proof: and_congr prod_self_subset_prod_self not_congr prod_self_subset_prod_self

中文:
定理 prod_self_ssubset_prod_self
  结论: s₁ ×ˢ s₁ ⊂ s₂ ×ˢ s₂ ↔ s₁ ⊂ s₂
  证明: and_congr prod_self_subset_prod_self not_congr prod_self_subset_prod_self

Depends on / 依赖: and_congr, not_congr, prod_self_subset_prod_self
-/
theorem prod_self_ssubset_prod_self : s₁ ×ˢ s₁ ⊂ s₂ ×ˢ s₂ ↔ s₁ ⊂ s₂ :=
and_congr prod_self_subset_prod_self not_congr prod_self_subset_prod_self

/--
theorem `prod_subset_iff` / 定理 `prod_subset_iff`

English:
theorem prod_subset_iff
  given: {P : Set (α × β)}
  statement: s ×ˢ t subseteq P ↔ forall x in s, forall y in t, (x, y) in P
  proof: ⟨fun h _ hx _ hy => h (mk_mem_prod hx hy), fun h ⟨_, _⟩ hp => h _ hp.1 _ hp.2⟩

中文:
定理 prod_subset_iff
  条件: {P : Set (α × β)}
  结论: s ×ˢ t subseteq P ↔ 对任意 x in s, 对任意 y in t, (x, y) in P
  证明: ⟨fun h _ hx _ hy => h (mk_mem_prod hx hy), fun h ⟨_, _⟩ hp => h _ hp.1 _ hp.2⟩

Depends on / 依赖: mk_mem_prod
-/
theorem prod_subset_iff {P : Set (α × β)} : s ×ˢ t subseteq P ↔ forall x in s, forall y in t, (x, y) in P :=
  ⟨fun h _ hx _ hy => h (mk_mem_prod hx hy), fun h ⟨_, _⟩ hp => h _ hp.1 _ hp.2⟩

/--
theorem `forall_prod_set` / 定理 `forall_prod_set`

English:
theorem forall_prod_set
  given: {p : α × β -> Prop}
  statement: (forall x in s ×ˢ t, p x) ↔ forall x in s, forall y in t, p (x, y)
  proof: prod_subset_iff

中文:
定理 forall_prod_set
  条件: {p : α × β -> 命题}
  结论: (对任意 x in s ×ˢ t, p x) ↔ 对任意 x in s, 对任意 y in t, p (x, y)
  证明: prod_subset_iff

Depends on / 依赖: prod_subset_iff
-/
theorem forall_prod_set {p : α × β -> Prop} : (forall x in s ×ˢ t, p x) ↔ forall x in s, forall y in t, p (x, y) :=
  prod_subset_iff

/--
theorem `exists_prod_set` / 定理 `exists_prod_set`

English:
theorem exists_prod_set
  given: {p : α × β -> Prop}
  statement: (exists x in s ×ˢ t, p x) ↔ exists x in s, exists y in t, p (x, y)
  proof: by
  simp [and_assoc]

@[simp]

中文:
定理 exists_prod_set
  条件: {p : α × β -> 命题}
  结论: (存在 x in s ×ˢ t, p x) ↔ 存在 x in s, 存在 y in t, p (x, y)
  证明: by
  simp [and_assoc]

@[simp]

Depends on / 依赖: and_assoc
-/
theorem exists_prod_set {p : α × β -> Prop} : (exists x in s ×ˢ t, p x) ↔ exists x in s, exists y in t, p (x, y) := by
  simp [and_assoc]

@[simp]
/--
theorem `prod_empty` / 定理 `prod_empty`

English:
theorem prod_empty
  statement: s ×ˢ (∅ : Set β) = ∅
  proof: by
  ext
  exact iff_of_eq (and_false _)

@[simp]

中文:
定理 prod_empty
  结论: s ×ˢ (∅ : Set β) = ∅
  证明: by
  ext
  exact iff_of_eq (and_false _)

@[simp]

Depends on / 依赖: and_false, iff_of_eq
-/
theorem prod_empty : s ×ˢ (∅ : Set β) = ∅ := by
  ext
  exact iff_of_eq (and_false _)

@[simp]
/--
theorem `empty_prod` / 定理 `empty_prod`

English:
theorem empty_prod
  statement: (∅ : Set α) ×ˢ t = ∅
  proof: by
  ext
  exact iff_of_eq (false_and _)

@[simp, mfld_simps]

中文:
定理 empty_prod
  结论: (∅ : Set α) ×ˢ t = ∅
  证明: by
  ext
  exact iff_of_eq (false_and _)

@[simp, mfld_simps]

Depends on / 依赖: false_and, iff_of_eq
-/
theorem empty_prod : (∅ : Set α) ×ˢ t = ∅ := by
  ext
  exact iff_of_eq (false_and _)

@[simp, mfld_simps]
/--
theorem `univ_prod_univ` / 定理 `univ_prod_univ`

English:
theorem univ_prod_univ
  statement: @univ α ×ˢ @univ β = univ
  proof: by
  ext
  exact iff_of_eq (true_and _)

中文:
定理 univ_prod_univ
  结论: @univ α ×ˢ @univ β = univ
  证明: by
  ext
  exact iff_of_eq (true_and _)

Depends on / 依赖: iff_of_eq, true_and
-/
theorem univ_prod_univ : @univ α ×ˢ @univ β = univ := by
  ext
  exact iff_of_eq (true_and _)

/--
theorem `univ_prod` / 定理 `univ_prod`

English:
theorem univ_prod
  given: {t : Set β}
  statement: (univ : Set α) ×ˢ t = Prod.snd ⁻¹' t
  proof: by simp [prod_eq]

中文:
定理 univ_prod
  条件: {t : Set β}
  结论: (univ : Set α) ×ˢ t = Prod.snd ⁻¹' t
  证明: by simp [prod_eq]

Depends on / 依赖: prod_eq
-/
theorem univ_prod {t : Set β} : (univ : Set α) ×ˢ t = Prod.snd ⁻¹' t := by simp [prod_eq]

/--
theorem `prod_univ` / 定理 `prod_univ`

English:
theorem prod_univ
  given: {s : Set α}
  statement: s ×ˢ (univ : Set β) = Prod.fst ⁻¹' s
  proof: by simp [prod_eq]

中文:
定理 prod_univ
  条件: {s : Set α}
  结论: s ×ˢ (univ : Set β) = Prod.fst ⁻¹' s
  证明: by simp [prod_eq]

Depends on / 依赖: prod_eq
-/
theorem prod_univ {s : Set α} : s ×ˢ (univ : Set β) = Prod.fst ⁻¹' s := by simp [prod_eq]

/--
lemma `prod_eq_univ` / 引理 `prod_eq_univ`

English:
lemma prod_eq_univ
  given: [Nonempty α] [Nonempty β]
  statement: s ×ˢ t = univ ↔ s = univ ∧ t = univ
  proof: by
  simp [eq_univ_iff_forall, forall_and]

中文:
引理 prod_eq_univ
  条件: [Nonempty α] [Nonempty β]
  结论: s ×ˢ t = univ ↔ s = univ ∧ t = univ
  证明: by
  simp [eq_univ_iff_forall, forall_and]
-/
@[simp] lemma prod_eq_univ [Nonempty α] [Nonempty β] : s ×ˢ t = univ ↔ s = univ ∧ t = univ := by
  simp [eq_univ_iff_forall, forall_and]

/--
theorem `singleton_prod` / 定理 `singleton_prod`

English:
theorem singleton_prod
  statement: ({a} : Set α) ×ˢ t = Prod.mk a '' t
  proof: by
  ext ⟨x, y⟩
  simp [and_left_comm, eq_comm]

中文:
定理 singleton_prod
  结论: ({a} : Set α) ×ˢ t = Prod.mk a '' t
  证明: by
  ext ⟨x, y⟩
  simp [and_left_comm, eq_comm]

Depends on / 依赖: and_left_comm, eq_comm
-/
theorem singleton_prod : ({a} : Set α) ×ˢ t = Prod.mk a '' t := by
  ext ⟨x, y⟩
  simp [and_left_comm, eq_comm]

/--
theorem `prod_singleton` / 定理 `prod_singleton`

English:
theorem prod_singleton
  statement: s ×ˢ ({b} : Set β) = (fun a => (a, b)) '' s
  proof: by
  ext ⟨x, y⟩
  simp [and_left_comm, eq_comm]

@[simp]

中文:
定理 prod_singleton
  结论: s ×ˢ ({b} : Set β) = (fun a => (a, b)) '' s
  证明: by
  ext ⟨x, y⟩
  simp [and_left_comm, eq_comm]

@[simp]

Depends on / 依赖: and_left_comm, eq_comm
-/
theorem prod_singleton : s ×ˢ ({b} : Set β) = (fun a => (a, b)) '' s := by
  ext ⟨x, y⟩
  simp [and_left_comm, eq_comm]

@[simp]
/--
theorem `singleton_prod_singleton` / 定理 `singleton_prod_singleton`

English:
theorem singleton_prod_singleton
  statement: ({a} : Set α) ×ˢ ({b} : Set β) = {(a, b)}
  proof: by ext ⟨c, d⟩; simp

@[simp]

中文:
定理 singleton_prod_singleton
  结论: ({a} : Set α) ×ˢ ({b} : Set β) = {(a, b)}
  证明: by ext ⟨c, d⟩; simp

@[simp]
-/
theorem singleton_prod_singleton : ({a} : Set α) ×ˢ ({b} : Set β) = {(a, b)} := by ext ⟨c, d⟩; simp

@[simp]
/--
theorem `union_prod` / 定理 `union_prod`

English:
theorem union_prod
  statement: (s₁ union s₂) ×ˢ t = s₁ ×ˢ t union s₂ ×ˢ t
  proof: by
  ext ⟨x, y⟩
  simp [or_and_right]

@[simp]

中文:
定理 union_prod
  结论: (s₁ union s₂) ×ˢ t = s₁ ×ˢ t union s₂ ×ˢ t
  证明: by
  ext ⟨x, y⟩
  simp [or_and_right]

@[simp]

Depends on / 依赖: or_and_right
-/
theorem union_prod : (s₁ union s₂) ×ˢ t = s₁ ×ˢ t union s₂ ×ˢ t := by
  ext ⟨x, y⟩
  simp [or_and_right]

@[simp]
/--
theorem `prod_union` / 定理 `prod_union`

English:
theorem prod_union
  statement: s ×ˢ (t₁ union t₂) = s ×ˢ t₁ union s ×ˢ t₂
  proof: by
  ext ⟨x, y⟩
  simp [and_or_left]

中文:
定理 prod_union
  结论: s ×ˢ (t₁ union t₂) = s ×ˢ t₁ union s ×ˢ t₂
  证明: by
  ext ⟨x, y⟩
  simp [and_or_left]

Depends on / 依赖: and_or_left
-/
theorem prod_union : s ×ˢ (t₁ union t₂) = s ×ˢ t₁ union s ×ˢ t₂ := by
  ext ⟨x, y⟩
  simp [and_or_left]

/--
theorem `inter_prod` / 定理 `inter_prod`

English:
theorem inter_prod
  statement: (s₁ inter s₂) ×ˢ t = s₁ ×ˢ t inter s₂ ×ˢ t
  proof: by
  ext ⟨x, y⟩
  simp only [← and_and_right, mem_inter_iff, mem_prod]

中文:
定理 inter_prod
  结论: (s₁ inter s₂) ×ˢ t = s₁ ×ˢ t inter s₂ ×ˢ t
  证明: by
  ext ⟨x, y⟩
  simp only [← and_and_right, mem_inter_iff, mem_prod]

Depends on / 依赖: and_and_right, mem_inter_iff, mem_prod
-/
theorem inter_prod : (s₁ inter s₂) ×ˢ t = s₁ ×ˢ t inter s₂ ×ˢ t := by
  ext ⟨x, y⟩
  simp only [← and_and_right, mem_inter_iff, mem_prod]

/--
theorem `prod_inter` / 定理 `prod_inter`

English:
theorem prod_inter
  statement: s ×ˢ (t₁ inter t₂) = s ×ˢ t₁ inter s ×ˢ t₂
  proof: by
  ext ⟨x, y⟩
  simp only [← and_and_left, mem_inter_iff, mem_prod]

@[mfld_simps]

中文:
定理 prod_inter
  结论: s ×ˢ (t₁ inter t₂) = s ×ˢ t₁ inter s ×ˢ t₂
  证明: by
  ext ⟨x, y⟩
  simp only [← and_and_left, mem_inter_iff, mem_prod]

@[mfld_simps]

Depends on / 依赖: and_and_left, mem_inter_iff, mem_prod
-/
theorem prod_inter : s ×ˢ (t₁ inter t₂) = s ×ˢ t₁ inter s ×ˢ t₂ := by
  ext ⟨x, y⟩
  simp only [← and_and_left, mem_inter_iff, mem_prod]

@[mfld_simps]
/--
theorem `prod_inter_prod` / 定理 `prod_inter_prod`

English:
theorem prod_inter_prod
  statement: s₁ ×ˢ t₁ inter s₂ ×ˢ t₂ = (s₁ inter s₂) ×ˢ (t₁ inter t₂)
  proof: by
  ext ⟨x, y⟩
  simp [and_assoc, and_left_comm]

中文:
定理 prod_inter_prod
  结论: s₁ ×ˢ t₁ inter s₂ ×ˢ t₂ = (s₁ inter s₂) ×ˢ (t₁ inter t₂)
  证明: by
  ext ⟨x, y⟩
  simp [and_assoc, and_left_comm]

Depends on / 依赖: and_assoc, and_left_comm
-/
theorem prod_inter_prod : s₁ ×ˢ t₁ inter s₂ ×ˢ t₂ = (s₁ inter s₂) ×ˢ (t₁ inter t₂) := by
  ext ⟨x, y⟩
  simp [and_assoc, and_left_comm]

/--
lemma `compl_prod_eq_union` / 引理 `compl_prod_eq_union`

English:
lemma compl_prod_eq_union
  given: {α β : Type*} (s : Set α) (t : Set β)
  proof: by
  grind

@[simp]

中文:
引理 compl_prod_eq_union
  条件: {α β : 类型} (s : Set α) (t : Set β)
  证明: by
  grind

@[simp]
-/
lemma compl_prod_eq_union {α β : Type*} (s : Set α) (t : Set β) :
    (s ×ˢ t)ᶜ = (sᶜ ×ˢ univ) union (univ ×ˢ tᶜ) := by
  grind

@[simp]
/--
theorem `disjoint_prod` / 定理 `disjoint_prod`

English:
theorem disjoint_prod
  statement: Disjoint (s₁ ×ˢ t₁) (s₂ ×ˢ t₂) ↔ Disjoint s₁ s₂ ∨ Disjoint t₁ t₂
  proof: by
  simp_rw [disjoint_left, mem_prod, Prod.forall]
  grind

中文:
定理 disjoint_prod
  结论: Disjoint (s₁ ×ˢ t₁) (s₂ ×ˢ t₂) ↔ Disjoint s₁ s₂ ∨ Disjoint t₁ t₂
  证明: by
  simp_rw [disjoint_left, mem_prod, Prod.forall]
  grind

Depends on / 依赖: Prod.forall, disjoint_left, mem_prod, simp_rw
-/
theorem disjoint_prod : Disjoint (s₁ ×ˢ t₁) (s₂ ×ˢ t₂) ↔ Disjoint s₁ s₂ ∨ Disjoint t₁ t₂ := by
  simp_rw [disjoint_left, mem_prod, Prod.forall]
  grind

/--
theorem `Disjoint.set_prod_left` / 定理 `Disjoint.set_prod_left`

English:
theorem Disjoint.set_prod_left
  given: (hs : Disjoint s₁ s₂) (t₁ t₂ : Set β)
  proof: disjoint_left.2 fun ⟨_a, _b⟩ ⟨ha₁, _⟩ ⟨ha₂, _⟩ => disjoint_left.1 hs ha₁ ha₂

中文:
定理 Disjoint.set_prod_left
  条件: (hs : Disjoint s₁ s₂) (t₁ t₂ : Set β)
  证明: disjoint_left.2 fun ⟨_a, _b⟩ ⟨ha₁, _⟩ ⟨ha₂, _⟩ => disjoint_left.1 hs ha₁ ha₂

Depends on / 依赖: disjoint_left
-/
theorem Disjoint.set_prod_left (hs : Disjoint s₁ s₂) (t₁ t₂ : Set β) :
    Disjoint (s₁ ×ˢ t₁) (s₂ ×ˢ t₂) :=
  disjoint_left.2 fun ⟨_a, _b⟩ ⟨ha₁, _⟩ ⟨ha₂, _⟩ => disjoint_left.1 hs ha₁ ha₂

/--
theorem `Disjoint.set_prod_right` / 定理 `Disjoint.set_prod_right`

English:
theorem Disjoint.set_prod_right
  given: (ht : Disjoint t₁ t₂) (s₁ s₂ : Set α)
  proof: disjoint_left.2 fun ⟨_a, _b⟩ ⟨_, hb₁⟩ ⟨_, hb₂⟩ => disjoint_left.1 ht hb₁ hb₂

中文:
定理 Disjoint.set_prod_right
  条件: (ht : Disjoint t₁ t₂) (s₁ s₂ : Set α)
  证明: disjoint_left.2 fun ⟨_a, _b⟩ ⟨_, hb₁⟩ ⟨_, hb₂⟩ => disjoint_left.1 ht hb₁ hb₂

Depends on / 依赖: WithZero, WithZero.denselyOrdered_iff.mpr, denselyOrdered_iff, disjoint_left
-/
theorem Disjoint.set_prod_right (ht : Disjoint t₁ t₂) (s₁ s₂ : Set α) :
    Disjoint (s₁ ×ˢ t₁) (s₂ ×ˢ t₂) :=
  disjoint_left.2 fun ⟨_a, _b⟩ ⟨_, hb₁⟩ ⟨_, hb₂⟩ => disjoint_left.1 ht hb₁ hb₂

/--
theorem `prodMap_image_prod` / 定理 `prodMap_image_prod`

English:
theorem prodMap_image_prod
  given: (f : α -> β) (g : γ -> δ) (s : Set α) (t : Set γ)
  proof: by
  ext
  aesop

中文:
定理 prodMap_image_prod
  条件: (f : α -> β) (g : γ -> δ) (s : Set α) (t : Set γ)
  证明: by
  ext
  aesop
-/
theorem prodMap_image_prod (f : α -> β) (g : γ -> δ) (s : Set α) (t : Set γ) :
    (Prod.map f g) '' (s ×ˢ t) = (f '' s) ×ˢ (g '' t) := by
  ext
  aesop

/--
theorem `insert_prod` / 定理 `insert_prod`

English:
theorem insert_prod
  statement: insert a s ×ˢ t = Prod.mk a '' t union s ×ˢ t
  proof: by
  simp only [insert_eq, union_prod, singleton_prod]

中文:
定理 insert_prod
  结论: insert a s ×ˢ t = Prod.mk a '' t union s ×ˢ t
  证明: by
  simp only [insert_eq, union_prod, singleton_prod]

Depends on / 依赖: insert_eq, singleton_prod, union_prod
-/
theorem insert_prod : insert a s ×ˢ t = Prod.mk a '' t union s ×ˢ t := by
  simp only [insert_eq, union_prod, singleton_prod]

/--
theorem `prod_insert` / 定理 `prod_insert`

English:
theorem prod_insert
  statement: s ×ˢ insert b t = (fun a => (a, b)) '' s union s ×ˢ t
  proof: by
  simp only [insert_eq, prod_union, prod_singleton]

中文:
定理 prod_insert
  结论: s ×ˢ insert b t = (fun a => (a, b)) '' s union s ×ˢ t
  证明: by
  simp only [insert_eq, prod_union, prod_singleton]

Depends on / 依赖: insert_eq, prod_singleton, prod_union
-/
theorem prod_insert : s ×ˢ insert b t = (fun a => (a, b)) '' s union s ×ˢ t := by
  simp only [insert_eq, prod_union, prod_singleton]

/--
theorem `prod_preimage_eq` / 定理 `prod_preimage_eq`

English:
theorem prod_preimage_eq
  given: {f : γ -> α} {g : δ -> β}
  proof: rfl

中文:
定理 prod_preimage_eq
  条件: {f : γ -> α} {g : δ -> β}
  证明: rfl
-/
theorem prod_preimage_eq {f : γ -> α} {g : δ -> β} :
    (f ⁻¹' s) ×ˢ (g ⁻¹' t) = (fun p : γ × δ => (f p.1, g p.2)) ⁻¹' s ×ˢ t :=
  rfl

/--
theorem `prod_preimage_left` / 定理 `prod_preimage_left`

English:
theorem prod_preimage_left
  given: {f : γ -> α}
  proof: rfl

中文:
定理 prod_preimage_left
  条件: {f : γ -> α}
  证明: rfl
-/
theorem prod_preimage_left {f : γ -> α} :
    (f ⁻¹' s) ×ˢ t = (fun p : γ × β => (f p.1, p.2)) ⁻¹' s ×ˢ t :=
  rfl

/--
theorem `prod_preimage_right` / 定理 `prod_preimage_right`

English:
theorem prod_preimage_right
  given: {g : δ -> β}
  proof: rfl

中文:
定理 prod_preimage_right
  条件: {g : δ -> β}
  证明: rfl
-/
theorem prod_preimage_right {g : δ -> β} :
    s ×ˢ (g ⁻¹' t) = (fun p : α × δ => (p.1, g p.2)) ⁻¹' s ×ˢ t :=
  rfl

/--
theorem `preimage_prod_map_prod` / 定理 `preimage_prod_map_prod`

English:
theorem preimage_prod_map_prod
  given: (f : α -> β) (g : γ -> δ) (s : Set β) (t : Set δ)
  proof: rfl

中文:
定理 preimage_prod_map_prod
  条件: (f : α -> β) (g : γ -> δ) (s : Set β) (t : Set δ)
  证明: rfl
-/
theorem preimage_prod_map_prod (f : α -> β) (g : γ -> δ) (s : Set β) (t : Set δ) :
    Prod.map f g ⁻¹' s ×ˢ t = (f ⁻¹' s) ×ˢ (g ⁻¹' t) :=
  rfl

/--
theorem `mk_preimage_prod` / 定理 `mk_preimage_prod`

English:
theorem mk_preimage_prod
  given: (f : γ -> α) (g : γ -> β)
  proof: rfl

@[simp]

中文:
定理 mk_preimage_prod
  条件: (f : γ -> α) (g : γ -> β)
  证明: rfl

@[simp]
-/
theorem mk_preimage_prod (f : γ -> α) (g : γ -> β) :
    (fun x => (f x, g x)) ⁻¹' s ×ˢ t = f ⁻¹' s inter g ⁻¹' t :=
  rfl

@[simp]
/--
theorem `mk_preimage_prod_left` / 定理 `mk_preimage_prod_left`

English:
theorem mk_preimage_prod_left
  given: (hb : b in t)
  statement: (fun a => (a, b)) ⁻¹' s ×ˢ t = s
  proof: by grind

@[simp]

中文:
定理 mk_preimage_prod_left
  条件: (hb : b in t)
  结论: (fun a => (a, b)) ⁻¹' s ×ˢ t = s
  证明: by grind

@[simp]
-/
theorem mk_preimage_prod_left (hb : b in t) : (fun a => (a, b)) ⁻¹' s ×ˢ t = s := by grind

@[simp]
/--
theorem `mk_preimage_prod_right` / 定理 `mk_preimage_prod_right`

English:
theorem mk_preimage_prod_right
  given: (ha : a in s)
  statement: Prod.mk a ⁻¹' s ×ˢ t = t
  proof: by grind

@[simp]

中文:
定理 mk_preimage_prod_right
  条件: (ha : a in s)
  结论: Prod.mk a ⁻¹' s ×ˢ t = t
  证明: by grind

@[simp]
-/
theorem mk_preimage_prod_right (ha : a in s) : Prod.mk a ⁻¹' s ×ˢ t = t := by grind

@[simp]
/--
theorem `mk_preimage_prod_left_eq_empty` / 定理 `mk_preimage_prod_left_eq_empty`

English:
theorem mk_preimage_prod_left_eq_empty
  given: (hb : b ∉ t)
  statement: (fun a => (a, b)) ⁻¹' s ×ˢ t = ∅
  proof: by grind

@[simp]

中文:
定理 mk_preimage_prod_left_eq_empty
  条件: (hb : b ∉ t)
  结论: (fun a => (a, b)) ⁻¹' s ×ˢ t = ∅
  证明: by grind

@[simp]
-/
theorem mk_preimage_prod_left_eq_empty (hb : b ∉ t) : (fun a => (a, b)) ⁻¹' s ×ˢ t = ∅ := by grind

@[simp]
/--
theorem `mk_preimage_prod_right_eq_empty` / 定理 `mk_preimage_prod_right_eq_empty`

English:
theorem mk_preimage_prod_right_eq_empty
  given: (ha : a ∉ s)
  statement: Prod.mk a ⁻¹' s ×ˢ t = ∅
  proof: by grind

中文:
定理 mk_preimage_prod_right_eq_empty
  条件: (ha : a ∉ s)
  结论: Prod.mk a ⁻¹' s ×ˢ t = ∅
  证明: by grind
-/
theorem mk_preimage_prod_right_eq_empty (ha : a ∉ s) : Prod.mk a ⁻¹' s ×ˢ t = ∅ := by grind

/--
theorem `mk_preimage_prod_left_eq_if` / 定理 `mk_preimage_prod_left_eq_if`

English:
theorem mk_preimage_prod_left_eq_if
  given: [DecidablePred (· in t)]
  proof: by grind

中文:
定理 mk_preimage_prod_left_eq_if
  条件: [DecidablePred (· in t)]
  证明: by grind
-/
theorem mk_preimage_prod_left_eq_if [DecidablePred (· in t)] :
    (fun a => (a, b)) ⁻¹' s ×ˢ t = if b in t then s else ∅ := by grind

/--
theorem `mk_preimage_prod_right_eq_if` / 定理 `mk_preimage_prod_right_eq_if`

English:
theorem mk_preimage_prod_right_eq_if
  given: [DecidablePred (· in s)]
  proof: by grind

中文:
定理 mk_preimage_prod_right_eq_if
  条件: [DecidablePred (· in s)]
  证明: by grind
-/
theorem mk_preimage_prod_right_eq_if [DecidablePred (· in s)] :
    Prod.mk a ⁻¹' s ×ˢ t = if a in s then t else ∅ := by grind

/--
theorem `mk_preimage_prod_left_fn_eq_if` / 定理 `mk_preimage_prod_left_fn_eq_if`

English:
theorem mk_preimage_prod_left_fn_eq_if
  given: [DecidablePred (· in t)] (f : γ -> α)
  proof: by grind

中文:
定理 mk_preimage_prod_left_fn_eq_if
  条件: [DecidablePred (· in t)] (f : γ -> α)
  证明: by grind
-/
theorem mk_preimage_prod_left_fn_eq_if [DecidablePred (· in t)] (f : γ -> α) :
    (fun a => (f a, b)) ⁻¹' s ×ˢ t = if b in t then f ⁻¹' s else ∅ := by grind

/--
theorem `mk_preimage_prod_right_fn_eq_if` / 定理 `mk_preimage_prod_right_fn_eq_if`

English:
theorem mk_preimage_prod_right_fn_eq_if
  given: [DecidablePred (· in s)] (g : δ -> β)
  proof: by grind

@[simp]

中文:
定理 mk_preimage_prod_right_fn_eq_if
  条件: [DecidablePred (· in s)] (g : δ -> β)
  证明: by grind

@[simp]
-/
theorem mk_preimage_prod_right_fn_eq_if [DecidablePred (· in s)] (g : δ -> β) :
    (fun b => (a, g b)) ⁻¹' s ×ˢ t = if a in s then g ⁻¹' t else ∅ := by grind

@[simp]
/--
theorem `preimage_swap_prod` / 定理 `preimage_swap_prod`

English:
theorem preimage_swap_prod
  given: (s : Set α) (t : Set β)
  statement: Prod.swap ⁻¹' s ×ˢ t = t ×ˢ s
  proof: by grind

@[simp]

中文:
定理 preimage_swap_prod
  条件: (s : Set α) (t : Set β)
  结论: Prod.swap ⁻¹' s ×ˢ t = t ×ˢ s
  证明: by grind

@[simp]
-/
theorem preimage_swap_prod (s : Set α) (t : Set β) : Prod.swap ⁻¹' s ×ˢ t = t ×ˢ s := by grind

@[simp]
/--
theorem `image_swap_prod` / 定理 `image_swap_prod`

English:
theorem image_swap_prod
  given: (s : Set α) (t : Set β)
  statement: Prod.swap '' s ×ˢ t = t ×ˢ s
  proof: by
  rw [image_swap_eq_preimage_swap]; rw [preimage_swap_prod]

中文:
定理 image_swap_prod
  条件: (s : Set α) (t : Set β)
  结论: Prod.swap '' s ×ˢ t = t ×ˢ s
  证明: by
  rw [image_swap_eq_preimage_swap]; rw [preimage_swap_prod]

Depends on / 依赖: image_swap_eq_preimage_swap, preimage_swap_prod
-/
theorem image_swap_prod (s : Set α) (t : Set β) : Prod.swap '' s ×ˢ t = t ×ˢ s := by
  rw [image_swap_eq_preimage_swap]; rw [preimage_swap_prod]

/--
theorem `mapsTo_swap_prod` / 定理 `mapsTo_swap_prod`

English:
theorem mapsTo_swap_prod
  given: (s : Set α) (t : Set β)
  statement: MapsTo Prod.swap (s ×ˢ t) (t ×ˢ s)
  proof: fun _ ⟨hx, hy⟩ => ⟨hy, hx⟩

中文:
定理 mapsTo_swap_prod
  条件: (s : Set α) (t : Set β)
  结论: MapsTo Prod.swap (s ×ˢ t) (t ×ˢ s)
  证明: fun _ ⟨hx, hy⟩ => ⟨hy, hx⟩

Depends on / 依赖: Iff.rfl
-/
theorem mapsTo_swap_prod (s : Set α) (t : Set β) : MapsTo Prod.swap (s ×ˢ t) (t ×ˢ s) :=
  fun _ ⟨hx, hy⟩ => ⟨hy, hx⟩

/--
theorem `prod_image_image_eq` / 定理 `prod_image_image_eq`

English:
theorem prod_image_image_eq
  given: {m₁ : α -> γ} {m₂ : β -> δ}
  proof: ext by
    simp [-exists_and_right, exists_and_right.symm, and_left_comm, and_assoc, and_comm]

中文:
定理 prod_image_image_eq
  条件: {m₁ : α -> γ} {m₂ : β -> δ}
  证明: ext by
    simp [-exists_and_right, exists_and_right.symm, and_left_comm, and_assoc, and_comm]

Depends on / 依赖: and_assoc, and_comm, and_left_comm, exists_and_right, exists_and_right.symm
-/
theorem prod_image_image_eq {m₁ : α -> γ} {m₂ : β -> δ} :
    (m₁ '' s) ×ˢ (m₂ '' t) = (fun p : α × β => (m₁ p.1, m₂ p.2)) '' s ×ˢ t :=
ext by
    simp [-exists_and_right, exists_and_right.symm, and_left_comm, and_assoc, and_comm]

/--
theorem `prod_range_range_eq` / 定理 `prod_range_range_eq`

English:
theorem prod_range_range_eq
  given: {m₁ : α -> γ} {m₂ : β -> δ}
  proof: ext by simp [range]

@[simp, mfld_simps]

中文:
定理 prod_range_range_eq
  条件: {m₁ : α -> γ} {m₂ : β -> δ}
  证明: ext by simp [range]

@[simp, mfld_simps]
-/
theorem prod_range_range_eq {m₁ : α -> γ} {m₂ : β -> δ} :
    range m₁ ×ˢ range m₂ = range fun p : α × β => (m₁ p.1, m₂ p.2) :=
ext by simp [range]

@[simp, mfld_simps]
/--
theorem `range_prodMap` / 定理 `range_prodMap`

English:
theorem range_prodMap
  given: {m₁ : α -> γ} {m₂ : β -> δ}
  statement: range (Prod.map m₁ m₂) = range m₁ ×ˢ range m₂
  proof: prod_range_range_eq.symm

中文:
定理 range_prodMap
  条件: {m₁ : α -> γ} {m₂ : β -> δ}
  结论: range (Prod.map m₁ m₂) = range m₁ ×ˢ range m₂
  证明: prod_range_range_eq.symm

Depends on / 依赖: prod_range_range_eq, prod_range_range_eq.symm
-/
theorem range_prodMap {m₁ : α -> γ} {m₂ : β -> δ} : range (Prod.map m₁ m₂) = range m₁ ×ˢ range m₂ :=
  prod_range_range_eq.symm

/--
theorem `prod_range_univ_eq` / 定理 `prod_range_univ_eq`

English:
theorem prod_range_univ_eq
  given: {m₁ : α -> γ}
  proof: ext by simp [range]

中文:
定理 prod_range_univ_eq
  条件: {m₁ : α -> γ}
  证明: ext by simp [range]
-/
theorem prod_range_univ_eq {m₁ : α -> γ} :
    range m₁ ×ˢ (univ : Set β) = range fun p : α × β => (m₁ p.1, p.2) :=
ext by simp [range]

/--
theorem `prod_univ_range_eq` / 定理 `prod_univ_range_eq`

English:
theorem prod_univ_range_eq
  given: {m₂ : β -> δ}
  proof: ext by simp [range]

中文:
定理 prod_univ_range_eq
  条件: {m₂ : β -> δ}
  证明: ext by simp [range]
-/
theorem prod_univ_range_eq {m₂ : β -> δ} :
    (univ : Set α) ×ˢ range m₂ = range fun p : α × β => (p.1, m₂ p.2) :=
ext by simp [range]

/--
theorem `range_pair_subset` / 定理 `range_pair_subset`

English:
theorem range_pair_subset
  given: (f : α -> β) (g : α -> γ)
  proof: by grind

中文:
定理 range_pair_subset
  条件: (f : α -> β) (g : α -> γ)
  证明: by grind
-/
theorem range_pair_subset (f : α -> β) (g : α -> γ) :
    (range fun x => (f x, g x)) subseteq range f ×ˢ range g := by grind

/--
theorem `Nonempty.prod` / 定理 `Nonempty.prod`

English:
theorem Nonempty.prod
  statement: s.Nonempty -> t.Nonempty -> (s ×ˢ t).Nonempty
  proof: fun ⟨x, hx⟩ ⟨y, hy⟩ =>
  ⟨(x, y), ⟨hx, hy⟩⟩

中文:
定理 Nonempty.prod
  结论: s.Nonempty -> t.Nonempty -> (s ×ˢ t).Nonempty
  证明: fun ⟨x, hx⟩ ⟨y, hy⟩ =>
  ⟨(x, y), ⟨hx, hy⟩⟩
-/
theorem Nonempty.prod : s.Nonempty -> t.Nonempty -> (s ×ˢ t).Nonempty := fun ⟨x, hx⟩ ⟨y, hy⟩ =>
  ⟨(x, y), ⟨hx, hy⟩⟩

/--
theorem `Nonempty.fst` / 定理 `Nonempty.fst`

English:
theorem Nonempty.fst
  statement: (s ×ˢ t).Nonempty -> s.Nonempty
  proof: fun ⟨x, hx⟩ => ⟨x.1, hx.1⟩

中文:
定理 Nonempty.fst
  结论: (s ×ˢ t).Nonempty -> s.Nonempty
  证明: fun ⟨x, hx⟩ => ⟨x.1, hx.1⟩
-/
theorem Nonempty.fst : (s ×ˢ t).Nonempty -> s.Nonempty := fun ⟨x, hx⟩ => ⟨x.1, hx.1⟩

/--
theorem `Nonempty.snd` / 定理 `Nonempty.snd`

English:
theorem Nonempty.snd
  statement: (s ×ˢ t).Nonempty -> t.Nonempty
  proof: fun ⟨x, hx⟩ => ⟨x.2, hx.2⟩

@[simp]

中文:
定理 Nonempty.snd
  结论: (s ×ˢ t).Nonempty -> t.Nonempty
  证明: fun ⟨x, hx⟩ => ⟨x.2, hx.2⟩

@[simp]
-/
theorem Nonempty.snd : (s ×ˢ t).Nonempty -> t.Nonempty := fun ⟨x, hx⟩ => ⟨x.2, hx.2⟩

@[simp]
/--
theorem `prod_nonempty_iff` / 定理 `prod_nonempty_iff`

English:
theorem prod_nonempty_iff
  statement: (s ×ˢ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty
  proof: ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.1.prod h.2⟩

@[simp]

中文:
定理 prod_nonempty_iff
  结论: (s ×ˢ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty
  证明: ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.1.prod h.2⟩

@[simp]

Depends on / 依赖: h.fst, h.snd
-/
theorem prod_nonempty_iff : (s ×ˢ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.1.prod h.2⟩

@[simp]
/--
theorem `prod_eq_empty_iff` / 定理 `prod_eq_empty_iff`

English:
theorem prod_eq_empty_iff
  statement: s ×ˢ t = ∅ ↔ s = ∅ ∨ t = ∅
  proof: by
  simp only [not_nonempty_iff_eq_empty.symm, prod_nonempty_iff, not_and_or]

中文:
定理 prod_eq_empty_iff
  结论: s ×ˢ t = ∅ ↔ s = ∅ ∨ t = ∅
  证明: by
  simp only [not_nonempty_iff_eq_empty.symm, prod_nonempty_iff, not_and_or]

Depends on / 依赖: not_and_or, not_nonempty_iff_eq_empty, not_nonempty_iff_eq_empty.symm, prod_nonempty_iff
-/
theorem prod_eq_empty_iff : s ×ˢ t = ∅ ↔ s = ∅ ∨ t = ∅ := by
  simp only [not_nonempty_iff_eq_empty.symm, prod_nonempty_iff, not_and_or]

/--
theorem `prod_sub_preimage_iff` / 定理 `prod_sub_preimage_iff`

English:
theorem prod_sub_preimage_iff
  given: {W : Set γ} {f : α × β -> γ}
  proof: by simp [subset_def]

中文:
定理 prod_sub_preimage_iff
  条件: {W : Set γ} {f : α × β -> γ}
  证明: by simp [subset_def]

Depends on / 依赖: subset_def
-/
theorem prod_sub_preimage_iff {W : Set γ} {f : α × β -> γ} :
    s ×ˢ t subseteq f ⁻¹' W ↔ forall a b, a in s -> b in t -> f (a, b) in W := by simp [subset_def]

/--
theorem `image_prodMk_subset_prod` / 定理 `image_prodMk_subset_prod`

English:
theorem image_prodMk_subset_prod
  given: {f : α -> β} {g : α -> γ} {s : Set α}
  proof: by grind

中文:
定理 image_prodMk_subset_prod
  条件: {f : α -> β} {g : α -> γ} {s : Set α}
  证明: by grind
-/
theorem image_prodMk_subset_prod {f : α -> β} {g : α -> γ} {s : Set α} :
    (fun x => (f x, g x)) '' s subseteq (f '' s) ×ˢ (g '' s) := by grind

/--
theorem `image_prodMk_subset_prod_left` / 定理 `image_prodMk_subset_prod_left`

English:
theorem image_prodMk_subset_prod_left
  given: (hb : b in t)
  statement: (fun a => (a, b)) '' s subseteq s ×ˢ t
  proof: by grind

中文:
定理 image_prodMk_subset_prod_left
  条件: (hb : b in t)
  结论: (fun a => (a, b)) '' s subseteq s ×ˢ t
  证明: by grind
-/
theorem image_prodMk_subset_prod_left (hb : b in t) : (fun a => (a, b)) '' s subseteq s ×ˢ t := by grind

/--
theorem `image_prodMk_subset_prod_right` / 定理 `image_prodMk_subset_prod_right`

English:
theorem image_prodMk_subset_prod_right
  given: (ha : a in s)
  statement: Prod.mk a '' t subseteq s ×ˢ t
  proof: by grind

中文:
定理 image_prodMk_subset_prod_right
  条件: (ha : a in s)
  结论: Prod.mk a '' t subseteq s ×ˢ t
  证明: by grind
-/
theorem image_prodMk_subset_prod_right (ha : a in s) : Prod.mk a '' t subseteq s ×ˢ t := by grind

/--
theorem `prod_subset_preimage_fst` / 定理 `prod_subset_preimage_fst`

English:
theorem prod_subset_preimage_fst
  given: (s : Set α) (t : Set β)
  statement: s ×ˢ t subseteq Prod.fst ⁻¹' s
  proof: inter_subset_left

中文:
定理 prod_subset_preimage_fst
  条件: (s : Set α) (t : Set β)
  结论: s ×ˢ t subseteq Prod.fst ⁻¹' s
  证明: inter_subset_left

Depends on / 依赖: inter_subset_left
-/
theorem prod_subset_preimage_fst (s : Set α) (t : Set β) : s ×ˢ t subseteq Prod.fst ⁻¹' s :=
  inter_subset_left

/--
theorem `fst_image_prod_subset` / 定理 `fst_image_prod_subset`

English:
theorem fst_image_prod_subset
  given: (s : Set α) (t : Set β)
  statement: Prod.fst '' s ×ˢ t subseteq s
  proof: image_subset_iff.2 prod_subset_preimage_fst s t

中文:
定理 fst_image_prod_subset
  条件: (s : Set α) (t : Set β)
  结论: Prod.fst '' s ×ˢ t subseteq s
  证明: image_subset_iff.2 prod_subset_preimage_fst s t

Depends on / 依赖: image_subset_iff, prod_subset_preimage_fst
-/
theorem fst_image_prod_subset (s : Set α) (t : Set β) : Prod.fst '' s ×ˢ t subseteq s :=
image_subset_iff.2 prod_subset_preimage_fst s t

/--
theorem `fst_image_prod` / 定理 `fst_image_prod`

English:
theorem fst_image_prod
  given: (s : Set β) {t : Set α} (ht : t.Nonempty)
  statement: Prod.fst '' s ×ˢ t = s
  proof: (fst_image_prod_subset _ _).antisymm fun y hy =>
    let ⟨x, hx⟩ := ht
    ⟨(y, x), ⟨hy, hx⟩, rfl⟩

中文:
定理 fst_image_prod
  条件: (s : Set β) {t : Set α} (ht : t.Nonempty)
  结论: Prod.fst '' s ×ˢ t = s
  证明: (fst_image_prod_subset _ _).antisymm fun y hy =>
    let ⟨x, hx⟩ := ht
    ⟨(y, x), ⟨hy, hx⟩, rfl⟩

Depends on / 依赖: antisymm, fst_image_prod_subset
-/
theorem fst_image_prod (s : Set β) {t : Set α} (ht : t.Nonempty) : Prod.fst '' s ×ˢ t = s :=
  (fst_image_prod_subset _ _).antisymm fun y hy =>
    let ⟨x, hx⟩ := ht
    ⟨(y, x), ⟨hy, hx⟩, rfl⟩

/--
lemma `mapsTo_fst_prod` / 引理 `mapsTo_fst_prod`

English:
lemma mapsTo_fst_prod
  given: {s : Set α} {t : Set β}
  statement: MapsTo Prod.fst (s ×ˢ t) s
  proof: fun _ hx => (mem_prod.1 hx).1

中文:
引理 mapsTo_fst_prod
  条件: {s : Set α} {t : Set β}
  结论: MapsTo Prod.fst (s ×ˢ t) s
  证明: fun _ hx => (mem_prod.1 hx).1

Depends on / 依赖: mem_prod
-/
lemma mapsTo_fst_prod {s : Set α} {t : Set β} : MapsTo Prod.fst (s ×ˢ t) s :=
  fun _ hx => (mem_prod.1 hx).1

/--
theorem `prod_subset_preimage_snd` / 定理 `prod_subset_preimage_snd`

English:
theorem prod_subset_preimage_snd
  given: (s : Set α) (t : Set β)
  statement: s ×ˢ t subseteq Prod.snd ⁻¹' t
  proof: inter_subset_right

中文:
定理 prod_subset_preimage_snd
  条件: (s : Set α) (t : Set β)
  结论: s ×ˢ t subseteq Prod.snd ⁻¹' t
  证明: inter_subset_right

Depends on / 依赖: inter_subset_right
-/
theorem prod_subset_preimage_snd (s : Set α) (t : Set β) : s ×ˢ t subseteq Prod.snd ⁻¹' t :=
  inter_subset_right

/--
theorem `snd_image_prod_subset` / 定理 `snd_image_prod_subset`

English:
theorem snd_image_prod_subset
  given: (s : Set α) (t : Set β)
  statement: Prod.snd '' s ×ˢ t subseteq t
  proof: image_subset_iff.2 prod_subset_preimage_snd s t

中文:
定理 snd_image_prod_subset
  条件: (s : Set α) (t : Set β)
  结论: Prod.snd '' s ×ˢ t subseteq t
  证明: image_subset_iff.2 prod_subset_preimage_snd s t

Depends on / 依赖: image_subset_iff, prod_subset_preimage_snd
-/
theorem snd_image_prod_subset (s : Set α) (t : Set β) : Prod.snd '' s ×ˢ t subseteq t :=
image_subset_iff.2 prod_subset_preimage_snd s t

/--
theorem `snd_image_prod` / 定理 `snd_image_prod`

English:
theorem snd_image_prod
  given: {s : Set α} (hs : s.Nonempty) (t : Set β)
  statement: Prod.snd '' s ×ˢ t = t
  proof: (snd_image_prod_subset _ _).antisymm fun y y_in =>
    let ⟨x, x_in⟩ := hs
    ⟨(x, y), ⟨x_in, y_in⟩, rfl⟩

中文:
定理 snd_image_prod
  条件: {s : Set α} (hs : s.Nonempty) (t : Set β)
  结论: Prod.snd '' s ×ˢ t = t
  证明: (snd_image_prod_subset _ _).antisymm fun y y_in =>
    let ⟨x, x_in⟩ := hs
    ⟨(x, y), ⟨x_in, y_in⟩, rfl⟩

Depends on / 依赖: antisymm, snd_image_prod_subset, x_in, y_in
-/
theorem snd_image_prod {s : Set α} (hs : s.Nonempty) (t : Set β) : Prod.snd '' s ×ˢ t = t :=
  (snd_image_prod_subset _ _).antisymm fun y y_in =>
    let ⟨x, x_in⟩ := hs
    ⟨(x, y), ⟨x_in, y_in⟩, rfl⟩

/--
theorem `subset_fst_image_prod_snd_image` / 定理 `subset_fst_image_prod_snd_image`

English:
theorem subset_fst_image_prod_snd_image
  given: {s : Set (α × β)}
  proof: fun ⟨p₁, p₂⟩ _ => by aesop

中文:
定理 subset_fst_image_prod_snd_image
  条件: {s : Set (α × β)}
  证明: fun ⟨p₁, p₂⟩ _ => by aesop
-/
theorem subset_fst_image_prod_snd_image {s : Set (α × β)} :
    s subseteq (Prod.fst '' s) ×ˢ (Prod.snd '' s) := fun ⟨p₁, p₂⟩ _ => by aesop

/--
lemma `mapsTo_snd_prod` / 引理 `mapsTo_snd_prod`

English:
lemma mapsTo_snd_prod
  given: {s : Set α} {t : Set β}
  statement: MapsTo Prod.snd (s ×ˢ t) t
  proof: fun _ hx => (mem_prod.1 hx).2

中文:
引理 mapsTo_snd_prod
  条件: {s : Set α} {t : Set β}
  结论: MapsTo Prod.snd (s ×ˢ t) t
  证明: fun _ hx => (mem_prod.1 hx).2

Depends on / 依赖: mem_prod
-/
lemma mapsTo_snd_prod {s : Set α} {t : Set β} : MapsTo Prod.snd (s ×ˢ t) t :=
  fun _ hx => (mem_prod.1 hx).2

/--
theorem `prod_sdiff_prod` / 定理 `prod_sdiff_prod`

English:
theorem prod_sdiff_prod
  statement: s ×ˢ t \ s₁ ×ˢ t₁ = s ×ˢ (t \ t₁) union (s \ s₁) ×ˢ t
  proof: by grind

@[deprecated (since := "2026-06-03")] alias prod_diff_prod := prod_sdiff_prod

中文:
定理 prod_sdiff_prod
  结论: s ×ˢ t \ s₁ ×ˢ t₁ = s ×ˢ (t \ t₁) union (s \ s₁) ×ˢ t
  证明: by grind

@[deprecated (since := "2026-06-03")] alias prod_diff_prod := prod_sdiff_prod
-/
theorem prod_sdiff_prod : s ×ˢ t \ s₁ ×ˢ t₁ = s ×ˢ (t \ t₁) union (s \ s₁) ×ˢ t := by grind

@[deprecated (since := "2026-06-03")] alias prod_diff_prod := prod_sdiff_prod

/--
theorem `prod_subset_prod_iff` / 定理 `prod_subset_prod_iff`

English:
theorem prod_subset_prod_iff
  statement: s ×ˢ t subseteq s₁ ×ˢ t₁ ↔ s subseteq s₁ ∧ t subseteq t₁ ∨ s = ∅ ∨ t = ∅
  proof: by
  rcases (s ×ˢ t).eq_empty_or_nonempty with h | h
  · simp [h, prod_eq_empty_iff.1 h]
  have st : s.Nonempty ∧ t.Nonempty := by rwa [prod_nonempty_iff] at h
  refine ⟨fun H => Or.inl ⟨?_, ?_⟩, ?_⟩
  · have := image_mono (f := Prod.fst) H
    rwa [fst_image_prod _ st.2, fst_image_prod _ (h.mono H)

中文:
定理 prod_subset_prod_iff
  结论: s ×ˢ t subseteq s₁ ×ˢ t₁ ↔ s subseteq s₁ ∧ t subseteq t₁ ∨ s = ∅ ∨ t = ∅
  证明: by
  rcases (s ×ˢ t).eq_empty_or_nonempty with h | h
  · simp [h, prod_eq_empty_iff.1 h]
  have st : s.Nonempty ∧ t.Nonempty := by rwa [prod_nonempty_iff] at h
  refine ⟨fun H => Or.inl ⟨?_, ?_⟩, ?_⟩
  · have := image_mono (f := Prod.fst) H
    rwa [fst_image_prod _ st.2, fst_image_prod _ (h.mono H)

Depends on / 依赖: Nonempty, Or.inl, Prod.fst, Prod.snd, eq_empty_or_nonempty, fst_image_prod, h.mono, image_mono, ne_empty, or_false, prod_eq_empty_iff, prod_mono, prod_nonempty_iff, s.Nonempty, snd_image_prod, t.Nonempty
-/
theorem prod_subset_prod_iff : s ×ˢ t subseteq s₁ ×ˢ t₁ ↔ s subseteq s₁ ∧ t subseteq t₁ ∨ s = ∅ ∨ t = ∅ := by
  rcases (s ×ˢ t).eq_empty_or_nonempty with h | h
  · simp [h, prod_eq_empty_iff.1 h]
  have st : s.Nonempty ∧ t.Nonempty := by rwa [prod_nonempty_iff] at h
  refine ⟨fun H => Or.inl ⟨?_, ?_⟩, ?_⟩
  · have := image_mono (f := Prod.fst) H
    rwa [fst_image_prod _ st.2, fst_image_prod _ (h.mono H).snd] at this
  · have := image_mono (f := Prod.snd) H
    rwa [snd_image_prod st.1, snd_image_prod (h.mono H).fst] at this
  · intro H
    simp only [st.1.ne_empty, st.2.ne_empty, or_false] at H
    exact prod_mono H.1 H.2

/--
theorem `prod_subset_prod_iff'` / 定理 `prod_subset_prod_iff'`

English:
theorem prod_subset_prod_iff'
  given: (h : (s ×ˢ t).Nonempty)
  statement: s ×ˢ t subseteq s₁ ×ˢ t₁ ↔ s subseteq s₁ ∧ t subseteq t₁
  proof: by
  rw [prod_subset_prod_iff]; rw [or_iff_left]
  rw [← Set.prod_eq_empty_iff]
  exact h.ne_empty

中文:
定理 prod_subset_prod_iff'
  条件: (h : (s ×ˢ t).Nonempty)
  结论: s ×ˢ t subseteq s₁ ×ˢ t₁ ↔ s subseteq s₁ ∧ t subseteq t₁
  证明: by
  rw [prod_subset_prod_iff]; rw [or_iff_left]
  rw [← Set.prod_eq_empty_iff]
  exact h.ne_empty

Depends on / 依赖: Set.prod_eq_empty_iff, h.ne_empty, ne_empty, or_iff_left, prod_eq_empty_iff, prod_subset_prod_iff
-/
theorem prod_subset_prod_iff' (h : (s ×ˢ t).Nonempty) : s ×ˢ t subseteq s₁ ×ˢ t₁ ↔ s subseteq s₁ ∧ t subseteq t₁ := by
  rw [prod_subset_prod_iff]; rw [or_iff_left]
  rw [← Set.prod_eq_empty_iff]
  exact h.ne_empty

/--
theorem `prod_subset_prod_iff_left` / 定理 `prod_subset_prod_iff_left`

English:
theorem prod_subset_prod_iff_left
  given: (h : t.Nonempty)
  statement: s ×ˢ t subseteq s₁ ×ˢ t ↔ s subseteq s₁
  proof: by
  simp +contextual [prod_subset_prod_iff, or_iff_left h.ne_empty]

中文:
定理 prod_subset_prod_iff_left
  条件: (h : t.Nonempty)
  结论: s ×ˢ t subseteq s₁ ×ˢ t ↔ s subseteq s₁
  证明: by
  simp +contextual [prod_subset_prod_iff, or_iff_left h.ne_empty]

Depends on / 依赖: contextual, h.ne_empty, ne_empty, or_iff_left, prod_subset_prod_iff
-/
theorem prod_subset_prod_iff_left (h : t.Nonempty) : s ×ˢ t subseteq s₁ ×ˢ t ↔ s subseteq s₁ := by
  simp +contextual [prod_subset_prod_iff, or_iff_left h.ne_empty]

/--
theorem `prod_subset_prod_iff_right` / 定理 `prod_subset_prod_iff_right`

English:
theorem prod_subset_prod_iff_right
  given: (h : s.Nonempty)
  statement: s ×ˢ t subseteq s ×ˢ t₁ ↔ t subseteq t₁
  proof: by
  simp +contextual [prod_subset_prod_iff, or_comm (a := s = ∅), or_iff_left h.ne_empty]

中文:
定理 prod_subset_prod_iff_right
  条件: (h : s.Nonempty)
  结论: s ×ˢ t subseteq s ×ˢ t₁ ↔ t subseteq t₁
  证明: by
  simp +contextual [prod_subset_prod_iff, or_comm (a := s = ∅), or_iff_left h.ne_empty]

Depends on / 依赖: contextual, h.ne_empty, ne_empty, or_comm, or_iff_left, prod_subset_prod_iff
-/
theorem prod_subset_prod_iff_right (h : s.Nonempty) : s ×ˢ t subseteq s ×ˢ t₁ ↔ t subseteq t₁ := by
  simp +contextual [prod_subset_prod_iff, or_comm (a := s = ∅), or_iff_left h.ne_empty]

/--
theorem `prod_eq_prod_iff_of_nonempty` / 定理 `prod_eq_prod_iff_of_nonempty`

English:
theorem prod_eq_prod_iff_of_nonempty
  given: (h : (s ×ˢ t).Nonempty)
  proof: by
  constructor
  · intro heq
    have h₁ : (s₁ ×ˢ t₁ : Set _).Nonempty := by rwa [← heq]
    rw [prod_nonempty_iff] at h h₁
    rw [← fst_image_prod s h.2]; rw [← fst_image_prod s₁ h₁.2]; rw [heq]; rw [eq_self_iff_true]; rw [true_and]; rw [←
      snd_image_prod h.1 t]; rw [← snd_image_prod h₁.1 t

中文:
定理 prod_eq_prod_iff_of_nonempty
  条件: (h : (s ×ˢ t).Nonempty)
  证明: by
  constructor
  · intro heq
    have h₁ : (s₁ ×ˢ t₁ : Set _).Nonempty := by rwa [← heq]
    rw [prod_nonempty_iff] at h h₁
    rw [← fst_image_prod s h.2]; rw [← fst_image_prod s₁ h₁.2]; rw [heq]; rw [eq_self_iff_true]; rw [true_and]; rw [←
      snd_image_prod h.1 t]; rw [← snd_image_prod h₁.1 t

Depends on / 依赖: Equiv.bijective_comp, Equiv.mk, Nonempty, Prod.ext, _def, bijective_comp, comp_bijective, eq_self_iff_true, fst_image_prod, inv_inv, isComplement, isComplement_iff_bijective, mul_inv_rev, prod_nonempty_iff, snd_image_prod, true_and
-/
theorem prod_eq_prod_iff_of_nonempty (h : (s ×ˢ t).Nonempty) :
    s ×ˢ t = s₁ ×ˢ t₁ ↔ s = s₁ ∧ t = t₁ := by
  constructor
  · intro heq
    have h₁ : (s₁ ×ˢ t₁ : Set _).Nonempty := by rwa [← heq]
    rw [prod_nonempty_iff] at h h₁
    rw [← fst_image_prod s h.2]; rw [← fst_image_prod s₁ h₁.2]; rw [heq]; rw [eq_self_iff_true]; rw [true_and]; rw [←
      snd_image_prod h.1 t]; rw [← snd_image_prod h₁.1 t₁]; rw [heq]
  · grind


/--
theorem `prod_eq_prod_iff` / 定理 `prod_eq_prod_iff`

English:
theorem prod_eq_prod_iff
  proof: by
  symm
  rcases eq_empty_or_nonempty (s ×ˢ t) with h | h
  · simp_rw [h, @eq_comm _ ∅, prod_eq_empty_iff, prod_eq_empty_iff.mp h, true_and,
      or_iff_right_iff_imp]
    rintro ⟨rfl, rfl⟩
    exact prod_eq_empty_iff.mp h
  rw [prod_eq_prod_iff_of_nonempty h]
  rw [nonempty_iff_ne_empty]; rw [Ne

中文:
定理 prod_eq_prod_iff
  证明: by
  symm
  rcases eq_empty_or_nonempty (s ×ˢ t) with h | h
  · simp_rw [h, @eq_comm _ ∅, prod_eq_empty_iff, prod_eq_empty_iff.mp h, true_and,
      or_iff_right_iff_imp]
    rintro ⟨rfl, rfl⟩
    exact prod_eq_empty_iff.mp h
  rw [prod_eq_prod_iff_of_nonempty h]
  rw [nonempty_iff_ne_empty]; rw [Ne

Depends on / 依赖: IsComplement, eq_comm, eq_empty_or_nonempty, false_and, nonempty_iff_ne_empty, or_false, or_iff_right_iff_imp, prod_eq_empty_iff, prod_eq_empty_iff.mp, prod_eq_prod_iff_of_nonempty, simp_rw, true_and
-/
theorem prod_eq_prod_iff :
    s ×ˢ t = s₁ ×ˢ t₁ ↔ s = s₁ ∧ t = t₁ ∨ (s = ∅ ∨ t = ∅) ∧ (s₁ = ∅ ∨ t₁ = ∅) := by
  symm
  rcases eq_empty_or_nonempty (s ×ˢ t) with h | h
  · simp_rw [h, @eq_comm _ ∅, prod_eq_empty_iff, prod_eq_empty_iff.mp h, true_and,
      or_iff_right_iff_imp]
    rintro ⟨rfl, rfl⟩
    exact prod_eq_empty_iff.mp h
  rw [prod_eq_prod_iff_of_nonempty h]
  rw [nonempty_iff_ne_empty]; rw [Ne]; rw [prod_eq_empty_iff] at h
  simp_rw [h, false_and, or_false]

@[simp]
/--
theorem `prod_eq_iff_eq` / 定理 `prod_eq_iff_eq`

English:
theorem prod_eq_iff_eq
  given: (ht : t.Nonempty)
  statement: s ×ˢ t = s₁ ×ˢ t ↔ s = s₁
  proof: by
  simp_rw [prod_eq_prod_iff, ht.ne_empty, and_true, or_iff_left_iff_imp, or_false]
  rintro ⟨rfl, rfl⟩
  rfl

中文:
定理 prod_eq_iff_eq
  条件: (ht : t.Nonempty)
  结论: s ×ˢ t = s₁ ×ˢ t ↔ s = s₁
  证明: by
  simp_rw [prod_eq_prod_iff, ht.ne_empty, and_true, or_iff_left_iff_imp, or_false]
  rintro ⟨rfl, rfl⟩
  rfl

Depends on / 依赖: and_true, ht.ne_empty, ne_empty, or_false, or_iff_left_iff_imp, prod_eq_prod_iff, simp_rw
-/
theorem prod_eq_iff_eq (ht : t.Nonempty) : s ×ˢ t = s₁ ×ˢ t ↔ s = s₁ := by
  simp_rw [prod_eq_prod_iff, ht.ne_empty, and_true, or_iff_left_iff_imp, or_false]
  rintro ⟨rfl, rfl⟩
  rfl

/--
theorem `subset_prod` / 定理 `subset_prod`

English:
theorem subset_prod
  given: {s : Set (α × β)}
  statement: s subseteq (Prod.fst '' s) ×ˢ (Prod.snd '' s)
  proof: fun _ hp => mem_prod.2 ⟨mem_image_of_mem _ hp, mem_image_of_mem _ hp⟩

中文:
定理 subset_prod
  条件: {s : Set (α × β)}
  结论: s subseteq (Prod.fst '' s) ×ˢ (Prod.snd '' s)
  证明: fun _ hp => mem_prod.2 ⟨mem_image_of_mem _ hp, mem_image_of_mem _ hp⟩

Depends on / 依赖: mem_image_of_mem, mem_prod
-/
theorem subset_prod {s : Set (α × β)} : s subseteq (Prod.fst '' s) ×ˢ (Prod.snd '' s) :=
  fun _ hp => mem_prod.2 ⟨mem_image_of_mem _ hp, mem_image_of_mem _ hp⟩

section Mono

variable [Preorder α] {f : α -> Set β} {g : α -> Set γ}

/--
theorem `_root_.Monotone.set_prod` / 定理 `_root_.Monotone.set_prod`

English:
theorem _root_.Monotone.set_prod
  given: (hf : Monotone f) (hg : Monotone g)
  proof: fun _ _ h => prod_mono (hf h) (hg h)

中文:
定理 _root_.Monotone.set_prod
  条件: (hf : Monotone f) (hg : Monotone g)
  证明: fun _ _ h => prod_mono (hf h) (hg h)

Depends on / 依赖: prod_mono
-/
theorem _root_.Monotone.set_prod (hf : Monotone f) (hg : Monotone g) :
    Monotone fun x => f x ×ˢ g x :=
  fun _ _ h => prod_mono (hf h) (hg h)

/--
theorem `_root_.Antitone.set_prod` / 定理 `_root_.Antitone.set_prod`

English:
theorem _root_.Antitone.set_prod
  given: (hf : Antitone f) (hg : Antitone g)
  proof: fun _ _ h => prod_mono (hf h) (hg h)

中文:
定理 _root_.Antitone.set_prod
  条件: (hf : Antitone f) (hg : Antitone g)
  证明: fun _ _ h => prod_mono (hf h) (hg h)

Depends on / 依赖: prod_mono
-/
theorem _root_.Antitone.set_prod (hf : Antitone f) (hg : Antitone g) :
    Antitone fun x => f x ×ˢ g x :=
  fun _ _ h => prod_mono (hf h) (hg h)

/--
theorem `_root_.MonotoneOn.set_prod` / 定理 `_root_.MonotoneOn.set_prod`

English:
theorem _root_.MonotoneOn.set_prod
  given: (hf : MonotoneOn f s) (hg : MonotoneOn g s)
  proof: fun _ ha _ hb h => prod_mono (hf ha hb h) (hg ha hb h)

中文:
定理 _root_.MonotoneOn.set_prod
  条件: (hf : MonotoneOn f s) (hg : MonotoneOn g s)
  证明: fun _ ha _ hb h => prod_mono (hf ha hb h) (hg ha hb h)

Depends on / 依赖: prod_mono
-/
theorem _root_.MonotoneOn.set_prod (hf : MonotoneOn f s) (hg : MonotoneOn g s) :
    MonotoneOn (fun x => f x ×ˢ g x) s := fun _ ha _ hb h => prod_mono (hf ha hb h) (hg ha hb h)

/--
theorem `_root_.AntitoneOn.set_prod` / 定理 `_root_.AntitoneOn.set_prod`

English:
theorem _root_.AntitoneOn.set_prod
  given: (hf : AntitoneOn f s) (hg : AntitoneOn g s)
  proof: fun _ ha _ hb h => prod_mono (hf ha hb h) (hg ha hb h)

中文:
定理 _root_.AntitoneOn.set_prod
  条件: (hf : AntitoneOn f s) (hg : AntitoneOn g s)
  证明: fun _ ha _ hb h => prod_mono (hf ha hb h) (hg ha hb h)

Depends on / 依赖: prod_mono
-/
theorem _root_.AntitoneOn.set_prod (hf : AntitoneOn f s) (hg : AntitoneOn g s) :
    AntitoneOn (fun x => f x ×ˢ g x) s := fun _ ha _ hb h => prod_mono (hf ha hb h) (hg ha hb h)

end Mono

/--
lemma `eqOn_prod_iff` / 引理 `eqOn_prod_iff`

English:
lemma eqOn_prod_iff
  given: {a b : α -> γ × δ}
  proof: by
  grind [EqOn]

中文:
引理 eqOn_prod_iff
  条件: {a b : α -> γ × δ}
  证明: by
  grind [EqOn]
-/
lemma eqOn_prod_iff {a b : α -> γ × δ} :
    EqOn a b s ↔ EqOn (Prod.fst ∘ a) (Prod.fst ∘ b) s ∧ EqOn (Prod.snd ∘ a) (Prod.snd ∘ b) s := by
  grind [EqOn]

/--
lemma `EqOn.left_of_eqOn_prodMap` / 引理 `EqOn.left_of_eqOn_prodMap`

English:
lemma EqOn.left_of_eqOn_prodMap
  statement: {f f' : α -> γ} {g g' : β -> δ}
  proof: by
  obtain ⟨x, hxt⟩ := ht
  intro x hxs
have h' := h mk_mem_prod hxs hxt
  grind

中文:
引理 EqOn.left_of_eqOn_prodMap
  结论: {f f' : α -> γ} {g g' : β -> δ}
  证明: by
  obtain ⟨x, hxt⟩ := ht
  intro x hxs
have h' := h mk_mem_prod hxs hxt
  grind

Depends on / 依赖: mk_mem_prod
-/
lemma EqOn.left_of_eqOn_prodMap {f f' : α -> γ} {g g' : β -> δ}
    (h : EqOn (Prod.map f g) (Prod.map f' g') (s ×ˢ t)) (ht : t.Nonempty) : EqOn f f' s := by
  obtain ⟨x, hxt⟩ := ht
  intro x hxs
have h' := h mk_mem_prod hxs hxt
  grind

/--
lemma `EqOn.right_of_eqOn_prodMap` / 引理 `EqOn.right_of_eqOn_prodMap`

English:
lemma EqOn.right_of_eqOn_prodMap
  statement: {f f' : α -> γ} {g g' : β -> δ}
  proof: by
  obtain ⟨x, hxs⟩ := hs
  intro x hxt
have h' := h mk_mem_prod hxs hxt
  grind

中文:
引理 EqOn.right_of_eqOn_prodMap
  结论: {f f' : α -> γ} {g g' : β -> δ}
  证明: by
  obtain ⟨x, hxs⟩ := hs
  intro x hxt
have h' := h mk_mem_prod hxs hxt
  grind

Depends on / 依赖: mk_mem_prod
-/
lemma EqOn.right_of_eqOn_prodMap {f f' : α -> γ} {g g' : β -> δ}
    (h : EqOn (Prod.map f g) (Prod.map f' g') (s ×ˢ t)) (hs : Set.Nonempty s) : EqOn g g' t := by
  obtain ⟨x, hxs⟩ := hs
  intro x hxt
have h' := h mk_mem_prod hxs hxt
  grind

/--
lemma `EqOn.prodMap` / 引理 `EqOn.prodMap`

English:
lemma EqOn.prodMap
  statement: {f f' : α -> γ} {g g' : β -> δ}
  proof: by
  grind [EqOn]

中文:
引理 EqOn.prodMap
  结论: {f f' : α -> γ} {g g' : β -> δ}
  证明: by
  grind [EqOn]
-/
lemma EqOn.prodMap {f f' : α -> γ} {g g' : β -> δ}
    (hf : EqOn f f' s) (hg : EqOn g g' t) : EqOn (Prod.map f g) (Prod.map f' g') (s ×ˢ t) := by
  grind [EqOn]

/--
lemma `eqOn_prodMap_iff` / 引理 `eqOn_prodMap_iff`

English:
lemma eqOn_prodMap_iff
  statement: {f f' : α -> γ} {g g' : β -> δ}
  proof: ⟨fun h => ⟨h.left_of_eqOn_prodMap ht, h.right_of_eqOn_prodMap hs⟩, fun ⟨h, h'⟩ => h.prodMap h'⟩

中文:
引理 eqOn_prodMap_iff
  结论: {f f' : α -> γ} {g g' : β -> δ}
  证明: ⟨fun h => ⟨h.left_of_eqOn_prodMap ht, h.right_of_eqOn_prodMap hs⟩, fun ⟨h, h'⟩ => h.prodMap h'⟩

Depends on / 依赖: h.left_of_eqOn_prodMap, h.prodMap, h.right_of_eqOn_prodMap, left_of_eqOn_prodMap, prodMap, right_of_eqOn_prodMap
-/
lemma eqOn_prodMap_iff {f f' : α -> γ} {g g' : β -> δ}
    {s : Set α} {t : Set β} (hs : Set.Nonempty s) (ht : Set.Nonempty t) :
    EqOn (Prod.map f g) (Prod.map f' g') (s ×ˢ t) ↔ EqOn f f' s ∧ EqOn g g' t :=
  ⟨fun h => ⟨h.left_of_eqOn_prodMap ht, h.right_of_eqOn_prodMap hs⟩, fun ⟨h, h'⟩ => h.prodMap h'⟩

end Prod

/-! ### Diagonal

In this section we prove some lemmas about the diagonal set `{p | p.1 = p.2}` and the diagonal map
`fun x ↦ (x, x)`.
-/


section Diagonal

variable {α : Type*} {s t : Set α}

/--
lemma `diagonal_nonempty` / 引理 `diagonal_nonempty`

English:
lemma diagonal_nonempty
  given: [Nonempty α]
  statement: (diagonal α).Nonempty
  proof: Nonempty.elim ‹_› fun x => ⟨_, mem_diagonal x⟩

中文:
引理 diagonal_nonempty
  条件: [Nonempty α]
  结论: (diagonal α).Nonempty
  证明: Nonempty.elim ‹_› fun x => ⟨_, mem_diagonal x⟩

Depends on / 依赖: Nonempty, Nonempty.elim, mem_diagonal
-/
lemma diagonal_nonempty [Nonempty α] : (diagonal α).Nonempty :=
  Nonempty.elim ‹_› fun x => ⟨_, mem_diagonal x⟩

/--
Instance `decidableMemDiagonal` / 实例 `decidableMemDiagonal`

English:
instance decidableMemDiagonal
  signature: [h : DecidableEq α] (x : α × α)
  body: h x.1 x.2

中文:
实例 decidableMemDiagonal
  签名: [h : DecidableEq α] (x : α × α)
  定义体: h x.1 x.2

Depends on / 依赖: isComplement_univ_singleton
-/
instance decidableMemDiagonal [h : DecidableEq α] (x : α × α) : Decidable (x in diagonal α) :=
  h x.1 x.2

/--
theorem `preimage_coe_coe_diagonal` / 定理 `preimage_coe_coe_diagonal`

English:
theorem preimage_coe_coe_diagonal
  given: (s : Set α)
  proof: by
  ext ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  simp [Set.diagonal]

@[simp]

中文:
定理 preimage_coe_coe_diagonal
  条件: (s : Set α)
  证明: by
  ext ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  simp [Set.diagonal]

@[simp]

Depends on / 依赖: Set.diagonal, diagonal, isComplement_singleton_univ
-/
theorem preimage_coe_coe_diagonal (s : Set α) :
    Prod.map (fun x : s => (x : α)) (fun x : s => (x : α)) ⁻¹' diagonal α = diagonal s := by
  ext ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  simp [Set.diagonal]

@[simp]
/--
theorem `range_diag` / 定理 `range_diag`

English:
theorem range_diag
  statement: range Function.diag = diagonal α
  proof: by
  ext ⟨x, y⟩
  simp [diagonal, eq_comm]

中文:
定理 range_diag
  结论: range Function.diag = diagonal α
  证明: by
  ext ⟨x, y⟩
  simp [diagonal, eq_comm]

Depends on / 依赖: coe_eq_univ, diagonal, eq_comm, isComplement_singleton_left, isComplement_singleton_left.trans
-/
theorem range_diag : range Function.diag = diagonal α := by
  ext ⟨x, y⟩
  simp [diagonal, eq_comm]

/--
theorem `diagonal_subset_iff` / 定理 `diagonal_subset_iff`

English:
theorem diagonal_subset_iff
  given: {s}
  statement: diagonal α subseteq s ↔ forall x, (x, x) in s
  proof: by grind

@[simp]

中文:
定理 diagonal_subset_iff
  条件: {s}
  结论: diagonal α subseteq s ↔ 对任意 x, (x, x) in s
  证明: by grind

@[simp]

Depends on / 依赖: coe_eq_univ, isComplement_singleton_right, isComplement_singleton_right.trans
-/
theorem diagonal_subset_iff {s} : diagonal α subseteq s ↔ forall x, (x, x) in s := by grind

@[simp]
/--
theorem `prod_subset_compl_diagonal_iff_disjoint` / 定理 `prod_subset_compl_diagonal_iff_disjoint`

English:
theorem prod_subset_compl_diagonal_iff_disjoint
  statement: s ×ˢ t subseteq (diagonal α)ᶜ ↔ Disjoint s t
  proof: prod_subset_iff.trans disjoint_iff_forall_ne.symm

@[simp]

中文:
定理 prod_subset_compl_diagonal_iff_disjoint
  结论: s ×ˢ t subseteq (diagonal α)ᶜ ↔ Disjoint s t
  证明: prod_subset_iff.trans disjoint_iff_forall_ne.symm

@[simp]

Depends on / 依赖: coe_eq_singleton, disjoint_iff_forall_ne, disjoint_iff_forall_ne.symm, isComplement_univ_left, isComplement_univ_left.trans, prod_subset_iff, prod_subset_iff.trans
-/
theorem prod_subset_compl_diagonal_iff_disjoint : s ×ˢ t subseteq (diagonal α)ᶜ ↔ Disjoint s t :=
  prod_subset_iff.trans disjoint_iff_forall_ne.symm

@[simp]
/--
theorem `diag_preimage_prod` / 定理 `diag_preimage_prod`

English:
theorem diag_preimage_prod
  given: (s t : Set α)
  statement: Function.diag ⁻¹' s ×ˢ t = s inter t
  proof: rfl

中文:
定理 diag_preimage_prod
  条件: (s t : Set α)
  结论: Function.diag ⁻¹' s ×ˢ t = s inter t
  证明: rfl

Depends on / 依赖: coe_eq_singleton, isComplement_univ_right, isComplement_univ_right.trans
-/
theorem diag_preimage_prod (s t : Set α) : Function.diag ⁻¹' s ×ˢ t = s inter t :=
  rfl

/--
theorem `diag_preimage_prod_self` / 定理 `diag_preimage_prod_self`

English:
theorem diag_preimage_prod_self
  given: (s : Set α)
  statement: Function.diag ⁻¹' s ×ˢ s = s
  proof: inter_self s

中文:
定理 diag_preimage_prod_self
  条件: (s : Set α)
  结论: Function.diag ⁻¹' s ×ˢ s = s
  证明: inter_self s

Depends on / 依赖: inter_self
-/
theorem diag_preimage_prod_self (s : Set α) : Function.diag ⁻¹' s ×ˢ s = s :=
  inter_self s

/--
theorem `diag_image` / 定理 `diag_image`

English:
theorem diag_image
  given: (s : Set α)
  statement: Function.diag '' s = diagonal α inter s ×ˢ s
  proof: by
  rw [← range_diag]; rw [← image_preimage_eq_range_inter]; rw [diag_preimage_prod_self]

中文:
定理 diag_image
  条件: (s : Set α)
  结论: Function.diag '' s = diagonal α inter s ×ˢ s
  证明: by
  rw [← range_diag]; rw [← image_preimage_eq_range_inter]; rw [diag_preimage_prod_self]

Depends on / 依赖: diag_preimage_prod_self, image_preimage_eq_range_inter, range_diag
-/
theorem diag_image (s : Set α) : Function.diag '' s = diagonal α inter s ×ˢ s := by
  rw [← range_diag]; rw [← image_preimage_eq_range_inter]; rw [diag_preimage_prod_self]

/--
theorem `diagonal_eq_univ_iff` / 定理 `diagonal_eq_univ_iff`

English:
theorem diagonal_eq_univ_iff
  statement: diagonal α = univ ↔ Subsingleton α
  proof: by
  simp only [subsingleton_iff, eq_univ_iff_forall, Prod.forall, mem_diagonal_iff]

中文:
定理 diagonal_eq_univ_iff
  结论: diagonal α = univ ↔ Subsingleton α
  证明: by
  simp only [subsingleton_iff, eq_univ_iff_forall, Prod.forall, mem_diagonal_iff]

Depends on / 依赖: Prod.forall, eq_univ_iff_forall, mem_diagonal_iff, subsingleton_iff
-/
theorem diagonal_eq_univ_iff : diagonal α = univ ↔ Subsingleton α := by
  simp only [subsingleton_iff, eq_univ_iff_forall, Prod.forall, mem_diagonal_iff]

/--
theorem `diagonal_eq_univ` / 定理 `diagonal_eq_univ`

English:
theorem diagonal_eq_univ
  given: [Subsingleton α]
  statement: diagonal α = univ
  proof: diagonal_eq_univ_iff.2 ‹_›

中文:
定理 diagonal_eq_univ
  条件: [Subsingleton α]
  结论: diagonal α = univ
  证明: diagonal_eq_univ_iff.2 ‹_›

Depends on / 依赖: diagonal_eq_univ_iff
-/
theorem diagonal_eq_univ [Subsingleton α] : diagonal α = univ := diagonal_eq_univ_iff.2 ‹_›

end Diagonal

/--
theorem `range_const_eq_diagonal` / 定理 `range_const_eq_diagonal`

English:
theorem range_const_eq_diagonal
  given: {α β : Type*} [hβ : Nonempty β]
  proof: by
  refine (range_eq_iff _ _).mpr ⟨fun _ _ _ => rfl, fun f hf => ?_⟩
  rcases isEmpty_or_nonempty α with h | ⟨⟨a⟩⟩
  · exact hβ.elim fun b => ⟨b, Subsingleton.elim _ _⟩
  · exact ⟨f a, funext fun x => hf _ _⟩

中文:
定理 range_const_eq_diagonal
  条件: {α β : 类型} [hβ : Nonempty β]
  证明: by
  refine (range_eq_iff _ _).mpr ⟨fun _ _ _ => rfl, fun f hf => ?_⟩
  rcases isEmpty_or_nonempty α with h | ⟨⟨a⟩⟩
  · exact hβ.elim fun b => ⟨b, Subsingleton.elim _ _⟩
  · exact ⟨f a, funext fun x => hf _ _⟩

Depends on / 依赖: Subsingleton, Subsingleton.elim, isEmpty_or_nonempty, range_eq_iff
-/
theorem range_const_eq_diagonal {α β : Type*} [hβ : Nonempty β] :
    range (const α) = {f : α -> β | forall x y, f x = f y} := by
  refine (range_eq_iff _ _).mpr ⟨fun _ _ _ => rfl, fun f hf => ?_⟩
  rcases isEmpty_or_nonempty α with h | ⟨⟨a⟩⟩
  · exact hβ.elim fun b => ⟨b, Subsingleton.elim _ _⟩
  · exact ⟨f a, funext fun x => hf _ _⟩

end Set

section Pullback

open Set

variable {X Y Z}

/--
Definition of `Function.Pullback` / `Function.Pullback` 的定义

English:
abbreviation Function.Pullback
  signature: (f : X -> Y) (g : Z -> Y)
  body: {p : X × Z // f p.1 = g p.2}

中文:
缩写 Function.Pullback
  签名: (f : X -> Y) (g : Z -> Y)
  定义体: {p : X × Z // f p.1 = g p.2}
-/
abbrev Function.Pullback (f : X -> Y) (g : Z -> Y) := {p : X × Z // f p.1 = g p.2}

/--
Definition of `Function.PullbackSelf` / `Function.PullbackSelf` 的定义

English:
abbreviation Function.PullbackSelf
  signature: (f : X -> Y)
  body: f.Pullback f

中文:
缩写 Function.PullbackSelf
  签名: (f : X -> Y)
  定义体: f.Pullback f

Depends on / 依赖: Pullback, f.Pullback
-/
abbrev Function.PullbackSelf (f : X -> Y) := f.Pullback f

/--
Definition of `Function.Pullback.fst` / `Function.Pullback.fst` 的定义

English:
definition Function.Pullback.fst
  signature: {f : X -> Y} {g : Z -> Y} (p : f.Pullback g)
  body: p.val.1

中文:
定义 Function.Pullback.fst
  签名: {f : X -> Y} {g : Z -> Y} (p : f.Pullback g)
  定义体: p.val.1

Depends on / 依赖: p.val
-/
def Function.Pullback.fst {f : X -> Y} {g : Z -> Y} (p : f.Pullback g) : X := p.val.1

/--
Definition of `Function.Pullback.snd` / `Function.Pullback.snd` 的定义

English:
definition Function.Pullback.snd
  signature: {f : X -> Y} {g : Z -> Y} (p : f.Pullback g)
  body: p.val.2

中文:
定义 Function.Pullback.snd
  签名: {f : X -> Y} {g : Z -> Y} (p : f.Pullback g)
  定义体: p.val.2

Depends on / 依赖: p.val
-/
def Function.Pullback.snd {f : X -> Y} {g : Z -> Y} (p : f.Pullback g) : Z := p.val.2

open Function.Pullback in
/--
lemma `Function.pullback_comm_sq` / 引理 `Function.pullback_comm_sq`

English:
lemma Function.pullback_comm_sq
  given: (f : X -> Y) (g : Z -> Y)
  proof: funext fun p => p.2

中文:
引理 Function.pullback_comm_sq
  条件: (f : X -> Y) (g : Z -> Y)
  证明: funext fun p => p.2
-/
lemma Function.pullback_comm_sq (f : X -> Y) (g : Z -> Y) :
    f ∘ @fst X Y Z f g = g ∘ @snd X Y Z f g := funext fun p => p.2

/-- The diagonal map $\Delta: X \to X \times_Y X$. -/
@[simps]
/--
Definition of `toPullbackDiag` / `toPullbackDiag` 的定义

English:
definition toPullbackDiag
  signature: (f : X -> Y) (x : X)
  body: ⟨(x, x), rfl⟩

中文:
定义 toPullbackDiag
  签名: (f : X -> Y) (x : X)
  定义体: ⟨(x, x), rfl⟩
-/
def toPullbackDiag (f : X -> Y) (x : X) : f.Pullback f := ⟨(x, x), rfl⟩

/--
Definition of `Function.pullbackDiagonal` / `Function.pullbackDiagonal` 的定义

English:
definition Function.pullbackDiagonal
  signature: (f : X -> Y)
  body: {p | p.fst = p.snd}

中文:
定义 Function.pullbackDiagonal
  签名: (f : X -> Y)
  定义体: {p | p.fst = p.snd}

Depends on / 依赖: p.fst, p.snd
-/
def Function.pullbackDiagonal (f : X -> Y) : Set (f.Pullback f) := {p | p.fst = p.snd}

/--
Definition of `Function.mapPullback` / `Function.mapPullback` 的定义

English:
definition Function.mapPullback
  signature: {X₁ X₂ Y₁ Y₂ Z₁ Z₂}
  body: ⟨(mapX p.fst, mapZ p.snd),
(congr_fun commX _).trans (congr_arg mapY p.2).trans congr_fun commZ.symm _⟩

中文:
定义 Function.mapPullback
  签名: {X₁ X₂ Y₁ Y₂ Z₁ Z₂}
  定义体: ⟨(mapX p.fst, mapZ p.snd),
(congr_fun commX _).trans (congr_arg mapY p.2).trans congr_fun commZ.symm _⟩

Depends on / 依赖: commZ.symm, congr_arg, congr_fun, p.fst, p.snd
-/
def Function.mapPullback {X₁ X₂ Y₁ Y₂ Z₁ Z₂}
    {f₁ : X₁ -> Y₁} {g₁ : Z₁ -> Y₁} {f₂ : X₂ -> Y₂} {g₂ : Z₂ -> Y₂}
    (mapX : X₁ -> X₂) (mapY : Y₁ -> Y₂) (mapZ : Z₁ -> Z₂)
    (commX : f₂ ∘ mapX = mapY ∘ f₁) (commZ : g₂ ∘ mapZ = mapY ∘ g₁)
    (p : f₁.Pullback g₁) : f₂.Pullback g₂ :=
  ⟨(mapX p.fst, mapZ p.snd),
(congr_fun commX _).trans (congr_arg mapY p.2).trans congr_fun commZ.symm _⟩

open Function.Pullback in
/--
Definition of `Function.PullbackSelf.map_fst` / `Function.PullbackSelf.map_fst` 的定义

English:
definition Function.PullbackSelf.map_fst
  signature: {f : X -> Y} {g : Z -> Y}
  body: mapPullback fst g fst (pullback_comm_sq f g) (pullback_comm_sq f g)

中文:
定义 Function.PullbackSelf.map_fst
  签名: {f : X -> Y} {g : Z -> Y}
  定义体: mapPullback fst g fst (pullback_comm_sq f g) (pullback_comm_sq f g)

Depends on / 依赖: mapPullback, pullback_comm_sq
-/
def Function.PullbackSelf.map_fst {f : X -> Y} {g : Z -> Y} :
    (@snd X Y Z f g).PullbackSelf -> f.PullbackSelf :=
  mapPullback fst g fst (pullback_comm_sq f g) (pullback_comm_sq f g)

open Function.Pullback in
/--
Definition of `Function.PullbackSelf.map_snd` / `Function.PullbackSelf.map_snd` 的定义

English:
definition Function.PullbackSelf.map_snd
  signature: {f : X -> Y} {g : Z -> Y}
  body: mapPullback snd f snd (pullback_comm_sq f g).symm (pullback_comm_sq f g).symm

中文:
定义 Function.PullbackSelf.map_snd
  签名: {f : X -> Y} {g : Z -> Y}
  定义体: mapPullback snd f snd (pullback_comm_sq f g).symm (pullback_comm_sq f g).symm

Depends on / 依赖: mapPullback, pullback_comm_sq
-/
def Function.PullbackSelf.map_snd {f : X -> Y} {g : Z -> Y} :
    (@fst X Y Z f g).PullbackSelf -> g.PullbackSelf :=
  mapPullback snd f snd (pullback_comm_sq f g).symm (pullback_comm_sq f g).symm

open Function.PullbackSelf Function.Pullback
/--
theorem `preimage_map_fst_pullbackDiagonal` / 定理 `preimage_map_fst_pullbackDiagonal`

English:
theorem preimage_map_fst_pullbackDiagonal
  given: {f : X -> Y} {g : Z -> Y}
  proof: by
  ext ⟨⟨p₁, p₂⟩, he⟩
  simp_rw [pullbackDiagonal, mem_ofPred, Subtype.ext_iff, Prod.ext_iff]
  exact (and_iff_left he).symm

中文:
定理 preimage_map_fst_pullbackDiagonal
  条件: {f : X -> Y} {g : Z -> Y}
  证明: by
  ext ⟨⟨p₁, p₂⟩, he⟩
  simp_rw [pullbackDiagonal, mem_ofPred, Subtype.ext_iff, Prod.ext_iff]
  exact (and_iff_left he).symm

Depends on / 依赖: Prod.ext_iff, Subtype, Subtype.ext_iff, and_iff_left, ext_iff, mem_ofPred, pullbackDiagonal, simp_rw
-/
theorem preimage_map_fst_pullbackDiagonal {f : X -> Y} {g : Z -> Y} :
    @map_fst X Y Z f g ⁻¹' pullbackDiagonal f = pullbackDiagonal (@snd X Y Z f g) := by
  ext ⟨⟨p₁, p₂⟩, he⟩
  simp_rw [pullbackDiagonal, mem_ofPred, Subtype.ext_iff, Prod.ext_iff]
  exact (and_iff_left he).symm

/--
theorem `Function.Injective.preimage_pullbackDiagonal` / 定理 `Function.Injective.preimage_pullbackDiagonal`

English:
theorem Function.Injective.preimage_pullbackDiagonal
  given: {f : X -> Y} {g : Z -> X} (inj : g.Injective)
  proof: ext fun _ => inj.eq_iff

中文:
定理 Function.Injective.preimage_pullbackDiagonal
  条件: {f : X -> Y} {g : Z -> X} (inj : g.Injective)
  证明: ext fun _ => inj.eq_iff

Depends on / 依赖: eq_iff, inj.eq_iff
-/
theorem Function.Injective.preimage_pullbackDiagonal {f : X -> Y} {g : Z -> X} (inj : g.Injective) :
    mapPullback g id g (by rfl) (by rfl) ⁻¹' pullbackDiagonal f = pullbackDiagonal (f ∘ g) :=
  ext fun _ => inj.eq_iff

/--
theorem `image_toPullbackDiag` / 定理 `image_toPullbackDiag`

English:
theorem image_toPullbackDiag
  given: (f : X -> Y) (s : Set X)
  proof: by
  ext x
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨rfl, hx, hx⟩
  · obtain ⟨⟨x, y⟩, h⟩ := x
    rintro ⟨rfl : x = y, h2x⟩
    exact mem_image_of_mem _ h2x.1

中文:
定理 image_toPullbackDiag
  条件: (f : X -> Y) (s : Set X)
  证明: by
  ext x
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨rfl, hx, hx⟩
  · obtain ⟨⟨x, y⟩, h⟩ := x
    rintro ⟨rfl : x = y, h2x⟩
    exact mem_image_of_mem _ h2x.1

Depends on / 依赖: mem_image_of_mem
-/
theorem image_toPullbackDiag (f : X -> Y) (s : Set X) :
    toPullbackDiag f '' s = pullbackDiagonal f inter Subtype.val ⁻¹' s ×ˢ s := by
  ext x
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨rfl, hx, hx⟩
  · obtain ⟨⟨x, y⟩, h⟩ := x
    rintro ⟨rfl : x = y, h2x⟩
    exact mem_image_of_mem _ h2x.1

/--
theorem `range_toPullbackDiag` / 定理 `range_toPullbackDiag`

English:
theorem range_toPullbackDiag
  given: (f : X -> Y)
  statement: range (toPullbackDiag f) = pullbackDiagonal f
  proof: by
  rw [← image_univ]; rw [image_toPullbackDiag]; rw [univ_prod_univ]; rw [preimage_univ]; rw [inter_univ]

中文:
定理 range_toPullbackDiag
  条件: (f : X -> Y)
  结论: range (toPullbackDiag f) = pullbackDiagonal f
  证明: by
  rw [← image_univ]; rw [image_toPullbackDiag]; rw [univ_prod_univ]; rw [preimage_univ]; rw [inter_univ]

Depends on / 依赖: image_toPullbackDiag, image_univ, inter_univ, preimage_univ, univ_prod_univ
-/
theorem range_toPullbackDiag (f : X -> Y) : range (toPullbackDiag f) = pullbackDiagonal f := by
  rw [← image_univ]; rw [image_toPullbackDiag]; rw [univ_prod_univ]; rw [preimage_univ]; rw [inter_univ]

/--
theorem `injective_toPullbackDiag` / 定理 `injective_toPullbackDiag`

English:
theorem injective_toPullbackDiag
  given: (f : X -> Y)
  statement: (toPullbackDiag f).Injective
  proof: fun _ _ h => congr_arg Prod.fst (congr_arg Subtype.val h)

中文:
定理 injective_toPullbackDiag
  条件: (f : X -> Y)
  结论: (toPullbackDiag f).Injective
  证明: fun _ _ h => congr_arg Prod.fst (congr_arg Subtype.val h)

Depends on / 依赖: Prod.fst, Subtype, Subtype.val, congr_arg
-/
theorem injective_toPullbackDiag (f : X -> Y) : (toPullbackDiag f).Injective :=
  fun _ _ h => congr_arg Prod.fst (congr_arg Subtype.val h)

end Pullback

namespace Set

section OffDiag

variable {α : Type*} {s t : Set α} {a : α}

/--
theorem `offDiag_mono` / 定理 `offDiag_mono`

English:
theorem offDiag_mono
  statement: Monotone (offDiag : Set α -> Set (α × α))
  proof: fun _ _ h _ =>
And.imp (@h _) And.imp_left @h _

@[simp]

中文:
定理 offDiag_mono
  结论: Monotone (offDiag : Set α -> Set (α × α))
  证明: fun _ _ h _ =>
And.imp (@h _) And.imp_left @h _

@[simp]
-/
theorem offDiag_mono : Monotone (offDiag : Set α -> Set (α × α)) := fun _ _ h _ =>
And.imp (@h _) And.imp_left @h _

@[simp]
/--
theorem `offDiag_nonempty` / 定理 `offDiag_nonempty`

English:
theorem offDiag_nonempty
  statement: s.offDiag.Nonempty ↔ s.Nontrivial
  proof: by
  simp [offDiag, Set.Nonempty, Set.Nontrivial]

@[simp]

中文:
定理 offDiag_nonempty
  结论: s.offDiag.Nonempty ↔ s.Nontrivial
  证明: by
  simp [offDiag, Set.Nonempty, Set.Nontrivial]

@[simp]

Depends on / 依赖: Nonempty, Nontrivial, Set.Nonempty, Set.Nontrivial, offDiag
-/
theorem offDiag_nonempty : s.offDiag.Nonempty ↔ s.Nontrivial := by
  simp [offDiag, Set.Nonempty, Set.Nontrivial]

@[simp]
/--
theorem `offDiag_eq_empty` / 定理 `offDiag_eq_empty`

English:
theorem offDiag_eq_empty
  statement: s.offDiag = ∅ ↔ s.Subsingleton
  proof: by
  rw [← not_nonempty_iff_eq_empty]; rw [← not_nontrivial_iff]; rw [offDiag_nonempty.not]

alias ⟨_, Nontrivial.offDiag_nonempty⟩ := offDiag_nonempty

alias ⟨_, Subsingleton.offDiag_eq_empty⟩ := offDiag_eq_empty

中文:
定理 offDiag_eq_empty
  结论: s.offDiag = ∅ ↔ s.Subsingleton
  证明: by
  rw [← not_nonempty_iff_eq_empty]; rw [← not_nontrivial_iff]; rw [offDiag_nonempty.not]

alias ⟨_, Nontrivial.offDiag_nonempty⟩ := offDiag_nonempty

alias ⟨_, Subsingleton.offDiag_eq_empty⟩ := offDiag_eq_empty

Depends on / 依赖: not_nonempty_iff_eq_empty, not_nontrivial_iff, offDiag_nonempty, offDiag_nonempty.not
-/
theorem offDiag_eq_empty : s.offDiag = ∅ ↔ s.Subsingleton := by
  rw [← not_nonempty_iff_eq_empty]; rw [← not_nontrivial_iff]; rw [offDiag_nonempty.not]

alias ⟨_, Nontrivial.offDiag_nonempty⟩ := offDiag_nonempty

alias ⟨_, Subsingleton.offDiag_eq_empty⟩ := offDiag_eq_empty

variable (s t)

/--
theorem `offDiag_subset_prod` / 定理 `offDiag_subset_prod`

English:
theorem offDiag_subset_prod
  statement: s.offDiag subseteq s ×ˢ s
  proof: fun _ hx => ⟨hx.1, hx.2.1⟩

中文:
定理 offDiag_subset_prod
  结论: s.offDiag subseteq s ×ˢ s
  证明: fun _ hx => ⟨hx.1, hx.2.1⟩
-/
theorem offDiag_subset_prod : s.offDiag subseteq s ×ˢ s := fun _ hx => ⟨hx.1, hx.2.1⟩

/--
theorem `offDiag_eq_sep_prod` / 定理 `offDiag_eq_sep_prod`

English:
theorem offDiag_eq_sep_prod
  statement: s.offDiag = { x in s ×ˢ s | x.1 != x.2 }
  proof: ext fun _ => and_assoc.symm

@[simp]

中文:
定理 offDiag_eq_sep_prod
  结论: s.offDiag = { x in s ×ˢ s | x.1 != x.2 }
  证明: ext fun _ => and_assoc.symm

@[simp]

Depends on / 依赖: and_assoc, and_assoc.symm
-/
theorem offDiag_eq_sep_prod : s.offDiag = { x in s ×ˢ s | x.1 != x.2 } :=
  ext fun _ => and_assoc.symm

@[simp]
/--
theorem `offDiag_empty` / 定理 `offDiag_empty`

English:
theorem offDiag_empty
  statement: (∅ : Set α).offDiag = ∅
  proof: by simp

@[simp]

中文:
定理 offDiag_empty
  结论: (∅ : Set α).offDiag = ∅
  证明: by simp

@[simp]
-/
theorem offDiag_empty : (∅ : Set α).offDiag = ∅ := by simp

@[simp]
/--
theorem `offDiag_singleton` / 定理 `offDiag_singleton`

English:
theorem offDiag_singleton
  given: (a : α)
  statement: ({a} : Set α).offDiag = ∅
  proof: by simp

@[simp]

中文:
定理 offDiag_singleton
  条件: (a : α)
  结论: ({a} : Set α).offDiag = ∅
  证明: by simp

@[simp]
-/
theorem offDiag_singleton (a : α) : ({a} : Set α).offDiag = ∅ := by simp

@[simp]
/--
theorem `offDiag_univ` / 定理 `offDiag_univ`

English:
theorem offDiag_univ
  statement: (univ : Set α).offDiag = (diagonal α)ᶜ
  proof: ext by simp

@[simp]

中文:
定理 offDiag_univ
  结论: (univ : Set α).offDiag = (diagonal α)ᶜ
  证明: ext by simp

@[simp]
-/
theorem offDiag_univ : (univ : Set α).offDiag = (diagonal α)ᶜ :=
ext by simp

@[simp]
/--
theorem `prod_sdiff_diagonal` / 定理 `prod_sdiff_diagonal`

English:
theorem prod_sdiff_diagonal
  statement: s ×ˢ s \ diagonal α = s.offDiag
  proof: ext fun _ => and_assoc

@[simp]

中文:
定理 prod_sdiff_diagonal
  结论: s ×ˢ s \ diagonal α = s.offDiag
  证明: ext fun _ => and_assoc

@[simp]

Depends on / 依赖: and_assoc
-/
theorem prod_sdiff_diagonal : s ×ˢ s \ diagonal α = s.offDiag :=
  ext fun _ => and_assoc

@[simp]
/--
theorem `disjoint_diagonal_offDiag` / 定理 `disjoint_diagonal_offDiag`

English:
theorem disjoint_diagonal_offDiag
  statement: Disjoint (diagonal α) s.offDiag
  proof: disjoint_left.mpr fun _ hd ho => ho.2.2 hd

中文:
定理 disjoint_diagonal_offDiag
  结论: Disjoint (diagonal α) s.offDiag
  证明: disjoint_left.mpr fun _ hd ho => ho.2.2 hd

Depends on / 依赖: disjoint_left, disjoint_left.mpr
-/
theorem disjoint_diagonal_offDiag : Disjoint (diagonal α) s.offDiag :=
  disjoint_left.mpr fun _ hd ho => ho.2.2 hd

/--
theorem `offDiag_inter` / 定理 `offDiag_inter`

English:
theorem offDiag_inter
  statement: (s inter t).offDiag = s.offDiag inter t.offDiag
  proof: ext fun x => by
    simp only [mem_offDiag, mem_inter_iff]
    tauto

中文:
定理 offDiag_inter
  结论: (s inter t).offDiag = s.offDiag inter t.offDiag
  证明: ext fun x => by
    simp only [mem_offDiag, mem_inter_iff]
    tauto

Depends on / 依赖: mem_inter_iff, mem_offDiag
-/
theorem offDiag_inter : (s inter t).offDiag = s.offDiag inter t.offDiag :=
  ext fun x => by
    simp only [mem_offDiag, mem_inter_iff]
    tauto

variable {s t}

/--
theorem `offDiag_union` / 定理 `offDiag_union`

English:
theorem offDiag_union
  given: (h : Disjoint s t)
  proof: by
  ext x
  simp only [mem_offDiag, mem_union, ne_eq, mem_prod]
  constructor
  · rintro ⟨h0 | h0, h1 | h1, h2⟩ <;> simp [h0, h1, h2]
  · rintro (((⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩) | ⟨h0, h1⟩) | ⟨h0, h1⟩) <;>
      simp [*, h.ne_of_mem, Ne.symm]

中文:
定理 offDiag_union
  条件: (h : Disjoint s t)
  证明: by
  ext x
  simp only [mem_offDiag, mem_union, ne_eq, mem_prod]
  constructor
  · rintro ⟨h0 | h0, h1 | h1, h2⟩ <;> simp [h0, h1, h2]
  · rintro (((⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩) | ⟨h0, h1⟩) | ⟨h0, h1⟩) <;>
      simp [*, h.ne_of_mem, Ne.symm]

Depends on / 依赖: Ne.symm, h.ne_of_mem, mem_offDiag, mem_prod, mem_union, ne_eq, ne_of_mem
-/
theorem offDiag_union (h : Disjoint s t) :
    (s union t).offDiag = s.offDiag union t.offDiag union s ×ˢ t union t ×ˢ s := by
  ext x
  simp only [mem_offDiag, mem_union, ne_eq, mem_prod]
  constructor
  · rintro ⟨h0 | h0, h1 | h1, h2⟩ <;> simp [h0, h1, h2]
  · rintro (((⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩) | ⟨h0, h1⟩) | ⟨h0, h1⟩) <;>
      simp [*, h.ne_of_mem, Ne.symm]

/--
theorem `offDiag_insert` / 定理 `offDiag_insert`

English:
theorem offDiag_insert
  given: (ha : a ∉ s)
  statement: (insert a s).offDiag = s.offDiag union {a} ×ˢ s union s ×ˢ {a}
  proof: by
  grind

中文:
定理 offDiag_insert
  条件: (ha : a ∉ s)
  结论: (insert a s).offDiag = s.offDiag union {a} ×ˢ s union s ×ˢ {a}
  证明: by
  grind
-/
theorem offDiag_insert (ha : a ∉ s) : (insert a s).offDiag = s.offDiag union {a} ×ˢ s union s ×ˢ {a} := by
  grind

end OffDiag

/-! ### Cartesian set-indexed product of sets -/


section Pi

variable {ι : Type*} {α β : ι -> Type*} {s s₁ s₂ : Set ι} {t t₁ t₂ : forall i, Set (α i)} {i : ι}

@[simp]
/--
theorem `empty_pi` / 定理 `empty_pi`

English:
theorem empty_pi
  given: (s : forall i, Set (α i))
  statement: pi ∅ s = univ
  proof: by grind

中文:
定理 empty_pi
  条件: (s : 对任意 i, Set (α i))
  结论: pi ∅ s = univ
  证明: by grind
-/
theorem empty_pi (s : forall i, Set (α i)) : pi ∅ s = univ := by grind

/--
theorem `subsingleton_univ_pi` / 定理 `subsingleton_univ_pi`

English:
theorem subsingleton_univ_pi
  given: (ht : forall i, (t i).Subsingleton)
  proof: fun _f hf _g hg => funext fun i =>
  (ht i) (hf _ <| mem_univ _) (hg _ <| mem_univ _)

@[simp]

中文:
定理 subsingleton_univ_pi
  条件: (ht : 对任意 i, (t i).Subsingleton)
  证明: fun _f hf _g hg => funext fun i =>
  (ht i) (hf _ <| mem_univ _) (hg _ <| mem_univ _)

@[simp]
-/
theorem subsingleton_univ_pi (ht : forall i, (t i).Subsingleton) :
    (univ.pi t).Subsingleton := fun _f hf _g hg => funext fun i =>
  (ht i) (hf _ <| mem_univ _) (hg _ <| mem_univ _)

@[simp]
/--
theorem `pi_univ` / 定理 `pi_univ`

English:
theorem pi_univ
  given: (s : Set ι)
  statement: (pi s fun i => (univ : Set (α i))) = univ
  proof: eq_univ_of_forall fun _ _ _ => mem_univ _

@[simp]

中文:
定理 pi_univ
  条件: (s : Set ι)
  结论: (pi s fun i => (univ : Set (α i))) = univ
  证明: eq_univ_of_forall fun _ _ _ => mem_univ _

@[simp]

Depends on / 依赖: eq_univ_of_forall, mem_univ
-/
theorem pi_univ (s : Set ι) : (pi s fun i => (univ : Set (α i))) = univ :=
  eq_univ_of_forall fun _ _ _ => mem_univ _

@[simp]
/--
theorem `pi_univ_ite` / 定理 `pi_univ_ite`

English:
theorem pi_univ_ite
  given: (s : Set ι) [DecidablePred (· in s)] (t : forall i, Set (α i))
  proof: by grind

@[gcongr]

中文:
定理 pi_univ_ite
  条件: (s : Set ι) [DecidablePred (· in s)] (t : 对任意 i, Set (α i))
  证明: by grind

@[gcongr]
-/
theorem pi_univ_ite (s : Set ι) [DecidablePred (· in s)] (t : forall i, Set (α i)) :
    (pi univ fun i => if i in s then t i else univ) = s.pi t := by grind

@[gcongr]
/--
theorem `pi_mono'` / 定理 `pi_mono'`

English:
theorem pi_mono'
  given: (h : forall i in s₂, t₁ i subseteq t₂ i) (h' : s₂ subseteq s₁)
  statement: pi s₁ t₁ subseteq pi s₂ t₂
  proof: fun _ hx i hi => h i hi (hx i (h' hi))

中文:
定理 pi_mono'
  条件: (h : 对任意 i in s₂, t₁ i subseteq t₂ i) (h' : s₂ subseteq s₁)
  结论: pi s₁ t₁ subseteq pi s₂ t₂
  证明: fun _ hx i hi => h i hi (hx i (h' hi))
-/
theorem pi_mono' (h : forall i in s₂, t₁ i subseteq t₂ i) (h' : s₂ subseteq s₁) : pi s₁ t₁ subseteq pi s₂ t₂ :=
  fun _ hx i hi => h i hi (hx i (h' hi))

/--
theorem `pi_mono` / 定理 `pi_mono`

English:
theorem pi_mono
  given: (h : forall i in s, t₁ i subseteq t₂ i)
  statement: pi s t₁ subseteq pi s t₂
  proof: pi_mono' h Subset.rfl

中文:
定理 pi_mono
  条件: (h : 对任意 i in s, t₁ i subseteq t₂ i)
  结论: pi s t₁ subseteq pi s t₂
  证明: pi_mono' h Subset.rfl

Depends on / 依赖: Subset, Subset.rfl, pi_mono
-/
theorem pi_mono (h : forall i in s, t₁ i subseteq t₂ i) : pi s t₁ subseteq pi s t₂ := pi_mono' h Subset.rfl

/--
theorem `pi_inter_distrib` / 定理 `pi_inter_distrib`

English:
theorem pi_inter_distrib
  statement: (s.pi fun i => t i inter t₁ i) = s.pi t inter s.pi t₁
  proof: by grind

中文:
定理 pi_inter_distrib
  结论: (s.pi fun i => t i inter t₁ i) = s.pi t inter s.pi t₁
  证明: by grind
-/
theorem pi_inter_distrib : (s.pi fun i => t i inter t₁ i) = s.pi t inter s.pi t₁ := by grind

/--
theorem `pi_congr` / 定理 `pi_congr`

English:
theorem pi_congr
  given: (h : s₁ = s₂) (h' : forall i in s₁, t₁ i = t₂ i)
  statement: s₁.pi t₁ = s₂.pi t₂
  proof: by grind

中文:
定理 pi_congr
  条件: (h : s₁ = s₂) (h' : 对任意 i in s₁, t₁ i = t₂ i)
  结论: s₁.pi t₁ = s₂.pi t₂
  证明: by grind
-/
theorem pi_congr (h : s₁ = s₂) (h' : forall i in s₁, t₁ i = t₂ i) : s₁.pi t₁ = s₂.pi t₂ := by grind

/--
theorem `pi_eq_empty` / 定理 `pi_eq_empty`

English:
theorem pi_eq_empty
  given: (hs : i in s) (ht : t i = ∅)
  statement: s.pi t = ∅
  proof: by grind

中文:
定理 pi_eq_empty
  条件: (hs : i in s) (ht : t i = ∅)
  结论: s.pi t = ∅
  证明: by grind
-/
theorem pi_eq_empty (hs : i in s) (ht : t i = ∅) : s.pi t = ∅ := by grind

/--
theorem `univ_pi_eq_empty` / 定理 `univ_pi_eq_empty`

English:
theorem univ_pi_eq_empty
  given: (ht : t i = ∅)
  statement: pi univ t = ∅
  proof: pi_eq_empty (mem_univ i) ht

中文:
定理 univ_pi_eq_empty
  条件: (ht : t i = ∅)
  结论: pi univ t = ∅
  证明: pi_eq_empty (mem_univ i) ht

Depends on / 依赖: mem_univ, pi_eq_empty
-/
theorem univ_pi_eq_empty (ht : t i = ∅) : pi univ t = ∅ :=
  pi_eq_empty (mem_univ i) ht

/--
theorem `pi_nonempty_iff` / 定理 `pi_nonempty_iff`

English:
theorem pi_nonempty_iff
  statement: (s.pi t).Nonempty ↔ forall i, exists x, i in s -> x in t i
  proof: by
  simp [Classical.skolem, Set.Nonempty]

中文:
定理 pi_nonempty_iff
  结论: (s.pi t).Nonempty ↔ 对任意 i, 存在 x, i in s -> x in t i
  证明: by
  simp [Classical.skolem, Set.Nonempty]

Depends on / 依赖: Classical, Classical.skolem, Nonempty, Set.Nonempty, skolem
-/
theorem pi_nonempty_iff : (s.pi t).Nonempty ↔ forall i, exists x, i in s -> x in t i := by
  simp [Classical.skolem, Set.Nonempty]

/--
theorem `univ_pi_nonempty_iff` / 定理 `univ_pi_nonempty_iff`

English:
theorem univ_pi_nonempty_iff
  statement: (pi univ t).Nonempty ↔ forall i, (t i).Nonempty
  proof: by
  simp [Classical.skolem, Set.Nonempty]

中文:
定理 univ_pi_nonempty_iff
  结论: (pi univ t).Nonempty ↔ 对任意 i, (t i).Nonempty
  证明: by
  simp [Classical.skolem, Set.Nonempty]

Depends on / 依赖: Classical, Classical.skolem, Nonempty, Set.Nonempty, skolem
-/
theorem univ_pi_nonempty_iff : (pi univ t).Nonempty ↔ forall i, (t i).Nonempty := by
  simp [Classical.skolem, Set.Nonempty]

/--
theorem `pi_eq_empty_iff` / 定理 `pi_eq_empty_iff`

English:
theorem pi_eq_empty_iff
  statement: s.pi t = ∅ ↔ exists i, IsEmpty (α i) ∨ i in s ∧ t i = ∅
  proof: by
  rw [← not_nonempty_iff_eq_empty]; rw [pi_nonempty_iff]
  push Not
  refine exists_congr fun i => ?_
  cases isEmpty_or_nonempty (α i) <;> simp [*, forall_and, eq_empty_iff_forall_notMem]

@[simp]

中文:
定理 pi_eq_empty_iff
  结论: s.pi t = ∅ ↔ 存在 i, IsEmpty (α i) ∨ i in s ∧ t i = ∅
  证明: by
  rw [← not_nonempty_iff_eq_empty]; rw [pi_nonempty_iff]
  push Not
  refine exists_congr fun i => ?_
  cases isEmpty_or_nonempty (α i) <;> simp [*, forall_and, eq_empty_iff_forall_notMem]

@[simp]

Depends on / 依赖: eq_empty_iff_forall_notMem, exists_congr, forall_and, isEmpty_or_nonempty, not_nonempty_iff_eq_empty, pi_nonempty_iff
-/
theorem pi_eq_empty_iff : s.pi t = ∅ ↔ exists i, IsEmpty (α i) ∨ i in s ∧ t i = ∅ := by
  rw [← not_nonempty_iff_eq_empty]; rw [pi_nonempty_iff]
  push Not
  refine exists_congr fun i => ?_
  cases isEmpty_or_nonempty (α i) <;> simp [*, forall_and, eq_empty_iff_forall_notMem]

@[simp]
/--
theorem `univ_pi_eq_empty_iff` / 定理 `univ_pi_eq_empty_iff`

English:
theorem univ_pi_eq_empty_iff
  statement: pi univ t = ∅ ↔ exists i, t i = ∅
  proof: by
  simp [← not_nonempty_iff_eq_empty, univ_pi_nonempty_iff]

@[simp]

中文:
定理 univ_pi_eq_empty_iff
  结论: pi univ t = ∅ ↔ 存在 i, t i = ∅
  证明: by
  simp [← not_nonempty_iff_eq_empty, univ_pi_nonempty_iff]

@[simp]

Depends on / 依赖: not_nonempty_iff_eq_empty, univ_pi_nonempty_iff
-/
theorem univ_pi_eq_empty_iff : pi univ t = ∅ ↔ exists i, t i = ∅ := by
  simp [← not_nonempty_iff_eq_empty, univ_pi_nonempty_iff]

@[simp]
/--
theorem `univ_pi_empty` / 定理 `univ_pi_empty`

English:
theorem univ_pi_empty
  given: [h : Nonempty ι]
  statement: pi univ (fun _ => ∅ : forall i, Set (α i)) = ∅
  proof: univ_pi_eq_empty_iff.2 h.elim fun x => ⟨x, rfl⟩

@[simp]

中文:
定理 univ_pi_empty
  条件: [h : Nonempty ι]
  结论: pi univ (fun _ => ∅ : 对任意 i, Set (α i)) = ∅
  证明: univ_pi_eq_empty_iff.2 h.elim fun x => ⟨x, rfl⟩

@[simp]

Depends on / 依赖: h.elim, univ_pi_eq_empty_iff
-/
theorem univ_pi_empty [h : Nonempty ι] : pi univ (fun _ => ∅ : forall i, Set (α i)) = ∅ :=
univ_pi_eq_empty_iff.2 h.elim fun x => ⟨x, rfl⟩

@[simp]
/--
theorem `disjoint_univ_pi` / 定理 `disjoint_univ_pi`

English:
theorem disjoint_univ_pi
  statement: Disjoint (pi univ t₁) (pi univ t₂) ↔ exists i, Disjoint (t₁ i) (t₂ i)
  proof: by
  simp only [disjoint_iff_inter_eq_empty, ← pi_inter_distrib, univ_pi_eq_empty_iff]

中文:
定理 disjoint_univ_pi
  结论: Disjoint (pi univ t₁) (pi univ t₂) ↔ 存在 i, Disjoint (t₁ i) (t₂ i)
  证明: by
  simp only [disjoint_iff_inter_eq_empty, ← pi_inter_distrib, univ_pi_eq_empty_iff]

Depends on / 依赖: disjoint_iff_inter_eq_empty, pi_inter_distrib, univ_pi_eq_empty_iff
-/
theorem disjoint_univ_pi : Disjoint (pi univ t₁) (pi univ t₂) ↔ exists i, Disjoint (t₁ i) (t₂ i) := by
  simp only [disjoint_iff_inter_eq_empty, ← pi_inter_distrib, univ_pi_eq_empty_iff]

/--
theorem `Disjoint.set_pi` / 定理 `Disjoint.set_pi`

English:
theorem Disjoint.set_pi
  given: (hi : i in s) (ht : Disjoint (t₁ i) (t₂ i))
  statement: Disjoint (s.pi t₁) (s.pi t₂)
  proof: disjoint_left.2 fun _ h₁ h₂ => disjoint_left.1 ht (h₁ _ hi) (h₂ _ hi)

中文:
定理 Disjoint.set_pi
  条件: (hi : i in s) (ht : Disjoint (t₁ i) (t₂ i))
  结论: Disjoint (s.pi t₁) (s.pi t₂)
  证明: disjoint_left.2 fun _ h₁ h₂ => disjoint_left.1 ht (h₁ _ hi) (h₂ _ hi)

Depends on / 依赖: disjoint_left
-/
theorem Disjoint.set_pi (hi : i in s) (ht : Disjoint (t₁ i) (t₂ i)) : Disjoint (s.pi t₁) (s.pi t₂) :=
  disjoint_left.2 fun _ h₁ h₂ => disjoint_left.1 ht (h₁ _ hi) (h₂ _ hi)

/--
theorem `uniqueElim_preimage` / 定理 `uniqueElim_preimage`

English:
theorem uniqueElim_preimage
  given: [Unique ι] (t : forall i, Set (α i))
  proof: by ext; simp [Unique.forall_iff]

中文:
定理 uniqueElim_preimage
  条件: [Unique ι] (t : 对任意 i, Set (α i))
  证明: by ext; simp [Unique.forall_iff]

Depends on / 依赖: Unique, Unique.forall_iff, forall_iff
-/
theorem uniqueElim_preimage [Unique ι] (t : forall i, Set (α i)) :
    uniqueElim ⁻¹' pi univ t = t (default : ι) := by ext; simp [Unique.forall_iff]

section Nonempty

variable [forall i, Nonempty (α i)]

/--
theorem `pi_eq_empty_iff'` / 定理 `pi_eq_empty_iff'`

English:
theorem pi_eq_empty_iff'
  statement: s.pi t = ∅ ↔ exists i in s, t i = ∅
  proof: by simp [pi_eq_empty_iff]

@[simp]

中文:
定理 pi_eq_empty_iff'
  结论: s.pi t = ∅ ↔ 存在 i in s, t i = ∅
  证明: by simp [pi_eq_empty_iff]

@[simp]

Depends on / 依赖: pi_eq_empty_iff
-/
theorem pi_eq_empty_iff' : s.pi t = ∅ ↔ exists i in s, t i = ∅ := by simp [pi_eq_empty_iff]

@[simp]
/--
theorem `disjoint_pi` / 定理 `disjoint_pi`

English:
theorem disjoint_pi
  statement: Disjoint (s.pi t₁) (s.pi t₂) ↔ exists i in s, Disjoint (t₁ i) (t₂ i)
  proof: by
  simp only [disjoint_iff_inter_eq_empty, ← pi_inter_distrib, pi_eq_empty_iff']

中文:
定理 disjoint_pi
  结论: Disjoint (s.pi t₁) (s.pi t₂) ↔ 存在 i in s, Disjoint (t₁ i) (t₂ i)
  证明: by
  simp only [disjoint_iff_inter_eq_empty, ← pi_inter_distrib, pi_eq_empty_iff']

Depends on / 依赖: disjoint_iff_inter_eq_empty, pi_eq_empty_iff, pi_inter_distrib
-/
theorem disjoint_pi : Disjoint (s.pi t₁) (s.pi t₂) ↔ exists i in s, Disjoint (t₁ i) (t₂ i) := by
  simp only [disjoint_iff_inter_eq_empty, ← pi_inter_distrib, pi_eq_empty_iff']

end Nonempty

@[simp]
/--
theorem `insert_pi` / 定理 `insert_pi`

English:
theorem insert_pi
  given: (i : ι) (s : Set ι) (t : forall i, Set (α i))
  proof: by grind

@[simp]

中文:
定理 insert_pi
  条件: (i : ι) (s : Set ι) (t : 对任意 i, Set (α i))
  证明: by grind

@[simp]
-/
theorem insert_pi (i : ι) (s : Set ι) (t : forall i, Set (α i)) :
    pi (insert i s) t = eval i ⁻¹' t i inter pi s t := by grind

@[simp]
/--
theorem `singleton_pi` / 定理 `singleton_pi`

English:
theorem singleton_pi
  given: (i : ι) (t : forall i, Set (α i))
  statement: pi {i} t = eval i ⁻¹' t i
  proof: by grind

中文:
定理 singleton_pi
  条件: (i : ι) (t : 对任意 i, Set (α i))
  结论: pi {i} t = eval i ⁻¹' t i
  证明: by grind
-/
theorem singleton_pi (i : ι) (t : forall i, Set (α i)) : pi {i} t = eval i ⁻¹' t i := by grind

/--
theorem `singleton_pi'` / 定理 `singleton_pi'`

English:
theorem singleton_pi'
  given: (i : ι) (t : forall i, Set (α i))
  statement: pi {i} t = { x | x i in t i }
  proof: singleton_pi i t

中文:
定理 singleton_pi'
  条件: (i : ι) (t : 对任意 i, Set (α i))
  结论: pi {i} t = { x | x i in t i }
  证明: singleton_pi i t

Depends on / 依赖: singleton_pi
-/
theorem singleton_pi' (i : ι) (t : forall i, Set (α i)) : pi {i} t = { x | x i in t i } :=
  singleton_pi i t

/--
theorem `univ_pi_singleton` / 定理 `univ_pi_singleton`

English:
theorem univ_pi_singleton
  given: (f : forall i, α i)
  statement: (pi univ fun i => {f i}) = ({f} : Set (forall i, α i))
  proof: ext fun g => by simp [funext_iff]

中文:
定理 univ_pi_singleton
  条件: (f : 对任意 i, α i)
  结论: (pi univ fun i => {f i}) = ({f} : Set (对任意 i, α i))
  证明: ext fun g => by simp [funext_iff]

Depends on / 依赖: funext_iff
-/
theorem univ_pi_singleton (f : forall i, α i) : (pi univ fun i => {f i}) = ({f} : Set (forall i, α i)) :=
  ext fun g => by simp [funext_iff]

/--
theorem `preimage_pi` / 定理 `preimage_pi`

English:
theorem preimage_pi
  given: (s : Set ι) (t : forall i, Set (β i)) (f : forall i, α i -> β i)
  proof: rfl

中文:
定理 preimage_pi
  条件: (s : Set ι) (t : 对任意 i, Set (β i)) (f : 对任意 i, α i -> β i)
  证明: rfl
-/
theorem preimage_pi (s : Set ι) (t : forall i, Set (β i)) (f : forall i, α i -> β i) :
    (fun (g : forall i, α i) i => f _ (g i)) ⁻¹' s.pi t = s.pi fun i => f i ⁻¹' t i :=
  rfl

/--
theorem `pi_if` / 定理 `pi_if`

English:
theorem pi_if
  given: {p : ι -> Prop} [h : DecidablePred p] (s : Set ι) (t₁ t₂ : forall i, Set (α i))
  proof: by
  ext f
  refine ⟨fun h => ?_, ?_⟩
  · constructor <;>
      · rintro i ⟨his, hpi⟩
        simpa [*] using h i
  · rintro ⟨ht₁, ht₂⟩ i his
    by_cases p i <;> simp_all

中文:
定理 pi_if
  条件: {p : ι -> 命题} [h : DecidablePred p] (s : Set ι) (t₁ t₂ : 对任意 i, Set (α i))
  证明: by
  ext f
  refine ⟨fun h => ?_, ?_⟩
  · constructor <;>
      · rintro i ⟨his, hpi⟩
        simpa [*] using h i
  · rintro ⟨ht₁, ht₂⟩ i his
    by_cases p i <;> simp_all
-/
theorem pi_if {p : ι -> Prop} [h : DecidablePred p] (s : Set ι) (t₁ t₂ : forall i, Set (α i)) :
    (pi s fun i => if p i then t₁ i else t₂ i) =
      pi ({ i in s | p i }) t₁ inter pi ({ i in s | ¬p i }) t₂ := by
  ext f
  refine ⟨fun h => ?_, ?_⟩
  · constructor <;>
      · rintro i ⟨his, hpi⟩
        simpa [*] using h i
  · rintro ⟨ht₁, ht₂⟩ i his
    by_cases p i <;> simp_all

/--
theorem `union_pi` / 定理 `union_pi`

English:
theorem union_pi
  statement: (s₁ union s₂).pi t = s₁.pi t inter s₂.pi t
  proof: by
  simp [pi, or_imp, forall_and, ofPred_and]

中文:
定理 union_pi
  结论: (s₁ union s₂).pi t = s₁.pi t inter s₂.pi t
  证明: by
  simp [pi, or_imp, forall_and, ofPred_and]

Depends on / 依赖: forall_and, ofPred_and, or_imp
-/
theorem union_pi : (s₁ union s₂).pi t = s₁.pi t inter s₂.pi t := by
  simp [pi, or_imp, forall_and, ofPred_and]

/--
theorem `union_pi_inter` / 定理 `union_pi_inter`

English:
theorem union_pi_inter
  proof: by
  grind

@[simp]

中文:
定理 union_pi_inter
  证明: by
  grind

@[simp]
-/
theorem union_pi_inter
    (ht₁ : forall i ∉ s₁, t₁ i = univ) (ht₂ : forall i ∉ s₂, t₂ i = univ) :
    (s₁ union s₂).pi (fun i => t₁ i inter t₂ i) = s₁.pi t₁ inter s₂.pi t₂ := by
  grind

@[simp]
/--
theorem `pi_inter_compl` / 定理 `pi_inter_compl`

English:
theorem pi_inter_compl
  given: (s : Set ι)
  statement: pi s t inter pi sᶜ t = pi univ t
  proof: by grind

中文:
定理 pi_inter_compl
  条件: (s : Set ι)
  结论: pi s t inter pi sᶜ t = pi univ t
  证明: by grind
-/
theorem pi_inter_compl (s : Set ι) : pi s t inter pi sᶜ t = pi univ t := by grind

/--
theorem `pi_update_of_notMem` / 定理 `pi_update_of_notMem`

English:
theorem pi_update_of_notMem
  statement: [DecidableEq ι] (hi : i ∉ s) (f : forall j, α j) (a : α i)
  proof: (pi_congr rfl) fun j hj => by
    rw [update_of_ne]
    exact fun h => hi (h ▸ hj)

中文:
定理 pi_update_of_notMem
  结论: [DecidableEq ι] (hi : i ∉ s) (f : 对任意 j, α j) (a : α i)
  证明: (pi_congr rfl) fun j hj => by
    rw [update_of_ne]
    exact fun h => hi (h ▸ hj)

Depends on / 依赖: pi_congr, update_of_ne
-/
theorem pi_update_of_notMem [DecidableEq ι] (hi : i ∉ s) (f : forall j, α j) (a : α i)
    (t : forall j, α j -> Set (β j)) : (s.pi fun j => t j (update f i a j)) = s.pi fun j => t j (f j) :=
  (pi_congr rfl) fun j hj => by
    rw [update_of_ne]
    exact fun h => hi (h ▸ hj)

/--
theorem `pi_update_of_mem` / 定理 `pi_update_of_mem`

English:
theorem pi_update_of_mem
  statement: [DecidableEq ι] (hi : i in s) (f : forall j, α j) (a : α i)
  proof: calc
    (s.pi fun j => t j (update f i a j)) = ({i} union s \ {i}).pi fun j => t j (update f i a j) := by
        rw [union_sdiff_self]; rw [union_eq_self_of_subset_left (singleton_subset_iff.2 hi)]
    _ = { x | x i in t i a } inter (s \ {i}).pi fun j => t j (f j) := by
        rw [union_pi]; rw [

中文:
定理 pi_update_of_mem
  结论: [DecidableEq ι] (hi : i in s) (f : 对任意 j, α j) (a : α i)
  证明: calc
    (s.pi fun j => t j (update f i a j)) = ({i} union s \ {i}).pi fun j => t j (update f i a j) := by
        rw [union_sdiff_self]; rw [union_eq_self_of_subset_left (singleton_subset_iff.2 hi)]
    _ = { x | x i in t i a } inter (s \ {i}).pi fun j => t j (f j) := by
        rw [union_pi]; rw [

Depends on / 依赖: Prod.ext_iff.mp, Subgroup, Subgroup.mul_mem_sup, Subtype, Subtype.ext_iff.mp, codisjoint_iff_le_sup, codisjoint_iff_le_sup.mpr, disjoint_iff_inf_le, disjoint_iff_inf_le.mpr, ext_iff, mul_mem_sup, mul_one, one_mul, pi_update_of_notMem, s.pi, singleton_pi, singleton_subset_iff, union_eq_self_of_subset_left, union_pi, union_sdiff_self
-/
theorem pi_update_of_mem [DecidableEq ι] (hi : i in s) (f : forall j, α j) (a : α i)
    (t : forall j, α j -> Set (β j)) :
    (s.pi fun j => t j (update f i a j)) = { x | x i in t i a } inter (s \ {i}).pi fun j => t j (f j) :=
  calc
    (s.pi fun j => t j (update f i a j)) = ({i} union s \ {i}).pi fun j => t j (update f i a j) := by
        rw [union_sdiff_self]; rw [union_eq_self_of_subset_left (singleton_subset_iff.2 hi)]
    _ = { x | x i in t i a } inter (s \ {i}).pi fun j => t j (f j) := by
        rw [union_pi]; rw [singleton_pi']; rw [update_self]; rw [pi_update_of_notMem]; simp

/--
theorem `univ_pi_update` / 定理 `univ_pi_update`

English:
theorem univ_pi_update
  statement: [DecidableEq ι] {β : ι -> Type*} (i : ι) (f : forall j, α j) (a : α i)
  proof: by
  rw [compl_eq_univ_sdiff]; rw [← pi_update_of_mem (mem_univ _)]

中文:
定理 univ_pi_update
  结论: [DecidableEq ι] {β : ι -> 类型} (i : ι) (f : 对任意 j, α j) (a : α i)
  证明: by
  rw [compl_eq_univ_sdiff]; rw [← pi_update_of_mem (mem_univ _)]

Depends on / 依赖: compl_eq_univ_sdiff, h.isCompl.sup_eq_top, isCompl, mem_univ, pi_update_of_mem, sup_eq_top
-/
theorem univ_pi_update [DecidableEq ι] {β : ι -> Type*} (i : ι) (f : forall j, α j) (a : α i)
    (t : forall j, α j -> Set (β j)) :
    (pi univ fun j => t j (update f i a j)) = { x | x i in t i a } inter pi {i}ᶜ fun j => t j (f j) := by
  rw [compl_eq_univ_sdiff]; rw [← pi_update_of_mem (mem_univ _)]

/--
theorem `univ_pi_update_univ` / 定理 `univ_pi_update_univ`

English:
theorem univ_pi_update_univ
  given: [DecidableEq ι] (i : ι) (s : Set (α i))
  proof: by
  rw [univ_pi_update i (fun j => (univ : Set (α j))) s fun j t => t]; rw [pi_univ]; rw [inter_univ]; rw [preimage]

中文:
定理 univ_pi_update_univ
  条件: [DecidableEq ι] (i : ι) (s : Set (α i))
  证明: by
  rw [univ_pi_update i (fun j => (univ : Set (α j))) s fun j t => t]; rw [pi_univ]; rw [inter_univ]; rw [preimage]

Depends on / 依赖: disjoint, h.isCompl.disjoint, inter_univ, isCompl, pi_univ, preimage, univ_pi_update
-/
theorem univ_pi_update_univ [DecidableEq ι] (i : ι) (s : Set (α i)) :
    pi univ (update (fun j : ι => (univ : Set (α j))) i s) = eval i ⁻¹' s := by
  rw [univ_pi_update i (fun j => (univ : Set (α j))) s fun j t => t]; rw [pi_univ]; rw [inter_univ]; rw [preimage]

/--
theorem `eval_image_pi_subset` / 定理 `eval_image_pi_subset`

English:
theorem eval_image_pi_subset
  given: (hs : i in s)
  statement: eval i '' s.pi t subseteq t i
  proof: image_subset_iff.2 fun _ hf => hf i hs

中文:
定理 eval_image_pi_subset
  条件: (hs : i in s)
  结论: eval i '' s.pi t subseteq t i
  证明: image_subset_iff.2 fun _ hf => hf i hs

Depends on / 依赖: card_left, h.card_left.symm, image_subset_iff
-/
theorem eval_image_pi_subset (hs : i in s) : eval i '' s.pi t subseteq t i :=
  image_subset_iff.2 fun _ hf => hf i hs

/--
theorem `eval_image_univ_pi_subset` / 定理 `eval_image_univ_pi_subset`

English:
theorem eval_image_univ_pi_subset
  statement: eval i '' pi univ t subseteq t i
  proof: eval_image_pi_subset (mem_univ i)

中文:
定理 eval_image_univ_pi_subset
  结论: eval i '' pi univ t subseteq t i
  证明: eval_image_pi_subset (mem_univ i)

Depends on / 依赖: MulEquiv, MulEquiv.symm, eval_image_pi_subset, h.leftQuotientEquiv.symm, leftQuotientEquiv, map_mul, mem_univ
-/
theorem eval_image_univ_pi_subset : eval i '' pi univ t subseteq t i :=
  eval_image_pi_subset (mem_univ i)

/--
theorem `subset_eval_image_pi` / 定理 `subset_eval_image_pi`

English:
theorem subset_eval_image_pi
  given: (ht : (s.pi t).Nonempty) (i : ι)
  statement: t i subseteq eval i '' s.pi t
  proof: by
  classical
  obtain ⟨f, hf⟩ := ht
  refine fun y hy => ⟨update f i y, fun j hj => ?_, update_self ..⟩
  obtain rfl | hji := eq_or_ne j i <;> simp [*, hf _ hj]

中文:
定理 subset_eval_image_pi
  条件: (ht : (s.pi t).Nonempty) (i : ι)
  结论: t i subseteq eval i '' s.pi t
  证明: by
  classical
  obtain ⟨f, hf⟩ := ht
  refine fun y hy => ⟨update f i y, fun j hj => ?_, update_self ..⟩
  obtain rfl | hji := eq_or_ne j i <;> simp [*, hf _ hj]

Depends on / 依赖: IsComplement, IsComplement.card_mul_card, card_mul_card, classical, eq_or_ne, update, update_self
-/
theorem subset_eval_image_pi (ht : (s.pi t).Nonempty) (i : ι) : t i subseteq eval i '' s.pi t := by
  classical
  obtain ⟨f, hf⟩ := ht
  refine fun y hy => ⟨update f i y, fun j hj => ?_, update_self ..⟩
  obtain rfl | hji := eq_or_ne j i <;> simp [*, hf _ hj]

/--
theorem `eval_image_pi` / 定理 `eval_image_pi`

English:
theorem eval_image_pi
  given: (hs : i in s) (ht : (s.pi t).Nonempty)
  statement: eval i '' s.pi t = t i
  proof: (eval_image_pi_subset hs).antisymm (subset_eval_image_pi ht i)

中文:
定理 eval_image_pi
  条件: (hs : i in s) (ht : (s.pi t).Nonempty)
  结论: eval i '' s.pi t = t i
  证明: (eval_image_pi_subset hs).antisymm (subset_eval_image_pi ht i)

Depends on / 依赖: Set.eq_univ_iff_forall.mp, antisymm, eq_univ_iff_forall, eval_image_pi_subset, mul_injective_of_disjoint, subset_eval_image_pi
-/
theorem eval_image_pi (hs : i in s) (ht : (s.pi t).Nonempty) : eval i '' s.pi t = t i :=
  (eval_image_pi_subset hs).antisymm (subset_eval_image_pi ht i)

/--
lemma `eval_image_pi_of_notMem` / 引理 `eval_image_pi_of_notMem`

English:
lemma eval_image_pi_of_notMem
  given: [Decidable (s.pi t).Nonempty] (hi : i ∉ s)
  proof: by
  classical
  ext xᵢ
  simp only [eval, mem_image, mem_pi, Set.Nonempty, mem_ite_empty_right, mem_univ, and_true]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    refine ⟨Function.update x i xᵢ, ?_⟩
    simpa +contextual [(ne_of_mem_of_not_mem · hi)]

@[simp]

中文:
引理 eval_image_pi_of_notMem
  条件: [Decidable (s.pi t).Nonempty] (hi : i ∉ s)
  证明: by
  classical
  ext xᵢ
  simp only [eval, mem_image, mem_pi, Set.Nonempty, mem_ite_empty_right, mem_univ, and_true]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    refine ⟨Function.update x i xᵢ, ?_⟩
    simpa +contextual [(ne_of_mem_of_not_mem · hi)]

@[simp]

Depends on / 依赖: Function, Function.update, Nat.bijective_iff_injective_and_card, Nat.card_prod, Nonempty, Set.Nonempty, and_true, bijective_iff_injective_and_card, card_prod, classical, contextual, mem_image, mem_ite_empty_right, mem_pi, mem_univ, mul_injective_of_disjoint, ne_of_mem_of_not_mem, update
-/
lemma eval_image_pi_of_notMem [Decidable (s.pi t).Nonempty] (hi : i ∉ s) :
    eval i '' s.pi t = if (s.pi t).Nonempty then univ else ∅ := by
  classical
  ext xᵢ
  simp only [eval, mem_image, mem_pi, Set.Nonempty, mem_ite_empty_right, mem_univ, and_true]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    refine ⟨Function.update x i xᵢ, ?_⟩
    simpa +contextual [(ne_of_mem_of_not_mem · hi)]

@[simp]
/--
theorem `eval_image_univ_pi` / 定理 `eval_image_univ_pi`

English:
theorem eval_image_univ_pi
  given: (ht : (pi univ t).Nonempty)
  proof: eval_image_pi (mem_univ i) ht

中文:
定理 eval_image_univ_pi
  条件: (ht : (pi univ t).Nonempty)
  证明: eval_image_pi (mem_univ i) ht

Depends on / 依赖: _of_card_mul_and_disjoint, card_mul_card, disjoint, eval_image_pi, h.card_mul_card, h.disjoint, isComplement, mem_univ
-/
theorem eval_image_univ_pi (ht : (pi univ t).Nonempty) :
    (fun f : forall i, α i => f i) '' pi univ t = t i :=
  eval_image_pi (mem_univ i) ht

/--
theorem `piMap_mapsTo_pi` / 定理 `piMap_mapsTo_pi`

English:
theorem piMap_mapsTo_pi
  statement: {I : Set ι} {f : forall i, α i -> β i} {s : forall i, Set (α i)} {t : forall i, Set (β i)}
  proof: fun _x hx i hi => h i hi (hx i hi)

中文:
定理 piMap_mapsTo_pi
  结论: {I : Set ι} {f : 对任意 i, α i -> β i} {s : 对任意 i, Set (α i)} {t : 对任意 i, Set (β i)}
  证明: fun _x hx i hi => h i hi (hx i hi)

Depends on / 依赖: _of_card_mul_and_disjoint, disjoint_of_coprime_natCard, isComplement
-/
theorem piMap_mapsTo_pi {I : Set ι} {f : forall i, α i -> β i} {s : forall i, Set (α i)} {t : forall i, Set (β i)}
    (h : forall i in I, MapsTo (f i) (s i) (t i)) :
    MapsTo (Pi.map f) (I.pi s) (I.pi t) :=
  fun _x hx i hi => h i hi (hx i hi)

/--
theorem `piMap_image_pi_subset` / 定理 `piMap_image_pi_subset`

English:
theorem piMap_image_pi_subset
  given: {f : forall i, α i -> β i} (t : forall i, Set (α i))
  proof: image_subset_iff.2 piMap_mapsTo_pi fun _ _ => mapsTo_image _ _

中文:
定理 piMap_image_pi_subset
  条件: {f : 对任意 i, α i -> β i} (t : 对任意 i, Set (α i))
  证明: image_subset_iff.2 piMap_mapsTo_pi fun _ _ => mapsTo_image _ _

Depends on / 依赖: Prod.ext, Subtype, Subtype.ext, Subtype.ext_iff, coe_mul, coe_one, eq_inv_of_mul_eq_one_right, ext_iff, image_subset_iff, inv_mul_cancel_left, isComplement_iff_existsUnique, isComplement_iff_existsUnique.mpr, mapsTo_image, mul_assoc, mul_smul, piMap_mapsTo_pi, right_eq_mul, smul_def, specialize
-/
theorem piMap_image_pi_subset {f : forall i, α i -> β i} (t : forall i, Set (α i)) :
    Pi.map f '' s.pi t subseteq s.pi fun i => f i '' t i :=
image_subset_iff.2 piMap_mapsTo_pi fun _ _ => mapsTo_image _ _

/--
theorem `piMap_image_pi` / 定理 `piMap_image_pi`

English:
theorem piMap_image_pi
  given: {f : forall i, α i -> β i} (hf : forall i ∉ s, Surjective (f i)) (t : forall i, Set (α i))
  proof: by
  refine Subset.antisymm (piMap_image_pi_subset _) fun b hb => ?_
  have (i : ι) : exists a, f i a = b i ∧ (i in s -> a in t i) := by
    if hi : i in s then
      exact (hb i hi).imp fun a ⟨hat, hab⟩ => ⟨hab, fun _ => hat⟩
    else
      exact (hf i hi (b i)).imp fun a ha => ⟨ha, (absurd · hi)⟩


中文:
定理 piMap_image_pi
  条件: {f : 对任意 i, α i -> β i} (hf : 对任意 i ∉ s, Surjective (f i)) (t : 对任意 i, Set (α i))
  证明: by
  refine Subset.antisymm (piMap_image_pi_subset _) fun b hb => ?_
  have (i : ι) : exists a, f i a = b i ∧ (i in s -> a in t i) := by
    if hi : i in s then
      exact (hb i hi).imp fun a ⟨hat, hab⟩ => ⟨hab, fun _ => hat⟩
    else
      exact (hf i hi (b i)).imp fun a ha => ⟨ha, (absurd · hi)⟩


Depends on / 依赖: Subset, Subset.antisymm, absurd, antisymm, piMap_image_pi_subset
-/
theorem piMap_image_pi {f : forall i, α i -> β i} (hf : forall i ∉ s, Surjective (f i)) (t : forall i, Set (α i)) :
    Pi.map f '' s.pi t = s.pi fun i => f i '' t i := by
  refine Subset.antisymm (piMap_image_pi_subset _) fun b hb => ?_
  have (i : ι) : exists a, f i a = b i ∧ (i in s -> a in t i) := by
    if hi : i in s then
      exact (hb i hi).imp fun a ⟨hat, hab⟩ => ⟨hab, fun _ => hat⟩
    else
      exact (hf i hi (b i)).imp fun a ha => ⟨ha, (absurd · hi)⟩
  choose a hab hat using this
  exact ⟨a, hat, funext hab⟩

/--
theorem `piMap_image_univ_pi` / 定理 `piMap_image_univ_pi`

English:
theorem piMap_image_univ_pi
  given: (f : forall i, α i -> β i) (t : forall i, Set (α i))
  proof: piMap_image_pi (by simp) t

@[simp]

中文:
定理 piMap_image_univ_pi
  条件: (f : 对任意 i, α i -> β i) (t : 对任意 i, Set (α i))
  证明: piMap_image_pi (by simp) t

@[simp]

Depends on / 依赖: piMap_image_pi
-/
theorem piMap_image_univ_pi (f : forall i, α i -> β i) (t : forall i, Set (α i)) :
    Pi.map f '' univ.pi t = univ.pi fun i => f i '' t i :=
  piMap_image_pi (by simp) t

@[simp]
/--
theorem `range_piMap` / 定理 `range_piMap`

English:
theorem range_piMap
  given: (f : forall i, α i -> β i)
  statement: range (Pi.map f) = pi univ fun i => range (f i)
  proof: by
  simp only [← image_univ, ← piMap_image_univ_pi, pi_univ]

中文:
定理 range_piMap
  条件: (f : 对任意 i, α i -> β i)
  结论: range (Pi.map f) = pi univ fun i => range (f i)
  证明: by
  simp only [← image_univ, ← piMap_image_univ_pi, pi_univ]

Depends on / 依赖: image_univ, piMap_image_univ_pi, pi_univ
-/
theorem range_piMap (f : forall i, α i -> β i) : range (Pi.map f) = pi univ fun i => range (f i) := by
  simp only [← image_univ, ← piMap_image_univ_pi, pi_univ]

/--
theorem `subset_pi_iff` / 定理 `subset_pi_iff`

English:
theorem subset_pi_iff
  given: {s'}
  statement: s' subseteq pi s t ↔ forall i in s, s' subseteq (· i) ⁻¹' t i
  proof: by
  grind

中文:
定理 subset_pi_iff
  条件: {s'}
  结论: s' subseteq pi s t ↔ 对任意 i in s, s' subseteq (· i) ⁻¹' t i
  证明: by
  grind
-/
theorem subset_pi_iff {s'} : s' subseteq pi s t ↔ forall i in s, s' subseteq (· i) ⁻¹' t i := by
  grind

/--
theorem `update_mem_pi_iff` / 定理 `update_mem_pi_iff`

English:
theorem update_mem_pi_iff
  given: [DecidableEq ι] {a : forall i, α i} {i : ι} {b : α i}
  proof: by grind

中文:
定理 update_mem_pi_iff
  条件: [DecidableEq ι] {a : 对任意 i, α i} {i : ι} {b : α i}
  证明: by grind
-/
theorem update_mem_pi_iff [DecidableEq ι] {a : forall i, α i} {i : ι} {b : α i} :
    update a i b in pi s t ↔ a in pi (s \ {i}) t ∧ (i in s -> b in t i) := by grind

/--
theorem `update_mem_pi_iff_of_mem` / 定理 `update_mem_pi_iff_of_mem`

English:
theorem update_mem_pi_iff_of_mem
  statement: [DecidableEq ι] {a : forall i, α i} {i : ι} {b : α i}
  proof: by
  rw [update_mem_pi_iff]; rw [and_iff_right]
  exact fun j hj => ha j hj.1

中文:
定理 update_mem_pi_iff_of_mem
  结论: [DecidableEq ι] {a : 对任意 i, α i} {i : ι} {b : α i}
  证明: by
  rw [update_mem_pi_iff]; rw [and_iff_right]
  exact fun j hj => ha j hj.1

Depends on / 依赖: and_iff_right, update_mem_pi_iff
-/
theorem update_mem_pi_iff_of_mem [DecidableEq ι] {a : forall i, α i} {i : ι} {b : α i}
    (ha : a in pi s t) : update a i b in pi s t ↔ i in s -> b in t i := by
  rw [update_mem_pi_iff]; rw [and_iff_right]
  exact fun j hj => ha j hj.1

/--
theorem `univ_pi_eq_singleton_iff` / 定理 `univ_pi_eq_singleton_iff`

English:
theorem univ_pi_eq_singleton_iff
  given: {a}
  statement: pi univ t = {a} ↔ forall i, t i = {a i}
  proof: by
  classical
  simp only [eq_singleton_iff_unique_mem]
  refine ⟨fun ⟨h₁, h₂⟩ i => ⟨by grind, fun x hx => ?_⟩, by grind⟩
  rw [← h₂ _ fun j _ => (update_mem_pi_iff_of_mem h₁).mpr (fun _ => hx) j trivial]; rw [update_self]

中文:
定理 univ_pi_eq_singleton_iff
  条件: {a}
  结论: pi univ t = {a} ↔ 对任意 i, t i = {a i}
  证明: by
  classical
  simp only [eq_singleton_iff_unique_mem]
  refine ⟨fun ⟨h₁, h₂⟩ i => ⟨by grind, fun x hx => ?_⟩, by grind⟩
  rw [← h₂ _ fun j _ => (update_mem_pi_iff_of_mem h₁).mpr (fun _ => hx) j trivial]; rw [update_self]

Depends on / 依赖: classical, eq_singleton_iff_unique_mem, update_mem_pi_iff_of_mem, update_self
-/
theorem univ_pi_eq_singleton_iff {a} : pi univ t = {a} ↔ forall i, t i = {a i} := by
  classical
  simp only [eq_singleton_iff_unique_mem]
  refine ⟨fun ⟨h₁, h₂⟩ i => ⟨by grind, fun x hx => ?_⟩, by grind⟩
  rw [← h₂ _ fun j _ => (update_mem_pi_iff_of_mem h₁).mpr (fun _ => hx) j trivial]; rw [update_self]

/--
theorem `pi_subset_pi_iff` / 定理 `pi_subset_pi_iff`

English:
theorem pi_subset_pi_iff
  statement: pi s t₁ subseteq pi s t₂ ↔ (forall i in s, t₁ i subseteq t₂ i) ∨ pi s t₁ = ∅
  proof: by
  refine
    ⟨fun h => or_iff_not_imp_right.2 ?_, fun h => h.elim pi_mono fun h' => h'.symm ▸ empty_subset _⟩
  rw [← Ne]; rw [← nonempty_iff_ne_empty]
  intro hne i hi
  simpa only [eval_image_pi hi hne, eval_image_pi hi (hne.mono h)] using
    image_mono (f := fun f : forall i, α i => f i) h

中文:
定理 pi_subset_pi_iff
  结论: pi s t₁ subseteq pi s t₂ ↔ (对任意 i in s, t₁ i subseteq t₂ i) ∨ pi s t₁ = ∅
  证明: by
  refine
    ⟨fun h => or_iff_not_imp_right.2 ?_, fun h => h.elim pi_mono fun h' => h'.symm ▸ empty_subset _⟩
  rw [← Ne]; rw [← nonempty_iff_ne_empty]
  intro hne i hi
  simpa only [eval_image_pi hi hne, eval_image_pi hi (hne.mono h)] using
    image_mono (f := fun f : forall i, α i => f i) h

Depends on / 依赖: empty_subset, eval_image_pi, h.elim, hne.mono, image_mono, nonempty_iff_ne_empty, or_iff_not_imp_right, pi_mono
-/
theorem pi_subset_pi_iff : pi s t₁ subseteq pi s t₂ ↔ (forall i in s, t₁ i subseteq t₂ i) ∨ pi s t₁ = ∅ := by
  refine
    ⟨fun h => or_iff_not_imp_right.2 ?_, fun h => h.elim pi_mono fun h' => h'.symm ▸ empty_subset _⟩
  rw [← Ne]; rw [← nonempty_iff_ne_empty]
  intro hne i hi
  simpa only [eval_image_pi hi hne, eval_image_pi hi (hne.mono h)] using
    image_mono (f := fun f : forall i, α i => f i) h

/--
theorem `univ_pi_subset_univ_pi_iff` / 定理 `univ_pi_subset_univ_pi_iff`

English:
theorem univ_pi_subset_univ_pi_iff
  proof: by simp [pi_subset_pi_iff]

中文:
定理 univ_pi_subset_univ_pi_iff
  证明: by simp [pi_subset_pi_iff]

Depends on / 依赖: pi_subset_pi_iff
-/
theorem univ_pi_subset_univ_pi_iff :
    pi univ t₁ subseteq pi univ t₂ ↔ (forall i, t₁ i subseteq t₂ i) ∨ exists i, t₁ i = ∅ := by simp [pi_subset_pi_iff]

/--
theorem `eval_preimage` / 定理 `eval_preimage`

English:
theorem eval_preimage
  given: [DecidableEq ι] {s : Set (α i)}
  proof: by
  ext x
  simp [@forall_update_iff _ (fun i => Set (α i)) _ _ _ _ fun i' y => x i' in y]

中文:
定理 eval_preimage
  条件: [DecidableEq ι] {s : Set (α i)}
  证明: by
  ext x
  simp [@forall_update_iff _ (fun i => Set (α i)) _ _ _ _ fun i' y => x i' in y]

Depends on / 依赖: forall_update_iff
-/
theorem eval_preimage [DecidableEq ι] {s : Set (α i)} :
    eval i ⁻¹' s = pi univ (update (fun _ => univ) i s) := by
  ext x
  simp [@forall_update_iff _ (fun i => Set (α i)) _ _ _ _ fun i' y => x i' in y]

/--
theorem `eval_preimage'` / 定理 `eval_preimage'`

English:
theorem eval_preimage'
  given: [DecidableEq ι] {s : Set (α i)}
  proof: by
  ext
  simp

中文:
定理 eval_preimage'
  条件: [DecidableEq ι] {s : Set (α i)}
  证明: by
  ext
  simp
-/
theorem eval_preimage' [DecidableEq ι] {s : Set (α i)} :
    eval i ⁻¹' s = pi {i} (update (fun _ => univ) i s) := by
  ext
  simp

/--
theorem `update_preimage_pi` / 定理 `update_preimage_pi`

English:
theorem update_preimage_pi
  statement: [DecidableEq ι] {f : forall i, α i} (hi : i in s)
  proof: by
  ext x
  refine ⟨fun h => ?_, fun hx j hj => ?_⟩
  · convert! h i hi
    simp
  · obtain rfl | h := eq_or_ne j i
    · simpa
    · rw [update_of_ne h]
      exact hf j hj h

中文:
定理 update_preimage_pi
  结论: [DecidableEq ι] {f : 对任意 i, α i} (hi : i in s)
  证明: by
  ext x
  refine ⟨fun h => ?_, fun hx j hj => ?_⟩
  · convert! h i hi
    simp
  · obtain rfl | h := eq_or_ne j i
    · simpa
    · rw [update_of_ne h]
      exact hf j hj h

Depends on / 依赖: convert, eq_or_ne, update_of_ne
-/
theorem update_preimage_pi [DecidableEq ι] {f : forall i, α i} (hi : i in s)
    (hf : forall j in s, j != i -> f j in t j) : update f i ⁻¹' s.pi t = t i := by
  ext x
  refine ⟨fun h => ?_, fun hx j hj => ?_⟩
  · convert! h i hi
    simp
  · obtain rfl | h := eq_or_ne j i
    · simpa
    · rw [update_of_ne h]
      exact hf j hj h

/--
theorem `update_image` / 定理 `update_image`

English:
theorem update_image
  given: [DecidableEq ι] (x : (i : ι) -> β i) (i : ι) (s : Set (β i))
  proof: by
  ext y
  simp only [mem_image, update_eq_iff, ne_eq, and_left_comm (a := _ in s), exists_eq_left, mem_pi,
    mem_univ, true_implies]
  rw [forall_update_iff (p := fun x s => y x in s)]
  simp [eq_comm]

中文:
定理 update_image
  条件: [DecidableEq ι] (x : (i : ι) -> β i) (i : ι) (s : Set (β i))
  证明: by
  ext y
  simp only [mem_image, update_eq_iff, ne_eq, and_left_comm (a := _ in s), exists_eq_left, mem_pi,
    mem_univ, true_implies]
  rw [forall_update_iff (p := fun x s => y x in s)]
  simp [eq_comm]

Depends on / 依赖: and_left_comm, eq_comm, exists_eq_left, forall_update_iff, mem_image, mem_pi, mem_univ, ne_eq, true_implies, update_eq_iff
-/
theorem update_image [DecidableEq ι] (x : (i : ι) -> β i) (i : ι) (s : Set (β i)) :
    update x i '' s = Set.univ.pi (update (fun j => {x j}) i s) := by
  ext y
  simp only [mem_image, update_eq_iff, ne_eq, and_left_comm (a := _ in s), exists_eq_left, mem_pi,
    mem_univ, true_implies]
  rw [forall_update_iff (p := fun x s => y x in s)]
  simp [eq_comm]

/--
theorem `update_preimage_univ_pi` / 定理 `update_preimage_univ_pi`

English:
theorem update_preimage_univ_pi
  given: [DecidableEq ι] {f : forall i, α i} (hf : forall j != i, f j in t j)
  proof: update_preimage_pi (mem_univ i) fun j _ => hf j

中文:
定理 update_preimage_univ_pi
  条件: [DecidableEq ι] {f : 对任意 i, α i} (hf : 对任意 j != i, f j in t j)
  证明: update_preimage_pi (mem_univ i) fun j _ => hf j

Depends on / 依赖: mem_univ, update_preimage_pi
-/
theorem update_preimage_univ_pi [DecidableEq ι] {f : forall i, α i} (hf : forall j != i, f j in t j) :
    update f i ⁻¹' pi univ t = t i :=
  update_preimage_pi (mem_univ i) fun j _ => hf j

/--
theorem `subset_pi_eval_image` / 定理 `subset_pi_eval_image`

English:
theorem subset_pi_eval_image
  given: (s : Set ι) (u : Set (forall i, α i))
  statement: u subseteq pi s fun i => eval i '' u
  proof: fun f hf _ _ => ⟨f, hf, rfl⟩

中文:
定理 subset_pi_eval_image
  条件: (s : Set ι) (u : Set (对任意 i, α i))
  结论: u subseteq pi s fun i => eval i '' u
  证明: fun f hf _ _ => ⟨f, hf, rfl⟩
-/
theorem subset_pi_eval_image (s : Set ι) (u : Set (forall i, α i)) : u subseteq pi s fun i => eval i '' u :=
  fun f hf _ _ => ⟨f, hf, rfl⟩

/--
theorem `univ_pi_ite` / 定理 `univ_pi_ite`

English:
theorem univ_pi_ite
  given: (s : Set ι) [DecidablePred (· in s)] (t : forall i, Set (α i))
  proof: by grind

中文:
定理 univ_pi_ite
  条件: (s : Set ι) [DecidablePred (· in s)] (t : 对任意 i, Set (α i))
  证明: by grind
-/
theorem univ_pi_ite (s : Set ι) [DecidablePred (· in s)] (t : forall i, Set (α i)) :
    (pi univ fun i => if i in s then t i else univ) = s.pi t := by grind

/--
lemma `uncurry_preimage_prod_pi` / 引理 `uncurry_preimage_prod_pi`

English:
lemma uncurry_preimage_prod_pi
  given: {κ α : Type*} (s : Set ι) (t : Set κ) (u : ι × κ -> Set α)
  proof: by grind

中文:
引理 uncurry_preimage_prod_pi
  条件: {κ α : 类型} (s : Set ι) (t : Set κ) (u : ι × κ -> Set α)
  证明: by grind
-/
lemma uncurry_preimage_prod_pi {κ α : Type*} (s : Set ι) (t : Set κ) (u : ι × κ -> Set α) :
    Function.uncurry ⁻¹' (s ×ˢ t).pi u = s.pi (fun i => t.pi fun j => u ⟨i, j⟩) := by grind

end Pi

end Set

namespace Equiv

open Set
variable {ι ι' : Type*} {α : ι -> Type*}

/--
theorem `piCongrLeft_symm_preimage_pi` / 定理 `piCongrLeft_symm_preimage_pi`

English:
theorem piCongrLeft_symm_preimage_pi
  given: (f : ι' ≃ ι) (s : Set ι') (t : forall i, Set (α i))
  proof: by
  ext; simp

中文:
定理 piCongrLeft_symm_preimage_pi
  条件: (f : ι' ≃ ι) (s : Set ι') (t : 对任意 i, Set (α i))
  证明: by
  ext; simp
-/
theorem piCongrLeft_symm_preimage_pi (f : ι' ≃ ι) (s : Set ι') (t : forall i, Set (α i)) :
    (f.piCongrLeft α).symm ⁻¹' s.pi (fun i' => t <| f i') = (f '' s).pi t := by
  ext; simp

/--
theorem `piCongrLeft_symm_preimage_univ_pi` / 定理 `piCongrLeft_symm_preimage_univ_pi`

English:
theorem piCongrLeft_symm_preimage_univ_pi
  given: (f : ι' ≃ ι) (t : forall i, Set (α i))
  proof: by
  simpa [f.surjective.range_eq] using piCongrLeft_symm_preimage_pi f univ t

中文:
定理 piCongrLeft_symm_preimage_univ_pi
  条件: (f : ι' ≃ ι) (t : 对任意 i, Set (α i))
  证明: by
  simpa [f.surjective.range_eq] using piCongrLeft_symm_preimage_pi f univ t

Depends on / 依赖: f.surjective.range_eq, piCongrLeft_symm_preimage_pi, range_eq, surjective
-/
theorem piCongrLeft_symm_preimage_univ_pi (f : ι' ≃ ι) (t : forall i, Set (α i)) :
    (f.piCongrLeft α).symm ⁻¹' univ.pi (fun i' => t <| f i') = univ.pi t := by
  simpa [f.surjective.range_eq] using piCongrLeft_symm_preimage_pi f univ t

/--
theorem `piCongrLeft_preimage_pi` / 定理 `piCongrLeft_preimage_pi`

English:
theorem piCongrLeft_preimage_pi
  given: (f : ι' ≃ ι) (s : Set ι') (t : forall i, Set (α i))
  proof: by
  apply Set.ext
  rw [← (f.piCongrLeft α).symm.forall_congr_right]
  simp

中文:
定理 piCongrLeft_preimage_pi
  条件: (f : ι' ≃ ι) (s : Set ι') (t : 对任意 i, Set (α i))
  证明: by
  apply Set.ext
  rw [← (f.piCongrLeft α).symm.forall_congr_right]
  simp

Depends on / 依赖: Set.ext, f.piCongrLeft, forall_congr_right, piCongrLeft, symm.forall_congr_right
-/
theorem piCongrLeft_preimage_pi (f : ι' ≃ ι) (s : Set ι') (t : forall i, Set (α i)) :
    f.piCongrLeft α ⁻¹' (f '' s).pi t = s.pi fun i => t (f i) := by
  apply Set.ext
  rw [← (f.piCongrLeft α).symm.forall_congr_right]
  simp

/--
theorem `piCongrLeft_preimage_univ_pi` / 定理 `piCongrLeft_preimage_univ_pi`

English:
theorem piCongrLeft_preimage_univ_pi
  given: (f : ι' ≃ ι) (t : forall i, Set (α i))
  proof: by
  simpa [f.surjective.range_eq] using piCongrLeft_preimage_pi f univ t

中文:
定理 piCongrLeft_preimage_univ_pi
  条件: (f : ι' ≃ ι) (t : 对任意 i, Set (α i))
  证明: by
  simpa [f.surjective.range_eq] using piCongrLeft_preimage_pi f univ t

Depends on / 依赖: f.surjective.range_eq, piCongrLeft_preimage_pi, range_eq, surjective
-/
theorem piCongrLeft_preimage_univ_pi (f : ι' ≃ ι) (t : forall i, Set (α i)) :
    f.piCongrLeft α ⁻¹' univ.pi t = univ.pi fun i => t (f i) := by
  simpa [f.surjective.range_eq] using piCongrLeft_preimage_pi f univ t

/--
theorem `sumPiEquivProdPi_symm_preimage_univ_pi` / 定理 `sumPiEquivProdPi_symm_preimage_univ_pi`

English:
theorem sumPiEquivProdPi_symm_preimage_univ_pi
  given: (π : ι oplus ι' -> Type*) (t : forall i, Set (π i))
  proof: by
  ext
  simp

中文:
定理 sumPiEquivProdPi_symm_preimage_univ_pi
  条件: (π : ι oplus ι' -> 类型) (t : 对任意 i, Set (π i))
  证明: by
  ext
  simp
-/
theorem sumPiEquivProdPi_symm_preimage_univ_pi (π : ι oplus ι' -> Type*) (t : forall i, Set (π i)) :
    (sumPiEquivProdPi π).symm ⁻¹' univ.pi t =
    univ.pi (fun i => t (.inl i)) ×ˢ univ.pi fun i => t (.inr i) := by
  ext
  simp

end Equiv

namespace Set

variable {α β γ δ : Type*} {s : Set α} {f : α -> β}

section graphOn
variable {x : α × β}

/--
lemma `mem_graphOn` / 引理 `mem_graphOn`

English:
lemma mem_graphOn
  statement: x in s.graphOn f ↔ x.1 in s ∧ f x.1 = x.2
  proof: by aesop (add simp graphOn)

中文:
引理 mem_graphOn
  结论: x in s.graphOn f ↔ x.1 in s ∧ f x.1 = x.2
  证明: by aesop (add simp graphOn)
-/
@[simp] lemma mem_graphOn : x in s.graphOn f ↔ x.1 in s ∧ f x.1 = x.2 := by aesop (add simp graphOn)

/--
lemma `graphOn_empty` / 引理 `graphOn_empty`

English:
lemma graphOn_empty
  given: (f : α -> β)
  statement: graphOn f ∅ = ∅
  proof: image_empty _

中文:
引理 graphOn_empty
  条件: (f : α -> β)
  结论: graphOn f ∅ = ∅
  证明: image_empty _
-/
@[simp] lemma graphOn_empty (f : α -> β) : graphOn f ∅ = ∅ := image_empty _
/--
lemma `graphOn_eq_empty` / 引理 `graphOn_eq_empty`

English:
lemma graphOn_eq_empty
  statement: graphOn f s = ∅ ↔ s = ∅
  proof: image_eq_empty

中文:
引理 graphOn_eq_empty
  结论: graphOn f s = ∅ ↔ s = ∅
  证明: image_eq_empty
-/
@[simp] lemma graphOn_eq_empty : graphOn f s = ∅ ↔ s = ∅ := image_eq_empty
/--
lemma `graphOn_nonempty` / 引理 `graphOn_nonempty`

English:
lemma graphOn_nonempty
  statement: (s.graphOn f).Nonempty ↔ s.Nonempty
  proof: image_nonempty

protected alias ⟨_, Nonempty.graphOn⟩ := graphOn_nonempty

@[simp]

中文:
引理 graphOn_nonempty
  结论: (s.graphOn f).Nonempty ↔ s.Nonempty
  证明: image_nonempty

protected alias ⟨_, Nonempty.graphOn⟩ := graphOn_nonempty

@[simp]
-/
@[simp] lemma graphOn_nonempty : (s.graphOn f).Nonempty ↔ s.Nonempty := image_nonempty

protected alias ⟨_, Nonempty.graphOn⟩ := graphOn_nonempty

@[simp]
/--
lemma `graphOn_union` / 引理 `graphOn_union`

English:
lemma graphOn_union
  given: (f : α -> β) (s t : Set α)
  statement: graphOn f (s union t) = graphOn f s union graphOn f t
  proof: image_union ..

@[simp]

中文:
引理 graphOn_union
  条件: (f : α -> β) (s t : Set α)
  结论: graphOn f (s union t) = graphOn f s union graphOn f t
  证明: image_union ..

@[simp]

Depends on / 依赖: image_union
-/
lemma graphOn_union (f : α -> β) (s t : Set α) : graphOn f (s union t) = graphOn f s union graphOn f t :=
  image_union ..

@[simp]
/--
lemma `graphOn_singleton` / 引理 `graphOn_singleton`

English:
lemma graphOn_singleton
  given: (f : α -> β) (x : α)
  statement: graphOn f {x} = {(x, f x)}
  proof: image_singleton ..

@[simp]

中文:
引理 graphOn_singleton
  条件: (f : α -> β) (x : α)
  结论: graphOn f {x} = {(x, f x)}
  证明: image_singleton ..

@[simp]

Depends on / 依赖: image_singleton
-/
lemma graphOn_singleton (f : α -> β) (x : α) : graphOn f {x} = {(x, f x)} :=
  image_singleton ..

@[simp]
/--
lemma `graphOn_insert` / 引理 `graphOn_insert`

English:
lemma graphOn_insert
  given: (f : α -> β) (x : α) (s : Set α)
  proof: image_insert_eq ..

@[simp]

中文:
引理 graphOn_insert
  条件: (f : α -> β) (x : α) (s : Set α)
  证明: image_insert_eq ..

@[simp]

Depends on / 依赖: image_insert_eq
-/
lemma graphOn_insert (f : α -> β) (x : α) (s : Set α) :
    graphOn f (insert x s) = insert (x, f x) (graphOn f s) :=
  image_insert_eq ..

@[simp]
/--
lemma `image_fst_graphOn` / 引理 `image_fst_graphOn`

English:
lemma image_fst_graphOn
  given: (f : α -> β) (s : Set α)
  statement: Prod.fst '' graphOn f s = s
  proof: by
  simp [graphOn, image_image]

中文:
引理 image_fst_graphOn
  条件: (f : α -> β) (s : Set α)
  结论: Prod.fst '' graphOn f s = s
  证明: by
  simp [graphOn, image_image]

Depends on / 依赖: graphOn, image_image
-/
lemma image_fst_graphOn (f : α -> β) (s : Set α) : Prod.fst '' graphOn f s = s := by
  simp [graphOn, image_image]

/--
lemma `image_snd_graphOn` / 引理 `image_snd_graphOn`

English:
lemma image_snd_graphOn
  given: (f : α -> β)
  statement: Prod.snd '' s.graphOn f = f '' s
  proof: by ext x; simp

中文:
引理 image_snd_graphOn
  条件: (f : α -> β)
  结论: Prod.snd '' s.graphOn f = f '' s
  证明: by ext x; simp
-/
@[simp] lemma image_snd_graphOn (f : α -> β) : Prod.snd '' s.graphOn f = f '' s := by ext x; simp

/--
lemma `fst_injOn_graph` / 引理 `fst_injOn_graph`

English:
lemma fst_injOn_graph
  statement: (s.graphOn f).InjOn Prod.fst
  proof: by aesop (add simp InjOn)

中文:
引理 fst_injOn_graph
  结论: (s.graphOn f).InjOn Prod.fst
  证明: by aesop (add simp InjOn)
-/
lemma fst_injOn_graph : (s.graphOn f).InjOn Prod.fst := by aesop (add simp InjOn)

/--
lemma `graphOn_comp` / 引理 `graphOn_comp`

English:
lemma graphOn_comp
  given: (s : Set α) (f : α -> β) (g : β -> γ)
  proof: by
  simpa using! image_comp (fun x => (x.1, g x.2)) (fun x => (x, f x)) _

中文:
引理 graphOn_comp
  条件: (s : Set α) (f : α -> β) (g : β -> γ)
  证明: by
  simpa using! image_comp (fun x => (x.1, g x.2)) (fun x => (x, f x)) _

Depends on / 依赖: image_comp
-/
lemma graphOn_comp (s : Set α) (f : α -> β) (g : β -> γ) :
    s.graphOn (g ∘ f) = (fun x => (x.1, g x.2)) '' s.graphOn f := by
  simpa using! image_comp (fun x => (x.1, g x.2)) (fun x => (x, f x)) _

/--
lemma `graphOn_univ_eq_range` / 引理 `graphOn_univ_eq_range`

English:
lemma graphOn_univ_eq_range
  statement: univ.graphOn f = range fun x => (x, f x)
  proof: image_univ

中文:
引理 graphOn_univ_eq_range
  结论: univ.graphOn f = range fun x => (x, f x)
  证明: image_univ

Depends on / 依赖: image_univ
-/
lemma graphOn_univ_eq_range : univ.graphOn f = range fun x => (x, f x) := image_univ

/--
lemma `graphOn_inj` / 引理 `graphOn_inj`

English:
lemma graphOn_inj
  given: {g : α -> β}
  statement: s.graphOn f = s.graphOn g ↔ s.EqOn f g
  proof: by
  simp [Set.ext_iff, forall_comm, EqOn]

中文:
引理 graphOn_inj
  条件: {g : α -> β}
  结论: s.graphOn f = s.graphOn g ↔ s.EqOn f g
  证明: by
  simp [Set.ext_iff, forall_comm, EqOn]
-/
@[simp] lemma graphOn_inj {g : α -> β} : s.graphOn f = s.graphOn g ↔ s.EqOn f g := by
  simp [Set.ext_iff, forall_comm, EqOn]

/--
lemma `graphOn_prod_graphOn` / 引理 `graphOn_prod_graphOn`

English:
lemma graphOn_prod_graphOn
  given: (s : Set α) (t : Set β) (f : α -> γ) (g : β -> δ)
  proof: by
  aesop

中文:
引理 graphOn_prod_graphOn
  条件: (s : Set α) (t : Set β) (f : α -> γ) (g : β -> δ)
  证明: by
  aesop
-/
lemma graphOn_prod_graphOn (s : Set α) (t : Set β) (f : α -> γ) (g : β -> δ) :
    s.graphOn f ×ˢ t.graphOn g = Equiv.prodProdProdComm .. ⁻¹' (s ×ˢ t).graphOn (Prod.map f g) := by
  aesop

/--
lemma `graphOn_prod_prodMap` / 引理 `graphOn_prod_prodMap`

English:
lemma graphOn_prod_prodMap
  given: (s : Set α) (t : Set β) (f : α -> γ) (g : β -> δ)
  proof: by
  aesop

中文:
引理 graphOn_prod_prodMap
  条件: (s : Set α) (t : Set β) (f : α -> γ) (g : β -> δ)
  证明: by
  aesop
-/
lemma graphOn_prod_prodMap (s : Set α) (t : Set β) (f : α -> γ) (g : β -> δ) :
    (s ×ˢ t).graphOn (Prod.map f g) = Equiv.prodProdProdComm .. ⁻¹' s.graphOn f ×ˢ t.graphOn g := by
  aesop

end graphOn

/-! ### Vertical line test -/

/--
lemma `exists_range_eq_graphOn_univ` / 引理 `exists_range_eq_graphOn_univ`

English:
lemma exists_range_eq_graphOn_univ
  statement: {f : α -> β × γ} (hf₁ : Surjective (Prod.fst ∘ f))
  proof: by
  refine ⟨fun h => (f (hf₁ h).choose).snd, ?_⟩
  ext x
  simp only [mem_range, comp_apply, mem_graphOn, mem_univ, true_and]
  refine ⟨?_, fun hi => ⟨(hf₁ x.1).choose, Prod.ext (hf₁ x.1).choose_spec hi⟩⟩
  rintro ⟨g, rfl⟩
  exact hf _ _ (hf₁ (f g).1).choose_spec

中文:
引理 exists_range_eq_graphOn_univ
  结论: {f : α -> β × γ} (hf₁ : Surjective (Prod.fst ∘ f))
  证明: by
  refine ⟨fun h => (f (hf₁ h).choose).snd, ?_⟩
  ext x
  simp only [mem_range, comp_apply, mem_graphOn, mem_univ, true_and]
  refine ⟨?_, fun hi => ⟨(hf₁ x.1).choose, Prod.ext (hf₁ x.1).choose_spec hi⟩⟩
  rintro ⟨g, rfl⟩
  exact hf _ _ (hf₁ (f g).1).choose_spec

Depends on / 依赖: Prod.ext, choose_spec, comp_apply, mem_graphOn, mem_range, mem_univ, true_and
-/
lemma exists_range_eq_graphOn_univ {f : α -> β × γ} (hf₁ : Surjective (Prod.fst ∘ f))
    (hf : forall g₁ g₂, (f g₁).1 = (f g₂).1 -> (f g₁).2 = (f g₂).2) :
    exists f' : β -> γ, range f = univ.graphOn f' := by
  refine ⟨fun h => (f (hf₁ h).choose).snd, ?_⟩
  ext x
  simp only [mem_range, comp_apply, mem_graphOn, mem_univ, true_and]
  refine ⟨?_, fun hi => ⟨(hf₁ x.1).choose, Prod.ext (hf₁ x.1).choose_spec hi⟩⟩
  rintro ⟨g, rfl⟩
  exact hf _ _ (hf₁ (f g).1).choose_spec

/--
lemma `exists_equiv_range_eq_graphOn_univ` / 引理 `exists_equiv_range_eq_graphOn_univ`

English:
lemma exists_equiv_range_eq_graphOn_univ
  statement: {f : α -> β × γ} (hf₁ : Surjective (Prod.fst ∘ f))
  proof: by
  obtain ⟨e₁, he₁⟩ := exists_range_eq_graphOn_univ hf₁ fun _ _ => (hf _ _).1
obtain ⟨e₂, he₂⟩ := exists_range_eq_graphOn_univ (f := Equiv.prodComm _ _ ∘ f) (by simpa)
    by simp [hf]
  have he₁₂ h i : e₁ h = i ↔ e₂ i = h := by
    rw [Set.ext_iff] at he₁ he₂
    aesop (add simp [Prod.swap_eq_iff

中文:
引理 exists_equiv_range_eq_graphOn_univ
  结论: {f : α -> β × γ} (hf₁ : Surjective (Prod.fst ∘ f))
  证明: by
  obtain ⟨e₁, he₁⟩ := exists_range_eq_graphOn_univ hf₁ fun _ _ => (hf _ _).1
obtain ⟨e₂, he₂⟩ := exists_range_eq_graphOn_univ (f := Equiv.prodComm _ _ ∘ f) (by simpa)
    by simp [hf]
  have he₁₂ h i : e₁ h = i ↔ e₂ i = h := by
    rw [Set.ext_iff] at he₁ he₂
    aesop (add simp [Prod.swap_eq_iff

Depends on / 依赖: Equiv.prodComm, Prod.swap_eq_iff_eq_swap, Set.ext_iff, exists_range_eq_graphOn_univ, ext_iff, invFun, left_inv, prodComm, right_inv, swap_eq_iff_eq_swap
-/
lemma exists_equiv_range_eq_graphOn_univ {f : α -> β × γ} (hf₁ : Surjective (Prod.fst ∘ f))
    (hf₂ : Surjective (Prod.snd ∘ f)) (hf : forall g₁ g₂, (f g₁).1 = (f g₂).1 ↔ (f g₁).2 = (f g₂).2) :
    exists e : β ≃ γ, range f = univ.graphOn e := by
  obtain ⟨e₁, he₁⟩ := exists_range_eq_graphOn_univ hf₁ fun _ _ => (hf _ _).1
obtain ⟨e₂, he₂⟩ := exists_range_eq_graphOn_univ (f := Equiv.prodComm _ _ ∘ f) (by simpa)
    by simp [hf]
  have he₁₂ h i : e₁ h = i ↔ e₂ i = h := by
    rw [Set.ext_iff] at he₁ he₂
    aesop (add simp [Prod.swap_eq_iff_eq_swap])
  exact ⟨
  { toFun := e₁
    invFun := e₂
    left_inv := fun h => by rw [← he₁₂]
    right_inv := fun i => by rw [he₁₂] }, he₁⟩

/--
lemma `exists_eq_mgraphOn_univ` / 引理 `exists_eq_mgraphOn_univ`

English:
lemma exists_eq_mgraphOn_univ
  statement: {s : Set (β × γ)}
  proof: by
  simpa using exists_range_eq_graphOn_univ hs₁.surjective
    fun a b h => congr_arg (Prod.snd ∘ (Subtype.val : s -> β × γ)) (hs₁.injective h)

中文:
引理 exists_eq_mgraphOn_univ
  结论: {s : Set (β × γ)}
  证明: by
  simpa using exists_range_eq_graphOn_univ hs₁.surjective
    fun a b h => congr_arg (Prod.snd ∘ (Subtype.val : s -> β × γ)) (hs₁.injective h)

Depends on / 依赖: Prod.snd, Subtype, Subtype.val, congr_arg, exists_range_eq_graphOn_univ, injective, surjective
-/
lemma exists_eq_mgraphOn_univ {s : Set (β × γ)}
    (hs₁ : Bijective (Prod.fst ∘ (Subtype.val : s -> β × γ))) : exists f : β -> γ, s = univ.graphOn f := by
  simpa using exists_range_eq_graphOn_univ hs₁.surjective
    fun a b h => congr_arg (Prod.snd ∘ (Subtype.val : s -> β × γ)) (hs₁.injective h)

end Set
