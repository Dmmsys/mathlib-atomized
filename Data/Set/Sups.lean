/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Set.NAry
public import Mathlib.Order.SupClosed
public import Mathlib.Order.UpperLower.Closure

/-!
# Set family operations

This file defines a few binary operations on `Set α` for use in set family combinatorics.

## Main declarations

* `s ⊻ t`: Set of elements of the form `a ⊔ b` where `a ∈ s`, `b ∈ t`.
* `s ⊼ t`: Set of elements of the form `a ⊓ b` where `a ∈ s`, `b ∈ t`.

## Notation

We define the following notation in scope `SetFamily`:
* `s ⊻ t`
* `s ⊼ t`

## References

[B. Bollobás, *Combinatorics*][bollobas1986]
-/

@[expose] public section


open Function

variable {F α β : Type*}

/--
Definition of `HasSups` / `HasSups` 的定义

English:
class HasSups
  parameters: (α : Type*)
  axioms and operations (1):
    - sups : α -> α -> α

中文:
类 有Sups
  参数: (α : 类型)
  公理与运算 (1 个):
    - sups : α -> α -> α
-/
class HasSups (α : Type*) where
  /-- The point-wise supremum `a ⊔ b` of `a, b : α`. -/
  sups : α -> α -> α

/--
Definition of `HasInfs` / `HasInfs` 的定义

English:
class HasInfs
  parameters: (α : Type*)
  axioms and operations (1):
    - infs : α -> α -> α

中文:
类 有Infs
  参数: (α : 类型)
  公理与运算 (1 个):
    - infs : α -> α -> α
-/
class HasInfs (α : Type*) where
  /-- The point-wise infimum `a ⊓ b` of `a, b : α`. -/
  infs : α -> α -> α

-- This notation is meant to have higher precedence than `⊔` and `⊓`, but still within the
-- realm of other binary notation.
@[inherit_doc]
infixl:74 " ⊻ " => HasSups.sups

@[inherit_doc]
infixl:75 " ⊼ " => HasInfs.infs

namespace Set

section Sups
variable [SemilatticeSup α] [SemilatticeSup β] [FunLike F α β] [SupHomClass F α β]
variable (s s₁ s₂ t t₁ t₂ u v : Set α)

/-- `s ⊻ t` is the set of elements of the form `a ⊔ b` where `a ∈ s`, `b ∈ t`. -/
@[instance_reducible]
/--
Definition of `hasSups` / `hasSups` 的定义

English:
definition hasSups
  signature: : HasSups (Set α)
  body: ⟨image2 (· ⊔ ·)⟩

scoped[SetFamily] attribute [instance] Set.hasSups

中文:
定义 hasSups
  签名: : 有Sups (集合 α)
  定义体: ⟨image2 (· ⊔ ·)⟩

scoped[SetFamily] attribute [instance] Set.hasSups
-/
protected def hasSups : HasSups (Set α) :=
  ⟨image2 (· ⊔ ·)⟩

scoped[SetFamily] attribute [instance] Set.hasSups

open SetFamily

variable {s s₁ s₂ t t₁ t₂ u} {a b c : α}

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

/--
theorem `sup_mem_sups` / 定理 `sup_mem_sups`

English:
theorem sup_mem_sups
  statement: a in s -> b in t -> a ⊔ b in s ⊻ t
  proof: mem_image2_of_mem

中文:
定理 sup_mem_sups
  结论: a in s -> b in t -> a ⊔ b in s ⊻ t
  证明: mem_image2_of_mem

Depends on / 依赖: mem_image2_of_mem
-/
theorem sup_mem_sups : a in s -> b in t -> a ⊔ b in s ⊻ t :=
  mem_image2_of_mem

/--
theorem `sups_subset` / 定理 `sups_subset`

English:
theorem sups_subset
  statement: s₁ subseteq s₂ -> t₁ subseteq t₂ -> s₁ ⊻ t₁ subseteq s₂ ⊻ t₂
  proof: image2_subset

中文:
定理 sups_subset
  结论: s₁ subseteq s₂ -> t₁ subseteq t₂ -> s₁ ⊻ t₁ subseteq s₂ ⊻ t₂
  证明: image2_subset

Depends on / 依赖: image2_subset
-/
theorem sups_subset : s₁ subseteq s₂ -> t₁ subseteq t₂ -> s₁ ⊻ t₁ subseteq s₂ ⊻ t₂ :=
  image2_subset

/--
theorem `sups_subset_left` / 定理 `sups_subset_left`

English:
theorem sups_subset_left
  statement: t₁ subseteq t₂ -> s ⊻ t₁ subseteq s ⊻ t₂
  proof: image2_subset_left

中文:
定理 sups_subset_left
  结论: t₁ subseteq t₂ -> s ⊻ t₁ subseteq s ⊻ t₂
  证明: image2_subset_left

Depends on / 依赖: image2_subset_left
-/
theorem sups_subset_left : t₁ subseteq t₂ -> s ⊻ t₁ subseteq s ⊻ t₂ :=
  image2_subset_left

/--
theorem `sups_subset_right` / 定理 `sups_subset_right`

English:
theorem sups_subset_right
  statement: s₁ subseteq s₂ -> s₁ ⊻ t subseteq s₂ ⊻ t
  proof: image2_subset_right

中文:
定理 sups_subset_right
  结论: s₁ subseteq s₂ -> s₁ ⊻ t subseteq s₂ ⊻ t
  证明: image2_subset_right

Depends on / 依赖: image2_subset_right
-/
theorem sups_subset_right : s₁ subseteq s₂ -> s₁ ⊻ t subseteq s₂ ⊻ t :=
  image2_subset_right

/--
theorem `image_subset_sups_left` / 定理 `image_subset_sups_left`

English:
theorem image_subset_sups_left
  statement: b in t -> (fun a => a ⊔ b) '' s subseteq s ⊻ t
  proof: image_subset_image2_left

中文:
定理 image_subset_sups_left
  结论: b in t -> (fun a => a ⊔ b) '' s subseteq s ⊻ t
  证明: image_subset_image2_left

Depends on / 依赖: image_subset_image2_left
-/
theorem image_subset_sups_left : b in t -> (fun a => a ⊔ b) '' s subseteq s ⊻ t :=
  image_subset_image2_left

/--
theorem `image_subset_sups_right` / 定理 `image_subset_sups_right`

English:
theorem image_subset_sups_right
  statement: a in s -> (· ⊔ ·) a '' t subseteq s ⊻ t
  proof: image_subset_image2_right

中文:
定理 image_subset_sups_right
  结论: a in s -> (· ⊔ ·) a '' t subseteq s ⊻ t
  证明: image_subset_image2_right

Depends on / 依赖: image_subset_image2_right
-/
theorem image_subset_sups_right : a in s -> (· ⊔ ·) a '' t subseteq s ⊻ t :=
  image_subset_image2_right

/--
theorem `forall_sups_iff` / 定理 `forall_sups_iff`

English:
theorem forall_sups_iff
  given: {p : α -> Prop}
  statement: (forall c in s ⊻ t, p c) ↔ forall a in s, forall b in t, p (a ⊔ b)
  proof: forall_mem_image2

@[simp]

中文:
定理 对任意_sups_iff
  条件: {p : α -> 命题}
  结论: (对任意 c in s ⊻ t, p c) ↔ 对任意 a in s, 对任意 b in t, p (a ⊔ b)
  证明: forall_mem_image2

@[simp]

Depends on / 依赖: forall_mem_image2
-/
theorem forall_sups_iff {p : α -> Prop} : (forall c in s ⊻ t, p c) ↔ forall a in s, forall b in t, p (a ⊔ b) :=
  forall_mem_image2

@[simp]
/--
theorem `sups_subset_iff` / 定理 `sups_subset_iff`

English:
theorem sups_subset_iff
  statement: s ⊻ t subseteq u ↔ forall a in s, forall b in t, a ⊔ b in u
  proof: image2_subset_iff

@[simp]

中文:
定理 sups_subset_iff
  结论: s ⊻ t subseteq u ↔ 对任意 a in s, 对任意 b in t, a ⊔ b in u
  证明: image2_subset_iff

@[simp]

Depends on / 依赖: image2_subset_iff
-/
theorem sups_subset_iff : s ⊻ t subseteq u ↔ forall a in s, forall b in t, a ⊔ b in u :=
  image2_subset_iff

@[simp]
/--
theorem `sups_nonempty` / 定理 `sups_nonempty`

English:
theorem sups_nonempty
  statement: (s ⊻ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty
  proof: image2_nonempty_iff

中文:
定理 sups_nonempty
  结论: (s ⊻ t).非空 ↔ s.非空 ∧ t.非空
  证明: image2_nonempty_iff

Depends on / 依赖: image2_nonempty_iff
-/
theorem sups_nonempty : (s ⊻ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image2_nonempty_iff

/--
theorem `Nonempty.sups` / 定理 `Nonempty.sups`

English:
theorem Nonempty.sups
  statement: s.Nonempty -> t.Nonempty -> (s ⊻ t).Nonempty
  proof: Nonempty.image2

中文:
定理 非空.sups
  结论: s.非空 -> t.非空 -> (s ⊻ t).非空
  证明: Nonempty.image2
-/
protected theorem Nonempty.sups : s.Nonempty -> t.Nonempty -> (s ⊻ t).Nonempty :=
  Nonempty.image2

/--
theorem `Nonempty.of_sups_left` / 定理 `Nonempty.of_sups_left`

English:
theorem Nonempty.of_sups_left
  statement: (s ⊻ t).Nonempty -> s.Nonempty
  proof: Nonempty.of_image2_left

中文:
定理 非空.of_sups_left
  结论: (s ⊻ t).非空 -> s.非空
  证明: Nonempty.of_image2_left
-/
theorem Nonempty.of_sups_left : (s ⊻ t).Nonempty -> s.Nonempty :=
  Nonempty.of_image2_left

/--
theorem `Nonempty.of_sups_right` / 定理 `Nonempty.of_sups_right`

English:
theorem Nonempty.of_sups_right
  statement: (s ⊻ t).Nonempty -> t.Nonempty
  proof: Nonempty.of_image2_right

@[simp]

中文:
定理 非空.of_sups_right
  结论: (s ⊻ t).非空 -> t.非空
  证明: Nonempty.of_image2_right

@[simp]
-/
theorem Nonempty.of_sups_right : (s ⊻ t).Nonempty -> t.Nonempty :=
  Nonempty.of_image2_right

@[simp]
/--
theorem `empty_sups` / 定理 `empty_sups`

English:
theorem empty_sups
  statement: ∅ ⊻ t = ∅
  proof: image2_empty_left

@[simp]

中文:
定理 empty_sups
  结论: ∅ ⊻ t = ∅
  证明: image2_empty_left

@[simp]

Depends on / 依赖: image2_empty_left
-/
theorem empty_sups : ∅ ⊻ t = ∅ :=
  image2_empty_left

@[simp]
/--
theorem `sups_empty` / 定理 `sups_empty`

English:
theorem sups_empty
  statement: s ⊻ ∅ = ∅
  proof: image2_empty_right

@[simp]

中文:
定理 sups_empty
  结论: s ⊻ ∅ = ∅
  证明: image2_empty_right

@[simp]

Depends on / 依赖: image2_empty_right
-/
theorem sups_empty : s ⊻ ∅ = ∅ :=
  image2_empty_right

@[simp]
/--
theorem `sups_eq_empty` / 定理 `sups_eq_empty`

English:
theorem sups_eq_empty
  statement: s ⊻ t = ∅ ↔ s = ∅ ∨ t = ∅
  proof: image2_eq_empty_iff

@[simp]

中文:
定理 sups_eq_empty
  结论: s ⊻ t = ∅ ↔ s = ∅ ∨ t = ∅
  证明: image2_eq_empty_iff

@[simp]

Depends on / 依赖: image2_eq_empty_iff
-/
theorem sups_eq_empty : s ⊻ t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image2_eq_empty_iff

@[simp]
/--
theorem `singleton_sups` / 定理 `singleton_sups`

English:
theorem singleton_sups
  statement: {a} ⊻ t = t.image fun b => a ⊔ b
  proof: image2_singleton_left

@[simp]

中文:
定理 singleton_sups
  结论: {a} ⊻ t = t.像 fun b => a ⊔ b
  证明: image2_singleton_left

@[simp]

Depends on / 依赖: image2_singleton_left
-/
theorem singleton_sups : {a} ⊻ t = t.image fun b => a ⊔ b :=
  image2_singleton_left

@[simp]
/--
theorem `sups_singleton` / 定理 `sups_singleton`

English:
theorem sups_singleton
  statement: s ⊻ {b} = s.image fun a => a ⊔ b
  proof: image2_singleton_right

中文:
定理 sups_singleton
  结论: s ⊻ {b} = s.像 fun a => a ⊔ b
  证明: image2_singleton_right

Depends on / 依赖: image2_singleton_right
-/
theorem sups_singleton : s ⊻ {b} = s.image fun a => a ⊔ b :=
  image2_singleton_right

/--
theorem `singleton_sups_singleton` / 定理 `singleton_sups_singleton`

English:
theorem singleton_sups_singleton
  statement: ({a} ⊻ {b} : Set α) = {a ⊔ b}
  proof: image2_singleton

中文:
定理 singleton_sups_singleton
  结论: ({a} ⊻ {b} : 集合 α) = {a ⊔ b}
  证明: image2_singleton

Depends on / 依赖: image2_singleton
-/
theorem singleton_sups_singleton : ({a} ⊻ {b} : Set α) = {a ⊔ b} :=
  image2_singleton

/--
theorem `sups_union_left` / 定理 `sups_union_left`

English:
theorem sups_union_left
  statement: (s₁ union s₂) ⊻ t = s₁ ⊻ t union s₂ ⊻ t
  proof: image2_union_left

中文:
定理 sups_union_left
  结论: (s₁ union s₂) ⊻ t = s₁ ⊻ t union s₂ ⊻ t
  证明: image2_union_left

Depends on / 依赖: image2_union_left
-/
theorem sups_union_left : (s₁ union s₂) ⊻ t = s₁ ⊻ t union s₂ ⊻ t :=
  image2_union_left

/--
theorem `sups_union_right` / 定理 `sups_union_right`

English:
theorem sups_union_right
  statement: s ⊻ (t₁ union t₂) = s ⊻ t₁ union s ⊻ t₂
  proof: image2_union_right

中文:
定理 sups_union_right
  结论: s ⊻ (t₁ union t₂) = s ⊻ t₁ union s ⊻ t₂
  证明: image2_union_right

Depends on / 依赖: image2_union_right
-/
theorem sups_union_right : s ⊻ (t₁ union t₂) = s ⊻ t₁ union s ⊻ t₂ :=
  image2_union_right

/--
theorem `sups_inter_subset_left` / 定理 `sups_inter_subset_left`

English:
theorem sups_inter_subset_left
  statement: (s₁ inter s₂) ⊻ t subseteq s₁ ⊻ t inter s₂ ⊻ t
  proof: image2_inter_subset_left

中文:
定理 sups_inter_subset_left
  结论: (s₁ inter s₂) ⊻ t subseteq s₁ ⊻ t inter s₂ ⊻ t
  证明: image2_inter_subset_left

Depends on / 依赖: image2_inter_subset_left
-/
theorem sups_inter_subset_left : (s₁ inter s₂) ⊻ t subseteq s₁ ⊻ t inter s₂ ⊻ t :=
  image2_inter_subset_left

/--
theorem `sups_inter_subset_right` / 定理 `sups_inter_subset_right`

English:
theorem sups_inter_subset_right
  statement: s ⊻ (t₁ inter t₂) subseteq s ⊻ t₁ inter s ⊻ t₂
  proof: image2_inter_subset_right

中文:
定理 sups_inter_subset_right
  结论: s ⊻ (t₁ inter t₂) subseteq s ⊻ t₁ inter s ⊻ t₂
  证明: image2_inter_subset_right

Depends on / 依赖: image2_inter_subset_right
-/
theorem sups_inter_subset_right : s ⊻ (t₁ inter t₂) subseteq s ⊻ t₁ inter s ⊻ t₂ :=
  image2_inter_subset_right

/--
lemma `image_sups` / 引理 `image_sups`

English:
lemma image_sups
  given: (f : F) (s t : Set α)
  statement: f '' (s ⊻ t) = f '' s ⊻ f '' t
  proof: image_image2_distrib map_sup f

中文:
引理 image_sups
  条件: (f : F) (s t : 集合 α)
  结论: f '' (s ⊻ t) = f '' s ⊻ f '' t
  证明: image_image2_distrib map_sup f

Depends on / 依赖: image_image2_distrib, map_sup
-/
lemma image_sups (f : F) (s t : Set α) : f '' (s ⊻ t) = f '' s ⊻ f '' t :=
image_image2_distrib map_sup f

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

Depends on / 依赖: Monoid, Monoid.fg_iff.mpr, Set.finite_range, Set.range, closure_range_of, fg_iff, finite_range, mem_sups, sup_idem
-/
lemma subset_sups_self : s subseteq s ⊻ s := fun _a ha => mem_sups.2 ⟨_, ha, _, ha, sup_idem _⟩
/--
lemma `sups_subset_self` / 引理 `sups_subset_self`

English:
lemma sups_subset_self
  statement: s ⊻ s subseteq s ↔ SupClosed s
  proof: sups_subset_iff

中文:
引理 sups_subset_self
  结论: s ⊻ s subseteq s ↔ SupClosed s
  证明: sups_subset_iff

Depends on / 依赖: sups_subset_iff
-/
lemma sups_subset_self : s ⊻ s subseteq s ↔ SupClosed s := sups_subset_iff

/--
lemma `sups_eq_self` / 引理 `sups_eq_self`

English:
lemma sups_eq_self
  statement: s ⊻ s = s ↔ SupClosed s
  proof: subset_sups_self.ge_iff_eq'.symm.trans sups_subset_self

中文:
引理 sups_eq_self
  结论: s ⊻ s = s ↔ SupClosed s
  证明: subset_sups_self.ge_iff_eq'.symm.trans sups_subset_self
-/
@[simp] lemma sups_eq_self : s ⊻ s = s ↔ SupClosed s :=
  subset_sups_self.ge_iff_eq'.symm.trans sups_subset_self

/--
lemma `sep_sups_le` / 引理 `sep_sups_le`

English:
lemma sep_sups_le
  given: (s t : Set α) (a : α)
  proof: by ext; aesop

中文:
引理 sep_sups_le
  条件: (s t : 集合 α) (a : α)
  证明: by ext; aesop
-/
lemma sep_sups_le (s t : Set α) (a : α) :
    {b in s ⊻ t | b <= a} = {b in s | b <= a} ⊻ {b in t | b <= a} := by ext; aesop

variable (s t u)

/--
theorem `iUnion_image_sup_left` / 定理 `iUnion_image_sup_left`

English:
theorem iUnion_image_sup_left
  statement: ⋃ a in s, (· ⊔ ·) a '' t = s ⊻ t
  proof: iUnion_image_left _

中文:
定理 iUnion_image_sup_left
  结论: ⋃ a in s, (· ⊔ ·) a '' t = s ⊻ t
  证明: iUnion_image_left _

Depends on / 依赖: iUnion_image_left
-/
theorem iUnion_image_sup_left : ⋃ a in s, (· ⊔ ·) a '' t = s ⊻ t :=
  iUnion_image_left _

/--
theorem `iUnion_image_sup_right` / 定理 `iUnion_image_sup_right`

English:
theorem iUnion_image_sup_right
  statement: ⋃ b in t, (· ⊔ b) '' s = s ⊻ t
  proof: iUnion_image_right _

@[simp]

中文:
定理 iUnion_image_sup_right
  结论: ⋃ b in t, (· ⊔ b) '' s = s ⊻ t
  证明: iUnion_image_right _

@[simp]

Depends on / 依赖: iUnion_image_right
-/
theorem iUnion_image_sup_right : ⋃ b in t, (· ⊔ b) '' s = s ⊻ t :=
  iUnion_image_right _

@[simp]
/--
theorem `image_sup_prod` / 定理 `image_sup_prod`

English:
theorem image_sup_prod
  given: (s t : Set α)
  statement: Set.image2 (· ⊔ ·) s t = s ⊻ t
  proof: rfl

中文:
定理 image_sup_prod
  条件: (s t : 集合 α)
  结论: 集合.image2 (· ⊔ ·) s t = s ⊻ t
  证明: rfl
-/
theorem image_sup_prod (s t : Set α) : Set.image2 (· ⊔ ·) s t = s ⊻ t := rfl

/--
theorem `sups_assoc` / 定理 `sups_assoc`

English:
theorem sups_assoc
  statement: s ⊻ t ⊻ u = s ⊻ (t ⊻ u)
  proof: image2_assoc sup_assoc

中文:
定理 sups_assoc
  结论: s ⊻ t ⊻ u = s ⊻ (t ⊻ u)
  证明: image2_assoc sup_assoc

Depends on / 依赖: image2_assoc, sup_assoc
-/
theorem sups_assoc : s ⊻ t ⊻ u = s ⊻ (t ⊻ u) := image2_assoc sup_assoc

/--
theorem `sups_comm` / 定理 `sups_comm`

English:
theorem sups_comm
  statement: s ⊻ t = t ⊻ s
  proof: image2_comm sup_comm

中文:
定理 sups_comm
  结论: s ⊻ t = t ⊻ s
  证明: image2_comm sup_comm

Depends on / 依赖: image2_comm, sup_comm
-/
theorem sups_comm : s ⊻ t = t ⊻ s := image2_comm sup_comm

/--
theorem `sups_left_comm` / 定理 `sups_left_comm`

English:
theorem sups_left_comm
  statement: s ⊻ (t ⊻ u) = t ⊻ (s ⊻ u)
  proof: image2_left_comm sup_left_comm

中文:
定理 sups_left_comm
  结论: s ⊻ (t ⊻ u) = t ⊻ (s ⊻ u)
  证明: image2_left_comm sup_left_comm

Depends on / 依赖: image2_left_comm, sup_left_comm
-/
theorem sups_left_comm : s ⊻ (t ⊻ u) = t ⊻ (s ⊻ u) :=
  image2_left_comm sup_left_comm

/--
theorem `sups_right_comm` / 定理 `sups_right_comm`

English:
theorem sups_right_comm
  statement: s ⊻ t ⊻ u = s ⊻ u ⊻ t
  proof: image2_right_comm sup_right_comm

中文:
定理 sups_right_comm
  结论: s ⊻ t ⊻ u = s ⊻ u ⊻ t
  证明: image2_right_comm sup_right_comm

Depends on / 依赖: image2_right_comm, sup_right_comm
-/
theorem sups_right_comm : s ⊻ t ⊻ u = s ⊻ u ⊻ t :=
  image2_right_comm sup_right_comm

/--
theorem `sups_sups_sups_comm` / 定理 `sups_sups_sups_comm`

English:
theorem sups_sups_sups_comm
  statement: s ⊻ t ⊻ (u ⊻ v) = s ⊻ u ⊻ (t ⊻ v)
  proof: image2_image2_image2_comm sup_sup_sup_comm

中文:
定理 sups_sups_sups_comm
  结论: s ⊻ t ⊻ (u ⊻ v) = s ⊻ u ⊻ (t ⊻ v)
  证明: image2_image2_image2_comm sup_sup_sup_comm

Depends on / 依赖: image2_image2_image2_comm, sup_sup_sup_comm
-/
theorem sups_sups_sups_comm : s ⊻ t ⊻ (u ⊻ v) = s ⊻ u ⊻ (t ⊻ v) :=
  image2_image2_image2_comm sup_sup_sup_comm

end Sups

section Infs

variable [SemilatticeInf α] [SemilatticeInf β] [FunLike F α β] [InfHomClass F α β]
variable (s s₁ s₂ t t₁ t₂ u v : Set α)

/-- `s ⊼ t` is the set of elements of the form `a ⊓ b` where `a ∈ s`, `b ∈ t`. -/
@[instance_reducible]
/--
Definition of `hasInfs` / `hasInfs` 的定义

English:
definition hasInfs
  signature: : HasInfs (Set α)
  body: ⟨image2 (· ⊓ ·)⟩

scoped[SetFamily] attribute [instance] Set.hasInfs

中文:
定义 hasInfs
  签名: : 有Infs (集合 α)
  定义体: ⟨image2 (· ⊓ ·)⟩

scoped[SetFamily] attribute [instance] Set.hasInfs
-/
protected def hasInfs : HasInfs (Set α) :=
  ⟨image2 (· ⊓ ·)⟩

scoped[SetFamily] attribute [instance] Set.hasInfs

open SetFamily

variable {s s₁ s₂ t t₁ t₂ u} {a b c : α}

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

/--
theorem `inf_mem_infs` / 定理 `inf_mem_infs`

English:
theorem inf_mem_infs
  statement: a in s -> b in t -> a ⊓ b in s ⊼ t
  proof: mem_image2_of_mem

中文:
定理 inf_mem_infs
  结论: a in s -> b in t -> a ⊓ b in s ⊼ t
  证明: mem_image2_of_mem

Depends on / 依赖: mem_image2_of_mem
-/
theorem inf_mem_infs : a in s -> b in t -> a ⊓ b in s ⊼ t :=
  mem_image2_of_mem

/--
theorem `infs_subset` / 定理 `infs_subset`

English:
theorem infs_subset
  statement: s₁ subseteq s₂ -> t₁ subseteq t₂ -> s₁ ⊼ t₁ subseteq s₂ ⊼ t₂
  proof: image2_subset

中文:
定理 infs_subset
  结论: s₁ subseteq s₂ -> t₁ subseteq t₂ -> s₁ ⊼ t₁ subseteq s₂ ⊼ t₂
  证明: image2_subset

Depends on / 依赖: image2_subset
-/
theorem infs_subset : s₁ subseteq s₂ -> t₁ subseteq t₂ -> s₁ ⊼ t₁ subseteq s₂ ⊼ t₂ :=
  image2_subset

/--
theorem `infs_subset_left` / 定理 `infs_subset_left`

English:
theorem infs_subset_left
  statement: t₁ subseteq t₂ -> s ⊼ t₁ subseteq s ⊼ t₂
  proof: image2_subset_left

中文:
定理 infs_subset_left
  结论: t₁ subseteq t₂ -> s ⊼ t₁ subseteq s ⊼ t₂
  证明: image2_subset_left

Depends on / 依赖: image2_subset_left
-/
theorem infs_subset_left : t₁ subseteq t₂ -> s ⊼ t₁ subseteq s ⊼ t₂ :=
  image2_subset_left

/--
theorem `infs_subset_right` / 定理 `infs_subset_right`

English:
theorem infs_subset_right
  statement: s₁ subseteq s₂ -> s₁ ⊼ t subseteq s₂ ⊼ t
  proof: image2_subset_right

中文:
定理 infs_subset_right
  结论: s₁ subseteq s₂ -> s₁ ⊼ t subseteq s₂ ⊼ t
  证明: image2_subset_right

Depends on / 依赖: image2_subset_right
-/
theorem infs_subset_right : s₁ subseteq s₂ -> s₁ ⊼ t subseteq s₂ ⊼ t :=
  image2_subset_right

/--
theorem `image_subset_infs_left` / 定理 `image_subset_infs_left`

English:
theorem image_subset_infs_left
  statement: b in t -> (fun a => a ⊓ b) '' s subseteq s ⊼ t
  proof: image_subset_image2_left

中文:
定理 image_subset_infs_left
  结论: b in t -> (fun a => a ⊓ b) '' s subseteq s ⊼ t
  证明: image_subset_image2_left

Depends on / 依赖: image_subset_image2_left
-/
theorem image_subset_infs_left : b in t -> (fun a => a ⊓ b) '' s subseteq s ⊼ t :=
  image_subset_image2_left

/--
theorem `image_subset_infs_right` / 定理 `image_subset_infs_right`

English:
theorem image_subset_infs_right
  statement: a in s -> (a ⊓ ·) '' t subseteq s ⊼ t
  proof: image_subset_image2_right

中文:
定理 image_subset_infs_right
  结论: a in s -> (a ⊓ ·) '' t subseteq s ⊼ t
  证明: image_subset_image2_right

Depends on / 依赖: image_subset_image2_right
-/
theorem image_subset_infs_right : a in s -> (a ⊓ ·) '' t subseteq s ⊼ t :=
  image_subset_image2_right

/--
theorem `forall_infs_iff` / 定理 `forall_infs_iff`

English:
theorem forall_infs_iff
  given: {p : α -> Prop}
  statement: (forall c in s ⊼ t, p c) ↔ forall a in s, forall b in t, p (a ⊓ b)
  proof: forall_mem_image2

@[simp]

中文:
定理 对任意_infs_iff
  条件: {p : α -> 命题}
  结论: (对任意 c in s ⊼ t, p c) ↔ 对任意 a in s, 对任意 b in t, p (a ⊓ b)
  证明: forall_mem_image2

@[simp]

Depends on / 依赖: forall_mem_image2
-/
theorem forall_infs_iff {p : α -> Prop} : (forall c in s ⊼ t, p c) ↔ forall a in s, forall b in t, p (a ⊓ b) :=
  forall_mem_image2

@[simp]
/--
theorem `infs_subset_iff` / 定理 `infs_subset_iff`

English:
theorem infs_subset_iff
  statement: s ⊼ t subseteq u ↔ forall a in s, forall b in t, a ⊓ b in u
  proof: image2_subset_iff

@[simp]

中文:
定理 infs_subset_iff
  结论: s ⊼ t subseteq u ↔ 对任意 a in s, 对任意 b in t, a ⊓ b in u
  证明: image2_subset_iff

@[simp]

Depends on / 依赖: image2_subset_iff
-/
theorem infs_subset_iff : s ⊼ t subseteq u ↔ forall a in s, forall b in t, a ⊓ b in u :=
  image2_subset_iff

@[simp]
/--
theorem `infs_nonempty` / 定理 `infs_nonempty`

English:
theorem infs_nonempty
  statement: (s ⊼ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty
  proof: image2_nonempty_iff

中文:
定理 infs_nonempty
  结论: (s ⊼ t).非空 ↔ s.非空 ∧ t.非空
  证明: image2_nonempty_iff

Depends on / 依赖: image2_nonempty_iff
-/
theorem infs_nonempty : (s ⊼ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image2_nonempty_iff

/--
theorem `Nonempty.infs` / 定理 `Nonempty.infs`

English:
theorem Nonempty.infs
  statement: s.Nonempty -> t.Nonempty -> (s ⊼ t).Nonempty
  proof: Nonempty.image2

中文:
定理 非空.infs
  结论: s.非空 -> t.非空 -> (s ⊼ t).非空
  证明: Nonempty.image2
-/
protected theorem Nonempty.infs : s.Nonempty -> t.Nonempty -> (s ⊼ t).Nonempty :=
  Nonempty.image2

/--
theorem `Nonempty.of_infs_left` / 定理 `Nonempty.of_infs_left`

English:
theorem Nonempty.of_infs_left
  statement: (s ⊼ t).Nonempty -> s.Nonempty
  proof: Nonempty.of_image2_left

中文:
定理 非空.of_infs_left
  结论: (s ⊼ t).非空 -> s.非空
  证明: Nonempty.of_image2_left
-/
theorem Nonempty.of_infs_left : (s ⊼ t).Nonempty -> s.Nonempty :=
  Nonempty.of_image2_left

/--
theorem `Nonempty.of_infs_right` / 定理 `Nonempty.of_infs_right`

English:
theorem Nonempty.of_infs_right
  statement: (s ⊼ t).Nonempty -> t.Nonempty
  proof: Nonempty.of_image2_right

@[simp]

中文:
定理 非空.of_infs_right
  结论: (s ⊼ t).非空 -> t.非空
  证明: Nonempty.of_image2_right

@[simp]
-/
theorem Nonempty.of_infs_right : (s ⊼ t).Nonempty -> t.Nonempty :=
  Nonempty.of_image2_right

@[simp]
/--
theorem `empty_infs` / 定理 `empty_infs`

English:
theorem empty_infs
  statement: ∅ ⊼ t = ∅
  proof: image2_empty_left

@[simp]

中文:
定理 empty_infs
  结论: ∅ ⊼ t = ∅
  证明: image2_empty_left

@[simp]

Depends on / 依赖: image2_empty_left
-/
theorem empty_infs : ∅ ⊼ t = ∅ :=
  image2_empty_left

@[simp]
/--
theorem `infs_empty` / 定理 `infs_empty`

English:
theorem infs_empty
  statement: s ⊼ ∅ = ∅
  proof: image2_empty_right

@[simp]

中文:
定理 infs_empty
  结论: s ⊼ ∅ = ∅
  证明: image2_empty_right

@[simp]

Depends on / 依赖: image2_empty_right
-/
theorem infs_empty : s ⊼ ∅ = ∅ :=
  image2_empty_right

@[simp]
/--
theorem `infs_eq_empty` / 定理 `infs_eq_empty`

English:
theorem infs_eq_empty
  statement: s ⊼ t = ∅ ↔ s = ∅ ∨ t = ∅
  proof: image2_eq_empty_iff

@[simp]

中文:
定理 infs_eq_empty
  结论: s ⊼ t = ∅ ↔ s = ∅ ∨ t = ∅
  证明: image2_eq_empty_iff

@[simp]

Depends on / 依赖: image2_eq_empty_iff
-/
theorem infs_eq_empty : s ⊼ t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image2_eq_empty_iff

@[simp]
/--
theorem `singleton_infs` / 定理 `singleton_infs`

English:
theorem singleton_infs
  statement: {a} ⊼ t = t.image fun b => a ⊓ b
  proof: image2_singleton_left

@[simp]

中文:
定理 singleton_infs
  结论: {a} ⊼ t = t.像 fun b => a ⊓ b
  证明: image2_singleton_left

@[simp]

Depends on / 依赖: image2_singleton_left
-/
theorem singleton_infs : {a} ⊼ t = t.image fun b => a ⊓ b :=
  image2_singleton_left

@[simp]
/--
theorem `infs_singleton` / 定理 `infs_singleton`

English:
theorem infs_singleton
  statement: s ⊼ {b} = s.image fun a => a ⊓ b
  proof: image2_singleton_right

中文:
定理 infs_singleton
  结论: s ⊼ {b} = s.像 fun a => a ⊓ b
  证明: image2_singleton_right

Depends on / 依赖: image2_singleton_right
-/
theorem infs_singleton : s ⊼ {b} = s.image fun a => a ⊓ b :=
  image2_singleton_right

/--
theorem `singleton_infs_singleton` / 定理 `singleton_infs_singleton`

English:
theorem singleton_infs_singleton
  statement: ({a} ⊼ {b} : Set α) = {a ⊓ b}
  proof: image2_singleton

中文:
定理 singleton_infs_singleton
  结论: ({a} ⊼ {b} : 集合 α) = {a ⊓ b}
  证明: image2_singleton

Depends on / 依赖: Finite, Finset, Finset.coe_univ, Finset.univ, Group.FG, Group.fg_of_finite, Subgroup, Subgroup.closure_univ, closure_univ, coe_univ, fg_of_finite, image2_singleton, nonempty_fintype
-/
theorem singleton_infs_singleton : ({a} ⊼ {b} : Set α) = {a ⊓ b} :=
  image2_singleton

/--
theorem `infs_union_left` / 定理 `infs_union_left`

English:
theorem infs_union_left
  statement: (s₁ union s₂) ⊼ t = s₁ ⊼ t union s₂ ⊼ t
  proof: image2_union_left

中文:
定理 infs_union_left
  结论: (s₁ union s₂) ⊼ t = s₁ ⊼ t union s₂ ⊼ t
  证明: image2_union_left

Depends on / 依赖: image2_union_left
-/
theorem infs_union_left : (s₁ union s₂) ⊼ t = s₁ ⊼ t union s₂ ⊼ t :=
  image2_union_left

/--
theorem `infs_union_right` / 定理 `infs_union_right`

English:
theorem infs_union_right
  statement: s ⊼ (t₁ union t₂) = s ⊼ t₁ union s ⊼ t₂
  proof: image2_union_right

中文:
定理 infs_union_right
  结论: s ⊼ (t₁ union t₂) = s ⊼ t₁ union s ⊼ t₂
  证明: image2_union_right

Depends on / 依赖: Group.fg_iff.mpr, Set.finite_range, Set.range, closure_range_of, fg_iff, finite_range, image2_union_right
-/
theorem infs_union_right : s ⊼ (t₁ union t₂) = s ⊼ t₁ union s ⊼ t₂ :=
  image2_union_right

/--
theorem `infs_inter_subset_left` / 定理 `infs_inter_subset_left`

English:
theorem infs_inter_subset_left
  statement: (s₁ inter s₂) ⊼ t subseteq s₁ ⊼ t inter s₂ ⊼ t
  proof: image2_inter_subset_left

中文:
定理 infs_inter_subset_left
  结论: (s₁ inter s₂) ⊼ t subseteq s₁ ⊼ t inter s₂ ⊼ t
  证明: image2_inter_subset_left

Depends on / 依赖: image2_inter_subset_left
-/
theorem infs_inter_subset_left : (s₁ inter s₂) ⊼ t subseteq s₁ ⊼ t inter s₂ ⊼ t :=
  image2_inter_subset_left

/--
theorem `infs_inter_subset_right` / 定理 `infs_inter_subset_right`

English:
theorem infs_inter_subset_right
  statement: s ⊼ (t₁ inter t₂) subseteq s ⊼ t₁ inter s ⊼ t₂
  proof: image2_inter_subset_right

中文:
定理 infs_inter_subset_right
  结论: s ⊼ (t₁ inter t₂) subseteq s ⊼ t₁ inter s ⊼ t₂
  证明: image2_inter_subset_right

Depends on / 依赖: image2_inter_subset_right
-/
theorem infs_inter_subset_right : s ⊼ (t₁ inter t₂) subseteq s ⊼ t₁ inter s ⊼ t₂ :=
  image2_inter_subset_right

/--
lemma `image_infs` / 引理 `image_infs`

English:
lemma image_infs
  given: (f : F) (s t : Set α)
  statement: f '' (s ⊼ t) = f '' s ⊼ f '' t
  proof: image_image2_distrib map_inf f

中文:
引理 image_infs
  条件: (f : F) (s t : 集合 α)
  结论: f '' (s ⊼ t) = f '' s ⊼ f '' t
  证明: image_image2_distrib map_inf f

Depends on / 依赖: image_image2_distrib, map_inf
-/
lemma image_infs (f : F) (s t : Set α) : f '' (s ⊼ t) = f '' s ⊼ f '' t :=
image_image2_distrib map_inf f

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
  statement: s ⊼ s subseteq s ↔ InfClosed s
  proof: infs_subset_iff

中文:
引理 infs_self_subset
  结论: s ⊼ s subseteq s ↔ InfClosed s
  证明: infs_subset_iff

Depends on / 依赖: infs_subset_iff
-/
lemma infs_self_subset : s ⊼ s subseteq s ↔ InfClosed s := infs_subset_iff

/--
lemma `infs_self` / 引理 `infs_self`

English:
lemma infs_self
  statement: s ⊼ s = s ↔ InfClosed s
  proof: subset_infs_self.ge_iff_eq'.symm.trans infs_self_subset

中文:
引理 infs_self
  结论: s ⊼ s = s ↔ InfClosed s
  证明: subset_infs_self.ge_iff_eq'.symm.trans infs_self_subset
-/
@[simp] lemma infs_self : s ⊼ s = s ↔ InfClosed s :=
  subset_infs_self.ge_iff_eq'.symm.trans infs_self_subset

/--
lemma `sep_infs_le` / 引理 `sep_infs_le`

English:
lemma sep_infs_le
  given: (s t : Set α) (a : α)
  proof: by ext; aesop

中文:
引理 sep_infs_le
  条件: (s t : 集合 α) (a : α)
  证明: by ext; aesop
-/
lemma sep_infs_le (s t : Set α) (a : α) :
    {b in s ⊼ t | a <= b} = {b in s | a <= b} ⊼ {b in t | a <= b} := by ext; aesop

variable (s t u)

/--
theorem `iUnion_image_inf_left` / 定理 `iUnion_image_inf_left`

English:
theorem iUnion_image_inf_left
  statement: ⋃ a in s, (a ⊓ ·) '' t = s ⊼ t
  proof: iUnion_image_left _

中文:
定理 iUnion_image_inf_left
  结论: ⋃ a in s, (a ⊓ ·) '' t = s ⊼ t
  证明: iUnion_image_left _

Depends on / 依赖: iUnion_image_left
-/
theorem iUnion_image_inf_left : ⋃ a in s, (a ⊓ ·) '' t = s ⊼ t :=
  iUnion_image_left _

/--
theorem `iUnion_image_inf_right` / 定理 `iUnion_image_inf_right`

English:
theorem iUnion_image_inf_right
  statement: ⋃ b in t, (· ⊓ b) '' s = s ⊼ t
  proof: iUnion_image_right _

@[simp]

中文:
定理 iUnion_image_inf_right
  结论: ⋃ b in t, (· ⊓ b) '' s = s ⊼ t
  证明: iUnion_image_right _

@[simp]

Depends on / 依赖: iUnion_image_right
-/
theorem iUnion_image_inf_right : ⋃ b in t, (· ⊓ b) '' s = s ⊼ t :=
  iUnion_image_right _

@[simp]
/--
theorem `image_inf_prod` / 定理 `image_inf_prod`

English:
theorem image_inf_prod
  given: (s t : Set α)
  statement: Set.image2 (fun x x_1 => x ⊓ x_1) s t = s ⊼ t
  proof: rfl

中文:
定理 image_inf_prod
  条件: (s t : 集合 α)
  结论: 集合.image2 (fun x x_1 => x ⊓ x_1) s t = s ⊼ t
  证明: rfl
-/
theorem image_inf_prod (s t : Set α) : Set.image2 (fun x x_1 => x ⊓ x_1) s t = s ⊼ t := rfl

/--
theorem `infs_assoc` / 定理 `infs_assoc`

English:
theorem infs_assoc
  statement: s ⊼ t ⊼ u = s ⊼ (t ⊼ u)
  proof: image2_assoc inf_assoc

中文:
定理 infs_assoc
  结论: s ⊼ t ⊼ u = s ⊼ (t ⊼ u)
  证明: image2_assoc inf_assoc

Depends on / 依赖: image2_assoc, inf_assoc
-/
theorem infs_assoc : s ⊼ t ⊼ u = s ⊼ (t ⊼ u) := image2_assoc inf_assoc

/--
theorem `infs_comm` / 定理 `infs_comm`

English:
theorem infs_comm
  statement: s ⊼ t = t ⊼ s
  proof: image2_comm inf_comm

中文:
定理 infs_comm
  结论: s ⊼ t = t ⊼ s
  证明: image2_comm inf_comm

Depends on / 依赖: image2_comm, inf_comm
-/
theorem infs_comm : s ⊼ t = t ⊼ s := image2_comm inf_comm

/--
theorem `infs_left_comm` / 定理 `infs_left_comm`

English:
theorem infs_left_comm
  statement: s ⊼ (t ⊼ u) = t ⊼ (s ⊼ u)
  proof: image2_left_comm inf_left_comm

中文:
定理 infs_left_comm
  结论: s ⊼ (t ⊼ u) = t ⊼ (s ⊼ u)
  证明: image2_left_comm inf_left_comm

Depends on / 依赖: image2_left_comm, inf_left_comm
-/
theorem infs_left_comm : s ⊼ (t ⊼ u) = t ⊼ (s ⊼ u) :=
  image2_left_comm inf_left_comm

/--
theorem `infs_right_comm` / 定理 `infs_right_comm`

English:
theorem infs_right_comm
  statement: s ⊼ t ⊼ u = s ⊼ u ⊼ t
  proof: image2_right_comm inf_right_comm

中文:
定理 infs_right_comm
  结论: s ⊼ t ⊼ u = s ⊼ u ⊼ t
  证明: image2_right_comm inf_right_comm

Depends on / 依赖: image2_right_comm, inf_right_comm
-/
theorem infs_right_comm : s ⊼ t ⊼ u = s ⊼ u ⊼ t :=
  image2_right_comm inf_right_comm

/--
theorem `infs_infs_infs_comm` / 定理 `infs_infs_infs_comm`

English:
theorem infs_infs_infs_comm
  statement: s ⊼ t ⊼ (u ⊼ v) = s ⊼ u ⊼ (t ⊼ v)
  proof: image2_image2_image2_comm inf_inf_inf_comm

中文:
定理 infs_infs_infs_comm
  结论: s ⊼ t ⊼ (u ⊼ v) = s ⊼ u ⊼ (t ⊼ v)
  证明: image2_image2_image2_comm inf_inf_inf_comm

Depends on / 依赖: image2_image2_image2_comm, inf_inf_inf_comm
-/
theorem infs_infs_infs_comm : s ⊼ t ⊼ (u ⊼ v) = s ⊼ u ⊼ (t ⊼ v) :=
  image2_image2_image2_comm inf_inf_inf_comm

end Infs

open SetFamily

section DistribLattice

variable [DistribLattice α] (s t u : Set α)

/--
theorem `sups_infs_subset_left` / 定理 `sups_infs_subset_left`

English:
theorem sups_infs_subset_left
  statement: s ⊻ t ⊼ u subseteq (s ⊻ t) ⊼ (s ⊻ u)
  proof: image2_distrib_subset_left sup_inf_left

中文:
定理 sups_infs_subset_left
  结论: s ⊻ t ⊼ u subseteq (s ⊻ t) ⊼ (s ⊻ u)
  证明: image2_distrib_subset_left sup_inf_left

Depends on / 依赖: image2_distrib_subset_left, sup_inf_left
-/
theorem sups_infs_subset_left : s ⊻ t ⊼ u subseteq (s ⊻ t) ⊼ (s ⊻ u) :=
  image2_distrib_subset_left sup_inf_left

/--
theorem `sups_infs_subset_right` / 定理 `sups_infs_subset_right`

English:
theorem sups_infs_subset_right
  statement: t ⊼ u ⊻ s subseteq (t ⊻ s) ⊼ (u ⊻ s)
  proof: image2_distrib_subset_right sup_inf_right

中文:
定理 sups_infs_subset_right
  结论: t ⊼ u ⊻ s subseteq (t ⊻ s) ⊼ (u ⊻ s)
  证明: image2_distrib_subset_right sup_inf_right

Depends on / 依赖: image2_distrib_subset_right, sup_inf_right
-/
theorem sups_infs_subset_right : t ⊼ u ⊻ s subseteq (t ⊻ s) ⊼ (u ⊻ s) :=
  image2_distrib_subset_right sup_inf_right

/--
theorem `infs_sups_subset_left` / 定理 `infs_sups_subset_left`

English:
theorem infs_sups_subset_left
  statement: s ⊼ (t ⊻ u) subseteq s ⊼ t ⊻ s ⊼ u
  proof: image2_distrib_subset_left inf_sup_left

中文:
定理 infs_sups_subset_left
  结论: s ⊼ (t ⊻ u) subseteq s ⊼ t ⊻ s ⊼ u
  证明: image2_distrib_subset_left inf_sup_left

Depends on / 依赖: image2_distrib_subset_left, inf_sup_left
-/
theorem infs_sups_subset_left : s ⊼ (t ⊻ u) subseteq s ⊼ t ⊻ s ⊼ u :=
  image2_distrib_subset_left inf_sup_left

/--
theorem `infs_sups_subset_right` / 定理 `infs_sups_subset_right`

English:
theorem infs_sups_subset_right
  statement: (t ⊻ u) ⊼ s subseteq t ⊼ s ⊻ u ⊼ s
  proof: image2_distrib_subset_right inf_sup_right

中文:
定理 infs_sups_subset_right
  结论: (t ⊻ u) ⊼ s subseteq t ⊼ s ⊻ u ⊼ s
  证明: image2_distrib_subset_right inf_sup_right

Depends on / 依赖: image2_distrib_subset_right, inf_sup_right
-/
theorem infs_sups_subset_right : (t ⊻ u) ⊼ s subseteq t ⊼ s ⊻ u ⊼ s :=
  image2_distrib_subset_right inf_sup_right

end DistribLattice

end Set

open SetFamily

@[simp]
/--
theorem `upperClosure_sups` / 定理 `upperClosure_sups`

English:
theorem upperClosure_sups
  given: [SemilatticeSup α] (s t : Set α)
  proof: by
  ext a
  simp only [SetLike.mem_coe, mem_upperClosure, Set.mem_sups,
    UpperSet.coe_sup, Set.mem_inter_iff]
  constructor
  · rintro ⟨_, ⟨b, hb, c, hc, rfl⟩, ha⟩
    exact ⟨⟨b, hb, le_sup_left.trans ha⟩, c, hc, le_sup_right.trans ha⟩
  · rintro ⟨⟨b, hb, hab⟩, c, hc, hac⟩
    exact ⟨_, ⟨b, hb, c, hc, rfl⟩, sup_le hab hac⟩

@[simp]

中文:
定理 upperClosure_sups
  条件: [SemilatticeSup α] (s t : 集合 α)
  证明: by
  ext a
  simp only [SetLike.mem_coe, mem_upperClosure, Set.mem_sups,
    UpperSet.coe_sup, Set.mem_inter_iff]
  constructor
  · rintro ⟨_, ⟨b, hb, c, hc, rfl⟩, ha⟩
    exact ⟨⟨b, hb, le_sup_left.trans ha⟩, c, hc, le_sup_right.trans ha⟩
  · rintro ⟨⟨b, hb, hab⟩, c, hc, hac⟩
    exact ⟨_, ⟨b, hb, c, hc, rfl⟩, sup_le hab hac⟩

@[simp]

Depends on / 依赖: Set.mem_inter_iff, Set.mem_sups, SetLike, SetLike.mem_coe, UpperSet, UpperSet.coe_sup, coe_sup, le_sup_left, le_sup_left.trans, le_sup_right, le_sup_right.trans, mem_coe, mem_inter_iff, mem_sups, mem_upperClosure, sup_le
-/
theorem upperClosure_sups [SemilatticeSup α] (s t : Set α) :
    upperClosure (s ⊻ t) = upperClosure s ⊔ upperClosure t := by
  ext a
  simp only [SetLike.mem_coe, mem_upperClosure, Set.mem_sups,
    UpperSet.coe_sup, Set.mem_inter_iff]
  constructor
  · rintro ⟨_, ⟨b, hb, c, hc, rfl⟩, ha⟩
    exact ⟨⟨b, hb, le_sup_left.trans ha⟩, c, hc, le_sup_right.trans ha⟩
  · rintro ⟨⟨b, hb, hab⟩, c, hc, hac⟩
    exact ⟨_, ⟨b, hb, c, hc, rfl⟩, sup_le hab hac⟩

@[simp]
/--
theorem `lowerClosure_infs` / 定理 `lowerClosure_infs`

English:
theorem lowerClosure_infs
  given: [SemilatticeInf α] (s t : Set α)
  proof: by
  ext a
  simp only [SetLike.mem_coe, mem_lowerClosure, Set.mem_infs]
  constructor
  · rintro ⟨_, ⟨b, hb, c, hc, rfl⟩, ha⟩
    exact ⟨⟨b, hb, ha.trans inf_le_left⟩, c, hc, ha.trans inf_le_right⟩
  · rintro ⟨⟨b, hb, hab⟩, c, hc, hac⟩
    exact ⟨_, ⟨b, hb, c, hc, rfl⟩, le_inf hab hac⟩

中文:
定理 lowerClosure_infs
  条件: [SemilatticeInf α] (s t : 集合 α)
  证明: by
  ext a
  simp only [SetLike.mem_coe, mem_lowerClosure, Set.mem_infs]
  constructor
  · rintro ⟨_, ⟨b, hb, c, hc, rfl⟩, ha⟩
    exact ⟨⟨b, hb, ha.trans inf_le_left⟩, c, hc, ha.trans inf_le_right⟩
  · rintro ⟨⟨b, hb, hab⟩, c, hc, hac⟩
    exact ⟨_, ⟨b, hb, c, hc, rfl⟩, le_inf hab hac⟩

Depends on / 依赖: Set.mem_infs, SetLike, SetLike.mem_coe, ha.trans, inf_le_left, inf_le_right, le_inf, mem_coe, mem_infs, mem_lowerClosure
-/
theorem lowerClosure_infs [SemilatticeInf α] (s t : Set α) :
    lowerClosure (s ⊼ t) = lowerClosure s ⊓ lowerClosure t := by
  ext a
  simp only [SetLike.mem_coe, mem_lowerClosure, Set.mem_infs]
  constructor
  · rintro ⟨_, ⟨b, hb, c, hc, rfl⟩, ha⟩
    exact ⟨⟨b, hb, ha.trans inf_le_left⟩, c, hc, ha.trans inf_le_right⟩
  · rintro ⟨⟨b, hb, hab⟩, c, hc, hac⟩
    exact ⟨_, ⟨b, hb, c, hc, rfl⟩, le_inf hab hac⟩
