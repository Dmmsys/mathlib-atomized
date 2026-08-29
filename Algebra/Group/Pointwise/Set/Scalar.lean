/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn, Yaël Dillies
-/
module

public import Mathlib.Algebra.Opposites
public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Data.Set.NAry
public import Mathlib.Tactic.Monotonicity.Attr

/-!
# Pointwise scalar operations of sets

This file defines pointwise scalar-flavored algebraic operations on sets.

## Main declarations

For sets `s` and `t` and scalar `a`:

* `s • t`: Scalar multiplication, set of all `x • y` where `x ∈ s` and `y ∈ t`.
* `s /ₛ t`: Scalar division, set of all `x /ₛ y` where `x ∈ s` and `y ∈ t`. Available in
  multiplicative torsors.
* `s +ᵥ t`: Scalar addition, set of all `x +ᵥ y` where `x ∈ s` and `y ∈ t`.
* `s -ᵥ t`: Scalar subtraction, set of all `x -ᵥ y` where `x ∈ s` and `y ∈ t`.
* `a • s`: Scaling, set of all `a • x` where `x ∈ s`.
* `a +ᵥ s`: Translation, set of all `a +ᵥ x` where `x ∈ s`.

For `α` a semigroup/monoid, `Set α` is a semigroup/monoid.
As an unfortunate side effect, this means that `n • s`, where `n : ℕ`, is ambiguous between
pointwise scaling and repeated pointwise addition; the former has `(2 : ℕ) • {1, 2} = {2, 4}`, while
the latter has `(2 : ℕ) • {1, 2} = {2, 3, 4}`. See note [pointwise nat action].

Appropriate definitions and results are also transported to the additive theory via `to_additive`.

## Implementation notes

* The following expressions are considered in simp-normal form in a group:
  `(fun h ↦ h * g) ⁻¹' s`, `(fun h ↦ g * h) ⁻¹' s`, `(fun h ↦ h * g⁻¹) ⁻¹' s`,
  `(fun h ↦ g⁻¹ * h) ⁻¹' s`, `s * t`, `s⁻¹`, `(1 : Set _)` (and similarly for additive variants).
  Expressions equal to one of these will be simplified.
* We put all instances in the scope `Pointwise`, so that these instances are not available by
  default. Note that we do not mark them as reducible (as argued by note [reducible non-instances])
  since we expect the scope to be open whenever the instances are actually used (and making the
  instances reducible changes the behavior of `simp`).

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/

@[expose] public section

assert_not_exists Set.iUnion MulAction MonoidWithZero IsOrderedMonoid

open Function MulOpposite

variable {F α β γ : Type*}

namespace Set

/-! ### Translation/scaling of sets -/

section SMul

/-- The dilation of set `x • s` is defined as `{x • y | y ∈ s}` in scope `Pointwise`. -/
@[to_additive (attr := instance_reducible)
/-- The translation of set `x +ᵥ s` is defined as `{x +ᵥ y | y ∈ s}` in scope `Pointwise`. -/]
/--
Definition of `smulSet` / `smulSet` 的定义

English:
definition smulSet
  signature: [SMul α β]
  body: image (a • ·)

中文:
定义 smulSet
  签名: [SMul α β]
  定义体: image (a • ·)
-/
protected def smulSet [SMul α β] : SMul α (Set β) where smul a := image (a • ·)

/-- The pointwise scalar multiplication of sets `s • t` is defined as `{x • y | x ∈ s, y ∈ t}` in
scope `Pointwise`. -/
@[to_additive (attr := instance_reducible)
/-- The pointwise scalar addition of sets `s +ᵥ t` is defined as `{x +ᵥ y | x ∈ s, y ∈ t}` in locale
`Pointwise`. -/]
/--
Definition of `smul` / `smul` 的定义

English:
definition smul
  signature: [SMul α β]
  body: image2 (· • ·)

scoped[Pointwise] attribute [instance] Set.smulSet Set.smul
scoped[Pointwise] attribute [instance] Set.vaddSet Set.vadd

中文:
定义 smul
  签名: [SMul α β]
  定义体: image2 (· • ·)

scoped[Pointwise] attribute [instance] Set.smulSet Set.smul
scoped[Pointwise] attribute [instance] Set.vaddSet Set.vadd
-/
protected def smul [SMul α β] : SMul (Set α) (Set β) where smul := image2 (· • ·)

scoped[Pointwise] attribute [instance] Set.smulSet Set.smul
scoped[Pointwise] attribute [instance] Set.vaddSet Set.vadd

open scoped Pointwise

section SMul
variable {ι : Sort*} {κ : ι -> Sort*} [SMul α β] {s s₁ s₂ : Set α} {t t₁ t₂ u : Set β} {a : α}
  {b : β}

/--
lemma `image2_smul` / 引理 `image2_smul`

English:
lemma image2_smul
  statement: image2 (· • ·) s t = s • t
  proof: rfl

@[to_additive vadd_image_prod]

中文:
引理 image2_smul
  结论: image2 (· • ·) s t = s • t
  证明: rfl

@[to_additive vadd_image_prod]
-/
@[to_additive (attr := simp)] lemma image2_smul : image2 (· • ·) s t = s • t := rfl

@[to_additive vadd_image_prod]
/--
lemma `image_smul_prod` / 引理 `image_smul_prod`

English:
lemma image_smul_prod
  statement: (fun x : α × β => x.fst • x.snd) '' s ×ˢ t = s • t
  proof: image_prod _

中文:
引理 image_smul_prod
  结论: (fun x : α × β => x.fst • x.snd) '' s ×ˢ t = s • t
  证明: image_prod _

Depends on / 依赖: image_prod
-/
lemma image_smul_prod : (fun x : α × β => x.fst • x.snd) '' s ×ˢ t = s • t := image_prod _

/--
lemma `mem_smul` / 引理 `mem_smul`

English:
lemma mem_smul
  statement: b in s • t ↔ exists x in s, exists y in t, x • y = b
  proof: Iff.rfl

中文:
引理 mem_smul
  结论: b in s • t ↔ 存在 x in s, 存在 y in t, x • y = b
  证明: Iff.rfl
-/
@[to_additive] lemma mem_smul : b in s • t ↔ exists x in s, exists y in t, x • y = b := Iff.rfl

/--
lemma `smul_mem_smul` / 引理 `smul_mem_smul`

English:
lemma smul_mem_smul
  statement: a in s -> b in t -> a • b in s • t
  proof: mem_image2_of_mem

中文:
引理 smul_mem_smul
  结论: a in s -> b in t -> a • b in s • t
  证明: mem_image2_of_mem
-/
@[to_additive] lemma smul_mem_smul : a in s -> b in t -> a • b in s • t := mem_image2_of_mem

/--
lemma `empty_smul` / 引理 `empty_smul`

English:
lemma empty_smul
  statement: (∅ : Set α) • t = ∅
  proof: image2_empty_left

中文:
引理 empty_smul
  结论: (∅ : Set α) • t = ∅
  证明: image2_empty_left
-/
@[to_additive (attr := simp)] lemma empty_smul : (∅ : Set α) • t = ∅ := image2_empty_left
/--
lemma `smul_empty` / 引理 `smul_empty`

English:
lemma smul_empty
  statement: s • (∅ : Set β) = ∅
  proof: image2_empty_right

中文:
引理 smul_empty
  结论: s • (∅ : Set β) = ∅
  证明: image2_empty_right
-/
@[to_additive (attr := simp)] lemma smul_empty : s • (∅ : Set β) = ∅ := image2_empty_right

/--
lemma `smul_eq_empty` / 引理 `smul_eq_empty`

English:
lemma smul_eq_empty
  statement: s • t = ∅ ↔ s = ∅ ∨ t = ∅
  proof: image2_eq_empty_iff

@[to_additive (attr := simp)]

中文:
引理 smul_eq_empty
  结论: s • t = ∅ ↔ s = ∅ ∨ t = ∅
  证明: image2_eq_empty_iff

@[to_additive (attr := simp)]
-/
@[to_additive (attr := simp)] lemma smul_eq_empty : s • t = ∅ ↔ s = ∅ ∨ t = ∅ := image2_eq_empty_iff

@[to_additive (attr := simp)]
/--
lemma `smul_nonempty` / 引理 `smul_nonempty`

English:
lemma smul_nonempty
  statement: (s • t).Nonempty ↔ s.Nonempty ∧ t.Nonempty
  proof: image2_nonempty_iff

中文:
引理 smul_nonempty
  结论: (s • t).Nonempty ↔ s.Nonempty ∧ t.Nonempty
  证明: image2_nonempty_iff

Depends on / 依赖: image2_nonempty_iff
-/
lemma smul_nonempty : (s • t).Nonempty ↔ s.Nonempty ∧ t.Nonempty := image2_nonempty_iff

/--
lemma `Nonempty.smul` / 引理 `Nonempty.smul`

English:
lemma Nonempty.smul
  statement: s.Nonempty -> t.Nonempty -> (s • t).Nonempty
  proof: .image2

中文:
引理 Nonempty.smul
  结论: s.Nonempty -> t.Nonempty -> (s • t).Nonempty
  证明: .image2
-/
@[to_additive] lemma Nonempty.smul : s.Nonempty -> t.Nonempty -> (s • t).Nonempty := .image2
/--
lemma `Nonempty.of_smul_left` / 引理 `Nonempty.of_smul_left`

English:
lemma Nonempty.of_smul_left
  statement: (s • t).Nonempty -> s.Nonempty
  proof: .of_image2_left

中文:
引理 Nonempty.of_smul_left
  结论: (s • t).Nonempty -> s.Nonempty
  证明: .of_image2_left
-/
@[to_additive] lemma Nonempty.of_smul_left : (s • t).Nonempty -> s.Nonempty := .of_image2_left
/--
lemma `Nonempty.of_smul_right` / 引理 `Nonempty.of_smul_right`

English:
lemma Nonempty.of_smul_right
  statement: (s • t).Nonempty -> t.Nonempty
  proof: .of_image2_right

@[to_additive (attr := simp low + 1)]

中文:
引理 Nonempty.of_smul_right
  结论: (s • t).Nonempty -> t.Nonempty
  证明: .of_image2_right

@[to_additive (attr := simp low + 1)]
-/
@[to_additive] lemma Nonempty.of_smul_right : (s • t).Nonempty -> t.Nonempty := .of_image2_right

@[to_additive (attr := simp low + 1)]
/--
lemma `smul_singleton` / 引理 `smul_singleton`

English:
lemma smul_singleton
  statement: s • ({b} : Set β) = (· • b) '' s
  proof: image2_singleton_right

@[to_additive (attr := simp low + 1)]

中文:
引理 smul_singleton
  结论: s • ({b} : Set β) = (· • b) '' s
  证明: image2_singleton_right

@[to_additive (attr := simp low + 1)]

Depends on / 依赖: image2_singleton_right
-/
lemma smul_singleton : s • ({b} : Set β) = (· • b) '' s := image2_singleton_right

@[to_additive (attr := simp low + 1)]
/--
lemma `singleton_smul` / 引理 `singleton_smul`

English:
lemma singleton_smul
  statement: ({a} : Set α) • t = a • t
  proof: image2_singleton_left

@[to_additive (attr := simp high)]

中文:
引理 singleton_smul
  结论: ({a} : Set α) • t = a • t
  证明: image2_singleton_left

@[to_additive (attr := simp high)]

Depends on / 依赖: image2_singleton_left
-/
lemma singleton_smul : ({a} : Set α) • t = a • t := image2_singleton_left

@[to_additive (attr := simp high)]
/--
lemma `singleton_smul_singleton` / 引理 `singleton_smul_singleton`

English:
lemma singleton_smul_singleton
  statement: ({a} : Set α) • ({b} : Set β) = {a • b}
  proof: image2_singleton

@[to_additive (attr := mono, gcongr)]

中文:
引理 singleton_smul_singleton
  结论: ({a} : Set α) • ({b} : Set β) = {a • b}
  证明: image2_singleton

@[to_additive (attr := mono, gcongr)]

Depends on / 依赖: image2_singleton
-/
lemma singleton_smul_singleton : ({a} : Set α) • ({b} : Set β) = {a • b} := image2_singleton

@[to_additive (attr := mono, gcongr)]
/--
lemma `smul_subset_smul` / 引理 `smul_subset_smul`

English:
lemma smul_subset_smul
  statement: s₁ subseteq s₂ -> t₁ subseteq t₂ -> s₁ • t₁ subseteq s₂ • t₂
  proof: image2_subset

@[to_additive]

中文:
引理 smul_subset_smul
  结论: s₁ subseteq s₂ -> t₁ subseteq t₂ -> s₁ • t₁ subseteq s₂ • t₂
  证明: image2_subset

@[to_additive]

Depends on / 依赖: image2_subset
-/
lemma smul_subset_smul : s₁ subseteq s₂ -> t₁ subseteq t₂ -> s₁ • t₁ subseteq s₂ • t₂ := image2_subset

@[to_additive]
/--
lemma `smul_subset_smul_left` / 引理 `smul_subset_smul_left`

English:
lemma smul_subset_smul_left
  statement: t₁ subseteq t₂ -> s • t₁ subseteq s • t₂
  proof: image2_subset_left

@[to_additive]

中文:
引理 smul_subset_smul_left
  结论: t₁ subseteq t₂ -> s • t₁ subseteq s • t₂
  证明: image2_subset_left

@[to_additive]

Depends on / 依赖: image2_subset_left
-/
lemma smul_subset_smul_left : t₁ subseteq t₂ -> s • t₁ subseteq s • t₂ := image2_subset_left

@[to_additive]
/--
lemma `smul_subset_smul_right` / 引理 `smul_subset_smul_right`

English:
lemma smul_subset_smul_right
  statement: s₁ subseteq s₂ -> s₁ • t subseteq s₂ • t
  proof: image2_subset_right

中文:
引理 smul_subset_smul_right
  结论: s₁ subseteq s₂ -> s₁ • t subseteq s₂ • t
  证明: image2_subset_right

Depends on / 依赖: image2_subset_right
-/
lemma smul_subset_smul_right : s₁ subseteq s₂ -> s₁ • t subseteq s₂ • t := image2_subset_right

/--
lemma `smul_subset_iff` / 引理 `smul_subset_iff`

English:
lemma smul_subset_iff
  statement: s • t subseteq u ↔ forall a in s, forall b in t, a • b in u
  proof: image2_subset_iff

中文:
引理 smul_subset_iff
  结论: s • t subseteq u ↔ 对任意 a in s, 对任意 b in t, a • b in u
  证明: image2_subset_iff
-/
@[to_additive] lemma smul_subset_iff : s • t subseteq u ↔ forall a in s, forall b in t, a • b in u := image2_subset_iff

/--
lemma `union_smul` / 引理 `union_smul`

English:
lemma union_smul
  statement: (s₁ union s₂) • t = s₁ • t union s₂ • t
  proof: image2_union_left

中文:
引理 union_smul
  结论: (s₁ union s₂) • t = s₁ • t union s₂ • t
  证明: image2_union_left
-/
@[to_additive] lemma union_smul : (s₁ union s₂) • t = s₁ • t union s₂ • t := image2_union_left
/--
lemma `smul_union` / 引理 `smul_union`

English:
lemma smul_union
  statement: s • (t₁ union t₂) = s • t₁ union s • t₂
  proof: image2_union_right

@[to_additive]

中文:
引理 smul_union
  结论: s • (t₁ union t₂) = s • t₁ union s • t₂
  证明: image2_union_right

@[to_additive]
-/
@[to_additive] lemma smul_union : s • (t₁ union t₂) = s • t₁ union s • t₂ := image2_union_right

@[to_additive]
/--
lemma `inter_smul_subset` / 引理 `inter_smul_subset`

English:
lemma inter_smul_subset
  statement: (s₁ inter s₂) • t subseteq s₁ • t inter s₂ • t
  proof: image2_inter_subset_left

@[to_additive]

中文:
引理 inter_smul_subset
  结论: (s₁ inter s₂) • t subseteq s₁ • t inter s₂ • t
  证明: image2_inter_subset_left

@[to_additive]

Depends on / 依赖: image2_inter_subset_left
-/
lemma inter_smul_subset : (s₁ inter s₂) • t subseteq s₁ • t inter s₂ • t := image2_inter_subset_left

@[to_additive]
/--
lemma `smul_inter_subset` / 引理 `smul_inter_subset`

English:
lemma smul_inter_subset
  statement: s • (t₁ inter t₂) subseteq s • t₁ inter s • t₂
  proof: image2_inter_subset_right

@[to_additive]

中文:
引理 smul_inter_subset
  结论: s • (t₁ inter t₂) subseteq s • t₁ inter s • t₂
  证明: image2_inter_subset_right

@[to_additive]

Depends on / 依赖: image2_inter_subset_right
-/
lemma smul_inter_subset : s • (t₁ inter t₂) subseteq s • t₁ inter s • t₂ := image2_inter_subset_right

@[to_additive]
/--
lemma `inter_smul_union_subset_union` / 引理 `inter_smul_union_subset_union`

English:
lemma inter_smul_union_subset_union
  statement: (s₁ inter s₂) • (t₁ union t₂) subseteq s₁ • t₁ union s₂ • t₂
  proof: image2_inter_union_subset_union

@[to_additive]

中文:
引理 inter_smul_union_subset_union
  结论: (s₁ inter s₂) • (t₁ union t₂) subseteq s₁ • t₁ union s₂ • t₂
  证明: image2_inter_union_subset_union

@[to_additive]

Depends on / 依赖: image2_inter_union_subset_union
-/
lemma inter_smul_union_subset_union : (s₁ inter s₂) • (t₁ union t₂) subseteq s₁ • t₁ union s₂ • t₂ :=
  image2_inter_union_subset_union

@[to_additive]
/--
lemma `union_smul_inter_subset_union` / 引理 `union_smul_inter_subset_union`

English:
lemma union_smul_inter_subset_union
  statement: (s₁ union s₂) • (t₁ inter t₂) subseteq s₁ • t₁ union s₂ • t₂
  proof: image2_union_inter_subset_union

@[to_additive]

中文:
引理 union_smul_inter_subset_union
  结论: (s₁ union s₂) • (t₁ inter t₂) subseteq s₁ • t₁ union s₂ • t₂
  证明: image2_union_inter_subset_union

@[to_additive]

Depends on / 依赖: image2_union_inter_subset_union
-/
lemma union_smul_inter_subset_union : (s₁ union s₂) • (t₁ inter t₂) subseteq s₁ • t₁ union s₂ • t₂ :=
  image2_union_inter_subset_union

@[to_additive]
/--
lemma `smul_set_subset_smul` / 引理 `smul_set_subset_smul`

English:
lemma smul_set_subset_smul
  given: {s : Set α}
  statement: a in s -> a • t subseteq s • t
  proof: image_subset_image2_right

中文:
引理 smul_set_subset_smul
  条件: {s : Set α}
  结论: a in s -> a • t subseteq s • t
  证明: image_subset_image2_right

Depends on / 依赖: image_subset_image2_right
-/
lemma smul_set_subset_smul {s : Set α} : a in s -> a • t subseteq s • t := image_subset_image2_right

end SMul

section SMulSet
variable {ι : Sort*} {κ : ι -> Sort*} [SMul α β] {s t t₁ t₂ : Set β} {a : α} {b : β} {x y : β}

/--
lemma `image_smul` / 引理 `image_smul`

English:
lemma image_smul
  statement: (fun x => a • x) '' t = a • t
  proof: rfl

scoped[Pointwise] attribute [simp] Set.image_smul Set.image_vadd

中文:
引理 image_smul
  结论: (fun x => a • x) '' t = a • t
  证明: rfl

scoped[Pointwise] attribute [simp] Set.image_smul Set.image_vadd
-/
@[to_additive] lemma image_smul : (fun x => a • x) '' t = a • t := rfl

scoped[Pointwise] attribute [simp] Set.image_smul Set.image_vadd

/--
lemma `mem_smul_set` / 引理 `mem_smul_set`

English:
lemma mem_smul_set
  statement: x in a • t ↔ exists y, y in t ∧ a • y = x
  proof: Iff.rfl

中文:
引理 mem_smul_set
  结论: x in a • t ↔ 存在 y, y in t ∧ a • y = x
  证明: Iff.rfl
-/
@[to_additive] lemma mem_smul_set : x in a • t ↔ exists y, y in t ∧ a • y = x := Iff.rfl

/--
lemma `smul_mem_smul_set` / 引理 `smul_mem_smul_set`

English:
lemma smul_mem_smul_set
  statement: b in s -> a • b in a • s
  proof: mem_image_of_mem _

中文:
引理 smul_mem_smul_set
  结论: b in s -> a • b in a • s
  证明: mem_image_of_mem _
-/
@[to_additive] lemma smul_mem_smul_set : b in s -> a • b in a • s := mem_image_of_mem _

/--
lemma `smul_set_empty` / 引理 `smul_set_empty`

English:
lemma smul_set_empty
  statement: a • (∅ : Set β) = ∅
  proof: image_empty _

中文:
引理 smul_set_empty
  结论: a • (∅ : Set β) = ∅
  证明: image_empty _
-/
@[to_additive (attr := simp)] lemma smul_set_empty : a • (∅ : Set β) = ∅ := image_empty _
/--
lemma `smul_set_eq_empty` / 引理 `smul_set_eq_empty`

English:
lemma smul_set_eq_empty
  statement: a • s = ∅ ↔ s = ∅
  proof: image_eq_empty

@[to_additive (attr := simp)]

中文:
引理 smul_set_eq_empty
  结论: a • s = ∅ ↔ s = ∅
  证明: image_eq_empty

@[to_additive (attr := simp)]
-/
@[to_additive (attr := simp)] lemma smul_set_eq_empty : a • s = ∅ ↔ s = ∅ := image_eq_empty

@[to_additive (attr := simp)]
/--
lemma `smul_set_nonempty` / 引理 `smul_set_nonempty`

English:
lemma smul_set_nonempty
  statement: (a • s).Nonempty ↔ s.Nonempty
  proof: image_nonempty

@[to_additive (attr := simp)]

中文:
引理 smul_set_nonempty
  结论: (a • s).Nonempty ↔ s.Nonempty
  证明: image_nonempty

@[to_additive (attr := simp)]

Depends on / 依赖: image_nonempty
-/
lemma smul_set_nonempty : (a • s).Nonempty ↔ s.Nonempty := image_nonempty

@[to_additive (attr := simp)]
/--
lemma `smul_set_singleton` / 引理 `smul_set_singleton`

English:
lemma smul_set_singleton
  statement: a • ({b} : Set β) = {a • b}
  proof: image_singleton

中文:
引理 smul_set_singleton
  结论: a • ({b} : Set β) = {a • b}
  证明: image_singleton

Depends on / 依赖: image_singleton
-/
lemma smul_set_singleton : a • ({b} : Set β) = {a • b} := image_singleton

/--
lemma `smul_set_mono` / 引理 `smul_set_mono`

English:
lemma smul_set_mono
  statement: s subseteq t -> a • s subseteq a • t
  proof: image_mono

@[to_additive]

中文:
引理 smul_set_mono
  结论: s subseteq t -> a • s subseteq a • t
  证明: image_mono

@[to_additive]
-/
@[to_additive (attr := gcongr)] lemma smul_set_mono : s subseteq t -> a • s subseteq a • t := image_mono

@[to_additive]
/--
lemma `smul_set_subset_iff` / 引理 `smul_set_subset_iff`

English:
lemma smul_set_subset_iff
  statement: a • s subseteq t ↔ forall ⦃b⦄, b in s -> a • b in t
  proof: image_subset_iff

@[to_additive]

中文:
引理 smul_set_subset_iff
  结论: a • s subseteq t ↔ 对任意 ⦃b⦄, b in s -> a • b in t
  证明: image_subset_iff

@[to_additive]

Depends on / 依赖: image_subset_iff
-/
lemma smul_set_subset_iff : a • s subseteq t ↔ forall ⦃b⦄, b in s -> a • b in t :=
  image_subset_iff

@[to_additive]
/--
lemma `smul_set_union` / 引理 `smul_set_union`

English:
lemma smul_set_union
  statement: a • (t₁ union t₂) = a • t₁ union a • t₂
  proof: image_union ..

@[to_additive]

中文:
引理 smul_set_union
  结论: a • (t₁ union t₂) = a • t₁ union a • t₂
  证明: image_union ..

@[to_additive]

Depends on / 依赖: image_union
-/
lemma smul_set_union : a • (t₁ union t₂) = a • t₁ union a • t₂ :=
  image_union ..

@[to_additive]
/--
lemma `smul_set_insert` / 引理 `smul_set_insert`

English:
lemma smul_set_insert
  given: (a : α) (b : β) (s : Set β)
  statement: a • insert b s = insert (a • b) (a • s)
  proof: image_insert_eq ..

@[to_additive]

中文:
引理 smul_set_insert
  条件: (a : α) (b : β) (s : Set β)
  结论: a • insert b s = insert (a • b) (a • s)
  证明: image_insert_eq ..

@[to_additive]

Depends on / 依赖: image_insert_eq
-/
lemma smul_set_insert (a : α) (b : β) (s : Set β) : a • insert b s = insert (a • b) (a • s) :=
  image_insert_eq ..

@[to_additive]
/--
lemma `smul_set_inter_subset` / 引理 `smul_set_inter_subset`

English:
lemma smul_set_inter_subset
  statement: a • (t₁ inter t₂) subseteq a • t₁ inter a • t₂
  proof: image_inter_subset ..

中文:
引理 smul_set_inter_subset
  结论: a • (t₁ inter t₂) subseteq a • t₁ inter a • t₂
  证明: image_inter_subset ..

Depends on / 依赖: image_inter_subset
-/
lemma smul_set_inter_subset : a • (t₁ inter t₂) subseteq a • t₁ inter a • t₂ :=
  image_inter_subset ..

/--
lemma `Nonempty.smul_set` / 引理 `Nonempty.smul_set`

English:
lemma Nonempty.smul_set
  statement: s.Nonempty -> (a • s).Nonempty
  proof: Nonempty.image _

中文:
引理 Nonempty.smul_set
  结论: s.Nonempty -> (a • s).Nonempty
  证明: Nonempty.image _
-/
@[to_additive] lemma Nonempty.smul_set : s.Nonempty -> (a • s).Nonempty := Nonempty.image _

end SMulSet

section Pi

variable {M ι : Type*} {π : ι -> Type*} [forall i, SMul M (π i)]

@[to_additive]
/--
theorem `smul_set_pi_of_surjective` / 定理 `smul_set_pi_of_surjective`

English:
theorem smul_set_pi_of_surjective
  statement: (c : M) (I : Set ι) (s : forall i, Set (π i))
  proof: piMap_image_pi hsurj s

@[to_additive]

中文:
定理 smul_set_pi_of_surjective
  结论: (c : M) (I : Set ι) (s : 对任意 i, Set (π i))
  证明: piMap_image_pi hsurj s

@[to_additive]

Depends on / 依赖: piMap_image_pi
-/
theorem smul_set_pi_of_surjective (c : M) (I : Set ι) (s : forall i, Set (π i))
    (hsurj : forall i ∉ I, Function.Surjective (c • · : π i -> π i)) : c • I.pi s = I.pi (c • s) :=
  piMap_image_pi hsurj s

@[to_additive]
/--
theorem `smul_set_univ_pi` / 定理 `smul_set_univ_pi`

English:
theorem smul_set_univ_pi
  given: (c : M) (s : forall i, Set (π i))
  statement: c • univ.pi s = univ.pi (c • s)
  proof: piMap_image_univ_pi _ s

中文:
定理 smul_set_univ_pi
  条件: (c : M) (s : 对任意 i, Set (π i))
  结论: c • univ.pi s = univ.pi (c • s)
  证明: piMap_image_univ_pi _ s

Depends on / 依赖: piMap_image_univ_pi
-/
theorem smul_set_univ_pi (c : M) (s : forall i, Set (π i)) : c • univ.pi s = univ.pi (c • s) :=
  piMap_image_univ_pi _ s

end Pi

variable {s : Set α} {t : Set β} {a : α} {b : β}

@[to_additive]
/--
lemma `range_smul_range` / 引理 `range_smul_range`

English:
lemma range_smul_range
  given: {ι κ : Type*} [SMul α β] (b : ι -> α) (c : κ -> β)
  proof: image2_range ..

@[to_additive]

中文:
引理 range_smul_range
  条件: {ι κ : 类型} [SMul α β] (b : ι -> α) (c : κ -> β)
  证明: image2_range ..

@[to_additive]

Depends on / 依赖: image2_range
-/
lemma range_smul_range {ι κ : Type*} [SMul α β] (b : ι -> α) (c : κ -> β) :
    range b • range c = range fun p : ι × κ => b p.1 • c p.2 :=
  image2_range ..

@[to_additive]
/--
lemma `smul_set_range` / 引理 `smul_set_range`

English:
lemma smul_set_range
  given: [SMul α β] {ι : Sort*} (a : α) (f : ι -> β)
  proof: (range_comp ..).symm

中文:
引理 smul_set_range
  条件: [SMul α β] {ι : Sort*} (a : α) (f : ι -> β)
  证明: (range_comp ..).symm

Depends on / 依赖: range_comp
-/
lemma smul_set_range [SMul α β] {ι : Sort*} (a : α) (f : ι -> β) :
    a • range f = range fun i => a • f i :=
  (range_comp ..).symm

/--
lemma `range_smul` / 引理 `range_smul`

English:
lemma range_smul
  given: [SMul α β] {ι : Sort*} (a : α) (f : ι -> β)
  proof: (smul_set_range ..).symm

中文:
引理 range_smul
  条件: [SMul α β] {ι : Sort*} (a : α) (f : ι -> β)
  证明: (smul_set_range ..).symm
-/
@[to_additive] lemma range_smul [SMul α β] {ι : Sort*} (a : α) (f : ι -> β) :
    range (fun i => a • f i) = a • range f := (smul_set_range ..).symm

end SMul

section SDiv
variable {ι : Sort*} {κ : ι -> Sort*} [SDiv α β] {s s₁ s₂ t t₁ t₂ : Set β} {u : Set α} {a : α}
  {b c : β}

@[to_additive]
/--
Instance `sdiv` / 实例 `sdiv`

English:
instance sdiv
  signature: : SDiv (Set α) (Set β) where sdiv
  body: image2 (· /ₛ ·)

@[to_additive (attr := simp)]

中文:
实例 sdiv
  签名: : SDiv (Set α) (Set β) where sdiv
  定义体: image2 (· /ₛ ·)

@[to_additive (attr := simp)]

Depends on / 依赖: image2
-/
instance sdiv : SDiv (Set α) (Set β) where sdiv := image2 (· /ₛ ·)

@[to_additive (attr := simp)]
/--
lemma `image2_sdiv` / 引理 `image2_sdiv`

English:
lemma image2_sdiv
  statement: image2 (· /ₛ ·) s t = s /ₛ t
  proof: rfl

@[to_additive Set.image_vsub_prod]

中文:
引理 image2_sdiv
  结论: image2 (· /ₛ ·) s t = s /ₛ t
  证明: rfl

@[to_additive Set.image_vsub_prod]
-/
lemma image2_sdiv : image2 (· /ₛ ·) s t = s /ₛ t := rfl

@[to_additive Set.image_vsub_prod]
/--
lemma `image_sdiv_prod` / 引理 `image_sdiv_prod`

English:
lemma image_sdiv_prod
  statement: (fun x : β × β => x.fst /ₛ x.snd) '' s ×ˢ t = s /ₛ t
  proof: image_prod _

@[to_additive]

中文:
引理 image_sdiv_prod
  结论: (fun x : β × β => x.fst /ₛ x.snd) '' s ×ˢ t = s /ₛ t
  证明: image_prod _

@[to_additive]

Depends on / 依赖: image_prod
-/
lemma image_sdiv_prod : (fun x : β × β => x.fst /ₛ x.snd) '' s ×ˢ t = s /ₛ t := image_prod _

@[to_additive]
/--
lemma `mem_sdiv` / 引理 `mem_sdiv`

English:
lemma mem_sdiv
  statement: a in s /ₛ t ↔ exists x in s, exists y in t, x /ₛ y = a
  proof: Iff.rfl

@[to_additive]

中文:
引理 mem_sdiv
  结论: a in s /ₛ t ↔ 存在 x in s, 存在 y in t, x /ₛ y = a
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
lemma mem_sdiv : a in s /ₛ t ↔ exists x in s, exists y in t, x /ₛ y = a := Iff.rfl

@[to_additive]
/--
lemma `sdiv_mem_sdiv` / 引理 `sdiv_mem_sdiv`

English:
lemma sdiv_mem_sdiv
  given: (hb : b in s) (hc : c in t)
  statement: b /ₛ c in s /ₛ t
  proof: mem_image2_of_mem hb hc

@[to_additive (attr := simp)]

中文:
引理 sdiv_mem_sdiv
  条件: (hb : b in s) (hc : c in t)
  结论: b /ₛ c in s /ₛ t
  证明: mem_image2_of_mem hb hc

@[to_additive (attr := simp)]

Depends on / 依赖: mem_image2_of_mem
-/
lemma sdiv_mem_sdiv (hb : b in s) (hc : c in t) : b /ₛ c in s /ₛ t := mem_image2_of_mem hb hc

@[to_additive (attr := simp)]
/--
lemma `empty_sdiv` / 引理 `empty_sdiv`

English:
lemma empty_sdiv
  given: (t : Set β)
  statement: ∅ /ₛ t = ∅
  proof: image2_empty_left

@[to_additive (attr := simp)]

中文:
引理 empty_sdiv
  条件: (t : Set β)
  结论: ∅ /ₛ t = ∅
  证明: image2_empty_left

@[to_additive (attr := simp)]

Depends on / 依赖: image2_empty_left
-/
lemma empty_sdiv (t : Set β) : ∅ /ₛ t = ∅ := image2_empty_left

@[to_additive (attr := simp)]
/--
lemma `sdiv_empty` / 引理 `sdiv_empty`

English:
lemma sdiv_empty
  given: (s : Set β)
  statement: s /ₛ ∅ = ∅
  proof: image2_empty_right

@[to_additive (attr := simp)]

中文:
引理 sdiv_empty
  条件: (s : Set β)
  结论: s /ₛ ∅ = ∅
  证明: image2_empty_right

@[to_additive (attr := simp)]

Depends on / 依赖: image2_empty_right
-/
lemma sdiv_empty (s : Set β) : s /ₛ ∅ = ∅ := image2_empty_right

@[to_additive (attr := simp)]
/--
lemma `sdiv_eq_empty` / 引理 `sdiv_eq_empty`

English:
lemma sdiv_eq_empty
  statement: s /ₛ t = ∅ ↔ s = ∅ ∨ t = ∅
  proof: image2_eq_empty_iff

@[to_additive (attr := simp)]

中文:
引理 sdiv_eq_empty
  结论: s /ₛ t = ∅ ↔ s = ∅ ∨ t = ∅
  证明: image2_eq_empty_iff

@[to_additive (attr := simp)]

Depends on / 依赖: image2_eq_empty_iff
-/
lemma sdiv_eq_empty : s /ₛ t = ∅ ↔ s = ∅ ∨ t = ∅ := image2_eq_empty_iff

@[to_additive (attr := simp)]
/--
lemma `sdiv_nonempty` / 引理 `sdiv_nonempty`

English:
lemma sdiv_nonempty
  statement: (s /ₛ t : Set α).Nonempty ↔ s.Nonempty ∧ t.Nonempty
  proof: image2_nonempty_iff

@[to_additive]

中文:
引理 sdiv_nonempty
  结论: (s /ₛ t : Set α).Nonempty ↔ s.Nonempty ∧ t.Nonempty
  证明: image2_nonempty_iff

@[to_additive]

Depends on / 依赖: image2_nonempty_iff
-/
lemma sdiv_nonempty : (s /ₛ t : Set α).Nonempty ↔ s.Nonempty ∧ t.Nonempty := image2_nonempty_iff

@[to_additive]
/--
lemma `Nonempty.sdiv` / 引理 `Nonempty.sdiv`

English:
lemma Nonempty.sdiv
  statement: s.Nonempty -> t.Nonempty -> (s /ₛ t : Set α).Nonempty
  proof: .image2

@[to_additive]

中文:
引理 Nonempty.sdiv
  结论: s.Nonempty -> t.Nonempty -> (s /ₛ t : Set α).Nonempty
  证明: .image2

@[to_additive]

Depends on / 依赖: image2
-/
lemma Nonempty.sdiv : s.Nonempty -> t.Nonempty -> (s /ₛ t : Set α).Nonempty := .image2

@[to_additive]
/--
lemma `Nonempty.of_sdiv_left` / 引理 `Nonempty.of_sdiv_left`

English:
lemma Nonempty.of_sdiv_left
  statement: (s /ₛ t : Set α).Nonempty -> s.Nonempty
  proof: .of_image2_left

@[to_additive]

中文:
引理 Nonempty.of_sdiv_left
  结论: (s /ₛ t : Set α).Nonempty -> s.Nonempty
  证明: .of_image2_left

@[to_additive]

Depends on / 依赖: of_image2_left
-/
lemma Nonempty.of_sdiv_left : (s /ₛ t : Set α).Nonempty -> s.Nonempty := .of_image2_left

@[to_additive]
/--
lemma `Nonempty.of_sdiv_right` / 引理 `Nonempty.of_sdiv_right`

English:
lemma Nonempty.of_sdiv_right
  statement: (s /ₛ t : Set α).Nonempty -> t.Nonempty
  proof: .of_image2_right

@[to_additive (attr := simp low + 1)]

中文:
引理 Nonempty.of_sdiv_right
  结论: (s /ₛ t : Set α).Nonempty -> t.Nonempty
  证明: .of_image2_right

@[to_additive (attr := simp low + 1)]

Depends on / 依赖: of_image2_right
-/
lemma Nonempty.of_sdiv_right : (s /ₛ t : Set α).Nonempty -> t.Nonempty := .of_image2_right

@[to_additive (attr := simp low + 1)]
/--
lemma `sdiv_singleton` / 引理 `sdiv_singleton`

English:
lemma sdiv_singleton
  given: (s : Set β) (b : β)
  statement: s /ₛ {b} = (· /ₛ b) '' s
  proof: image2_singleton_right

@[to_additive (attr := simp low + 1)]

中文:
引理 sdiv_singleton
  条件: (s : Set β) (b : β)
  结论: s /ₛ {b} = (· /ₛ b) '' s
  证明: image2_singleton_right

@[to_additive (attr := simp low + 1)]

Depends on / 依赖: image2_singleton_right
-/
lemma sdiv_singleton (s : Set β) (b : β) : s /ₛ {b} = (· /ₛ b) '' s := image2_singleton_right

@[to_additive (attr := simp low + 1)]
/--
lemma `singleton_sdiv` / 引理 `singleton_sdiv`

English:
lemma singleton_sdiv
  given: (t : Set β) (b : β)
  statement: {b} /ₛ t = (b /ₛ ·) '' t
  proof: image2_singleton_left

@[to_additive (attr := simp high)]

中文:
引理 singleton_sdiv
  条件: (t : Set β) (b : β)
  结论: {b} /ₛ t = (b /ₛ ·) '' t
  证明: image2_singleton_left

@[to_additive (attr := simp high)]

Depends on / 依赖: image2_singleton_left
-/
lemma singleton_sdiv (t : Set β) (b : β) : {b} /ₛ t = (b /ₛ ·) '' t := image2_singleton_left

@[to_additive (attr := simp high)]
/--
lemma `singleton_sdiv_singleton` / 引理 `singleton_sdiv_singleton`

English:
lemma singleton_sdiv_singleton
  statement: ({b} : Set β) /ₛ {c} = {b /ₛ c}
  proof: image2_singleton

@[to_additive (attr := mono, gcongr)]

中文:
引理 singleton_sdiv_singleton
  结论: ({b} : Set β) /ₛ {c} = {b /ₛ c}
  证明: image2_singleton

@[to_additive (attr := mono, gcongr)]

Depends on / 依赖: image2_singleton
-/
lemma singleton_sdiv_singleton : ({b} : Set β) /ₛ {c} = {b /ₛ c} := image2_singleton

@[to_additive (attr := mono, gcongr)]
/--
lemma `sdiv_subset_sdiv` / 引理 `sdiv_subset_sdiv`

English:
lemma sdiv_subset_sdiv
  statement: s₁ subseteq s₂ -> t₁ subseteq t₂ -> s₁ /ₛ t₁ subseteq s₂ /ₛ t₂
  proof: image2_subset

@[to_additive]

中文:
引理 sdiv_subset_sdiv
  结论: s₁ subseteq s₂ -> t₁ subseteq t₂ -> s₁ /ₛ t₁ subseteq s₂ /ₛ t₂
  证明: image2_subset

@[to_additive]

Depends on / 依赖: image2_subset
-/
lemma sdiv_subset_sdiv : s₁ subseteq s₂ -> t₁ subseteq t₂ -> s₁ /ₛ t₁ subseteq s₂ /ₛ t₂ := image2_subset

@[to_additive]
/--
lemma `sdiv_subset_sdiv_left` / 引理 `sdiv_subset_sdiv_left`

English:
lemma sdiv_subset_sdiv_left
  statement: t₁ subseteq t₂ -> s /ₛ t₁ subseteq s /ₛ t₂
  proof: image2_subset_left

@[to_additive]

中文:
引理 sdiv_subset_sdiv_left
  结论: t₁ subseteq t₂ -> s /ₛ t₁ subseteq s /ₛ t₂
  证明: image2_subset_left

@[to_additive]

Depends on / 依赖: image2_subset_left
-/
lemma sdiv_subset_sdiv_left : t₁ subseteq t₂ -> s /ₛ t₁ subseteq s /ₛ t₂ := image2_subset_left

@[to_additive]
/--
lemma `sdiv_subset_sdiv_right` / 引理 `sdiv_subset_sdiv_right`

English:
lemma sdiv_subset_sdiv_right
  statement: s₁ subseteq s₂ -> s₁ /ₛ t subseteq s₂ /ₛ t
  proof: image2_subset_right

@[to_additive]

中文:
引理 sdiv_subset_sdiv_right
  结论: s₁ subseteq s₂ -> s₁ /ₛ t subseteq s₂ /ₛ t
  证明: image2_subset_right

@[to_additive]

Depends on / 依赖: image2_subset_right
-/
lemma sdiv_subset_sdiv_right : s₁ subseteq s₂ -> s₁ /ₛ t subseteq s₂ /ₛ t := image2_subset_right

@[to_additive]
/--
lemma `sdiv_subset_iff` / 引理 `sdiv_subset_iff`

English:
lemma sdiv_subset_iff
  statement: s /ₛ t subseteq u ↔ forall x in s, forall y in t, x /ₛ y in u
  proof: image2_subset_iff

@[to_additive]

中文:
引理 sdiv_subset_iff
  结论: s /ₛ t subseteq u ↔ 对任意 x in s, 对任意 y in t, x /ₛ y in u
  证明: image2_subset_iff

@[to_additive]

Depends on / 依赖: image2_subset_iff
-/
lemma sdiv_subset_iff : s /ₛ t subseteq u ↔ forall x in s, forall y in t, x /ₛ y in u := image2_subset_iff

@[to_additive]
/--
lemma `sdiv_self_mono` / 引理 `sdiv_self_mono`

English:
lemma sdiv_self_mono
  given: (h : s subseteq t)
  statement: s /ₛ s subseteq t /ₛ t
  proof: sdiv_subset_sdiv h h

@[to_additive]

中文:
引理 sdiv_self_mono
  条件: (h : s subseteq t)
  结论: s /ₛ s subseteq t /ₛ t
  证明: sdiv_subset_sdiv h h

@[to_additive]

Depends on / 依赖: sdiv_subset_sdiv
-/
lemma sdiv_self_mono (h : s subseteq t) : s /ₛ s subseteq t /ₛ t := sdiv_subset_sdiv h h

@[to_additive]
/--
lemma `union_sdiv` / 引理 `union_sdiv`

English:
lemma union_sdiv
  statement: s₁ union s₂ /ₛ t = s₁ /ₛ t union (s₂ /ₛ t)
  proof: image2_union_left

@[to_additive]

中文:
引理 union_sdiv
  结论: s₁ union s₂ /ₛ t = s₁ /ₛ t union (s₂ /ₛ t)
  证明: image2_union_left

@[to_additive]

Depends on / 依赖: image2_union_left
-/
lemma union_sdiv : s₁ union s₂ /ₛ t = s₁ /ₛ t union (s₂ /ₛ t) := image2_union_left

@[to_additive]
/--
lemma `sdiv_union` / 引理 `sdiv_union`

English:
lemma sdiv_union
  statement: s /ₛ (t₁ union t₂) = s /ₛ t₁ union (s /ₛ t₂)
  proof: image2_union_right

@[to_additive]

中文:
引理 sdiv_union
  结论: s /ₛ (t₁ union t₂) = s /ₛ t₁ union (s /ₛ t₂)
  证明: image2_union_right

@[to_additive]

Depends on / 依赖: image2_union_right
-/
lemma sdiv_union : s /ₛ (t₁ union t₂) = s /ₛ t₁ union (s /ₛ t₂) := image2_union_right

@[to_additive]
/--
lemma `inter_sdiv_subset` / 引理 `inter_sdiv_subset`

English:
lemma inter_sdiv_subset
  statement: s₁ inter s₂ /ₛ t subseteq (s₁ /ₛ t) inter (s₂ /ₛ t)
  proof: image2_inter_subset_left

@[to_additive]

中文:
引理 inter_sdiv_subset
  结论: s₁ inter s₂ /ₛ t subseteq (s₁ /ₛ t) inter (s₂ /ₛ t)
  证明: image2_inter_subset_left

@[to_additive]

Depends on / 依赖: image2_inter_subset_left
-/
lemma inter_sdiv_subset : s₁ inter s₂ /ₛ t subseteq (s₁ /ₛ t) inter (s₂ /ₛ t) := image2_inter_subset_left

@[to_additive]
/--
lemma `sdiv_inter_subset` / 引理 `sdiv_inter_subset`

English:
lemma sdiv_inter_subset
  statement: s /ₛ t₁ inter t₂ subseteq (s /ₛ t₁) inter (s /ₛ t₂)
  proof: image2_inter_subset_right

@[to_additive]

中文:
引理 sdiv_inter_subset
  结论: s /ₛ t₁ inter t₂ subseteq (s /ₛ t₁) inter (s /ₛ t₂)
  证明: image2_inter_subset_right

@[to_additive]

Depends on / 依赖: image2_inter_subset_right
-/
lemma sdiv_inter_subset : s /ₛ t₁ inter t₂ subseteq (s /ₛ t₁) inter (s /ₛ t₂) := image2_inter_subset_right

@[to_additive]
/--
lemma `inter_sdiv_union_subset_union` / 引理 `inter_sdiv_union_subset_union`

English:
lemma inter_sdiv_union_subset_union
  statement: s₁ inter s₂ /ₛ (t₁ union t₂) subseteq s₁ /ₛ t₁ union (s₂ /ₛ t₂)
  proof: image2_inter_union_subset_union

@[to_additive]

中文:
引理 inter_sdiv_union_subset_union
  结论: s₁ inter s₂ /ₛ (t₁ union t₂) subseteq s₁ /ₛ t₁ union (s₂ /ₛ t₂)
  证明: image2_inter_union_subset_union

@[to_additive]

Depends on / 依赖: image2_inter_union_subset_union
-/
lemma inter_sdiv_union_subset_union : s₁ inter s₂ /ₛ (t₁ union t₂) subseteq s₁ /ₛ t₁ union (s₂ /ₛ t₂) :=
  image2_inter_union_subset_union

@[to_additive]
/--
lemma `union_sdiv_inter_subset_union` / 引理 `union_sdiv_inter_subset_union`

English:
lemma union_sdiv_inter_subset_union
  statement: s₁ union s₂ /ₛ t₁ inter t₂ subseteq s₁ /ₛ t₁ union (s₂ /ₛ t₂)
  proof: image2_union_inter_subset_union

中文:
引理 union_sdiv_inter_subset_union
  结论: s₁ union s₂ /ₛ t₁ inter t₂ subseteq s₁ /ₛ t₁ union (s₂ /ₛ t₂)
  证明: image2_union_inter_subset_union

Depends on / 依赖: image2_union_inter_subset_union
-/
lemma union_sdiv_inter_subset_union : s₁ union s₂ /ₛ t₁ inter t₂ subseteq s₁ /ₛ t₁ union (s₂ /ₛ t₂) :=
  image2_union_inter_subset_union

end SDiv

open scoped Pointwise

@[to_additive]
/--
lemma `image_smul_comm` / 引理 `image_smul_comm`

English:
lemma image_smul_comm
  given: [SMul α β] [SMul α γ] (f : β -> γ) (a : α) (s : Set β)
  proof: image_comm

中文:
引理 image_smul_comm
  条件: [SMul α β] [SMul α γ] (f : β -> γ) (a : α) (s : Set β)
  证明: image_comm

Depends on / 依赖: image_comm
-/
lemma image_smul_comm [SMul α β] [SMul α γ] (f : β -> γ) (a : α) (s : Set β) :
    (forall b, f (a • b) = a • f b) -> f '' (a • s) = a • f '' s := image_comm

section SMul
variable [SMul αᵐᵒᵖ β] [SMul β γ] [SMul α γ]

-- TODO: replace hypothesis and conclusion with a typeclass
@[to_additive]
/--
lemma `op_smul_set_smul_eq_smul_smul_set` / 引理 `op_smul_set_smul_eq_smul_smul_set`

English:
lemma op_smul_set_smul_eq_smul_smul_set
  statement: (a : α) (s : Set β) (t : Set γ)
  proof: by
  ext; simp [mem_smul, mem_smul_set, h]

中文:
引理 op_smul_set_smul_eq_smul_smul_set
  结论: (a : α) (s : Set β) (t : Set γ)
  证明: by
  ext; simp [mem_smul, mem_smul_set, h]

Depends on / 依赖: mem_smul, mem_smul_set
-/
lemma op_smul_set_smul_eq_smul_smul_set (a : α) (s : Set β) (t : Set γ)
    (h : forall (a : α) (b : β) (c : γ), (op a • b) • c = b • a • c) : (op a • s) • t = s • a • t := by
  ext; simp [mem_smul, mem_smul_set, h]

end SMul

end Set
