/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Wrenna Robson, Violeta Hernández Palacios
-/
module

public import Mathlib.Data.Set.Lattice
public import Mathlib.Order.Closure

/-!
# Formal concept analysis

This file defines concept lattices. A concept of a relation `r : α → β → Prop` is a pair of sets
`s : Set α` and `t : Set β` such that `s` is the set of all `a : α` that are related to all elements
of `t`, and `t` is the set of all `b : β` that are related to all elements of `s`.

Ordering the concepts of a relation `r` by inclusion on the first component gives rise to a
*concept lattice*. Every concept lattice is complete and in fact every complete lattice arises as
the concept lattice of its `≤`.

## Implementation notes

Concept lattices are usually defined from a *context*, that is the triple `(α, β, r)`, but the type
of `r` determines `α` and `β` already, so we do not define contexts as a separate object.

## References

* [Davey, Priestley *Introduction to Lattices and Order*][davey_priestley]
* [Birkhoff, Garrett *Lattice Theory*][birkhoff1940]

## Tags

concept, formal concept analysis, intent, extent, object, attribute
-/

@[expose] public section


open Function OrderDual Order Set

variable {ι : Sort*} {α β γ : Type*} {κ : ι -> Sort*} (r : α -> β -> Prop) {s : Set α} {t : Set β}

/-! ### Lower and upper polars -/

/--
Definition of `upperPolar` / `upperPolar` 的定义

English:
definition upperPolar
  signature: (s : Set α)
  body: { b | forall ⦃a⦄, a in s -> r a b }

中文:
定义 upperPolar
  签名: (s : Set α)
  定义体: { b | forall ⦃a⦄, a in s -> r a b }
-/
def upperPolar (s : Set α) : Set β :=
  { b | forall ⦃a⦄, a in s -> r a b }

/--
Definition of `lowerPolar` / `lowerPolar` 的定义

English:
definition lowerPolar
  signature: (t : Set β)
  body: { a | forall ⦃b⦄, b in t -> r a b }

中文:
定义 lowerPolar
  签名: (t : Set β)
  定义体: { a | forall ⦃b⦄, b in t -> r a b }
-/
def lowerPolar (t : Set β) : Set α :=
  { a | forall ⦃b⦄, b in t -> r a b }

/--
theorem `upperPolar_le` / 定理 `upperPolar_le`

English:
theorem upperPolar_le
  given: [LE α]
  statement: upperPolar (· <= ·) s = upperBounds s
  proof: rfl

中文:
定理 upperPolar_le
  条件: [LE α]
  结论: upperPolar (· <= ·) s = upperBounds s
  证明: rfl
-/
@[simp] theorem upperPolar_le [LE α] : upperPolar (· <= ·) s = upperBounds s := rfl
/--
theorem `lowerPolar_le` / 定理 `lowerPolar_le`

English:
theorem lowerPolar_le
  given: [LE β]
  statement: lowerPolar (· <= ·) t = lowerBounds t
  proof: rfl

中文:
定理 lowerPolar_le
  条件: [LE β]
  结论: lowerPolar (· <= ·) t = lowerBounds t
  证明: rfl
-/
@[simp] theorem lowerPolar_le [LE β] : lowerPolar (· <= ·) t = lowerBounds t := rfl

variable {r} {a : α} {b : β}

/--
theorem `mem_upperPolar_iff` / 定理 `mem_upperPolar_iff`

English:
theorem mem_upperPolar_iff
  statement: b in upperPolar r s ↔ forall ⦃a⦄, a in s -> r a b
  proof: .rfl

中文:
定理 mem_upperPolar_iff
  结论: b in upperPolar r s ↔ 对任意 ⦃a⦄, a in s -> r a b
  证明: .rfl
-/
theorem mem_upperPolar_iff : b in upperPolar r s ↔ forall ⦃a⦄, a in s -> r a b := .rfl
/--
theorem `mem_lowerPolar_iff` / 定理 `mem_lowerPolar_iff`

English:
theorem mem_lowerPolar_iff
  statement: a in lowerPolar r t ↔ forall ⦃b⦄, b in t -> r a b
  proof: .rfl

中文:
定理 mem_lowerPolar_iff
  结论: a in lowerPolar r t ↔ 对任意 ⦃b⦄, b in t -> r a b
  证明: .rfl
-/
theorem mem_lowerPolar_iff : a in lowerPolar r t ↔ forall ⦃b⦄, b in t -> r a b := .rfl

/--
theorem `subset_upperPolar_iff_subset_lowerPolar` / 定理 `subset_upperPolar_iff_subset_lowerPolar`

English:
theorem subset_upperPolar_iff_subset_lowerPolar
  proof: ⟨fun h _ ha _ hb => h hb ha, fun h _ hb _ ha => h ha hb⟩

中文:
定理 subset_upperPolar_iff_subset_lowerPolar
  证明: ⟨fun h _ ha _ hb => h hb ha, fun h _ hb _ ha => h ha hb⟩
-/
theorem subset_upperPolar_iff_subset_lowerPolar :
    t subseteq upperPolar r s ↔ s subseteq lowerPolar r t :=
  ⟨fun h _ ha _ hb => h hb ha, fun h _ hb _ ha => h ha hb⟩

variable (r)

/--
theorem `gc_upperPolar_lowerPolar` / 定理 `gc_upperPolar_lowerPolar`

English:
theorem gc_upperPolar_lowerPolar
  proof: fun _ _ =>
  subset_upperPolar_iff_subset_lowerPolar

中文:
定理 gc_upperPolar_lowerPolar
  证明: fun _ _ =>
  subset_upperPolar_iff_subset_lowerPolar
-/
theorem gc_upperPolar_lowerPolar :
    GaloisConnection (toDual ∘ upperPolar r) (lowerPolar r ∘ ofDual) := fun _ _ =>
  subset_upperPolar_iff_subset_lowerPolar

/--
theorem `gc_lowerPolar_upperPolar` / 定理 `gc_lowerPolar_upperPolar`

English:
theorem gc_lowerPolar_upperPolar
  proof: fun _ _ =>
  subset_upperPolar_iff_subset_lowerPolar

中文:
定理 gc_lowerPolar_upperPolar
  证明: fun _ _ =>
  subset_upperPolar_iff_subset_lowerPolar
-/
theorem gc_lowerPolar_upperPolar :
    GaloisConnection (toDual ∘ lowerPolar r) (upperPolar r ∘ ofDual) := fun _ _ =>
  subset_upperPolar_iff_subset_lowerPolar

/--
theorem `upperPolar_swap` / 定理 `upperPolar_swap`

English:
theorem upperPolar_swap
  given: (t : Set β)
  statement: upperPolar (swap r) t = lowerPolar r t
  proof: rfl

中文:
定理 upperPolar_swap
  条件: (t : Set β)
  结论: upperPolar (swap r) t = lowerPolar r t
  证明: rfl
-/
theorem upperPolar_swap (t : Set β) : upperPolar (swap r) t = lowerPolar r t :=
  rfl

/--
theorem `lowerPolar_swap` / 定理 `lowerPolar_swap`

English:
theorem lowerPolar_swap
  given: (s : Set α)
  statement: lowerPolar (swap r) s = upperPolar r s
  proof: rfl

@[simp]

中文:
定理 lowerPolar_swap
  条件: (s : Set α)
  结论: lowerPolar (swap r) s = upperPolar r s
  证明: rfl

@[simp]
-/
theorem lowerPolar_swap (s : Set α) : lowerPolar (swap r) s = upperPolar r s :=
  rfl

@[simp]
/--
theorem `upperPolar_empty` / 定理 `upperPolar_empty`

English:
theorem upperPolar_empty
  statement: upperPolar r ∅ = univ
  proof: eq_univ_of_forall fun _ _ => False.elim

@[simp]

中文:
定理 upperPolar_empty
  结论: upperPolar r ∅ = univ
  证明: eq_univ_of_forall fun _ _ => False.elim

@[simp]

Depends on / 依赖: False.elim, eq_univ_of_forall
-/
theorem upperPolar_empty : upperPolar r ∅ = univ :=
  eq_univ_of_forall fun _ _ => False.elim

@[simp]
/--
theorem `lowerPolar_empty` / 定理 `lowerPolar_empty`

English:
theorem lowerPolar_empty
  statement: lowerPolar r ∅ = univ
  proof: upperPolar_empty _

@[simp]

中文:
定理 lowerPolar_empty
  结论: lowerPolar r ∅ = univ
  证明: upperPolar_empty _

@[simp]

Depends on / 依赖: upperPolar_empty
-/
theorem lowerPolar_empty : lowerPolar r ∅ = univ :=
  upperPolar_empty _

@[simp]
/--
theorem `mem_upperPolar_singleton` / 定理 `mem_upperPolar_singleton`

English:
theorem mem_upperPolar_singleton
  statement: b in upperPolar r {a} ↔ r a b
  proof: by
  simp_rw [mem_upperPolar_iff, mem_singleton_iff, forall_eq]

@[simp]

中文:
定理 mem_upperPolar_singleton
  结论: b in upperPolar r {a} ↔ r a b
  证明: by
  simp_rw [mem_upperPolar_iff, mem_singleton_iff, forall_eq]

@[simp]

Depends on / 依赖: forall_eq, mem_singleton_iff, mem_upperPolar_iff, simp_rw
-/
theorem mem_upperPolar_singleton : b in upperPolar r {a} ↔ r a b := by
  simp_rw [mem_upperPolar_iff, mem_singleton_iff, forall_eq]

@[simp]
/--
theorem `mem_lowerPolar_singleton` / 定理 `mem_lowerPolar_singleton`

English:
theorem mem_lowerPolar_singleton
  statement: a in lowerPolar r {b} ↔ r a b
  proof: by
  simp_rw [mem_lowerPolar_iff, mem_singleton_iff, forall_eq]

@[simp]

中文:
定理 mem_lowerPolar_singleton
  结论: a in lowerPolar r {b} ↔ r a b
  证明: by
  simp_rw [mem_lowerPolar_iff, mem_singleton_iff, forall_eq]

@[simp]

Depends on / 依赖: forall_eq, mem_lowerPolar_iff, mem_singleton_iff, simp_rw
-/
theorem mem_lowerPolar_singleton : a in lowerPolar r {b} ↔ r a b := by
  simp_rw [mem_lowerPolar_iff, mem_singleton_iff, forall_eq]

@[simp]
/--
theorem `upperPolar_union` / 定理 `upperPolar_union`

English:
theorem upperPolar_union
  given: (s₁ s₂ : Set α)
  proof: ext fun _ => forall₂_or_left

@[simp]

中文:
定理 upperPolar_union
  条件: (s₁ s₂ : Set α)
  证明: ext fun _ => forall₂_or_left

@[simp]
-/
theorem upperPolar_union (s₁ s₂ : Set α) :
    upperPolar r (s₁ union s₂) = upperPolar r s₁ inter upperPolar r s₂ :=
  ext fun _ => forall₂_or_left

@[simp]
/--
theorem `lowerPolar_union` / 定理 `lowerPolar_union`

English:
theorem lowerPolar_union
  given: (t₁ t₂ : Set β)
  proof: upperPolar_union ..

@[simp]

中文:
定理 lowerPolar_union
  条件: (t₁ t₂ : Set β)
  证明: upperPolar_union ..

@[simp]

Depends on / 依赖: upperPolar_union
-/
theorem lowerPolar_union (t₁ t₂ : Set β) :
    lowerPolar r (t₁ union t₂) = lowerPolar r t₁ inter lowerPolar r t₂ :=
  upperPolar_union ..

@[simp]
/--
theorem `upperPolar_iUnion` / 定理 `upperPolar_iUnion`

English:
theorem upperPolar_iUnion
  given: (f : ι -> Set α)
  proof: (gc_upperPolar_lowerPolar r).l_iSup

@[simp]

中文:
定理 upperPolar_iUnion
  条件: (f : ι -> Set α)
  证明: (gc_upperPolar_lowerPolar r).l_iSup

@[simp]

Depends on / 依赖: gc_upperPolar_lowerPolar, l_iSup
-/
theorem upperPolar_iUnion (f : ι -> Set α) :
    upperPolar r (⋃ i, f i) = ⋂ i, upperPolar r (f i) :=
  (gc_upperPolar_lowerPolar r).l_iSup

@[simp]
/--
theorem `lowerPolar_iUnion` / 定理 `lowerPolar_iUnion`

English:
theorem lowerPolar_iUnion
  given: (f : ι -> Set β)
  proof: upperPolar_iUnion ..

中文:
定理 lowerPolar_iUnion
  条件: (f : ι -> Set β)
  证明: upperPolar_iUnion ..

Depends on / 依赖: upperPolar_iUnion
-/
theorem lowerPolar_iUnion (f : ι -> Set β) :
    lowerPolar r (⋃ i, f i) = ⋂ i, lowerPolar r (f i) :=
  upperPolar_iUnion ..

/--
theorem `upperPolar_iUnion₂` / 定理 `upperPolar_iUnion₂`

English:
theorem upperPolar_iUnion₂
  given: (f : forall i, κ i -> Set α)
  proof: (gc_upperPolar_lowerPolar r).l_iSup₂

中文:
定理 upperPolar_iUnion₂
  条件: (f : 对任意 i, κ i -> Set α)
  证明: (gc_upperPolar_lowerPolar r).l_iSup₂

Depends on / 依赖: gc_upperPolar_lowerPolar
-/
theorem upperPolar_iUnion₂ (f : forall i, κ i -> Set α) :
    upperPolar r (⋃ (i) (j), f i j) = ⋂ (i) (j), upperPolar r (f i j) :=
  (gc_upperPolar_lowerPolar r).l_iSup₂

/--
theorem `lowerPolar_iUnion₂` / 定理 `lowerPolar_iUnion₂`

English:
theorem lowerPolar_iUnion₂
  given: (f : forall i, κ i -> Set β)
  proof: upperPolar_iUnion₂ ..

中文:
定理 lowerPolar_iUnion₂
  条件: (f : 对任意 i, κ i -> Set β)
  证明: upperPolar_iUnion₂ ..
-/
theorem lowerPolar_iUnion₂ (f : forall i, κ i -> Set β) :
    lowerPolar r (⋃ (i) (j), f i j) = ⋂ (i) (j), lowerPolar r (f i j) :=
  upperPolar_iUnion₂ ..

/--
theorem `subset_lowerPolar_upperPolar` / 定理 `subset_lowerPolar_upperPolar`

English:
theorem subset_lowerPolar_upperPolar
  given: (s : Set α)
  proof: (gc_upperPolar_lowerPolar r).le_u_l _

中文:
定理 subset_lowerPolar_upperPolar
  条件: (s : Set α)
  证明: (gc_upperPolar_lowerPolar r).le_u_l _

Depends on / 依赖: gc_upperPolar_lowerPolar, le_u_l
-/
theorem subset_lowerPolar_upperPolar (s : Set α) :
    s subseteq lowerPolar r (upperPolar r s) :=
  (gc_upperPolar_lowerPolar r).le_u_l _

/--
theorem `subset_upperPolar_lowerPolar` / 定理 `subset_upperPolar_lowerPolar`

English:
theorem subset_upperPolar_lowerPolar
  given: (t : Set β)
  proof: subset_lowerPolar_upperPolar _ t

@[simp]

中文:
定理 subset_upperPolar_lowerPolar
  条件: (t : Set β)
  证明: subset_lowerPolar_upperPolar _ t

@[simp]

Depends on / 依赖: subset_lowerPolar_upperPolar
-/
theorem subset_upperPolar_lowerPolar (t : Set β) :
    t subseteq upperPolar r (lowerPolar r t) :=
  subset_lowerPolar_upperPolar _ t

@[simp]
/--
theorem `upperPolar_lowerPolar_upperPolar` / 定理 `upperPolar_lowerPolar_upperPolar`

English:
theorem upperPolar_lowerPolar_upperPolar
  given: (s : Set α)
  proof: (gc_upperPolar_lowerPolar r).l_u_l_eq_l _

@[simp]

中文:
定理 upperPolar_lowerPolar_upperPolar
  条件: (s : Set α)
  证明: (gc_upperPolar_lowerPolar r).l_u_l_eq_l _

@[simp]

Depends on / 依赖: gc_upperPolar_lowerPolar, l_u_l_eq_l
-/
theorem upperPolar_lowerPolar_upperPolar (s : Set α) :
    upperPolar r (lowerPolar r <| upperPolar r s) = upperPolar r s :=
  (gc_upperPolar_lowerPolar r).l_u_l_eq_l _

@[simp]
/--
theorem `lowerPolar_upperPolar_lowerPolar` / 定理 `lowerPolar_upperPolar_lowerPolar`

English:
theorem lowerPolar_upperPolar_lowerPolar
  given: (t : Set β)
  proof: upperPolar_lowerPolar_upperPolar _ t

中文:
定理 lowerPolar_upperPolar_lowerPolar
  条件: (t : Set β)
  证明: upperPolar_lowerPolar_upperPolar _ t

Depends on / 依赖: upperPolar_lowerPolar_upperPolar
-/
theorem lowerPolar_upperPolar_lowerPolar (t : Set β) :
    lowerPolar r (upperPolar r <| lowerPolar r t) = lowerPolar r t :=
  upperPolar_lowerPolar_upperPolar _ t

/--
theorem `upperPolar_anti` / 定理 `upperPolar_anti`

English:
theorem upperPolar_anti
  statement: Antitone (upperPolar r)
  proof: (gc_upperPolar_lowerPolar r).monotone_l

中文:
定理 upperPolar_anti
  结论: Antitone (upperPolar r)
  证明: (gc_upperPolar_lowerPolar r).monotone_l

Depends on / 依赖: gc_upperPolar_lowerPolar, monotone_l
-/
theorem upperPolar_anti : Antitone (upperPolar r) :=
  (gc_upperPolar_lowerPolar r).monotone_l

/--
theorem `lowerPolar_anti` / 定理 `lowerPolar_anti`

English:
theorem lowerPolar_anti
  statement: Antitone (lowerPolar r)
  proof: upperPolar_anti _

中文:
定理 lowerPolar_anti
  结论: Antitone (lowerPolar r)
  证明: upperPolar_anti _

Depends on / 依赖: upperPolar_anti
-/
theorem lowerPolar_anti : Antitone (lowerPolar r) :=
  upperPolar_anti _

/--
theorem `lowerPolar_upperPolar_monotone` / 定理 `lowerPolar_upperPolar_monotone`

English:
theorem lowerPolar_upperPolar_monotone
  statement: Monotone (lowerPolar r ∘ upperPolar r)
  proof: (gc_upperPolar_lowerPolar r).monotone_u_comp_l

中文:
定理 lowerPolar_upperPolar_monotone
  结论: Monotone (lowerPolar r ∘ upperPolar r)
  证明: (gc_upperPolar_lowerPolar r).monotone_u_comp_l

Depends on / 依赖: gc_upperPolar_lowerPolar, monotone_u_comp_l
-/
theorem lowerPolar_upperPolar_monotone : Monotone (lowerPolar r ∘ upperPolar r) :=
  (gc_upperPolar_lowerPolar r).monotone_u_comp_l

/--
theorem `upperPolar_lowerPolar_monotone` / 定理 `upperPolar_lowerPolar_monotone`

English:
theorem upperPolar_lowerPolar_monotone
  statement: Monotone (upperPolar r ∘ lowerPolar r)
  proof: (gc_lowerPolar_upperPolar r).monotone_u_comp_l

中文:
定理 upperPolar_lowerPolar_monotone
  结论: Monotone (upperPolar r ∘ lowerPolar r)
  证明: (gc_lowerPolar_upperPolar r).monotone_u_comp_l

Depends on / 依赖: gc_lowerPolar_upperPolar, monotone_u_comp_l
-/
theorem upperPolar_lowerPolar_monotone : Monotone (upperPolar r ∘ lowerPolar r) :=
  (gc_lowerPolar_upperPolar r).monotone_u_comp_l

/-- The `extentClosure` of a set is the smallest extent containing it. See
`IsExtent.lowerPolar_upperPolar_subset` for this proof. -/
@[simps!]
/--
Definition of `extentClosure` / `extentClosure` 的定义

English:
definition extentClosure
  signature: (r : α -> β -> Prop)
  body: (gc_upperPolar_lowerPolar r).closureOperator

中文:
定义 extentClosure
  签名: (r : α -> β -> 命题)
  定义体: (gc_upperPolar_lowerPolar r).closureOperator

Depends on / 依赖: closureOperator, gc_upperPolar_lowerPolar
-/
def extentClosure (r : α -> β -> Prop) : ClosureOperator (Set α) :=
  (gc_upperPolar_lowerPolar r).closureOperator

/-- The `intentClosure` of a set is the smallest intent containing it. See
`IsIntent.upperPolar_lowerPolar_subset` for this proof. -/
@[simps!]
/--
Definition of `intentClosure` / `intentClosure` 的定义

English:
definition intentClosure
  signature: (r : α -> β -> Prop)
  body: (gc_lowerPolar_upperPolar r).closureOperator

中文:
定义 intentClosure
  签名: (r : α -> β -> 命题)
  定义体: (gc_lowerPolar_upperPolar r).closureOperator

Depends on / 依赖: closureOperator, gc_lowerPolar_upperPolar
-/
def intentClosure (r : α -> β -> Prop) : ClosureOperator (Set β) :=
  (gc_lowerPolar_upperPolar r).closureOperator

/-! ### Intent and extent -/

namespace Order

variable {r}

/--
Definition of `IsExtent` / `IsExtent` 的定义

English:
definition IsExtent
  signature: (r : α -> β -> Prop) (s : Set α)
  body: s in range (lowerPolar r)

中文:
定义 IsExtent
  签名: (r : α -> β -> 命题) (s : Set α)
  定义体: s in range (lowerPolar r)

Depends on / 依赖: lowerPolar
-/
def IsExtent (r : α -> β -> Prop) (s : Set α) := s in range (lowerPolar r)

/--
theorem `isExtent_lowerPolar` / 定理 `isExtent_lowerPolar`

English:
theorem isExtent_lowerPolar
  statement: IsExtent r (lowerPolar r t)
  proof: ⟨_, rfl⟩

中文:
定理 isExtent_lowerPolar
  结论: IsExtent r (lowerPolar r t)
  证明: ⟨_, rfl⟩
-/
@[simp] theorem isExtent_lowerPolar : IsExtent r (lowerPolar r t) := ⟨_, rfl⟩

/--
theorem `isExtent_iff` / 定理 `isExtent_iff`

English:
theorem isExtent_iff
  statement: IsExtent r s ↔ lowerPolar r (upperPolar r s) = s
  proof: ⟨fun ⟨t, h⟩ => h ▸ lowerPolar_upperPolar_lowerPolar r t, fun h => ⟨_, h⟩⟩

alias ⟨IsExtent.eq, _⟩ := isExtent_iff

@[simp]

中文:
定理 isExtent_iff
  结论: IsExtent r s ↔ lowerPolar r (upperPolar r s) = s
  证明: ⟨fun ⟨t, h⟩ => h ▸ lowerPolar_upperPolar_lowerPolar r t, fun h => ⟨_, h⟩⟩

alias ⟨IsExtent.eq, _⟩ := isExtent_iff

@[simp]

Depends on / 依赖: lowerPolar_upperPolar_lowerPolar
-/
theorem isExtent_iff : IsExtent r s ↔ lowerPolar r (upperPolar r s) = s :=
  ⟨fun ⟨t, h⟩ => h ▸ lowerPolar_upperPolar_lowerPolar r t, fun h => ⟨_, h⟩⟩

alias ⟨IsExtent.eq, _⟩ := isExtent_iff

@[simp]
/--
theorem `IsExtent.univ` / 定理 `IsExtent.univ`

English:
theorem IsExtent.univ
  statement: IsExtent r univ
  proof: isExtent_iff.2 (gc_upperPolar_lowerPolar r).u_l_top

中文:
定理 IsExtent.univ
  结论: IsExtent r univ
  证明: isExtent_iff.2 (gc_upperPolar_lowerPolar r).u_l_top
-/
protected theorem IsExtent.univ : IsExtent r univ :=
  isExtent_iff.2 (gc_upperPolar_lowerPolar r).u_l_top

/--
theorem `IsExtent.inter` / 定理 `IsExtent.inter`

English:
theorem IsExtent.inter
  given: {s' : Set α}
  proof: by
  simp_rw [IsExtent, mem_range, forall_exists_index]
  rintro t rfl t' rfl
  exact ⟨_, lowerPolar_union r t t'⟩

中文:
定理 IsExtent.inter
  条件: {s' : Set α}
  证明: by
  simp_rw [IsExtent, mem_range, forall_exists_index]
  rintro t rfl t' rfl
  exact ⟨_, lowerPolar_union r t t'⟩
-/
protected theorem IsExtent.inter {s' : Set α} :
    IsExtent r s -> IsExtent r s' -> IsExtent r (s inter s') := by
  simp_rw [IsExtent, mem_range, forall_exists_index]
  rintro t rfl t' rfl
  exact ⟨_, lowerPolar_union r t t'⟩

/--
theorem `IsExtent.iInter` / 定理 `IsExtent.iInter`

English:
theorem IsExtent.iInter
  given: (f : ι -> Set α) (hf : forall i, IsExtent r (f i))
  proof: ⟨_, (lowerPolar_iUnion ..).trans (iInter_congr fun i => (hf i).eq)⟩

中文:
定理 IsExtent.iInter
  条件: (f : ι -> Set α) (hf : 对任意 i, IsExtent r (f i))
  证明: ⟨_, (lowerPolar_iUnion ..).trans (iInter_congr fun i => (hf i).eq)⟩
-/
protected theorem IsExtent.iInter (f : ι -> Set α) (hf : forall i, IsExtent r (f i)) :
    IsExtent r (⋂ i, f i) :=
  ⟨_, (lowerPolar_iUnion ..).trans (iInter_congr fun i => (hf i).eq)⟩

/--
theorem `IsExtent.iInter₂` / 定理 `IsExtent.iInter₂`

English:
theorem IsExtent.iInter₂
  given: (f : forall i, κ i -> Set α) (hf : forall i j, IsExtent r (f i j))
  proof: ⟨_, (lowerPolar_iUnion₂ ..).trans (iInter₂_congr fun i j => (hf i j).eq)⟩

中文:
定理 IsExtent.iInter₂
  条件: (f : 对任意 i, κ i -> Set α) (hf : 对任意 i j, IsExtent r (f i j))
  证明: ⟨_, (lowerPolar_iUnion₂ ..).trans (iInter₂_congr fun i j => (hf i j).eq)⟩
-/
protected theorem IsExtent.iInter₂ (f : forall i, κ i -> Set α) (hf : forall i j, IsExtent r (f i j)) :
    IsExtent r (⋂ (i) (j), f i j) :=
  ⟨_, (lowerPolar_iUnion₂ ..).trans (iInter₂_congr fun i j => (hf i j).eq)⟩

/--
theorem `IsExtent.lowerPolar_upperPolar_subset` / 定理 `IsExtent.lowerPolar_upperPolar_subset`

English:
theorem IsExtent.lowerPolar_upperPolar_subset
  given: {s' : Set α} (h : IsExtent r s) (hs' : s' subseteq s)
  proof: by
  rw [← h.eq]
  exact lowerPolar_upperPolar_monotone r hs'

中文:
定理 IsExtent.lowerPolar_upperPolar_subset
  条件: {s' : Set α} (h : IsExtent r s) (hs' : s' subseteq s)
  证明: by
  rw [← h.eq]
  exact lowerPolar_upperPolar_monotone r hs'

Depends on / 依赖: h.eq, lowerPolar_upperPolar_monotone
-/
theorem IsExtent.lowerPolar_upperPolar_subset {s' : Set α} (h : IsExtent r s) (hs' : s' subseteq s) :
    lowerPolar r (upperPolar r s') subseteq s := by
  rw [← h.eq]
  exact lowerPolar_upperPolar_monotone r hs'

/--
Definition of `IsIntent` / `IsIntent` 的定义

English:
definition IsIntent
  signature: (r : α -> β -> Prop) (t : Set β)
  body: t in range (upperPolar r)

中文:
定义 IsIntent
  签名: (r : α -> β -> 命题) (t : Set β)
  定义体: t in range (upperPolar r)

Depends on / 依赖: upperPolar
-/
def IsIntent (r : α -> β -> Prop) (t : Set β) := t in range (upperPolar r)

/--
theorem `isIntent_upperPolar` / 定理 `isIntent_upperPolar`

English:
theorem isIntent_upperPolar
  statement: IsIntent r (upperPolar r s)
  proof: ⟨_, rfl⟩

中文:
定理 isIntent_upperPolar
  结论: Is整数ent r (upperPolar r s)
  证明: ⟨_, rfl⟩
-/
@[simp] theorem isIntent_upperPolar : IsIntent r (upperPolar r s) := ⟨_, rfl⟩

/--
theorem `isIntent_iff` / 定理 `isIntent_iff`

English:
theorem isIntent_iff
  statement: IsIntent r t ↔ upperPolar r (lowerPolar r t) = t
  proof: isExtent_iff

alias ⟨IsIntent.eq, _⟩ := isIntent_iff

中文:
定理 isIntent_iff
  结论: Is整数ent r t ↔ upperPolar r (lowerPolar r t) = t
  证明: isExtent_iff

alias ⟨IsIntent.eq, _⟩ := isIntent_iff

Depends on / 依赖: isExtent_iff
-/
theorem isIntent_iff : IsIntent r t ↔ upperPolar r (lowerPolar r t) = t := isExtent_iff

alias ⟨IsIntent.eq, _⟩ := isIntent_iff

/--
theorem `IsIntent.univ` / 定理 `IsIntent.univ`

English:
theorem IsIntent.univ
  statement: IsIntent r univ
  proof: IsExtent.univ

中文:
定理 IsIntent.univ
  结论: Is整数ent r univ
  证明: IsExtent.univ
-/
@[simp] protected theorem IsIntent.univ : IsIntent r univ := IsExtent.univ

/--
theorem `IsIntent.inter` / 定理 `IsIntent.inter`

English:
theorem IsIntent.inter
  given: {t' : Set β}
  proof: IsExtent.inter

中文:
定理 IsIntent.inter
  条件: {t' : Set β}
  证明: IsExtent.inter
-/
protected theorem IsIntent.inter {t' : Set β} :
    IsIntent r t -> IsIntent r t' -> IsIntent r (t inter t') :=
  IsExtent.inter

/--
theorem `IsIntent.iInter` / 定理 `IsIntent.iInter`

English:
theorem IsIntent.iInter
  given: (f : ι -> Set β) (hf : forall i, IsIntent r (f i))
  proof: IsExtent.iInter _ hf

中文:
定理 IsIntent.iInter
  条件: (f : ι -> Set β) (hf : 对任意 i, Is整数ent r (f i))
  证明: IsExtent.iInter _ hf
-/
protected theorem IsIntent.iInter (f : ι -> Set β) (hf : forall i, IsIntent r (f i)) :
    IsIntent r (⋂ i, f i) :=
  IsExtent.iInter _ hf

/--
theorem `IsIntent.iInter₂` / 定理 `IsIntent.iInter₂`

English:
theorem IsIntent.iInter₂
  given: (f : forall i, κ i -> Set β) (hf : forall i j, IsIntent r (f i j))
  proof: IsExtent.iInter₂ _ hf

中文:
定理 IsIntent.iInter₂
  条件: (f : 对任意 i, κ i -> Set β) (hf : 对任意 i j, Is整数ent r (f i j))
  证明: IsExtent.iInter₂ _ hf
-/
protected theorem IsIntent.iInter₂ (f : forall i, κ i -> Set β) (hf : forall i j, IsIntent r (f i j)) :
    IsIntent r (⋂ (i) (j), f i j) :=
  IsExtent.iInter₂ _ hf

/--
theorem `IsIntent.upperPolar_lowerPolar_subset` / 定理 `IsIntent.upperPolar_lowerPolar_subset`

English:
theorem IsIntent.upperPolar_lowerPolar_subset
  given: {t' : Set β} (h : IsIntent r t) (ht' : t' subseteq t)
  proof: by
  rw [← h.eq]
  exact upperPolar_lowerPolar_monotone r ht'

中文:
定理 IsIntent.upperPolar_lowerPolar_subset
  条件: {t' : Set β} (h : Is整数ent r t) (ht' : t' subseteq t)
  证明: by
  rw [← h.eq]
  exact upperPolar_lowerPolar_monotone r ht'

Depends on / 依赖: h.eq, upperPolar_lowerPolar_monotone
-/
theorem IsIntent.upperPolar_lowerPolar_subset {t' : Set β} (h : IsIntent r t) (ht' : t' subseteq t) :
    upperPolar r (lowerPolar r t') subseteq t := by
  rw [← h.eq]
  exact upperPolar_lowerPolar_monotone r ht'

end Order

/-! ### Concepts -/

variable (α β)

/--
Definition of `Concept` / `Concept` 的定义

English:
structure Concept
  parameters: where
  axioms and operations (4):
    - extent : Set α
    - intent : Set β
    - upperPolar_extent : upperPolar r extent = intent
    - lowerPolar_intent : lowerPolar r intent = extent

中文:
结构 Concept
  参数: where
  公理与运算 (4 个):
    - extent : Set α
    - intent : Set β
    - upperPolar_extent : upperPolar r extent = intent
    - lowerPolar_intent : lowerPolar r intent = extent
-/
structure Concept where
  /-- The extent of a concept. -/
  extent : Set α
  /-- The intent of a concept. -/
  intent : Set β
  /-- The intent consists of all elements related to all elements of the extent. -/
  upperPolar_extent : upperPolar r extent = intent
  /-- The extent consists of all elements related to all elements of the intent. -/
  lowerPolar_intent : lowerPolar r intent = extent

initialize_simps_projections Concept (as_prefix extent, as_prefix intent)

namespace Concept

variable {r r' α β}
variable {c d : Concept α β r} {c' : Concept α α r'}

attribute [simp] upperPolar_extent lowerPolar_intent

/-- See `Concept.ext'` for a version using the intent. -/
@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (h : c.extent = d.extent)
  statement: c = d
  proof: by
  obtain ⟨s₁, t₁, rfl, _⟩ := c
  obtain ⟨s₂, t₂, rfl, _⟩ := d
  subst h
  rfl

中文:
定理 ext
  条件: (h : c.extent = d.extent)
  结论: c = d
  证明: by
  obtain ⟨s₁, t₁, rfl, _⟩ := c
  obtain ⟨s₂, t₂, rfl, _⟩ := d
  subst h
  rfl
-/
theorem ext (h : c.extent = d.extent) : c = d := by
  obtain ⟨s₁, t₁, rfl, _⟩ := c
  obtain ⟨s₂, t₂, rfl, _⟩ := d
  subst h
  rfl

/--
theorem `ext'` / 定理 `ext'`

English:
theorem ext'
  given: (h : c.intent = d.intent)
  statement: c = d
  proof: by
  obtain ⟨s₁, t₁, _, rfl⟩ := c
  obtain ⟨s₂, t₂, _, rfl⟩ := d
  subst h
  rfl

中文:
定理 ext'
  条件: (h : c.intent = d.intent)
  结论: c = d
  证明: by
  obtain ⟨s₁, t₁, _, rfl⟩ := c
  obtain ⟨s₂, t₂, _, rfl⟩ := d
  subst h
  rfl
-/
theorem ext' (h : c.intent = d.intent) : c = d := by
  obtain ⟨s₁, t₁, _, rfl⟩ := c
  obtain ⟨s₂, t₂, _, rfl⟩ := d
  subst h
  rfl

/--
theorem `extent_injective` / 定理 `extent_injective`

English:
theorem extent_injective
  statement: Injective (@extent α β r)
  proof: fun _ _ => ext

中文:
定理 extent_injective
  结论: Injective (@extent α β r)
  证明: fun _ _ => ext
-/
theorem extent_injective : Injective (@extent α β r) := fun _ _ => ext

/--
theorem `intent_injective` / 定理 `intent_injective`

English:
theorem intent_injective
  statement: Injective (@intent α β r)
  proof: fun _ _ => ext'

中文:
定理 intent_injective
  结论: Injective (@intent α β r)
  证明: fun _ _ => ext'
-/
theorem intent_injective : Injective (@intent α β r) := fun _ _ => ext'

/-- Copy a concept, adjusting definitional equalities. -/
@[simps]
/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (c : Concept α β r) (e : Set α) (i : Set β) (he : e = c.extent) (hi : i = c.intent)
  body: e
  intent := i
  upperPolar_extent := he ▸ hi ▸ c.upperPolar_extent
  lowerPolar_intent := he ▸ hi ▸ c.lowerPolar_intent

中文:
定义 copy
  签名: (c : Concept α β r) (e : Set α) (i : Set β) (he : e = c.extent) (hi : i = c.intent)
  定义体: e
  intent := i
  upperPolar_extent := he ▸ hi ▸ c.upperPolar_extent
  lowerPolar_intent := he ▸ hi ▸ c.lowerPolar_intent
-/
def copy (c : Concept α β r) (e : Set α) (i : Set β) (he : e = c.extent) (hi : i = c.intent) :
    Concept α β r where
  extent := e
  intent := i
  upperPolar_extent := he ▸ hi ▸ c.upperPolar_extent
  lowerPolar_intent := he ▸ hi ▸ c.lowerPolar_intent

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (c : Concept α β r) (e : Set α) (i : Set β) (he hi)
  statement: c.copy e i he hi = c
  proof: by
  ext; simp_all

中文:
定理 copy_eq
  条件: (c : Concept α β r) (e : Set α) (i : Set β) (he hi)
  结论: c.copy e i he hi = c
  证明: by
  ext; simp_all
-/
theorem copy_eq (c : Concept α β r) (e : Set α) (i : Set β) (he hi) : c.copy e i he hi = c := by
  ext; simp_all

variable (r s) in
/-- Define a concept from an extent, by setting the intent to its upper polar. -/
@[simps]
/--
Definition of `ofIsExtent` / `ofIsExtent` 的定义

English:
definition ofIsExtent
  signature: (hs : IsExtent r s)
  body: s
  intent := upperPolar r s
  upperPolar_extent := rfl
  lowerPolar_intent := hs.eq

@[simp]

中文:
定义 ofIsExtent
  签名: (hs : IsExtent r s)
  定义体: s
  intent := upperPolar r s
  upperPolar_extent := rfl
  lowerPolar_intent := hs.eq

@[simp]
-/
def ofIsExtent (hs : IsExtent r s) : Concept α β r where
  extent := s
  intent := upperPolar r s
  upperPolar_extent := rfl
  lowerPolar_intent := hs.eq

@[simp]
/--
theorem `isExtent_extent` / 定理 `isExtent_extent`

English:
theorem isExtent_extent
  given: (c : Concept α β r)
  statement: IsExtent r c.extent
  proof: lowerPolar_intent c ▸ isExtent_lowerPolar

中文:
定理 isExtent_extent
  条件: (c : Concept α β r)
  结论: IsExtent r c.extent
  证明: lowerPolar_intent c ▸ isExtent_lowerPolar

Depends on / 依赖: isExtent_lowerPolar, lowerPolar_intent
-/
theorem isExtent_extent (c : Concept α β r) : IsExtent r c.extent :=
  lowerPolar_intent c ▸ isExtent_lowerPolar

/--
theorem `isExtent_iff_exists_concept` / 定理 `isExtent_iff_exists_concept`

English:
theorem isExtent_iff_exists_concept
  statement: IsExtent r s ↔ exists c : Concept α β r, c.extent = s
  proof: ⟨fun h => ⟨ofIsExtent _ _ h, rfl⟩, fun ⟨c, h⟩ => h ▸ c.isExtent_extent⟩

中文:
定理 isExtent_iff_exists_concept
  结论: IsExtent r s ↔ 存在 c : Concept α β r, c.extent = s
  证明: ⟨fun h => ⟨ofIsExtent _ _ h, rfl⟩, fun ⟨c, h⟩ => h ▸ c.isExtent_extent⟩

Depends on / 依赖: c.isExtent_extent, isExtent_extent, ofIsExtent
-/
theorem isExtent_iff_exists_concept : IsExtent r s ↔ exists c : Concept α β r, c.extent = s :=
  ⟨fun h => ⟨ofIsExtent _ _ h, rfl⟩, fun ⟨c, h⟩ => h ▸ c.isExtent_extent⟩

variable (r t) in
/-- Define a concept from an intent, by setting the extent to its lower polar. -/
@[simps]
/--
Definition of `ofIsIntent` / `ofIsIntent` 的定义

English:
definition ofIsIntent
  signature: (ht : IsIntent r t)
  body: lowerPolar r t
  intent := t
  upperPolar_extent := ht.eq
  lowerPolar_intent := rfl

@[simp]

中文:
定义 ofIsIntent
  签名: (ht : Is整数ent r t)
  定义体: lowerPolar r t
  intent := t
  upperPolar_extent := ht.eq
  lowerPolar_intent := rfl

@[simp]

Depends on / 依赖: lowerPolar
-/
def ofIsIntent (ht : IsIntent r t) : Concept α β r where
  extent := lowerPolar r t
  intent := t
  upperPolar_extent := ht.eq
  lowerPolar_intent := rfl

@[simp]
/--
theorem `isIntent_intent` / 定理 `isIntent_intent`

English:
theorem isIntent_intent
  given: (c : Concept α β r)
  statement: IsIntent r c.intent
  proof: upperPolar_extent c ▸ isIntent_upperPolar

中文:
定理 isIntent_intent
  条件: (c : Concept α β r)
  结论: Is整数ent r c.intent
  证明: upperPolar_extent c ▸ isIntent_upperPolar

Depends on / 依赖: isIntent_upperPolar, upperPolar_extent
-/
theorem isIntent_intent (c : Concept α β r) : IsIntent r c.intent :=
  upperPolar_extent c ▸ isIntent_upperPolar

/--
theorem `isIntent_iff_exists_concept` / 定理 `isIntent_iff_exists_concept`

English:
theorem isIntent_iff_exists_concept
  statement: IsIntent r t ↔ exists c : Concept α β r, c.intent = t
  proof: ⟨fun h => ⟨ofIsIntent _ _ h, rfl⟩, fun ⟨c, h⟩ => h ▸ c.isIntent_intent⟩

中文:
定理 isIntent_iff_exists_concept
  结论: Is整数ent r t ↔ 存在 c : Concept α β r, c.intent = t
  证明: ⟨fun h => ⟨ofIsIntent _ _ h, rfl⟩, fun ⟨c, h⟩ => h ▸ c.isIntent_intent⟩

Depends on / 依赖: c.isIntent_intent, isIntent_intent, ofIsIntent
-/
theorem isIntent_iff_exists_concept : IsIntent r t ↔ exists c : Concept α β r, c.intent = t :=
  ⟨fun h => ⟨ofIsIntent _ _ h, rfl⟩, fun ⟨c, h⟩ => h ▸ c.isIntent_intent⟩

/-- The concept generated from the upper polar of a set, i.e. the smallest concept containing the
set of objects `s`. -/
@[simps!]
/--
Definition of `ofObjects` / `ofObjects` 的定义

English:
definition ofObjects
  signature: (r : α -> β -> Prop) (s : Set α)
  body: ofIsIntent r _ (isIntent_upperPolar (s := s))

中文:
定义 ofObjects
  签名: (r : α -> β -> 命题) (s : Set α)
  定义体: ofIsIntent r _ (isIntent_upperPolar (s := s))

Depends on / 依赖: isIntent_upperPolar, ofIsIntent
-/
def ofObjects (r : α -> β -> Prop) (s : Set α) : Concept α β r :=
  ofIsIntent r _ (isIntent_upperPolar (s := s))

/--
Definition of `ofObject` / `ofObject` 的定义

English:
abbreviation ofObject
  signature: (r : α -> β -> Prop) (a : α)
  body: ofObjects r {a}

@[simp]

中文:
缩写 ofObject
  签名: (r : α -> β -> 命题) (a : α)
  定义体: ofObjects r {a}

@[simp]

Depends on / 依赖: ofObjects
-/
abbrev ofObject (r : α -> β -> Prop) (a : α) : Concept α β r := ofObjects r {a}

@[simp]
/--
theorem `ofObjects_extent` / 定理 `ofObjects_extent`

English:
theorem ofObjects_extent
  statement: ofObjects r c.extent = c
  proof: intent_injective c.upperPolar_extent

中文:
定理 ofObjects_extent
  结论: ofObjects r c.extent = c
  证明: intent_injective c.upperPolar_extent

Depends on / 依赖: c.upperPolar_extent, intent_injective, upperPolar_extent
-/
theorem ofObjects_extent : ofObjects r c.extent = c :=
  intent_injective c.upperPolar_extent

/--
theorem `extent_ofObjects_of_isExtent` / 定理 `extent_ofObjects_of_isExtent`

English:
theorem extent_ofObjects_of_isExtent
  given: (hs : IsExtent r s)
  statement: (ofObjects r s).extent = s
  proof: hs.eq

中文:
定理 extent_ofObjects_of_isExtent
  条件: (hs : IsExtent r s)
  结论: (ofObjects r s).extent = s
  证明: hs.eq

Depends on / 依赖: hs.eq
-/
theorem extent_ofObjects_of_isExtent (hs : IsExtent r s) : (ofObjects r s).extent = s :=
  hs.eq

/--
theorem `leftInverse_ofObjects_extent` / 定理 `leftInverse_ofObjects_extent`

English:
theorem leftInverse_ofObjects_extent
  statement: LeftInverse (ofObjects r) extent
  proof: fun _ => ofObjects_extent

中文:
定理 leftInverse_ofObjects_extent
  结论: LeftInverse (ofObjects r) extent
  证明: fun _ => ofObjects_extent

Depends on / 依赖: ofObjects_extent
-/
theorem leftInverse_ofObjects_extent : LeftInverse (ofObjects r) extent :=
  fun _ => ofObjects_extent

/--
theorem `leftInvOn_extent_ofObjects` / 定理 `leftInvOn_extent_ofObjects`

English:
theorem leftInvOn_extent_ofObjects
  statement: Set.LeftInvOn extent (ofObjects r) {s | IsExtent r s}
  proof: fun _ => IsExtent.eq

中文:
定理 leftInvOn_extent_ofObjects
  结论: Set.LeftInvOn extent (ofObjects r) {s | IsExtent r s}
  证明: fun _ => IsExtent.eq

Depends on / 依赖: IsExtent, IsExtent.eq
-/
theorem leftInvOn_extent_ofObjects : Set.LeftInvOn extent (ofObjects r) {s | IsExtent r s} :=
  fun _ => IsExtent.eq

/--
theorem `surjective_ofObjects` / 定理 `surjective_ofObjects`

English:
theorem surjective_ofObjects
  statement: Surjective (ofObjects r)
  proof: leftInverse_ofObjects_extent.surjective

中文:
定理 surjective_ofObjects
  结论: Surjective (ofObjects r)
  证明: leftInverse_ofObjects_extent.surjective

Depends on / 依赖: leftInverse_ofObjects_extent, leftInverse_ofObjects_extent.surjective, surjective
-/
theorem surjective_ofObjects : Surjective (ofObjects r) :=
  leftInverse_ofObjects_extent.surjective

/-- The concept generated from the lower polar of a set, i.e. the smallest concept whose set of
attributes is contained in `t`. -/
@[simps!]
/--
Definition of `ofAttributes` / `ofAttributes` 的定义

English:
definition ofAttributes
  signature: (r : α -> β -> Prop) (t : Set β)
  body: ofIsExtent r _ (isExtent_lowerPolar (t := t))

中文:
定义 ofAttributes
  签名: (r : α -> β -> 命题) (t : Set β)
  定义体: ofIsExtent r _ (isExtent_lowerPolar (t := t))

Depends on / 依赖: isExtent_lowerPolar, ofIsExtent
-/
def ofAttributes (r : α -> β -> Prop) (t : Set β) : Concept α β r :=
  ofIsExtent r _ (isExtent_lowerPolar (t := t))

/--
Definition of `ofAttribute` / `ofAttribute` 的定义

English:
abbreviation ofAttribute
  signature: (r : α -> β -> Prop) (b : β)
  body: ofAttributes r {b}

@[simp]

中文:
缩写 ofAttribute
  签名: (r : α -> β -> 命题) (b : β)
  定义体: ofAttributes r {b}

@[simp]

Depends on / 依赖: ofAttributes
-/
abbrev ofAttribute (r : α -> β -> Prop) (b : β) : Concept α β r := ofAttributes r {b}

@[simp]
/--
theorem `ofAttributes_intent` / 定理 `ofAttributes_intent`

English:
theorem ofAttributes_intent
  statement: ofAttributes r c.intent = c
  proof: extent_injective c.lowerPolar_intent

中文:
定理 ofAttributes_intent
  结论: ofAttributes r c.intent = c
  证明: extent_injective c.lowerPolar_intent

Depends on / 依赖: c.lowerPolar_intent, extent_injective, lowerPolar_intent
-/
theorem ofAttributes_intent : ofAttributes r c.intent = c :=
  extent_injective c.lowerPolar_intent

/--
theorem `intent_ofAttributes_of_isIntent` / 定理 `intent_ofAttributes_of_isIntent`

English:
theorem intent_ofAttributes_of_isIntent
  given: (hs : IsIntent r t)
  statement: (ofAttributes r t).intent = t
  proof: hs.eq

中文:
定理 intent_ofAttributes_of_isIntent
  条件: (hs : Is整数ent r t)
  结论: (ofAttributes r t).intent = t
  证明: hs.eq

Depends on / 依赖: hs.eq
-/
theorem intent_ofAttributes_of_isIntent (hs : IsIntent r t) : (ofAttributes r t).intent = t :=
  hs.eq

/--
theorem `leftInverse_ofAttributes_extent` / 定理 `leftInverse_ofAttributes_extent`

English:
theorem leftInverse_ofAttributes_extent
  statement: LeftInverse (ofAttributes r) intent
  proof: fun c => extent_injective c.lowerPolar_intent

中文:
定理 leftInverse_ofAttributes_extent
  结论: LeftInverse (ofAttributes r) intent
  证明: fun c => extent_injective c.lowerPolar_intent

Depends on / 依赖: c.lowerPolar_intent, extent_injective, lowerPolar_intent
-/
theorem leftInverse_ofAttributes_extent : LeftInverse (ofAttributes r) intent :=
  fun c => extent_injective c.lowerPolar_intent

/--
theorem `leftInvOn_ofObjects_intent` / 定理 `leftInvOn_ofObjects_intent`

English:
theorem leftInvOn_ofObjects_intent
  statement: Set.LeftInvOn intent (ofAttributes r) {s | IsIntent r s}
  proof: fun _ => IsIntent.eq

中文:
定理 leftInvOn_ofObjects_intent
  结论: Set.LeftInvOn intent (ofAttributes r) {s | Is整数ent r s}
  证明: fun _ => IsIntent.eq

Depends on / 依赖: IsIntent, IsIntent.eq
-/
theorem leftInvOn_ofObjects_intent : Set.LeftInvOn intent (ofAttributes r) {s | IsIntent r s} :=
  fun _ => IsIntent.eq

/--
theorem `surjective_ofAttributes` / 定理 `surjective_ofAttributes`

English:
theorem surjective_ofAttributes
  statement: Surjective (ofAttributes r)
  proof: leftInverse_ofAttributes_extent.surjective

中文:
定理 surjective_ofAttributes
  结论: Surjective (ofAttributes r)
  证明: leftInverse_ofAttributes_extent.surjective

Depends on / 依赖: leftInverse_ofAttributes_extent, leftInverse_ofAttributes_extent.surjective, surjective
-/
theorem surjective_ofAttributes : Surjective (ofAttributes r) :=
  leftInverse_ofAttributes_extent.surjective

/--
theorem `rel_extent_intent` / 定理 `rel_extent_intent`

English:
theorem rel_extent_intent
  given: {x y} (hx : x in c.extent) (hy : y in c.intent)
  statement: r x y
  proof: by
  rw [← c.upperPolar_extent] at hy
  exact hy hx

中文:
定理 rel_extent_intent
  条件: {x y} (hx : x in c.extent) (hy : y in c.intent)
  结论: r x y
  证明: by
  rw [← c.upperPolar_extent] at hy
  exact hy hx

Depends on / 依赖: c.upperPolar_extent, upperPolar_extent
-/
theorem rel_extent_intent {x y} (hx : x in c.extent) (hy : y in c.intent) : r x y := by
  rw [← c.upperPolar_extent] at hy
  exact hy hx

/--
theorem `disjoint_extent_intent` / 定理 `disjoint_extent_intent`

English:
theorem disjoint_extent_intent
  given: [Std.Irrefl r']
  statement: Disjoint c'.extent c'.intent
  proof: by
  rw [disjoint_iff_forall_ne]
  rintro x hx _ hx' rfl
  exact irrefl x (rel_extent_intent hx hx')

中文:
定理 disjoint_extent_intent
  条件: [Std.Irrefl r']
  结论: Disjoint c'.extent c'.intent
  证明: by
  rw [disjoint_iff_forall_ne]
  rintro x hx _ hx' rfl
  exact irrefl x (rel_extent_intent hx hx')

Depends on / 依赖: disjoint_iff_forall_ne, irrefl, rel_extent_intent
-/
theorem disjoint_extent_intent [Std.Irrefl r'] : Disjoint c'.extent c'.intent := by
  rw [disjoint_iff_forall_ne]
  rintro x hx _ hx' rfl
  exact irrefl x (rel_extent_intent hx hx')

/--
theorem `mem_extent_of_rel_extent` / 定理 `mem_extent_of_rel_extent`

English:
theorem mem_extent_of_rel_extent
  given: [IsTrans α r'] {x y} (hy : r' y x) (hx : x in c'.extent)
  proof: by
  rw [← lowerPolar_intent]
  exact fun z hz => _root_.trans hy (rel_extent_intent hx hz)

中文:
定理 mem_extent_of_rel_extent
  条件: [IsTrans α r'] {x y} (hy : r' y x) (hx : x in c'.extent)
  证明: by
  rw [← lowerPolar_intent]
  exact fun z hz => _root_.trans hy (rel_extent_intent hx hz)

Depends on / 依赖: _root_, _root_.trans, lowerPolar_intent, rel_extent_intent
-/
theorem mem_extent_of_rel_extent [IsTrans α r'] {x y} (hy : r' y x) (hx : x in c'.extent) :
    y in c'.extent := by
  rw [← lowerPolar_intent]
  exact fun z hz => _root_.trans hy (rel_extent_intent hx hz)

/--
theorem `mem_intent_of_intent_rel` / 定理 `mem_intent_of_intent_rel`

English:
theorem mem_intent_of_intent_rel
  given: [IsTrans α r'] {x y} (hy : r' x y) (hx : x in c'.intent)
  proof: by
  rw [← upperPolar_extent]
  exact fun z hz => _root_.trans (rel_extent_intent hz hx) hy

中文:
定理 mem_intent_of_intent_rel
  条件: [IsTrans α r'] {x y} (hy : r' x y) (hx : x in c'.intent)
  证明: by
  rw [← upperPolar_extent]
  exact fun z hz => _root_.trans (rel_extent_intent hz hx) hy

Depends on / 依赖: _root_, _root_.trans, rel_extent_intent, upperPolar_extent
-/
theorem mem_intent_of_intent_rel [IsTrans α r'] {x y} (hy : r' x y) (hx : x in c'.intent) :
    y in c'.intent := by
  rw [← upperPolar_extent]
  exact fun z hz => _root_.trans (rel_extent_intent hz hx) hy

/--
theorem `codisjoint_extent_intent` / 定理 `codisjoint_extent_intent`

English:
theorem codisjoint_extent_intent
  given: [Std.Trichotomous r'] [IsTrans α r']
  proof: by
  rw [codisjoint_iff_le_sup]
  refine fun x _ => or_iff_not_imp_left.2 fun hx => ?_
  rw [← upperPolar_extent]
  intro y hy
apply Not.imp_symm Std.Trichotomous.trichotomous x y (hx <| mem_extent_of_rel_extent · hy)
  exact (hx <| · ▸ hy)

中文:
定理 codisjoint_extent_intent
  条件: [Std.Trichotomous r'] [IsTrans α r']
  证明: by
  rw [codisjoint_iff_le_sup]
  refine fun x _ => or_iff_not_imp_left.2 fun hx => ?_
  rw [← upperPolar_extent]
  intro y hy
apply Not.imp_symm Std.Trichotomous.trichotomous x y (hx <| mem_extent_of_rel_extent · hy)
  exact (hx <| · ▸ hy)

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom, Not.imp_symm, Std.Trichotomous.trichotomous, Trichotomous, codisjoint_iff_le_sup, imp_symm, mem_extent_of_rel_extent, or_iff_not_imp_left, trichotomous, upperPolar_extent
-/
theorem codisjoint_extent_intent [Std.Trichotomous r'] [IsTrans α r'] :
    Codisjoint c'.extent c'.intent := by
  rw [codisjoint_iff_le_sup]
  refine fun x _ => or_iff_not_imp_left.2 fun hx => ?_
  rw [← upperPolar_extent]
  intro y hy
apply Not.imp_symm Std.Trichotomous.trichotomous x y (hx <| mem_extent_of_rel_extent · hy)
  exact (hx <| · ▸ hy)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (Concept α β r)
  body: .lift _ extent_injective

中文:
实例 :
  签名: PartialOrder (Concept α β r)
  定义体: .lift _ extent_injective

Depends on / 依赖: extent_injective
-/
instance : PartialOrder (Concept α β r) := .lift _ extent_injective

/--
theorem `isCompl_extent_intent` / 定理 `isCompl_extent_intent`

English:
theorem isCompl_extent_intent
  given: [IsStrictTotalOrder α r'] (c' : Concept α α r')
  proof: ⟨c'.disjoint_extent_intent, c'.codisjoint_extent_intent⟩

@[simp]

中文:
定理 isCompl_extent_intent
  条件: [IsStrictTotalOrder α r'] (c' : Concept α α r')
  证明: ⟨c'.disjoint_extent_intent, c'.codisjoint_extent_intent⟩

@[simp]

Depends on / 依赖: codisjoint_extent_intent, disjoint_extent_intent, f.hom
-/
theorem isCompl_extent_intent [IsStrictTotalOrder α r'] (c' : Concept α α r') :
    IsCompl c'.extent c'.intent :=
  ⟨c'.disjoint_extent_intent, c'.codisjoint_extent_intent⟩

@[simp]
/--
theorem `compl_extent` / 定理 `compl_extent`

English:
theorem compl_extent
  given: [IsStrictTotalOrder α r'] (c' : Concept α α r')
  statement: c'.extentᶜ = c'.intent
  proof: c'.isCompl_extent_intent.compl_eq

@[simp]

中文:
定理 compl_extent
  条件: [IsStrictTotalOrder α r'] (c' : Concept α α r')
  结论: c'.extentᶜ = c'.intent
  证明: c'.isCompl_extent_intent.compl_eq

@[simp]

Depends on / 依赖: compl_eq, isCompl_extent_intent, isCompl_extent_intent.compl_eq
-/
theorem compl_extent [IsStrictTotalOrder α r'] (c' : Concept α α r') : c'.extentᶜ = c'.intent :=
  c'.isCompl_extent_intent.compl_eq

@[simp]
/--
theorem `compl_intent` / 定理 `compl_intent`

English:
theorem compl_intent
  given: [IsStrictTotalOrder α r'] (c' : Concept α α r')
  statement: c'.intentᶜ = c'.extent
  proof: c'.isCompl_extent_intent.symm.compl_eq

@[simp]

中文:
定理 compl_intent
  条件: [IsStrictTotalOrder α r'] (c' : Concept α α r')
  结论: c'.intentᶜ = c'.extent
  证明: c'.isCompl_extent_intent.symm.compl_eq

@[simp]

Depends on / 依赖: compl_eq, isCompl_extent_intent, isCompl_extent_intent.symm.compl_eq
-/
theorem compl_intent [IsStrictTotalOrder α r'] (c' : Concept α α r') : c'.intentᶜ = c'.extent :=
  c'.isCompl_extent_intent.symm.compl_eq

@[simp]
/--
theorem `extent_subset_extent_iff` / 定理 `extent_subset_extent_iff`

English:
theorem extent_subset_extent_iff
  statement: c.extent subseteq d.extent ↔ c <= d
  proof: Iff.rfl

@[simp]

中文:
定理 extent_subset_extent_iff
  结论: c.extent subseteq d.extent ↔ c <= d
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem extent_subset_extent_iff : c.extent subseteq d.extent ↔ c <= d :=
  Iff.rfl

@[simp]
/--
theorem `extent_ssubset_extent_iff` / 定理 `extent_ssubset_extent_iff`

English:
theorem extent_ssubset_extent_iff
  statement: c.extent ⊂ d.extent ↔ c < d
  proof: Iff.rfl

@[simp]

中文:
定理 extent_ssubset_extent_iff
  结论: c.extent ⊂ d.extent ↔ c < d
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem extent_ssubset_extent_iff : c.extent ⊂ d.extent ↔ c < d :=
  Iff.rfl

@[simp]
/--
theorem `intent_subset_intent_iff` / 定理 `intent_subset_intent_iff`

English:
theorem intent_subset_intent_iff
  statement: c.intent subseteq d.intent ↔ d <= c
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← extent_subset_extent_iff, ← c.lowerPolar_intent, ← d.lowerPolar_intent]
    exact lowerPolar_anti _ h
  · rw [← c.upperPolar_extent, ← d.upperPolar_extent]
    exact upperPolar_anti _ h

@[simp]

中文:
定理 intent_subset_intent_iff
  结论: c.intent subseteq d.intent ↔ d <= c
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← extent_subset_extent_iff, ← c.lowerPolar_intent, ← d.lowerPolar_intent]
    exact lowerPolar_anti _ h
  · rw [← c.upperPolar_extent, ← d.upperPolar_extent]
    exact upperPolar_anti _ h

@[simp]

Depends on / 依赖: c.lowerPolar_intent, c.upperPolar_extent, d.lowerPolar_intent, d.upperPolar_extent, extent_subset_extent_iff, lowerPolar_anti, lowerPolar_intent, upperPolar_anti, upperPolar_extent
-/
theorem intent_subset_intent_iff : c.intent subseteq d.intent ↔ d <= c := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← extent_subset_extent_iff, ← c.lowerPolar_intent, ← d.lowerPolar_intent]
    exact lowerPolar_anti _ h
  · rw [← c.upperPolar_extent, ← d.upperPolar_extent]
    exact upperPolar_anti _ h

@[simp]
/--
theorem `intent_ssubset_intent_iff` / 定理 `intent_ssubset_intent_iff`

English:
theorem intent_ssubset_intent_iff
  statement: c.intent ⊂ d.intent ↔ d < c
  proof: by
  rw [ssubset_iff_subset_not_subset]; rw [lt_iff_le_not_ge]; rw [intent_subset_intent_iff]; rw [intent_subset_intent_iff]

中文:
定理 intent_ssubset_intent_iff
  结论: c.intent ⊂ d.intent ↔ d < c
  证明: by
  rw [ssubset_iff_subset_not_subset]; rw [lt_iff_le_not_ge]; rw [intent_subset_intent_iff]; rw [intent_subset_intent_iff]

Depends on / 依赖: intent_subset_intent_iff, lt_iff_le_not_ge, ssubset_iff_subset_not_subset
-/
theorem intent_ssubset_intent_iff : c.intent ⊂ d.intent ↔ d < c := by
  rw [ssubset_iff_subset_not_subset]; rw [lt_iff_le_not_ge]; rw [intent_subset_intent_iff]; rw [intent_subset_intent_iff]

/--
theorem `strictMono_extent` / 定理 `strictMono_extent`

English:
theorem strictMono_extent
  statement: StrictMono (@extent α β r)
  proof: fun _ _ =>
  extent_ssubset_extent_iff.2

中文:
定理 strictMono_extent
  结论: StrictMono (@extent α β r)
  证明: fun _ _ =>
  extent_ssubset_extent_iff.2
-/
theorem strictMono_extent : StrictMono (@extent α β r) := fun _ _ =>
  extent_ssubset_extent_iff.2

/--
theorem `strictAnti_intent` / 定理 `strictAnti_intent`

English:
theorem strictAnti_intent
  statement: StrictAnti (@intent α β r)
  proof: fun _ _ =>
  intent_ssubset_intent_iff.2

@[simp]

中文:
定理 strictAnti_intent
  结论: StrictAnti (@intent α β r)
  证明: fun _ _ =>
  intent_ssubset_intent_iff.2

@[simp]
-/
theorem strictAnti_intent : StrictAnti (@intent α β r) := fun _ _ =>
  intent_ssubset_intent_iff.2

@[simp]
/--
theorem `isLowerSet_extent_le` / 定理 `isLowerSet_extent_le`

English:
theorem isLowerSet_extent_le
  given: {α : Type*} [Preorder α] (c : Concept α α (· <= ·))
  proof: @mem_extent_of_rel_extent _ _ _ _

@[simp]

中文:
定理 isLowerSet_extent_le
  条件: {α : 类型} [Preorder α] (c : Concept α α (· <= ·))
  证明: @mem_extent_of_rel_extent _ _ _ _

@[simp]

Depends on / 依赖: mem_extent_of_rel_extent
-/
theorem isLowerSet_extent_le {α : Type*} [Preorder α] (c : Concept α α (· <= ·)) :
    IsLowerSet c.extent :=
  @mem_extent_of_rel_extent _ _ _ _

@[simp]
/--
theorem `isUpperSet_intent_le` / 定理 `isUpperSet_intent_le`

English:
theorem isUpperSet_intent_le
  given: {α : Type*} [Preorder α] (c : Concept α α (· <= ·))
  proof: @mem_intent_of_intent_rel _ _ _ _

@[simp]

中文:
定理 isUpperSet_intent_le
  条件: {α : 类型} [Preorder α] (c : Concept α α (· <= ·))
  证明: @mem_intent_of_intent_rel _ _ _ _

@[simp]

Depends on / 依赖: mem_intent_of_intent_rel
-/
theorem isUpperSet_intent_le {α : Type*} [Preorder α] (c : Concept α α (· <= ·)) :
    IsUpperSet c.intent :=
  @mem_intent_of_intent_rel _ _ _ _

@[simp]
/--
theorem `isLowerSet_extent_lt` / 定理 `isLowerSet_extent_lt`

English:
theorem isLowerSet_extent_lt
  given: {α : Type*} [PartialOrder α] (c : Concept α α (· < ·))
  proof: by
  intro a b hb ha
  obtain rfl | hb := hb.eq_or_lt
  · assumption
  · exact mem_extent_of_rel_extent hb ha

@[simp]

中文:
定理 isLowerSet_extent_lt
  条件: {α : 类型} [PartialOrder α] (c : Concept α α (· < ·))
  证明: by
  intro a b hb ha
  obtain rfl | hb := hb.eq_or_lt
  · assumption
  · exact mem_extent_of_rel_extent hb ha

@[simp]

Depends on / 依赖: eq_or_lt, hb.eq_or_lt, mem_extent_of_rel_extent
-/
theorem isLowerSet_extent_lt {α : Type*} [PartialOrder α] (c : Concept α α (· < ·)) :
    IsLowerSet c.extent := by
  intro a b hb ha
  obtain rfl | hb := hb.eq_or_lt
  · assumption
  · exact mem_extent_of_rel_extent hb ha

@[simp]
/--
theorem `isUpperSet_intent_lt` / 定理 `isUpperSet_intent_lt`

English:
theorem isUpperSet_intent_lt
  given: {α : Type*} [PartialOrder α] (c : Concept α α (· < ·))
  proof: by
  intro a b hb ha
  obtain rfl | hb := hb.eq_or_lt
  · assumption
  · exact mem_intent_of_intent_rel hb ha

@[simps!]

中文:
定理 isUpperSet_intent_lt
  条件: {α : 类型} [PartialOrder α] (c : Concept α α (· < ·))
  证明: by
  intro a b hb ha
  obtain rfl | hb := hb.eq_or_lt
  · assumption
  · exact mem_intent_of_intent_rel hb ha

@[simps!]

Depends on / 依赖: eq_or_lt, hb.eq_or_lt, mem_intent_of_intent_rel
-/
theorem isUpperSet_intent_lt {α : Type*} [PartialOrder α] (c : Concept α α (· < ·)) :
    IsUpperSet c.intent := by
  intro a b hb ha
  obtain rfl | hb := hb.eq_or_lt
  · assumption
  · exact mem_intent_of_intent_rel hb ha

@[simps!]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Max (Concept α β r)
  body: ofIsIntent _ _ (c.isIntent_intent.inter d.isIntent_intent)

alias extent_sup := extent_max
alias intent_sup := intent_max

@[simps!]

中文:
实例 :
  签名: Max (Concept α β r)
  定义体: ofIsIntent _ _ (c.isIntent_intent.inter d.isIntent_intent)

alias extent_sup := extent_max
alias intent_sup := intent_max

@[simps!]

Depends on / 依赖: c.isIntent_intent.inter, d.isIntent_intent, isIntent_intent, ofIsIntent
-/
instance : Max (Concept α β r) where
  max c d := ofIsIntent _ _ (c.isIntent_intent.inter d.isIntent_intent)

alias extent_sup := extent_max
alias intent_sup := intent_max

@[simps!]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min (Concept α β r)
  body: ofIsExtent _ _ (c.isExtent_extent.inter d.isExtent_extent)

alias extent_inf := extent_min
alias intent_inf := intent_min

中文:
实例 :
  签名: Min (Concept α β r)
  定义体: ofIsExtent _ _ (c.isExtent_extent.inter d.isExtent_extent)

alias extent_inf := extent_min
alias intent_inf := intent_min

Depends on / 依赖: c.isExtent_extent.inter, d.isExtent_extent, isExtent_extent, ofIsExtent
-/
instance : Min (Concept α β r) where
  min c d := ofIsExtent _ _ (c.isExtent_extent.inter d.isExtent_extent)

alias extent_inf := extent_min
alias intent_inf := intent_min

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SemilatticeInf (Concept α β r)
  body: extent_injective.semilatticeInf _ .rfl .rfl fun _ _ => rfl

中文:
实例 :
  签名: SemilatticeInf (Concept α β r)
  定义体: extent_injective.semilatticeInf _ .rfl .rfl fun _ _ => rfl

Depends on / 依赖: extent_injective, extent_injective.semilatticeInf, semilatticeInf
-/
instance : SemilatticeInf (Concept α β r) :=
  extent_injective.semilatticeInf _ .rfl .rfl fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SemilatticeSup (Concept α β r)
  body: (toDual.injective.comp intent_injective).semilatticeSup _ (by simp) (by simp) fun _ _ => rfl

中文:
实例 :
  签名: SemilatticeSup (Concept α β r)
  定义体: (toDual.injective.comp intent_injective).semilatticeSup _ (by simp) (by simp) fun _ _ => rfl

Depends on / 依赖: injective, intent_injective, semilatticeSup, toDual, toDual.injective.comp
-/
instance : SemilatticeSup (Concept α β r) :=
  (toDual.injective.comp intent_injective).semilatticeSup _ (by simp) (by simp) fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Lattice (Concept α β r)

中文:
实例 :
  签名: Lattice (Concept α β r)
-/
instance : Lattice (Concept α β r) where

@[simp]
/--
theorem `ofObjects_le_iff` / 定理 `ofObjects_le_iff`

English:
theorem ofObjects_le_iff
  statement: ofObjects r s <= c ↔ s subseteq c.extent
  proof: by
  rw [← extent_subset_extent_iff]
  exact ⟨((subset_lowerPolar_upperPolar r s).trans ·),
    (isExtent_extent c).lowerPolar_upperPolar_subset⟩

中文:
定理 ofObjects_le_iff
  结论: ofObjects r s <= c ↔ s subseteq c.extent
  证明: by
  rw [← extent_subset_extent_iff]
  exact ⟨((subset_lowerPolar_upperPolar r s).trans ·),
    (isExtent_extent c).lowerPolar_upperPolar_subset⟩

Depends on / 依赖: extent_subset_extent_iff, isExtent_extent, lowerPolar_upperPolar_subset, subset_lowerPolar_upperPolar
-/
theorem ofObjects_le_iff : ofObjects r s <= c ↔ s subseteq c.extent := by
  rw [← extent_subset_extent_iff]
  exact ⟨((subset_lowerPolar_upperPolar r s).trans ·),
    (isExtent_extent c).lowerPolar_upperPolar_subset⟩

/--
theorem `le_ofObjects_of_extent_subset` / 定理 `le_ofObjects_of_extent_subset`

English:
theorem le_ofObjects_of_extent_subset
  given: (h : c.extent subseteq s)
  statement: c <= ofObjects r s
  proof: by
  simpa using! (lowerPolar_anti r).comp (upperPolar_anti r) h

@[simp]

中文:
定理 le_ofObjects_of_extent_subset
  条件: (h : c.extent subseteq s)
  结论: c <= ofObjects r s
  证明: by
  simpa using! (lowerPolar_anti r).comp (upperPolar_anti r) h

@[simp]

Depends on / 依赖: lowerPolar_anti, upperPolar_anti
-/
theorem le_ofObjects_of_extent_subset (h : c.extent subseteq s) : c <= ofObjects r s := by
  simpa using! (lowerPolar_anti r).comp (upperPolar_anti r) h

@[simp]
/--
theorem `le_ofAttributes_iff` / 定理 `le_ofAttributes_iff`

English:
theorem le_ofAttributes_iff
  statement: c <= ofAttributes r t ↔ t subseteq c.intent
  proof: by
  rw [← intent_subset_intent_iff]
  exact ⟨((subset_upperPolar_lowerPolar r t).trans ·),
    (isIntent_intent c).upperPolar_lowerPolar_subset⟩

中文:
定理 le_ofAttributes_iff
  结论: c <= ofAttributes r t ↔ t subseteq c.intent
  证明: by
  rw [← intent_subset_intent_iff]
  exact ⟨((subset_upperPolar_lowerPolar r t).trans ·),
    (isIntent_intent c).upperPolar_lowerPolar_subset⟩

Depends on / 依赖: intent_subset_intent_iff, isIntent_intent, subset_upperPolar_lowerPolar, upperPolar_lowerPolar_subset
-/
theorem le_ofAttributes_iff : c <= ofAttributes r t ↔ t subseteq c.intent := by
  rw [← intent_subset_intent_iff]
  exact ⟨((subset_upperPolar_lowerPolar r t).trans ·),
    (isIntent_intent c).upperPolar_lowerPolar_subset⟩

/--
theorem `ofAttributes_le_of_intent_subset` / 定理 `ofAttributes_le_of_intent_subset`

English:
theorem ofAttributes_le_of_intent_subset
  given: (h : c.intent subseteq t)
  statement: ofAttributes r t <= c
  proof: by
  rw [← intent_subset_intent_iff]
  simpa using (upperPolar_anti r).comp (lowerPolar_anti r) h

中文:
定理 ofAttributes_le_of_intent_subset
  条件: (h : c.intent subseteq t)
  结论: ofAttributes r t <= c
  证明: by
  rw [← intent_subset_intent_iff]
  simpa using (upperPolar_anti r).comp (lowerPolar_anti r) h

Depends on / 依赖: intent_subset_intent_iff, lowerPolar_anti, upperPolar_anti
-/
theorem ofAttributes_le_of_intent_subset (h : c.intent subseteq t) : ofAttributes r t <= c := by
  rw [← intent_subset_intent_iff]
  simpa using (upperPolar_anti r).comp (lowerPolar_anti r) h

/--
theorem `ofObject_le_ofAttribute_iff` / 定理 `ofObject_le_ofAttribute_iff`

English:
theorem ofObject_le_ofAttribute_iff
  given: {a b}
  statement: ofObject r a <= ofAttribute r b ↔ r a b
  proof: by
  simp

@[simps!]

中文:
定理 ofObject_le_ofAttribute_iff
  条件: {a b}
  结论: ofObject r a <= ofAttribute r b ↔ r a b
  证明: by
  simp

@[simps!]
-/
theorem ofObject_le_ofAttribute_iff {a b} : ofObject r a <= ofAttribute r b ↔ r a b := by
  simp

@[simps!]
/--
Instance `instBoundedOrderConcept` / 实例 `instBoundedOrderConcept`

English:
instance instBoundedOrderConcept
  signature: : BoundedOrder (Concept α β r) where
  body: ofIsExtent _ _ .univ
  le_top _ := subset_univ _
  bot := ofIsIntent _ _ .univ
bot_le _ := intent_subset_intent_iff.1 subset_univ _

@[simps!]

中文:
实例 instBoundedOrderConcept
  签名: : BoundedOrder (Concept α β r) where
  定义体: ofIsExtent _ _ .univ
  le_top _ := subset_univ _
  bot := ofIsIntent _ _ .univ
bot_le _ := intent_subset_intent_iff.1 subset_univ _

@[simps!]

Depends on / 依赖: ofIsExtent
-/
instance instBoundedOrderConcept : BoundedOrder (Concept α β r) where
  top := ofIsExtent _ _ .univ
  le_top _ := subset_univ _
  bot := ofIsIntent _ _ .univ
bot_le _ := intent_subset_intent_iff.1 subset_univ _

@[simps!]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InfSet (Concept α β r)
  body: ofIsExtent _ _ (.iInter₂ _ fun c (_ : c in S) => c.isExtent_extent)

@[simps!]

中文:
实例 :
  签名: InfSet (Concept α β r)
  定义体: ofIsExtent _ _ (.iInter₂ _ fun c (_ : c in S) => c.isExtent_extent)

@[simps!]

Depends on / 依赖: c.isExtent_extent, isExtent_extent, ofIsExtent
-/
instance : InfSet (Concept α β r) where
  sInf S := ofIsExtent _ _ (.iInter₂ _ fun c (_ : c in S) => c.isExtent_extent)

@[simps!]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SupSet (Concept α β r)
  body: ofIsIntent _ _ (.iInter₂ _ fun c (_ : c in S) => c.isIntent_intent)

中文:
实例 :
  签名: SupSet (Concept α β r)
  定义体: ofIsIntent _ _ (.iInter₂ _ fun c (_ : c in S) => c.isIntent_intent)

Depends on / 依赖: c.isIntent_intent, isIntent_intent, ofIsIntent
-/
instance : SupSet (Concept α β r) where
  sSup S := ofIsIntent _ _ (.iInter₂ _ fun c (_ : c in S) => c.isIntent_intent)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLattice (Concept α β r)
  body: by
    refine ⟨fun _ hc => ?_, fun _ hc => ?_⟩
· exact intent_subset_intent_iff.1 biInter_subset_of_mem hc
· exact intent_subset_intent_iff.1
        subset_iInter₂ fun a ha => intent_subset_intent_iff.2 (hc ha)
  isGLB_sInf s := ⟨fun _ => biInter_subset_of_mem, fun _ => subset_iInter₂⟩

@[simp]

中文:
实例 :
  签名: CompleteLattice (Concept α β r)
  定义体: by
    refine ⟨fun _ hc => ?_, fun _ hc => ?_⟩
· exact intent_subset_intent_iff.1 biInter_subset_of_mem hc
· exact intent_subset_intent_iff.1
        subset_iInter₂ fun a ha => intent_subset_intent_iff.2 (hc ha)
  isGLB_sInf s := ⟨fun _ => biInter_subset_of_mem, fun _ => subset_iInter₂⟩

@[simp]

Depends on / 依赖: biInter_subset_of_mem, intent_subset_intent_iff, isGLB_sInf
-/
instance : CompleteLattice (Concept α β r) where
  isLUB_sSup s := by
    refine ⟨fun _ hc => ?_, fun _ hc => ?_⟩
· exact intent_subset_intent_iff.1 biInter_subset_of_mem hc
· exact intent_subset_intent_iff.1
        subset_iInter₂ fun a ha => intent_subset_intent_iff.2 (hc ha)
  isGLB_sInf s := ⟨fun _ => biInter_subset_of_mem, fun _ => subset_iInter₂⟩

@[simp]
/--
theorem `extent_iSup` / 定理 `extent_iSup`

English:
theorem extent_iSup
  given: (f : ι -> Concept α β r)
  proof: by
  simp_rw [iSup, extent_sSup, ← Set.iInf_eq_iInter, iInf_range]

@[simp]

中文:
定理 extent_iSup
  条件: (f : ι -> Concept α β r)
  证明: by
  simp_rw [iSup, extent_sSup, ← Set.iInf_eq_iInter, iInf_range]

@[simp]

Depends on / 依赖: Set.iInf_eq_iInter, extent_sSup, iInf_eq_iInter, iInf_range, simp_rw
-/
theorem extent_iSup (f : ι -> Concept α β r) :
    (⨆ i, f i).extent = lowerPolar r (⋂ i, (f i).intent) := by
  simp_rw [iSup, extent_sSup, ← Set.iInf_eq_iInter, iInf_range]

@[simp]
/--
theorem `intent_iSup` / 定理 `intent_iSup`

English:
theorem intent_iSup
  given: (f : ι -> Concept α β r)
  statement: (⨆ i, f i).intent = ⋂ i, (f i).intent
  proof: by
  simp_rw [iSup, intent_sSup, ← Set.iInf_eq_iInter, iInf_range]

@[simp]

中文:
定理 intent_iSup
  条件: (f : ι -> Concept α β r)
  结论: (⨆ i, f i).intent = ⋂ i, (f i).intent
  证明: by
  simp_rw [iSup, intent_sSup, ← Set.iInf_eq_iInter, iInf_range]

@[simp]

Depends on / 依赖: Set.iInf_eq_iInter, iInf_eq_iInter, iInf_range, intent_sSup, simp_rw
-/
theorem intent_iSup (f : ι -> Concept α β r) : (⨆ i, f i).intent = ⋂ i, (f i).intent := by
  simp_rw [iSup, intent_sSup, ← Set.iInf_eq_iInter, iInf_range]

@[simp]
/--
theorem `extent_iInf` / 定理 `extent_iInf`

English:
theorem extent_iInf
  given: (f : ι -> Concept α β r)
  statement: (⨅ i, f i).extent = ⋂ i, (f i).extent
  proof: by
  simp_rw [iInf, extent_sInf, ← Set.iInf_eq_iInter, iInf_range]

@[simp]

中文:
定理 extent_iInf
  条件: (f : ι -> Concept α β r)
  结论: (⨅ i, f i).extent = ⋂ i, (f i).extent
  证明: by
  simp_rw [iInf, extent_sInf, ← Set.iInf_eq_iInter, iInf_range]

@[simp]

Depends on / 依赖: Set.iInf_eq_iInter, extent_sInf, iInf_eq_iInter, iInf_range, simp_rw
-/
theorem extent_iInf (f : ι -> Concept α β r) : (⨅ i, f i).extent = ⋂ i, (f i).extent := by
  simp_rw [iInf, extent_sInf, ← Set.iInf_eq_iInter, iInf_range]

@[simp]
/--
theorem `intent_iInf` / 定理 `intent_iInf`

English:
theorem intent_iInf
  given: (f : ι -> Concept α β r)
  proof: by
  simp_rw [iInf, intent_sInf, ← Set.iInf_eq_iInter, iInf_range]

中文:
定理 intent_iInf
  条件: (f : ι -> Concept α β r)
  证明: by
  simp_rw [iInf, intent_sInf, ← Set.iInf_eq_iInter, iInf_range]

Depends on / 依赖: Set.iInf_eq_iInter, iInf_eq_iInter, iInf_range, intent_sInf, simp_rw
-/
theorem intent_iInf (f : ι -> Concept α β r) :
    (⨅ i, f i).intent = upperPolar r (⋂ i, (f i).extent) := by
  simp_rw [iInf, intent_sInf, ← Set.iInf_eq_iInter, iInf_range]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Concept α β r)
  body: ⟨⊥⟩

中文:
实例 :
  签名: Inhabited (Concept α β r)
  定义体: ⟨⊥⟩
-/
instance : Inhabited (Concept α β r) :=
  ⟨⊥⟩

/-- Swap the sets of a concept to make it a concept of the dual context. -/
@[simps]
/--
Definition of `swap` / `swap` 的定义

English:
definition swap
  signature: (c : Concept α β r)
  body: ⟨c.intent, c.extent, c.lowerPolar_intent, c.upperPolar_extent⟩

@[simp]

中文:
定义 swap
  签名: (c : Concept α β r)
  定义体: ⟨c.intent, c.extent, c.lowerPolar_intent, c.upperPolar_extent⟩

@[simp]

Depends on / 依赖: c.extent, c.intent, c.lowerPolar_intent, c.upperPolar_extent, extent, intent, lowerPolar_intent, upperPolar_extent
-/
def swap (c : Concept α β r) : Concept β α (swap r) :=
  ⟨c.intent, c.extent, c.lowerPolar_intent, c.upperPolar_extent⟩

@[simp]
/--
theorem `swap_swap` / 定理 `swap_swap`

English:
theorem swap_swap
  given: (c : Concept α β r)
  statement: c.swap.swap = c
  proof: ext rfl

@[simp]

中文:
定理 swap_swap
  条件: (c : Concept α β r)
  结论: c.swap.swap = c
  证明: ext rfl

@[simp]
-/
theorem swap_swap (c : Concept α β r) : c.swap.swap = c :=
  ext rfl

@[simp]
/--
theorem `swap_le_swap_iff` / 定理 `swap_le_swap_iff`

English:
theorem swap_le_swap_iff
  statement: c.swap <= d.swap ↔ d <= c
  proof: intent_subset_intent_iff

@[simp]

中文:
定理 swap_le_swap_iff
  结论: c.swap <= d.swap ↔ d <= c
  证明: intent_subset_intent_iff

@[simp]

Depends on / 依赖: intent_subset_intent_iff
-/
theorem swap_le_swap_iff : c.swap <= d.swap ↔ d <= c :=
  intent_subset_intent_iff

@[simp]
/--
theorem `swap_lt_swap_iff` / 定理 `swap_lt_swap_iff`

English:
theorem swap_lt_swap_iff
  statement: c.swap < d.swap ↔ d < c
  proof: intent_ssubset_intent_iff

中文:
定理 swap_lt_swap_iff
  结论: c.swap < d.swap ↔ d < c
  证明: intent_ssubset_intent_iff

Depends on / 依赖: intent_ssubset_intent_iff
-/
theorem swap_lt_swap_iff : c.swap < d.swap ↔ d < c :=
  intent_ssubset_intent_iff

/-- The dual of a concept lattice is isomorphic to the concept lattice of the dual context. -/
@[simps]
/--
Definition of `swapEquiv` / `swapEquiv` 的定义

English:
definition swapEquiv
  signature: : (Concept α β r)ᵒᵈ ≃o Concept β α (Function.swap r) where
  body: swap ∘ ofDual
  invFun := toDual ∘ swap
  left_inv := swap_swap
  right_inv := swap_swap
  map_rel_iff' := swap_le_swap_iff

中文:
定义 swapEquiv
  签名: : (Concept α β r)ᵒᵈ ≃o Concept β α (Function.swap r) where
  定义体: swap ∘ ofDual
  invFun := toDual ∘ swap
  left_inv := swap_swap
  right_inv := swap_swap
  map_rel_iff' := swap_le_swap_iff

Depends on / 依赖: ofDual
-/
def swapEquiv : (Concept α β r)ᵒᵈ ≃o Concept β α (Function.swap r) where
  toFun := swap ∘ ofDual
  invFun := toDual ∘ swap
  left_inv := swap_swap
  right_inv := swap_swap
  map_rel_iff' := swap_le_swap_iff

end Concept
