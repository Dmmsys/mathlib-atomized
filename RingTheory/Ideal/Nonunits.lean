/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
module

public import Mathlib.RingTheory.Ideal.Maximal

/-!
# The set of non-invertible elements of a monoid

## Main definitions

* `nonunits` is the set of non-invertible elements of a monoid.

## Main results

* `exists_max_ideal_of_mem_nonunits`: every element of `nonunits` is contained in a maximal ideal
-/

@[expose] public section


variable {F α β : Type*} {a b : α}

/--
Definition of `nonunits` / `nonunits` 的定义

English:
definition nonunits
  signature: (α : Type*) [Monoid α]
  body: { a | ¬IsUnit a }

@[simp]

中文:
定义 nonunits
  签名: (α : 类型) [Monoid α]
  定义体: { a | ¬IsUnit a }

@[simp]

Depends on / 依赖: IsUnit
-/
def nonunits (α : Type*) [Monoid α] : Set α :=
  { a | ¬IsUnit a }

@[simp]
/--
theorem `mem_nonunits_iff` / 定理 `mem_nonunits_iff`

English:
theorem mem_nonunits_iff
  given: [Monoid α]
  statement: a in nonunits α ↔ ¬IsUnit a
  proof: Iff.rfl

中文:
定理 mem_nonunits_iff
  条件: [Monoid α]
  结论: a in nonunits α ↔ ¬IsUnit a
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_nonunits_iff [Monoid α] : a in nonunits α ↔ ¬IsUnit a :=
  Iff.rfl

/--
theorem `mul_mem_nonunits_right` / 定理 `mul_mem_nonunits_right`

English:
theorem mul_mem_nonunits_right
  given: [CommMonoid α]
  statement: b in nonunits α -> a * b in nonunits α
  proof: mt isUnit_of_mul_isUnit_right

中文:
定理 mul_mem_nonunits_right
  条件: [CommMonoid α]
  结论: b in nonunits α -> a * b in nonunits α
  证明: mt isUnit_of_mul_isUnit_right

Depends on / 依赖: isUnit_of_mul_isUnit_right
-/
theorem mul_mem_nonunits_right [CommMonoid α] : b in nonunits α -> a * b in nonunits α :=
  mt isUnit_of_mul_isUnit_right

/--
theorem `mul_mem_nonunits_left` / 定理 `mul_mem_nonunits_left`

English:
theorem mul_mem_nonunits_left
  given: [CommMonoid α]
  statement: a in nonunits α -> a * b in nonunits α
  proof: mt isUnit_of_mul_isUnit_left

中文:
定理 mul_mem_nonunits_left
  条件: [CommMonoid α]
  结论: a in nonunits α -> a * b in nonunits α
  证明: mt isUnit_of_mul_isUnit_left

Depends on / 依赖: isUnit_of_mul_isUnit_left
-/
theorem mul_mem_nonunits_left [CommMonoid α] : a in nonunits α -> a * b in nonunits α :=
  mt isUnit_of_mul_isUnit_left

/--
theorem `zero_mem_nonunits` / 定理 `zero_mem_nonunits`

English:
theorem zero_mem_nonunits
  given: [MonoidWithZero α]
  statement: 0 in nonunits α ↔ (0 : α) != 1
  proof: not_congr isUnit_zero_iff

@[simp high] -- High priority shortcut lemma

中文:
定理 zero_mem_nonunits
  条件: [MonoidWithZero α]
  结论: 0 in nonunits α ↔ (0 : α) != 1
  证明: not_congr isUnit_zero_iff

@[simp high] -- High priority shortcut lemma

Depends on / 依赖: isUnit_zero_iff, not_congr
-/
theorem zero_mem_nonunits [MonoidWithZero α] : 0 in nonunits α ↔ (0 : α) != 1 :=
  not_congr isUnit_zero_iff

@[simp high] -- High priority shortcut lemma
/--
theorem `one_notMem_nonunits` / 定理 `one_notMem_nonunits`

English:
theorem one_notMem_nonunits
  given: [Monoid α]
  statement: (1 : α) ∉ nonunits α
  proof: not_not_intro isUnit_one

@[simp high] -- High priority shortcut lemma

中文:
定理 one_notMem_nonunits
  条件: [Monoid α]
  结论: (1 : α) ∉ nonunits α
  证明: not_not_intro isUnit_one

@[simp high] -- High priority shortcut lemma

Depends on / 依赖: isUnit_one, not_not_intro
-/
theorem one_notMem_nonunits [Monoid α] : (1 : α) ∉ nonunits α :=
  not_not_intro isUnit_one

@[simp high] -- High priority shortcut lemma
/--
theorem `map_mem_nonunits_iff` / 定理 `map_mem_nonunits_iff`

English:
theorem map_mem_nonunits_iff
  statement: [Monoid α] [Monoid β] [FunLike F α β] [MonoidHomClass F α β] (f : F)
  proof: ⟨fun h ha => h ha.map f, fun h ha => h ha.of_map⟩

中文:
定理 map_mem_nonunits_iff
  结论: [Monoid α] [Monoid β] [FunLike F α β] [MonoidHomClass F α β] (f : F)
  证明: ⟨fun h ha => h ha.map f, fun h ha => h ha.of_map⟩

Depends on / 依赖: ha.map, ha.of_map, of_map
-/
theorem map_mem_nonunits_iff [Monoid α] [Monoid β] [FunLike F α β] [MonoidHomClass F α β] (f : F)
    [IsLocalHom f] (a) : f a in nonunits β ↔ a in nonunits α :=
⟨fun h ha => h ha.map f, fun h ha => h ha.of_map⟩

/--
theorem `coe_subset_nonunits` / 定理 `coe_subset_nonunits`

English:
theorem coe_subset_nonunits
  given: [Semiring α] {I : Ideal α} (h : I != ⊤)
  statement: (I : Set α) subseteq nonunits α
  proof: fun _x hx hu => h I.eq_top_of_isUnit_mem hx hu

中文:
定理 coe_subset_nonunits
  条件: [Semiring α] {I : Ideal α} (h : I != ⊤)
  结论: (I : Set α) subseteq nonunits α
  证明: fun _x hx hu => h I.eq_top_of_isUnit_mem hx hu

Depends on / 依赖: I.eq_top_of_isUnit_mem, eq_top_of_isUnit_mem
-/
theorem coe_subset_nonunits [Semiring α] {I : Ideal α} (h : I != ⊤) : (I : Set α) subseteq nonunits α :=
fun _x hx hu => h I.eq_top_of_isUnit_mem hx hu

/--
theorem `exists_max_ideal_of_mem_nonunits` / 定理 `exists_max_ideal_of_mem_nonunits`

English:
theorem exists_max_ideal_of_mem_nonunits
  given: [CommSemiring α] (h : a in nonunits α)
  proof: by
  have : Ideal.span ({a} : Set α) != ⊤ := by
    intro H
    rw [Ideal.span_singleton_eq_top] at H
    contradiction
  rcases Ideal.exists_le_maximal _ this with ⟨I, Imax, H⟩
  use I, Imax
  apply H
  apply Ideal.subset_span
  exact Set.mem_singleton a

中文:
定理 exists_max_ideal_of_mem_nonunits
  条件: [CommSemiring α] (h : a in nonunits α)
  证明: by
  have : Ideal.span ({a} : Set α) != ⊤ := by
    intro H
    rw [Ideal.span_singleton_eq_top] at H
    contradiction
  rcases Ideal.exists_le_maximal _ this with ⟨I, Imax, H⟩
  use I, Imax
  apply H
  apply Ideal.subset_span
  exact Set.mem_singleton a

Depends on / 依赖: Ideal.exists_le_maximal, Ideal.span, Ideal.span_singleton_eq_top, Ideal.subset_span, Set.mem_singleton, exists_le_maximal, mem_singleton, span_singleton_eq_top, subset_span
-/
theorem exists_max_ideal_of_mem_nonunits [CommSemiring α] (h : a in nonunits α) :
    exists I : Ideal α, I.IsMaximal ∧ a in I := by
  have : Ideal.span ({a} : Set α) != ⊤ := by
    intro H
    rw [Ideal.span_singleton_eq_top] at H
    contradiction
  rcases Ideal.exists_le_maximal _ this with ⟨I, Imax, H⟩
  use I, Imax
  apply H
  apply Ideal.subset_span
  exact Set.mem_singleton a

namespace Submonoid

variable {C : Type*} [SetLike C α]

/--
theorem `inv_mem_of_isUnit` / 定理 `inv_mem_of_isUnit`

English:
theorem inv_mem_of_isUnit
  given: [DivisionMonoid α] [SubmonoidClass C α] {S : C} {a : S} (ha : IsUnit a)
  proof: by
  obtain ⟨u, rfl⟩ := ha
  convert! u⁻¹.1.2
  exact (map_inv ((subtype <| ofClass S).comp <| Units.coeHom S) u).symm

中文:
定理 inv_mem_of_isUnit
  条件: [DivisionMonoid α] [SubmonoidClass C α] {S : C} {a : S} (ha : IsUnit a)
  证明: by
  obtain ⟨u, rfl⟩ := ha
  convert! u⁻¹.1.2
  exact (map_inv ((subtype <| ofClass S).comp <| Units.coeHom S) u).symm

Depends on / 依赖: Units.coeHom, coeHom, convert, map_inv, ofClass, subtype
-/
theorem inv_mem_of_isUnit [DivisionMonoid α] [SubmonoidClass C α] {S : C} {a : S} (ha : IsUnit a) :
    (a : α)⁻¹ in S := by
  obtain ⟨u, rfl⟩ := ha
  convert! u⁻¹.1.2
  exact (map_inv ((subtype <| ofClass S).comp <| Units.coeHom S) u).symm

section Group

variable [Group α] [SubmonoidClass C α] {S : C} {a : S}

/--
theorem `isUnit_iff` / 定理 `isUnit_iff`

English:
theorem isUnit_iff
  statement: IsUnit a ↔ (a : α)⁻¹ in S where
  proof: inv_mem_of_isUnit
  mpr h := ⟨⟨a, ⟨_, h⟩, Subtype.ext (mul_inv_cancel _), Subtype.ext (inv_mul_cancel _)⟩, rfl⟩

中文:
定理 isUnit_iff
  结论: IsUnit a ↔ (a : α)⁻¹ in S where
  证明: inv_mem_of_isUnit
  mpr h := ⟨⟨a, ⟨_, h⟩, Subtype.ext (mul_inv_cancel _), Subtype.ext (inv_mul_cancel _)⟩, rfl⟩

Depends on / 依赖: inv_mem_of_isUnit
-/
theorem isUnit_iff : IsUnit a ↔ (a : α)⁻¹ in S where
  mp := inv_mem_of_isUnit
  mpr h := ⟨⟨a, ⟨_, h⟩, Subtype.ext (mul_inv_cancel _), Subtype.ext (inv_mul_cancel _)⟩, rfl⟩

/--
theorem `mem_nonunits_iff` / 定理 `mem_nonunits_iff`

English:
theorem mem_nonunits_iff
  statement: a in nonunits S ↔ (a : α)⁻¹ ∉ S
  proof: by
  rw [mem_nonunits_iff]; rw [isUnit_iff]

中文:
定理 mem_nonunits_iff
  结论: a in nonunits S ↔ (a : α)⁻¹ ∉ S
  证明: by
  rw [mem_nonunits_iff]; rw [isUnit_iff]
-/
protected theorem mem_nonunits_iff : a in nonunits S ↔ (a : α)⁻¹ ∉ S := by
  rw [mem_nonunits_iff]; rw [isUnit_iff]

end Group

section GroupWithZero

variable [GroupWithZero α] [SubmonoidClass C α] {S : C} {a : S}

/--
theorem `isUnit_iff_and` / 定理 `isUnit_iff_and`

English:
theorem isUnit_iff_and
  statement: IsUnit a ↔ (a : α) != 0 ∧ (a : α)⁻¹ in S where
  proof: ⟨(h.map <| subtype <| ofClass S).ne_zero, inv_mem_of_isUnit h⟩
  mpr h :=
    ⟨⟨a, ⟨_, h.2⟩, Subtype.ext (mul_inv_cancel₀ h.1), Subtype.ext (inv_mul_cancel₀ h.1)⟩, rfl⟩

中文:
定理 isUnit_iff_and
  结论: IsUnit a ↔ (a : α) != 0 ∧ (a : α)⁻¹ in S where
  证明: ⟨(h.map <| subtype <| ofClass S).ne_zero, inv_mem_of_isUnit h⟩
  mpr h :=
    ⟨⟨a, ⟨_, h.2⟩, Subtype.ext (mul_inv_cancel₀ h.1), Subtype.ext (inv_mul_cancel₀ h.1)⟩, rfl⟩

Depends on / 依赖: h.map, inv_mem_of_isUnit, ne_zero, ofClass, subtype
-/
theorem isUnit_iff_and : IsUnit a ↔ (a : α) != 0 ∧ (a : α)⁻¹ in S where
  mp h := ⟨(h.map <| subtype <| ofClass S).ne_zero, inv_mem_of_isUnit h⟩
  mpr h :=
    ⟨⟨a, ⟨_, h.2⟩, Subtype.ext (mul_inv_cancel₀ h.1), Subtype.ext (inv_mul_cancel₀ h.1)⟩, rfl⟩

/--
theorem `isUnit_iff_of_ne_zero` / 定理 `isUnit_iff_of_ne_zero`

English:
theorem isUnit_iff_of_ne_zero
  given: (ha : (a : α) != 0)
  statement: IsUnit a ↔ (a : α)⁻¹ in S
  proof: by
  rw [isUnit_iff_and]; rw [and_iff_right ha]

中文:
定理 isUnit_iff_of_ne_zero
  条件: (ha : (a : α) != 0)
  结论: IsUnit a ↔ (a : α)⁻¹ in S
  证明: by
  rw [isUnit_iff_and]; rw [and_iff_right ha]

Depends on / 依赖: and_iff_right, isUnit_iff_and
-/
theorem isUnit_iff_of_ne_zero (ha : (a : α) != 0) : IsUnit a ↔ (a : α)⁻¹ in S := by
  rw [isUnit_iff_and]; rw [and_iff_right ha]

/--
theorem `mem_nonunits_iff_or` / 定理 `mem_nonunits_iff_or`

English:
theorem mem_nonunits_iff_or
  statement: a in nonunits S ↔ (a : α) = 0 ∨ (a : α)⁻¹ ∉ S
  proof: by
  rw [mem_nonunits_iff]; rw [isUnit_iff_and]; rw [not_and_or]; rw [Ne]; rw [not_not]

中文:
定理 mem_nonunits_iff_or
  结论: a in nonunits S ↔ (a : α) = 0 ∨ (a : α)⁻¹ ∉ S
  证明: by
  rw [mem_nonunits_iff]; rw [isUnit_iff_and]; rw [not_and_or]; rw [Ne]; rw [not_not]

Depends on / 依赖: isUnit_iff_and, mem_nonunits_iff, not_and_or, not_not
-/
theorem mem_nonunits_iff_or : a in nonunits S ↔ (a : α) = 0 ∨ (a : α)⁻¹ ∉ S := by
  rw [mem_nonunits_iff]; rw [isUnit_iff_and]; rw [not_and_or]; rw [Ne]; rw [not_not]

/--
theorem `mem_nonunits_iff_of_ne_zero` / 定理 `mem_nonunits_iff_of_ne_zero`

English:
theorem mem_nonunits_iff_of_ne_zero
  given: (ha : (a : α) != 0)
  statement: a in nonunits S ↔ (a : α)⁻¹ ∉ S
  proof: by
  rw [mem_nonunits_iff_or]; rw [or_iff_right ha]

中文:
定理 mem_nonunits_iff_of_ne_zero
  条件: (ha : (a : α) != 0)
  结论: a in nonunits S ↔ (a : α)⁻¹ ∉ S
  证明: by
  rw [mem_nonunits_iff_or]; rw [or_iff_right ha]

Depends on / 依赖: mem_nonunits_iff_or, or_iff_right
-/
theorem mem_nonunits_iff_of_ne_zero (ha : (a : α) != 0) : a in nonunits S ↔ (a : α)⁻¹ ∉ S := by
  rw [mem_nonunits_iff_or]; rw [or_iff_right ha]

end GroupWithZero

end Submonoid
