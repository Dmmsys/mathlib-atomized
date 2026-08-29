/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.SetTheory.Cardinal.Finite

/-!

# Cardinality of finite types

The cardinality of a finite type `α` is given by `Nat.card α`. This function has
the "junk value" of `0` for infinite types, but to ensure the function has valid
output, one just needs to know that it's possible to produce a `Finite` instance
for the type. (Note: we could have defined a `Finite.card` that required you to
supply a `Finite` instance, but (a) the function would be `noncomputable` anyway
so there is no need to supply the instance and (b) the function would have a more
complicated dependent type that easily leads to "motive not type correct" errors.)

## Implementation notes

Theorems about `Nat.card` are sometimes incidentally true for both finite and infinite
types. If removing a finiteness constraint results in no loss in legibility, we remove
it. We generally put such theorems into the `SetTheory.Cardinal.Finite` module.

-/

@[expose] public section

assert_not_exists Field

noncomputable section

variable {α β γ : Type*}

/--
Definition of `Finite.equivFin` / `Finite.equivFin` 的定义

English:
definition Finite.equivFin
  signature: (α : Type*) [Finite α]
  body: by
  have := (Finite.exists_equiv_fin α).choose_spec.some
  rwa [Nat.card_eq_of_equiv_fin this]

中文:
定义 有限.equivFin
  签名: (α : 类型) [有限 α]
  定义体: by
  have := (Finite.exists_equiv_fin α).choose_spec.some
  rwa [Nat.card_eq_of_equiv_fin this]

Depends on / 依赖: Finite, Finite.exists_equiv_fin, Nat.card_eq_of_equiv_fin, card_eq_of_equiv_fin, choose_spec, choose_spec.some, exists_equiv_fin
-/
def Finite.equivFin (α : Type*) [Finite α] : α ≃ Fin (Nat.card α) := by
  have := (Finite.exists_equiv_fin α).choose_spec.some
  rwa [Nat.card_eq_of_equiv_fin this]

/--
Definition of `Finite.equivFinOfCardEq` / `Finite.equivFinOfCardEq` 的定义

English:
definition Finite.equivFinOfCardEq
  signature: [Finite α] {n : Nat} (h : Nat.card α = n)
  body: by
  subst h
  apply Finite.equivFin

中文:
定义 有限.equivFinOfCardEq
  签名: [有限 α] {n : 自然数} (h : 自然数.card α = n)
  定义体: by
  subst h
  apply Finite.equivFin

Depends on / 依赖: Finite, Finite.equivFin, equivFin
-/
def Finite.equivFinOfCardEq [Finite α] {n : Nat} (h : Nat.card α = n) : α ≃ Fin n := by
  subst h
  apply Finite.equivFin

open scoped Classical in
/--
theorem `Nat.card_eq` / 定理 `Nat.card_eq`

English:
theorem Nat.card_eq
  given: (α : Type*)
  proof: by
  cases finite_or_infinite α
  · let := Fintype.ofFinite α
    simp only [this, *, Nat.card_eq_fintype_card, dif_pos]
  · simp only [*, card_eq_zero_of_infinite, not_finite_iff_infinite.mpr, dite_false]

中文:
定理 自然数.card_eq
  条件: (α : 类型)
  证明: by
  cases finite_or_infinite α
  · let := Fintype.ofFinite α
    simp only [this, *, Nat.card_eq_fintype_card, dif_pos]
  · simp only [*, card_eq_zero_of_infinite, not_finite_iff_infinite.mpr, dite_false]

Depends on / 依赖: Fintype, Fintype.ofFinite, Nat.card_eq_fintype_card, card_eq_fintype_card, card_eq_zero_of_infinite, dif_pos, dite_false, finite_or_infinite, not_finite_iff_infinite, not_finite_iff_infinite.mpr, ofFinite
-/
theorem Nat.card_eq (α : Type*) :
    Nat.card α = if _ : Finite α then @Fintype.card α (Fintype.ofFinite α) else 0 := by
  cases finite_or_infinite α
  · let := Fintype.ofFinite α
    simp only [this, *, Nat.card_eq_fintype_card, dif_pos]
  · simp only [*, card_eq_zero_of_infinite, not_finite_iff_infinite.mpr, dite_false]

/--
theorem `Finite.card_pos_iff` / 定理 `Finite.card_pos_iff`

English:
theorem Finite.card_pos_iff
  given: [Finite α]
  statement: 0 < Nat.card α ↔ Nonempty α
  proof: by
  have := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card]; rw [Fintype.card_pos_iff]

中文:
定理 有限.card_pos_iff
  条件: [有限 α]
  结论: 0 < 自然数.card α ↔ 非空 α
  证明: by
  have := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card]; rw [Fintype.card_pos_iff]

Depends on / 依赖: Fintype, Fintype.card_pos_iff, Fintype.ofFinite, Nat.card_eq_fintype_card, card_eq_fintype_card, card_pos_iff, ofFinite
-/
theorem Finite.card_pos_iff [Finite α] : 0 < Nat.card α ↔ Nonempty α := by
  have := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card]; rw [Fintype.card_pos_iff]

/--
theorem `Finite.card_pos` / 定理 `Finite.card_pos`

English:
theorem Finite.card_pos
  given: [Finite α] [h : Nonempty α]
  statement: 0 < Nat.card α
  proof: Finite.card_pos_iff.mpr h

中文:
定理 有限.card_pos
  条件: [有限 α] [h : 非空 α]
  结论: 0 < 自然数.card α
  证明: Finite.card_pos_iff.mpr h

Depends on / 依赖: Finite, Finite.card_pos_iff.mpr, card_pos_iff
-/
theorem Finite.card_pos [Finite α] [h : Nonempty α] : 0 < Nat.card α :=
  Finite.card_pos_iff.mpr h

namespace Finite

/--
theorem `card_eq` / 定理 `card_eq`

English:
theorem card_eq
  given: [Finite α] [Finite β]
  statement: Nat.card α = Nat.card β ↔ Nonempty (α ≃ β)
  proof: by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  simp only [Nat.card_eq_fintype_card, Fintype.card_eq]

中文:
定理 card_eq
  条件: [有限 α] [有限 β]
  结论: 自然数.card α = 自然数.card β ↔ 非空 (α ≃ β)
  证明: by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  simp only [Nat.card_eq_fintype_card, Fintype.card_eq]

Depends on / 依赖: Fintype, Fintype.card_eq, Fintype.ofFinite, Nat.card_eq_fintype_card, card_eq, card_eq_fintype_card, ofFinite
-/
theorem card_eq [Finite α] [Finite β] : Nat.card α = Nat.card β ↔ Nonempty (α ≃ β) := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  simp only [Nat.card_eq_fintype_card, Fintype.card_eq]

/--
theorem `card_le_one_iff_subsingleton` / 定理 `card_le_one_iff_subsingleton`

English:
theorem card_le_one_iff_subsingleton
  given: [Finite α]
  statement: Nat.card α <= 1 ↔ Subsingleton α
  proof: by
  have := Fintype.ofFinite α
  simp only [Nat.card_eq_fintype_card, Fintype.card_le_one_iff_subsingleton]

中文:
定理 card_le_one_iff_subsingleton
  条件: [有限 α]
  结论: 自然数.card α <= 1 ↔ 子单例 α
  证明: by
  have := Fintype.ofFinite α
  simp only [Nat.card_eq_fintype_card, Fintype.card_le_one_iff_subsingleton]

Depends on / 依赖: Fintype, Fintype.card_le_one_iff_subsingleton, Fintype.ofFinite, Nat.card_eq_fintype_card, card_eq_fintype_card, card_le_one_iff_subsingleton, ofFinite
-/
theorem card_le_one_iff_subsingleton [Finite α] : Nat.card α <= 1 ↔ Subsingleton α := by
  have := Fintype.ofFinite α
  simp only [Nat.card_eq_fintype_card, Fintype.card_le_one_iff_subsingleton]

/--
theorem `one_lt_card_iff_nontrivial` / 定理 `one_lt_card_iff_nontrivial`

English:
theorem one_lt_card_iff_nontrivial
  given: [Finite α]
  statement: 1 < Nat.card α ↔ Nontrivial α
  proof: by
  have := Fintype.ofFinite α
  simp only [Nat.card_eq_fintype_card, Fintype.one_lt_card_iff_nontrivial]

中文:
定理 one_lt_card_iff_nontrivial
  条件: [有限 α]
  结论: 1 < 自然数.card α ↔ 非平凡 α
  证明: by
  have := Fintype.ofFinite α
  simp only [Nat.card_eq_fintype_card, Fintype.one_lt_card_iff_nontrivial]

Depends on / 依赖: Fintype, Fintype.ofFinite, Fintype.one_lt_card_iff_nontrivial, Nat.card_eq_fintype_card, card_eq_fintype_card, ofFinite, one_lt_card_iff_nontrivial
-/
theorem one_lt_card_iff_nontrivial [Finite α] : 1 < Nat.card α ↔ Nontrivial α := by
  have := Fintype.ofFinite α
  simp only [Nat.card_eq_fintype_card, Fintype.one_lt_card_iff_nontrivial]

/--
theorem `one_lt_card` / 定理 `one_lt_card`

English:
theorem one_lt_card
  given: [Finite α] [h : Nontrivial α]
  statement: 1 < Nat.card α
  proof: one_lt_card_iff_nontrivial.mpr h

@[simp]

中文:
定理 one_lt_card
  条件: [有限 α] [h : 非平凡 α]
  结论: 1 < 自然数.card α
  证明: one_lt_card_iff_nontrivial.mpr h

@[simp]

Depends on / 依赖: one_lt_card_iff_nontrivial, one_lt_card_iff_nontrivial.mpr
-/
theorem one_lt_card [Finite α] [h : Nontrivial α] : 1 < Nat.card α :=
  one_lt_card_iff_nontrivial.mpr h

@[simp]
/--
theorem `card_option` / 定理 `card_option`

English:
theorem card_option
  given: [Finite α]
  statement: Nat.card (Option α) = Nat.card α + 1
  proof: by
  have := Fintype.ofFinite α
  simp only [Nat.card_eq_fintype_card, Fintype.card_option]

中文:
定理 card_option
  条件: [有限 α]
  结论: 自然数.card (选项类型 α) = 自然数.card α + 1
  证明: by
  have := Fintype.ofFinite α
  simp only [Nat.card_eq_fintype_card, Fintype.card_option]

Depends on / 依赖: Fintype, Fintype.card_option, Fintype.ofFinite, Nat.card_eq_fintype_card, card_eq_fintype_card, card_option, ofFinite
-/
theorem card_option [Finite α] : Nat.card (Option α) = Nat.card α + 1 := by
  have := Fintype.ofFinite α
  simp only [Nat.card_eq_fintype_card, Fintype.card_option]

/--
theorem `card_le_of_embedding` / 定理 `card_le_of_embedding`

English:
theorem card_le_of_embedding
  given: [Finite β] (f : α ↪ β)
  statement: Nat.card α <= Nat.card β
  proof: Nat.card_le_card_of_injective _ f.injective

中文:
定理 card_le_of_embedding
  条件: [有限 β] (f : α ↪ β)
  结论: 自然数.card α <= 自然数.card β
  证明: Nat.card_le_card_of_injective _ f.injective

Depends on / 依赖: Nat.card_le_card_of_injective, card_le_card_of_injective, f.injective, injective
-/
theorem card_le_of_embedding [Finite β] (f : α ↪ β) : Nat.card α <= Nat.card β :=
  Nat.card_le_card_of_injective _ f.injective

/--
theorem `card_eq_zero_iff` / 定理 `card_eq_zero_iff`

English:
theorem card_eq_zero_iff
  given: [Finite α]
  statement: Nat.card α = 0 ↔ IsEmpty α
  proof: by
  have := Fintype.ofFinite α
  simp only [Nat.card_eq_fintype_card, Fintype.card_eq_zero_iff]

中文:
定理 card_eq_zero_iff
  条件: [有限 α]
  结论: 自然数.card α = 0 ↔ 是空 α
  证明: by
  have := Fintype.ofFinite α
  simp only [Nat.card_eq_fintype_card, Fintype.card_eq_zero_iff]

Depends on / 依赖: Fintype, Fintype.card_eq_zero_iff, Fintype.ofFinite, Nat.card_eq_fintype_card, card_eq_fintype_card, card_eq_zero_iff, ofFinite
-/
theorem card_eq_zero_iff [Finite α] : Nat.card α = 0 ↔ IsEmpty α := by
  have := Fintype.ofFinite α
  simp only [Nat.card_eq_fintype_card, Fintype.card_eq_zero_iff]

/--
theorem `card_le_of_injective'` / 定理 `card_le_of_injective'`

English:
theorem card_le_of_injective'
  statement: {f : α -> β} (hf : Function.Injective f)
  proof: (or_not_of_imp h).casesOn (fun h => le_of_eq_of_le h (Nat.zero_le _)) fun h =>
    @Nat.card_le_card_of_injective α β (Nat.finite_of_card_ne_zero h) f hf

中文:
定理 card_le_of_injective'
  结论: {f : α -> β} (hf : 函数.单射 f)
  证明: (or_not_of_imp h).casesOn (fun h => le_of_eq_of_le h (Nat.zero_le _)) fun h =>
    @Nat.card_le_card_of_injective α β (Nat.finite_of_card_ne_zero h) f hf

Depends on / 依赖: Nat.card_le_card_of_injective, Nat.finite_of_card_ne_zero, Nat.zero_le, card_le_card_of_injective, casesOn, finite_of_card_ne_zero, le_of_eq_of_le, or_not_of_imp, zero_le
-/
theorem card_le_of_injective' {f : α -> β} (hf : Function.Injective f)
    (h : Nat.card β = 0 -> Nat.card α = 0) : Nat.card α <= Nat.card β :=
  (or_not_of_imp h).casesOn (fun h => le_of_eq_of_le h (Nat.zero_le _)) fun h =>
    @Nat.card_le_card_of_injective α β (Nat.finite_of_card_ne_zero h) f hf

/--
theorem `card_le_of_embedding'` / 定理 `card_le_of_embedding'`

English:
theorem card_le_of_embedding'
  given: (f : α ↪ β) (h : Nat.card β = 0 -> Nat.card α = 0)
  proof: card_le_of_injective' f.2 h

中文:
定理 card_le_of_embedding'
  条件: (f : α ↪ β) (h : 自然数.card β = 0 -> 自然数.card α = 0)
  证明: card_le_of_injective' f.2 h

Depends on / 依赖: card_le_of_injective
-/
theorem card_le_of_embedding' (f : α ↪ β) (h : Nat.card β = 0 -> Nat.card α = 0) :
    Nat.card α <= Nat.card β :=
  card_le_of_injective' f.2 h

/--
theorem `card_le_of_surjective'` / 定理 `card_le_of_surjective'`

English:
theorem card_le_of_surjective'
  statement: {f : α -> β} (hf : Function.Surjective f)
  proof: (or_not_of_imp h).casesOn (fun h => le_of_eq_of_le h (Nat.zero_le _)) fun h =>
    @Nat.card_le_card_of_surjective α β (Nat.finite_of_card_ne_zero h) f hf

中文:
定理 card_le_of_surjective'
  结论: {f : α -> β} (hf : 函数.满射 f)
  证明: (or_not_of_imp h).casesOn (fun h => le_of_eq_of_le h (Nat.zero_le _)) fun h =>
    @Nat.card_le_card_of_surjective α β (Nat.finite_of_card_ne_zero h) f hf

Depends on / 依赖: Nat.card_le_card_of_surjective, Nat.finite_of_card_ne_zero, Nat.zero_le, card_le_card_of_surjective, casesOn, finite_of_card_ne_zero, le_of_eq_of_le, or_not_of_imp, zero_le
-/
theorem card_le_of_surjective' {f : α -> β} (hf : Function.Surjective f)
    (h : Nat.card α = 0 -> Nat.card β = 0) : Nat.card β <= Nat.card α :=
  (or_not_of_imp h).casesOn (fun h => le_of_eq_of_le h (Nat.zero_le _)) fun h =>
    @Nat.card_le_card_of_surjective α β (Nat.finite_of_card_ne_zero h) f hf

/--
theorem `card_eq_zero_of_surjective` / 定理 `card_eq_zero_of_surjective`

English:
theorem card_eq_zero_of_surjective
  given: {f : α -> β} (hf : Function.Surjective f) (h : Nat.card β = 0)
  proof: by
  cases finite_or_infinite β
  · have := card_eq_zero_iff.mp h
    have := Function.isEmpty f
    exact Nat.card_of_isEmpty
  · have := Infinite.of_surjective f hf
    exact Nat.card_eq_zero_of_infinite

中文:
定理 card_eq_zero_of_surjective
  条件: {f : α -> β} (hf : 函数.满射 f) (h : 自然数.card β = 0)
  证明: by
  cases finite_or_infinite β
  · have := card_eq_zero_iff.mp h
    have := Function.isEmpty f
    exact Nat.card_of_isEmpty
  · have := Infinite.of_surjective f hf
    exact Nat.card_eq_zero_of_infinite

Depends on / 依赖: Function, Function.isEmpty, Infinite, Infinite.of_surjective, Nat.card_eq_zero_of_infinite, Nat.card_of_isEmpty, card_eq_zero_iff, card_eq_zero_iff.mp, card_eq_zero_of_infinite, card_of_isEmpty, finite_or_infinite, isEmpty, of_surjective
-/
theorem card_eq_zero_of_surjective {f : α -> β} (hf : Function.Surjective f) (h : Nat.card β = 0) :
    Nat.card α = 0 := by
  cases finite_or_infinite β
  · have := card_eq_zero_iff.mp h
    have := Function.isEmpty f
    exact Nat.card_of_isEmpty
  · have := Infinite.of_surjective f hf
    exact Nat.card_eq_zero_of_infinite

/--
theorem `card_eq_zero_of_injective` / 定理 `card_eq_zero_of_injective`

English:
theorem card_eq_zero_of_injective
  statement: [Nonempty α] {f : α -> β} (hf : Function.Injective f)
  proof: card_eq_zero_of_surjective (Function.invFun_surjective hf) h

中文:
定理 card_eq_zero_of_injective
  结论: [非空 α] {f : α -> β} (hf : 函数.单射 f)
  证明: card_eq_zero_of_surjective (Function.invFun_surjective hf) h

Depends on / 依赖: Function, Function.invFun_surjective, card_eq_zero_of_surjective, invFun_surjective
-/
theorem card_eq_zero_of_injective [Nonempty α] {f : α -> β} (hf : Function.Injective f)
    (h : Nat.card α = 0) : Nat.card β = 0 :=
  card_eq_zero_of_surjective (Function.invFun_surjective hf) h

/--
theorem `card_eq_zero_of_embedding` / 定理 `card_eq_zero_of_embedding`

English:
theorem card_eq_zero_of_embedding
  given: [Nonempty α] (f : α ↪ β) (h : Nat.card α = 0)
  statement: Nat.card β = 0
  proof: card_eq_zero_of_injective f.2 h

中文:
定理 card_eq_zero_of_embedding
  条件: [非空 α] (f : α ↪ β) (h : 自然数.card α = 0)
  结论: 自然数.card β = 0
  证明: card_eq_zero_of_injective f.2 h

Depends on / 依赖: card_eq_zero_of_injective
-/
theorem card_eq_zero_of_embedding [Nonempty α] (f : α ↪ β) (h : Nat.card α = 0) : Nat.card β = 0 :=
  card_eq_zero_of_injective f.2 h

/--
theorem `card_image_le` / 定理 `card_image_le`

English:
theorem card_image_le
  given: {s : Set α} [Finite s] (f : α -> β)
  statement: Nat.card (f '' s) <= Nat.card s
  proof: Nat.card_le_card_of_surjective _ Set.imageFactorization_surjective

中文:
定理 card_image_le
  条件: {s : 集合 α} [有限 s] (f : α -> β)
  结论: 自然数.card (f '' s) <= 自然数.card s
  证明: Nat.card_le_card_of_surjective _ Set.imageFactorization_surjective

Depends on / 依赖: Nat.card_le_card_of_surjective, Set.imageFactorization_surjective, card_le_card_of_surjective, imageFactorization_surjective
-/
theorem card_image_le {s : Set α} [Finite s] (f : α -> β) : Nat.card (f '' s) <= Nat.card s :=
  Nat.card_le_card_of_surjective _ Set.imageFactorization_surjective

/--
theorem `card_range_le` / 定理 `card_range_le`

English:
theorem card_range_le
  given: [Finite α] (f : α -> β)
  statement: Nat.card (Set.range f) <= Nat.card α
  proof: Nat.card_le_card_of_surjective _ Set.rangeFactorization_surjective

中文:
定理 card_range_le
  条件: [有限 α] (f : α -> β)
  结论: 自然数.card (集合.range f) <= 自然数.card α
  证明: Nat.card_le_card_of_surjective _ Set.rangeFactorization_surjective

Depends on / 依赖: Nat.card_le_card_of_surjective, Set.rangeFactorization_surjective, card_le_card_of_surjective, rangeFactorization_surjective
-/
theorem card_range_le [Finite α] (f : α -> β) : Nat.card (Set.range f) <= Nat.card α :=
  Nat.card_le_card_of_surjective _ Set.rangeFactorization_surjective

/--
theorem `card_subtype_le` / 定理 `card_subtype_le`

English:
theorem card_subtype_le
  given: [Finite α] (p : α -> Prop)
  statement: Nat.card { x // p x } <= Nat.card α
  proof: by
  classical
  have := Fintype.ofFinite α
  simpa only [Nat.card_eq_fintype_card] using Fintype.card_subtype_le p

中文:
定理 card_subtype_le
  条件: [有限 α] (p : α -> 命题)
  结论: 自然数.card { x // p x } <= 自然数.card α
  证明: by
  classical
  have := Fintype.ofFinite α
  simpa only [Nat.card_eq_fintype_card] using Fintype.card_subtype_le p

Depends on / 依赖: Fintype, Fintype.card_subtype_le, Fintype.ofFinite, Nat.card_eq_fintype_card, card_eq_fintype_card, card_subtype_le, classical, ofFinite
-/
theorem card_subtype_le [Finite α] (p : α -> Prop) : Nat.card { x // p x } <= Nat.card α := by
  classical
  have := Fintype.ofFinite α
  simpa only [Nat.card_eq_fintype_card] using Fintype.card_subtype_le p

/--
theorem `card_subtype_lt` / 定理 `card_subtype_lt`

English:
theorem card_subtype_lt
  given: [Finite α] {p : α -> Prop} {x : α} (hx : ¬p x)
  proof: by
  classical
  have := Fintype.ofFinite α
  simpa only [Nat.card_eq_fintype_card, gt_iff_lt] using Fintype.card_subtype_lt hx

中文:
定理 card_subtype_lt
  条件: [有限 α] {p : α -> 命题} {x : α} (hx : ¬p x)
  证明: by
  classical
  have := Fintype.ofFinite α
  simpa only [Nat.card_eq_fintype_card, gt_iff_lt] using Fintype.card_subtype_lt hx

Depends on / 依赖: Fintype, Fintype.card_subtype_lt, Fintype.ofFinite, Nat.card_eq_fintype_card, card_eq_fintype_card, card_subtype_lt, classical, gt_iff_lt, ofFinite
-/
theorem card_subtype_lt [Finite α] {p : α -> Prop} {x : α} (hx : ¬p x) :
    Nat.card { x // p x } < Nat.card α := by
  classical
  have := Fintype.ofFinite α
  simpa only [Nat.card_eq_fintype_card, gt_iff_lt] using Fintype.card_subtype_lt hx

/-- A custom induction principle for finite types, by strong induction on `Nat.card`:
the base case is a subsingleton type, and the induction step is for nontrivial types,
where one can assume the hypothesis for all types of smaller cardinality. -/
@[elab_as_elim]
/--
theorem `induction_subsingleton_or_nontrivial` / 定理 `induction_subsingleton_or_nontrivial`

English:
theorem induction_subsingleton_or_nontrivial
  statement: {P : Type* -> Prop} (α) [Finite α]
  proof: by
  obtain ⟨n, hn⟩ : exists n, Nat.card α = n := ⟨Nat.card α, rfl⟩
  induction n using Nat.strong_induction_on generalizing α with | _ n ih
  rcases subsingleton_or_nontrivial α with hsing | hnontriv
  · apply hbase
  · apply hstep
    intro β _ hlt
    rw [hn] at hlt
    exact ih (Nat.card β) hlt 

中文:
定理 induction_subsingleton_or_nontrivial
  结论: {P : 类型 -> 命题} (α) [有限 α]
  证明: by
  obtain ⟨n, hn⟩ : exists n, Nat.card α = n := ⟨Nat.card α, rfl⟩
  induction n using Nat.strong_induction_on generalizing α with | _ n ih
  rcases subsingleton_or_nontrivial α with hsing | hnontriv
  · apply hbase
  · apply hstep
    intro β _ hlt
    rw [hn] at hlt
    exact ih (Nat.card β) hlt 

Depends on / 依赖: Nat.card, Nat.strong_induction_on, generalizing, hnontriv, strong_induction_on, subsingleton_or_nontrivial
-/
theorem induction_subsingleton_or_nontrivial {P : Type* -> Prop} (α) [Finite α]
    (hbase : forall (α) [Finite α] [Subsingleton α], P α)
    (hstep : forall (α) [Finite α] [Nontrivial α],
      (forall (β) [Finite β], Nat.card β < Nat.card α -> P β) -> P α) :
    P α := by
  obtain ⟨n, hn⟩ : exists n, Nat.card α = n := ⟨Nat.card α, rfl⟩
  induction n using Nat.strong_induction_on generalizing α with | _ n ih
  rcases subsingleton_or_nontrivial α with hsing | hnontriv
  · apply hbase
  · apply hstep
    intro β _ hlt
    rw [hn] at hlt
    exact ih (Nat.card β) hlt _ rfl

end Finite

namespace ENat

/--
theorem `card_eq_coe_natCard` / 定理 `card_eq_coe_natCard`

English:
theorem card_eq_coe_natCard
  given: (α : Type*) [Finite α]
  statement: card α = Nat.card α
  proof: by
  unfold ENat.card
  apply symm
  rw [Cardinal.natCast_eq_toENat]
  exact Nat.cast_card

中文:
定理 card_eq_coe_natCard
  条件: (α : 类型) [有限 α]
  结论: card α = 自然数.card α
  证明: by
  unfold ENat.card
  apply symm
  rw [Cardinal.natCast_eq_toENat]
  exact Nat.cast_card

Depends on / 依赖: Cardinal, Cardinal.natCast_eq_toENat, ENat.card, Nat.cast_card, cast_card, natCast_eq_toENat
-/
theorem card_eq_coe_natCard (α : Type*) [Finite α] : card α = Nat.card α := by
  unfold ENat.card
  apply symm
  rw [Cardinal.natCast_eq_toENat]
  exact Nat.cast_card

end ENat

namespace Set

/--
theorem `card_union_le` / 定理 `card_union_le`

English:
theorem card_union_le
  given: (s t : Set α)
  statement: Nat.card (↥(s union t)) <= Nat.card s + Nat.card t
  proof: by
  rcases _root_.finite_or_infinite (↥(s union t)) with h | h
  · rw [finite_coe_iff, finite_union, ← finite_coe_iff, ← finite_coe_iff] at h
    cases h
    rw [← @Nat.cast_le Cardinal]; rw [Nat.cast_add]; rw [Nat.cast_card]; rw [Nat.cast_card]; rw [Nat.cast_card]
    exact Cardinal.mk_union_le s 

中文:
定理 card_union_le
  条件: (s t : 集合 α)
  结论: 自然数.card (↥(s union t)) <= 自然数.card s + 自然数.card t
  证明: by
  rcases _root_.finite_or_infinite (↥(s union t)) with h | h
  · rw [finite_coe_iff, finite_union, ← finite_coe_iff, ← finite_coe_iff] at h
    cases h
    rw [← @Nat.cast_le Cardinal]; rw [Nat.cast_add]; rw [Nat.cast_card]; rw [Nat.cast_card]; rw [Nat.cast_card]
    exact Cardinal.mk_union_le s 

Depends on / 依赖: Cardinal, Cardinal.mk_union_le, Nat.cast_add, Nat.cast_card, Nat.cast_le, _root_, _root_.finite_or_infinite, cast_add, cast_card, cast_le, finite_coe_iff, finite_or_infinite, finite_union, mk_union_le
-/
theorem card_union_le (s t : Set α) : Nat.card (↥(s union t)) <= Nat.card s + Nat.card t := by
  rcases _root_.finite_or_infinite (↥(s union t)) with h | h
  · rw [finite_coe_iff, finite_union, ← finite_coe_iff, ← finite_coe_iff] at h
    cases h
    rw [← @Nat.cast_le Cardinal]; rw [Nat.cast_add]; rw [Nat.cast_card]; rw [Nat.cast_card]; rw [Nat.cast_card]
    exact Cardinal.mk_union_le s t
  · simp

namespace Finite

variable {s t : Set α}

/--
theorem `card_lt_card` / 定理 `card_lt_card`

English:
theorem card_lt_card
  given: (ht : t.Finite) (hsub : s ⊂ t)
  statement: Nat.card s < Nat.card t
  proof: by
  have : Fintype t := Finite.fintype ht
  have : Fintype s := Finite.fintype (subset ht (subset_of_ssubset hsub))
  simp only [Nat.card_eq_fintype_card]
  exact Set.card_lt_card hsub

中文:
定理 card_lt_card
  条件: (ht : t.有限) (hsub : s ⊂ t)
  结论: 自然数.card s < 自然数.card t
  证明: by
  have : Fintype t := Finite.fintype ht
  have : Fintype s := Finite.fintype (subset ht (subset_of_ssubset hsub))
  simp only [Nat.card_eq_fintype_card]
  exact Set.card_lt_card hsub

Depends on / 依赖: Finite, Finite.fintype, Fintype, Nat.card_eq_fintype_card, Set.card_lt_card, card_eq_fintype_card, card_lt_card, fintype, subset, subset_of_ssubset
-/
theorem card_lt_card (ht : t.Finite) (hsub : s ⊂ t) : Nat.card s < Nat.card t := by
  have : Fintype t := Finite.fintype ht
  have : Fintype s := Finite.fintype (subset ht (subset_of_ssubset hsub))
  simp only [Nat.card_eq_fintype_card]
  exact Set.card_lt_card hsub

/--
theorem `_root_.Set.ecard_le_ecard` / 定理 `_root_.Set.ecard_le_ecard`

English:
theorem _root_.Set.ecard_le_ecard
  given: (hsub : s subseteq t)
  statement: ENat.card s <= ENat.card t
  proof: ENat.card_le_card_of_injective inclusion_injective hsub

中文:
定理 _root_.集合.ecard_le_ecard
  条件: (hsub : s subseteq t)
  结论: E自然数.card s <= E自然数.card t
  证明: ENat.card_le_card_of_injective inclusion_injective hsub

Depends on / 依赖: ENat.card_le_card_of_injective, card_le_card_of_injective, inclusion_injective
-/
theorem _root_.Set.ecard_le_ecard (hsub : s subseteq t) : ENat.card s <= ENat.card t :=
ENat.card_le_card_of_injective inclusion_injective hsub

/--
theorem `ecard_lt_ecard` / 定理 `ecard_lt_ecard`

English:
theorem ecard_lt_ecard
  given: (hs : s.Finite) (hsub : s ⊂ t)
  statement: ENat.card s < ENat.card t
  proof: by
  classical
  suffices ENat.card t <= ENat.card s -> t subseteq s from
lt_of_le_not_ge (ecard_le_ecard hsub.subset) fun hle => not_subset_of_ssubset hsub this hle
  intro hle
  suffices ENat.card ↑(t \ s) <= 0 by
    rwa [← sdiff_eq_empty, ← Set.isEmpty_coe_sort, ← ENat.card_eq_zero_iff_empty,
  

中文:
定理 ecard_lt_ecard
  条件: (hs : s.有限) (hsub : s ⊂ t)
  结论: E自然数.card s < E自然数.card t
  证明: by
  classical
  suffices ENat.card t <= ENat.card s -> t subseteq s from
lt_of_le_not_ge (ecard_le_ecard hsub.subset) fun hle => not_subset_of_ssubset hsub this hle
  intro hle
  suffices ENat.card ↑(t \ s) <= 0 by
    rwa [← sdiff_eq_empty, ← Set.isEmpty_coe_sort, ← ENat.card_eq_zero_iff_empty,
  

Depends on / 依赖: ENat.ca, ENat.card, ENat.card_eq_zero_iff_empty, ENat.card_lt_top.mpr, Set.isEmpty_coe_sort, WithTop, WithTop.le_of_add_le_add_right, card_eq_zero_iff_empty, card_lt_top, classical, ecard_le_ecard, hsub.subset, isEmpty_coe_sort, le_of_add_le_add_right, lt_of_le_not_ge, nonpos_iff_eq_zero, not_subset_of_ssubset, sdiff_eq_empty, subset, subseteq
-/
theorem ecard_lt_ecard (hs : s.Finite) (hsub : s ⊂ t) : ENat.card s < ENat.card t := by
  classical
  suffices ENat.card t <= ENat.card s -> t subseteq s from
lt_of_le_not_ge (ecard_le_ecard hsub.subset) fun hle => not_subset_of_ssubset hsub this hle
  intro hle
  suffices ENat.card ↑(t \ s) <= 0 by
    rwa [← sdiff_eq_empty, ← Set.isEmpty_coe_sort, ← ENat.card_eq_zero_iff_empty,
      ← nonpos_iff_eq_zero]
  suffices ENat.card ↑(t \ s) + ENat.card ↑s <= 0 + ENat.card ↑s from
    WithTop.le_of_add_le_add_right (ENat.card_lt_top.mpr hs).ne this
  suffices ENat.card ↑t <= 0 + ENat.card ↑s by
    rwa [← ENat.card_sum, ← ENat.card_congr <| Equiv.Set.union disjoint_sdiff_left,
      sdiff_union_of_subset hsub.subset]
  exact le_add_of_le_right hle

/--
theorem `card_strictMonoOn` / 定理 `card_strictMonoOn`

English:
theorem card_strictMonoOn
  statement: StrictMonoOn (α := Set α) (Nat.card ∘ (↑)) (Set.ofPred Set.Finite)
  proof: fun _ _ _ => card_lt_card

中文:
定理 card_strictMonoOn
  结论: StrictMonoOn (α := 集合 α) (自然数.card ∘ (↑)) (集合.ofPred 集合.有限)
  证明: fun _ _ _ => card_lt_card

Depends on / 依赖: Finite, Nat.card, Set.Finite, Set.ofPred, ofPred
-/
theorem card_strictMonoOn : StrictMonoOn (α := Set α) (Nat.card ∘ (↑)) (Set.ofPred Set.Finite) :=
  fun _ _ _ => card_lt_card

/--
theorem `ecard_strictMonoOn` / 定理 `ecard_strictMonoOn`

English:
theorem ecard_strictMonoOn
  statement: StrictMonoOn (α := Set α) (ENat.card ∘ (↑)) (Set.ofPred Set.Finite)
  proof: fun _ hs _ _ => hs.ecard_lt_ecard

中文:
定理 ecard_strictMonoOn
  结论: StrictMonoOn (α := 集合 α) (E自然数.card ∘ (↑)) (集合.ofPred 集合.有限)
  证明: fun _ hs _ _ => hs.ecard_lt_ecard

Depends on / 依赖: ENat.card, Finite, Set.Finite, Set.ofPred, ofPred
-/
theorem ecard_strictMonoOn : StrictMonoOn (α := Set α) (ENat.card ∘ (↑)) (Set.ofPred Set.Finite) :=
  fun _ hs _ _ => hs.ecard_lt_ecard

/--
theorem `eq_of_subset_of_card_le` / 定理 `eq_of_subset_of_card_le`

English:
theorem eq_of_subset_of_card_le
  given: (ht : t.Finite) (hsub : s subseteq t) (hcard : Nat.card t <= Nat.card s)
  proof: (eq_or_ssubset_of_subset hsub).elim id fun h => absurd hcard not_le_of_gt ht.card_lt_card h

中文:
定理 eq_of_subset_of_card_le
  条件: (ht : t.有限) (hsub : s subseteq t) (hcard : 自然数.card t <= 自然数.card s)
  证明: (eq_or_ssubset_of_subset hsub).elim id fun h => absurd hcard not_le_of_gt ht.card_lt_card h

Depends on / 依赖: absurd, card_lt_card, eq_or_ssubset_of_subset, ht.card_lt_card, not_le_of_gt
-/
theorem eq_of_subset_of_card_le (ht : t.Finite) (hsub : s subseteq t) (hcard : Nat.card t <= Nat.card s) :
    s = t :=
(eq_or_ssubset_of_subset hsub).elim id fun h => absurd hcard not_le_of_gt ht.card_lt_card h

/--
theorem `equiv_image_eq_iff_subset` / 定理 `equiv_image_eq_iff_subset`

English:
theorem equiv_image_eq_iff_subset
  given: (e : α ≃ α) (hs : s.Finite)
  statement: e '' s = s ↔ e '' s subseteq s
  proof: ⟨fun h => by rw [h], fun h => hs.eq_of_subset_of_card_le h
    ge_of_eq (Nat.card_congr (e.image s).symm)⟩

中文:
定理 equiv_image_eq_iff_subset
  条件: (e : α ≃ α) (hs : s.有限)
  结论: e '' s = s ↔ e '' s subseteq s
  证明: ⟨fun h => by rw [h], fun h => hs.eq_of_subset_of_card_le h
    ge_of_eq (Nat.card_congr (e.image s).symm)⟩

Depends on / 依赖: Nat.card_congr, card_congr, e.image, eq_of_subset_of_card_le, ge_of_eq, hs.eq_of_subset_of_card_le
-/
theorem equiv_image_eq_iff_subset (e : α ≃ α) (hs : s.Finite) : e '' s = s ↔ e '' s subseteq s :=
⟨fun h => by rw [h], fun h => hs.eq_of_subset_of_card_le h
    ge_of_eq (Nat.card_congr (e.image s).symm)⟩

end Finite

/--
theorem `card_strictMono` / 定理 `card_strictMono`

English:
theorem card_strictMono
  given: [Finite α]
  statement: StrictMono (α := Set α) (Nat.card ∘ (↑))
  proof: fun _ t => t.toFinite.card_lt_card

中文:
定理 card_strictMono
  条件: [有限 α]
  结论: 严格递增 (α := 集合 α) (自然数.card ∘ (↑))
  证明: fun _ t => t.toFinite.card_lt_card

Depends on / 依赖: Nat.card
-/
theorem card_strictMono [Finite α] : StrictMono (α := Set α) (Nat.card ∘ (↑)) :=
  fun _ t => t.toFinite.card_lt_card

/--
theorem `ecard_strictMono` / 定理 `ecard_strictMono`

English:
theorem ecard_strictMono
  given: [Finite α]
  statement: StrictMono (α := Set α) (ENat.card ∘ (↑))
  proof: fun s _ => s.toFinite.ecard_lt_ecard

中文:
定理 ecard_strictMono
  条件: [有限 α]
  结论: 严格递增 (α := 集合 α) (E自然数.card ∘ (↑))
  证明: fun s _ => s.toFinite.ecard_lt_ecard

Depends on / 依赖: ENat.card
-/
theorem ecard_strictMono [Finite α] : StrictMono (α := Set α) (ENat.card ∘ (↑)) :=
  fun s _ => s.toFinite.ecard_lt_ecard

/--
theorem `eq_top_of_card_le_of_finite` / 定理 `eq_top_of_card_le_of_finite`

English:
theorem eq_top_of_card_le_of_finite
  given: [Finite α] {s : Set α} (h : Nat.card α <= Nat.card s)
  statement: s = ⊤
  proof: Set.Finite.eq_of_subset_of_card_le univ.toFinite (subset_univ s)
    Nat.card_congr (Equiv.Set.univ α) ▸ h

中文:
定理 eq_top_of_card_le_of_finite
  条件: [有限 α] {s : 集合 α} (h : 自然数.card α <= 自然数.card s)
  结论: s = ⊤
  证明: Set.Finite.eq_of_subset_of_card_le univ.toFinite (subset_univ s)
    Nat.card_congr (Equiv.Set.univ α) ▸ h

Depends on / 依赖: Equiv.Set.univ, Finite, Nat.card_congr, Set.Finite.eq_of_subset_of_card_le, card_congr, eq_of_subset_of_card_le, subset_univ, toFinite, univ.toFinite
-/
theorem eq_top_of_card_le_of_finite [Finite α] {s : Set α} (h : Nat.card α <= Nat.card s) : s = ⊤ :=
Set.Finite.eq_of_subset_of_card_le univ.toFinite (subset_univ s)
    Nat.card_congr (Equiv.Set.univ α) ▸ h

end Set

namespace List.Nodup

variable {l : List α} (h : l.Nodup)
include h

/--
theorem `length_le_natCard` / 定理 `length_le_natCard`

English:
theorem length_le_natCard
  given: [Finite α]
  statement: l.length <= Nat.card α
  proof: by
  have := Fintype.ofFinite α
  grw [h.length_le_card, Fintype.card_eq_nat_card]

中文:
定理 length_le_natCard
  条件: [有限 α]
  结论: l.length <= 自然数.card α
  证明: by
  have := Fintype.ofFinite α
  grw [h.length_le_card, Fintype.card_eq_nat_card]

Depends on / 依赖: Fintype, Fintype.card_eq_nat_card, Fintype.ofFinite, card_eq_nat_card, h.length_le_card, length_le_card, ofFinite
-/
theorem length_le_natCard [Finite α] : l.length <= Nat.card α := by
  have := Fintype.ofFinite α
  grw [h.length_le_card, Fintype.card_eq_nat_card]

/--
theorem `length_le_enatCard` / 定理 `length_le_enatCard`

English:
theorem length_le_enatCard
  statement: l.length <= ENat.card α
  proof: by
  cases finite_or_infinite α
  · grw [h.length_le_natCard, ENat.card_eq_coe_natCard]
  · grw [ENat.card_eq_top_of_infinite]
    exact le_top

中文:
定理 length_le_enatCard
  结论: l.length <= E自然数.card α
  证明: by
  cases finite_or_infinite α
  · grw [h.length_le_natCard, ENat.card_eq_coe_natCard]
  · grw [ENat.card_eq_top_of_infinite]
    exact le_top

Depends on / 依赖: ENat.card_eq_coe_natCard, ENat.card_eq_top_of_infinite, card_eq_coe_natCard, card_eq_top_of_infinite, finite_or_infinite, h.length_le_natCard, le_top, length_le_natCard
-/
theorem length_le_enatCard : l.length <= ENat.card α := by
  cases finite_or_infinite α
  · grw [h.length_le_natCard, ENat.card_eq_coe_natCard]
  · grw [ENat.card_eq_top_of_infinite]
    exact le_top

end List.Nodup
