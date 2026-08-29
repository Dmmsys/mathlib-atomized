/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Data.ENat.Pow
public import Mathlib.Data.ULift
public import Mathlib.Data.ZMod.Defs
public import Mathlib.SetTheory.Cardinal.ToNat
public import Mathlib.SetTheory.Cardinal.ENat

/-!
# Finite Cardinality Functions

## Main Definitions

* `Nat.card α` is the cardinality of `α` as a natural number.
  If `α` is infinite, `Nat.card α = 0`.
* `ENat.card α` is the cardinality of `α` as an extended natural number.
  If `α` is infinite, `ENat.card α = ⊤`.
-/

@[expose] public section

assert_not_exists Field

open Cardinal Function

noncomputable section

variable {α β : Type*}

universe u v

namespace Nat

/--
Definition of `card` / `card` 的定义

English:
definition card
  signature: (α : Type*)
  body: toNat (mk α)

@[simp]

中文:
定义 card
  签名: (α : 类型)
  定义体: toNat (mk α)

@[simp]
-/
protected def card (α : Type*) : Nat :=
  toNat (mk α)

@[simp]
/--
theorem `card_eq_fintype_card` / 定理 `card_eq_fintype_card`

English:
theorem card_eq_fintype_card
  given: [Fintype α]
  statement: Nat.card α = Fintype.card α
  proof: mk_toNat_eq_card

中文:
定理 card_eq_fintype_card
  条件: [Fintype α]
  结论: 自然数.card α = Fintype.card α
  证明: mk_toNat_eq_card

Depends on / 依赖: mk_toNat_eq_card
-/
theorem card_eq_fintype_card [Fintype α] : Nat.card α = Fintype.card α :=
  mk_toNat_eq_card

/--
theorem `_root_.Fintype.card_eq_nat_card` / 定理 `_root_.Fintype.card_eq_nat_card`

English:
theorem _root_.Fintype.card_eq_nat_card
  given: {_ : Fintype α}
  statement: Fintype.card α = Nat.card α
  proof: mk_toNat_eq_card.symm

中文:
定理 _root_.Fintype.card_eq_nat_card
  条件: {_ : Fintype α}
  结论: Fintype.card α = 自然数.card α
  证明: mk_toNat_eq_card.symm

Depends on / 依赖: mk_toNat_eq_card, mk_toNat_eq_card.symm
-/
theorem _root_.Fintype.card_eq_nat_card {_ : Fintype α} : Fintype.card α = Nat.card α :=
  mk_toNat_eq_card.symm

/--
lemma `card_eq_finsetCard` / 引理 `card_eq_finsetCard`

English:
lemma card_eq_finsetCard
  given: (s : Finset α)
  statement: Nat.card s = s.card
  proof: by
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe]

中文:
引理 card_eq_finsetCard
  条件: (s : Finset α)
  结论: 自然数.card s = s.card
  证明: by
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe]

Depends on / 依赖: Fintype, Fintype.card_coe, Nat.card_eq_fintype_card, card_coe, card_eq_fintype_card
-/
lemma card_eq_finsetCard (s : Finset α) : Nat.card s = s.card := by
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe]

/--
lemma `card_eq_card_toFinset` / 引理 `card_eq_card_toFinset`

English:
lemma card_eq_card_toFinset
  given: (s : Set α) [Fintype s]
  statement: Nat.card s = s.toFinset.card
  proof: by
  simp only [← Nat.card_eq_finsetCard, s.mem_toFinset]

中文:
引理 card_eq_card_toFinset
  条件: (s : Set α) [Fintype s]
  结论: 自然数.card s = s.toFinset.card
  证明: by
  simp only [← Nat.card_eq_finsetCard, s.mem_toFinset]

Depends on / 依赖: Nat.card_eq_finsetCard, card_eq_finsetCard, mem_toFinset, s.mem_toFinset
-/
lemma card_eq_card_toFinset (s : Set α) [Fintype s] : Nat.card s = s.toFinset.card := by
  simp only [← Nat.card_eq_finsetCard, s.mem_toFinset]

/--
lemma `card_eq_card_finite_toFinset` / 引理 `card_eq_card_finite_toFinset`

English:
lemma card_eq_card_finite_toFinset
  given: {s : Set α} (hs : s.Finite)
  statement: Nat.card s = hs.toFinset.card
  proof: by
  simp only [← Nat.card_eq_finsetCard, hs.mem_toFinset]

中文:
引理 card_eq_card_finite_toFinset
  条件: {s : Set α} (hs : s.Finite)
  结论: 自然数.card s = hs.toFinset.card
  证明: by
  simp only [← Nat.card_eq_finsetCard, hs.mem_toFinset]

Depends on / 依赖: Nat.card_eq_finsetCard, card_eq_finsetCard, hs.mem_toFinset, mem_toFinset
-/
lemma card_eq_card_finite_toFinset {s : Set α} (hs : s.Finite) : Nat.card s = hs.toFinset.card := by
  simp only [← Nat.card_eq_finsetCard, hs.mem_toFinset]

/--
theorem `subtype_card` / 定理 `subtype_card`

English:
theorem subtype_card
  given: {p : α -> Prop} (s : Finset α) (H : forall x : α, x in s ↔ p x)
  proof: by
  rw [← Fintype.subtype_card s H]; rw [Fintype.card_eq_nat_card]

中文:
定理 subtype_card
  条件: {p : α -> 命题} (s : Finset α) (H : 对任意 x : α, x in s ↔ p x)
  证明: by
  rw [← Fintype.subtype_card s H]; rw [Fintype.card_eq_nat_card]

Depends on / 依赖: Fintype, Fintype.card_eq_nat_card, Fintype.subtype_card, card_eq_nat_card, subtype_card
-/
theorem subtype_card {p : α -> Prop} (s : Finset α) (H : forall x : α, x in s ↔ p x) :
    Nat.card { x // p x } = Finset.card s := by
  rw [← Fintype.subtype_card s H]; rw [Fintype.card_eq_nat_card]

/--
theorem `card_of_isEmpty` / 定理 `card_of_isEmpty`

English:
theorem card_of_isEmpty
  given: [IsEmpty α]
  statement: Nat.card α = 0
  proof: by simp [Nat.card]

中文:
定理 card_of_isEmpty
  条件: [IsEmpty α]
  结论: 自然数.card α = 0
  证明: by simp [Nat.card]
-/
@[simp] theorem card_of_isEmpty [IsEmpty α] : Nat.card α = 0 := by simp [Nat.card]

/--
lemma `card_eq_zero_of_infinite` / 引理 `card_eq_zero_of_infinite`

English:
lemma card_eq_zero_of_infinite
  given: [Infinite α]
  statement: Nat.card α = 0
  proof: mk_toNat_of_infinite

中文:
引理 card_eq_zero_of_infinite
  条件: [Infinite α]
  结论: 自然数.card α = 0
  证明: mk_toNat_of_infinite
-/
@[simp] lemma card_eq_zero_of_infinite [Infinite α] : Nat.card α = 0 := mk_toNat_of_infinite

/--
lemma `cast_card` / 引理 `cast_card`

English:
lemma cast_card
  given: [Finite α]
  statement: (Nat.card α : Cardinal) = Cardinal.mk α
  proof: by
  rw [Nat.card]; rw [Cardinal.cast_toNat_of_lt_aleph0]
  exact Cardinal.lt_aleph0_of_finite _

中文:
引理 cast_card
  条件: [Finite α]
  结论: (自然数.card α : Cardinal) = Cardinal.mk α
  证明: by
  rw [Nat.card]; rw [Cardinal.cast_toNat_of_lt_aleph0]
  exact Cardinal.lt_aleph0_of_finite _

Depends on / 依赖: Cardinal, Cardinal.cast_toNat_of_lt_aleph0, Cardinal.lt_aleph0_of_finite, Nat.card, cast_toNat_of_lt_aleph0, lt_aleph0_of_finite
-/
lemma cast_card [Finite α] : (Nat.card α : Cardinal) = Cardinal.mk α := by
  rw [Nat.card]; rw [Cardinal.cast_toNat_of_lt_aleph0]
  exact Cardinal.lt_aleph0_of_finite _

/--
lemma `_root_.Set.Infinite.card_eq_zero` / 引理 `_root_.Set.Infinite.card_eq_zero`

English:
lemma _root_.Set.Infinite.card_eq_zero
  given: {s : Set α} (hs : s.Infinite)
  statement: Nat.card s = 0
  proof: @card_eq_zero_of_infinite _ hs.to_subtype

中文:
引理 _root_.Set.Infinite.card_eq_zero
  条件: {s : Set α} (hs : s.Infinite)
  结论: 自然数.card s = 0
  证明: @card_eq_zero_of_infinite _ hs.to_subtype

Depends on / 依赖: card_eq_zero_of_infinite, hs.to_subtype, to_subtype
-/
lemma _root_.Set.Infinite.card_eq_zero {s : Set α} (hs : s.Infinite) : Nat.card s = 0 :=
  @card_eq_zero_of_infinite _ hs.to_subtype

/--
lemma `card_eq_zero` / 引理 `card_eq_zero`

English:
lemma card_eq_zero
  statement: Nat.card α = 0 ↔ IsEmpty α ∨ Infinite α
  proof: by
  simp [Nat.card, mk_eq_zero_iff, aleph0_le_mk_iff]

中文:
引理 card_eq_zero
  结论: 自然数.card α = 0 ↔ IsEmpty α ∨ Infinite α
  证明: by
  simp [Nat.card, mk_eq_zero_iff, aleph0_le_mk_iff]

Depends on / 依赖: Nat.card, aleph0_le_mk_iff, mk_eq_zero_iff
-/
lemma card_eq_zero : Nat.card α = 0 ↔ IsEmpty α ∨ Infinite α := by
  simp [Nat.card, mk_eq_zero_iff, aleph0_le_mk_iff]

/--
lemma `card_ne_zero` / 引理 `card_ne_zero`

English:
lemma card_ne_zero
  statement: Nat.card α != 0 ↔ Nonempty α ∧ Finite α
  proof: by simp [card_eq_zero, not_or]

中文:
引理 card_ne_zero
  结论: 自然数.card α != 0 ↔ Nonempty α ∧ Finite α
  证明: by simp [card_eq_zero, not_or]

Depends on / 依赖: card_eq_zero, not_or
-/
lemma card_ne_zero : Nat.card α != 0 ↔ Nonempty α ∧ Finite α := by simp [card_eq_zero, not_or]

/--
lemma `card_pos_iff` / 引理 `card_pos_iff`

English:
lemma card_pos_iff
  statement: 0 < Nat.card α ↔ Nonempty α ∧ Finite α
  proof: by
  simp [Nat.card, mk_eq_zero_iff, mk_lt_aleph0_iff]

中文:
引理 card_pos_iff
  结论: 0 < 自然数.card α ↔ Nonempty α ∧ Finite α
  证明: by
  simp [Nat.card, mk_eq_zero_iff, mk_lt_aleph0_iff]

Depends on / 依赖: Nat.card, mk_eq_zero_iff, mk_lt_aleph0_iff
-/
lemma card_pos_iff : 0 < Nat.card α ↔ Nonempty α ∧ Finite α := by
  simp [Nat.card, mk_eq_zero_iff, mk_lt_aleph0_iff]

/--
lemma `card_pos` / 引理 `card_pos`

English:
lemma card_pos
  given: [Nonempty α] [Finite α]
  statement: 0 < Nat.card α
  proof: card_pos_iff.2 ⟨‹_›, ‹_›⟩

中文:
引理 card_pos
  条件: [Nonempty α] [Finite α]
  结论: 0 < 自然数.card α
  证明: card_pos_iff.2 ⟨‹_›, ‹_›⟩
-/
@[simp] lemma card_pos [Nonempty α] [Finite α] : 0 < Nat.card α := card_pos_iff.2 ⟨‹_›, ‹_›⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: α] [Finite α] : NeZero (Nat.card α)
  body: ⟨card_pos.ne'⟩

中文:
实例 [Nonempty
  签名: α] [Finite α] : NeZero (自然数.card α)
  定义体: ⟨card_pos.ne'⟩

Depends on / 依赖: card_pos, card_pos.ne
-/
instance [Nonempty α] [Finite α] : NeZero (Nat.card α) := ⟨card_pos.ne'⟩

/--
theorem `finite_of_card_ne_zero` / 定理 `finite_of_card_ne_zero`

English:
theorem finite_of_card_ne_zero
  given: (h : Nat.card α != 0)
  statement: Finite α
  proof: (card_ne_zero.1 h).2

中文:
定理 finite_of_card_ne_zero
  条件: (h : 自然数.card α != 0)
  结论: Finite α
  证明: (card_ne_zero.1 h).2

Depends on / 依赖: card_ne_zero
-/
theorem finite_of_card_ne_zero (h : Nat.card α != 0) : Finite α := (card_ne_zero.1 h).2

/--
theorem `card_congr` / 定理 `card_congr`

English:
theorem card_congr
  given: (f : α ≃ β)
  statement: Nat.card α = Nat.card β
  proof: Cardinal.toNat_congr f

中文:
定理 card_congr
  条件: (f : α ≃ β)
  结论: 自然数.card α = 自然数.card β
  证明: Cardinal.toNat_congr f

Depends on / 依赖: Cardinal, Cardinal.toNat_congr, toNat_congr
-/
theorem card_congr (f : α ≃ β) : Nat.card α = Nat.card β :=
  Cardinal.toNat_congr f

/--
lemma `card_le_card_of_injective` / 引理 `card_le_card_of_injective`

English:
lemma card_le_card_of_injective
  statement: {α : Type u} {β : Type v} [Finite β] (f : α -> β)
  proof: by
  simpa using! toNat_le_toNat (lift_mk_le_lift_mk_of_injective hf) (by simp)

中文:
引理 card_le_card_of_injective
  结论: {α : 类型u} {β : 类型v} [Finite β] (f : α -> β)
  证明: by
  simpa using! toNat_le_toNat (lift_mk_le_lift_mk_of_injective hf) (by simp)

Depends on / 依赖: lift_mk_le_lift_mk_of_injective, toNat_le_toNat
-/
lemma card_le_card_of_injective {α : Type u} {β : Type v} [Finite β] (f : α -> β)
    (hf : Injective f) : Nat.card α <= Nat.card β := by
  simpa using! toNat_le_toNat (lift_mk_le_lift_mk_of_injective hf) (by simp)

/--
lemma `card_le_card_of_surjective` / 引理 `card_le_card_of_surjective`

English:
lemma card_le_card_of_surjective
  statement: {α : Type u} {β : Type v} [Finite α] (f : α -> β)
  proof: by
  have : lift.{u} #β <= lift.{v} #α := mk_le_of_surjective (ULift.map_surjective.2 hf)
  simpa using! toNat_le_toNat this (by simp)

中文:
引理 card_le_card_of_surjective
  结论: {α : 类型u} {β : 类型v} [Finite α] (f : α -> β)
  证明: by
  have : lift.{u} #β <= lift.{v} #α := mk_le_of_surjective (ULift.map_surjective.2 hf)
  simpa using! toNat_le_toNat this (by simp)

Depends on / 依赖: ULift.map_surjective, map_surjective, mk_le_of_surjective, toNat_le_toNat
-/
lemma card_le_card_of_surjective {α : Type u} {β : Type v} [Finite α] (f : α -> β)
    (hf : Surjective f) : Nat.card β <= Nat.card α := by
  have : lift.{u} #β <= lift.{v} #α := mk_le_of_surjective (ULift.map_surjective.2 hf)
  simpa using! toNat_le_toNat this (by simp)

/--
theorem `card_eq_of_bijective` / 定理 `card_eq_of_bijective`

English:
theorem card_eq_of_bijective
  given: (f : α -> β) (hf : Function.Bijective f)
  statement: Nat.card α = Nat.card β
  proof: card_congr (Equiv.ofBijective f hf)

中文:
定理 card_eq_of_bijective
  条件: (f : α -> β) (hf : Function.Bijective f)
  结论: 自然数.card α = 自然数.card β
  证明: card_congr (Equiv.ofBijective f hf)

Depends on / 依赖: Equiv.ofBijective, card_congr, ofBijective
-/
theorem card_eq_of_bijective (f : α -> β) (hf : Function.Bijective f) : Nat.card α = Nat.card β :=
  card_congr (Equiv.ofBijective f hf)

/--
theorem `bijective_iff_injective_and_card` / 定理 `bijective_iff_injective_and_card`

English:
theorem bijective_iff_injective_and_card
  given: [Finite β] (f : α -> β)
  proof: by
  rw [Bijective]; rw [and_congr_right_iff]
  intro h
  have := Fintype.ofFinite β
  have := Fintype.ofInjective f h
  revert h
  rw [← and_congr_right_iff]; rw [← Bijective]; rw [card_eq_fintype_card]; rw [card_eq_fintype_card]; rw [Fintype.bijective_iff_injective_and_card]

中文:
定理 bijective_iff_injective_and_card
  条件: [Finite β] (f : α -> β)
  证明: by
  rw [Bijective]; rw [and_congr_right_iff]
  intro h
  have := Fintype.ofFinite β
  have := Fintype.ofInjective f h
  revert h
  rw [← and_congr_right_iff]; rw [← Bijective]; rw [card_eq_fintype_card]; rw [card_eq_fintype_card]; rw [Fintype.bijective_iff_injective_and_card]
-/
protected theorem bijective_iff_injective_and_card [Finite β] (f : α -> β) :
    Bijective f ↔ Injective f ∧ Nat.card α = Nat.card β := by
  rw [Bijective]; rw [and_congr_right_iff]
  intro h
  have := Fintype.ofFinite β
  have := Fintype.ofInjective f h
  revert h
  rw [← and_congr_right_iff]; rw [← Bijective]; rw [card_eq_fintype_card]; rw [card_eq_fintype_card]; rw [Fintype.bijective_iff_injective_and_card]

/--
theorem `bijective_iff_surjective_and_card` / 定理 `bijective_iff_surjective_and_card`

English:
theorem bijective_iff_surjective_and_card
  given: [Finite α] (f : α -> β)
  proof: by
  classical
  rw [_root_.and_comm]; rw [Bijective]; rw [and_congr_left_iff]
  intro h
  have := Fintype.ofFinite α
  have := Fintype.ofSurjective f h
  revert h
  rw [← and_congr_left_iff]; rw [← Bijective]; rw [← and_comm]; rw [card_eq_fintype_card]; rw [card_eq_fintype_card]; rw [Fintype.biject

中文:
定理 bijective_iff_surjective_and_card
  条件: [Finite α] (f : α -> β)
  证明: by
  classical
  rw [_root_.and_comm]; rw [Bijective]; rw [and_congr_left_iff]
  intro h
  have := Fintype.ofFinite α
  have := Fintype.ofSurjective f h
  revert h
  rw [← and_congr_left_iff]; rw [← Bijective]; rw [← and_comm]; rw [card_eq_fintype_card]; rw [card_eq_fintype_card]; rw [Fintype.biject
-/
protected theorem bijective_iff_surjective_and_card [Finite α] (f : α -> β) :
    Bijective f ↔ Surjective f ∧ Nat.card α = Nat.card β := by
  classical
  rw [_root_.and_comm]; rw [Bijective]; rw [and_congr_left_iff]
  intro h
  have := Fintype.ofFinite α
  have := Fintype.ofSurjective f h
  revert h
  rw [← and_congr_left_iff]; rw [← Bijective]; rw [← and_comm]; rw [card_eq_fintype_card]; rw [card_eq_fintype_card]; rw [Fintype.bijective_iff_surjective_and_card]

/--
theorem `_root_.Function.Injective.bijective_of_nat_card_le` / 定理 `_root_.Function.Injective.bijective_of_nat_card_le`

English:
theorem _root_.Function.Injective.bijective_of_nat_card_le
  statement: [Finite β] {f : α -> β}
  proof: (Nat.bijective_iff_injective_and_card f).mpr
.symm⟩ ⟨inj, hc.antisymm (card_le_card_of_injective f inj)

中文:
定理 _root_.Function.Injective.bijective_of_nat_card_le
  结论: [Finite β] {f : α -> β}
  证明: (Nat.bijective_iff_injective_and_card f).mpr
.symm⟩ ⟨inj, hc.antisymm (card_le_card_of_injective f inj)

Depends on / 依赖: Nat.bijective_iff_injective_and_card, antisymm, bijective_iff_injective_and_card, card_le_card_of_injective, hc.antisymm
-/
theorem _root_.Function.Injective.bijective_of_nat_card_le [Finite β] {f : α -> β}
    (inj : Injective f) (hc : Nat.card β <= Nat.card α) : Bijective f :=
  (Nat.bijective_iff_injective_and_card f).mpr
.symm⟩ ⟨inj, hc.antisymm (card_le_card_of_injective f inj)

/--
theorem `_root_.Function.Surjective.bijective_of_nat_card_le` / 定理 `_root_.Function.Surjective.bijective_of_nat_card_le`

English:
theorem _root_.Function.Surjective.bijective_of_nat_card_le
  statement: [Finite α] {f : α -> β}
  proof: (Nat.bijective_iff_surjective_and_card f).mpr
    ⟨surj, hc.antisymm (card_le_card_of_surjective f surj)⟩

中文:
定理 _root_.Function.Surjective.bijective_of_nat_card_le
  结论: [Finite α] {f : α -> β}
  证明: (Nat.bijective_iff_surjective_and_card f).mpr
    ⟨surj, hc.antisymm (card_le_card_of_surjective f surj)⟩

Depends on / 依赖: Nat.bijective_iff_surjective_and_card, antisymm, bijective_iff_surjective_and_card, card_le_card_of_surjective, hc.antisymm
-/
theorem _root_.Function.Surjective.bijective_of_nat_card_le [Finite α] {f : α -> β}
    (surj : Surjective f) (hc : Nat.card α <= Nat.card β) : Bijective f :=
  (Nat.bijective_iff_surjective_and_card f).mpr
    ⟨surj, hc.antisymm (card_le_card_of_surjective f surj)⟩

/--
theorem `card_eq_of_equiv_fin` / 定理 `card_eq_of_equiv_fin`

English:
theorem card_eq_of_equiv_fin
  given: {α : Type*} {n : Nat} (f : α ≃ Fin n)
  statement: Nat.card α = n
  proof: by
  simpa only [card_eq_fintype_card, Fintype.card_fin] using card_congr f

中文:
定理 card_eq_of_equiv_fin
  条件: {α : 类型} {n : 自然数} (f : α ≃ Fin n)
  结论: 自然数.card α = n
  证明: by
  simpa only [card_eq_fintype_card, Fintype.card_fin] using card_congr f

Depends on / 依赖: Fintype, Fintype.card_fin, card_congr, card_eq_fintype_card, card_fin
-/
theorem card_eq_of_equiv_fin {α : Type*} {n : Nat} (f : α ≃ Fin n) : Nat.card α = n := by
  simpa only [card_eq_fintype_card, Fintype.card_fin] using card_congr f

/--
lemma `card_fin` / 引理 `card_fin`

English:
lemma card_fin
  given: (n : Nat)
  statement: Nat.card (Fin n) = n
  proof: by
  rw [Nat.card_eq_fintype_card]; rw [Fintype.card_fin]

中文:
引理 card_fin
  条件: (n : 自然数)
  结论: 自然数.card (Fin n) = n
  证明: by
  rw [Nat.card_eq_fintype_card]; rw [Fintype.card_fin]

Depends on / 依赖: Fintype, Fintype.card_fin, Nat.card_eq_fintype_card, card_eq_fintype_card, card_fin
-/
lemma card_fin (n : Nat) : Nat.card (Fin n) = n := by
  rw [Nat.card_eq_fintype_card]; rw [Fintype.card_fin]

section Set
open Set
variable {s t : Set α}

/--
lemma `card_mono` / 引理 `card_mono`

English:
lemma card_mono
  given: (ht : t.Finite) (h : s subseteq t)
  statement: Nat.card s <= Nat.card t
  proof: toNat_le_toNat (mk_le_mk_of_subset h) ht.lt_aleph0

中文:
引理 card_mono
  条件: (ht : t.Finite) (h : s subseteq t)
  结论: 自然数.card s <= 自然数.card t
  证明: toNat_le_toNat (mk_le_mk_of_subset h) ht.lt_aleph0

Depends on / 依赖: ht.lt_aleph0, lt_aleph0, mk_le_mk_of_subset, toNat_le_toNat
-/
lemma card_mono (ht : t.Finite) (h : s subseteq t) : Nat.card s <= Nat.card t :=
  toNat_le_toNat (mk_le_mk_of_subset h) ht.lt_aleph0

/--
lemma `card_image_le` / 引理 `card_image_le`

English:
lemma card_image_le
  given: {f : α -> β} (hs : s.Finite)
  statement: Nat.card (f '' s) <= Nat.card s
  proof: have := hs.to_subtype
  card_le_card_of_surjective (imageFactorization f s) imageFactorization_surjective

中文:
引理 card_image_le
  条件: {f : α -> β} (hs : s.Finite)
  结论: 自然数.card (f '' s) <= 自然数.card s
  证明: have := hs.to_subtype
  card_le_card_of_surjective (imageFactorization f s) imageFactorization_surjective

Depends on / 依赖: card_le_card_of_surjective, hs.to_subtype, imageFactorization, imageFactorization_surjective, to_subtype
-/
lemma card_image_le {f : α -> β} (hs : s.Finite) : Nat.card (f '' s) <= Nat.card s :=
  have := hs.to_subtype
  card_le_card_of_surjective (imageFactorization f s) imageFactorization_surjective

/--
lemma `card_image_of_injOn` / 引理 `card_image_of_injOn`

English:
lemma card_image_of_injOn
  given: {f : α -> β} (hf : s.InjOn f)
  statement: Nat.card (f '' s) = Nat.card s
  proof: by
  classical
  obtain hs | hs := s.finite_or_infinite
  · have := hs.fintype
    simp_rw [Nat.card_eq_fintype_card, Set.card_image_of_inj_on hf]
  · have := hs.to_subtype
    have := (hs.image hf).to_subtype
    simp [Nat.card_eq_zero_of_infinite]

中文:
引理 card_image_of_injOn
  条件: {f : α -> β} (hf : s.InjOn f)
  结论: 自然数.card (f '' s) = 自然数.card s
  证明: by
  classical
  obtain hs | hs := s.finite_or_infinite
  · have := hs.fintype
    simp_rw [Nat.card_eq_fintype_card, Set.card_image_of_inj_on hf]
  · have := hs.to_subtype
    have := (hs.image hf).to_subtype
    simp [Nat.card_eq_zero_of_infinite]

Depends on / 依赖: Nat.card_eq_fintype_card, Nat.card_eq_zero_of_infinite, Set.card_image_of_inj_on, card_eq_fintype_card, card_eq_zero_of_infinite, card_image_of_inj_on, classical, finite_or_infinite, fintype, hs.fintype, hs.image, hs.to_subtype, s.finite_or_infinite, simp_rw, to_subtype
-/
lemma card_image_of_injOn {f : α -> β} (hf : s.InjOn f) : Nat.card (f '' s) = Nat.card s := by
  classical
  obtain hs | hs := s.finite_or_infinite
  · have := hs.fintype
    simp_rw [Nat.card_eq_fintype_card, Set.card_image_of_inj_on hf]
  · have := hs.to_subtype
    have := (hs.image hf).to_subtype
    simp [Nat.card_eq_zero_of_infinite]

/--
lemma `card_image_of_injective` / 引理 `card_image_of_injective`

English:
lemma card_image_of_injective
  given: {f : α -> β} (hf : Injective f) (s : Set α)
  proof: card_image_of_injOn hf.injOn

中文:
引理 card_image_of_injective
  条件: {f : α -> β} (hf : Injective f) (s : Set α)
  证明: card_image_of_injOn hf.injOn

Depends on / 依赖: card_image_of_injOn, hf.injOn
-/
lemma card_image_of_injective {f : α -> β} (hf : Injective f) (s : Set α) :
    Nat.card (f '' s) = Nat.card s := card_image_of_injOn hf.injOn

/--
lemma `card_image_equiv` / 引理 `card_image_equiv`

English:
lemma card_image_equiv
  given: (e : α ≃ β)
  statement: Nat.card (e '' s) = Nat.card s
  proof: Nat.card_congr (e.image s).symm

中文:
引理 card_image_equiv
  条件: (e : α ≃ β)
  结论: 自然数.card (e '' s) = 自然数.card s
  证明: Nat.card_congr (e.image s).symm

Depends on / 依赖: Nat.card_congr, card_congr, e.image
-/
lemma card_image_equiv (e : α ≃ β) : Nat.card (e '' s) = Nat.card s :=
    Nat.card_congr (e.image s).symm

/--
lemma `card_preimage_of_injOn` / 引理 `card_preimage_of_injOn`

English:
lemma card_preimage_of_injOn
  given: {f : α -> β} {s : Set β} (hf : (f ⁻¹' s).InjOn f) (hsf : s subseteq range f)
  proof: by
  rw [← Nat.card_image_of_injOn hf]; rw [image_preimage_eq_iff.2 hsf]

中文:
引理 card_preimage_of_injOn
  条件: {f : α -> β} {s : Set β} (hf : (f ⁻¹' s).InjOn f) (hsf : s subseteq range f)
  证明: by
  rw [← Nat.card_image_of_injOn hf]; rw [image_preimage_eq_iff.2 hsf]

Depends on / 依赖: Nat.card_image_of_injOn, card_image_of_injOn, image_preimage_eq_iff
-/
lemma card_preimage_of_injOn {f : α -> β} {s : Set β} (hf : (f ⁻¹' s).InjOn f) (hsf : s subseteq range f) :
    Nat.card (f ⁻¹' s) = Nat.card s := by
  rw [← Nat.card_image_of_injOn hf]; rw [image_preimage_eq_iff.2 hsf]

/--
lemma `card_preimage_of_injective` / 引理 `card_preimage_of_injective`

English:
lemma card_preimage_of_injective
  given: {f : α -> β} {s : Set β} (hf : Injective f) (hsf : s subseteq range f)
  proof: card_preimage_of_injOn hf.injOn hsf

中文:
引理 card_preimage_of_injective
  条件: {f : α -> β} {s : Set β} (hf : Injective f) (hsf : s subseteq range f)
  证明: card_preimage_of_injOn hf.injOn hsf

Depends on / 依赖: card_preimage_of_injOn, hf.injOn
-/
lemma card_preimage_of_injective {f : α -> β} {s : Set β} (hf : Injective f) (hsf : s subseteq range f) :
    Nat.card (f ⁻¹' s) = Nat.card s := card_preimage_of_injOn hf.injOn hsf

/--
lemma `card_univ` / 引理 `card_univ`

English:
lemma card_univ
  statement: Nat.card (univ : Set α) = Nat.card α
  proof: card_congr (Equiv.Set.univ α)

中文:
引理 card_univ
  结论: 自然数.card (univ : Set α) = 自然数.card α
  证明: card_congr (Equiv.Set.univ α)

Depends on / 依赖: Equiv.Set.univ, card_congr
-/
lemma card_univ : Nat.card (univ : Set α) = Nat.card α :=
  card_congr (Equiv.Set.univ α)

/--
lemma `card_range_of_injective` / 引理 `card_range_of_injective`

English:
lemma card_range_of_injective
  given: {f : α -> β} (hf : Injective f)
  proof: by
  rw [← Nat.card_preimage_of_injective hf le_rfl]
  simp [Nat.card_univ]

中文:
引理 card_range_of_injective
  条件: {f : α -> β} (hf : Injective f)
  证明: by
  rw [← Nat.card_preimage_of_injective hf le_rfl]
  simp [Nat.card_univ]

Depends on / 依赖: Nat.card_preimage_of_injective, Nat.card_univ, card_preimage_of_injective, card_univ, le_rfl
-/
lemma card_range_of_injective {f : α -> β} (hf : Injective f) :
    Nat.card (range f) = Nat.card α := by
  rw [← Nat.card_preimage_of_injective hf le_rfl]
  simp [Nat.card_univ]

end Set

/--
Definition of `equivFinOfCardPos` / `equivFinOfCardPos` 的定义

English:
definition equivFinOfCardPos
  signature: {α : Type*} (h : Nat.card α != 0)
  body: by
  cases fintypeOrInfinite α
  · simpa only [card_eq_fintype_card] using Fintype.equivFin α
  · simp only [card_eq_zero_of_infinite, ne_eq, not_true_eq_false] at h

中文:
定义 equivFinOfCardPos
  签名: {α : 类型} (h : 自然数.card α != 0)
  定义体: by
  cases fintypeOrInfinite α
  · simpa only [card_eq_fintype_card] using Fintype.equivFin α
  · simp only [card_eq_zero_of_infinite, ne_eq, not_true_eq_false] at h

Depends on / 依赖: Fintype, Fintype.equivFin, card_eq_fintype_card, card_eq_zero_of_infinite, equivFin, fintypeOrInfinite, ne_eq, not_true_eq_false
-/
def equivFinOfCardPos {α : Type*} (h : Nat.card α != 0) : α ≃ Fin (Nat.card α) := by
  cases fintypeOrInfinite α
  · simpa only [card_eq_fintype_card] using Fintype.equivFin α
  · simp only [card_eq_zero_of_infinite, ne_eq, not_true_eq_false] at h

/--
theorem `card_of_subsingleton` / 定理 `card_of_subsingleton`

English:
theorem card_of_subsingleton
  given: (a : α) [Subsingleton α]
  statement: Nat.card α = 1
  proof: by
  let := Fintype.ofSubsingleton a
  rw [card_eq_fintype_card]; rw [Fintype.card_ofSubsingleton a]

中文:
定理 card_of_subsingleton
  条件: (a : α) [Subsingleton α]
  结论: 自然数.card α = 1
  证明: by
  let := Fintype.ofSubsingleton a
  rw [card_eq_fintype_card]; rw [Fintype.card_ofSubsingleton a]

Depends on / 依赖: Fintype, Fintype.card_ofSubsingleton, Fintype.ofSubsingleton, card_eq_fintype_card, card_ofSubsingleton, ofSubsingleton
-/
theorem card_of_subsingleton (a : α) [Subsingleton α] : Nat.card α = 1 := by
  let := Fintype.ofSubsingleton a
  rw [card_eq_fintype_card]; rw [Fintype.card_ofSubsingleton a]

/--
theorem `card_eq_one_iff_unique` / 定理 `card_eq_one_iff_unique`

English:
theorem card_eq_one_iff_unique
  statement: Nat.card α = 1 ↔ Subsingleton α ∧ Nonempty α
  proof: Cardinal.toNat_eq_one_iff_unique

@[simp]

中文:
定理 card_eq_one_iff_unique
  结论: 自然数.card α = 1 ↔ Subsingleton α ∧ Nonempty α
  证明: Cardinal.toNat_eq_one_iff_unique

@[simp]

Depends on / 依赖: Cardinal, Cardinal.toNat_eq_one_iff_unique, toNat_eq_one_iff_unique
-/
theorem card_eq_one_iff_unique : Nat.card α = 1 ↔ Subsingleton α ∧ Nonempty α :=
  Cardinal.toNat_eq_one_iff_unique

@[simp]
/--
theorem `card_unique` / 定理 `card_unique`

English:
theorem card_unique
  given: [Nonempty α] [Subsingleton α]
  statement: Nat.card α = 1
  proof: by
  simp [card_eq_one_iff_unique, *]

中文:
定理 card_unique
  条件: [Nonempty α] [Subsingleton α]
  结论: 自然数.card α = 1
  证明: by
  simp [card_eq_one_iff_unique, *]

Depends on / 依赖: card_eq_one_iff_unique
-/
theorem card_unique [Nonempty α] [Subsingleton α] : Nat.card α = 1 := by
  simp [card_eq_one_iff_unique, *]

/--
theorem `card_eq_one_iff_exists` / 定理 `card_eq_one_iff_exists`

English:
theorem card_eq_one_iff_exists
  statement: Nat.card α = 1 ↔ exists x : α, forall y : α, y = x
  proof: by
  rw [card_eq_one_iff_unique]
  exact ⟨fun ⟨s, ⟨a⟩⟩ => ⟨a, fun x => s.elim x a⟩, fun ⟨x, h⟩ => ⟨subsingleton_of_forall_eq x h, ⟨x⟩⟩⟩

中文:
定理 card_eq_one_iff_exists
  结论: 自然数.card α = 1 ↔ 存在 x : α, 对任意 y : α, y = x
  证明: by
  rw [card_eq_one_iff_unique]
  exact ⟨fun ⟨s, ⟨a⟩⟩ => ⟨a, fun x => s.elim x a⟩, fun ⟨x, h⟩ => ⟨subsingleton_of_forall_eq x h, ⟨x⟩⟩⟩

Depends on / 依赖: card_eq_one_iff_unique, s.elim, subsingleton_of_forall_eq
-/
theorem card_eq_one_iff_exists : Nat.card α = 1 ↔ exists x : α, forall y : α, y = x := by
  rw [card_eq_one_iff_unique]
  exact ⟨fun ⟨s, ⟨a⟩⟩ => ⟨a, fun x => s.elim x a⟩, fun ⟨x, h⟩ => ⟨subsingleton_of_forall_eq x h, ⟨x⟩⟩⟩

/--
theorem `card_eq_two_iff` / 定理 `card_eq_two_iff`

English:
theorem card_eq_two_iff
  statement: Nat.card α = 2 ↔ exists x y : α, x != y ∧ {x, y} = @Set.univ α
  proof: toNat_eq_ofNat.trans mk_eq_two_iff

中文:
定理 card_eq_two_iff
  结论: 自然数.card α = 2 ↔ 存在 x y : α, x != y ∧ {x, y} = @Set.univ α
  证明: toNat_eq_ofNat.trans mk_eq_two_iff

Depends on / 依赖: mk_eq_two_iff, toNat_eq_ofNat, toNat_eq_ofNat.trans
-/
theorem card_eq_two_iff : Nat.card α = 2 ↔ exists x y : α, x != y ∧ {x, y} = @Set.univ α :=
  toNat_eq_ofNat.trans mk_eq_two_iff

/--
theorem `card_eq_two_iff'` / 定理 `card_eq_two_iff'`

English:
theorem card_eq_two_iff'
  given: (x : α)
  statement: Nat.card α = 2 ↔ exists! y, y != x
  proof: toNat_eq_ofNat.trans (mk_eq_two_iff' x)

@[simp]

中文:
定理 card_eq_two_iff'
  条件: (x : α)
  结论: 自然数.card α = 2 ↔ 存在! y, y != x
  证明: toNat_eq_ofNat.trans (mk_eq_two_iff' x)

@[simp]

Depends on / 依赖: mk_eq_two_iff, toNat_eq_ofNat, toNat_eq_ofNat.trans
-/
theorem card_eq_two_iff' (x : α) : Nat.card α = 2 ↔ exists! y, y != x :=
  toNat_eq_ofNat.trans (mk_eq_two_iff' x)

@[simp]
/--
theorem `card_subtype_true` / 定理 `card_subtype_true`

English:
theorem card_subtype_true
  statement: Nat.card {_a : α // True} = Nat.card α
  proof: card_congr Equiv.subtypeUnivEquiv fun _ => trivial

@[simp]

中文:
定理 card_subtype_true
  结论: 自然数.card {_a : α // True} = 自然数.card α
  证明: card_congr Equiv.subtypeUnivEquiv fun _ => trivial

@[simp]

Depends on / 依赖: Equiv.subtypeUnivEquiv, card_congr, subtypeUnivEquiv
-/
theorem card_subtype_true : Nat.card {_a : α // True} = Nat.card α :=
card_congr Equiv.subtypeUnivEquiv fun _ => trivial

@[simp]
/--
theorem `card_sum` / 定理 `card_sum`

English:
theorem card_sum
  given: [Finite α] [Finite β]
  statement: Nat.card (α oplus β) = Nat.card α + Nat.card β
  proof: by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  simp_rw [Nat.card_eq_fintype_card, Fintype.card_sum]

@[simp]

中文:
定理 card_sum
  条件: [Finite α] [Finite β]
  结论: 自然数.card (α oplus β) = 自然数.card α + 自然数.card β
  证明: by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  simp_rw [Nat.card_eq_fintype_card, Fintype.card_sum]

@[simp]

Depends on / 依赖: Fintype, Fintype.card_sum, Fintype.ofFinite, Nat.card_eq_fintype_card, card_eq_fintype_card, card_sum, ofFinite, simp_rw
-/
theorem card_sum [Finite α] [Finite β] : Nat.card (α oplus β) = Nat.card α + Nat.card β := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  simp_rw [Nat.card_eq_fintype_card, Fintype.card_sum]

@[simp]
/--
theorem `card_prod` / 定理 `card_prod`

English:
theorem card_prod
  given: (α β : Type*)
  statement: Nat.card (α × β) = Nat.card α * Nat.card β
  proof: by
  simp only [Nat.card, mk_prod, toNat_mul, toNat_lift]

@[simp]

中文:
定理 card_prod
  条件: (α β : 类型)
  结论: 自然数.card (α × β) = 自然数.card α * 自然数.card β
  证明: by
  simp only [Nat.card, mk_prod, toNat_mul, toNat_lift]

@[simp]

Depends on / 依赖: Nat.card, mk_prod, toNat_lift, toNat_mul
-/
theorem card_prod (α β : Type*) : Nat.card (α × β) = Nat.card α * Nat.card β := by
  simp only [Nat.card, mk_prod, toNat_mul, toNat_lift]

@[simp]
/--
theorem `card_ulift` / 定理 `card_ulift`

English:
theorem card_ulift
  given: (α : Type*)
  statement: Nat.card (ULift α) = Nat.card α
  proof: card_congr Equiv.ulift

@[simp]

中文:
定理 card_ulift
  条件: (α : 类型)
  结论: 自然数.card (ULift α) = 自然数.card α
  证明: card_congr Equiv.ulift

@[simp]

Depends on / 依赖: Equiv.ulift, card_congr
-/
theorem card_ulift (α : Type*) : Nat.card (ULift α) = Nat.card α :=
  card_congr Equiv.ulift

@[simp]
/--
theorem `card_plift` / 定理 `card_plift`

English:
theorem card_plift
  given: (α : Type*)
  statement: Nat.card (PLift α) = Nat.card α
  proof: card_congr Equiv.plift

中文:
定理 card_plift
  条件: (α : 类型)
  结论: 自然数.card (PLift α) = 自然数.card α
  证明: card_congr Equiv.plift

Depends on / 依赖: Equiv.plift, card_congr
-/
theorem card_plift (α : Type*) : Nat.card (PLift α) = Nat.card α :=
  card_congr Equiv.plift

/--
theorem `card_sigma` / 定理 `card_sigma`

English:
theorem card_sigma
  given: {β : α -> Type*} [Fintype α] [forall a, Finite (β a)]
  proof: by
  let _ (a : α) : Fintype (β a) := Fintype.ofFinite (β a)
  simp_rw [Nat.card_eq_fintype_card, Fintype.card_sigma]

中文:
定理 card_sigma
  条件: {β : α -> 类型} [Fintype α] [对任意 a, Finite (β a)]
  证明: by
  let _ (a : α) : Fintype (β a) := Fintype.ofFinite (β a)
  simp_rw [Nat.card_eq_fintype_card, Fintype.card_sigma]

Depends on / 依赖: Fintype, Fintype.card_sigma, Fintype.ofFinite, Nat.card_eq_fintype_card, card_eq_fintype_card, card_sigma, ofFinite, simp_rw
-/
theorem card_sigma {β : α -> Type*} [Fintype α] [forall a, Finite (β a)] :
    Nat.card (Sigma β) = ∑ a, Nat.card (β a) := by
  let _ (a : α) : Fintype (β a) := Fintype.ofFinite (β a)
  simp_rw [Nat.card_eq_fintype_card, Fintype.card_sigma]

/--
theorem `card_pi` / 定理 `card_pi`

English:
theorem card_pi
  given: {β : α -> Type*} [Fintype α]
  statement: Nat.card (forall a, β a) = ∏ a, Nat.card (β a)
  proof: by
  simp_rw [Nat.card, mk_pi, prod_eq_of_fintype, toNat_lift, _root_.map_prod]

中文:
定理 card_pi
  条件: {β : α -> 类型} [Fintype α]
  结论: 自然数.card (对任意 a, β a) = ∏ a, 自然数.card (β a)
  证明: by
  simp_rw [Nat.card, mk_pi, prod_eq_of_fintype, toNat_lift, _root_.map_prod]

Depends on / 依赖: Nat.card, _root_, _root_.map_prod, map_prod, mk_pi, prod_eq_of_fintype, simp_rw, toNat_lift
-/
theorem card_pi {β : α -> Type*} [Fintype α] : Nat.card (forall a, β a) = ∏ a, Nat.card (β a) := by
  simp_rw [Nat.card, mk_pi, prod_eq_of_fintype, toNat_lift, _root_.map_prod]

/--
theorem `card_fun` / 定理 `card_fun`

English:
theorem card_fun
  given: [Finite α]
  statement: Nat.card (α -> β) = Nat.card β ^ Nat.card α
  proof: by
  have := Fintype.ofFinite α
  rw [Nat.card_pi]; rw [Finset.prod_const]; rw [Finset.card_univ]; rw [← Nat.card_eq_fintype_card]

@[simp]

中文:
定理 card_fun
  条件: [Finite α]
  结论: 自然数.card (α -> β) = 自然数.card β ^ 自然数.card α
  证明: by
  have := Fintype.ofFinite α
  rw [Nat.card_pi]; rw [Finset.prod_const]; rw [Finset.card_univ]; rw [← Nat.card_eq_fintype_card]

@[simp]

Depends on / 依赖: Finset, Finset.card_univ, Finset.prod_const, Fintype, Fintype.ofFinite, Nat.card_eq_fintype_card, Nat.card_pi, card_eq_fintype_card, card_pi, card_univ, ofFinite, prod_const
-/
theorem card_fun [Finite α] : Nat.card (α -> β) = Nat.card β ^ Nat.card α := by
  have := Fintype.ofFinite α
  rw [Nat.card_pi]; rw [Finset.prod_const]; rw [Finset.card_univ]; rw [← Nat.card_eq_fintype_card]

@[simp]
/--
theorem `card_zmod` / 定理 `card_zmod`

English:
theorem card_zmod
  given: (n : Nat)
  statement: Nat.card (ZMod n) = n
  proof: by
  cases n
  · exact @Nat.card_eq_zero_of_infinite _ Int.infinite
  · rw [Nat.card_eq_fintype_card, ZMod.card]

中文:
定理 card_zmod
  条件: (n : 自然数)
  结论: 自然数.card (ZMod n) = n
  证明: by
  cases n
  · exact @Nat.card_eq_zero_of_infinite _ Int.infinite
  · rw [Nat.card_eq_fintype_card, ZMod.card]

Depends on / 依赖: Int.infinite, Nat.card_eq_fintype_card, Nat.card_eq_zero_of_infinite, ZMod.card, card_eq_fintype_card, card_eq_zero_of_infinite, infinite
-/
theorem card_zmod (n : Nat) : Nat.card (ZMod n) = n := by
  cases n
  · exact @Nat.card_eq_zero_of_infinite _ Int.infinite
  · rw [Nat.card_eq_fintype_card, ZMod.card]

end Nat

namespace Set
variable {s : Set α}

/--
lemma `card_singleton_prod` / 引理 `card_singleton_prod`

English:
lemma card_singleton_prod
  given: (a : α) (t : Set β)
  statement: Nat.card ({a} ×ˢ t) = Nat.card t
  proof: by
  rw [singleton_prod]; rw [Nat.card_image_of_injective (Prod.mk_right_injective a)]

中文:
引理 card_singleton_prod
  条件: (a : α) (t : Set β)
  结论: 自然数.card ({a} ×ˢ t) = 自然数.card t
  证明: by
  rw [singleton_prod]; rw [Nat.card_image_of_injective (Prod.mk_right_injective a)]

Depends on / 依赖: Nat.card_image_of_injective, Prod.mk_right_injective, card_image_of_injective, mk_right_injective, singleton_prod
-/
lemma card_singleton_prod (a : α) (t : Set β) : Nat.card ({a} ×ˢ t) = Nat.card t := by
  rw [singleton_prod]; rw [Nat.card_image_of_injective (Prod.mk_right_injective a)]

/--
lemma `card_prod_singleton` / 引理 `card_prod_singleton`

English:
lemma card_prod_singleton
  given: (s : Set α) (b : β)
  statement: Nat.card (s ×ˢ {b}) = Nat.card s
  proof: by
  rw [prod_singleton]; rw [Nat.card_image_of_injective (Prod.mk_left_injective b)]

中文:
引理 card_prod_singleton
  条件: (s : Set α) (b : β)
  结论: 自然数.card (s ×ˢ {b}) = 自然数.card s
  证明: by
  rw [prod_singleton]; rw [Nat.card_image_of_injective (Prod.mk_left_injective b)]

Depends on / 依赖: Nat.card_image_of_injective, Prod.mk_left_injective, card_image_of_injective, mk_left_injective, prod_singleton
-/
lemma card_prod_singleton (s : Set α) (b : β) : Nat.card (s ×ˢ {b}) = Nat.card s := by
  rw [prod_singleton]; rw [Nat.card_image_of_injective (Prod.mk_left_injective b)]

/--
theorem `natCard_pos` / 定理 `natCard_pos`

English:
theorem natCard_pos
  given: (hs : s.Finite)
  statement: 0 < Nat.card s ↔ s.Nonempty
  proof: by
  simp [pos_iff_ne_zero, Nat.card_eq_zero, hs.to_subtype, nonempty_iff_ne_empty]

protected alias ⟨_, Nonempty.natCard_pos⟩ := natCard_pos

中文:
定理 natCard_pos
  条件: (hs : s.Finite)
  结论: 0 < 自然数.card s ↔ s.Nonempty
  证明: by
  simp [pos_iff_ne_zero, Nat.card_eq_zero, hs.to_subtype, nonempty_iff_ne_empty]

protected alias ⟨_, Nonempty.natCard_pos⟩ := natCard_pos

Depends on / 依赖: Nat.card_eq_zero, card_eq_zero, hs.to_subtype, nonempty_iff_ne_empty, pos_iff_ne_zero, to_subtype
-/
theorem natCard_pos (hs : s.Finite) : 0 < Nat.card s ↔ s.Nonempty := by
  simp [pos_iff_ne_zero, Nat.card_eq_zero, hs.to_subtype, nonempty_iff_ne_empty]

protected alias ⟨_, Nonempty.natCard_pos⟩ := natCard_pos

/--
lemma `natCard_graphOn` / 引理 `natCard_graphOn`

English:
lemma natCard_graphOn
  given: (s : Set α) (f : α -> β)
  statement: Nat.card (s.graphOn f) = Nat.card s
  proof: by
  rw [← Nat.card_image_of_injOn fst_injOn_graph]; rw [image_fst_graphOn]

中文:
引理 natCard_graphOn
  条件: (s : Set α) (f : α -> β)
  结论: 自然数.card (s.graphOn f) = 自然数.card s
  证明: by
  rw [← Nat.card_image_of_injOn fst_injOn_graph]; rw [image_fst_graphOn]

Depends on / 依赖: Nat.card_image_of_injOn, card_image_of_injOn, fst_injOn_graph, image_fst_graphOn
-/
lemma natCard_graphOn (s : Set α) (f : α -> β) : Nat.card (s.graphOn f) = Nat.card s := by
  rw [← Nat.card_image_of_injOn fst_injOn_graph]; rw [image_fst_graphOn]

end Set


namespace ENat

/--
Definition of `card` / `card` 的定义

English:
definition card
  signature: (α : Type*)
  body: toENat (mk α)

@[simp]

中文:
定义 card
  签名: (α : 类型)
  定义体: toENat (mk α)

@[simp]

Depends on / 依赖: toENat
-/
def card (α : Type*) : Nat∞ :=
  toENat (mk α)

@[simp]
/--
theorem `card_eq_coe_fintype_card` / 定理 `card_eq_coe_fintype_card`

English:
theorem card_eq_coe_fintype_card
  given: [Fintype α]
  statement: card α = Fintype.card α
  proof: by
  simp [card]

@[simp high]

中文:
定理 card_eq_coe_fintype_card
  条件: [Fintype α]
  结论: card α = Fintype.card α
  证明: by
  simp [card]

@[simp high]
-/
theorem card_eq_coe_fintype_card [Fintype α] : card α = Fintype.card α := by
  simp [card]

@[simp high]
/--
theorem `card_eq_top_of_infinite` / 定理 `card_eq_top_of_infinite`

English:
theorem card_eq_top_of_infinite
  given: [Infinite α]
  statement: card α = ⊤
  proof: by
  simp only [card, toENat_eq_top, aleph0_le_mk]

中文:
定理 card_eq_top_of_infinite
  条件: [Infinite α]
  结论: card α = ⊤
  证明: by
  simp only [card, toENat_eq_top, aleph0_le_mk]

Depends on / 依赖: aleph0_le_mk, toENat_eq_top
-/
theorem card_eq_top_of_infinite [Infinite α] : card α = ⊤ := by
  simp only [card, toENat_eq_top, aleph0_le_mk]

/--
lemma `card_eq_top` / 引理 `card_eq_top`

English:
lemma card_eq_top
  statement: card α = ⊤ ↔ Infinite α
  proof: by simp [card, aleph0_le_mk_iff]

中文:
引理 card_eq_top
  结论: card α = ⊤ ↔ Infinite α
  证明: by simp [card, aleph0_le_mk_iff]
-/
@[simp] lemma card_eq_top : card α = ⊤ ↔ Infinite α := by simp [card, aleph0_le_mk_iff]

/--
theorem `card_lt_top_of_finite` / 定理 `card_lt_top_of_finite`

English:
theorem card_lt_top_of_finite
  given: [Finite α]
  statement: card α < ⊤
  proof: by simp [card]

中文:
定理 card_lt_top_of_finite
  条件: [Finite α]
  结论: card α < ⊤
  证明: by simp [card]
-/
@[simp high] theorem card_lt_top_of_finite [Finite α] : card α < ⊤ := by simp [card]

/--
theorem `card_lt_top` / 定理 `card_lt_top`

English:
theorem card_lt_top
  statement: card α < ⊤ ↔ Finite α
  proof: by simp [card, lt_aleph0_iff_finite]

@[simp]

中文:
定理 card_lt_top
  结论: card α < ⊤ ↔ Finite α
  证明: by simp [card, lt_aleph0_iff_finite]

@[simp]
-/
@[simp] theorem card_lt_top : card α < ⊤ ↔ Finite α := by simp [card, lt_aleph0_iff_finite]

@[simp]
/--
theorem `card_sum` / 定理 `card_sum`

English:
theorem card_sum
  given: (α β : Type*)
  proof: by
  simp only [card, mk_sum, map_add, toENat_lift]

中文:
定理 card_sum
  条件: (α β : 类型)
  证明: by
  simp only [card, mk_sum, map_add, toENat_lift]

Depends on / 依赖: map_add, mk_sum, toENat_lift
-/
theorem card_sum (α β : Type*) :
    card (α oplus β) = card α + card β := by
  simp only [card, mk_sum, map_add, toENat_lift]

/--
theorem `card_congr` / 定理 `card_congr`

English:
theorem card_congr
  given: {α β : Type*} (f : α ≃ β)
  statement: card α = card β
  proof: Cardinal.toENat_congr f

中文:
定理 card_congr
  条件: {α β : 类型} (f : α ≃ β)
  结论: card α = card β
  证明: Cardinal.toENat_congr f

Depends on / 依赖: Cardinal, Cardinal.toENat_congr, toENat_congr
-/
theorem card_congr {α β : Type*} (f : α ≃ β) : card α = card β :=
  Cardinal.toENat_congr f

/--
lemma `card_ulift` / 引理 `card_ulift`

English:
lemma card_ulift
  given: (α : Type*)
  statement: card (ULift α) = card α
  proof: card_congr Equiv.ulift

中文:
引理 card_ulift
  条件: (α : 类型)
  结论: card (ULift α) = card α
  证明: card_congr Equiv.ulift
-/
@[simp] lemma card_ulift (α : Type*) : card (ULift α) = card α := card_congr Equiv.ulift

/--
lemma `card_plift` / 引理 `card_plift`

English:
lemma card_plift
  given: (α : Type*)
  statement: card (PLift α) = card α
  proof: card_congr Equiv.plift

中文:
引理 card_plift
  条件: (α : 类型)
  结论: card (PLift α) = card α
  证明: card_congr Equiv.plift
-/
@[simp] lemma card_plift (α : Type*) : card (PLift α) = card α := card_congr Equiv.plift

/--
theorem `card_image_of_injOn` / 定理 `card_image_of_injOn`

English:
theorem card_image_of_injOn
  given: {α β : Type*} {f : α -> β} {s : Set α} (h : Set.InjOn f s)
  proof: card_congr (Equiv.Set.imageOfInjOn f s h).symm

中文:
定理 card_image_of_injOn
  条件: {α β : 类型} {f : α -> β} {s : Set α} (h : Set.InjOn f s)
  证明: card_congr (Equiv.Set.imageOfInjOn f s h).symm

Depends on / 依赖: Equiv.Set.imageOfInjOn, card_congr, imageOfInjOn
-/
theorem card_image_of_injOn {α β : Type*} {f : α -> β} {s : Set α} (h : Set.InjOn f s) :
    card (f '' s) = card s :=
  card_congr (Equiv.Set.imageOfInjOn f s h).symm

/--
theorem `card_image_of_injective` / 定理 `card_image_of_injective`

English:
theorem card_image_of_injective
  statement: {α β : Type*} (f : α -> β) (s : Set α)
  proof: card_image_of_injOn h.injOn

中文:
定理 card_image_of_injective
  结论: {α β : 类型} (f : α -> β) (s : Set α)
  证明: card_image_of_injOn h.injOn

Depends on / 依赖: card_image_of_injOn, h.injOn
-/
theorem card_image_of_injective {α β : Type*} (f : α -> β) (s : Set α)
    (h : Function.Injective f) : card (f '' s) = card s := card_image_of_injOn h.injOn

/--
lemma `card_le_card_of_injective` / 引理 `card_le_card_of_injective`

English:
lemma card_le_card_of_injective
  given: {α β : Type*} {f : α -> β} (hf : Injective f)
  statement: card α <= card β
  proof: by
  rw [← card_ulift α]; rw [← card_ulift β]
exact Cardinal.gciENat.gc.monotone_u Cardinal.lift_mk_le_lift_mk_of_injective hf

@[deprecated natCast_le_toENat (since := "2026-02-17")]

中文:
引理 card_le_card_of_injective
  条件: {α β : 类型} {f : α -> β} (hf : Injective f)
  结论: card α <= card β
  证明: by
  rw [← card_ulift α]; rw [← card_ulift β]
exact Cardinal.gciENat.gc.monotone_u Cardinal.lift_mk_le_lift_mk_of_injective hf

@[deprecated natCast_le_toENat (since := "2026-02-17")]

Depends on / 依赖: Cardinal, Cardinal.gciENat.gc.monotone_u, Cardinal.lift_mk_le_lift_mk_of_injective, card_ulift, gciENat, lift_mk_le_lift_mk_of_injective, monotone_u
-/
lemma card_le_card_of_injective {α β : Type*} {f : α -> β} (hf : Injective f) : card α <= card β := by
  rw [← card_ulift α]; rw [← card_ulift β]
exact Cardinal.gciENat.gc.monotone_u Cardinal.lift_mk_le_lift_mk_of_injective hf

@[deprecated natCast_le_toENat (since := "2026-02-17")]
/--
theorem `_root_.Cardinal.natCast_le_toENat_iff` / 定理 `_root_.Cardinal.natCast_le_toENat_iff`

English:
theorem _root_.Cardinal.natCast_le_toENat_iff
  given: {n : Nat} {c : Cardinal}
  proof: by
  rw [← toENat_nat n]; rw [toENat_le_iff_of_le_aleph0 natCast_le_aleph0]

@[deprecated toENat_le_natCast (since := "2026-02-17")]

中文:
定理 _root_.Cardinal.natCast_le_toENat_iff
  条件: {n : 自然数} {c : Cardinal}
  证明: by
  rw [← toENat_nat n]; rw [toENat_le_iff_of_le_aleph0 natCast_le_aleph0]

@[deprecated toENat_le_natCast (since := "2026-02-17")]

Depends on / 依赖: natCast_le_aleph0, toENat_le_iff_of_le_aleph0, toENat_nat
-/
theorem _root_.Cardinal.natCast_le_toENat_iff {n : Nat} {c : Cardinal} :
    ↑n <= toENat c ↔ ↑n <= c := by
  rw [← toENat_nat n]; rw [toENat_le_iff_of_le_aleph0 natCast_le_aleph0]

@[deprecated toENat_le_natCast (since := "2026-02-17")]
/--
theorem `_root_.Cardinal.toENat_le_natCast_iff` / 定理 `_root_.Cardinal.toENat_le_natCast_iff`

English:
theorem _root_.Cardinal.toENat_le_natCast_iff
  given: {c : Cardinal} {n : Nat}
  proof: by simp

@[deprecated natCast_eq_toENat (since := "2026-02-17")]

中文:
定理 _root_.Cardinal.toENat_le_natCast_iff
  条件: {c : Cardinal} {n : 自然数}
  证明: by simp

@[deprecated natCast_eq_toENat (since := "2026-02-17")]
-/
theorem _root_.Cardinal.toENat_le_natCast_iff {c : Cardinal} {n : Nat} :
    toENat c <= n ↔ c <= n := by simp

@[deprecated natCast_eq_toENat (since := "2026-02-17")]
/--
theorem `_root_.Cardinal.natCast_eq_toENat_iff` / 定理 `_root_.Cardinal.natCast_eq_toENat_iff`

English:
theorem _root_.Cardinal.natCast_eq_toENat_iff
  given: {n : Nat} {c : Cardinal}
  proof: by
  rw [le_antisymm_iff]; rw [le_antisymm_iff]; rw [Cardinal.toENat_le_natCast]; rw [Cardinal.natCast_le_toENat]

@[deprecated toENat_eq_natCast (since := "2026-02-17")]

中文:
定理 _root_.Cardinal.natCast_eq_toENat_iff
  条件: {n : 自然数} {c : Cardinal}
  证明: by
  rw [le_antisymm_iff]; rw [le_antisymm_iff]; rw [Cardinal.toENat_le_natCast]; rw [Cardinal.natCast_le_toENat]

@[deprecated toENat_eq_natCast (since := "2026-02-17")]

Depends on / 依赖: Cardinal, Cardinal.natCast_le_toENat, Cardinal.toENat_le_natCast, le_antisymm_iff, natCast_le_toENat, toENat_le_natCast
-/
theorem _root_.Cardinal.natCast_eq_toENat_iff {n : Nat} {c : Cardinal} :
    ↑n = toENat c ↔ ↑n = c := by
  rw [le_antisymm_iff]; rw [le_antisymm_iff]; rw [Cardinal.toENat_le_natCast]; rw [Cardinal.natCast_le_toENat]

@[deprecated toENat_eq_natCast (since := "2026-02-17")]
/--
theorem `_root_.Cardinal.toENat_eq_natCast_iff` / 定理 `_root_.Cardinal.toENat_eq_natCast_iff`

English:
theorem _root_.Cardinal.toENat_eq_natCast_iff
  given: {c : Cardinal} {n : Nat}
  proof: by simp

@[deprecated natCast_lt_toENat (since := "2026-02-17")]

中文:
定理 _root_.Cardinal.toENat_eq_natCast_iff
  条件: {c : Cardinal} {n : 自然数}
  证明: by simp

@[deprecated natCast_lt_toENat (since := "2026-02-17")]
-/
theorem _root_.Cardinal.toENat_eq_natCast_iff {c : Cardinal} {n : Nat} :
    Cardinal.toENat c = n ↔ c = n := by simp

@[deprecated natCast_lt_toENat (since := "2026-02-17")]
/--
theorem `_root_.Cardinal.natCast_lt_toENat_iff` / 定理 `_root_.Cardinal.natCast_lt_toENat_iff`

English:
theorem _root_.Cardinal.natCast_lt_toENat_iff
  given: {n : Nat} {c : Cardinal}
  proof: by
  simp only [← not_le, Cardinal.toENat_le_natCast]

@[deprecated toENat_lt_natCast (since := "2026-02-17")]

中文:
定理 _root_.Cardinal.natCast_lt_toENat_iff
  条件: {n : 自然数} {c : Cardinal}
  证明: by
  simp only [← not_le, Cardinal.toENat_le_natCast]

@[deprecated toENat_lt_natCast (since := "2026-02-17")]

Depends on / 依赖: Cardinal, Cardinal.toENat_le_natCast, not_le, toENat_le_natCast
-/
theorem _root_.Cardinal.natCast_lt_toENat_iff {n : Nat} {c : Cardinal} :
    ↑n < toENat c ↔ ↑n < c := by
  simp only [← not_le, Cardinal.toENat_le_natCast]

@[deprecated toENat_lt_natCast (since := "2026-02-17")]
/--
theorem `_root_.Cardinal.toENat_lt_natCast_iff` / 定理 `_root_.Cardinal.toENat_lt_natCast_iff`

English:
theorem _root_.Cardinal.toENat_lt_natCast_iff
  given: {n : Nat} {c : Cardinal}
  proof: by
  simp only [← not_le, Cardinal.natCast_le_toENat]

中文:
定理 _root_.Cardinal.toENat_lt_natCast_iff
  条件: {n : 自然数} {c : Cardinal}
  证明: by
  simp only [← not_le, Cardinal.natCast_le_toENat]

Depends on / 依赖: Cardinal, Cardinal.natCast_le_toENat, natCast_le_toENat, not_le
-/
theorem _root_.Cardinal.toENat_lt_natCast_iff {n : Nat} {c : Cardinal} :
    toENat c < ↑n ↔ c < ↑n := by
  simp only [← not_le, Cardinal.natCast_le_toENat]

/--
theorem `card_eq_zero_iff_empty` / 定理 `card_eq_zero_iff_empty`

English:
theorem card_eq_zero_iff_empty
  given: (α : Type*)
  statement: card α = 0 ↔ IsEmpty α
  proof: by
  rw [← Cardinal.mk_eq_zero_iff]
  simp [card]

中文:
定理 card_eq_zero_iff_empty
  条件: (α : 类型)
  结论: card α = 0 ↔ IsEmpty α
  证明: by
  rw [← Cardinal.mk_eq_zero_iff]
  simp [card]

Depends on / 依赖: Cardinal, Cardinal.mk_eq_zero_iff, mk_eq_zero_iff
-/
theorem card_eq_zero_iff_empty (α : Type*) : card α = 0 ↔ IsEmpty α := by
  rw [← Cardinal.mk_eq_zero_iff]
  simp [card]

/--
theorem `card_ne_zero_iff_nonempty` / 定理 `card_ne_zero_iff_nonempty`

English:
theorem card_ne_zero_iff_nonempty
  given: (α : Type*)
  statement: card α != 0 ↔ Nonempty α
  proof: by
  simp [card_eq_zero_iff_empty]

中文:
定理 card_ne_zero_iff_nonempty
  条件: (α : 类型)
  结论: card α != 0 ↔ Nonempty α
  证明: by
  simp [card_eq_zero_iff_empty]

Depends on / 依赖: card_eq_zero_iff_empty
-/
theorem card_ne_zero_iff_nonempty (α : Type*) : card α != 0 ↔ Nonempty α := by
  simp [card_eq_zero_iff_empty]

/--
lemma `card_ne_zero` / 引理 `card_ne_zero`

English:
lemma card_ne_zero
  given: [Nonempty α]
  statement: card α != 0
  proof: (card_ne_zero_iff_nonempty _).2 ‹_›

中文:
引理 card_ne_zero
  条件: [Nonempty α]
  结论: card α != 0
  证明: (card_ne_zero_iff_nonempty _).2 ‹_›
-/
@[simp] lemma card_ne_zero [Nonempty α] : card α != 0 := (card_ne_zero_iff_nonempty _).2 ‹_›

/--
theorem `card_pos_iff_nonempty` / 定理 `card_pos_iff_nonempty`

English:
theorem card_pos_iff_nonempty
  given: (α : Type*)
  statement: 0 < card α ↔ Nonempty α
  proof: by
  rw [pos_iff_ne_zero]; rw [card_ne_zero_iff_nonempty]

中文:
定理 card_pos_iff_nonempty
  条件: (α : 类型)
  结论: 0 < card α ↔ Nonempty α
  证明: by
  rw [pos_iff_ne_zero]; rw [card_ne_zero_iff_nonempty]

Depends on / 依赖: card_ne_zero_iff_nonempty, pos_iff_ne_zero
-/
theorem card_pos_iff_nonempty (α : Type*) : 0 < card α ↔ Nonempty α := by
  rw [pos_iff_ne_zero]; rw [card_ne_zero_iff_nonempty]

/--
theorem `one_le_card_iff_nonempty` / 定理 `one_le_card_iff_nonempty`

English:
theorem one_le_card_iff_nonempty
  given: (α : Type*)
  statement: 1 <= card α ↔ Nonempty α
  proof: by
  simp [Order.one_le_iff_ne_zero, card_eq_zero_iff_empty]

中文:
定理 one_le_card_iff_nonempty
  条件: (α : 类型)
  结论: 1 <= card α ↔ Nonempty α
  证明: by
  simp [Order.one_le_iff_ne_zero, card_eq_zero_iff_empty]

Depends on / 依赖: Order.one_le_iff_ne_zero, card_eq_zero_iff_empty, one_le_iff_ne_zero
-/
theorem one_le_card_iff_nonempty (α : Type*) : 1 <= card α ↔ Nonempty α := by
  simp [Order.one_le_iff_ne_zero, card_eq_zero_iff_empty]

/--
lemma `card_pos` / 引理 `card_pos`

English:
lemma card_pos
  given: [Nonempty α]
  statement: 0 < card α
  proof: by simp [pos_iff_ne_zero]

中文:
引理 card_pos
  条件: [Nonempty α]
  结论: 0 < card α
  证明: by simp [pos_iff_ne_zero]
-/
@[simp] lemma card_pos [Nonempty α] : 0 < card α := by simp [pos_iff_ne_zero]

/--
theorem `card_le_one_iff_subsingleton` / 定理 `card_le_one_iff_subsingleton`

English:
theorem card_le_one_iff_subsingleton
  given: (α : Type*)
  statement: card α <= 1 ↔ Subsingleton α
  proof: by
  rw [← le_one_iff_subsingleton]
  simp [card]

中文:
定理 card_le_one_iff_subsingleton
  条件: (α : 类型)
  结论: card α <= 1 ↔ Subsingleton α
  证明: by
  rw [← le_one_iff_subsingleton]
  simp [card]

Depends on / 依赖: le_one_iff_subsingleton
-/
theorem card_le_one_iff_subsingleton (α : Type*) : card α <= 1 ↔ Subsingleton α := by
  rw [← le_one_iff_subsingleton]
  simp [card]

/--
lemma `card_le_one` / 引理 `card_le_one`

English:
lemma card_le_one
  given: [Subsingleton α]
  statement: card α <= 1
  proof: by simpa [card_le_one_iff_subsingleton]

中文:
引理 card_le_one
  条件: [Subsingleton α]
  结论: card α <= 1
  证明: by simpa [card_le_one_iff_subsingleton]
-/
@[simp] lemma card_le_one [Subsingleton α] : card α <= 1 := by simpa [card_le_one_iff_subsingleton]

/--
lemma `card_eq_one_iff_unique` / 引理 `card_eq_one_iff_unique`

English:
lemma card_eq_one_iff_unique
  given: {α : Type*}
  statement: card α = 1 ↔ Nonempty (Unique α)
  proof: by
  rw [unique_iff_subsingleton_and_nonempty α]; rw [le_antisymm_iff]
  exact and_congr (card_le_one_iff_subsingleton α) (one_le_card_iff_nonempty α)

中文:
引理 card_eq_one_iff_unique
  条件: {α : 类型}
  结论: card α = 1 ↔ Nonempty (Unique α)
  证明: by
  rw [unique_iff_subsingleton_and_nonempty α]; rw [le_antisymm_iff]
  exact and_congr (card_le_one_iff_subsingleton α) (one_le_card_iff_nonempty α)

Depends on / 依赖: and_congr, card_le_one_iff_subsingleton, le_antisymm_iff, one_le_card_iff_nonempty, unique_iff_subsingleton_and_nonempty
-/
lemma card_eq_one_iff_unique {α : Type*} : card α = 1 ↔ Nonempty (Unique α) := by
  rw [unique_iff_subsingleton_and_nonempty α]; rw [le_antisymm_iff]
  exact and_congr (card_le_one_iff_subsingleton α) (one_le_card_iff_nonempty α)

/--
theorem `one_lt_card_iff_nontrivial` / 定理 `one_lt_card_iff_nontrivial`

English:
theorem one_lt_card_iff_nontrivial
  given: (α : Type*)
  statement: 1 < card α ↔ Nontrivial α
  proof: by
  rw [← Cardinal.one_lt_iff_nontrivial]
  conv_rhs => rw [← Nat.cast_one]
  rw [← natCast_lt_toENat]
  simp only [ENat.card, Nat.cast_one]

中文:
定理 one_lt_card_iff_nontrivial
  条件: (α : 类型)
  结论: 1 < card α ↔ Nontrivial α
  证明: by
  rw [← Cardinal.one_lt_iff_nontrivial]
  conv_rhs => rw [← Nat.cast_one]
  rw [← natCast_lt_toENat]
  simp only [ENat.card, Nat.cast_one]

Depends on / 依赖: Cardinal, Cardinal.one_lt_iff_nontrivial, ENat.card, Nat.cast_one, cast_one, conv_rhs, natCast_lt_toENat, one_lt_iff_nontrivial
-/
theorem one_lt_card_iff_nontrivial (α : Type*) : 1 < card α ↔ Nontrivial α := by
  rw [← Cardinal.one_lt_iff_nontrivial]
  conv_rhs => rw [← Nat.cast_one]
  rw [← natCast_lt_toENat]
  simp only [ENat.card, Nat.cast_one]

/--
lemma `one_lt_card` / 引理 `one_lt_card`

English:
lemma one_lt_card
  given: [Nontrivial α]
  statement: 1 < card α
  proof: by simpa [one_lt_card_iff_nontrivial]

中文:
引理 one_lt_card
  条件: [Nontrivial α]
  结论: 1 < card α
  证明: by simpa [one_lt_card_iff_nontrivial]
-/
@[simp] lemma one_lt_card [Nontrivial α] : 1 < card α := by simpa [one_lt_card_iff_nontrivial]

/--
lemma `exists_ne_ne_of_three_le` / 引理 `exists_ne_ne_of_three_le`

English:
lemma exists_ne_ne_of_three_le
  given: (h : 3 <= ENat.card α) (x y : α)
  statement: exists z, z != x ∧ z != y
  proof: Cardinal.exists_ne_ne_of_three_le (by simpa [ENat.card] using h) x y

@[simp]

中文:
引理 exists_ne_ne_of_three_le
  条件: (h : 3 <= E自然数.card α) (x y : α)
  结论: 存在 z, z != x ∧ z != y
  证明: Cardinal.exists_ne_ne_of_three_le (by simpa [ENat.card] using h) x y

@[simp]

Depends on / 依赖: Cardinal, Cardinal.exists_ne_ne_of_three_le, ENat.card, exists_ne_ne_of_three_le
-/
lemma exists_ne_ne_of_three_le (h : 3 <= ENat.card α) (x y : α) : exists z, z != x ∧ z != y :=
  Cardinal.exists_ne_ne_of_three_le (by simpa [ENat.card] using h) x y

@[simp]
/--
theorem `card_prod` / 定理 `card_prod`

English:
theorem card_prod
  given: (α β : Type*)
  statement: card (α × β) = card α * card β
  proof: by
  simp [ENat.card]

@[simp]

中文:
定理 card_prod
  条件: (α β : 类型)
  结论: card (α × β) = card α * card β
  证明: by
  simp [ENat.card]

@[simp]

Depends on / 依赖: ENat.card
-/
theorem card_prod (α β : Type*) : card (α × β) = card α * card β := by
  simp [ENat.card]

@[simp]
/--
lemma `card_fun` / 引理 `card_fun`

English:
lemma card_fun
  given: {α β : Type*}
  statement: card (α -> β) = card β ^ card α
  proof: by
  classical
  rcases isEmpty_or_nonempty α with α_emp | α_emp
  · simp [(card_eq_zero_iff_empty α).2 α_emp]
  rcases finite_or_infinite α
  · rcases finite_or_infinite β
    · let := Fintype.ofFinite α
      let := Fintype.ofFinite β
      simp
    · simp only [card_eq_top_of_infinite]
      rw [

中文:
引理 card_fun
  条件: {α β : 类型}
  结论: card (α -> β) = card β ^ card α
  证明: by
  classical
  rcases isEmpty_or_nonempty α with α_emp | α_emp
  · simp [(card_eq_zero_iff_empty α).2 α_emp]
  rcases finite_or_infinite α
  · rcases finite_or_infinite β
    · let := Fintype.ofFinite α
      let := Fintype.ofFinite β
      simp
    · simp only [card_eq_top_of_infinite]
      rw [

Depends on / 依赖: Fintype, Fintype.ofFinite, Order.lt_one_iff, card_eq_top_of_infinite, card_eq_zero_iff_empty, card_ne_zero_iff_nonempty, classical, finite_or_infinite, isEmpty_or_nonempty, lt_one_iff, lt_trichotomy, ofFinite, top_epow
-/
lemma card_fun {α β : Type*} : card (α -> β) = card β ^ card α := by
  classical
  rcases isEmpty_or_nonempty α with α_emp | α_emp
  · simp [(card_eq_zero_iff_empty α).2 α_emp]
  rcases finite_or_infinite α
  · rcases finite_or_infinite β
    · let := Fintype.ofFinite α
      let := Fintype.ofFinite β
      simp
    · simp only [card_eq_top_of_infinite]
      rw [top_epow]
      rwa [card_ne_zero_iff_nonempty]
  · rw [card_eq_top_of_infinite (α := α)]
    rcases lt_trichotomy (card β) 1 with b_0 | b_1 | b_2
    · rw [Order.lt_one_iff, card_eq_zero_iff_empty] at b_0
      rw [(card_eq_zero_iff_empty β).2 b_0]; rw [zero_epow_top]; rw [card_eq_zero_iff_empty]
      simp [b_0]
    · rw [b_1, one_epow]
      apply le_antisymm
      · let := (card_le_one_iff_subsingleton β).1 b_1.le
        exact (card_le_one_iff_subsingleton (α -> β)).2 Pi.instSubsingleton
      · let := (one_le_card_iff_nonempty β).1 b_1.ge
        exact (one_le_card_iff_nonempty (α -> β)).2 Pi.instNonempty
    · rw [epow_top b_2, card_eq_top]
      rw [one_lt_card_iff_nontrivial β] at b_2
      exact Pi.infinite_of_left

end ENat
