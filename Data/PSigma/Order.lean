/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Minchao Wu
-/
module

public import Mathlib.Data.Sigma.Lex
public import Mathlib.Util.Notation3
public import Mathlib.Data.Sigma.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Order.Lex

/-!
# Lexicographic order on a sigma type

This file defines the lexicographic order on `Σₗ' i, α i`. `a` is less than `b` if its summand is
strictly less than the summand of `b` or they are in the same summand and `a` is less than `b`
there.

## Notation
* `Σₗ' i, α i`: Sigma type equipped with the lexicographic order. A type synonym of `Σ' i, α i`.

## See also
Related files are:
* `Data.Finset.Colex`: Colexicographic order on finite sets.
* `Data.List.Lex`: Lexicographic order on lists.
* `Data.Pi.Lex`: Lexicographic order on `Πₗ i, α i`.
* `Data.Sigma.Order`: Lexicographic order on `Σₗ i, α i`. Basically a twin of this file.
* `Data.Prod.Lex`: Lexicographic order on `α × β`.

## TODO
Define the disjoint order on `Σ' i, α i`, where `x ≤ y` only if `x.fst = y.fst`.
Prove that a sigma type is a `NoMaxOrder`, `NoMinOrder`, `DenselyOrdered` when its summands
are.
-/

public section


variable {ι : Type*} {α : ι -> Type*}

namespace PSigma

/-- The notation `Σₗ' i, α i` refers to a sigma type which is locally equipped with the
lexicographic order. -/
-- TODO: make `Lex` be `Sort u -> Sort u` so we can remove `.{_+1, _+1}`
notation3 "Σₗ' " (...) ", " r:(scoped p => _root_.Lex (PSigma.{_ + 1, _ + 1} p)) => r

namespace Lex

/--
Instance `le` / 实例 `le`

English:
instance le
  signature: [LT ι] [forall i, LE (α i)]
  body: ⟨Lex (· < ·) fun _ => (· <= ·)⟩

中文:
实例 le
  签名: [LT ι] [对任意 i, LE (α i)]
  定义体: ⟨Lex (· < ·) fun _ => (· <= ·)⟩
-/
instance le [LT ι] [forall i, LE (α i)] : LE (Σₗ' i, α i) :=
  ⟨Lex (· < ·) fun _ => (· <= ·)⟩

/--
Instance `lt` / 实例 `lt`

English:
instance lt
  signature: [LT ι] [forall i, LT (α i)]
  body: ⟨Lex (· < ·) fun _ => (· < ·)⟩

中文:
实例 lt
  签名: [LT ι] [对任意 i, LT (α i)]
  定义体: ⟨Lex (· < ·) fun _ => (· < ·)⟩
-/
instance lt [LT ι] [forall i, LT (α i)] : LT (Σₗ' i, α i) :=
  ⟨Lex (· < ·) fun _ => (· < ·)⟩

/--
Instance `preorder` / 实例 `preorder`

English:
instance preorder
  signature: [Preorder ι] [forall i, Preorder (α i)]
  body: { Lex.le, Lex.lt with
    le_refl := fun ⟨_, _⟩ => Lex.right _ le_rfl,
    le_trans := by
      rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ ⟨a₃, b₃⟩ ⟨h₁r⟩ ⟨h₂r⟩
      · left
        apply lt_trans
        repeat' assumption
      · left
        assumption
      · left
        assumption
      · right
        apply le_

中文:
实例 preorder
  签名: [预序 ι] [对任意 i, 预序 (α i)]
  定义体: { Lex.le, Lex.lt with
    le_refl := fun ⟨_, _⟩ => Lex.right _ le_rfl,
    le_trans := by
      rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ ⟨a₃, b₃⟩ ⟨h₁r⟩ ⟨h₂r⟩
      · left
        apply lt_trans
        repeat' assumption
      · left
        assumption
      · left
        assumption
      · right
        apply le_

Depends on / 依赖: Lex.le, Lex.lt, Lex.right, hab.mono_right, hij.not_gt, le_of_lt, le_refl, le_rfl, le_trans, lt_iff_le_not_ge, lt_irrefl, lt_trans, mono_right, not_gt, repeat
-/
instance preorder [Preorder ι] [forall i, Preorder (α i)] : Preorder (Σₗ' i, α i) :=
  { Lex.le, Lex.lt with
    le_refl := fun ⟨_, _⟩ => Lex.right _ le_rfl,
    le_trans := by
      rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ ⟨a₃, b₃⟩ ⟨h₁r⟩ ⟨h₂r⟩
      · left
        apply lt_trans
        repeat' assumption
      · left
        assumption
      · left
        assumption
      · right
        apply le_trans
        repeat' assumption,
    lt_iff_le_not_ge := by
      refine fun a b => ⟨fun hab => ⟨hab.mono_right fun i a b => le_of_lt, ?_⟩, ?_⟩
      · rintro (⟨i, a, hji⟩ | ⟨i, hba⟩) <;> obtain ⟨_, _, hij⟩ | ⟨_, hab⟩ := hab
        · exact hij.not_gt hji
        · exact lt_irrefl _ hji
        · exact lt_irrefl _ hij
        · exact hab.not_ge hba
      · rintro ⟨⟨j, b, hij⟩ | ⟨i, hab⟩, hba⟩
        · exact Lex.left _ _ hij
        · exact Lex.right _ (hab.lt_of_not_ge fun h => hba <| Lex.right _ h) }

/--
Instance `partialOrder` / 实例 `partialOrder`

English:
instance partialOrder
  signature: [PartialOrder ι] [forall i, PartialOrder (α i)]
  body: { Lex.preorder with
    le_antisymm := by
      rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ (⟨_, _, hlt₁⟩ | ⟨_, hlt₁⟩) (⟨_, _, hlt₂⟩ | ⟨_, hlt₂⟩)
      · exact (lt_irrefl a₁ <| hlt₁.trans hlt₂).elim
      · exact (lt_irrefl a₁ hlt₁).elim
      · exact (lt_irrefl a₁ hlt₂).elim
      · rw [hlt₁.antisymm hlt₂] }

中文:
实例 partialOrder
  签名: [偏序 ι] [对任意 i, 偏序 (α i)]
  定义体: { Lex.preorder with
    le_antisymm := by
      rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ (⟨_, _, hlt₁⟩ | ⟨_, hlt₁⟩) (⟨_, _, hlt₂⟩ | ⟨_, hlt₂⟩)
      · exact (lt_irrefl a₁ <| hlt₁.trans hlt₂).elim
      · exact (lt_irrefl a₁ hlt₁).elim
      · exact (lt_irrefl a₁ hlt₂).elim
      · rw [hlt₁.antisymm hlt₂] }

Depends on / 依赖: Lex.preorder, antisymm, le_antisymm, lt_irrefl, preorder
-/
instance partialOrder [PartialOrder ι] [forall i, PartialOrder (α i)] : PartialOrder (Σₗ' i, α i) :=
  { Lex.preorder with
    le_antisymm := by
      rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ (⟨_, _, hlt₁⟩ | ⟨_, hlt₁⟩) (⟨_, _, hlt₂⟩ | ⟨_, hlt₂⟩)
      · exact (lt_irrefl a₁ <| hlt₁.trans hlt₂).elim
      · exact (lt_irrefl a₁ hlt₁).elim
      · exact (lt_irrefl a₁ hlt₂).elim
      · rw [hlt₁.antisymm hlt₂] }

/--
Instance `linearOrder` / 实例 `linearOrder`

English:
instance linearOrder
  signature: [LinearOrder ι] [forall i, LinearOrder (α i)]
  body: { Lex.partialOrder with
    le_total := by
      rintro ⟨i, a⟩ ⟨j, b⟩
      obtain hij | rfl | hji := lt_trichotomy i j
      · exact Or.inl (Lex.left _ _ hij)
      · obtain hab | hba := le_total a b
        · exact Or.inl (Lex.right _ hab)
        · exact Or.inr (Lex.right _ hba)
      · exact Or.

中文:
实例 linearOrder
  签名: [线性序 ι] [对任意 i, 线性序 (α i)]
  定义体: { Lex.partialOrder with
    le_total := by
      rintro ⟨i, a⟩ ⟨j, b⟩
      obtain hij | rfl | hji := lt_trichotomy i j
      · exact Or.inl (Lex.left _ _ hij)
      · obtain hab | hba := le_total a b
        · exact Or.inl (Lex.right _ hab)
        · exact Or.inr (Lex.right _ hba)
      · exact Or.

Depends on / 依赖: Lex.decidable, Lex.left, Lex.partialOrder, Lex.right, Or.inl, Or.inr, PSigma, PSigma.decidableEq, decidable, decidableEq, le_total, lt_trichotomy, partialOrder, toDecidableEq, toDecidableLE, toDecidableLT
-/
instance linearOrder [LinearOrder ι] [forall i, LinearOrder (α i)] : LinearOrder (Σₗ' i, α i) :=
  { Lex.partialOrder with
    le_total := by
      rintro ⟨i, a⟩ ⟨j, b⟩
      obtain hij | rfl | hji := lt_trichotomy i j
      · exact Or.inl (Lex.left _ _ hij)
      · obtain hab | hba := le_total a b
        · exact Or.inl (Lex.right _ hab)
        · exact Or.inr (Lex.right _ hba)
      · exact Or.inr (Lex.left _ _ hji),
    toDecidableEq := PSigma.decidableEq, toDecidableLE := Lex.decidable _ _,
    toDecidableLT := Lex.decidable _ _ }

/--
Instance `orderBot` / 实例 `orderBot`

English:
instance orderBot
  signature: [PartialOrder ι] [OrderBot ι] [forall i, Preorder (α i)] [OrderBot (α ⊥)]
  body: ⟨⊥, ⊥⟩
  bot_le := fun ⟨a, b⟩ => by
    obtain rfl | ha := eq_bot_or_bot_lt a
    · exact Lex.right _ bot_le
    · exact Lex.left _ _ ha

中文:
实例 orderBot
  签名: [偏序 ι] [有底序 ι] [对任意 i, 预序 (α i)] [有底序 (α ⊥)]
  定义体: ⟨⊥, ⊥⟩
  bot_le := fun ⟨a, b⟩ => by
    obtain rfl | ha := eq_bot_or_bot_lt a
    · exact Lex.right _ bot_le
    · exact Lex.left _ _ ha
-/
instance orderBot [PartialOrder ι] [OrderBot ι] [forall i, Preorder (α i)] [OrderBot (α ⊥)] :
    OrderBot (Σₗ' i, α i) where
  bot := ⟨⊥, ⊥⟩
  bot_le := fun ⟨a, b⟩ => by
    obtain rfl | ha := eq_bot_or_bot_lt a
    · exact Lex.right _ bot_le
    · exact Lex.left _ _ ha

/--
Instance `orderTop` / 实例 `orderTop`

English:
instance orderTop
  signature: [PartialOrder ι] [OrderTop ι] [forall i, Preorder (α i)] [OrderTop (α ⊤)]
  body: ⟨⊤, ⊤⟩
  le_top := fun ⟨a, b⟩ => by
    obtain rfl | ha := eq_top_or_lt_top a
    · exact Lex.right _ le_top
    · exact Lex.left _ _ ha

中文:
实例 orderTop
  签名: [偏序 ι] [有顶序 ι] [对任意 i, 预序 (α i)] [有顶序 (α ⊤)]
  定义体: ⟨⊤, ⊤⟩
  le_top := fun ⟨a, b⟩ => by
    obtain rfl | ha := eq_top_or_lt_top a
    · exact Lex.right _ le_top
    · exact Lex.left _ _ ha
-/
instance orderTop [PartialOrder ι] [OrderTop ι] [forall i, Preorder (α i)] [OrderTop (α ⊤)] :
    OrderTop (Σₗ' i, α i) where
  top := ⟨⊤, ⊤⟩
  le_top := fun ⟨a, b⟩ => by
    obtain rfl | ha := eq_top_or_lt_top a
    · exact Lex.right _ le_top
    · exact Lex.left _ _ ha

/--
Instance `boundedOrder` / 实例 `boundedOrder`

English:
instance boundedOrder
  signature: [PartialOrder ι] [BoundedOrder ι] [forall i, Preorder (α i)] [OrderBot (α ⊥)]
  body: { Lex.orderBot, Lex.orderTop with }

中文:
实例 boundedOrder
  签名: [偏序 ι] [有界序 ι] [对任意 i, 预序 (α i)] [有底序 (α ⊥)]
  定义体: { Lex.orderBot, Lex.orderTop with }

Depends on / 依赖: Lex.orderBot, Lex.orderTop, orderBot, orderTop
-/
instance boundedOrder [PartialOrder ι] [BoundedOrder ι] [forall i, Preorder (α i)] [OrderBot (α ⊥)]
    [OrderTop (α ⊤)] : BoundedOrder (Σₗ' i, α i) :=
  { Lex.orderBot, Lex.orderTop with }

/--
Instance `denselyOrdered` / 实例 `denselyOrdered`

English:
instance denselyOrdered
  signature: [Preorder ι] [DenselyOrdered ι] [forall i, Nonempty (α i)] [forall i, Preorder (α i)]
  body: ⟨by
    rintro ⟨i, a⟩ ⟨j, b⟩ (⟨_, _, h⟩ | @⟨_, _, b, h⟩)
    · obtain ⟨k, hi, hj⟩ := exists_between h
      obtain ⟨c⟩ : Nonempty (α k) := inferInstance
      exact ⟨⟨k, c⟩, left _ _ hi, left _ _ hj⟩
    · obtain ⟨c, ha, hb⟩ := exists_between h
      exact ⟨⟨i, c⟩, right _ ha, right _ hb⟩⟩

中文:
实例 denselyOrdered
  签名: [预序 ι] [稠密序 ι] [对任意 i, 非空 (α i)] [对任意 i, 预序 (α i)]
  定义体: ⟨by
    rintro ⟨i, a⟩ ⟨j, b⟩ (⟨_, _, h⟩ | @⟨_, _, b, h⟩)
    · obtain ⟨k, hi, hj⟩ := exists_between h
      obtain ⟨c⟩ : Nonempty (α k) := inferInstance
      exact ⟨⟨k, c⟩, left _ _ hi, left _ _ hj⟩
    · obtain ⟨c, ha, hb⟩ := exists_between h
      exact ⟨⟨i, c⟩, right _ ha, right _ hb⟩⟩

Depends on / 依赖: Nonempty, exists_between
-/
instance denselyOrdered [Preorder ι] [DenselyOrdered ι] [forall i, Nonempty (α i)] [forall i, Preorder (α i)]
    [forall i, DenselyOrdered (α i)] : DenselyOrdered (Σₗ' i, α i) :=
  ⟨by
    rintro ⟨i, a⟩ ⟨j, b⟩ (⟨_, _, h⟩ | @⟨_, _, b, h⟩)
    · obtain ⟨k, hi, hj⟩ := exists_between h
      obtain ⟨c⟩ : Nonempty (α k) := inferInstance
      exact ⟨⟨k, c⟩, left _ _ hi, left _ _ hj⟩
    · obtain ⟨c, ha, hb⟩ := exists_between h
      exact ⟨⟨i, c⟩, right _ ha, right _ hb⟩⟩

/--
Instance `denselyOrdered_of_noMaxOrder` / 实例 `denselyOrdered_of_noMaxOrder`

English:
instance denselyOrdered_of_noMaxOrder
  signature: [Preorder ι] [forall i, Preorder (α i)]
  body: ⟨by
    rintro ⟨i, a⟩ ⟨j, b⟩ (⟨_, _, h⟩ | @⟨_, _, b, h⟩)
    · obtain ⟨c, ha⟩ := exists_gt a
      exact ⟨⟨i, c⟩, right _ ha, left _ _ h⟩
    · obtain ⟨c, ha, hb⟩ := exists_between h
      exact ⟨⟨i, c⟩, right _ ha, right _ hb⟩⟩

中文:
实例 denselyOrdered_of_noMaxOrder
  签名: [预序 ι] [对任意 i, 预序 (α i)]
  定义体: ⟨by
    rintro ⟨i, a⟩ ⟨j, b⟩ (⟨_, _, h⟩ | @⟨_, _, b, h⟩)
    · obtain ⟨c, ha⟩ := exists_gt a
      exact ⟨⟨i, c⟩, right _ ha, left _ _ h⟩
    · obtain ⟨c, ha, hb⟩ := exists_between h
      exact ⟨⟨i, c⟩, right _ ha, right _ hb⟩⟩

Depends on / 依赖: exists_between, exists_gt
-/
instance denselyOrdered_of_noMaxOrder [Preorder ι] [forall i, Preorder (α i)]
    [forall i, DenselyOrdered (α i)] [forall i, NoMaxOrder (α i)] : DenselyOrdered (Σₗ' i, α i) :=
  ⟨by
    rintro ⟨i, a⟩ ⟨j, b⟩ (⟨_, _, h⟩ | @⟨_, _, b, h⟩)
    · obtain ⟨c, ha⟩ := exists_gt a
      exact ⟨⟨i, c⟩, right _ ha, left _ _ h⟩
    · obtain ⟨c, ha, hb⟩ := exists_between h
      exact ⟨⟨i, c⟩, right _ ha, right _ hb⟩⟩

/--
Instance `denselyOrdered_of_noMinOrder` / 实例 `denselyOrdered_of_noMinOrder`

English:
instance denselyOrdered_of_noMinOrder
  signature: [Preorder ι] [forall i, Preorder (α i)]
  body: ⟨by
    rintro ⟨i, a⟩ ⟨j, b⟩ (⟨_, _, h⟩ | @⟨_, _, b, h⟩)
    · obtain ⟨c, hb⟩ := exists_lt b
      exact ⟨⟨j, c⟩, left _ _ h, right _ hb⟩
    · obtain ⟨c, ha, hb⟩ := exists_between h
      exact ⟨⟨i, c⟩, right _ ha, right _ hb⟩⟩

中文:
实例 denselyOrdered_of_noMinOrder
  签名: [预序 ι] [对任意 i, 预序 (α i)]
  定义体: ⟨by
    rintro ⟨i, a⟩ ⟨j, b⟩ (⟨_, _, h⟩ | @⟨_, _, b, h⟩)
    · obtain ⟨c, hb⟩ := exists_lt b
      exact ⟨⟨j, c⟩, left _ _ h, right _ hb⟩
    · obtain ⟨c, ha, hb⟩ := exists_between h
      exact ⟨⟨i, c⟩, right _ ha, right _ hb⟩⟩

Depends on / 依赖: exists_between, exists_lt
-/
instance denselyOrdered_of_noMinOrder [Preorder ι] [forall i, Preorder (α i)]
    [forall i, DenselyOrdered (α i)] [forall i, NoMinOrder (α i)] : DenselyOrdered (Σₗ' i, α i) :=
  ⟨by
    rintro ⟨i, a⟩ ⟨j, b⟩ (⟨_, _, h⟩ | @⟨_, _, b, h⟩)
    · obtain ⟨c, hb⟩ := exists_lt b
      exact ⟨⟨j, c⟩, left _ _ h, right _ hb⟩
    · obtain ⟨c, ha, hb⟩ := exists_between h
      exact ⟨⟨i, c⟩, right _ ha, right _ hb⟩⟩

/--
Instance `noMaxOrder_of_nonempty` / 实例 `noMaxOrder_of_nonempty`

English:
instance noMaxOrder_of_nonempty
  signature: [Preorder ι] [forall i, Preorder (α i)] [NoMaxOrder ι]
  body: ⟨by
    rintro ⟨i, a⟩
    obtain ⟨j, h⟩ := exists_gt i
    obtain ⟨b⟩ : Nonempty (α j) := inferInstance
    exact ⟨⟨j, b⟩, left _ _ h⟩⟩

中文:
实例 noMaxOrder_of_nonempty
  签名: [预序 ι] [对任意 i, 预序 (α i)] [NoMax序 ι]
  定义体: ⟨by
    rintro ⟨i, a⟩
    obtain ⟨j, h⟩ := exists_gt i
    obtain ⟨b⟩ : Nonempty (α j) := inferInstance
    exact ⟨⟨j, b⟩, left _ _ h⟩⟩

Depends on / 依赖: Nonempty, exists_gt
-/
instance noMaxOrder_of_nonempty [Preorder ι] [forall i, Preorder (α i)] [NoMaxOrder ι]
    [forall i, Nonempty (α i)] : NoMaxOrder (Σₗ' i, α i) :=
  ⟨by
    rintro ⟨i, a⟩
    obtain ⟨j, h⟩ := exists_gt i
    obtain ⟨b⟩ : Nonempty (α j) := inferInstance
    exact ⟨⟨j, b⟩, left _ _ h⟩⟩

/--
Instance `noMinOrder_of_nonempty` / 实例 `noMinOrder_of_nonempty`

English:
instance noMinOrder_of_nonempty
  signature: [Preorder ι] [forall i, Preorder (α i)] [NoMinOrder ι]
  body: ⟨by
    rintro ⟨i, a⟩
    obtain ⟨j, h⟩ := exists_lt i
    obtain ⟨b⟩ : Nonempty (α j) := inferInstance
    exact ⟨⟨j, b⟩, left _ _ h⟩⟩

中文:
实例 noMinOrder_of_nonempty
  签名: [预序 ι] [对任意 i, 预序 (α i)] [NoMin序 ι]
  定义体: ⟨by
    rintro ⟨i, a⟩
    obtain ⟨j, h⟩ := exists_lt i
    obtain ⟨b⟩ : Nonempty (α j) := inferInstance
    exact ⟨⟨j, b⟩, left _ _ h⟩⟩

Depends on / 依赖: Nonempty, exists_lt
-/
instance noMinOrder_of_nonempty [Preorder ι] [forall i, Preorder (α i)] [NoMinOrder ι]
    [forall i, Nonempty (α i)] : NoMinOrder (Σₗ' i, α i) :=
  ⟨by
    rintro ⟨i, a⟩
    obtain ⟨j, h⟩ := exists_lt i
    obtain ⟨b⟩ : Nonempty (α j) := inferInstance
    exact ⟨⟨j, b⟩, left _ _ h⟩⟩

/--
Instance `noMaxOrder` / 实例 `noMaxOrder`

English:
instance noMaxOrder
  signature: [Preorder ι] [forall i, Preorder (α i)] [forall i, NoMaxOrder (α i)]
  body: ⟨by
    rintro ⟨i, a⟩
    obtain ⟨b, h⟩ := exists_gt a
    exact ⟨⟨i, b⟩, right _ h⟩⟩

中文:
实例 noMaxOrder
  签名: [预序 ι] [对任意 i, 预序 (α i)] [对任意 i, NoMax序 (α i)]
  定义体: ⟨by
    rintro ⟨i, a⟩
    obtain ⟨b, h⟩ := exists_gt a
    exact ⟨⟨i, b⟩, right _ h⟩⟩

Depends on / 依赖: exists_gt
-/
instance noMaxOrder [Preorder ι] [forall i, Preorder (α i)] [forall i, NoMaxOrder (α i)] :
    NoMaxOrder (Σₗ' i, α i) :=
  ⟨by
    rintro ⟨i, a⟩
    obtain ⟨b, h⟩ := exists_gt a
    exact ⟨⟨i, b⟩, right _ h⟩⟩

/--
Instance `noMinOrder` / 实例 `noMinOrder`

English:
instance noMinOrder
  signature: [Preorder ι] [forall i, Preorder (α i)] [forall i, NoMinOrder (α i)]
  body: ⟨by
    rintro ⟨i, a⟩
    obtain ⟨b, h⟩ := exists_lt a
    exact ⟨⟨i, b⟩, right _ h⟩⟩

中文:
实例 noMinOrder
  签名: [预序 ι] [对任意 i, 预序 (α i)] [对任意 i, NoMin序 (α i)]
  定义体: ⟨by
    rintro ⟨i, a⟩
    obtain ⟨b, h⟩ := exists_lt a
    exact ⟨⟨i, b⟩, right _ h⟩⟩

Depends on / 依赖: exists_lt
-/
instance noMinOrder [Preorder ι] [forall i, Preorder (α i)] [forall i, NoMinOrder (α i)] :
    NoMinOrder (Σₗ' i, α i) :=
  ⟨by
    rintro ⟨i, a⟩
    obtain ⟨b, h⟩ := exists_lt a
    exact ⟨⟨i, b⟩, right _ h⟩⟩

end Lex

end PSigma
