/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Heyting.Basic
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Lex
public import Mathlib.Order.WithBot

/-!
# Orders on a sum type

This file defines the disjoint sum and the linear (aka lexicographic) sum of two orders and
provides relation instances for `Sum.LiftRel` and `Sum.Lex`.

We declare the disjoint sum of orders as the default set of instances. The linear order goes on a
type synonym.

## Main declarations

* `Sum.LE`, `Sum.LT`: Disjoint sum of orders.
* `Sum.Lex.LE`, `Sum.Lex.LT`: Lexicographic/linear sum of orders.

## Notation

* `α ⊕ₗ β`: The linear sum of `α` and `β`.
-/

@[expose] public section


variable {α β γ : Type*}

namespace Sum

/-! ### Unbundled relation classes -/


section LiftRel

variable (r : α -> α -> Prop) (s : β -> β -> Prop)

@[refl]
/--
theorem `LiftRel.refl` / 定理 `LiftRel.refl`

English:
theorem LiftRel.refl
  given: [Std.Refl r] [Std.Refl s]
  statement: forall x, LiftRel r s x x

中文:
定理 LiftRel.refl
  条件: [Std.Refl r] [Std.Refl s]
  结论: 对任意 x, LiftRel r s x x
-/
theorem LiftRel.refl [Std.Refl r] [Std.Refl s] : forall x, LiftRel r s x x
  | inl a => LiftRel.inl (_root_.refl a)
  | inr a => LiftRel.inr (_root_.refl a)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Std.Refl
  signature: r] [Std.Refl s] : Std.Refl (LiftRel r s)
  body: ⟨LiftRel.refl _ _⟩

中文:
实例 [Std.Refl
  签名: r] [Std.Refl s] : Std.Refl (LiftRel r s)
  定义体: ⟨LiftRel.refl _ _⟩

Depends on / 依赖: LiftRel, LiftRel.refl
-/
instance [Std.Refl r] [Std.Refl s] : Std.Refl (LiftRel r s) :=
  ⟨LiftRel.refl _ _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Std.Irrefl
  signature: r] [Std.Irrefl s] : Std.Irrefl (LiftRel r s)
  body: ⟨by rintro _ (⟨h⟩ | ⟨h⟩) <;> exact irrefl _ h⟩

@[trans]

中文:
实例 [Std.Irrefl
  签名: r] [Std.Irrefl s] : Std.Irrefl (LiftRel r s)
  定义体: ⟨by rintro _ (⟨h⟩ | ⟨h⟩) <;> exact irrefl _ h⟩

@[trans]

Depends on / 依赖: irrefl
-/
instance [Std.Irrefl r] [Std.Irrefl s] : Std.Irrefl (LiftRel r s) :=
  ⟨by rintro _ (⟨h⟩ | ⟨h⟩) <;> exact irrefl _ h⟩

@[trans]
/--
theorem `LiftRel.trans` / 定理 `LiftRel.trans`

English:
theorem LiftRel.trans
  given: [IsTrans α r] [IsTrans β s]

中文:
定理 LiftRel.trans
  条件: [是Trans α r] [是Trans β s]
-/
theorem LiftRel.trans [IsTrans α r] [IsTrans β s] :
    forall {a b c}, LiftRel r s a b -> LiftRel r s b c -> LiftRel r s a c
| _, _, _, LiftRel.inl hab, LiftRel.inl hbc => LiftRel.inl _root_.trans hab hbc
| _, _, _, LiftRel.inr hab, LiftRel.inr hbc => LiftRel.inr _root_.trans hab hbc

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsTrans
  signature: α r] [IsTrans β s] : IsTrans (α oplus β) (LiftRel r s)
  body: ⟨fun _ _ _ => LiftRel.trans _ _⟩

中文:
实例 [是Trans
  签名: α r] [是Trans β s] : 是Trans (α oplus β) (LiftRel r s)
  定义体: ⟨fun _ _ _ => LiftRel.trans _ _⟩

Depends on / 依赖: LiftRel, LiftRel.trans
-/
instance [IsTrans α r] [IsTrans β s] : IsTrans (α oplus β) (LiftRel r s) :=
  ⟨fun _ _ _ => LiftRel.trans _ _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Std.Antisymm
  signature: r] [Std.Antisymm s] : Std.Antisymm (LiftRel r s)
  body: ⟨by rintro _ _ (⟨hab⟩ | ⟨hab⟩) (⟨hba⟩ | ⟨hba⟩) <;> rw [antisymm hab hba]⟩

中文:
实例 [Std.反对称
  签名: r] [Std.反对称 s] : Std.反对称 (LiftRel r s)
  定义体: ⟨by rintro _ _ (⟨hab⟩ | ⟨hab⟩) (⟨hba⟩ | ⟨hba⟩) <;> rw [antisymm hab hba]⟩

Depends on / 依赖: antisymm
-/
instance [Std.Antisymm r] [Std.Antisymm s] : Std.Antisymm (LiftRel r s) :=
  ⟨by rintro _ _ (⟨hab⟩ | ⟨hab⟩) (⟨hba⟩ | ⟨hba⟩) <;> rw [antisymm hab hba]⟩

end LiftRel

section Lex

variable (r : α -> α -> Prop) (s : β -> β -> Prop)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Std.Refl
  signature: r] [Std.Refl s] : Std.Refl (Lex r s)
  body: ⟨by
    rintro (a | a)
    exacts [Lex.inl (refl _), Lex.inr (refl _)]⟩

中文:
实例 [Std.Refl
  签名: r] [Std.Refl s] : Std.Refl (Lex r s)
  定义体: ⟨by
    rintro (a | a)
    exacts [Lex.inl (refl _), Lex.inr (refl _)]⟩

Depends on / 依赖: Lex.inl, Lex.inr, exacts
-/
instance [Std.Refl r] [Std.Refl s] : Std.Refl (Lex r s) :=
  ⟨by
    rintro (a | a)
    exacts [Lex.inl (refl _), Lex.inr (refl _)]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Std.Irrefl
  signature: r] [Std.Irrefl s] : Std.Irrefl (Lex r s)
  body: ⟨by rintro _ (⟨h⟩ | ⟨h⟩) <;> exact irrefl _ h⟩

中文:
实例 [Std.Irrefl
  签名: r] [Std.Irrefl s] : Std.Irrefl (Lex r s)
  定义体: ⟨by rintro _ (⟨h⟩ | ⟨h⟩) <;> exact irrefl _ h⟩

Depends on / 依赖: irrefl
-/
instance [Std.Irrefl r] [Std.Irrefl s] : Std.Irrefl (Lex r s) :=
  ⟨by rintro _ (⟨h⟩ | ⟨h⟩) <;> exact irrefl _ h⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsTrans
  signature: α r] [IsTrans β s] : IsTrans (α oplus β) (Lex r s)
  body: ⟨by
    rintro _ _ _ (⟨hab⟩ | ⟨hab⟩) (⟨hbc⟩ | ⟨hbc⟩)
    exacts [.inl (_root_.trans hab hbc), .sep _ _, .inr (_root_.trans hab hbc), .sep _ _]⟩

中文:
实例 [是Trans
  签名: α r] [是Trans β s] : 是Trans (α oplus β) (Lex r s)
  定义体: ⟨by
    rintro _ _ _ (⟨hab⟩ | ⟨hab⟩) (⟨hbc⟩ | ⟨hbc⟩)
    exacts [.inl (_root_.trans hab hbc), .sep _ _, .inr (_root_.trans hab hbc), .sep _ _]⟩

Depends on / 依赖: _root_, _root_.trans, exacts
-/
instance [IsTrans α r] [IsTrans β s] : IsTrans (α oplus β) (Lex r s) :=
  ⟨by
    rintro _ _ _ (⟨hab⟩ | ⟨hab⟩) (⟨hbc⟩ | ⟨hbc⟩)
    exacts [.inl (_root_.trans hab hbc), .sep _ _, .inr (_root_.trans hab hbc), .sep _ _]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Std.Antisymm
  signature: r] [Std.Antisymm s] : Std.Antisymm (Lex r s)
  body: ⟨by rintro _ _ (⟨hab⟩ | ⟨hab⟩) (⟨hba⟩ | ⟨hba⟩) <;> rw [antisymm hab hba]⟩

中文:
实例 [Std.反对称
  签名: r] [Std.反对称 s] : Std.反对称 (Lex r s)
  定义体: ⟨by rintro _ _ (⟨hab⟩ | ⟨hab⟩) (⟨hba⟩ | ⟨hba⟩) <;> rw [antisymm hab hba]⟩

Depends on / 依赖: antisymm
-/
instance [Std.Antisymm r] [Std.Antisymm s] : Std.Antisymm (Lex r s) :=
  ⟨by rintro _ _ (⟨hab⟩ | ⟨hab⟩) (⟨hba⟩ | ⟨hba⟩) <;> rw [antisymm hab hba]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Std.Total
  signature: r] [Std.Total s] : Std.Total (Lex r s)
  body: ⟨fun a b =>
    match a, b with
    | inl a, inl b => (total_of r a b).imp Lex.inl Lex.inl
    | inl _, inr _ => Or.inl (Lex.sep _ _)
    | inr _, inl _ => Or.inr (Lex.sep _ _)
    | inr a, inr b => (total_of s a b).imp Lex.inr Lex.inr⟩

中文:
实例 [Std.全
  签名: r] [Std.全 s] : Std.全 (Lex r s)
  定义体: ⟨fun a b =>
    match a, b with
    | inl a, inl b => (total_of r a b).imp Lex.inl Lex.inl
    | inl _, inr _ => Or.inl (Lex.sep _ _)
    | inr _, inl _ => Or.inr (Lex.sep _ _)
    | inr a, inr b => (total_of s a b).imp Lex.inr Lex.inr⟩

Depends on / 依赖: Lex.inl, Lex.inr, Lex.sep, Or.inl, Or.inr, total_of
-/
instance [Std.Total r] [Std.Total s] : Std.Total (Lex r s) :=
  ⟨fun a b =>
    match a, b with
    | inl a, inl b => (total_of r a b).imp Lex.inl Lex.inl
    | inl _, inr _ => Or.inl (Lex.sep _ _)
    | inr _, inl _ => Or.inr (Lex.sep _ _)
    | inr a, inr b => (total_of s a b).imp Lex.inr Lex.inr⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Std.Trichotomous
  signature: r] [Std.Trichotomous s] : Std.Trichotomous (Lex r s)
  body: by
  grind [Std.Trichotomous, Lex]

中文:
实例 [Std.三歧
  签名: r] [Std.三歧 s] : Std.三歧 (Lex r s)
  定义体: by
  grind [Std.Trichotomous, Lex]

Depends on / 依赖: Std.Trichotomous, Trichotomous
-/
instance [Std.Trichotomous r] [Std.Trichotomous s] : Std.Trichotomous (Lex r s) := by
  grind [Std.Trichotomous, Lex]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsWellOrder
  signature: α r] [IsWellOrder β s] :
  body: Sum.lex_wf IsWellFounded.wf IsWellFounded.wf

中文:
实例 [是良序
  签名: α r] [是良序 β s] :
  定义体: Sum.lex_wf IsWellFounded.wf IsWellFounded.wf

Depends on / 依赖: IsWellFounded, IsWellFounded.wf, Sum.lex_wf, lex_wf
-/
instance [IsWellOrder α r] [IsWellOrder β s] :
    IsWellOrder (α oplus β) (Sum.Lex r s) where wf := Sum.lex_wf IsWellFounded.wf IsWellFounded.wf

end Lex

/-! ### Disjoint sum of two orders -/


section Disjoint

/--
Instance `instLESum` / 实例 `instLESum`

English:
instance instLESum
  signature: [LE α] [LE β]
  body: ⟨LiftRel (· <= ·) (· <= ·)⟩

中文:
实例 instLESum
  签名: [LE α] [LE β]
  定义体: ⟨LiftRel (· <= ·) (· <= ·)⟩

Depends on / 依赖: LiftRel, summand_smul_def
-/
instance instLESum [LE α] [LE β] : LE (α oplus β) :=
  ⟨LiftRel (· <= ·) (· <= ·)⟩

/--
Instance `instLTSum` / 实例 `instLTSum`

English:
instance instLTSum
  signature: [LT α] [LT β]
  body: ⟨LiftRel (· < ·) (· < ·)⟩

中文:
实例 instLTSum
  签名: [LT α] [LT β]
  定义体: ⟨LiftRel (· < ·) (· < ·)⟩

Depends on / 依赖: LiftRel
-/
instance instLTSum [LT α] [LT β] : LT (α oplus β) :=
  ⟨LiftRel (· < ·) (· < ·)⟩

/--
theorem `le_def` / 定理 `le_def`

English:
theorem le_def
  given: [LE α] [LE β] {a b : α oplus β}
  statement: a <= b ↔ LiftRel (· <= ·) (· <= ·) a b
  proof: Iff.rfl

中文:
定理 le_def
  条件: [LE α] [LE β] {a b : α oplus β}
  结论: a <= b ↔ LiftRel (· <= ·) (· <= ·) a b
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem le_def [LE α] [LE β] {a b : α oplus β} : a <= b ↔ LiftRel (· <= ·) (· <= ·) a b :=
  Iff.rfl

/--
theorem `lt_def` / 定理 `lt_def`

English:
theorem lt_def
  given: [LT α] [LT β] {a b : α oplus β}
  statement: a < b ↔ LiftRel (· < ·) (· < ·) a b
  proof: Iff.rfl

@[simp]

中文:
定理 lt_def
  条件: [LT α] [LT β] {a b : α oplus β}
  结论: a < b ↔ LiftRel (· < ·) (· < ·) a b
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem lt_def [LT α] [LT β] {a b : α oplus β} : a < b ↔ LiftRel (· < ·) (· < ·) a b :=
  Iff.rfl

@[simp]
/--
theorem `inl_le_inl_iff` / 定理 `inl_le_inl_iff`

English:
theorem inl_le_inl_iff
  given: [LE α] [LE β] {a b : α}
  statement: (inl a : α oplus β) <= inl b ↔ a <= b
  proof: liftRel_inl_inl

@[simp]

中文:
定理 inl_le_inl_iff
  条件: [LE α] [LE β] {a b : α}
  结论: (inl a : α oplus β) <= inl b ↔ a <= b
  证明: liftRel_inl_inl

@[simp]

Depends on / 依赖: liftRel_inl_inl
-/
theorem inl_le_inl_iff [LE α] [LE β] {a b : α} : (inl a : α oplus β) <= inl b ↔ a <= b :=
  liftRel_inl_inl

@[simp]
/--
theorem `inr_le_inr_iff` / 定理 `inr_le_inr_iff`

English:
theorem inr_le_inr_iff
  given: [LE α] [LE β] {a b : β}
  statement: (inr a : α oplus β) <= inr b ↔ a <= b
  proof: liftRel_inr_inr

@[simp]

中文:
定理 inr_le_inr_iff
  条件: [LE α] [LE β] {a b : β}
  结论: (inr a : α oplus β) <= inr b ↔ a <= b
  证明: liftRel_inr_inr

@[simp]

Depends on / 依赖: liftRel_inr_inr
-/
theorem inr_le_inr_iff [LE α] [LE β] {a b : β} : (inr a : α oplus β) <= inr b ↔ a <= b :=
  liftRel_inr_inr

@[simp]
/--
theorem `inl_lt_inl_iff` / 定理 `inl_lt_inl_iff`

English:
theorem inl_lt_inl_iff
  given: [LT α] [LT β] {a b : α}
  statement: (inl a : α oplus β) < inl b ↔ a < b
  proof: liftRel_inl_inl

@[simp]

中文:
定理 inl_lt_inl_iff
  条件: [LT α] [LT β] {a b : α}
  结论: (inl a : α oplus β) < inl b ↔ a < b
  证明: liftRel_inl_inl

@[simp]

Depends on / 依赖: liftRel_inl_inl
-/
theorem inl_lt_inl_iff [LT α] [LT β] {a b : α} : (inl a : α oplus β) < inl b ↔ a < b :=
  liftRel_inl_inl

@[simp]
/--
theorem `inr_lt_inr_iff` / 定理 `inr_lt_inr_iff`

English:
theorem inr_lt_inr_iff
  given: [LT α] [LT β] {a b : β}
  statement: (inr a : α oplus β) < inr b ↔ a < b
  proof: liftRel_inr_inr

@[simp]

中文:
定理 inr_lt_inr_iff
  条件: [LT α] [LT β] {a b : β}
  结论: (inr a : α oplus β) < inr b ↔ a < b
  证明: liftRel_inr_inr

@[simp]

Depends on / 依赖: liftRel_inr_inr
-/
theorem inr_lt_inr_iff [LT α] [LT β] {a b : β} : (inr a : α oplus β) < inr b ↔ a < b :=
  liftRel_inr_inr

@[simp]
/--
theorem `not_inl_le_inr` / 定理 `not_inl_le_inr`

English:
theorem not_inl_le_inr
  given: [LE α] [LE β] {a : α} {b : β}
  statement: ¬inl b <= inr a
  proof: not_liftRel_inl_inr

@[simp]

中文:
定理 not_inl_le_inr
  条件: [LE α] [LE β] {a : α} {b : β}
  结论: ¬inl b <= inr a
  证明: not_liftRel_inl_inr

@[simp]

Depends on / 依赖: not_liftRel_inl_inr
-/
theorem not_inl_le_inr [LE α] [LE β] {a : α} {b : β} : ¬inl b <= inr a :=
  not_liftRel_inl_inr

@[simp]
/--
theorem `not_inl_lt_inr` / 定理 `not_inl_lt_inr`

English:
theorem not_inl_lt_inr
  given: [LT α] [LT β] {a : α} {b : β}
  statement: ¬inl b < inr a
  proof: not_liftRel_inl_inr

@[simp]

中文:
定理 not_inl_lt_inr
  条件: [LT α] [LT β] {a : α} {b : β}
  结论: ¬inl b < inr a
  证明: not_liftRel_inl_inr

@[simp]

Depends on / 依赖: not_liftRel_inl_inr
-/
theorem not_inl_lt_inr [LT α] [LT β] {a : α} {b : β} : ¬inl b < inr a :=
  not_liftRel_inl_inr

@[simp]
/--
theorem `not_inr_le_inl` / 定理 `not_inr_le_inl`

English:
theorem not_inr_le_inl
  given: [LE α] [LE β] {a : α} {b : β}
  statement: ¬inr b <= inl a
  proof: not_liftRel_inr_inl

@[simp]

中文:
定理 not_inr_le_inl
  条件: [LE α] [LE β] {a : α} {b : β}
  结论: ¬inr b <= inl a
  证明: not_liftRel_inr_inl

@[simp]

Depends on / 依赖: not_liftRel_inr_inl
-/
theorem not_inr_le_inl [LE α] [LE β] {a : α} {b : β} : ¬inr b <= inl a :=
  not_liftRel_inr_inl

@[simp]
/--
theorem `not_inr_lt_inl` / 定理 `not_inr_lt_inl`

English:
theorem not_inr_lt_inl
  given: [LT α] [LT β] {a : α} {b : β}
  statement: ¬inr b < inl a
  proof: not_liftRel_inr_inl

中文:
定理 not_inr_lt_inl
  条件: [LT α] [LT β] {a : α} {b : β}
  结论: ¬inr b < inl a
  证明: not_liftRel_inr_inl

Depends on / 依赖: not_liftRel_inr_inl
-/
theorem not_inr_lt_inl [LT α] [LT β] {a : α} {b : β} : ¬inr b < inl a :=
  not_liftRel_inr_inl

section Preorder

variable [Preorder α] [Preorder β]

/--
Instance `instPreorderSum` / 实例 `instPreorderSum`

English:
instance instPreorderSum
  signature: : Preorder (α oplus β)
  body: { instLESum, instLTSum with
    le_refl := fun _ => LiftRel.refl _ _ _,
    le_trans := fun _ _ _ => LiftRel.trans _ _,
    lt_iff_le_not_ge := fun a b => by
      refine ⟨fun hab => ⟨hab.mono (fun _ _ => le_of_lt) fun _ _ => le_of_lt, ?_⟩, ?_⟩
      · rintro (⟨hba⟩ | ⟨hba⟩)
        · exact hba.not_gt (inl_lt_inl_iff.1 hab)
        · exact hba.not_gt (inr_lt_inr_iff.1 hab)
      · rintro ⟨⟨hab⟩ | ⟨hab⟩, hba⟩
        · exact LiftRel.inl (hab.lt_of_not_ge fun h => hba <| LiftRel.inl h)
        · exact LiftRel.inr (hab.lt_of_not_ge fun h => hba <| LiftRel.inr h) }

中文:
实例 instPreorderSum
  签名: : 预序 (α oplus β)
  定义体: { instLESum, instLTSum with
    le_refl := fun _ => LiftRel.refl _ _ _,
    le_trans := fun _ _ _ => LiftRel.trans _ _,
    lt_iff_le_not_ge := fun a b => by
      refine ⟨fun hab => ⟨hab.mono (fun _ _ => le_of_lt) fun _ _ => le_of_lt, ?_⟩, ?_⟩
      · rintro (⟨hba⟩ | ⟨hba⟩)
        · exact hba.not_gt (inl_lt_inl_iff.1 hab)
        · exact hba.not_gt (inr_lt_inr_iff.1 hab)
      · rintro ⟨⟨hab⟩ | ⟨hab⟩, hba⟩
        · exact LiftRel.inl (hab.lt_of_not_ge fun h => hba <| LiftRel.inl h)
        · exact LiftRel.inr (hab.lt_of_not_ge fun h => hba <| LiftRel.inr h) }

Depends on / 依赖: LiftRel, LiftRel.inl, LiftRel.inr, LiftRel.refl, LiftRel.trans, hab.lt_of_not_ge, hab.mono, hba.not_gt, inl_lt_inl_iff, inr_lt_inr_iff, instLESum, instLTSum, le_of_lt, le_refl, le_trans, lt_iff_le_not_ge, lt_of_not_ge, not_gt
-/
instance instPreorderSum : Preorder (α oplus β) :=
  { instLESum, instLTSum with
    le_refl := fun _ => LiftRel.refl _ _ _,
    le_trans := fun _ _ _ => LiftRel.trans _ _,
    lt_iff_le_not_ge := fun a b => by
      refine ⟨fun hab => ⟨hab.mono (fun _ _ => le_of_lt) fun _ _ => le_of_lt, ?_⟩, ?_⟩
      · rintro (⟨hba⟩ | ⟨hba⟩)
        · exact hba.not_gt (inl_lt_inl_iff.1 hab)
        · exact hba.not_gt (inr_lt_inr_iff.1 hab)
      · rintro ⟨⟨hab⟩ | ⟨hab⟩, hba⟩
        · exact LiftRel.inl (hab.lt_of_not_ge fun h => hba <| LiftRel.inl h)
        · exact LiftRel.inr (hab.lt_of_not_ge fun h => hba <| LiftRel.inr h) }

/--
theorem `inl_mono` / 定理 `inl_mono`

English:
theorem inl_mono
  statement: Monotone (inl : α -> α oplus β)
  proof: fun _ _ => LiftRel.inl

中文:
定理 inl_mono
  结论: 递增 (inl : α -> α oplus β)
  证明: fun _ _ => LiftRel.inl

Depends on / 依赖: LiftRel, LiftRel.inl
-/
theorem inl_mono : Monotone (inl : α -> α oplus β) := fun _ _ => LiftRel.inl

/--
theorem `inr_mono` / 定理 `inr_mono`

English:
theorem inr_mono
  statement: Monotone (inr : β -> α oplus β)
  proof: fun _ _ => LiftRel.inr

中文:
定理 inr_mono
  结论: 递增 (inr : β -> α oplus β)
  证明: fun _ _ => LiftRel.inr

Depends on / 依赖: LiftRel, LiftRel.inr
-/
theorem inr_mono : Monotone (inr : β -> α oplus β) := fun _ _ => LiftRel.inr

/--
theorem `inl_strictMono` / 定理 `inl_strictMono`

English:
theorem inl_strictMono
  statement: StrictMono (inl : α -> α oplus β)
  proof: fun _ _ => LiftRel.inl

中文:
定理 inl_strictMono
  结论: 严格递增 (inl : α -> α oplus β)
  证明: fun _ _ => LiftRel.inl

Depends on / 依赖: LiftRel, LiftRel.inl
-/
theorem inl_strictMono : StrictMono (inl : α -> α oplus β) := fun _ _ => LiftRel.inl

/--
theorem `inr_strictMono` / 定理 `inr_strictMono`

English:
theorem inr_strictMono
  statement: StrictMono (inr : β -> α oplus β)
  proof: fun _ _ => LiftRel.inr

中文:
定理 inr_strictMono
  结论: 严格递增 (inr : β -> α oplus β)
  证明: fun _ _ => LiftRel.inr

Depends on / 依赖: LiftRel, LiftRel.inr
-/
theorem inr_strictMono : StrictMono (inr : β -> α oplus β) := fun _ _ => LiftRel.inr

end Preorder

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PartialOrder
  signature: α] [PartialOrder β] : PartialOrder (α oplus β)
  body: { instPreorderSum with
    le_antisymm := fun _ _ => show LiftRel _ _ _ _ -> _ from antisymm }

中文:
实例 [偏序
  签名: α] [偏序 β] : 偏序 (α oplus β)
  定义体: { instPreorderSum with
    le_antisymm := fun _ _ => show LiftRel _ _ _ _ -> _ from antisymm }

Depends on / 依赖: LiftRel, antisymm, instPreorderSum, le_antisymm
-/
instance [PartialOrder α] [PartialOrder β] : PartialOrder (α oplus β) :=
  { instPreorderSum with
    le_antisymm := fun _ _ => show LiftRel _ _ _ _ -> _ from antisymm }

/--
Instance `noMinOrder` / 实例 `noMinOrder`

English:
instance noMinOrder
  signature: [LT α] [LT β] [NoMinOrder α] [NoMinOrder β]
  body: ⟨fun a =>
    match a with
    | inl a =>
      let ⟨b, h⟩ := exists_lt a
      ⟨inl b, inl_lt_inl_iff.2 h⟩
    | inr a =>
      let ⟨b, h⟩ := exists_lt a
      ⟨inr b, inr_lt_inr_iff.2 h⟩⟩

中文:
实例 noMinOrder
  签名: [LT α] [LT β] [NoMin序 α] [NoMin序 β]
  定义体: ⟨fun a =>
    match a with
    | inl a =>
      let ⟨b, h⟩ := exists_lt a
      ⟨inl b, inl_lt_inl_iff.2 h⟩
    | inr a =>
      let ⟨b, h⟩ := exists_lt a
      ⟨inr b, inr_lt_inr_iff.2 h⟩⟩

Depends on / 依赖: exists_lt, inl_lt_inl_iff, inr_lt_inr_iff
-/
instance noMinOrder [LT α] [LT β] [NoMinOrder α] [NoMinOrder β] : NoMinOrder (α oplus β) :=
  ⟨fun a =>
    match a with
    | inl a =>
      let ⟨b, h⟩ := exists_lt a
      ⟨inl b, inl_lt_inl_iff.2 h⟩
    | inr a =>
      let ⟨b, h⟩ := exists_lt a
      ⟨inr b, inr_lt_inr_iff.2 h⟩⟩

/--
Instance `noMaxOrder` / 实例 `noMaxOrder`

English:
instance noMaxOrder
  signature: [LT α] [LT β] [NoMaxOrder α] [NoMaxOrder β]
  body: ⟨fun a =>
    match a with
    | inl a =>
      let ⟨b, h⟩ := exists_gt a
      ⟨inl b, inl_lt_inl_iff.2 h⟩
    | inr a =>
      let ⟨b, h⟩ := exists_gt a
      ⟨inr b, inr_lt_inr_iff.2 h⟩⟩

@[simp]

中文:
实例 noMaxOrder
  签名: [LT α] [LT β] [NoMax序 α] [NoMax序 β]
  定义体: ⟨fun a =>
    match a with
    | inl a =>
      let ⟨b, h⟩ := exists_gt a
      ⟨inl b, inl_lt_inl_iff.2 h⟩
    | inr a =>
      let ⟨b, h⟩ := exists_gt a
      ⟨inr b, inr_lt_inr_iff.2 h⟩⟩

@[simp]

Depends on / 依赖: exists_gt, inl_lt_inl_iff, inr_lt_inr_iff
-/
instance noMaxOrder [LT α] [LT β] [NoMaxOrder α] [NoMaxOrder β] : NoMaxOrder (α oplus β) :=
  ⟨fun a =>
    match a with
    | inl a =>
      let ⟨b, h⟩ := exists_gt a
      ⟨inl b, inl_lt_inl_iff.2 h⟩
    | inr a =>
      let ⟨b, h⟩ := exists_gt a
      ⟨inr b, inr_lt_inr_iff.2 h⟩⟩

@[simp]
/--
theorem `noMinOrder_iff` / 定理 `noMinOrder_iff`

English:
theorem noMinOrder_iff
  given: [LT α] [LT β]
  statement: NoMinOrder (α oplus β) ↔ NoMinOrder α ∧ NoMinOrder β
  proof: ⟨fun _ =>
    ⟨⟨fun a => by
        obtain ⟨b | b, h⟩ := exists_lt (inl a : α oplus β)
        · exact ⟨b, inl_lt_inl_iff.1 h⟩
        · exact (not_inr_lt_inl h).elim⟩,
      ⟨fun a => by
        obtain ⟨b | b, h⟩ := exists_lt (inr a : α oplus β)
        · exact (not_inl_lt_inr h).elim
        · exact ⟨b, inr_lt_inr_iff.1 h⟩⟩⟩,
    fun h => @Sum.noMinOrder _ _ _ _ h.1 h.2⟩

@[simp]

中文:
定理 noMinOrder_iff
  条件: [LT α] [LT β]
  结论: NoMin序 (α oplus β) ↔ NoMin序 α ∧ NoMin序 β
  证明: ⟨fun _ =>
    ⟨⟨fun a => by
        obtain ⟨b | b, h⟩ := exists_lt (inl a : α oplus β)
        · exact ⟨b, inl_lt_inl_iff.1 h⟩
        · exact (not_inr_lt_inl h).elim⟩,
      ⟨fun a => by
        obtain ⟨b | b, h⟩ := exists_lt (inr a : α oplus β)
        · exact (not_inl_lt_inr h).elim
        · exact ⟨b, inr_lt_inr_iff.1 h⟩⟩⟩,
    fun h => @Sum.noMinOrder _ _ _ _ h.1 h.2⟩

@[simp]

Depends on / 依赖: Sum.noMinOrder, exists_lt, inl_lt_inl_iff, inr_lt_inr_iff, noMinOrder, not_inl_lt_inr, not_inr_lt_inl
-/
theorem noMinOrder_iff [LT α] [LT β] : NoMinOrder (α oplus β) ↔ NoMinOrder α ∧ NoMinOrder β :=
  ⟨fun _ =>
    ⟨⟨fun a => by
        obtain ⟨b | b, h⟩ := exists_lt (inl a : α oplus β)
        · exact ⟨b, inl_lt_inl_iff.1 h⟩
        · exact (not_inr_lt_inl h).elim⟩,
      ⟨fun a => by
        obtain ⟨b | b, h⟩ := exists_lt (inr a : α oplus β)
        · exact (not_inl_lt_inr h).elim
        · exact ⟨b, inr_lt_inr_iff.1 h⟩⟩⟩,
    fun h => @Sum.noMinOrder _ _ _ _ h.1 h.2⟩

@[simp]
/--
theorem `noMaxOrder_iff` / 定理 `noMaxOrder_iff`

English:
theorem noMaxOrder_iff
  given: [LT α] [LT β]
  statement: NoMaxOrder (α oplus β) ↔ NoMaxOrder α ∧ NoMaxOrder β
  proof: ⟨fun _ =>
    ⟨⟨fun a => by
        obtain ⟨b | b, h⟩ := exists_gt (inl a : α oplus β)
        · exact ⟨b, inl_lt_inl_iff.1 h⟩
        · exact (not_inl_lt_inr h).elim⟩,
      ⟨fun a => by
        obtain ⟨b | b, h⟩ := exists_gt (inr a : α oplus β)
        · exact (not_inr_lt_inl h).elim
        · exact ⟨b, inr_lt_inr_iff.1 h⟩⟩⟩,
    fun h => @Sum.noMaxOrder _ _ _ _ h.1 h.2⟩

中文:
定理 noMaxOrder_iff
  条件: [LT α] [LT β]
  结论: NoMax序 (α oplus β) ↔ NoMax序 α ∧ NoMax序 β
  证明: ⟨fun _ =>
    ⟨⟨fun a => by
        obtain ⟨b | b, h⟩ := exists_gt (inl a : α oplus β)
        · exact ⟨b, inl_lt_inl_iff.1 h⟩
        · exact (not_inl_lt_inr h).elim⟩,
      ⟨fun a => by
        obtain ⟨b | b, h⟩ := exists_gt (inr a : α oplus β)
        · exact (not_inr_lt_inl h).elim
        · exact ⟨b, inr_lt_inr_iff.1 h⟩⟩⟩,
    fun h => @Sum.noMaxOrder _ _ _ _ h.1 h.2⟩

Depends on / 依赖: Sum.noMaxOrder, exists_gt, inl_lt_inl_iff, inr_lt_inr_iff, noMaxOrder, not_inl_lt_inr, not_inr_lt_inl
-/
theorem noMaxOrder_iff [LT α] [LT β] : NoMaxOrder (α oplus β) ↔ NoMaxOrder α ∧ NoMaxOrder β :=
  ⟨fun _ =>
    ⟨⟨fun a => by
        obtain ⟨b | b, h⟩ := exists_gt (inl a : α oplus β)
        · exact ⟨b, inl_lt_inl_iff.1 h⟩
        · exact (not_inl_lt_inr h).elim⟩,
      ⟨fun a => by
        obtain ⟨b | b, h⟩ := exists_gt (inr a : α oplus β)
        · exact (not_inr_lt_inl h).elim
        · exact ⟨b, inr_lt_inr_iff.1 h⟩⟩⟩,
    fun h => @Sum.noMaxOrder _ _ _ _ h.1 h.2⟩

/--
Instance `denselyOrdered` / 实例 `denselyOrdered`

English:
instance denselyOrdered
  signature: [LT α] [LT β] [DenselyOrdered α] [DenselyOrdered β]
  body: ⟨fun a b h =>
    match a, b, h with
    | inl _, inl _, LiftRel.inl h =>
      let ⟨c, ha, hb⟩ := exists_between h
      ⟨toLex (inl c), LiftRel.inl ha, LiftRel.inl hb⟩
    | inr _, inr _, LiftRel.inr h =>
      let ⟨c, ha, hb⟩ := exists_between h
      ⟨toLex (inr c), LiftRel.inr ha, LiftRel.inr hb⟩⟩

@[simp]

中文:
实例 denselyOrdered
  签名: [LT α] [LT β] [稠密序 α] [稠密序 β]
  定义体: ⟨fun a b h =>
    match a, b, h with
    | inl _, inl _, LiftRel.inl h =>
      let ⟨c, ha, hb⟩ := exists_between h
      ⟨toLex (inl c), LiftRel.inl ha, LiftRel.inl hb⟩
    | inr _, inr _, LiftRel.inr h =>
      let ⟨c, ha, hb⟩ := exists_between h
      ⟨toLex (inr c), LiftRel.inr ha, LiftRel.inr hb⟩⟩

@[simp]

Depends on / 依赖: LiftRel, LiftRel.inl, LiftRel.inr, exists_between
-/
instance denselyOrdered [LT α] [LT β] [DenselyOrdered α] [DenselyOrdered β] :
    DenselyOrdered (α oplus β) :=
  ⟨fun a b h =>
    match a, b, h with
    | inl _, inl _, LiftRel.inl h =>
      let ⟨c, ha, hb⟩ := exists_between h
      ⟨toLex (inl c), LiftRel.inl ha, LiftRel.inl hb⟩
    | inr _, inr _, LiftRel.inr h =>
      let ⟨c, ha, hb⟩ := exists_between h
      ⟨toLex (inr c), LiftRel.inr ha, LiftRel.inr hb⟩⟩

@[simp]
/--
theorem `denselyOrdered_iff` / 定理 `denselyOrdered_iff`

English:
theorem denselyOrdered_iff
  given: [LT α] [LT β]
  proof: ⟨fun _ =>
    ⟨⟨fun a b h => by
        obtain ⟨c | c, ha, hb⟩ := @exists_between (α oplus β) _ _ _ _ (inl_lt_inl_iff.2 h)
        · exact ⟨c, inl_lt_inl_iff.1 ha, inl_lt_inl_iff.1 hb⟩
        · exact (not_inl_lt_inr ha).elim⟩,
      ⟨fun a b h => by
        obtain ⟨c | c, ha, hb⟩ := @exists_between (α oplus β) _ _ _ _ (inr_lt_inr_iff.2 h)
        · exact (not_inl_lt_inr hb).elim
        · exact ⟨c, inr_lt_inr_iff.1 ha, inr_lt_inr_iff.1 hb⟩⟩⟩,
    fun h => @Sum.denselyOrdered _ _ _ _ h.1 h.2⟩

@[simp]

中文:
定理 denselyOrdered_iff
  条件: [LT α] [LT β]
  证明: ⟨fun _ =>
    ⟨⟨fun a b h => by
        obtain ⟨c | c, ha, hb⟩ := @exists_between (α oplus β) _ _ _ _ (inl_lt_inl_iff.2 h)
        · exact ⟨c, inl_lt_inl_iff.1 ha, inl_lt_inl_iff.1 hb⟩
        · exact (not_inl_lt_inr ha).elim⟩,
      ⟨fun a b h => by
        obtain ⟨c | c, ha, hb⟩ := @exists_between (α oplus β) _ _ _ _ (inr_lt_inr_iff.2 h)
        · exact (not_inl_lt_inr hb).elim
        · exact ⟨c, inr_lt_inr_iff.1 ha, inr_lt_inr_iff.1 hb⟩⟩⟩,
    fun h => @Sum.denselyOrdered _ _ _ _ h.1 h.2⟩

@[simp]

Depends on / 依赖: Sum.denselyOrdered, denselyOrdered, exists_between, inl_lt_inl_iff, inr_lt_inr_iff, not_inl_lt_inr
-/
theorem denselyOrdered_iff [LT α] [LT β] :
    DenselyOrdered (α oplus β) ↔ DenselyOrdered α ∧ DenselyOrdered β :=
  ⟨fun _ =>
    ⟨⟨fun a b h => by
        obtain ⟨c | c, ha, hb⟩ := @exists_between (α oplus β) _ _ _ _ (inl_lt_inl_iff.2 h)
        · exact ⟨c, inl_lt_inl_iff.1 ha, inl_lt_inl_iff.1 hb⟩
        · exact (not_inl_lt_inr ha).elim⟩,
      ⟨fun a b h => by
        obtain ⟨c | c, ha, hb⟩ := @exists_between (α oplus β) _ _ _ _ (inr_lt_inr_iff.2 h)
        · exact (not_inl_lt_inr hb).elim
        · exact ⟨c, inr_lt_inr_iff.1 ha, inr_lt_inr_iff.1 hb⟩⟩⟩,
    fun h => @Sum.denselyOrdered _ _ _ _ h.1 h.2⟩

@[simp]
/--
theorem `swap_le_swap_iff` / 定理 `swap_le_swap_iff`

English:
theorem swap_le_swap_iff
  given: [LE α] [LE β] {a b : α oplus β}
  statement: a.swap <= b.swap ↔ a <= b
  proof: liftRel_swap_iff

@[simp]

中文:
定理 swap_le_swap_iff
  条件: [LE α] [LE β] {a b : α oplus β}
  结论: a.swap <= b.swap ↔ a <= b
  证明: liftRel_swap_iff

@[simp]

Depends on / 依赖: liftRel_swap_iff
-/
theorem swap_le_swap_iff [LE α] [LE β] {a b : α oplus β} : a.swap <= b.swap ↔ a <= b :=
  liftRel_swap_iff

@[simp]
/--
theorem `swap_lt_swap_iff` / 定理 `swap_lt_swap_iff`

English:
theorem swap_lt_swap_iff
  given: [LT α] [LT β] {a b : α oplus β}
  statement: a.swap < b.swap ↔ a < b
  proof: liftRel_swap_iff

中文:
定理 swap_lt_swap_iff
  条件: [LT α] [LT β] {a b : α oplus β}
  结论: a.swap < b.swap ↔ a < b
  证明: liftRel_swap_iff

Depends on / 依赖: liftRel_swap_iff
-/
theorem swap_lt_swap_iff [LT α] [LT β] {a b : α oplus β} : a.swap < b.swap ↔ a < b :=
  liftRel_swap_iff

end Disjoint

/-! ### Linear sum of two orders -/


namespace Lex


/-- The linear sum of two orders -/
notation3:30 α " oplusₗ " β:29 => _root_.Lex (α oplus β)

--TODO: Can we make `inlₗ`, `inrₗ` `local notation`?
/-- Lexicographical `Sum.inl`. Only used for pattern matching. -/
@[match_pattern]
/--
Definition of `_root_.Sum.inlₗ` / `_root_.Sum.inlₗ` 的定义

English:
abbreviation _root_.Sum.inlₗ
  signature: (x : α)
  body: toLex (Sum.inl x)

中文:
缩写 _root_.和.inlₗ
  签名: (x : α)
  定义体: toLex (Sum.inl x)

Depends on / 依赖: Sum.inl
-/
abbrev _root_.Sum.inlₗ (x : α) : α oplusₗ β :=
  toLex (Sum.inl x)

/-- Lexicographical `Sum.inr`. Only used for pattern matching. -/
@[match_pattern]
/--
Definition of `_root_.Sum.inrₗ` / `_root_.Sum.inrₗ` 的定义

English:
abbreviation _root_.Sum.inrₗ
  signature: (x : β)
  body: toLex (Sum.inr x)

中文:
缩写 _root_.和.inrₗ
  签名: (x : β)
  定义体: toLex (Sum.inr x)

Depends on / 依赖: Sum.inr
-/
abbrev _root_.Sum.inrₗ (x : β) : α oplusₗ β :=
  toLex (Sum.inr x)

/--
Instance `LE` / 实例 `LE`

English:
instance LE
  signature: [LE α] [LE β]
  body: ⟨Lex (· <= ·) (· <= ·)⟩

中文:
实例 LE
  签名: [LE α] [LE β]
  定义体: ⟨Lex (· <= ·) (· <= ·)⟩
-/
protected instance LE [LE α] [LE β] : LE (α oplusₗ β) :=
  ⟨Lex (· <= ·) (· <= ·)⟩

/--
Instance `LT` / 实例 `LT`

English:
instance LT
  signature: [LT α] [LT β]
  body: ⟨Lex (· < ·) (· < ·)⟩

@[simp]

中文:
实例 LT
  签名: [LT α] [LT β]
  定义体: ⟨Lex (· < ·) (· < ·)⟩

@[simp]
-/
protected instance LT [LT α] [LT β] : LT (α oplusₗ β) :=
  ⟨Lex (· < ·) (· < ·)⟩

@[simp]
/--
theorem `toLex_le_toLex` / 定理 `toLex_le_toLex`

English:
theorem toLex_le_toLex
  given: [LE α] [LE β] {a b : α oplus β}
  proof: Iff.rfl

@[simp]

中文:
定理 toLex_le_toLex
  条件: [LE α] [LE β] {a b : α oplus β}
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem toLex_le_toLex [LE α] [LE β] {a b : α oplus β} :
    toLex a <= toLex b ↔ Lex (· <= ·) (· <= ·) a b :=
  Iff.rfl

@[simp]
/--
theorem `toLex_lt_toLex` / 定理 `toLex_lt_toLex`

English:
theorem toLex_lt_toLex
  given: [LT α] [LT β] {a b : α oplus β}
  proof: Iff.rfl

中文:
定理 toLex_lt_toLex
  条件: [LT α] [LT β] {a b : α oplus β}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem toLex_lt_toLex [LT α] [LT β] {a b : α oplus β} :
    toLex a < toLex b ↔ Lex (· < ·) (· < ·) a b :=
  Iff.rfl

/--
theorem `le_def` / 定理 `le_def`

English:
theorem le_def
  given: [LE α] [LE β] {a b : α oplusₗ β}
  statement: a <= b ↔ Lex (· <= ·) (· <= ·) (ofLex a) (ofLex b)
  proof: Iff.rfl

中文:
定理 le_def
  条件: [LE α] [LE β] {a b : α oplusₗ β}
  结论: a <= b ↔ Lex (· <= ·) (· <= ·) (ofLex a) (ofLex b)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem le_def [LE α] [LE β] {a b : α oplusₗ β} : a <= b ↔ Lex (· <= ·) (· <= ·) (ofLex a) (ofLex b) :=
  Iff.rfl

/--
theorem `lt_def` / 定理 `lt_def`

English:
theorem lt_def
  given: [LT α] [LT β] {a b : α oplusₗ β}
  statement: a < b ↔ Lex (· < ·) (· < ·) (ofLex a) (ofLex b)
  proof: Iff.rfl

中文:
定理 lt_def
  条件: [LT α] [LT β] {a b : α oplusₗ β}
  结论: a < b ↔ Lex (· < ·) (· < ·) (ofLex a) (ofLex b)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem lt_def [LT α] [LT β] {a b : α oplusₗ β} : a < b ↔ Lex (· < ·) (· < ·) (ofLex a) (ofLex b) :=
  Iff.rfl

/--
theorem `inl_le_inl_iff` / 定理 `inl_le_inl_iff`

English:
theorem inl_le_inl_iff
  given: [LE α] [LE β] {a b : α}
  statement: toLex (inl a : α oplus β) <= toLex (inl b) ↔ a <= b
  proof: lex_inl_inl

中文:
定理 inl_le_inl_iff
  条件: [LE α] [LE β] {a b : α}
  结论: toLex (inl a : α oplus β) <= toLex (inl b) ↔ a <= b
  证明: lex_inl_inl

Depends on / 依赖: lex_inl_inl
-/
theorem inl_le_inl_iff [LE α] [LE β] {a b : α} : toLex (inl a : α oplus β) <= toLex (inl b) ↔ a <= b :=
  lex_inl_inl

/--
theorem `inr_le_inr_iff` / 定理 `inr_le_inr_iff`

English:
theorem inr_le_inr_iff
  given: [LE α] [LE β] {a b : β}
  statement: toLex (inr a : α oplus β) <= toLex (inr b) ↔ a <= b
  proof: lex_inr_inr

中文:
定理 inr_le_inr_iff
  条件: [LE α] [LE β] {a b : β}
  结论: toLex (inr a : α oplus β) <= toLex (inr b) ↔ a <= b
  证明: lex_inr_inr

Depends on / 依赖: lex_inr_inr
-/
theorem inr_le_inr_iff [LE α] [LE β] {a b : β} : toLex (inr a : α oplus β) <= toLex (inr b) ↔ a <= b :=
  lex_inr_inr

/--
theorem `inl_lt_inl_iff` / 定理 `inl_lt_inl_iff`

English:
theorem inl_lt_inl_iff
  given: [LT α] [LT β] {a b : α}
  statement: toLex (inl a : α oplus β) < toLex (inl b) ↔ a < b
  proof: lex_inl_inl

中文:
定理 inl_lt_inl_iff
  条件: [LT α] [LT β] {a b : α}
  结论: toLex (inl a : α oplus β) < toLex (inl b) ↔ a < b
  证明: lex_inl_inl

Depends on / 依赖: lex_inl_inl
-/
theorem inl_lt_inl_iff [LT α] [LT β] {a b : α} : toLex (inl a : α oplus β) < toLex (inl b) ↔ a < b :=
  lex_inl_inl

/--
theorem `inr_lt_inr_iff` / 定理 `inr_lt_inr_iff`

English:
theorem inr_lt_inr_iff
  given: [LT α] [LT β] {a b : β}
  statement: toLex (inr a : α oplusₗ β) < toLex (inr b) ↔ a < b
  proof: lex_inr_inr

中文:
定理 inr_lt_inr_iff
  条件: [LT α] [LT β] {a b : β}
  结论: toLex (inr a : α oplusₗ β) < toLex (inr b) ↔ a < b
  证明: lex_inr_inr

Depends on / 依赖: lex_inr_inr
-/
theorem inr_lt_inr_iff [LT α] [LT β] {a b : β} : toLex (inr a : α oplusₗ β) < toLex (inr b) ↔ a < b :=
  lex_inr_inr

/--
theorem `inl_le_inr` / 定理 `inl_le_inr`

English:
theorem inl_le_inr
  given: [LE α] [LE β] (a : α) (b : β)
  statement: toLex (inl a) <= toLex (inr b)
  proof: Lex.sep _ _

中文:
定理 inl_le_inr
  条件: [LE α] [LE β] (a : α) (b : β)
  结论: toLex (inl a) <= toLex (inr b)
  证明: Lex.sep _ _

Depends on / 依赖: Lex.sep
-/
theorem inl_le_inr [LE α] [LE β] (a : α) (b : β) : toLex (inl a) <= toLex (inr b) :=
  Lex.sep _ _

/--
theorem `inl_lt_inr` / 定理 `inl_lt_inr`

English:
theorem inl_lt_inr
  given: [LT α] [LT β] (a : α) (b : β)
  statement: toLex (inl a) < toLex (inr b)
  proof: Lex.sep _ _

中文:
定理 inl_lt_inr
  条件: [LT α] [LT β] (a : α) (b : β)
  结论: toLex (inl a) < toLex (inr b)
  证明: Lex.sep _ _

Depends on / 依赖: Lex.sep
-/
theorem inl_lt_inr [LT α] [LT β] (a : α) (b : β) : toLex (inl a) < toLex (inr b) :=
  Lex.sep _ _

/--
theorem `not_inr_le_inl` / 定理 `not_inr_le_inl`

English:
theorem not_inr_le_inl
  given: [LE α] [LE β] {a : α} {b : β}
  statement: ¬toLex (inr b) <= toLex (inl a)
  proof: lex_inr_inl

中文:
定理 not_inr_le_inl
  条件: [LE α] [LE β] {a : α} {b : β}
  结论: ¬toLex (inr b) <= toLex (inl a)
  证明: lex_inr_inl

Depends on / 依赖: lex_inr_inl
-/
theorem not_inr_le_inl [LE α] [LE β] {a : α} {b : β} : ¬toLex (inr b) <= toLex (inl a) :=
  lex_inr_inl

/--
theorem `not_inr_lt_inl` / 定理 `not_inr_lt_inl`

English:
theorem not_inr_lt_inl
  given: [LT α] [LT β] {a : α} {b : β}
  statement: ¬toLex (inr b) < toLex (inl a)
  proof: lex_inr_inl

中文:
定理 not_inr_lt_inl
  条件: [LT α] [LT β] {a : α} {b : β}
  结论: ¬toLex (inr b) < toLex (inl a)
  证明: lex_inr_inl

Depends on / 依赖: lex_inr_inl
-/
theorem not_inr_lt_inl [LT α] [LT β] {a : α} {b : β} : ¬toLex (inr b) < toLex (inl a) :=
  lex_inr_inl

/--
Definition of `toLexRelIsoLT` / `toLexRelIsoLT` 的定义

English:
definition toLexRelIsoLT
  signature: [LT α] [LT β]
  body: toLex
  invFun := ofLex
  map_rel_iff' := .rfl

@[simp]

中文:
定义 toLexRelIsoLT
  签名: [LT α] [LT β]
  定义体: toLex
  invFun := ofLex
  map_rel_iff' := .rfl

@[simp]
-/
def toLexRelIsoLT [LT α] [LT β] :
    Sum.Lex (· < · : α -> α -> Prop) (· < · : β -> β -> Prop) ≃r (· < · : α oplusₗ β -> _ -> _) where
  toFun := toLex
  invFun := ofLex
  map_rel_iff' := .rfl

@[simp]
/--
theorem `toLexRelIsoLT_coe` / 定理 `toLexRelIsoLT_coe`

English:
theorem toLexRelIsoLT_coe
  given: [LT α] [LT β]
  statement: ⇑(toLexRelIsoLT (α := α) (β := β)) = toLex
  proof: rfl

@[simp]

中文:
定理 toLexRelIsoLT_coe
  条件: [LT α] [LT β]
  结论: ⇑(toLexRelIsoLT (α := α) (β := β)) = toLex
  证明: rfl

@[simp]
-/
theorem toLexRelIsoLT_coe [LT α] [LT β] : ⇑(toLexRelIsoLT (α := α) (β := β)) = toLex :=
  rfl

@[simp]
/--
theorem `toLexRelIsoLT_symm_coe` / 定理 `toLexRelIsoLT_symm_coe`

English:
theorem toLexRelIsoLT_symm_coe
  given: [LT α] [LT β]
  statement: ⇑(toLexRelIsoLT (α := α) (β := β)).symm = ofLex
  proof: rfl

中文:
定理 toLexRelIsoLT_symm_coe
  条件: [LT α] [LT β]
  结论: ⇑(toLexRelIsoLT (α := α) (β := β)).symm = ofLex
  证明: rfl
-/
theorem toLexRelIsoLT_symm_coe [LT α] [LT β] : ⇑(toLexRelIsoLT (α := α) (β := β)).symm = ofLex :=
  rfl

/--
Definition of `toLexRelIsoLE` / `toLexRelIsoLE` 的定义

English:
definition toLexRelIsoLE
  signature: [LE α] [LE β]
  body: toLex
  invFun := ofLex
  map_rel_iff' := .rfl

@[simp]

中文:
定义 toLexRelIsoLE
  签名: [LE α] [LE β]
  定义体: toLex
  invFun := ofLex
  map_rel_iff' := .rfl

@[simp]
-/
def toLexRelIsoLE [LE α] [LE β] :
    Sum.Lex (· <= · : α -> α -> Prop) (· <= · : β -> β -> Prop) ≃r (· <= · : α oplusₗ β -> _ -> _) where
  toFun := toLex
  invFun := ofLex
  map_rel_iff' := .rfl

@[simp]
/--
theorem `toLexRelIsoLE_coe` / 定理 `toLexRelIsoLE_coe`

English:
theorem toLexRelIsoLE_coe
  given: [LE α] [LE β]
  statement: ⇑(toLexRelIsoLE (α := α) (β := β)) = toLex
  proof: rfl

@[simp]

中文:
定理 toLexRelIsoLE_coe
  条件: [LE α] [LE β]
  结论: ⇑(toLexRelIsoLE (α := α) (β := β)) = toLex
  证明: rfl

@[simp]
-/
theorem toLexRelIsoLE_coe [LE α] [LE β] : ⇑(toLexRelIsoLE (α := α) (β := β)) = toLex :=
  rfl

@[simp]
/--
theorem `toLexRelIsoLE_symm_coe` / 定理 `toLexRelIsoLE_symm_coe`

English:
theorem toLexRelIsoLE_symm_coe
  given: [LE α] [LE β]
  statement: ⇑(toLexRelIsoLE (α := α) (β := β)).symm = ofLex
  proof: rfl

中文:
定理 toLexRelIsoLE_symm_coe
  条件: [LE α] [LE β]
  结论: ⇑(toLexRelIsoLE (α := α) (β := β)).symm = ofLex
  证明: rfl
-/
theorem toLexRelIsoLE_symm_coe [LE α] [LE β] : ⇑(toLexRelIsoLE (α := α) (β := β)).symm = ofLex :=
  rfl

section Preorder

variable [Preorder α] [Preorder β]

/--
Instance `preorder` / 实例 `preorder`

English:
instance preorder
  signature: : Preorder (α oplusₗ β)
  body: { Lex.LE, Lex.LT with
    le_refl := refl_of (Lex (· <= ·) (· <= ·)),
    le_trans := fun _ _ _ => trans_of (Lex (· <= ·) (· <= ·)),
    lt_iff_le_not_ge := fun a b => by
      refine ⟨fun hab => ⟨hab.mono (fun _ _ => le_of_lt) fun _ _ => le_of_lt, ?_⟩, ?_⟩
      · rintro (⟨hba⟩ | ⟨hba⟩ | ⟨b, a⟩)
        · exact hba.not_gt (inl_lt_inl_iff.1 hab)
        · exact hba.not_gt (inr_lt_inr_iff.1 hab)
        · exact not_inr_lt_inl hab
      · rintro ⟨⟨hab⟩ | ⟨hab⟩ | ⟨a, b⟩, hba⟩
        · exact Lex.inl (hab.lt_of_not_ge fun h => hba <| Lex.inl h)
        · exact Lex.inr (hab.lt_of_not_ge fun h => hba <| Lex.inr h)
        · exact Lex.sep _ _ }

中文:
实例 preorder
  签名: : 预序 (α oplusₗ β)
  定义体: { Lex.LE, Lex.LT with
    le_refl := refl_of (Lex (· <= ·) (· <= ·)),
    le_trans := fun _ _ _ => trans_of (Lex (· <= ·) (· <= ·)),
    lt_iff_le_not_ge := fun a b => by
      refine ⟨fun hab => ⟨hab.mono (fun _ _ => le_of_lt) fun _ _ => le_of_lt, ?_⟩, ?_⟩
      · rintro (⟨hba⟩ | ⟨hba⟩ | ⟨b, a⟩)
        · exact hba.not_gt (inl_lt_inl_iff.1 hab)
        · exact hba.not_gt (inr_lt_inr_iff.1 hab)
        · exact not_inr_lt_inl hab
      · rintro ⟨⟨hab⟩ | ⟨hab⟩ | ⟨a, b⟩, hba⟩
        · exact Lex.inl (hab.lt_of_not_ge fun h => hba <| Lex.inl h)
        · exact Lex.inr (hab.lt_of_not_ge fun h => hba <| Lex.inr h)
        · exact Lex.sep _ _ }

Depends on / 依赖: Lex.LE, Lex.LT, Lex.inl, Lex.inr, hab.lt_of_not_ge, hab.mono, hba.not_gt, inl_lt_inl_iff, inr_lt_inr_iff, le_of_lt, le_refl, le_trans, lt_iff_le_not_ge, lt_of_not_ge, not_gt, not_inr_lt_inl, refl_of, trans_of
-/
instance preorder : Preorder (α oplusₗ β) :=
  { Lex.LE, Lex.LT with
    le_refl := refl_of (Lex (· <= ·) (· <= ·)),
    le_trans := fun _ _ _ => trans_of (Lex (· <= ·) (· <= ·)),
    lt_iff_le_not_ge := fun a b => by
      refine ⟨fun hab => ⟨hab.mono (fun _ _ => le_of_lt) fun _ _ => le_of_lt, ?_⟩, ?_⟩
      · rintro (⟨hba⟩ | ⟨hba⟩ | ⟨b, a⟩)
        · exact hba.not_gt (inl_lt_inl_iff.1 hab)
        · exact hba.not_gt (inr_lt_inr_iff.1 hab)
        · exact not_inr_lt_inl hab
      · rintro ⟨⟨hab⟩ | ⟨hab⟩ | ⟨a, b⟩, hba⟩
        · exact Lex.inl (hab.lt_of_not_ge fun h => hba <| Lex.inl h)
        · exact Lex.inr (hab.lt_of_not_ge fun h => hba <| Lex.inr h)
        · exact Lex.sep _ _ }

/--
theorem `toLex_mono` / 定理 `toLex_mono`

English:
theorem toLex_mono
  statement: Monotone (@toLex (α oplus β))
  proof: fun _ _ h => h.lex

中文:
定理 toLex_mono
  结论: 递增 (@toLex (α oplus β))
  证明: fun _ _ h => h.lex

Depends on / 依赖: h.lex
-/
theorem toLex_mono : Monotone (@toLex (α oplus β)) := fun _ _ h => h.lex

/--
theorem `toLex_strictMono` / 定理 `toLex_strictMono`

English:
theorem toLex_strictMono
  statement: StrictMono (@toLex (α oplus β))
  proof: fun _ _ h => h.lex

中文:
定理 toLex_strictMono
  结论: 严格递增 (@toLex (α oplus β))
  证明: fun _ _ h => h.lex

Depends on / 依赖: h.lex
-/
theorem toLex_strictMono : StrictMono (@toLex (α oplus β)) := fun _ _ h => h.lex

/--
theorem `inl_mono` / 定理 `inl_mono`

English:
theorem inl_mono
  statement: Monotone (toLex ∘ inl : α -> α oplusₗ β)
  proof: toLex_mono.comp Sum.inl_mono

中文:
定理 inl_mono
  结论: 递增 (toLex ∘ inl : α -> α oplusₗ β)
  证明: toLex_mono.comp Sum.inl_mono

Depends on / 依赖: Sum.inl_mono, inl_mono, toLex_mono, toLex_mono.comp
-/
theorem inl_mono : Monotone (toLex ∘ inl : α -> α oplusₗ β) :=
  toLex_mono.comp Sum.inl_mono

/--
theorem `inr_mono` / 定理 `inr_mono`

English:
theorem inr_mono
  statement: Monotone (toLex ∘ inr : β -> α oplusₗ β)
  proof: toLex_mono.comp Sum.inr_mono

中文:
定理 inr_mono
  结论: 递增 (toLex ∘ inr : β -> α oplusₗ β)
  证明: toLex_mono.comp Sum.inr_mono

Depends on / 依赖: Sum.inr_mono, inr_mono, toLex_mono, toLex_mono.comp
-/
theorem inr_mono : Monotone (toLex ∘ inr : β -> α oplusₗ β) :=
  toLex_mono.comp Sum.inr_mono

/--
theorem `inl_strictMono` / 定理 `inl_strictMono`

English:
theorem inl_strictMono
  statement: StrictMono (toLex ∘ inl : α -> α oplusₗ β)
  proof: toLex_strictMono.comp Sum.inl_strictMono

中文:
定理 inl_strictMono
  结论: 严格递增 (toLex ∘ inl : α -> α oplusₗ β)
  证明: toLex_strictMono.comp Sum.inl_strictMono

Depends on / 依赖: Sum.inl_strictMono, inl_strictMono, toLex_strictMono, toLex_strictMono.comp
-/
theorem inl_strictMono : StrictMono (toLex ∘ inl : α -> α oplusₗ β) :=
  toLex_strictMono.comp Sum.inl_strictMono

/--
theorem `inr_strictMono` / 定理 `inr_strictMono`

English:
theorem inr_strictMono
  statement: StrictMono (toLex ∘ inr : β -> α oplusₗ β)
  proof: toLex_strictMono.comp Sum.inr_strictMono

中文:
定理 inr_strictMono
  结论: 严格递增 (toLex ∘ inr : β -> α oplusₗ β)
  证明: toLex_strictMono.comp Sum.inr_strictMono

Depends on / 依赖: Sum.inr_strictMono, inr_strictMono, toLex_strictMono, toLex_strictMono.comp
-/
theorem inr_strictMono : StrictMono (toLex ∘ inr : β -> α oplusₗ β) :=
  toLex_strictMono.comp Sum.inr_strictMono

end Preorder

/--
Instance `partialOrder` / 实例 `partialOrder`

English:
instance partialOrder
  signature: [PartialOrder α] [PartialOrder β]
  body: { Lex.preorder with le_antisymm := fun _ _ => antisymm_of (Lex (· <= ·) (· <= ·)) }

中文:
实例 partialOrder
  签名: [偏序 α] [偏序 β]
  定义体: { Lex.preorder with le_antisymm := fun _ _ => antisymm_of (Lex (· <= ·) (· <= ·)) }

Depends on / 依赖: Lex.preorder, antisymm_of, le_antisymm, preorder
-/
instance partialOrder [PartialOrder α] [PartialOrder β] : PartialOrder (α oplusₗ β) :=
  { Lex.preorder with le_antisymm := fun _ _ => antisymm_of (Lex (· <= ·) (· <= ·)) }

/--
Instance `linearOrder` / 实例 `linearOrder`

English:
instance linearOrder
  signature: [LinearOrder α] [LinearOrder β]
  body: { Lex.partialOrder with
    le_total := total_of (Lex (· <= ·) (· <= ·)),
    toDecidableLE := instDecidableRelSumLex,
    toDecidableLT := instDecidableRelSumLex,
    toDecidableEq := instDecidableEqSum }

中文:
实例 linearOrder
  签名: [线性序 α] [线性序 β]
  定义体: { Lex.partialOrder with
    le_total := total_of (Lex (· <= ·) (· <= ·)),
    toDecidableLE := instDecidableRelSumLex,
    toDecidableLT := instDecidableRelSumLex,
    toDecidableEq := instDecidableEqSum }

Depends on / 依赖: Lex.partialOrder, instDecidableEqSum, instDecidableRelSumLex, le_total, partialOrder, toDecidableEq, toDecidableLE, toDecidableLT, total_of
-/
instance linearOrder [LinearOrder α] [LinearOrder β] : LinearOrder (α oplusₗ β) :=
  { Lex.partialOrder with
    le_total := total_of (Lex (· <= ·) (· <= ·)),
    toDecidableLE := instDecidableRelSumLex,
    toDecidableLT := instDecidableRelSumLex,
    toDecidableEq := instDecidableEqSum }

/--
Instance `orderBot` / 实例 `orderBot`

English:
instance orderBot
  signature: [LE α] [OrderBot α] [LE β]
  body: inl ⊥
  bot_le := by
    rintro (a | b)
    · exact Lex.inl bot_le
    · exact Lex.sep _ _

@[simp]

中文:
实例 orderBot
  签名: [LE α] [有底序 α] [LE β]
  定义体: inl ⊥
  bot_le := by
    rintro (a | b)
    · exact Lex.inl bot_le
    · exact Lex.sep _ _

@[simp]
-/
instance orderBot [LE α] [OrderBot α] [LE β] :
    OrderBot (α oplusₗ β) where
  bot := inl ⊥
  bot_le := by
    rintro (a | b)
    · exact Lex.inl bot_le
    · exact Lex.sep _ _

@[simp]
/--
theorem `inl_bot` / 定理 `inl_bot`

English:
theorem inl_bot
  given: [LE α] [OrderBot α] [LE β]
  statement: toLex (inl ⊥ : α oplus β) = ⊥
  proof: rfl

中文:
定理 inl_bot
  条件: [LE α] [有底序 α] [LE β]
  结论: toLex (inl ⊥ : α oplus β) = ⊥
  证明: rfl
-/
theorem inl_bot [LE α] [OrderBot α] [LE β] : toLex (inl ⊥ : α oplus β) = ⊥ :=
  rfl

/--
Instance `orderTop` / 实例 `orderTop`

English:
instance orderTop
  signature: [LE α] [LE β] [OrderTop β]
  body: inr ⊤
  le_top := by
    rintro (a | b)
    · exact Lex.sep _ _
    · exact Lex.inr le_top

@[simp]

中文:
实例 orderTop
  签名: [LE α] [LE β] [有顶序 β]
  定义体: inr ⊤
  le_top := by
    rintro (a | b)
    · exact Lex.sep _ _
    · exact Lex.inr le_top

@[simp]
-/
instance orderTop [LE α] [LE β] [OrderTop β] :
    OrderTop (α oplusₗ β) where
  top := inr ⊤
  le_top := by
    rintro (a | b)
    · exact Lex.sep _ _
    · exact Lex.inr le_top

@[simp]
/--
theorem `inr_top` / 定理 `inr_top`

English:
theorem inr_top
  given: [LE α] [LE β] [OrderTop β]
  statement: toLex (inr ⊤ : α oplus β) = ⊤
  proof: rfl

中文:
定理 inr_top
  条件: [LE α] [LE β] [有顶序 β]
  结论: toLex (inr ⊤ : α oplus β) = ⊤
  证明: rfl
-/
theorem inr_top [LE α] [LE β] [OrderTop β] : toLex (inr ⊤ : α oplus β) = ⊤ :=
  rfl

/--
Instance `boundedOrder` / 实例 `boundedOrder`

English:
instance boundedOrder
  signature: [LE α] [LE β] [OrderBot α] [OrderTop β]
  body: { Lex.orderBot, Lex.orderTop with }

中文:
实例 boundedOrder
  签名: [LE α] [LE β] [有底序 α] [有顶序 β]
  定义体: { Lex.orderBot, Lex.orderTop with }

Depends on / 依赖: Lex.orderBot, Lex.orderTop, orderBot, orderTop
-/
instance boundedOrder [LE α] [LE β] [OrderBot α] [OrderTop β] : BoundedOrder (α oplusₗ β) :=
  { Lex.orderBot, Lex.orderTop with }

/--
Instance `noMinOrder` / 实例 `noMinOrder`

English:
instance noMinOrder
  signature: [LT α] [LT β] [NoMinOrder α] [NoMinOrder β]
  body: ⟨fun a =>
    match a with
    | inl a =>
      let ⟨b, h⟩ := exists_lt a
      ⟨toLex (inl b), inl_lt_inl_iff.2 h⟩
    | inr a =>
      let ⟨b, h⟩ := exists_lt a
      ⟨toLex (inr b), inr_lt_inr_iff.2 h⟩⟩

中文:
实例 noMinOrder
  签名: [LT α] [LT β] [NoMin序 α] [NoMin序 β]
  定义体: ⟨fun a =>
    match a with
    | inl a =>
      let ⟨b, h⟩ := exists_lt a
      ⟨toLex (inl b), inl_lt_inl_iff.2 h⟩
    | inr a =>
      let ⟨b, h⟩ := exists_lt a
      ⟨toLex (inr b), inr_lt_inr_iff.2 h⟩⟩

Depends on / 依赖: exists_lt, inl_lt_inl_iff, inr_lt_inr_iff
-/
instance noMinOrder [LT α] [LT β] [NoMinOrder α] [NoMinOrder β] : NoMinOrder (α oplusₗ β) :=
  ⟨fun a =>
    match a with
    | inl a =>
      let ⟨b, h⟩ := exists_lt a
      ⟨toLex (inl b), inl_lt_inl_iff.2 h⟩
    | inr a =>
      let ⟨b, h⟩ := exists_lt a
      ⟨toLex (inr b), inr_lt_inr_iff.2 h⟩⟩

/--
Instance `noMaxOrder` / 实例 `noMaxOrder`

English:
instance noMaxOrder
  signature: [LT α] [LT β] [NoMaxOrder α] [NoMaxOrder β]
  body: ⟨fun a =>
    match a with
    | inl a =>
      let ⟨b, h⟩ := exists_gt a
      ⟨toLex (inl b), inl_lt_inl_iff.2 h⟩
    | inr a =>
      let ⟨b, h⟩ := exists_gt a
      ⟨toLex (inr b), inr_lt_inr_iff.2 h⟩⟩

中文:
实例 noMaxOrder
  签名: [LT α] [LT β] [NoMax序 α] [NoMax序 β]
  定义体: ⟨fun a =>
    match a with
    | inl a =>
      let ⟨b, h⟩ := exists_gt a
      ⟨toLex (inl b), inl_lt_inl_iff.2 h⟩
    | inr a =>
      let ⟨b, h⟩ := exists_gt a
      ⟨toLex (inr b), inr_lt_inr_iff.2 h⟩⟩

Depends on / 依赖: exists_gt, inl_lt_inl_iff, inr_lt_inr_iff
-/
instance noMaxOrder [LT α] [LT β] [NoMaxOrder α] [NoMaxOrder β] : NoMaxOrder (α oplusₗ β) :=
  ⟨fun a =>
    match a with
    | inl a =>
      let ⟨b, h⟩ := exists_gt a
      ⟨toLex (inl b), inl_lt_inl_iff.2 h⟩
    | inr a =>
      let ⟨b, h⟩ := exists_gt a
      ⟨toLex (inr b), inr_lt_inr_iff.2 h⟩⟩

/--
Instance `noMinOrder_of_nonempty` / 实例 `noMinOrder_of_nonempty`

English:
instance noMinOrder_of_nonempty
  signature: [LT α] [LT β] [NoMinOrder α] [Nonempty α]
  body: ⟨fun a =>
    match a with
    | inl a =>
      let ⟨b, h⟩ := exists_lt a
      ⟨toLex (inl b), inl_lt_inl_iff.2 h⟩
    | inr _ => ⟨toLex (inl <| Classical.arbitrary α), inl_lt_inr _ _⟩⟩

中文:
实例 noMinOrder_of_nonempty
  签名: [LT α] [LT β] [NoMin序 α] [非空 α]
  定义体: ⟨fun a =>
    match a with
    | inl a =>
      let ⟨b, h⟩ := exists_lt a
      ⟨toLex (inl b), inl_lt_inl_iff.2 h⟩
    | inr _ => ⟨toLex (inl <| Classical.arbitrary α), inl_lt_inr _ _⟩⟩

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary, exists_lt, inl_lt_inl_iff, inl_lt_inr
-/
instance noMinOrder_of_nonempty [LT α] [LT β] [NoMinOrder α] [Nonempty α] : NoMinOrder (α oplusₗ β) :=
  ⟨fun a =>
    match a with
    | inl a =>
      let ⟨b, h⟩ := exists_lt a
      ⟨toLex (inl b), inl_lt_inl_iff.2 h⟩
    | inr _ => ⟨toLex (inl <| Classical.arbitrary α), inl_lt_inr _ _⟩⟩

/--
Instance `noMaxOrder_of_nonempty` / 实例 `noMaxOrder_of_nonempty`

English:
instance noMaxOrder_of_nonempty
  signature: [LT α] [LT β] [NoMaxOrder β] [Nonempty β]
  body: ⟨fun a =>
    match a with
    | inl _ => ⟨toLex (inr <| Classical.arbitrary β), inl_lt_inr _ _⟩
    | inr a =>
      let ⟨b, h⟩ := exists_gt a
      ⟨toLex (inr b), inr_lt_inr_iff.2 h⟩⟩

中文:
实例 noMaxOrder_of_nonempty
  签名: [LT α] [LT β] [NoMax序 β] [非空 β]
  定义体: ⟨fun a =>
    match a with
    | inl _ => ⟨toLex (inr <| Classical.arbitrary β), inl_lt_inr _ _⟩
    | inr a =>
      let ⟨b, h⟩ := exists_gt a
      ⟨toLex (inr b), inr_lt_inr_iff.2 h⟩⟩

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary, exists_gt, inl_lt_inr, inr_lt_inr_iff
-/
instance noMaxOrder_of_nonempty [LT α] [LT β] [NoMaxOrder β] [Nonempty β] : NoMaxOrder (α oplusₗ β) :=
  ⟨fun a =>
    match a with
    | inl _ => ⟨toLex (inr <| Classical.arbitrary β), inl_lt_inr _ _⟩
    | inr a =>
      let ⟨b, h⟩ := exists_gt a
      ⟨toLex (inr b), inr_lt_inr_iff.2 h⟩⟩

/--
Instance `denselyOrdered_of_noMaxOrder` / 实例 `denselyOrdered_of_noMaxOrder`

English:
instance denselyOrdered_of_noMaxOrder
  signature: [LT α] [LT β] [DenselyOrdered α] [DenselyOrdered β]
  body: ⟨fun a b h =>
    match a, b, h with
    | inl _, inl _, Lex.inl h =>
      let ⟨c, ha, hb⟩ := exists_between h
      ⟨toLex (inl c), inl_lt_inl_iff.2 ha, inl_lt_inl_iff.2 hb⟩
    | inl a, inr _, Lex.sep _ _ =>
      let ⟨c, h⟩ := exists_gt a
      ⟨toLex (inl c), inl_lt_inl_iff.2 h, inl_lt_inr _ _⟩
    | inr _, inr _, Lex.inr h =>
      let ⟨c, ha, hb⟩ := exists_between h
      ⟨toLex (inr c), inr_lt_inr_iff.2 ha, inr_lt_inr_iff.2 hb⟩⟩

中文:
实例 denselyOrdered_of_noMaxOrder
  签名: [LT α] [LT β] [稠密序 α] [稠密序 β]
  定义体: ⟨fun a b h =>
    match a, b, h with
    | inl _, inl _, Lex.inl h =>
      let ⟨c, ha, hb⟩ := exists_between h
      ⟨toLex (inl c), inl_lt_inl_iff.2 ha, inl_lt_inl_iff.2 hb⟩
    | inl a, inr _, Lex.sep _ _ =>
      let ⟨c, h⟩ := exists_gt a
      ⟨toLex (inl c), inl_lt_inl_iff.2 h, inl_lt_inr _ _⟩
    | inr _, inr _, Lex.inr h =>
      let ⟨c, ha, hb⟩ := exists_between h
      ⟨toLex (inr c), inr_lt_inr_iff.2 ha, inr_lt_inr_iff.2 hb⟩⟩

Depends on / 依赖: Lex.inl, Lex.inr, Lex.sep, exists_between, exists_gt, inl_lt_inl_iff, inl_lt_inr, inr_lt_inr_iff
-/
instance denselyOrdered_of_noMaxOrder [LT α] [LT β] [DenselyOrdered α] [DenselyOrdered β]
    [NoMaxOrder α] : DenselyOrdered (α oplusₗ β) :=
  ⟨fun a b h =>
    match a, b, h with
    | inl _, inl _, Lex.inl h =>
      let ⟨c, ha, hb⟩ := exists_between h
      ⟨toLex (inl c), inl_lt_inl_iff.2 ha, inl_lt_inl_iff.2 hb⟩
    | inl a, inr _, Lex.sep _ _ =>
      let ⟨c, h⟩ := exists_gt a
      ⟨toLex (inl c), inl_lt_inl_iff.2 h, inl_lt_inr _ _⟩
    | inr _, inr _, Lex.inr h =>
      let ⟨c, ha, hb⟩ := exists_between h
      ⟨toLex (inr c), inr_lt_inr_iff.2 ha, inr_lt_inr_iff.2 hb⟩⟩

/--
Instance `denselyOrdered_of_noMinOrder` / 实例 `denselyOrdered_of_noMinOrder`

English:
instance denselyOrdered_of_noMinOrder
  signature: [LT α] [LT β] [DenselyOrdered α] [DenselyOrdered β]
  body: ⟨fun a b h =>
    match a, b, h with
    | inl _, inl _, Lex.inl h =>
      let ⟨c, ha, hb⟩ := exists_between h
      ⟨toLex (inl c), inl_lt_inl_iff.2 ha, inl_lt_inl_iff.2 hb⟩
    | inl _, inr b, Lex.sep _ _ =>
      let ⟨c, h⟩ := exists_lt b
      ⟨toLex (inr c), inl_lt_inr _ _, inr_lt_inr_iff.2 h⟩
    | inr _, inr _, Lex.inr h =>
      let ⟨c, ha, hb⟩ := exists_between h
      ⟨toLex (inr c), inr_lt_inr_iff.2 ha, inr_lt_inr_iff.2 hb⟩⟩

中文:
实例 denselyOrdered_of_noMinOrder
  签名: [LT α] [LT β] [稠密序 α] [稠密序 β]
  定义体: ⟨fun a b h =>
    match a, b, h with
    | inl _, inl _, Lex.inl h =>
      let ⟨c, ha, hb⟩ := exists_between h
      ⟨toLex (inl c), inl_lt_inl_iff.2 ha, inl_lt_inl_iff.2 hb⟩
    | inl _, inr b, Lex.sep _ _ =>
      let ⟨c, h⟩ := exists_lt b
      ⟨toLex (inr c), inl_lt_inr _ _, inr_lt_inr_iff.2 h⟩
    | inr _, inr _, Lex.inr h =>
      let ⟨c, ha, hb⟩ := exists_between h
      ⟨toLex (inr c), inr_lt_inr_iff.2 ha, inr_lt_inr_iff.2 hb⟩⟩

Depends on / 依赖: Lex.inl, Lex.inr, Lex.sep, exists_between, exists_lt, inl_lt_inl_iff, inl_lt_inr, inr_lt_inr_iff
-/
instance denselyOrdered_of_noMinOrder [LT α] [LT β] [DenselyOrdered α] [DenselyOrdered β]
    [NoMinOrder β] : DenselyOrdered (α oplusₗ β) :=
  ⟨fun a b h =>
    match a, b, h with
    | inl _, inl _, Lex.inl h =>
      let ⟨c, ha, hb⟩ := exists_between h
      ⟨toLex (inl c), inl_lt_inl_iff.2 ha, inl_lt_inl_iff.2 hb⟩
    | inl _, inr b, Lex.sep _ _ =>
      let ⟨c, h⟩ := exists_lt b
      ⟨toLex (inr c), inl_lt_inr _ _, inr_lt_inr_iff.2 h⟩
    | inr _, inr _, Lex.inr h =>
      let ⟨c, ha, hb⟩ := exists_between h
      ⟨toLex (inr c), inr_lt_inr_iff.2 ha, inr_lt_inr_iff.2 hb⟩⟩

end Lex

end Sum

/-! ### Order isomorphisms -/


open OrderDual Sum

namespace OrderIso

variable {α₁ α₂ β₁ β₂ γ₁ γ₂ : Type*} [LE α] [LE β] [LE γ]
  [LE α₁] [LE α₂] [LE β₁] [LE β₂] [LE γ₁] [LE γ₂] (a : α) (b : β) (c : γ)

/-- `Equiv.sumCongr` promoted to an order isomorphism. -/
@[simps! apply]
/--
Definition of `sumCongr` / `sumCongr` 的定义

English:
definition sumCongr
  signature: (ea : α₁ ≃o α₂) (eb : β₁ ≃o β₂)
  body: .sumCongr ea eb
  map_rel_iff' := by aesop

@[simp]

中文:
定义 sumCongr
  签名: (ea : α₁ ≃o α₂) (eb : β₁ ≃o β₂)
  定义体: .sumCongr ea eb
  map_rel_iff' := by aesop

@[simp]

Depends on / 依赖: sumCongr
-/
def sumCongr (ea : α₁ ≃o α₂) (eb : β₁ ≃o β₂) : α₁ oplus β₁ ≃o α₂ oplus β₂ where
  toEquiv := .sumCongr ea eb
  map_rel_iff' := by aesop

@[simp]
/--
theorem `sumCongr_trans` / 定理 `sumCongr_trans`

English:
theorem sumCongr_trans
  given: (e₁ : α₁ ≃o β₁) (e₂ : α₂ ≃o β₂) (f₁ : β₁ ≃o γ₁) (f₂ : β₂ ≃o γ₂)
  proof: by
  ext; simp

@[simp]

中文:
定理 sumCongr_trans
  条件: (e₁ : α₁ ≃o β₁) (e₂ : α₂ ≃o β₂) (f₁ : β₁ ≃o γ₁) (f₂ : β₂ ≃o γ₂)
  证明: by
  ext; simp

@[simp]
-/
theorem sumCongr_trans (e₁ : α₁ ≃o β₁) (e₂ : α₂ ≃o β₂) (f₁ : β₁ ≃o γ₁) (f₂ : β₂ ≃o γ₂) :
    (e₁.sumCongr e₂).trans (f₁.sumCongr f₂) = (e₁.trans f₁).sumCongr (e₂.trans f₂) := by
  ext; simp

@[simp]
/--
theorem `sumCongr_symm` / 定理 `sumCongr_symm`

English:
theorem sumCongr_symm
  given: (ea : α₁ ≃o α₂) (eb : β₁ ≃o β₂)
  proof: rfl

@[simp]

中文:
定理 sumCongr_symm
  条件: (ea : α₁ ≃o α₂) (eb : β₁ ≃o β₂)
  证明: rfl

@[simp]
-/
theorem sumCongr_symm (ea : α₁ ≃o α₂) (eb : β₁ ≃o β₂) :
    (ea.sumCongr eb).symm = ea.symm.sumCongr eb.symm :=
  rfl

@[simp]
/--
theorem `sumCongr_refl` / 定理 `sumCongr_refl`

English:
theorem sumCongr_refl
  statement: sumCongr (.refl α) (.refl β) = .refl _
  proof: by
  ext; simp

中文:
定理 sumCongr_refl
  结论: sumCongr (.refl α) (.refl β) = .refl _
  证明: by
  ext; simp
-/
theorem sumCongr_refl : sumCongr (.refl α) (.refl β) = .refl _ := by
  ext; simp

/-- `Equiv.sumComm` promoted to an order isomorphism. -/
@[simps! apply]
/--
Definition of `sumComm` / `sumComm` 的定义

English:
definition sumComm
  signature: (α β : Type*) [LE α] [LE β]
  body: { Equiv.sumComm α β with map_rel_iff' := swap_le_swap_iff }

@[simp]

中文:
定义 sumComm
  签名: (α β : 类型) [LE α] [LE β]
  定义体: { Equiv.sumComm α β with map_rel_iff' := swap_le_swap_iff }

@[simp]

Depends on / 依赖: Equiv.sumComm, map_rel_iff, sumComm, swap_le_swap_iff
-/
def sumComm (α β : Type*) [LE α] [LE β] : α oplus β ≃o β oplus α :=
  { Equiv.sumComm α β with map_rel_iff' := swap_le_swap_iff }

@[simp]
/--
theorem `sumComm_symm` / 定理 `sumComm_symm`

English:
theorem sumComm_symm
  given: (α β : Type*) [LE α] [LE β]
  proof: rfl

中文:
定理 sumComm_symm
  条件: (α β : 类型) [LE α] [LE β]
  证明: rfl
-/
theorem sumComm_symm (α β : Type*) [LE α] [LE β] :
    (OrderIso.sumComm α β).symm = OrderIso.sumComm β α :=
  rfl

/--
Definition of `sumAssoc` / `sumAssoc` 的定义

English:
definition sumAssoc
  signature: (α β γ : Type*) [LE α] [LE β] [LE γ]
  body: { Equiv.sumAssoc α β γ with
    map_rel_iff' := fun {a b} => by
      rcases a with ((_ | _) | _) <;> rcases b with ((_ | _) | _) <;>
      simp [Equiv.sumAssoc] }

@[simp]

中文:
定义 sumAssoc
  签名: (α β γ : 类型) [LE α] [LE β] [LE γ]
  定义体: { Equiv.sumAssoc α β γ with
    map_rel_iff' := fun {a b} => by
      rcases a with ((_ | _) | _) <;> rcases b with ((_ | _) | _) <;>
      simp [Equiv.sumAssoc] }

@[simp]

Depends on / 依赖: Equiv.sumAssoc, map_rel_iff, sumAssoc
-/
def sumAssoc (α β γ : Type*) [LE α] [LE β] [LE γ] : (α oplus β) oplus γ ≃o α oplus (β oplus γ) :=
  { Equiv.sumAssoc α β γ with
    map_rel_iff' := fun {a b} => by
      rcases a with ((_ | _) | _) <;> rcases b with ((_ | _) | _) <;>
      simp [Equiv.sumAssoc] }

@[simp]
/--
theorem `sumAssoc_apply_inl_inl` / 定理 `sumAssoc_apply_inl_inl`

English:
theorem sumAssoc_apply_inl_inl
  statement: sumAssoc α β γ (inl (inl a)) = inl a
  proof: rfl

@[simp]

中文:
定理 sumAssoc_apply_inl_inl
  结论: sumAssoc α β γ (inl (inl a)) = inl a
  证明: rfl

@[simp]
-/
theorem sumAssoc_apply_inl_inl : sumAssoc α β γ (inl (inl a)) = inl a :=
  rfl

@[simp]
/--
theorem `sumAssoc_apply_inl_inr` / 定理 `sumAssoc_apply_inl_inr`

English:
theorem sumAssoc_apply_inl_inr
  statement: sumAssoc α β γ (inl (inr b)) = inr (inl b)
  proof: rfl

@[simp]

中文:
定理 sumAssoc_apply_inl_inr
  结论: sumAssoc α β γ (inl (inr b)) = inr (inl b)
  证明: rfl

@[simp]
-/
theorem sumAssoc_apply_inl_inr : sumAssoc α β γ (inl (inr b)) = inr (inl b) :=
  rfl

@[simp]
/--
theorem `sumAssoc_apply_inr` / 定理 `sumAssoc_apply_inr`

English:
theorem sumAssoc_apply_inr
  statement: sumAssoc α β γ (inr c) = inr (inr c)
  proof: rfl

@[simp]

中文:
定理 sumAssoc_apply_inr
  结论: sumAssoc α β γ (inr c) = inr (inr c)
  证明: rfl

@[simp]
-/
theorem sumAssoc_apply_inr : sumAssoc α β γ (inr c) = inr (inr c) :=
  rfl

@[simp]
/--
theorem `sumAssoc_symm_apply_inl` / 定理 `sumAssoc_symm_apply_inl`

English:
theorem sumAssoc_symm_apply_inl
  statement: (sumAssoc α β γ).symm (inl a) = inl (inl a)
  proof: rfl

@[simp]

中文:
定理 sumAssoc_symm_apply_inl
  结论: (sumAssoc α β γ).symm (inl a) = inl (inl a)
  证明: rfl

@[simp]
-/
theorem sumAssoc_symm_apply_inl : (sumAssoc α β γ).symm (inl a) = inl (inl a) :=
  rfl

@[simp]
/--
theorem `sumAssoc_symm_apply_inr_inl` / 定理 `sumAssoc_symm_apply_inr_inl`

English:
theorem sumAssoc_symm_apply_inr_inl
  statement: (sumAssoc α β γ).symm (inr (inl b)) = inl (inr b)
  proof: rfl

@[simp]

中文:
定理 sumAssoc_symm_apply_inr_inl
  结论: (sumAssoc α β γ).symm (inr (inl b)) = inl (inr b)
  证明: rfl

@[simp]
-/
theorem sumAssoc_symm_apply_inr_inl : (sumAssoc α β γ).symm (inr (inl b)) = inl (inr b) :=
  rfl

@[simp]
/--
theorem `sumAssoc_symm_apply_inr_inr` / 定理 `sumAssoc_symm_apply_inr_inr`

English:
theorem sumAssoc_symm_apply_inr_inr
  statement: (sumAssoc α β γ).symm (inr (inr c)) = inr c
  proof: rfl

中文:
定理 sumAssoc_symm_apply_inr_inr
  结论: (sumAssoc α β γ).symm (inr (inr c)) = inr c
  证明: rfl
-/
theorem sumAssoc_symm_apply_inr_inr : (sumAssoc α β γ).symm (inr (inr c)) = inr c :=
  rfl

/--
Definition of `sumDualDistrib` / `sumDualDistrib` 的定义

English:
definition sumDualDistrib
  signature: (α β : Type*) [LE α] [LE β]
  body: { Equiv.refl _ with
    map_rel_iff' := by
      rintro (a | a) (b | b)
      · change inl (toDual a) <= inl (toDual b) ↔ toDual (inl a) <= toDual (inl b)
        simp [toDual_le_toDual, inl_le_inl_iff]
      · exact iff_of_false (@not_inl_le_inr (OrderDual β) (OrderDual α) _ _ _ _) not_inr_le_inl
      · exact iff_of_false (@not_inr_le_inl (OrderDual α) (OrderDual β) _ _ _ _) not_inl_le_inr
      · change inr (toDual a) <= inr (toDual b) ↔ toDual (inr a) <= toDual (inr b)
        simp [toDual_le_toDual, inr_le_inr_iff] }

@[simp]

中文:
定义 sumDualDistrib
  签名: (α β : 类型) [LE α] [LE β]
  定义体: { Equiv.refl _ with
    map_rel_iff' := by
      rintro (a | a) (b | b)
      · change inl (toDual a) <= inl (toDual b) ↔ toDual (inl a) <= toDual (inl b)
        simp [toDual_le_toDual, inl_le_inl_iff]
      · exact iff_of_false (@not_inl_le_inr (OrderDual β) (OrderDual α) _ _ _ _) not_inr_le_inl
      · exact iff_of_false (@not_inr_le_inl (OrderDual α) (OrderDual β) _ _ _ _) not_inl_le_inr
      · change inr (toDual a) <= inr (toDual b) ↔ toDual (inr a) <= toDual (inr b)
        simp [toDual_le_toDual, inr_le_inr_iff] }

@[simp]

Depends on / 依赖: Equiv.refl, OrderDual, iff_of_false, inl_le_inl_iff, inr_le_inr_iff, map_rel_iff, not_inl_le_inr, not_inr_le_inl, toDual, toDual_le_toDual
-/
def sumDualDistrib (α β : Type*) [LE α] [LE β] : (α oplus β)ᵒᵈ ≃o αᵒᵈ oplus βᵒᵈ :=
  { Equiv.refl _ with
    map_rel_iff' := by
      rintro (a | a) (b | b)
      · change inl (toDual a) <= inl (toDual b) ↔ toDual (inl a) <= toDual (inl b)
        simp [toDual_le_toDual, inl_le_inl_iff]
      · exact iff_of_false (@not_inl_le_inr (OrderDual β) (OrderDual α) _ _ _ _) not_inr_le_inl
      · exact iff_of_false (@not_inr_le_inl (OrderDual α) (OrderDual β) _ _ _ _) not_inl_le_inr
      · change inr (toDual a) <= inr (toDual b) ↔ toDual (inr a) <= toDual (inr b)
        simp [toDual_le_toDual, inr_le_inr_iff] }

@[simp]
/--
theorem `sumDualDistrib_inl` / 定理 `sumDualDistrib_inl`

English:
theorem sumDualDistrib_inl
  statement: sumDualDistrib α β (toDual (inl a)) = inl (toDual a)
  proof: rfl

@[simp]

中文:
定理 sumDualDistrib_inl
  结论: sumDualDistrib α β (toDual (inl a)) = inl (toDual a)
  证明: rfl

@[simp]
-/
theorem sumDualDistrib_inl : sumDualDistrib α β (toDual (inl a)) = inl (toDual a) :=
  rfl

@[simp]
/--
theorem `sumDualDistrib_inr` / 定理 `sumDualDistrib_inr`

English:
theorem sumDualDistrib_inr
  statement: sumDualDistrib α β (toDual (inr b)) = inr (toDual b)
  proof: rfl

@[simp]

中文:
定理 sumDualDistrib_inr
  结论: sumDualDistrib α β (toDual (inr b)) = inr (toDual b)
  证明: rfl

@[simp]
-/
theorem sumDualDistrib_inr : sumDualDistrib α β (toDual (inr b)) = inr (toDual b) :=
  rfl

@[simp]
/--
theorem `sumDualDistrib_symm_inl` / 定理 `sumDualDistrib_symm_inl`

English:
theorem sumDualDistrib_symm_inl
  statement: (sumDualDistrib α β).symm (inl (toDual a)) = toDual (inl a)
  proof: rfl

@[simp]

中文:
定理 sumDualDistrib_symm_inl
  结论: (sumDualDistrib α β).symm (inl (toDual a)) = toDual (inl a)
  证明: rfl

@[simp]
-/
theorem sumDualDistrib_symm_inl : (sumDualDistrib α β).symm (inl (toDual a)) = toDual (inl a) :=
  rfl

@[simp]
/--
theorem `sumDualDistrib_symm_inr` / 定理 `sumDualDistrib_symm_inr`

English:
theorem sumDualDistrib_symm_inr
  statement: (sumDualDistrib α β).symm (inr (toDual b)) = toDual (inr b)
  proof: rfl

中文:
定理 sumDualDistrib_symm_inr
  结论: (sumDualDistrib α β).symm (inr (toDual b)) = toDual (inr b)
  证明: rfl
-/
theorem sumDualDistrib_symm_inr : (sumDualDistrib α β).symm (inr (toDual b)) = toDual (inr b) :=
  rfl

/-- `Equiv.sumCongr` promoted to an order isomorphism between lexicographic sums. -/
@[simps! apply]
/--
Definition of `sumLexCongr` / `sumLexCongr` 的定义

English:
definition sumLexCongr
  signature: (ea : α₁ ≃o α₂) (eb : β₁ ≃o β₂)
  body: ofLex.trans ((Equiv.sumCongr ea eb).trans toLex)
  map_rel_iff' := by simp_rw [Lex.forall]; rintro (a | a) (b | b) <;> simp

@[simp]

中文:
定义 sumLexCongr
  签名: (ea : α₁ ≃o α₂) (eb : β₁ ≃o β₂)
  定义体: ofLex.trans ((Equiv.sumCongr ea eb).trans toLex)
  map_rel_iff' := by simp_rw [Lex.forall]; rintro (a | a) (b | b) <;> simp

@[simp]

Depends on / 依赖: Equiv.sumCongr, ofLex.trans, sumCongr
-/
def sumLexCongr (ea : α₁ ≃o α₂) (eb : β₁ ≃o β₂) : α₁ oplusₗ β₁ ≃o α₂ oplusₗ β₂ where
  toEquiv := ofLex.trans ((Equiv.sumCongr ea eb).trans toLex)
  map_rel_iff' := by simp_rw [Lex.forall]; rintro (a | a) (b | b) <;> simp

@[simp]
/--
theorem `sumLexCongr_trans` / 定理 `sumLexCongr_trans`

English:
theorem sumLexCongr_trans
  given: (e₁ : α₁ ≃o β₁) (e₂ : α₂ ≃o β₂) (f₁ : β₁ ≃o γ₁) (f₂ : β₂ ≃o γ₂)
  proof: by
  ext; simp

@[simp]

中文:
定理 sumLexCongr_trans
  条件: (e₁ : α₁ ≃o β₁) (e₂ : α₂ ≃o β₂) (f₁ : β₁ ≃o γ₁) (f₂ : β₂ ≃o γ₂)
  证明: by
  ext; simp

@[simp]
-/
theorem sumLexCongr_trans (e₁ : α₁ ≃o β₁) (e₂ : α₂ ≃o β₂) (f₁ : β₁ ≃o γ₁) (f₂ : β₂ ≃o γ₂) :
    (e₁.sumLexCongr e₂).trans (f₁.sumLexCongr f₂) = (e₁.trans f₁).sumLexCongr (e₂.trans f₂) := by
  ext; simp

@[simp]
/--
theorem `sumLexCongr_symm` / 定理 `sumLexCongr_symm`

English:
theorem sumLexCongr_symm
  given: (ea : α₁ ≃o α₂) (eb : β₁ ≃o β₂)
  proof: rfl

@[simp]

中文:
定理 sumLexCongr_symm
  条件: (ea : α₁ ≃o α₂) (eb : β₁ ≃o β₂)
  证明: rfl

@[simp]
-/
theorem sumLexCongr_symm (ea : α₁ ≃o α₂) (eb : β₁ ≃o β₂) :
    (ea.sumLexCongr eb).symm = ea.symm.sumLexCongr eb.symm :=
  rfl

@[simp]
/--
theorem `sumLexCongr_refl` / 定理 `sumLexCongr_refl`

English:
theorem sumLexCongr_refl
  statement: sumLexCongr (.refl α) (.refl β) = .refl _
  proof: by
  ext; simp

中文:
定理 sumLexCongr_refl
  结论: sumLexCongr (.refl α) (.refl β) = .refl _
  证明: by
  ext; simp
-/
theorem sumLexCongr_refl : sumLexCongr (.refl α) (.refl β) = .refl _ := by
  ext; simp

/--
Definition of `sumLexAssoc` / `sumLexAssoc` 的定义

English:
definition sumLexAssoc
  signature: (α β γ : Type*) [LE α] [LE β] [LE γ]
  body: { Equiv.sumAssoc α β γ with
    map_rel_iff' := fun {a b} =>
      ⟨fun h =>
        match a, b, h with
| inlₗ (inlₗ _), inlₗ (inlₗ _), Lex.inl h => Lex.inl Lex.inl h
| inlₗ (inlₗ _), inlₗ (inrₗ _), Lex.sep _ _ => Lex.inl Lex.sep _ _
        | inlₗ (inlₗ _), inrₗ _, Lex.sep _ _ => Lex.sep _ _
| inlₗ (inrₗ _), inlₗ (inrₗ _), Lex.inr (Lex.inl h) => Lex.inl Lex.inr h
        | inlₗ (inrₗ _), inrₗ _, Lex.inr (Lex.sep _ _) => Lex.sep _ _
        | inrₗ _, inrₗ _, Lex.inr (Lex.inr h) => Lex.inr h,
        fun h =>
        match a, b, h with
        | inlₗ (inlₗ _), inlₗ (inlₗ _), Lex.inl (Lex.inl h) => Lex.inl h
        | inlₗ (inlₗ _), inlₗ (inrₗ _), Lex.inl (Lex.sep _ _) => Lex.sep _ _
        | inlₗ (inlₗ _), inrₗ _, Lex.sep _ _ => Lex.sep _ _
| inlₗ (inrₗ _), inlₗ (inrₗ _), Lex.inl (Lex.inr h) => Lex.inr Lex.inl h
| inlₗ (inrₗ _), inrₗ _, Lex.sep _ _ => Lex.inr Lex.sep _ _
| inrₗ _, inrₗ _, Lex.inr h => Lex.inr Lex.inr h⟩ }

@[simp]

中文:
定义 sumLexAssoc
  签名: (α β γ : 类型) [LE α] [LE β] [LE γ]
  定义体: { Equiv.sumAssoc α β γ with
    map_rel_iff' := fun {a b} =>
      ⟨fun h =>
        match a, b, h with
| inlₗ (inlₗ _), inlₗ (inlₗ _), Lex.inl h => Lex.inl Lex.inl h
| inlₗ (inlₗ _), inlₗ (inrₗ _), Lex.sep _ _ => Lex.inl Lex.sep _ _
        | inlₗ (inlₗ _), inrₗ _, Lex.sep _ _ => Lex.sep _ _
| inlₗ (inrₗ _), inlₗ (inrₗ _), Lex.inr (Lex.inl h) => Lex.inl Lex.inr h
        | inlₗ (inrₗ _), inrₗ _, Lex.inr (Lex.sep _ _) => Lex.sep _ _
        | inrₗ _, inrₗ _, Lex.inr (Lex.inr h) => Lex.inr h,
        fun h =>
        match a, b, h with
        | inlₗ (inlₗ _), inlₗ (inlₗ _), Lex.inl (Lex.inl h) => Lex.inl h
        | inlₗ (inlₗ _), inlₗ (inrₗ _), Lex.inl (Lex.sep _ _) => Lex.sep _ _
        | inlₗ (inlₗ _), inrₗ _, Lex.sep _ _ => Lex.sep _ _
| inlₗ (inrₗ _), inlₗ (inrₗ _), Lex.inl (Lex.inr h) => Lex.inr Lex.inl h
| inlₗ (inrₗ _), inrₗ _, Lex.sep _ _ => Lex.inr Lex.sep _ _
| inrₗ _, inrₗ _, Lex.inr h => Lex.inr Lex.inr h⟩ }

@[simp]

Depends on / 依赖: Equiv.sumAssoc, Lex.inl, Lex.inr, Lex.sep, _stabilizer, eq_one_of_smul_eq_one, exists_smul_eq, isComplement, map_rel_iff, sumAssoc
-/
def sumLexAssoc (α β γ : Type*) [LE α] [LE β] [LE γ] : (α oplusₗ β) oplusₗ γ ≃o α oplusₗ β oplusₗ γ :=
  { Equiv.sumAssoc α β γ with
    map_rel_iff' := fun {a b} =>
      ⟨fun h =>
        match a, b, h with
| inlₗ (inlₗ _), inlₗ (inlₗ _), Lex.inl h => Lex.inl Lex.inl h
| inlₗ (inlₗ _), inlₗ (inrₗ _), Lex.sep _ _ => Lex.inl Lex.sep _ _
        | inlₗ (inlₗ _), inrₗ _, Lex.sep _ _ => Lex.sep _ _
| inlₗ (inrₗ _), inlₗ (inrₗ _), Lex.inr (Lex.inl h) => Lex.inl Lex.inr h
        | inlₗ (inrₗ _), inrₗ _, Lex.inr (Lex.sep _ _) => Lex.sep _ _
        | inrₗ _, inrₗ _, Lex.inr (Lex.inr h) => Lex.inr h,
        fun h =>
        match a, b, h with
        | inlₗ (inlₗ _), inlₗ (inlₗ _), Lex.inl (Lex.inl h) => Lex.inl h
        | inlₗ (inlₗ _), inlₗ (inrₗ _), Lex.inl (Lex.sep _ _) => Lex.sep _ _
        | inlₗ (inlₗ _), inrₗ _, Lex.sep _ _ => Lex.sep _ _
| inlₗ (inrₗ _), inlₗ (inrₗ _), Lex.inl (Lex.inr h) => Lex.inr Lex.inl h
| inlₗ (inrₗ _), inrₗ _, Lex.sep _ _ => Lex.inr Lex.sep _ _
| inrₗ _, inrₗ _, Lex.inr h => Lex.inr Lex.inr h⟩ }

@[simp]
/--
theorem `sumLexAssoc_apply_inl_inl` / 定理 `sumLexAssoc_apply_inl_inl`

English:
theorem sumLexAssoc_apply_inl_inl
  proof: rfl

@[simp]

中文:
定理 sumLexAssoc_apply_inl_inl
  证明: rfl

@[simp]
-/
theorem sumLexAssoc_apply_inl_inl :
    sumLexAssoc α β γ (toLex <| inl <| toLex <| inl a) = toLex (inl a) :=
  rfl

@[simp]
/--
theorem `sumLexAssoc_apply_inl_inr` / 定理 `sumLexAssoc_apply_inl_inr`

English:
theorem sumLexAssoc_apply_inl_inr
  proof: rfl

@[simp]

中文:
定理 sumLexAssoc_apply_inl_inr
  证明: rfl

@[simp]
-/
theorem sumLexAssoc_apply_inl_inr :
    sumLexAssoc α β γ (toLex <| inl <| toLex <| inr b) = toLex (inr <| toLex <| inl b) :=
  rfl

@[simp]
/--
theorem `sumLexAssoc_apply_inr` / 定理 `sumLexAssoc_apply_inr`

English:
theorem sumLexAssoc_apply_inr
  proof: rfl

@[simp]

中文:
定理 sumLexAssoc_apply_inr
  证明: rfl

@[simp]
-/
theorem sumLexAssoc_apply_inr :
    sumLexAssoc α β γ (toLex <| inr c) = toLex (inr <| toLex <| inr c) :=
  rfl

@[simp]
/--
theorem `sumLexAssoc_symm_apply_inl` / 定理 `sumLexAssoc_symm_apply_inl`

English:
theorem sumLexAssoc_symm_apply_inl
  statement: (sumLexAssoc α β γ).symm (inl a) = inl (inl a)
  proof: rfl

@[simp]

中文:
定理 sumLexAssoc_symm_apply_inl
  结论: (sumLexAssoc α β γ).symm (inl a) = inl (inl a)
  证明: rfl

@[simp]
-/
theorem sumLexAssoc_symm_apply_inl : (sumLexAssoc α β γ).symm (inl a) = inl (inl a) :=
  rfl

@[simp]
/--
theorem `sumLexAssoc_symm_apply_inr_inl` / 定理 `sumLexAssoc_symm_apply_inr_inl`

English:
theorem sumLexAssoc_symm_apply_inr_inl
  statement: (sumLexAssoc α β γ).symm (inr (inl b)) = inl (inr b)
  proof: rfl

@[simp]

中文:
定理 sumLexAssoc_symm_apply_inr_inl
  结论: (sumLexAssoc α β γ).symm (inr (inl b)) = inl (inr b)
  证明: rfl

@[simp]
-/
theorem sumLexAssoc_symm_apply_inr_inl : (sumLexAssoc α β γ).symm (inr (inl b)) = inl (inr b) :=
  rfl

@[simp]
/--
theorem `sumLexAssoc_symm_apply_inr_inr` / 定理 `sumLexAssoc_symm_apply_inr_inr`

English:
theorem sumLexAssoc_symm_apply_inr_inr
  statement: (sumLexAssoc α β γ).symm (inr (inr c)) = inr c
  proof: rfl

中文:
定理 sumLexAssoc_symm_apply_inr_inr
  结论: (sumLexAssoc α β γ).symm (inr (inr c)) = inr c
  证明: rfl
-/
theorem sumLexAssoc_symm_apply_inr_inr : (sumLexAssoc α β γ).symm (inr (inr c)) = inr c :=
  rfl

/--
Definition of `sumLexDualAntidistrib` / `sumLexDualAntidistrib` 的定义

English:
definition sumLexDualAntidistrib
  signature: (α β : Type*) [LE α] [LE β]
  body: { Equiv.sumComm α β with
    map_rel_iff' := fun {a b} => by
      rcases a with (a | a) <;> rcases b with (b | b)
      · change
          toLex (inr <| toDual a) <= toLex (inr <| toDual b) ↔
            toDual (toLex <| inl a) <= toDual (toLex <| inl b)
        simp [toDual_le_toDual]
      · exact iff_of_false (@Lex.not_inr_le_inl (OrderDual β) (OrderDual α) _ _ _ _)
          Lex.not_inr_le_inl
      · exact iff_of_true (@Lex.inl_le_inr (OrderDual β) (OrderDual α) _ _ _ _)
          (Lex.inl_le_inr _ _)
      · change
          toLex (inl <| toDual a) <= toLex (inl <| toDual b) ↔
            toDual (toLex <| inr a) <= toDual (toLex <| inr b)
        simp [toDual_le_toDual] }

@[simp]

中文:
定义 sumLexDualAntidistrib
  签名: (α β : 类型) [LE α] [LE β]
  定义体: { Equiv.sumComm α β with
    map_rel_iff' := fun {a b} => by
      rcases a with (a | a) <;> rcases b with (b | b)
      · change
          toLex (inr <| toDual a) <= toLex (inr <| toDual b) ↔
            toDual (toLex <| inl a) <= toDual (toLex <| inl b)
        simp [toDual_le_toDual]
      · exact iff_of_false (@Lex.not_inr_le_inl (OrderDual β) (OrderDual α) _ _ _ _)
          Lex.not_inr_le_inl
      · exact iff_of_true (@Lex.inl_le_inr (OrderDual β) (OrderDual α) _ _ _ _)
          (Lex.inl_le_inr _ _)
      · change
          toLex (inl <| toDual a) <= toLex (inl <| toDual b) ↔
            toDual (toLex <| inr a) <= toDual (toLex <| inr b)
        simp [toDual_le_toDual] }

@[simp]

Depends on / 依赖: Equiv.sumComm, Lex.inl_le_inr, Lex.not_inr_le_inl, OrderDual, iff_of_false, iff_of_true, inl_le_inr, map_rel_iff, not_inr_le_inl, sumComm, toDual, toDual_le_toDual
-/
def sumLexDualAntidistrib (α β : Type*) [LE α] [LE β] : (α oplusₗ β)ᵒᵈ ≃o βᵒᵈ oplusₗ αᵒᵈ :=
  { Equiv.sumComm α β with
    map_rel_iff' := fun {a b} => by
      rcases a with (a | a) <;> rcases b with (b | b)
      · change
          toLex (inr <| toDual a) <= toLex (inr <| toDual b) ↔
            toDual (toLex <| inl a) <= toDual (toLex <| inl b)
        simp [toDual_le_toDual]
      · exact iff_of_false (@Lex.not_inr_le_inl (OrderDual β) (OrderDual α) _ _ _ _)
          Lex.not_inr_le_inl
      · exact iff_of_true (@Lex.inl_le_inr (OrderDual β) (OrderDual α) _ _ _ _)
          (Lex.inl_le_inr _ _)
      · change
          toLex (inl <| toDual a) <= toLex (inl <| toDual b) ↔
            toDual (toLex <| inr a) <= toDual (toLex <| inr b)
        simp [toDual_le_toDual] }

@[simp]
/--
theorem `sumLexDualAntidistrib_inl` / 定理 `sumLexDualAntidistrib_inl`

English:
theorem sumLexDualAntidistrib_inl
  proof: rfl

@[simp]

中文:
定理 sumLexDualAntidistrib_inl
  证明: rfl

@[simp]
-/
theorem sumLexDualAntidistrib_inl :
    sumLexDualAntidistrib α β (toDual (inl a)) = inr (toDual a) :=
  rfl

@[simp]
/--
theorem `sumLexDualAntidistrib_inr` / 定理 `sumLexDualAntidistrib_inr`

English:
theorem sumLexDualAntidistrib_inr
  proof: rfl

@[simp]

中文:
定理 sumLexDualAntidistrib_inr
  证明: rfl

@[simp]
-/
theorem sumLexDualAntidistrib_inr :
    sumLexDualAntidistrib α β (toDual (inr b)) = inl (toDual b) :=
  rfl

@[simp]
/--
theorem `sumLexDualAntidistrib_symm_inl` / 定理 `sumLexDualAntidistrib_symm_inl`

English:
theorem sumLexDualAntidistrib_symm_inl
  proof: rfl

@[simp]

中文:
定理 sumLexDualAntidistrib_symm_inl
  证明: rfl

@[simp]
-/
theorem sumLexDualAntidistrib_symm_inl :
    (sumLexDualAntidistrib α β).symm (inl (toDual b)) = toDual (inr b) :=
  rfl

@[simp]
/--
theorem `sumLexDualAntidistrib_symm_inr` / 定理 `sumLexDualAntidistrib_symm_inr`

English:
theorem sumLexDualAntidistrib_symm_inr
  proof: rfl

中文:
定理 sumLexDualAntidistrib_symm_inr
  证明: rfl
-/
theorem sumLexDualAntidistrib_symm_inr :
    (sumLexDualAntidistrib α β).symm (inr (toDual a)) = toDual (inl a) :=
  rfl

/--
Definition of `sumLexEmpty` / `sumLexEmpty` 的定义

English:
definition sumLexEmpty
  signature: [IsEmpty β]
  body: RelIso.sumLexEmpty ..

中文:
定义 sumLexEmpty
  签名: [是空 β]
  定义体: RelIso.sumLexEmpty ..

Depends on / 依赖: RelIso, RelIso.sumLexEmpty, sumLexEmpty
-/
def sumLexEmpty [IsEmpty β] : Lex (α oplus β) ≃o α :=
  RelIso.sumLexEmpty ..

/--
Definition of `emptySumLex` / `emptySumLex` 的定义

English:
definition emptySumLex
  signature: [IsEmpty β]
  body: RelIso.emptySumLex ..

@[simp]

中文:
定义 emptySumLex
  签名: [是空 β]
  定义体: RelIso.emptySumLex ..

@[simp]

Depends on / 依赖: RelIso, RelIso.emptySumLex, emptySumLex
-/
def emptySumLex [IsEmpty β] : Lex (β oplus α) ≃o α :=
  RelIso.emptySumLex ..

@[simp]
/--
lemma `sumLexEmpty_apply_inl` / 引理 `sumLexEmpty_apply_inl`

English:
lemma sumLexEmpty_apply_inl
  given: [IsEmpty β] (x : α)
  statement: sumLexEmpty (β := β) (toLex <| .inl x) = x
  proof: rfl

@[simp]

中文:
引理 sumLexEmpty_apply_inl
  条件: [是空 β] (x : α)
  结论: sumLexEmpty (β := β) (toLex <| .inl x) = x
  证明: rfl

@[simp]
-/
lemma sumLexEmpty_apply_inl [IsEmpty β] (x : α) : sumLexEmpty (β := β) (toLex <| .inl x) = x :=
  rfl

@[simp]
/--
lemma `emptySumLex_apply_inr` / 引理 `emptySumLex_apply_inr`

English:
lemma emptySumLex_apply_inr
  given: [IsEmpty β] (x : α)
  statement: emptySumLex (β := β) (toLex <| .inr x) = x
  proof: rfl

中文:
引理 emptySumLex_apply_inr
  条件: [是空 β] (x : α)
  结论: emptySumLex (β := β) (toLex <| .inr x) = x
  证明: rfl
-/
lemma emptySumLex_apply_inr [IsEmpty β] (x : α) : emptySumLex (β := β) (toLex <| .inr x) = x :=
  rfl

end OrderIso

variable [LE α]

namespace WithBot

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `orderIsoPUnitSumLex` / `orderIsoPUnitSumLex` 的定义

English:
definition orderIsoPUnitSumLex
  signature: : WithBot α ≃o PUnit oplusₗ α
  body: ⟨(Equiv.optionEquivSumPUnit α).trans (Equiv.sumComm _ _).trans toLex, fun {a b} => by
    simp only [Equiv.optionEquivSumPUnit, Option.elim, Equiv.trans_apply, Equiv.coe_fn_mk,
      Equiv.sumComm_apply, swap, Lex.toLex_le_toLex, le_refl]
    cases a <;> cases b
    · simp only [elim_inr, lex_inl_inl, bot_le]
    · simp only [elim_inr, elim_inl, Lex.sep, bot_le]
    · simp only [elim_inl, elim_inr, lex_inr_inl, false_iff]
      exact not_coe_le_bot _
    · simp only [elim_inl, lex_inr_inr, coe_le_coe]
  ⟩

@[simp]

中文:
定义 orderIsoPUnitSumLex
  签名: : WithBot α ≃o 命题单元 oplusₗ α
  定义体: ⟨(Equiv.optionEquivSumPUnit α).trans (Equiv.sumComm _ _).trans toLex, fun {a b} => by
    simp only [Equiv.optionEquivSumPUnit, Option.elim, Equiv.trans_apply, Equiv.coe_fn_mk,
      Equiv.sumComm_apply, swap, Lex.toLex_le_toLex, le_refl]
    cases a <;> cases b
    · simp only [elim_inr, lex_inl_inl, bot_le]
    · simp only [elim_inr, elim_inl, Lex.sep, bot_le]
    · simp only [elim_inl, elim_inr, lex_inr_inl, false_iff]
      exact not_coe_le_bot _
    · simp only [elim_inl, lex_inr_inr, coe_le_coe]
  ⟩

@[simp]

Depends on / 依赖: Equiv.coe_fn_mk, Equiv.optionEquivSumPUnit, Equiv.sumComm, Equiv.sumComm_apply, Equiv.trans_apply, Lex.sep, Lex.toLex_le_toLex, Option.elim, bot_le, coe_fn_mk, coe_le_coe, elim_inl, elim_inr, false_iff, le_refl, lex_inl_inl, lex_inr_inl, lex_inr_inr, not_coe_le_bot, optionEquivSumPUnit
-/
def orderIsoPUnitSumLex : WithBot α ≃o PUnit oplusₗ α :=
⟨(Equiv.optionEquivSumPUnit α).trans (Equiv.sumComm _ _).trans toLex, fun {a b} => by
    simp only [Equiv.optionEquivSumPUnit, Option.elim, Equiv.trans_apply, Equiv.coe_fn_mk,
      Equiv.sumComm_apply, swap, Lex.toLex_le_toLex, le_refl]
    cases a <;> cases b
    · simp only [elim_inr, lex_inl_inl, bot_le]
    · simp only [elim_inr, elim_inl, Lex.sep, bot_le]
    · simp only [elim_inl, elim_inr, lex_inr_inl, false_iff]
      exact not_coe_le_bot _
    · simp only [elim_inl, lex_inr_inr, coe_le_coe]
  ⟩

@[simp]
/--
theorem `orderIsoPUnitSumLex_bot` / 定理 `orderIsoPUnitSumLex_bot`

English:
theorem orderIsoPUnitSumLex_bot
  statement: @orderIsoPUnitSumLex α _ ⊥ = toLex (inl PUnit.unit)
  proof: rfl

@[simp]

中文:
定理 orderIsoPUnitSumLex_bot
  结论: @orderIsoPUnitSumLex α _ ⊥ = toLex (inl 命题单元.unit)
  证明: rfl

@[simp]
-/
theorem orderIsoPUnitSumLex_bot : @orderIsoPUnitSumLex α _ ⊥ = toLex (inl PUnit.unit) :=
  rfl

@[simp]
/--
theorem `orderIsoPUnitSumLex_toLex` / 定理 `orderIsoPUnitSumLex_toLex`

English:
theorem orderIsoPUnitSumLex_toLex
  given: (a : α)
  statement: orderIsoPUnitSumLex ↑a = toLex (inr a)
  proof: rfl

@[simp]

中文:
定理 orderIsoPUnitSumLex_toLex
  条件: (a : α)
  结论: orderIsoPUnitSumLex ↑a = toLex (inr a)
  证明: rfl

@[simp]
-/
theorem orderIsoPUnitSumLex_toLex (a : α) : orderIsoPUnitSumLex ↑a = toLex (inr a) :=
  rfl

@[simp]
/--
theorem `orderIsoPUnitSumLex_symm_inl` / 定理 `orderIsoPUnitSumLex_symm_inl`

English:
theorem orderIsoPUnitSumLex_symm_inl
  given: (x : PUnit)
  proof: rfl

@[simp]

中文:
定理 orderIsoPUnitSumLex_symm_inl
  条件: (x : 命题单元)
  证明: rfl

@[simp]
-/
theorem orderIsoPUnitSumLex_symm_inl (x : PUnit) :
    (@orderIsoPUnitSumLex α _).symm (toLex <| inl x) = ⊥ :=
  rfl

@[simp]
/--
theorem `orderIsoPUnitSumLex_symm_inr` / 定理 `orderIsoPUnitSumLex_symm_inr`

English:
theorem orderIsoPUnitSumLex_symm_inr
  given: (a : α)
  statement: orderIsoPUnitSumLex.symm (toLex <| inr a) = a
  proof: rfl

中文:
定理 orderIsoPUnitSumLex_symm_inr
  条件: (a : α)
  结论: orderIsoPUnitSumLex.symm (toLex <| inr a) = a
  证明: rfl
-/
theorem orderIsoPUnitSumLex_symm_inr (a : α) : orderIsoPUnitSumLex.symm (toLex <| inr a) = a :=
  rfl

end WithBot

namespace WithTop

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `orderIsoSumLexPUnit` / `orderIsoSumLexPUnit` 的定义

English:
definition orderIsoSumLexPUnit
  signature: : WithTop α ≃o α oplusₗ PUnit
  body: ⟨(Equiv.optionEquivSumPUnit α).trans toLex, fun {a b} => by
    simp only [Equiv.optionEquivSumPUnit, Option.elim, Equiv.trans_apply, Equiv.coe_fn_mk,
      Lex.toLex_le_toLex, le_refl]
    cases a <;> cases b
    · simp only [lex_inr_inr, le_top]
    · simp only [lex_inr_inl, false_iff]
      exact not_top_le_coe _
    · simp only [Lex.sep, le_top]
    · simp only [lex_inl_inl, coe_le_coe]⟩

@[simp]

中文:
定义 orderIsoSumLexPUnit
  签名: : WithTop α ≃o α oplusₗ 命题单元
  定义体: ⟨(Equiv.optionEquivSumPUnit α).trans toLex, fun {a b} => by
    simp only [Equiv.optionEquivSumPUnit, Option.elim, Equiv.trans_apply, Equiv.coe_fn_mk,
      Lex.toLex_le_toLex, le_refl]
    cases a <;> cases b
    · simp only [lex_inr_inr, le_top]
    · simp only [lex_inr_inl, false_iff]
      exact not_top_le_coe _
    · simp only [Lex.sep, le_top]
    · simp only [lex_inl_inl, coe_le_coe]⟩

@[simp]

Depends on / 依赖: Equiv.coe_fn_mk, Equiv.optionEquivSumPUnit, Equiv.trans_apply, Lex.sep, Lex.toLex_le_toLex, Option.elim, coe_fn_mk, coe_le_coe, false_iff, le_refl, le_top, lex_inl_inl, lex_inr_inl, lex_inr_inr, not_top_le_coe, optionEquivSumPUnit, toLex_le_toLex, trans_apply
-/
def orderIsoSumLexPUnit : WithTop α ≃o α oplusₗ PUnit :=
  ⟨(Equiv.optionEquivSumPUnit α).trans toLex, fun {a b} => by
    simp only [Equiv.optionEquivSumPUnit, Option.elim, Equiv.trans_apply, Equiv.coe_fn_mk,
      Lex.toLex_le_toLex, le_refl]
    cases a <;> cases b
    · simp only [lex_inr_inr, le_top]
    · simp only [lex_inr_inl, false_iff]
      exact not_top_le_coe _
    · simp only [Lex.sep, le_top]
    · simp only [lex_inl_inl, coe_le_coe]⟩

@[simp]
/--
theorem `orderIsoSumLexPUnit_top` / 定理 `orderIsoSumLexPUnit_top`

English:
theorem orderIsoSumLexPUnit_top
  statement: @orderIsoSumLexPUnit α _ ⊤ = toLex (inr PUnit.unit)
  proof: rfl

@[simp]

中文:
定理 orderIsoSumLexPUnit_top
  结论: @orderIsoSumLexPUnit α _ ⊤ = toLex (inr 命题单元.unit)
  证明: rfl

@[simp]
-/
theorem orderIsoSumLexPUnit_top : @orderIsoSumLexPUnit α _ ⊤ = toLex (inr PUnit.unit) :=
  rfl

@[simp]
/--
theorem `orderIsoSumLexPUnit_toLex` / 定理 `orderIsoSumLexPUnit_toLex`

English:
theorem orderIsoSumLexPUnit_toLex
  given: (a : α)
  statement: orderIsoSumLexPUnit ↑a = toLex (inl a)
  proof: rfl

@[simp]

中文:
定理 orderIsoSumLexPUnit_toLex
  条件: (a : α)
  结论: orderIsoSumLexPUnit ↑a = toLex (inl a)
  证明: rfl

@[simp]
-/
theorem orderIsoSumLexPUnit_toLex (a : α) : orderIsoSumLexPUnit ↑a = toLex (inl a) :=
  rfl

@[simp]
/--
theorem `orderIsoSumLexPUnit_symm_inr` / 定理 `orderIsoSumLexPUnit_symm_inr`

English:
theorem orderIsoSumLexPUnit_symm_inr
  given: (x : PUnit)
  proof: rfl

@[simp]

中文:
定理 orderIsoSumLexPUnit_symm_inr
  条件: (x : 命题单元)
  证明: rfl

@[simp]
-/
theorem orderIsoSumLexPUnit_symm_inr (x : PUnit) :
    (@orderIsoSumLexPUnit α _).symm (toLex <| inr x) = ⊤ :=
  rfl

@[simp]
/--
theorem `orderIsoSumLexPUnit_symm_inl` / 定理 `orderIsoSumLexPUnit_symm_inl`

English:
theorem orderIsoSumLexPUnit_symm_inl
  given: (a : α)
  statement: orderIsoSumLexPUnit.symm (toLex <| inl a) = a
  proof: rfl

中文:
定理 orderIsoSumLexPUnit_symm_inl
  条件: (a : α)
  结论: orderIsoSumLexPUnit.symm (toLex <| inl a) = a
  证明: rfl
-/
theorem orderIsoSumLexPUnit_symm_inl (a : α) : orderIsoSumLexPUnit.symm (toLex <| inl a) = a :=
  rfl

end WithTop
