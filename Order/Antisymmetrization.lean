/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Logic.Relation
public import Mathlib.Order.Hom.Basic
public import Mathlib.Tactic.Tauto

/-!
# Turning a preorder into a partial order

This file allows to make a preorder into a partial order by quotienting out the elements `a`, `b`
such that `a ≤ b` and `b ≤ a`.

`Antisymmetrization` is a functor from `Preorder` to `PartialOrder`. See `Preorder_to_PartialOrder`.

## Main declarations

* `AntisymmRel`: The antisymmetrization relation. `AntisymmRel r a b` means that `a` and `b` are
  related both ways by `r`.
* `Antisymmetrization α r`: The quotient of `α` by `AntisymmRel r`. Even when `r` is just a
  preorder, `Antisymmetrization α` is a partial order.
-/

@[expose] public section

open Function OrderDual

variable {α β : Type*} {a b c d : α}

section Relation

variable (r : α -> α -> Prop)

/--
Definition of `AntisymmRel` / `AntisymmRel` 的定义

English:
definition AntisymmRel
  signature: (a b : α)
  body: r a b ∧ r b a

中文:
定义 AntisymmRel
  签名: (a b : α)
  定义体: r a b ∧ r b a
-/
def AntisymmRel (a b : α) : Prop :=
  r a b ∧ r b a

/--
theorem `antisymmRel_swap` / 定理 `antisymmRel_swap`

English:
theorem antisymmRel_swap
  statement: AntisymmRel (swap r) = AntisymmRel r
  proof: funext₂ fun _ _ => propext and_comm

中文:
定理 antisymmRel_swap
  结论: AntisymmRel (swap r) = AntisymmRel r
  证明: funext₂ fun _ _ => propext and_comm

Depends on / 依赖: and_comm, propext
-/
theorem antisymmRel_swap : AntisymmRel (swap r) = AntisymmRel r :=
  funext₂ fun _ _ => propext and_comm

/--
theorem `antisymmRel_swap_apply` / 定理 `antisymmRel_swap_apply`

English:
theorem antisymmRel_swap_apply
  statement: AntisymmRel (swap r) a b ↔ AntisymmRel r a b
  proof: and_comm

@[simp, refl]

中文:
定理 antisymmRel_swap_apply
  结论: AntisymmRel (swap r) a b ↔ AntisymmRel r a b
  证明: and_comm

@[simp, refl]

Depends on / 依赖: and_comm
-/
theorem antisymmRel_swap_apply : AntisymmRel (swap r) a b ↔ AntisymmRel r a b :=
  and_comm

@[simp, refl]
/--
theorem `AntisymmRel.refl` / 定理 `AntisymmRel.refl`

English:
theorem AntisymmRel.refl
  given: [Std.Refl r] (a : α)
  statement: AntisymmRel r a a
  proof: ⟨_root_.refl _, _root_.refl _⟩

中文:
定理 AntisymmRel.refl
  条件: [Std.Refl r] (a : α)
  结论: AntisymmRel r a a
  证明: ⟨_root_.refl _, _root_.refl _⟩

Depends on / 依赖: _root_, _root_.refl
-/
theorem AntisymmRel.refl [Std.Refl r] (a : α) : AntisymmRel r a a :=
  ⟨_root_.refl _, _root_.refl _⟩

variable {r} in
/--
lemma `AntisymmRel.rfl` / 引理 `AntisymmRel.rfl`

English:
lemma AntisymmRel.rfl
  given: [Std.Refl r] {a : α}
  statement: AntisymmRel r a a
  proof: .refl ..

中文:
引理 AntisymmRel.rfl
  条件: [Std.Refl r] {a : α}
  结论: AntisymmRel r a a
  证明: .refl ..
-/
lemma AntisymmRel.rfl [Std.Refl r] {a : α} : AntisymmRel r a a := .refl ..

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Std.Refl
  signature: r] : Std.Refl (AntisymmRel r) where
  body: .refl r

中文:
实例 [Std.Refl
  签名: r] : Std.Refl (AntisymmRel r) where
  定义体: .refl r
-/
instance [Std.Refl r] : Std.Refl (AntisymmRel r) where
  refl := .refl r

variable {r}

/--
theorem `AntisymmRel.of_eq` / 定理 `AntisymmRel.of_eq`

English:
theorem AntisymmRel.of_eq
  given: [Std.Refl r] {a b : α} (h : a = b)
  statement: AntisymmRel r a b
  proof: h ▸ .rfl
alias Eq.antisymmRel := AntisymmRel.of_eq

@[symm]

中文:
定理 AntisymmRel.of_eq
  条件: [Std.Refl r] {a b : α} (h : a = b)
  结论: AntisymmRel r a b
  证明: h ▸ .rfl
alias Eq.antisymmRel := AntisymmRel.of_eq

@[symm]
-/
theorem AntisymmRel.of_eq [Std.Refl r] {a b : α} (h : a = b) : AntisymmRel r a b := h ▸ .rfl
alias Eq.antisymmRel := AntisymmRel.of_eq

@[symm]
/--
theorem `AntisymmRel.symm` / 定理 `AntisymmRel.symm`

English:
theorem AntisymmRel.symm
  statement: AntisymmRel r a b -> AntisymmRel r b a
  proof: And.symm

中文:
定理 AntisymmRel.symm
  结论: AntisymmRel r a b -> AntisymmRel r b a
  证明: And.symm

Depends on / 依赖: And.symm
-/
theorem AntisymmRel.symm : AntisymmRel r a b -> AntisymmRel r b a :=
  And.symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Std.Symm (AntisymmRel r)
  body: AntisymmRel.symm

中文:
实例 :
  签名: Std.Symm (AntisymmRel r)
  定义体: AntisymmRel.symm

Depends on / 依赖: AntisymmRel, AntisymmRel.symm
-/
instance : Std.Symm (AntisymmRel r) where
  symm _ _ := AntisymmRel.symm

/--
theorem `antisymmRel_comm` / 定理 `antisymmRel_comm`

English:
theorem antisymmRel_comm
  statement: AntisymmRel r a b ↔ AntisymmRel r b a
  proof: And.comm

@[trans]

中文:
定理 antisymmRel_comm
  结论: AntisymmRel r a b ↔ AntisymmRel r b a
  证明: And.comm

@[trans]

Depends on / 依赖: And.comm
-/
theorem antisymmRel_comm : AntisymmRel r a b ↔ AntisymmRel r b a :=
  And.comm

@[trans]
/--
theorem `AntisymmRel.trans` / 定理 `AntisymmRel.trans`

English:
theorem AntisymmRel.trans
  given: [IsTrans α r] (hab : AntisymmRel r a b) (hbc : AntisymmRel r b c)
  proof: ⟨_root_.trans hab.1 hbc.1, _root_.trans hbc.2 hab.2⟩

中文:
定理 AntisymmRel.trans
  条件: [是Trans α r] (hab : AntisymmRel r a b) (hbc : AntisymmRel r b c)
  证明: ⟨_root_.trans hab.1 hbc.1, _root_.trans hbc.2 hab.2⟩

Depends on / 依赖: _root_, _root_.trans
-/
theorem AntisymmRel.trans [IsTrans α r] (hab : AntisymmRel r a b) (hbc : AntisymmRel r b c) :
    AntisymmRel r a c :=
  ⟨_root_.trans hab.1 hbc.1, _root_.trans hbc.2 hab.2⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsTrans
  signature: α r] : IsTrans α (AntisymmRel r) where
  body: .trans

中文:
实例 [是Trans
  签名: α r] : 是Trans α (AntisymmRel r) where
  定义体: .trans
-/
instance [IsTrans α r] : IsTrans α (AntisymmRel r) where
  trans _ _ _ := .trans

/--
Instance `AntisymmRel.decidableRel` / 实例 `AntisymmRel.decidableRel`

English:
instance AntisymmRel.decidableRel
  signature: [DecidableRel r]
  body: fun _ _ => instDecidableAnd

@[simp]

中文:
实例 AntisymmRel.decidableRel
  签名: [DecidableRel r]
  定义体: fun _ _ => instDecidableAnd

@[simp]

Depends on / 依赖: instDecidableAnd
-/
instance AntisymmRel.decidableRel [DecidableRel r] : DecidableRel (AntisymmRel r) :=
  fun _ _ => instDecidableAnd

@[simp]
/--
theorem `antisymmRel_iff_eq` / 定理 `antisymmRel_iff_eq`

English:
theorem antisymmRel_iff_eq
  given: [Std.Refl r] [Std.Antisymm r]
  statement: AntisymmRel r a b ↔ a = b
  proof: antisymm_iff

alias ⟨AntisymmRel.eq, _⟩ := antisymmRel_iff_eq

中文:
定理 antisymmRel_iff_eq
  条件: [Std.Refl r] [Std.反对称 r]
  结论: AntisymmRel r a b ↔ a = b
  证明: antisymm_iff

alias ⟨AntisymmRel.eq, _⟩ := antisymmRel_iff_eq

Depends on / 依赖: antisymm_iff
-/
theorem antisymmRel_iff_eq [Std.Refl r] [Std.Antisymm r] : AntisymmRel r a b ↔ a = b :=
  antisymm_iff

alias ⟨AntisymmRel.eq, _⟩ := antisymmRel_iff_eq

namespace Mathlib.Tactic.GCongr

variable {α : Type*} {a b : α} {r : α -> α -> Prop}

/--
lemma `AntisymmRel.left` / 引理 `AntisymmRel.left`

English:
lemma AntisymmRel.left
  given: (h : AntisymmRel r a b)
  statement: r a b
  proof: h.1

中文:
引理 AntisymmRel.left
  条件: (h : AntisymmRel r a b)
  结论: r a b
  证明: h.1
-/
lemma AntisymmRel.left (h : AntisymmRel r a b) : r a b := h.1

/-- See if the term is `AntisymmRel r a b` and the goal is `r a b`. -/
@[gcongr_forward] meta def exactAntisymmRelLeft : ForwardExt where
  eval h goal := do goal.assignIfDefEq (← Lean.Meta.mkAppM ``AntisymmRel.left #[h])

end Mathlib.Tactic.GCongr

end Relation

section LE

variable [LE α]

/--
theorem `AntisymmRel.le` / 定理 `AntisymmRel.le`

English:
theorem AntisymmRel.le
  given: (h : AntisymmRel (· <= ·) a b)
  statement: a <= b
  proof: h.1

中文:
定理 AntisymmRel.le
  条件: (h : AntisymmRel (· <= ·) a b)
  结论: a <= b
  证明: h.1
-/
theorem AntisymmRel.le (h : AntisymmRel (· <= ·) a b) : a <= b := h.1
/--
theorem `AntisymmRel.ge` / 定理 `AntisymmRel.ge`

English:
theorem AntisymmRel.ge
  given: (h : AntisymmRel (· <= ·) a b)
  statement: b <= a
  proof: h.2

中文:
定理 AntisymmRel.ge
  条件: (h : AntisymmRel (· <= ·) a b)
  结论: b <= a
  证明: h.2
-/
theorem AntisymmRel.ge (h : AntisymmRel (· <= ·) a b) : b <= a := h.2

end LE

section IsPreorder

variable (α) (r : α -> α -> Prop) [IsPreorder α r]

/-- The antisymmetrization relation as an equivalence relation. -/
@[simps, instance_reducible]
/--
Definition of `AntisymmRel.setoid` / `AntisymmRel.setoid` 的定义

English:
definition AntisymmRel.setoid
  signature: : Setoid α
  body: ⟨AntisymmRel r, .refl r, .symm, .trans⟩

中文:
定义 AntisymmRel.setoid
  签名: : 集合等价关系 α
  定义体: ⟨AntisymmRel r, .refl r, .symm, .trans⟩

Depends on / 依赖: AntisymmRel
-/
def AntisymmRel.setoid : Setoid α :=
  ⟨AntisymmRel r, .refl r, .symm, .trans⟩

/--
Definition of `Antisymmetrization` / `Antisymmetrization` 的定义

English:
definition Antisymmetrization
  signature: : Type _
  body: Quotient AntisymmRel.setoid α r

中文:
定义 Antisymmetrization
  签名: : 类型 _
  定义体: Quotient AntisymmRel.setoid α r

Depends on / 依赖: AntisymmRel, AntisymmRel.setoid, Quotient, setoid
-/
def Antisymmetrization : Type _ :=
Quotient AntisymmRel.setoid α r

variable {α}

/--
Definition of `toAntisymmetrization` / `toAntisymmetrization` 的定义

English:
definition toAntisymmetrization
  signature: : α -> Antisymmetrization α r
  body: Quotient.mk _

中文:
定义 toAntisymmetrization
  签名: : α -> Antisymmetrization α r
  定义体: Quotient.mk _

Depends on / 依赖: Quotient, Quotient.mk
-/
def toAntisymmetrization : α -> Antisymmetrization α r :=
  Quotient.mk _

/--
Definition of `ofAntisymmetrization` / `ofAntisymmetrization` 的定义

English:
definition ofAntisymmetrization
  signature: : Antisymmetrization α r -> α
  body: Quotient.out

中文:
定义 ofAntisymmetrization
  签名: : Antisymmetrization α r -> α
  定义体: Quotient.out

Depends on / 依赖: Quotient, Quotient.out
-/
noncomputable def ofAntisymmetrization : Antisymmetrization α r -> α :=
  Quotient.out

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: α] : Inhabited (Antisymmetrization α r)
  body: inferInstanceAs Inhabited (Quotient _)

中文:
实例 [可居
  签名: α] : 可居 (Antisymmetrization α r)
  定义体: inferInstanceAs Inhabited (Quotient _)

Depends on / 依赖: Inhabited, Quotient
-/
instance [Inhabited α] : Inhabited (Antisymmetrization α r) :=
inferInstanceAs Inhabited (Quotient _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: α] : Subsingleton (Antisymmetrization α r)
  body: inferInstanceAs Subsingleton (Quotient _)

@[elab_as_elim]

中文:
实例 [子单例
  签名: α] : 子单例 (Antisymmetrization α r)
  定义体: inferInstanceAs Subsingleton (Quotient _)

@[elab_as_elim]

Depends on / 依赖: Quotient, Subsingleton
-/
instance [Subsingleton α] : Subsingleton (Antisymmetrization α r) :=
inferInstanceAs Subsingleton (Quotient _)

@[elab_as_elim]
/--
theorem `Antisymmetrization.ind` / 定理 `Antisymmetrization.ind`

English:
theorem Antisymmetrization.ind
  given: {p : Antisymmetrization α r -> Prop}
  proof: Quot.ind

@[elab_as_elim]

中文:
定理 Antisymmetrization.ind
  条件: {p : Antisymmetrization α r -> 命题}
  证明: Quot.ind

@[elab_as_elim]
-/
protected theorem Antisymmetrization.ind {p : Antisymmetrization α r -> Prop} :
    (forall a, p <| toAntisymmetrization r a) -> forall q, p q :=
  Quot.ind

@[elab_as_elim]
/--
theorem `Antisymmetrization.induction_on` / 定理 `Antisymmetrization.induction_on`

English:
theorem Antisymmetrization.induction_on
  statement: {p : Antisymmetrization α r -> Prop}
  proof: Quotient.inductionOn' a h

@[simp]

中文:
定理 Antisymmetrization.induction_on
  结论: {p : Antisymmetrization α r -> 命题}
  证明: Quotient.inductionOn' a h

@[simp]
-/
protected theorem Antisymmetrization.induction_on {p : Antisymmetrization α r -> Prop}
    (a : Antisymmetrization α r) (h : forall a, p <| toAntisymmetrization r a) : p a :=
  Quotient.inductionOn' a h

@[simp]
/--
theorem `toAntisymmetrization_ofAntisymmetrization` / 定理 `toAntisymmetrization_ofAntisymmetrization`

English:
theorem toAntisymmetrization_ofAntisymmetrization
  given: (a : Antisymmetrization α r)
  proof: Quotient.out_eq' _

中文:
定理 toAntisymmetrization_ofAntisymmetrization
  条件: (a : Antisymmetrization α r)
  证明: Quotient.out_eq' _

Depends on / 依赖: Quotient, Quotient.out_eq, out_eq
-/
theorem toAntisymmetrization_ofAntisymmetrization (a : Antisymmetrization α r) :
    toAntisymmetrization r (ofAntisymmetrization r a) = a :=
  Quotient.out_eq' _

end IsPreorder

section Preorder

variable [Preorder α] [Preorder β]

/--
theorem `le_iff_lt_or_antisymmRel` / 定理 `le_iff_lt_or_antisymmRel`

English:
theorem le_iff_lt_or_antisymmRel
  statement: a <= b ↔ a < b ∨ AntisymmRel (· <= ·) a b
  proof: by
  rw [lt_iff_le_not_ge]; rw [AntisymmRel]
  tauto

alias ⟨LE.le.lt_or_antisymmRel, _⟩ := le_iff_lt_or_antisymmRel

中文:
定理 le_iff_lt_or_antisymmRel
  结论: a <= b ↔ a < b ∨ AntisymmRel (· <= ·) a b
  证明: by
  rw [lt_iff_le_not_ge]; rw [AntisymmRel]
  tauto

alias ⟨LE.le.lt_or_antisymmRel, _⟩ := le_iff_lt_or_antisymmRel

Depends on / 依赖: AntisymmRel, lt_iff_le_not_ge
-/
theorem le_iff_lt_or_antisymmRel : a <= b ↔ a < b ∨ AntisymmRel (· <= ·) a b := by
  rw [lt_iff_le_not_ge]; rw [AntisymmRel]
  tauto

alias ⟨LE.le.lt_or_antisymmRel, _⟩ := le_iff_lt_or_antisymmRel

/--
theorem `le_of_le_of_antisymmRel` / 定理 `le_of_le_of_antisymmRel`

English:
theorem le_of_le_of_antisymmRel
  given: (h₁ : a <= b) (h₂ : AntisymmRel (· <= ·) b c)
  statement: a <= c
  proof: h₁.trans h₂.le

中文:
定理 le_of_le_of_antisymmRel
  条件: (h₁ : a <= b) (h₂ : AntisymmRel (· <= ·) b c)
  结论: a <= c
  证明: h₁.trans h₂.le
-/
theorem le_of_le_of_antisymmRel (h₁ : a <= b) (h₂ : AntisymmRel (· <= ·) b c) : a <= c :=
  h₁.trans h₂.le

/--
theorem `le_of_antisymmRel_of_le` / 定理 `le_of_antisymmRel_of_le`

English:
theorem le_of_antisymmRel_of_le
  given: (h₁ : AntisymmRel (· <= ·) a b) (h₂ : b <= c)
  statement: a <= c
  proof: h₁.le.trans h₂

alias LE.le.trans_antisymmRel := le_of_le_of_antisymmRel
alias AntisymmRel.trans_le := le_of_antisymmRel_of_le

中文:
定理 le_of_antisymmRel_of_le
  条件: (h₁ : AntisymmRel (· <= ·) a b) (h₂ : b <= c)
  结论: a <= c
  证明: h₁.le.trans h₂

alias LE.le.trans_antisymmRel := le_of_le_of_antisymmRel
alias AntisymmRel.trans_le := le_of_antisymmRel_of_le

Depends on / 依赖: le.trans
-/
theorem le_of_antisymmRel_of_le (h₁ : AntisymmRel (· <= ·) a b) (h₂ : b <= c) : a <= c :=
  h₁.le.trans h₂

alias LE.le.trans_antisymmRel := le_of_le_of_antisymmRel
alias AntisymmRel.trans_le := le_of_antisymmRel_of_le

/--
theorem `lt_of_lt_of_antisymmRel` / 定理 `lt_of_lt_of_antisymmRel`

English:
theorem lt_of_lt_of_antisymmRel
  given: (h₁ : a < b) (h₂ : AntisymmRel (· <= ·) b c)
  statement: a < c
  proof: h₁.trans_le h₂.le

中文:
定理 lt_of_lt_of_antisymmRel
  条件: (h₁ : a < b) (h₂ : AntisymmRel (· <= ·) b c)
  结论: a < c
  证明: h₁.trans_le h₂.le

Depends on / 依赖: trans_le
-/
theorem lt_of_lt_of_antisymmRel (h₁ : a < b) (h₂ : AntisymmRel (· <= ·) b c) : a < c :=
  h₁.trans_le h₂.le

/--
theorem `lt_of_antisymmRel_of_lt` / 定理 `lt_of_antisymmRel_of_lt`

English:
theorem lt_of_antisymmRel_of_lt
  given: (h₁ : AntisymmRel (· <= ·) a b) (h₂ : b < c)
  statement: a < c
  proof: h₁.le.trans_lt h₂

alias LT.lt.trans_antisymmRel := lt_of_lt_of_antisymmRel
alias AntisymmRel.trans_lt := lt_of_antisymmRel_of_lt

中文:
定理 lt_of_antisymmRel_of_lt
  条件: (h₁ : AntisymmRel (· <= ·) a b) (h₂ : b < c)
  结论: a < c
  证明: h₁.le.trans_lt h₂

alias LT.lt.trans_antisymmRel := lt_of_lt_of_antisymmRel
alias AntisymmRel.trans_lt := lt_of_antisymmRel_of_lt

Depends on / 依赖: le.trans_lt, trans_lt
-/
theorem lt_of_antisymmRel_of_lt (h₁ : AntisymmRel (· <= ·) a b) (h₂ : b < c) : a < c :=
  h₁.le.trans_lt h₂

alias LT.lt.trans_antisymmRel := lt_of_lt_of_antisymmRel
alias AntisymmRel.trans_lt := lt_of_antisymmRel_of_lt

/--
theorem `not_lt_of_antisymmRel` / 定理 `not_lt_of_antisymmRel`

English:
theorem not_lt_of_antisymmRel
  given: (h : AntisymmRel (· <= ·) a b)
  statement: ¬ a < b
  proof: h.ge.not_gt

中文:
定理 not_lt_of_antisymmRel
  条件: (h : AntisymmRel (· <= ·) a b)
  结论: ¬ a < b
  证明: h.ge.not_gt

Depends on / 依赖: h.ge.not_gt, not_gt
-/
theorem not_lt_of_antisymmRel (h : AntisymmRel (· <= ·) a b) : ¬ a < b :=
  h.ge.not_gt

/--
theorem `not_gt_of_antisymmRel` / 定理 `not_gt_of_antisymmRel`

English:
theorem not_gt_of_antisymmRel
  given: (h : AntisymmRel (· <= ·) a b)
  statement: ¬ b < a
  proof: h.le.not_gt

alias AntisymmRel.not_lt := not_lt_of_antisymmRel
alias AntisymmRel.not_gt := not_gt_of_antisymmRel

中文:
定理 not_gt_of_antisymmRel
  条件: (h : AntisymmRel (· <= ·) a b)
  结论: ¬ b < a
  证明: h.le.not_gt

alias AntisymmRel.not_lt := not_lt_of_antisymmRel
alias AntisymmRel.not_gt := not_gt_of_antisymmRel

Depends on / 依赖: h.le.not_gt, not_gt
-/
theorem not_gt_of_antisymmRel (h : AntisymmRel (· <= ·) a b) : ¬ b < a :=
  h.le.not_gt

alias AntisymmRel.not_lt := not_lt_of_antisymmRel
alias AntisymmRel.not_gt := not_gt_of_antisymmRel

/--
theorem `not_antisymmRel_of_lt` / 定理 `not_antisymmRel_of_lt`

English:
theorem not_antisymmRel_of_lt
  statement: a < b -> ¬ AntisymmRel (· <= ·) a b
  proof: imp_not_comm.1 not_lt_of_antisymmRel

中文:
定理 not_antisymmRel_of_lt
  结论: a < b -> ¬ AntisymmRel (· <= ·) a b
  证明: imp_not_comm.1 not_lt_of_antisymmRel

Depends on / 依赖: imp_not_comm, not_lt_of_antisymmRel
-/
theorem not_antisymmRel_of_lt : a < b -> ¬ AntisymmRel (· <= ·) a b :=
  imp_not_comm.1 not_lt_of_antisymmRel

/--
theorem `not_antisymmRel_of_gt` / 定理 `not_antisymmRel_of_gt`

English:
theorem not_antisymmRel_of_gt
  statement: b < a -> ¬ AntisymmRel (· <= ·) a b
  proof: imp_not_comm.1 not_gt_of_antisymmRel

alias LT.lt.not_antisymmRel := not_antisymmRel_of_lt
alias LT.lt.not_antisymmRel_symm := not_antisymmRel_of_gt

中文:
定理 not_antisymmRel_of_gt
  结论: b < a -> ¬ AntisymmRel (· <= ·) a b
  证明: imp_not_comm.1 not_gt_of_antisymmRel

alias LT.lt.not_antisymmRel := not_antisymmRel_of_lt
alias LT.lt.not_antisymmRel_symm := not_antisymmRel_of_gt

Depends on / 依赖: imp_not_comm, not_gt_of_antisymmRel
-/
theorem not_antisymmRel_of_gt : b < a -> ¬ AntisymmRel (· <= ·) a b :=
  imp_not_comm.1 not_gt_of_antisymmRel

alias LT.lt.not_antisymmRel := not_antisymmRel_of_lt
alias LT.lt.not_antisymmRel_symm := not_antisymmRel_of_gt

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: @Trans α α α (· <= ·) (AntisymmRel (· <= ·)) (· <= ·)
  body: le_of_le_of_antisymmRel

中文:
实例 :
  签名: @Trans α α α (· <= ·) (AntisymmRel (· <= ·)) (· <= ·)
  定义体: le_of_le_of_antisymmRel

Depends on / 依赖: le_of_le_of_antisymmRel
-/
instance : @Trans α α α (· <= ·) (AntisymmRel (· <= ·)) (· <= ·) where
  trans := le_of_le_of_antisymmRel

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: @Trans α α α (AntisymmRel (· <= ·)) (· <= ·) (· <= ·)
  body: le_of_antisymmRel_of_le

中文:
实例 :
  签名: @Trans α α α (AntisymmRel (· <= ·)) (· <= ·) (· <= ·)
  定义体: le_of_antisymmRel_of_le

Depends on / 依赖: le_of_antisymmRel_of_le
-/
instance : @Trans α α α (AntisymmRel (· <= ·)) (· <= ·) (· <= ·) where
  trans := le_of_antisymmRel_of_le

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: @Trans α α α (· < ·) (AntisymmRel (· <= ·)) (· < ·)
  body: lt_of_lt_of_antisymmRel

中文:
实例 :
  签名: @Trans α α α (· < ·) (AntisymmRel (· <= ·)) (· < ·)
  定义体: lt_of_lt_of_antisymmRel

Depends on / 依赖: lt_of_lt_of_antisymmRel
-/
instance : @Trans α α α (· < ·) (AntisymmRel (· <= ·)) (· < ·) where
  trans := lt_of_lt_of_antisymmRel

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: @Trans α α α (AntisymmRel (· <= ·)) (· < ·) (· < ·)
  body: lt_of_antisymmRel_of_lt

中文:
实例 :
  签名: @Trans α α α (AntisymmRel (· <= ·)) (· < ·) (· < ·)
  定义体: lt_of_antisymmRel_of_lt

Depends on / 依赖: lt_of_antisymmRel_of_lt
-/
instance : @Trans α α α (AntisymmRel (· <= ·)) (· < ·) (· < ·) where
  trans := lt_of_antisymmRel_of_lt

/--
theorem `AntisymmRel.le_congr` / 定理 `AntisymmRel.le_congr`

English:
theorem AntisymmRel.le_congr
  given: (h₁ : AntisymmRel (· <= ·) a b) (h₂ : AntisymmRel (· <= ·) c d)
  proof: (h₁.symm.trans_le h).trans_antisymmRel h₂
  mpr h := (h₁.trans_le h).trans_antisymmRel h₂.symm

中文:
定理 AntisymmRel.le_congr
  条件: (h₁ : AntisymmRel (· <= ·) a b) (h₂ : AntisymmRel (· <= ·) c d)
  证明: (h₁.symm.trans_le h).trans_antisymmRel h₂
  mpr h := (h₁.trans_le h).trans_antisymmRel h₂.symm

Depends on / 依赖: symm.trans_le, trans_antisymmRel, trans_le
-/
theorem AntisymmRel.le_congr (h₁ : AntisymmRel (· <= ·) a b) (h₂ : AntisymmRel (· <= ·) c d) :
    a <= c ↔ b <= d where
  mp h := (h₁.symm.trans_le h).trans_antisymmRel h₂
  mpr h := (h₁.trans_le h).trans_antisymmRel h₂.symm

/--
theorem `AntisymmRel.le_congr_left` / 定理 `AntisymmRel.le_congr_left`

English:
theorem AntisymmRel.le_congr_left
  given: (h : AntisymmRel (· <= ·) a b)
  statement: a <= c ↔ b <= c
  proof: h.le_congr .rfl

中文:
定理 AntisymmRel.le_congr_left
  条件: (h : AntisymmRel (· <= ·) a b)
  结论: a <= c ↔ b <= c
  证明: h.le_congr .rfl

Depends on / 依赖: h.le_congr, le_congr
-/
theorem AntisymmRel.le_congr_left (h : AntisymmRel (· <= ·) a b) : a <= c ↔ b <= c :=
  h.le_congr .rfl

/--
theorem `AntisymmRel.le_congr_right` / 定理 `AntisymmRel.le_congr_right`

English:
theorem AntisymmRel.le_congr_right
  given: (h : AntisymmRel (· <= ·) b c)
  statement: a <= b ↔ a <= c
  proof: AntisymmRel.rfl.le_congr h

中文:
定理 AntisymmRel.le_congr_right
  条件: (h : AntisymmRel (· <= ·) b c)
  结论: a <= b ↔ a <= c
  证明: AntisymmRel.rfl.le_congr h

Depends on / 依赖: AntisymmRel, AntisymmRel.rfl.le_congr, le_congr
-/
theorem AntisymmRel.le_congr_right (h : AntisymmRel (· <= ·) b c) : a <= b ↔ a <= c :=
  AntisymmRel.rfl.le_congr h

/--
theorem `AntisymmRel.lt_congr` / 定理 `AntisymmRel.lt_congr`

English:
theorem AntisymmRel.lt_congr
  given: (h₁ : AntisymmRel (· <= ·) a b) (h₂ : AntisymmRel (· <= ·) c d)
  proof: (h₁.symm.trans_lt h).trans_antisymmRel h₂
  mpr h := (h₁.trans_lt h).trans_antisymmRel h₂.symm

中文:
定理 AntisymmRel.lt_congr
  条件: (h₁ : AntisymmRel (· <= ·) a b) (h₂ : AntisymmRel (· <= ·) c d)
  证明: (h₁.symm.trans_lt h).trans_antisymmRel h₂
  mpr h := (h₁.trans_lt h).trans_antisymmRel h₂.symm

Depends on / 依赖: symm.trans_lt, trans_antisymmRel, trans_lt
-/
theorem AntisymmRel.lt_congr (h₁ : AntisymmRel (· <= ·) a b) (h₂ : AntisymmRel (· <= ·) c d) :
    a < c ↔ b < d where
  mp h := (h₁.symm.trans_lt h).trans_antisymmRel h₂
  mpr h := (h₁.trans_lt h).trans_antisymmRel h₂.symm

/--
theorem `AntisymmRel.lt_congr_left` / 定理 `AntisymmRel.lt_congr_left`

English:
theorem AntisymmRel.lt_congr_left
  given: (h : AntisymmRel (· <= ·) a b)
  statement: a < c ↔ b < c
  proof: h.lt_congr .rfl

中文:
定理 AntisymmRel.lt_congr_left
  条件: (h : AntisymmRel (· <= ·) a b)
  结论: a < c ↔ b < c
  证明: h.lt_congr .rfl

Depends on / 依赖: h.lt_congr, lt_congr
-/
theorem AntisymmRel.lt_congr_left (h : AntisymmRel (· <= ·) a b) : a < c ↔ b < c :=
  h.lt_congr .rfl

/--
theorem `AntisymmRel.lt_congr_right` / 定理 `AntisymmRel.lt_congr_right`

English:
theorem AntisymmRel.lt_congr_right
  given: (h : AntisymmRel (· <= ·) b c)
  statement: a < b ↔ a < c
  proof: AntisymmRel.rfl.lt_congr h

中文:
定理 AntisymmRel.lt_congr_right
  条件: (h : AntisymmRel (· <= ·) b c)
  结论: a < b ↔ a < c
  证明: AntisymmRel.rfl.lt_congr h

Depends on / 依赖: AntisymmRel, AntisymmRel.rfl.lt_congr, lt_congr
-/
theorem AntisymmRel.lt_congr_right (h : AntisymmRel (· <= ·) b c) : a < b ↔ a < c :=
  AntisymmRel.rfl.lt_congr h

/--
theorem `AntisymmRel.antisymmRel_congr` / 定理 `AntisymmRel.antisymmRel_congr`

English:
theorem AntisymmRel.antisymmRel_congr
  proof: rel_congr h₁ h₂

中文:
定理 AntisymmRel.antisymmRel_congr
  证明: rel_congr h₁ h₂

Depends on / 依赖: rel_congr
-/
theorem AntisymmRel.antisymmRel_congr
    (h₁ : AntisymmRel (· <= ·) a b) (h₂ : AntisymmRel (· <= ·) c d) :
    AntisymmRel (· <= ·) a c ↔ AntisymmRel (· <= ·) b d :=
  rel_congr h₁ h₂

/--
theorem `AntisymmRel.antisymmRel_congr_left` / 定理 `AntisymmRel.antisymmRel_congr_left`

English:
theorem AntisymmRel.antisymmRel_congr_left
  given: (h : AntisymmRel (· <= ·) a b)
  proof: rel_congr_left h

中文:
定理 AntisymmRel.antisymmRel_congr_left
  条件: (h : AntisymmRel (· <= ·) a b)
  证明: rel_congr_left h

Depends on / 依赖: rel_congr_left
-/
theorem AntisymmRel.antisymmRel_congr_left (h : AntisymmRel (· <= ·) a b) :
    AntisymmRel (· <= ·) a c ↔ AntisymmRel (· <= ·) b c :=
  rel_congr_left h

/--
theorem `AntisymmRel.antisymmRel_congr_right` / 定理 `AntisymmRel.antisymmRel_congr_right`

English:
theorem AntisymmRel.antisymmRel_congr_right
  given: (h : AntisymmRel (· <= ·) b c)
  proof: rel_congr_right h

中文:
定理 AntisymmRel.antisymmRel_congr_right
  条件: (h : AntisymmRel (· <= ·) b c)
  证明: rel_congr_right h

Depends on / 依赖: rel_congr_right
-/
theorem AntisymmRel.antisymmRel_congr_right (h : AntisymmRel (· <= ·) b c) :
    AntisymmRel (· <= ·) a b ↔ AntisymmRel (· <= ·) a c :=
  rel_congr_right h

/--
theorem `AntisymmRel.image` / 定理 `AntisymmRel.image`

English:
theorem AntisymmRel.image
  given: (h : AntisymmRel (· <= ·) a b) {f : α -> β} (hf : Monotone f)
  proof: ⟨hf h.1, hf h.2⟩

中文:
定理 AntisymmRel.像
  条件: (h : AntisymmRel (· <= ·) a b) {f : α -> β} (hf : 递增 f)
  证明: ⟨hf h.1, hf h.2⟩
-/
theorem AntisymmRel.image (h : AntisymmRel (· <= ·) a b) {f : α -> β} (hf : Monotone f) :
    AntisymmRel (· <= ·) (f a) (f b) :=
  ⟨hf h.1, hf h.2⟩

/--
Instance `instPartialOrderAntisymmetrization` / 实例 `instPartialOrderAntisymmetrization`

English:
instance instPartialOrderAntisymmetrization
  signature: : PartialOrder (Antisymmetrization α (· <= ·)) where
  body: Quotient.lift₂ (· <= ·) fun (_ _ _ _ : α) h₁ h₂ =>
propext ⟨fun h => h₁.2.trans h.trans h₂.1, fun h => h₁.1.trans h.trans h₂.2⟩
  lt :=
    Quotient.lift₂ (· < ·) fun (_ _ _ _ : α) h₁ h₂ =>
propext ⟨fun h => h₁.2.trans_lt h.trans_le h₂.1, fun h =>
h₁.1.trans_lt h.trans_le h₂.2⟩
  le_refl a := Quotie

中文:
实例 instPartialOrderAntisymmetrization
  签名: : 偏序 (Antisymmetrization α (· <= ·)) where
  定义体: Quotient.lift₂ (· <= ·) fun (_ _ _ _ : α) h₁ h₂ =>
propext ⟨fun h => h₁.2.trans h.trans h₂.1, fun h => h₁.1.trans h.trans h₂.2⟩
  lt :=
    Quotient.lift₂ (· < ·) fun (_ _ _ _ : α) h₁ h₂ =>
propext ⟨fun h => h₁.2.trans_lt h.trans_le h₂.1, fun h =>
h₁.1.trans_lt h.trans_le h₂.2⟩
  le_refl a := Quotie

Depends on / 依赖: Quotient, Quotient.induct, Quotient.inductionOn, Quotient.lift, h.trans, h.trans_le, induct, inductionOn, le_antisymm, le_refl, le_trans, lt_iff_le_not_ge, propext, trans_le, trans_lt
-/
instance instPartialOrderAntisymmetrization : PartialOrder (Antisymmetrization α (· <= ·)) where
  le :=
    Quotient.lift₂ (· <= ·) fun (_ _ _ _ : α) h₁ h₂ =>
propext ⟨fun h => h₁.2.trans h.trans h₂.1, fun h => h₁.1.trans h.trans h₂.2⟩
  lt :=
    Quotient.lift₂ (· < ·) fun (_ _ _ _ : α) h₁ h₂ =>
propext ⟨fun h => h₁.2.trans_lt h.trans_le h₂.1, fun h =>
h₁.1.trans_lt h.trans_le h₂.2⟩
  le_refl a := Quotient.inductionOn' a le_refl
  le_trans a b c := Quotient.inductionOn₃' a b c fun _ _ _ => le_trans
  lt_iff_le_not_ge a b := Quotient.inductionOn₂' a b fun _ _ => lt_iff_le_not_ge
  le_antisymm a b := Quotient.inductionOn₂' a b fun _ _ hab hba => Quotient.sound' ⟨hab, hba⟩

/--
theorem `antisymmetrization_fibration` / 定理 `antisymmetrization_fibration`

English:
theorem antisymmetrization_fibration
  proof: by
  rintro a ⟨b⟩ h
  exact ⟨b, h, rfl⟩

中文:
定理 antisymmetrization_fibration
  证明: by
  rintro a ⟨b⟩ h
  exact ⟨b, h, rfl⟩
-/
theorem antisymmetrization_fibration :
    Relation.Fibration (· < ·) (· < ·) (toAntisymmetrization (α := α) (· <= ·)) := by
  rintro a ⟨b⟩ h
  exact ⟨b, h, rfl⟩

/--
theorem `acc_antisymmetrization_iff` / 定理 `acc_antisymmetrization_iff`

English:
theorem acc_antisymmetrization_iff
  statement: Acc (· < ·)
  proof: acc_lift₂_iff

中文:
定理 acc_antisymmetrization_iff
  结论: Acc (· < ·)
  证明: acc_lift₂_iff
-/
theorem acc_antisymmetrization_iff : Acc (· < ·)
    (toAntisymmetrization (α := α) (· <= ·) a) ↔ Acc (· < ·) a :=
  acc_lift₂_iff

/--
theorem `wellFounded_antisymmetrization_iff` / 定理 `wellFounded_antisymmetrization_iff`

English:
theorem wellFounded_antisymmetrization_iff
  proof: wellFounded_lift₂_iff

中文:
定理 wellFounded_antisymmetrization_iff
  证明: wellFounded_lift₂_iff
-/
theorem wellFounded_antisymmetrization_iff :
    WellFounded (@LT.lt (Antisymmetrization α (· <= ·)) _) ↔ WellFounded (@LT.lt α _) :=
  wellFounded_lift₂_iff

/--
theorem `wellFoundedLT_antisymmetrization_iff` / 定理 `wellFoundedLT_antisymmetrization_iff`

English:
theorem wellFoundedLT_antisymmetrization_iff
  proof: by
  simp_rw [isWellFounded_iff, wellFounded_antisymmetrization_iff]

中文:
定理 wellFoundedLT_antisymmetrization_iff
  证明: by
  simp_rw [isWellFounded_iff, wellFounded_antisymmetrization_iff]

Depends on / 依赖: isWellFounded_iff, simp_rw, wellFounded_antisymmetrization_iff
-/
theorem wellFoundedLT_antisymmetrization_iff :
    WellFoundedLT (Antisymmetrization α (· <= ·)) ↔ WellFoundedLT α := by
  simp_rw [isWellFounded_iff, wellFounded_antisymmetrization_iff]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `wellFoundedGT_antisymmetrization_iff` / 定理 `wellFoundedGT_antisymmetrization_iff`

English:
theorem wellFoundedGT_antisymmetrization_iff
  proof: by
  simp_rw [isWellFounded_iff]
  convert! wellFounded_liftOn₂'_iff with ⟨_⟩ ⟨_⟩
  exact fun _ _ _ _ h₁ h₂ => propext
    ⟨fun h => (h₂.2.trans_lt h).trans_le h₁.1, fun h => (h₂.1.trans_lt h).trans_le h₁.2⟩

中文:
定理 wellFoundedGT_antisymmetrization_iff
  证明: by
  simp_rw [isWellFounded_iff]
  convert! wellFounded_liftOn₂'_iff with ⟨_⟩ ⟨_⟩
  exact fun _ _ _ _ h₁ h₂ => propext
    ⟨fun h => (h₂.2.trans_lt h).trans_le h₁.1, fun h => (h₂.1.trans_lt h).trans_le h₁.2⟩

Depends on / 依赖: _iff, convert, isWellFounded_iff, propext, simp_rw, trans_le, trans_lt
-/
theorem wellFoundedGT_antisymmetrization_iff :
    WellFoundedGT (Antisymmetrization α (· <= ·)) ↔ WellFoundedGT α := by
  simp_rw [isWellFounded_iff]
  convert! wellFounded_liftOn₂'_iff with ⟨_⟩ ⟨_⟩
  exact fun _ _ _ _ h₁ h₂ => propext
    ⟨fun h => (h₂.2.trans_lt h).trans_le h₁.1, fun h => (h₂.1.trans_lt h).trans_le h₁.2⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [WellFoundedLT
  signature: α] : WellFoundedLT (Antisymmetrization α (· <= ·))
  body: wellFoundedLT_antisymmetrization_iff.mpr ‹_›

中文:
实例 [WellFoundedLT
  签名: α] : WellFoundedLT (Antisymmetrization α (· <= ·))
  定义体: wellFoundedLT_antisymmetrization_iff.mpr ‹_›

Depends on / 依赖: wellFoundedLT_antisymmetrization_iff, wellFoundedLT_antisymmetrization_iff.mpr
-/
instance [WellFoundedLT α] : WellFoundedLT (Antisymmetrization α (· <= ·)) :=
  wellFoundedLT_antisymmetrization_iff.mpr ‹_›

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [WellFoundedGT
  signature: α] : WellFoundedGT (Antisymmetrization α (· <= ·))
  body: wellFoundedGT_antisymmetrization_iff.mpr ‹_›

中文:
实例 [WellFoundedGT
  签名: α] : WellFoundedGT (Antisymmetrization α (· <= ·))
  定义体: wellFoundedGT_antisymmetrization_iff.mpr ‹_›

Depends on / 依赖: wellFoundedGT_antisymmetrization_iff, wellFoundedGT_antisymmetrization_iff.mpr
-/
instance [WellFoundedGT α] : WellFoundedGT (Antisymmetrization α (· <= ·)) :=
  wellFoundedGT_antisymmetrization_iff.mpr ‹_›

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableLE
  signature: α] [DecidableLT α] [@Std.Total α (· <= ·)] :
  body: { instPartialOrderAntisymmetrization with
le_total := fun a b => Quotient.inductionOn₂' a b total_of (· <= ·),
    toDecidableLE := fun _ _ => show Decidable (Quotient.liftOn₂' _ _ _ _) from inferInstance,
    toDecidableLT := fun _ _ => show Decidable (Quotient.liftOn₂' _ _ _ _) from inferInstance 

中文:
实例 [DecidableLE
  签名: α] [DecidableLT α] [@Std.全 α (· <= ·)] :
  定义体: { instPartialOrderAntisymmetrization with
le_total := fun a b => Quotient.inductionOn₂' a b total_of (· <= ·),
    toDecidableLE := fun _ _ => show Decidable (Quotient.liftOn₂' _ _ _ _) from inferInstance,
    toDecidableLT := fun _ _ => show Decidable (Quotient.liftOn₂' _ _ _ _) from inferInstance 

Depends on / 依赖: Decidable, Quotient, Quotient.inductionOn, Quotient.liftOn, instPartialOrderAntisymmetrization, le_total, toDecidableLE, toDecidableLT, total_of
-/
instance [DecidableLE α] [DecidableLT α] [@Std.Total α (· <= ·)] :
    LinearOrder (Antisymmetrization α (· <= ·)) :=
  { instPartialOrderAntisymmetrization with
le_total := fun a b => Quotient.inductionOn₂' a b total_of (· <= ·),
    toDecidableLE := fun _ _ => show Decidable (Quotient.liftOn₂' _ _ _ _) from inferInstance,
    toDecidableLT := fun _ _ => show Decidable (Quotient.liftOn₂' _ _ _ _) from inferInstance }

@[simp]
/--
theorem `toAntisymmetrization_le_toAntisymmetrization_iff` / 定理 `toAntisymmetrization_le_toAntisymmetrization_iff`

English:
theorem toAntisymmetrization_le_toAntisymmetrization_iff
  proof: Iff.rfl

@[simp]

中文:
定理 toAntisymmetrization_le_toAntisymmetrization_iff
  证明: Iff.rfl

@[simp]

Depends on / 依赖: toAntisymmetrization
-/
theorem toAntisymmetrization_le_toAntisymmetrization_iff :
    toAntisymmetrization (α := α) (· <= ·) a <= toAntisymmetrization (α := α) (· <= ·) b ↔ a <= b :=
  Iff.rfl

@[simp]
/--
theorem `toAntisymmetrization_lt_toAntisymmetrization_iff` / 定理 `toAntisymmetrization_lt_toAntisymmetrization_iff`

English:
theorem toAntisymmetrization_lt_toAntisymmetrization_iff
  proof: Iff.rfl

@[simp]

中文:
定理 toAntisymmetrization_lt_toAntisymmetrization_iff
  证明: Iff.rfl

@[simp]

Depends on / 依赖: toAntisymmetrization
-/
theorem toAntisymmetrization_lt_toAntisymmetrization_iff :
    toAntisymmetrization (α := α) (· <= ·) a < toAntisymmetrization (α := α) (· <= ·) b ↔ a < b :=
  Iff.rfl

@[simp]
/--
theorem `ofAntisymmetrization_le_ofAntisymmetrization_iff` / 定理 `ofAntisymmetrization_le_ofAntisymmetrization_iff`

English:
theorem ofAntisymmetrization_le_ofAntisymmetrization_iff
  given: {a b : Antisymmetrization α (· <= ·)}
  proof: (Quotient.outRelEmbedding _).map_rel_iff

@[simp]

中文:
定理 ofAntisymmetrization_le_ofAntisymmetrization_iff
  条件: {a b : Antisymmetrization α (· <= ·)}
  证明: (Quotient.outRelEmbedding _).map_rel_iff

@[simp]

Depends on / 依赖: Quotient, Quotient.outRelEmbedding, map_rel_iff, outRelEmbedding
-/
theorem ofAntisymmetrization_le_ofAntisymmetrization_iff {a b : Antisymmetrization α (· <= ·)} :
    ofAntisymmetrization (· <= ·) a <= ofAntisymmetrization (· <= ·) b ↔ a <= b :=
  (Quotient.outRelEmbedding _).map_rel_iff

@[simp]
/--
theorem `ofAntisymmetrization_lt_ofAntisymmetrization_iff` / 定理 `ofAntisymmetrization_lt_ofAntisymmetrization_iff`

English:
theorem ofAntisymmetrization_lt_ofAntisymmetrization_iff
  given: {a b : Antisymmetrization α (· <= ·)}
  proof: (Quotient.outRelEmbedding _).map_rel_iff

@[gcongr, mono]

中文:
定理 ofAntisymmetrization_lt_ofAntisymmetrization_iff
  条件: {a b : Antisymmetrization α (· <= ·)}
  证明: (Quotient.outRelEmbedding _).map_rel_iff

@[gcongr, mono]

Depends on / 依赖: Quotient, Quotient.outRelEmbedding, map_rel_iff, outRelEmbedding
-/
theorem ofAntisymmetrization_lt_ofAntisymmetrization_iff {a b : Antisymmetrization α (· <= ·)} :
    ofAntisymmetrization (· <= ·) a < ofAntisymmetrization (· <= ·) b ↔ a < b :=
  (Quotient.outRelEmbedding _).map_rel_iff

@[gcongr, mono]
/--
theorem `toAntisymmetrization_mono` / 定理 `toAntisymmetrization_mono`

English:
theorem toAntisymmetrization_mono
  statement: Monotone (toAntisymmetrization (α := α) (· <= ·))
  proof: fun _ _ => id

中文:
定理 toAntisymmetrization_mono
  结论: 递增 (toAntisymmetrization (α := α) (· <= ·))
  证明: fun _ _ => id
-/
theorem toAntisymmetrization_mono : Monotone (toAntisymmetrization (α := α) (· <= ·)) :=
  fun _ _ => id

open scoped Relator in
/--
theorem `liftFun_antisymmRel` / 定理 `liftFun_antisymmRel`

English:
theorem liftFun_antisymmRel
  given: (f : α ->o β)
  proof: fun _ _ h =>
  ⟨f.mono h.1, f.mono h.2⟩

中文:
定理 liftFun_antisymmRel
  条件: (f : α ->o β)
  证明: fun _ _ h =>
  ⟨f.mono h.1, f.mono h.2⟩
-/
theorem liftFun_antisymmRel (f : α ->o β) :
    ((AntisymmRel.setoid α (· <= ·)).r ⇒ (AntisymmRel.setoid β (· <= ·)).r) f f := fun _ _ h =>
  ⟨f.mono h.1, f.mono h.2⟩

/--
Definition of `OrderHom.antisymmetrization` / `OrderHom.antisymmetrization` 的定义

English:
definition OrderHom.antisymmetrization
  signature: (f : α ->o β)
  body: ⟨Quotient.map' f liftFun_antisymmRel f, fun a b => Quotient.inductionOn₂' a b f.mono⟩

@[simp]

中文:
定义 序态射.antisymmetrization
  签名: (f : α ->o β)
  定义体: ⟨Quotient.map' f liftFun_antisymmRel f, fun a b => Quotient.inductionOn₂' a b f.mono⟩

@[simp]
-/
protected def OrderHom.antisymmetrization (f : α ->o β) :
    Antisymmetrization α (· <= ·) ->o Antisymmetrization β (· <= ·) :=
⟨Quotient.map' f liftFun_antisymmRel f, fun a b => Quotient.inductionOn₂' a b f.mono⟩

@[simp]
/--
theorem `OrderHom.coe_antisymmetrization` / 定理 `OrderHom.coe_antisymmetrization`

English:
theorem OrderHom.coe_antisymmetrization
  given: (f : α ->o β)
  proof: rfl

中文:
定理 序态射.coe_antisymmetrization
  条件: (f : α ->o β)
  证明: rfl
-/
theorem OrderHom.coe_antisymmetrization (f : α ->o β) :
    ⇑f.antisymmetrization = Quotient.map' f (liftFun_antisymmRel f) :=
  rfl

/--
theorem `OrderHom.antisymmetrization_apply` / 定理 `OrderHom.antisymmetrization_apply`

English:
theorem OrderHom.antisymmetrization_apply
  given: (f : α ->o β) (a : Antisymmetrization α (· <= ·))
  proof: rfl

@[simp]

中文:
定理 序态射.antisymmetrization_apply
  条件: (f : α ->o β) (a : Antisymmetrization α (· <= ·))
  证明: rfl

@[simp]
-/
theorem OrderHom.antisymmetrization_apply (f : α ->o β) (a : Antisymmetrization α (· <= ·)) :
    f.antisymmetrization a = Quotient.map' f (liftFun_antisymmRel f) a :=
  rfl

@[simp]
/--
theorem `OrderHom.antisymmetrization_apply_mk` / 定理 `OrderHom.antisymmetrization_apply_mk`

English:
theorem OrderHom.antisymmetrization_apply_mk
  given: (f : α ->o β) (a : α)
  proof: @Quotient.map_mk _ _ (_root_.id _) (_root_.id _) f (liftFun_antisymmRel f) _

中文:
定理 序态射.antisymmetrization_apply_mk
  条件: (f : α ->o β) (a : α)
  证明: @Quotient.map_mk _ _ (_root_.id _) (_root_.id _) f (liftFun_antisymmRel f) _

Depends on / 依赖: Quotient, Quotient.map_mk, _root_, _root_.id, liftFun_antisymmRel, map_mk
-/
theorem OrderHom.antisymmetrization_apply_mk (f : α ->o β) (a : α) :
    f.antisymmetrization (toAntisymmetrization _ a) = toAntisymmetrization _ (f a) :=
  @Quotient.map_mk _ _ (_root_.id _) (_root_.id _) f (liftFun_antisymmRel f) _

variable (α)

/-- `ofAntisymmetrization` as an order embedding. -/
@[simps]
/--
Definition of `OrderEmbedding.ofAntisymmetrization` / `OrderEmbedding.ofAntisymmetrization` 的定义

English:
definition OrderEmbedding.ofAntisymmetrization
  signature: : Antisymmetrization α (· <= ·) ↪o α
  body: { Quotient.outRelEmbedding _ with toFun := _root_.ofAntisymmetrization _ }

中文:
定义 OrderEmbedding.ofAntisymmetrization
  签名: : Antisymmetrization α (· <= ·) ↪o α
  定义体: { Quotient.outRelEmbedding _ with toFun := _root_.ofAntisymmetrization _ }

Depends on / 依赖: Quotient, Quotient.outRelEmbedding, _root_, _root_.ofAntisymmetrization, ofAntisymmetrization, outRelEmbedding
-/
noncomputable def OrderEmbedding.ofAntisymmetrization : Antisymmetrization α (· <= ·) ↪o α :=
  { Quotient.outRelEmbedding _ with toFun := _root_.ofAntisymmetrization _ }

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `OrderIso.dualAntisymmetrization` / `OrderIso.dualAntisymmetrization` 的定义

English:
definition OrderIso.dualAntisymmetrization
  signature: :
  body: (Quotient.map' id) fun _ _ => And.symm
  invFun := (Quotient.map' id) fun _ _ => And.symm
  left_inv a := Quotient.inductionOn' a fun a => by simp_rw [Quotient.map'_mk'', id]
  right_inv a := Quotient.inductionOn' a fun a => by simp_rw [Quotient.map'_mk'', id]
  map_rel_iff' := @fun a b => Quotient.

中文:
定义 OrderIso.dualAntisymmetrization
  签名: :
  定义体: (Quotient.map' id) fun _ _ => And.symm
  invFun := (Quotient.map' id) fun _ _ => And.symm
  left_inv a := Quotient.inductionOn' a fun a => by simp_rw [Quotient.map'_mk'', id]
  right_inv a := Quotient.inductionOn' a fun a => by simp_rw [Quotient.map'_mk'', id]
  map_rel_iff' := @fun a b => Quotient.

Depends on / 依赖: And.symm, Quotient, Quotient.map
-/
def OrderIso.dualAntisymmetrization :
    (Antisymmetrization α (· <= ·))ᵒᵈ ≃o Antisymmetrization αᵒᵈ (· <= ·) where
  toFun := (Quotient.map' id) fun _ _ => And.symm
  invFun := (Quotient.map' id) fun _ _ => And.symm
  left_inv a := Quotient.inductionOn' a fun a => by simp_rw [Quotient.map'_mk'', id]
  right_inv a := Quotient.inductionOn' a fun a => by simp_rw [Quotient.map'_mk'', id]
  map_rel_iff' := @fun a b => Quotient.inductionOn₂' a b fun _ _ => Iff.rfl

@[simp]
/--
theorem `OrderIso.dualAntisymmetrization_apply` / 定理 `OrderIso.dualAntisymmetrization_apply`

English:
theorem OrderIso.dualAntisymmetrization_apply
  given: (a : α)
  proof: rfl

@[simp]

中文:
定理 OrderIso.dualAntisymmetrization_apply
  条件: (a : α)
  证明: rfl

@[simp]
-/
theorem OrderIso.dualAntisymmetrization_apply (a : α) :
    OrderIso.dualAntisymmetrization _ (toDual <| toAntisymmetrization _ a) =
      toAntisymmetrization _ (toDual a) :=
  rfl

@[simp]
/--
theorem `OrderIso.dualAntisymmetrization_symm_apply` / 定理 `OrderIso.dualAntisymmetrization_symm_apply`

English:
theorem OrderIso.dualAntisymmetrization_symm_apply
  given: (a : α)
  proof: rfl

中文:
定理 OrderIso.dualAntisymmetrization_symm_apply
  条件: (a : α)
  证明: rfl
-/
theorem OrderIso.dualAntisymmetrization_symm_apply (a : α) :
    (OrderIso.dualAntisymmetrization _).symm (toAntisymmetrization _ <| toDual a) =
      toDual (toAntisymmetrization _ a) :=
  rfl

end Preorder

section SymmGen

open Relation

variable {r : α -> α -> Prop}

/--
theorem `AntisymmRel.symmGen` / 定理 `AntisymmRel.symmGen`

English:
theorem AntisymmRel.symmGen
  given: (h : AntisymmRel r a b)
  statement: SymmGen r a b
  proof: Or.inl h.1

中文:
定理 AntisymmRel.symmGen
  条件: (h : AntisymmRel r a b)
  结论: SymmGen r a b
  证明: Or.inl h.1

Depends on / 依赖: Or.inl
-/
theorem AntisymmRel.symmGen (h : AntisymmRel r a b) : SymmGen r a b :=
  Or.inl h.1

variable [Preorder α]

/--
theorem `Relation.SymmGen.of_lt` / 定理 `Relation.SymmGen.of_lt`

English:
theorem Relation.SymmGen.of_lt
  given: (h : a < b)
  statement: SymmGen (· <= ·) a b
  proof: h.le.symmGen

中文:
定理 关系.SymmGen.of_lt
  条件: (h : a < b)
  结论: SymmGen (· <= ·) a b
  证明: h.le.symmGen

Depends on / 依赖: h.le.symmGen, symmGen
-/
theorem Relation.SymmGen.of_lt (h : a < b) : SymmGen (· <= ·) a b := h.le.symmGen
/--
theorem `Relation.SymmGen.of_gt` / 定理 `Relation.SymmGen.of_gt`

English:
theorem Relation.SymmGen.of_gt
  given: (h : b < a)
  statement: SymmGen (· <= ·) a b
  proof: h.le.symmGen_symm

alias _root_.LT.lt.symmGen := SymmGen.of_lt
alias _root_.LT.lt.symmGen_symm := SymmGen.of_gt

@[trans]

中文:
定理 关系.SymmGen.of_gt
  条件: (h : b < a)
  结论: SymmGen (· <= ·) a b
  证明: h.le.symmGen_symm

alias _root_.LT.lt.symmGen := SymmGen.of_lt
alias _root_.LT.lt.symmGen_symm := SymmGen.of_gt

@[trans]

Depends on / 依赖: h.le.symmGen_symm, symmGen_symm
-/
theorem Relation.SymmGen.of_gt (h : b < a) : SymmGen (· <= ·) a b := h.le.symmGen_symm

alias _root_.LT.lt.symmGen := SymmGen.of_lt
alias _root_.LT.lt.symmGen_symm := SymmGen.of_gt

@[trans]
/--
theorem `Relation.SymmGen.of_symmGen_of_antisymmRel` / 定理 `Relation.SymmGen.of_symmGen_of_antisymmRel`

English:
theorem Relation.SymmGen.of_symmGen_of_antisymmRel
  proof: by
  obtain (h | h) := h₁
  · exact (h.trans h₂.le).symmGen
  · exact (h₂.ge.trans h).symmGen_symm

alias Relation.SymmGen.trans_antisymmRel := SymmGen.of_symmGen_of_antisymmRel

中文:
定理 关系.SymmGen.of_symmGen_of_antisymmRel
  证明: by
  obtain (h | h) := h₁
  · exact (h.trans h₂.le).symmGen
  · exact (h₂.ge.trans h).symmGen_symm

alias Relation.SymmGen.trans_antisymmRel := SymmGen.of_symmGen_of_antisymmRel

Depends on / 依赖: ge.trans, h.trans, symmGen, symmGen_symm
-/
theorem Relation.SymmGen.of_symmGen_of_antisymmRel
    (h₁ : SymmGen (· <= ·) a b) (h₂ : AntisymmRel (· <= ·) b c) : SymmGen (· <= ·) a c := by
  obtain (h | h) := h₁
  · exact (h.trans h₂.le).symmGen
  · exact (h₂.ge.trans h).symmGen_symm

alias Relation.SymmGen.trans_antisymmRel := SymmGen.of_symmGen_of_antisymmRel

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: @Trans α α α (SymmGen (· <= ·)) (AntisymmRel (· <= ·)) (SymmGen (· <= ·))
  body: SymmGen.of_symmGen_of_antisymmRel

@[trans]

中文:
实例 :
  签名: @Trans α α α (SymmGen (· <= ·)) (AntisymmRel (· <= ·)) (SymmGen (· <= ·))
  定义体: SymmGen.of_symmGen_of_antisymmRel

@[trans]

Depends on / 依赖: SymmGen, SymmGen.of_symmGen_of_antisymmRel, of_symmGen_of_antisymmRel
-/
instance : @Trans α α α (SymmGen (· <= ·)) (AntisymmRel (· <= ·)) (SymmGen (· <= ·)) where
  trans := SymmGen.of_symmGen_of_antisymmRel

@[trans]
/--
theorem `Relation.SymmGen.of_antisymmRel_of_symmGen` / 定理 `Relation.SymmGen.of_antisymmRel_of_symmGen`

English:
theorem Relation.SymmGen.of_antisymmRel_of_symmGen
  proof: (h₂.symm.trans_antisymmRel h₁.symm).symm

alias AntisymmRel.trans_symmGen := SymmGen.of_antisymmRel_of_symmGen

中文:
定理 关系.SymmGen.of_antisymmRel_of_symmGen
  证明: (h₂.symm.trans_antisymmRel h₁.symm).symm

alias AntisymmRel.trans_symmGen := SymmGen.of_antisymmRel_of_symmGen

Depends on / 依赖: symm.trans_antisymmRel, trans_antisymmRel
-/
theorem Relation.SymmGen.of_antisymmRel_of_symmGen
    (h₁ : AntisymmRel (· <= ·) a b) (h₂ : SymmGen (· <= ·) b c) : SymmGen (· <= ·) a c :=
  (h₂.symm.trans_antisymmRel h₁.symm).symm

alias AntisymmRel.trans_symmGen := SymmGen.of_antisymmRel_of_symmGen

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: @Trans α α α (AntisymmRel (· <= ·)) (SymmGen (· <= ·)) (SymmGen (· <= ·))
  body: SymmGen.of_antisymmRel_of_symmGen

中文:
实例 :
  签名: @Trans α α α (AntisymmRel (· <= ·)) (SymmGen (· <= ·)) (SymmGen (· <= ·))
  定义体: SymmGen.of_antisymmRel_of_symmGen

Depends on / 依赖: SymmGen, SymmGen.of_antisymmRel_of_symmGen, of_antisymmRel_of_symmGen
-/
instance : @Trans α α α (AntisymmRel (· <= ·)) (SymmGen (· <= ·)) (SymmGen (· <= ·)) where
  trans := SymmGen.of_antisymmRel_of_symmGen

/--
theorem `AntisymmRel.symmGen_congr` / 定理 `AntisymmRel.symmGen_congr`

English:
theorem AntisymmRel.symmGen_congr
  given: (h₁ : AntisymmRel (· <= ·) a b) (h₂ : AntisymmRel (· <= ·) c d)
  proof: (h₁.symm.trans_symmGen h).trans_antisymmRel h₂
  mpr h := (h₁.trans_symmGen h).trans_antisymmRel h₂.symm

中文:
定理 AntisymmRel.symmGen_congr
  条件: (h₁ : AntisymmRel (· <= ·) a b) (h₂ : AntisymmRel (· <= ·) c d)
  证明: (h₁.symm.trans_symmGen h).trans_antisymmRel h₂
  mpr h := (h₁.trans_symmGen h).trans_antisymmRel h₂.symm

Depends on / 依赖: symm.trans_symmGen, trans_antisymmRel, trans_symmGen
-/
theorem AntisymmRel.symmGen_congr (h₁ : AntisymmRel (· <= ·) a b) (h₂ : AntisymmRel (· <= ·) c d) :
    SymmGen (· <= ·) a c ↔ SymmGen (· <= ·) b d where
  mp h := (h₁.symm.trans_symmGen h).trans_antisymmRel h₂
  mpr h := (h₁.trans_symmGen h).trans_antisymmRel h₂.symm

/--
theorem `AntisymmRel.symmGen_congr_left` / 定理 `AntisymmRel.symmGen_congr_left`

English:
theorem AntisymmRel.symmGen_congr_left
  given: (h : AntisymmRel (· <= ·) a b)
  proof: h.symmGen_congr .rfl

中文:
定理 AntisymmRel.symmGen_congr_left
  条件: (h : AntisymmRel (· <= ·) a b)
  证明: h.symmGen_congr .rfl

Depends on / 依赖: h.symmGen_congr, symmGen_congr
-/
theorem AntisymmRel.symmGen_congr_left (h : AntisymmRel (· <= ·) a b) :
    SymmGen (· <= ·) a c ↔ SymmGen (· <= ·) b c :=
  h.symmGen_congr .rfl

/--
theorem `AntisymmRel.symmGen_congr_right` / 定理 `AntisymmRel.symmGen_congr_right`

English:
theorem AntisymmRel.symmGen_congr_right
  given: (h : AntisymmRel (· <= ·) b c)
  proof: AntisymmRel.rfl.symmGen_congr h

中文:
定理 AntisymmRel.symmGen_congr_right
  条件: (h : AntisymmRel (· <= ·) b c)
  证明: AntisymmRel.rfl.symmGen_congr h

Depends on / 依赖: AntisymmRel, AntisymmRel.rfl.symmGen_congr, symmGen_congr
-/
theorem AntisymmRel.symmGen_congr_right (h : AntisymmRel (· <= ·) b c) :
    SymmGen (· <= ·) a b ↔ SymmGen (· <= ·) a c :=
  AntisymmRel.rfl.symmGen_congr h

end SymmGen

section Prod

variable (α β) [Preorder α] [Preorder β]

namespace Antisymmetrization

/--
Definition of `prodEquiv` / `prodEquiv` 的定义

English:
definition prodEquiv
  signature: : Antisymmetrization (α × β) (· <= ·) ≃o
  body: Quotient.lift (fun ab => (⟦ab.1⟧, ⟦ab.2⟧)) fun ab₁ ab₂ h =>
    Prod.ext (Quotient.sound ⟨h.1.1, h.2.1⟩) (Quotient.sound ⟨h.1.2, h.2.2⟩)
invFun := Function.uncurry Quotient.lift₂ (fun a b => ⟦(a, b)⟧)
    fun a₁ b₁ a₂ b₂ h₁ h₂ => Quotient.sound ⟨⟨h₁.1, h₂.1⟩, h₁.2, h₂.2⟩
  left_inv := by rintro ⟨_⟩;

中文:
定义 prodEquiv
  签名: : Antisymmetrization (α × β) (· <= ·) ≃o
  定义体: Quotient.lift (fun ab => (⟦ab.1⟧, ⟦ab.2⟧)) fun ab₁ ab₂ h =>
    Prod.ext (Quotient.sound ⟨h.1.1, h.2.1⟩) (Quotient.sound ⟨h.1.2, h.2.2⟩)
invFun := Function.uncurry Quotient.lift₂ (fun a b => ⟦(a, b)⟧)
    fun a₁ b₁ a₂ b₂ h₁ h₂ => Quotient.sound ⟨⟨h₁.1, h₂.1⟩, h₁.2, h₂.2⟩
  left_inv := by rintro ⟨_⟩;

Depends on / 依赖: Quotient, Quotient.lift
-/
def prodEquiv : Antisymmetrization (α × β) (· <= ·) ≃o
    Antisymmetrization α (· <= ·) × Antisymmetrization β (· <= ·) where
  toFun := Quotient.lift (fun ab => (⟦ab.1⟧, ⟦ab.2⟧)) fun ab₁ ab₂ h =>
    Prod.ext (Quotient.sound ⟨h.1.1, h.2.1⟩) (Quotient.sound ⟨h.1.2, h.2.2⟩)
invFun := Function.uncurry Quotient.lift₂ (fun a b => ⟦(a, b)⟧)
    fun a₁ b₁ a₂ b₂ h₁ h₂ => Quotient.sound ⟨⟨h₁.1, h₂.1⟩, h₁.2, h₂.2⟩
  left_inv := by rintro ⟨_⟩; rfl
  right_inv := by rintro ⟨⟨_⟩, ⟨_⟩⟩; rfl
  map_rel_iff' := by rintro ⟨_⟩ ⟨_⟩; rfl

/--
lemma `prodEquiv_apply_mk` / 引理 `prodEquiv_apply_mk`

English:
lemma prodEquiv_apply_mk
  given: {ab}
  statement: prodEquiv α β ⟦ab⟧ = (⟦ab.1⟧, ⟦ab.2⟧)
  proof: rfl

中文:
引理 prodEquiv_apply_mk
  条件: {ab}
  结论: prodEquiv α β ⟦ab⟧ = (⟦ab.1⟧, ⟦ab.2⟧)
  证明: rfl
-/
@[simp] lemma prodEquiv_apply_mk {ab} : prodEquiv α β ⟦ab⟧ = (⟦ab.1⟧, ⟦ab.2⟧) := rfl
/--
lemma `prodEquiv_symm_apply_mk` / 引理 `prodEquiv_symm_apply_mk`

English:
lemma prodEquiv_symm_apply_mk
  given: {a b}
  statement: (prodEquiv α β).symm (⟦a⟧, ⟦b⟧) = ⟦(a, b)⟧
  proof: rfl

中文:
引理 prodEquiv_symm_apply_mk
  条件: {a b}
  结论: (prodEquiv α β).symm (⟦a⟧, ⟦b⟧) = ⟦(a, b)⟧
  证明: rfl
-/
@[simp] lemma prodEquiv_symm_apply_mk {a b} : (prodEquiv α β).symm (⟦a⟧, ⟦b⟧) = ⟦(a, b)⟧ := rfl

end Antisymmetrization

end Prod
