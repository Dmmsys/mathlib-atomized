/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Data.Subtype
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.Prop
public import Mathlib.Order.Notation
public import Mathlib.Tactic.Spread
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Inhabit
public import Mathlib.Tactic.SimpRw
public import Mathlib.Tactic.GCongr.Core
public import Mathlib.Tactic.Attr.Register
public import Mathlib.Tactic.FastInstance

/-!
# Basic definitions about `≤` and `<`

This file proves basic results about orders, provides extensive dot notation, defines useful order
classes and allows to transfer order instances.

### Transferring orders

- `Order.Preimage`, `Preorder.lift`: Transfers a (pre)order on `β` to an order on `α`
  using a function `f : α → β`.
- `PartialOrder.lift`, `LinearOrder.lift`: Transfers a partial (resp., linear) order on `β` to a
  partial (resp., linear) order on `α` using an injective function `f`.

### Extra class

* `DenselyOrdered`: An order with no gap, i.e. for any two elements `a < b` there exists `c` such
  that `a < c < b`.

## Notes

`≤` and `<` are highly favored over `≥` and `>` in mathlib. The reason is that we can formulate all
lemmas using `≤`/`<`, and `rw` has trouble unifying `≤` and `≥`. Hence choosing one direction spares
us useless duplication.

Dot notation is particularly useful on `≤` (`LE.le`) and `<` (`LT.lt`). To that end, we
provide many aliases to dot notation-less lemmas. For example, `le_trans` is aliased with
`LE.le.trans` and can be used to construct `hab.trans hbc : a ≤ c` when `hab : a ≤ b`,
`hbc : b ≤ c`, `lt_of_le_of_lt` is aliased as `LE.le.trans_lt` and can be used to construct
`hab.trans hbc : a < c` when `hab : a ≤ b`, `hbc : b < c`.

## TODO

- expand module docs

## Tags

preorder, order, partial order, poset, linear order, chain
-/

@[expose] public section


open Function

variable {ι α β : Type*} {π : ι -> Type*}

/-! ### Bare relations -/

attribute [ext] LE

section LE

variable [LE α] {a b c : α}

/--
lemma `LE.le.ge` / 引理 `LE.le.ge`

English:
lemma LE.le.ge
  given: (h : a <= b)
  statement: b >= a
  proof: h

中文:
引理 LE.le.ge
  条件: (h : a <= b)
  结论: b >= a
  证明: h
-/
@[to_dual self] protected lemma LE.le.ge (h : a <= b) : b >= a := h
/--
lemma `GE.ge.le` / 引理 `GE.ge.le`

English:
lemma GE.ge.le
  given: (h : a >= b)
  statement: b <= a
  proof: h

@[to_dual trans_eq'] alias LE.le.trans_eq := le_of_le_of_eq
@[to_dual trans_ge] alias Eq.trans_le := le_of_eq_of_le

中文:
引理 GE.ge.le
  条件: (h : a >= b)
  结论: b <= a
  证明: h

@[to_dual trans_eq'] alias LE.le.trans_eq := le_of_le_of_eq
@[to_dual trans_ge] alias Eq.trans_le := le_of_eq_of_le
-/
@[to_dual self] protected lemma GE.ge.le (h : a >= b) : b <= a := h

@[to_dual trans_eq'] alias LE.le.trans_eq := le_of_le_of_eq
@[to_dual trans_ge] alias Eq.trans_le := le_of_eq_of_le

end LE

section LT

variable [LT α] {a b c : α}

/--
lemma `LT.lt.gt` / 引理 `LT.lt.gt`

English:
lemma LT.lt.gt
  given: (h : a < b)
  statement: b > a
  proof: h

中文:
引理 LT.lt.gt
  条件: (h : a < b)
  结论: b > a
  证明: h
-/
@[to_dual self] protected lemma LT.lt.gt (h : a < b) : b > a := h
/--
lemma `GT.gt.lt` / 引理 `GT.gt.lt`

English:
lemma GT.gt.lt
  given: (h : a > b)
  statement: b < a
  proof: h

@[to_dual trans_eq'] alias LT.lt.trans_eq := lt_of_lt_of_eq
@[to_dual trans_gt] alias Eq.trans_lt := lt_of_eq_of_lt

中文:
引理 GT.gt.lt
  条件: (h : a > b)
  结论: b < a
  证明: h

@[to_dual trans_eq'] alias LT.lt.trans_eq := lt_of_lt_of_eq
@[to_dual trans_gt] alias Eq.trans_lt := lt_of_eq_of_lt
-/
@[to_dual self] protected lemma GT.gt.lt (h : a > b) : b < a := h

@[to_dual trans_eq'] alias LT.lt.trans_eq := lt_of_lt_of_eq
@[to_dual trans_gt] alias Eq.trans_lt := lt_of_eq_of_lt

end LT

/-- Given a relation `R` on `β` and a function `f : α → β`, the preimage relation on `α` is defined
by `x ≤ y ↔ f x ≤ f y`. It is the unique relation on `α` making `f` a `RelEmbedding` (assuming `f`
is injective). -/
@[simp]
/--
Definition of `Order.Preimage` / `Order.Preimage` 的定义

English:
definition Order.Preimage
  signature: (f : α -> β) (s : β -> β -> Prop) (x y : α)
  body: s (f x) (f y)

@[inherit_doc] infixl:80 " ⁻¹'o " => Order.Preimage

中文:
定义 Order.原像
  签名: (f : α -> β) (s : β -> β -> 命题) (x y : α)
  定义体: s (f x) (f y)

@[inherit_doc] infixl:80 " ⁻¹'o " => Order.Preimage
-/
def Order.Preimage (f : α -> β) (s : β -> β -> Prop) (x y : α) : Prop := s (f x) (f y)

@[inherit_doc] infixl:80 " ⁻¹'o " => Order.Preimage

/--
Instance `Order.Preimage.decidable` / 实例 `Order.Preimage.decidable`

English:
instance Order.Preimage.decidable
  signature: (f : α -> β) (s : β -> β -> Prop) [H : DecidableRel s]
  body: fun _ _ => H _ _

中文:
实例 Order.原像.decidable
  签名: (f : α -> β) (s : β -> β -> 命题) [H : DecidableRel s]
  定义体: fun _ _ => H _ _
-/
instance Order.Preimage.decidable (f : α -> β) (s : β -> β -> Prop) [H : DecidableRel s] :
    DecidableRel (f ⁻¹'o s) := fun _ _ => H _ _

/-! ### Preorders -/

section Preorder

variable [Preorder α] {a b c d : α}

@[to_dual self]
/--
theorem `not_lt_iff_not_le_or_ge` / 定理 `not_lt_iff_not_le_or_ge`

English:
theorem not_lt_iff_not_le_or_ge
  statement: ¬a < b ↔ ¬a <= b ∨ b <= a
  proof: by
  rw [lt_iff_le_not_ge]; rw [Classical.not_and_iff_not_or_not]; rw [Classical.not_not]

中文:
定理 not_lt_iff_not_le_or_ge
  结论: ¬a < b ↔ ¬a <= b ∨ b <= a
  证明: by
  rw [lt_iff_le_not_ge]; rw [Classical.not_and_iff_not_or_not]; rw [Classical.not_not]

Depends on / 依赖: Classical, Classical.not_and_iff_not_or_not, Classical.not_not, lt_iff_le_not_ge, not_and_iff_not_or_not, not_not
-/
theorem not_lt_iff_not_le_or_ge : ¬a < b ↔ ¬a <= b ∨ b <= a := by
  rw [lt_iff_le_not_ge]; rw [Classical.not_and_iff_not_or_not]; rw [Classical.not_not]

-- Unnecessary brackets are here for readability
@[to_dual self]
/--
lemma `not_lt_iff_le_imp_ge` / 引理 `not_lt_iff_le_imp_ge`

English:
lemma not_lt_iff_le_imp_ge
  statement: ¬ a < b ↔ (a <= b -> b <= a)
  proof: by
  simp [not_lt_iff_not_le_or_ge, or_iff_not_imp_left]

@[simp]

中文:
引理 not_lt_iff_le_imp_ge
  结论: ¬ a < b ↔ (a <= b -> b <= a)
  证明: by
  simp [not_lt_iff_not_le_or_ge, or_iff_not_imp_left]

@[simp]

Depends on / 依赖: not_lt_iff_not_le_or_ge, or_iff_not_imp_left
-/
lemma not_lt_iff_le_imp_ge : ¬ a < b ↔ (a <= b -> b <= a) := by
  simp [not_lt_iff_not_le_or_ge, or_iff_not_imp_left]

@[simp]
/--
lemma `lt_self_iff_false` / 引理 `lt_self_iff_false`

English:
lemma lt_self_iff_false
  given: (x : α)
  statement: x < x ↔ False
  proof: ⟨lt_irrefl x, False.elim⟩

@[to_dual ge_trans'] alias le_trans' := ge_trans
@[to_dual gt_trans'] alias lt_trans' := gt_trans
@[to_dual trans'] alias LE.le.trans := le_trans
@[to_dual trans'] alias LT.lt.trans := lt_trans
@[to_dual trans_lt'] alias LE.le.trans_lt := lt_of_le_of_lt
@[to_dual trans_le'

中文:
引理 lt_self_iff_false
  条件: (x : α)
  结论: x < x ↔ 假
  证明: ⟨lt_irrefl x, False.elim⟩

@[to_dual ge_trans'] alias le_trans' := ge_trans
@[to_dual gt_trans'] alias lt_trans' := gt_trans
@[to_dual trans'] alias LE.le.trans := le_trans
@[to_dual trans'] alias LT.lt.trans := lt_trans
@[to_dual trans_lt'] alias LE.le.trans_lt := lt_of_le_of_lt
@[to_dual trans_le'

Depends on / 依赖: False.elim, lt_irrefl
-/
lemma lt_self_iff_false (x : α) : x < x ↔ False := ⟨lt_irrefl x, False.elim⟩

@[to_dual ge_trans'] alias le_trans' := ge_trans
@[to_dual gt_trans'] alias lt_trans' := gt_trans
@[to_dual trans'] alias LE.le.trans := le_trans
@[to_dual trans'] alias LT.lt.trans := lt_trans
@[to_dual trans_lt'] alias LE.le.trans_lt := lt_of_le_of_lt
@[to_dual trans_le'] alias LT.lt.trans_le := lt_of_lt_of_le

@[to_dual self] alias LE.le.lt_of_not_ge := lt_of_le_not_ge
@[to_dual self] alias LT.lt.le := le_of_lt
@[to_dual self] alias LT.lt.asymm := lt_asymm
@[to_dual self] alias LT.lt.not_gt := lt_asymm

@[to_dual ne'] alias LT.lt.ne := ne_of_lt
@[to_dual ge] alias Eq.le := le_of_eq

/--
lemma `LT.lt.false` / 引理 `LT.lt.false`

English:
lemma LT.lt.false
  statement: a < a -> False
  proof: lt_irrefl a

中文:
引理 LT.lt.false
  结论: a < a -> 假
  证明: lt_irrefl a
-/
protected lemma LT.lt.false : a < a -> False := lt_irrefl a

/--
lemma `Eq.not_lt` / 引理 `Eq.not_lt`

English:
lemma Eq.not_lt
  given: (hab : a = b)
  statement: ¬a < b
  proof: fun h' => h'.ne hab

@[to_dual ne_of_not_ge]

中文:
引理 相等.not_lt
  条件: (hab : a = b)
  结论: ¬a < b
  证明: fun h' => h'.ne hab

@[to_dual ne_of_not_ge]
-/
@[to_dual not_gt] protected lemma Eq.not_lt (hab : a = b) : ¬a < b := fun h' => h'.ne hab

@[to_dual ne_of_not_ge]
/--
theorem `ne_of_not_le` / 定理 `ne_of_not_le`

English:
theorem ne_of_not_le
  given: (h : ¬a <= b)
  statement: a != b
  proof: fun hab => h (le_of_eq hab)

@[simp, to_dual self]

中文:
定理 ne_of_not_le
  条件: (h : ¬a <= b)
  结论: a != b
  证明: fun hab => h (le_of_eq hab)

@[simp, to_dual self]

Depends on / 依赖: le_of_eq
-/
theorem ne_of_not_le (h : ¬a <= b) : a != b := fun hab => h (le_of_eq hab)

@[simp, to_dual self]
/--
lemma `le_of_subsingleton` / 引理 `le_of_subsingleton`

English:
lemma le_of_subsingleton
  given: [Subsingleton α]
  statement: a <= b
  proof: (Subsingleton.elim a b).le

中文:
引理 le_of_subsingleton
  条件: [子单例 α]
  结论: a <= b
  证明: (Subsingleton.elim a b).le

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
lemma le_of_subsingleton [Subsingleton α] : a <= b := (Subsingleton.elim a b).le

-- Making this a @[simp] lemma causes confluence problems downstream.
@[nontriviality, to_dual self]
/--
lemma `not_lt_of_subsingleton` / 引理 `not_lt_of_subsingleton`

English:
lemma not_lt_of_subsingleton
  given: [Subsingleton α]
  statement: ¬a < b
  proof: (Subsingleton.elim a b).not_lt

@[to_dual le_of_forall_ge]

中文:
引理 not_lt_of_subsingleton
  条件: [子单例 α]
  结论: ¬a < b
  证明: (Subsingleton.elim a b).not_lt

@[to_dual le_of_forall_ge]

Depends on / 依赖: Subsingleton, Subsingleton.elim, not_lt
-/
lemma not_lt_of_subsingleton [Subsingleton α] : ¬a < b := (Subsingleton.elim a b).not_lt

@[to_dual le_of_forall_ge]
/--
theorem `le_of_forall_le` / 定理 `le_of_forall_le`

English:
theorem le_of_forall_le
  given: (H : forall c, c <= a -> c <= b)
  statement: a <= b
  proof: H _ le_rfl

@[to_dual forall_ge_iff_le]

中文:
定理 le_of_对任意_le
  条件: (H : 对任意 c, c <= a -> c <= b)
  结论: a <= b
  证明: H _ le_rfl

@[to_dual forall_ge_iff_le]

Depends on / 依赖: le_rfl
-/
theorem le_of_forall_le (H : forall c, c <= a -> c <= b) : a <= b := H _ le_rfl

@[to_dual forall_ge_iff_le]
/--
theorem `forall_le_iff_le` / 定理 `forall_le_iff_le`

English:
theorem forall_le_iff_le
  statement: (forall ⦃c⦄, c <= a -> c <= b) ↔ a <= b
  proof: ⟨le_of_forall_le, fun h _ hca => le_trans hca h⟩

中文:
定理 对任意_le_iff_le
  结论: (对任意 ⦃c⦄, c <= a -> c <= b) ↔ a <= b
  证明: ⟨le_of_forall_le, fun h _ hca => le_trans hca h⟩

Depends on / 依赖: le_of_forall_le, le_trans
-/
theorem forall_le_iff_le : (forall ⦃c⦄, c <= a -> c <= b) ↔ a <= b :=
  ⟨le_of_forall_le, fun h _ hca => le_trans hca h⟩

/-- monotonicity of `≤` with respect to `→` -/
@[gcongr, to_dual self (reorder := a b, c d, h₁ h₂)]
/--
theorem `le_imp_le_of_le_of_le` / 定理 `le_imp_le_of_le_of_le`

English:
theorem le_imp_le_of_le_of_le
  given: (h₁ : c <= a) (h₂ : b <= d)
  statement: a <= b -> c <= d
  proof: fun hab => (h₁.trans hab).trans h₂

中文:
定理 le_imp_le_of_le_of_le
  条件: (h₁ : c <= a) (h₂ : b <= d)
  结论: a <= b -> c <= d
  证明: fun hab => (h₁.trans hab).trans h₂
-/
theorem le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d) : a <= b -> c <= d :=
  fun hab => (h₁.trans hab).trans h₂

/-- monotonicity of `<` with respect to `→` -/
@[gcongr, to_dual self (reorder := a b, c d, h₁ h₂)]
/--
theorem `lt_imp_lt_of_le_of_le` / 定理 `lt_imp_lt_of_le_of_le`

English:
theorem lt_imp_lt_of_le_of_le
  given: (h₁ : c <= a) (h₂ : b <= d)
  statement: a < b -> c < d
  proof: fun hab => (h₁.trans_lt hab).trans_le h₂

中文:
定理 lt_imp_lt_of_le_of_le
  条件: (h₁ : c <= a) (h₂ : b <= d)
  结论: a < b -> c < d
  证明: fun hab => (h₁.trans_lt hab).trans_le h₂

Depends on / 依赖: trans_le, trans_lt
-/
theorem lt_imp_lt_of_le_of_le (h₁ : c <= a) (h₂ : b <= d) : a < b -> c < d :=
  fun hab => (h₁.trans_lt hab).trans_le h₂

/-- monotonicity of `≥` with respect to `→` -/
@[gcongr, to_dual self (reorder := a b, c d, h₁ h₂)]
/--
theorem `ge_imp_ge_of_le_of_le` / 定理 `ge_imp_ge_of_le_of_le`

English:
theorem ge_imp_ge_of_le_of_le
  given: (h₁ : a <= c) (h₂ : d <= b)
  statement: a >= b -> c >= d
  proof: fun hab => (h₂.trans hab).trans h₁

中文:
定理 ge_imp_ge_of_le_of_le
  条件: (h₁ : a <= c) (h₂ : d <= b)
  结论: a >= b -> c >= d
  证明: fun hab => (h₂.trans hab).trans h₁
-/
theorem ge_imp_ge_of_le_of_le (h₁ : a <= c) (h₂ : d <= b) : a >= b -> c >= d :=
  fun hab => (h₂.trans hab).trans h₁

/-- monotonicity of `>` with respect to `→` -/
@[gcongr, to_dual self (reorder := a b, c d, h₁ h₂)]
/--
theorem `gt_imp_gt_of_le_of_le` / 定理 `gt_imp_gt_of_le_of_le`

English:
theorem gt_imp_gt_of_le_of_le
  given: (h₁ : a <= c) (h₂ : d <= b)
  statement: a > b -> c > d
  proof: fun hab => (h₂.trans_lt hab).trans_le h₁

中文:
定理 gt_imp_gt_of_le_of_le
  条件: (h₁ : a <= c) (h₂ : d <= b)
  结论: a > b -> c > d
  证明: fun hab => (h₂.trans_lt hab).trans_le h₁

Depends on / 依赖: trans_le, trans_lt
-/
theorem gt_imp_gt_of_le_of_le (h₁ : a <= c) (h₂ : d <= b) : a > b -> c > d :=
  fun hab => (h₂.trans_lt hab).trans_le h₁

attribute [gcongr strict] lt_of_lt_of_le lt_of_lt_of_le'

namespace Mathlib.Tactic.GCongr
open Lean Meta

/-- See if the term is `a < b` and the goal is `a ≤ b`. -/
@[gcongr_forward] meta def exactLeOfLt : ForwardExt where
  eval h goal := do
    let le_of_lt := .const ``le_of_lt [← mkFreshLevelMVar]
    let (mvars, _, _) ← forallMetaTelescope (← inferType le_of_lt)
    mvars[4]!.mvarId!.assignIfDefEq h
    goal.assignIfDefEq (mkAppN le_of_lt mvars)

end Mathlib.Tactic.GCongr

end Preorder

/-! ### Partial order -/

section PartialOrder

variable [PartialOrder α] {a b : α}

@[to_dual lt_of_le'] -- TODO: should be called `gt_of_ge`
/--
theorem `Ne.lt_of_le` / 定理 `Ne.lt_of_le`

English:
theorem Ne.lt_of_le
  statement: a != b -> a <= b -> a < b
  proof: flip lt_of_le_of_ne

中文:
定理 不等.lt_of_le
  结论: a != b -> a <= b -> a < b
  证明: flip lt_of_le_of_ne

Depends on / 依赖: lt_of_le_of_ne
-/
theorem Ne.lt_of_le : a != b -> a <= b -> a < b :=
  flip lt_of_le_of_ne

namespace LE.le

@[to_dual antisymm'] alias antisymm := le_antisymm
@[to_dual lt_of_ne'] alias lt_of_ne := lt_of_le_of_ne

@[to_dual lt_iff_ne']
/--
theorem `lt_iff_ne` / 定理 `lt_iff_ne`

English:
theorem lt_iff_ne
  given: (h : a <= b)
  statement: a < b ↔ a != b
  proof: ⟨ne_of_lt, h.lt_of_ne⟩

@[to_dual not_lt_iff_eq']

中文:
定理 lt_iff_ne
  条件: (h : a <= b)
  结论: a < b ↔ a != b
  证明: ⟨ne_of_lt, h.lt_of_ne⟩

@[to_dual not_lt_iff_eq']

Depends on / 依赖: h.lt_of_ne, lt_of_ne, ne_of_lt
-/
theorem lt_iff_ne (h : a <= b) : a < b ↔ a != b := ⟨ne_of_lt, h.lt_of_ne⟩

@[to_dual not_lt_iff_eq']
/--
theorem `not_lt_iff_eq` / 定理 `not_lt_iff_eq`

English:
theorem not_lt_iff_eq
  given: (h : a <= b)
  statement: ¬a < b ↔ a = b
  proof: h.lt_iff_ne.not_left

@[to_dual ge_iff_eq']

中文:
定理 not_lt_iff_eq
  条件: (h : a <= b)
  结论: ¬a < b ↔ a = b
  证明: h.lt_iff_ne.not_left

@[to_dual ge_iff_eq']

Depends on / 依赖: h.lt_iff_ne.not_left, lt_iff_ne, not_left
-/
theorem not_lt_iff_eq (h : a <= b) : ¬a < b ↔ a = b := h.lt_iff_ne.not_left

@[to_dual ge_iff_eq']
/--
theorem `ge_iff_eq` / 定理 `ge_iff_eq`

English:
theorem ge_iff_eq
  given: (h : a <= b)
  statement: b <= a ↔ a = b
  proof: ⟨h.antisymm, Eq.ge⟩

中文:
定理 ge_iff_eq
  条件: (h : a <= b)
  结论: b <= a ↔ a = b
  证明: ⟨h.antisymm, Eq.ge⟩

Depends on / 依赖: Eq.ge, antisymm, h.antisymm
-/
theorem ge_iff_eq (h : a <= b) : b <= a ↔ a = b := ⟨h.antisymm, Eq.ge⟩

end LE.le

-- Unnecessary brackets are here for readability
@[to_dual le_imp_eq_iff_le_imp_ge']
/--
lemma `le_imp_eq_iff_le_imp_ge` / 引理 `le_imp_eq_iff_le_imp_ge`

English:
lemma le_imp_eq_iff_le_imp_ge
  statement: (a <= b -> a = b) ↔ (a <= b -> b <= a) where
  proof: (h hab).ge
  mpr h hab := hab.antisymm (h hab)

中文:
引理 le_imp_eq_iff_le_imp_ge
  结论: (a <= b -> a = b) ↔ (a <= b -> b <= a) where
  证明: (h hab).ge
  mpr h hab := hab.antisymm (h hab)
-/
lemma le_imp_eq_iff_le_imp_ge : (a <= b -> a = b) ↔ (a <= b -> b <= a) where
  mp h hab := (h hab).ge
  mpr h hab := hab.antisymm (h hab)

-- See Note [decidable namespace]
@[to_dual le_iff_eq_or_lt']
/--
theorem `Decidable.le_iff_eq_or_lt` / 定理 `Decidable.le_iff_eq_or_lt`

English:
theorem Decidable.le_iff_eq_or_lt
  given: [DecidableLE α]
  statement: a <= b ↔ a = b ∨ a < b
  proof: Decidable.le_iff_lt_or_eq.trans or_comm

@[to_dual le_iff_eq_or_lt']

中文:
定理 可判定.le_iff_eq_or_lt
  条件: [DecidableLE α]
  结论: a <= b ↔ a = b ∨ a < b
  证明: Decidable.le_iff_lt_or_eq.trans or_comm

@[to_dual le_iff_eq_or_lt']
-/
protected theorem Decidable.le_iff_eq_or_lt [DecidableLE α] : a <= b ↔ a = b ∨ a < b :=
  Decidable.le_iff_lt_or_eq.trans or_comm

@[to_dual le_iff_eq_or_lt']
/--
theorem `le_iff_eq_or_lt` / 定理 `le_iff_eq_or_lt`

English:
theorem le_iff_eq_or_lt
  statement: a <= b ↔ a = b ∨ a < b
  proof: le_iff_lt_or_eq.trans or_comm

@[to_dual lt_iff_le_and_ne']

中文:
定理 le_iff_eq_or_lt
  结论: a <= b ↔ a = b ∨ a < b
  证明: le_iff_lt_or_eq.trans or_comm

@[to_dual lt_iff_le_and_ne']

Depends on / 依赖: le_iff_lt_or_eq, le_iff_lt_or_eq.trans, or_comm
-/
theorem le_iff_eq_or_lt : a <= b ↔ a = b ∨ a < b := le_iff_lt_or_eq.trans or_comm

@[to_dual lt_iff_le_and_ne']
/--
theorem `lt_iff_le_and_ne` / 定理 `lt_iff_le_and_ne`

English:
theorem lt_iff_le_and_ne
  statement: a < b ↔ a <= b ∧ a != b
  proof: ⟨fun h => ⟨le_of_lt h, ne_of_lt h⟩, fun ⟨h1, h2⟩ => h1.lt_of_ne h2⟩

中文:
定理 lt_iff_le_and_ne
  结论: a < b ↔ a <= b ∧ a != b
  证明: ⟨fun h => ⟨le_of_lt h, ne_of_lt h⟩, fun ⟨h1, h2⟩ => h1.lt_of_ne h2⟩

Depends on / 依赖: h1.lt_of_ne, le_of_lt, lt_of_ne, ne_of_lt
-/
theorem lt_iff_le_and_ne : a < b ↔ a <= b ∧ a != b :=
  ⟨fun h => ⟨le_of_lt h, ne_of_lt h⟩, fun ⟨h1, h2⟩ => h1.lt_of_ne h2⟩

-- See Note [decidable namespace]
@[to_dual eq_iff_ge_not_gt]
/--
theorem `Decidable.eq_iff_le_not_lt` / 定理 `Decidable.eq_iff_le_not_lt`

English:
theorem Decidable.eq_iff_le_not_lt
  given: [DecidableLE α]
  statement: a = b ↔ a <= b ∧ ¬a < b
  proof: ⟨fun h => ⟨h.le, h ▸ lt_irrefl _⟩, fun ⟨h₁, h₂⟩ =>
h₁.antisymm Decidable.byContradiction fun h₃ => h₂ (h₁.lt_of_not_ge h₃)⟩

@[to_dual eq_iff_ge_not_gt]

中文:
定理 可判定.eq_iff_le_not_lt
  条件: [DecidableLE α]
  结论: a = b ↔ a <= b ∧ ¬a < b
  证明: ⟨fun h => ⟨h.le, h ▸ lt_irrefl _⟩, fun ⟨h₁, h₂⟩ =>
h₁.antisymm Decidable.byContradiction fun h₃ => h₂ (h₁.lt_of_not_ge h₃)⟩

@[to_dual eq_iff_ge_not_gt]
-/
protected theorem Decidable.eq_iff_le_not_lt [DecidableLE α] : a = b ↔ a <= b ∧ ¬a < b :=
  ⟨fun h => ⟨h.le, h ▸ lt_irrefl _⟩, fun ⟨h₁, h₂⟩ =>
h₁.antisymm Decidable.byContradiction fun h₃ => h₂ (h₁.lt_of_not_ge h₃)⟩

@[to_dual eq_iff_ge_not_gt]
/--
theorem `eq_iff_le_not_lt` / 定理 `eq_iff_le_not_lt`

English:
theorem eq_iff_le_not_lt
  statement: a = b ↔ a <= b ∧ ¬a < b
  proof: open scoped Classical in
  Decidable.eq_iff_le_not_lt

中文:
定理 eq_iff_le_not_lt
  结论: a = b ↔ a <= b ∧ ¬a < b
  证明: open scoped Classical in
  Decidable.eq_iff_le_not_lt

Depends on / 依赖: Classical, scoped
-/
theorem eq_iff_le_not_lt : a = b ↔ a <= b ∧ ¬a < b := open scoped Classical in
  Decidable.eq_iff_le_not_lt

-- See Note [decidable namespace]
@[to_dual eq_or_lt_of_le']
/--
theorem `Decidable.eq_or_lt_of_le` / 定理 `Decidable.eq_or_lt_of_le`

English:
theorem Decidable.eq_or_lt_of_le
  given: [DecidableLE α] (h : a <= b)
  statement: a = b ∨ a < b
  proof: (Decidable.lt_or_eq_of_le h).symm

@[to_dual eq_or_lt_of_le']

中文:
定理 可判定.eq_or_lt_of_le
  条件: [DecidableLE α] (h : a <= b)
  结论: a = b ∨ a < b
  证明: (Decidable.lt_or_eq_of_le h).symm

@[to_dual eq_or_lt_of_le']
-/
protected theorem Decidable.eq_or_lt_of_le [DecidableLE α] (h : a <= b) : a = b ∨ a < b :=
  (Decidable.lt_or_eq_of_le h).symm

@[to_dual eq_or_lt_of_le']
/--
theorem `eq_or_lt_of_le` / 定理 `eq_or_lt_of_le`

English:
theorem eq_or_lt_of_le
  given: (h : a <= b)
  statement: a = b ∨ a < b
  proof: (lt_or_eq_of_le h).symm

@[to_dual lt_or_eq_dec'] alias LE.le.lt_or_eq_dec := Decidable.lt_or_eq_of_le
@[to_dual eq_or_lt_dec'] alias LE.le.eq_or_lt_dec := Decidable.eq_or_lt_of_le
@[to_dual lt_or_eq'] alias LE.le.lt_or_eq := lt_or_eq_of_le
@[to_dual eq_or_lt'] alias LE.le.eq_or_lt := eq_or_lt_of_le

中文:
定理 eq_or_lt_of_le
  条件: (h : a <= b)
  结论: a = b ∨ a < b
  证明: (lt_or_eq_of_le h).symm

@[to_dual lt_or_eq_dec'] alias LE.le.lt_or_eq_dec := Decidable.lt_or_eq_of_le
@[to_dual eq_or_lt_dec'] alias LE.le.eq_or_lt_dec := Decidable.eq_or_lt_of_le
@[to_dual lt_or_eq'] alias LE.le.lt_or_eq := lt_or_eq_of_le
@[to_dual eq_or_lt'] alias LE.le.eq_or_lt := eq_or_lt_of_le

Depends on / 依赖: lt_or_eq_of_le
-/
theorem eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b := (lt_or_eq_of_le h).symm

@[to_dual lt_or_eq_dec'] alias LE.le.lt_or_eq_dec := Decidable.lt_or_eq_of_le
@[to_dual eq_or_lt_dec'] alias LE.le.eq_or_lt_dec := Decidable.eq_or_lt_of_le
@[to_dual lt_or_eq'] alias LE.le.lt_or_eq := lt_or_eq_of_le
@[to_dual eq_or_lt'] alias LE.le.eq_or_lt := eq_or_lt_of_le

@[to_dual eq_of_le_of_not_lt']
/--
theorem `eq_of_le_of_not_lt` / 定理 `eq_of_le_of_not_lt`

English:
theorem eq_of_le_of_not_lt
  given: (h₁ : a <= b) (h₂ : ¬a < b)
  statement: a = b
  proof: h₁.eq_or_lt.resolve_right h₂

@[to_dual eq_of_not_lt'] alias LE.le.eq_of_not_lt := eq_of_le_of_not_lt

@[to_dual ge_iff_gt]

中文:
定理 eq_of_le_of_not_lt
  条件: (h₁ : a <= b) (h₂ : ¬a < b)
  结论: a = b
  证明: h₁.eq_or_lt.resolve_right h₂

@[to_dual eq_of_not_lt'] alias LE.le.eq_of_not_lt := eq_of_le_of_not_lt

@[to_dual ge_iff_gt]

Depends on / 依赖: eq_or_lt, eq_or_lt.resolve_right, resolve_right
-/
theorem eq_of_le_of_not_lt (h₁ : a <= b) (h₂ : ¬a < b) : a = b := h₁.eq_or_lt.resolve_right h₂

@[to_dual eq_of_not_lt'] alias LE.le.eq_of_not_lt := eq_of_le_of_not_lt

@[to_dual ge_iff_gt]
/--
theorem `Ne.le_iff_lt` / 定理 `Ne.le_iff_lt`

English:
theorem Ne.le_iff_lt
  given: (h : a != b)
  statement: a <= b ↔ a < b
  proof: ⟨fun h' => lt_of_le_of_ne h' h, fun h => h.le⟩

@[to_dual not_ge_or_not_le]

中文:
定理 不等.le_iff_lt
  条件: (h : a != b)
  结论: a <= b ↔ a < b
  证明: ⟨fun h' => lt_of_le_of_ne h' h, fun h => h.le⟩

@[to_dual not_ge_or_not_le]

Depends on / 依赖: h.le, lt_of_le_of_ne
-/
theorem Ne.le_iff_lt (h : a != b) : a <= b ↔ a < b := ⟨fun h' => lt_of_le_of_ne h' h, fun h => h.le⟩

@[to_dual not_ge_or_not_le]
/--
theorem `Ne.not_le_or_not_ge` / 定理 `Ne.not_le_or_not_ge`

English:
theorem Ne.not_le_or_not_ge
  given: (h : a != b)
  statement: ¬a <= b ∨ ¬b <= a
  proof: not_and_or.1 le_antisymm_iff.not.1 h

中文:
定理 不等.not_le_or_not_ge
  条件: (h : a != b)
  结论: ¬a <= b ∨ ¬b <= a
  证明: not_and_or.1 le_antisymm_iff.not.1 h

Depends on / 依赖: le_antisymm_iff, le_antisymm_iff.not, not_and_or
-/
theorem Ne.not_le_or_not_ge (h : a != b) : ¬a <= b ∨ ¬b <= a := not_and_or.1 le_antisymm_iff.not.1 h

-- See Note [decidable namespace]
@[to_dual ne_iff_gt_iff_ge]
/--
theorem `Decidable.ne_iff_lt_iff_le` / 定理 `Decidable.ne_iff_lt_iff_le`

English:
theorem Decidable.ne_iff_lt_iff_le
  given: [DecidableEq α]
  statement: (a != b ↔ a < b) ↔ a <= b
  proof: ⟨fun h => Decidable.byCases le_of_eq (le_of_lt ∘ h.mp), fun h => ⟨lt_of_le_of_ne h, ne_of_lt⟩⟩

@[to_dual (attr := simp) ne_iff_gt_iff_ge]

中文:
定理 可判定.ne_iff_lt_iff_le
  条件: [DecidableEq α]
  结论: (a != b ↔ a < b) ↔ a <= b
  证明: ⟨fun h => Decidable.byCases le_of_eq (le_of_lt ∘ h.mp), fun h => ⟨lt_of_le_of_ne h, ne_of_lt⟩⟩

@[to_dual (attr := simp) ne_iff_gt_iff_ge]
-/
protected theorem Decidable.ne_iff_lt_iff_le [DecidableEq α] : (a != b ↔ a < b) ↔ a <= b :=
  ⟨fun h => Decidable.byCases le_of_eq (le_of_lt ∘ h.mp), fun h => ⟨lt_of_le_of_ne h, ne_of_lt⟩⟩

@[to_dual (attr := simp) ne_iff_gt_iff_ge]
/--
theorem `ne_iff_lt_iff_le` / 定理 `ne_iff_lt_iff_le`

English:
theorem ne_iff_lt_iff_le
  statement: (a != b ↔ a < b) ↔ a <= b
  proof: open scoped Classical in
  Decidable.ne_iff_lt_iff_le

@[to_dual eq_of_forall_ge_iff]

中文:
定理 ne_iff_lt_iff_le
  结论: (a != b ↔ a < b) ↔ a <= b
  证明: open scoped Classical in
  Decidable.ne_iff_lt_iff_le

@[to_dual eq_of_forall_ge_iff]

Depends on / 依赖: Classical, scoped
-/
theorem ne_iff_lt_iff_le : (a != b ↔ a < b) ↔ a <= b := open scoped Classical in
  Decidable.ne_iff_lt_iff_le

@[to_dual eq_of_forall_ge_iff]
/--
lemma `eq_of_forall_le_iff` / 引理 `eq_of_forall_le_iff`

English:
lemma eq_of_forall_le_iff
  given: (H : forall c, c <= a ↔ c <= b)
  statement: a = b
  proof: ((H _).1 le_rfl).antisymm ((H _).2 le_rfl)

中文:
引理 eq_of_对任意_le_iff
  条件: (H : 对任意 c, c <= a ↔ c <= b)
  结论: a = b
  证明: ((H _).1 le_rfl).antisymm ((H _).2 le_rfl)

Depends on / 依赖: antisymm, le_rfl
-/
lemma eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b) : a = b :=
  ((H _).1 le_rfl).antisymm ((H _).2 le_rfl)

/--
lemma `commutative_of_le` / 引理 `commutative_of_le`

English:
lemma commutative_of_le
  given: {f : β -> β -> α} (comm : forall a b, f a b <= f b a)
  statement: forall a b, f a b = f b a
  proof: fun _ _ => (comm _ _).antisymm comm _ _

中文:
引理 commutative_of_le
  条件: {f : β -> β -> α} (comm : 对任意 a b, f a b <= f b a)
  结论: 对任意 a b, f a b = f b a
  证明: fun _ _ => (comm _ _).antisymm comm _ _

Depends on / 依赖: antisymm
-/
lemma commutative_of_le {f : β -> β -> α} (comm : forall a b, f a b <= f b a) : forall a b, f a b = f b a :=
fun _ _ => (comm _ _).antisymm comm _ _

/--
lemma `associative_of_commutative_of_le` / 引理 `associative_of_commutative_of_le`

English:
lemma associative_of_commutative_of_le
  statement: {f : α -> α -> α} (comm : Std.Commutative f)
  proof: le_antisymm (assoc _ _ _) by
      rw [comm.comm]; rw [comm.comm b]; rw [comm.comm _ c]; rw [comm.comm a]
      exact assoc ..

中文:
引理 associative_of_commutative_of_le
  结论: {f : α -> α -> α} (comm : Std.交换 f)
  证明: le_antisymm (assoc _ _ _) by
      rw [comm.comm]; rw [comm.comm b]; rw [comm.comm _ c]; rw [comm.comm a]
      exact assoc ..

Depends on / 依赖: comm.comm, le_antisymm
-/
lemma associative_of_commutative_of_le {f : α -> α -> α} (comm : Std.Commutative f)
    (assoc : forall a b c, f (f a b) c <= f a (f b c)) : Std.Associative f where
  assoc a b c :=
le_antisymm (assoc _ _ _) by
      rw [comm.comm]; rw [comm.comm b]; rw [comm.comm _ c]; rw [comm.comm a]
      exact assoc ..

end PartialOrder

section LinearOrder
variable [LinearOrder α] {a b : α}

namespace LE.le

@[to_dual lt_or_ge]
/--
lemma `gt_or_le` / 引理 `gt_or_le`

English:
lemma gt_or_le
  given: (h : a <= b) (c : α)
  statement: a < c ∨ c <= b
  proof: (lt_or_ge a c).imp id h.trans'

@[to_dual le_or_gt]

中文:
引理 gt_or_le
  条件: (h : a <= b) (c : α)
  结论: a < c ∨ c <= b
  证明: (lt_or_ge a c).imp id h.trans'

@[to_dual le_or_gt]

Depends on / 依赖: h.trans, lt_or_ge
-/
lemma gt_or_le (h : a <= b) (c : α) : a < c ∨ c <= b := (lt_or_ge a c).imp id h.trans'

@[to_dual le_or_gt]
/--
lemma `ge_or_lt` / 引理 `ge_or_lt`

English:
lemma ge_or_lt
  given: (h : a <= b) (c : α)
  statement: a <= c ∨ c < b
  proof: (le_or_gt a c).imp id h.trans_lt'

@[to_dual le_or_ge]

中文:
引理 ge_or_lt
  条件: (h : a <= b) (c : α)
  结论: a <= c ∨ c < b
  证明: (le_or_gt a c).imp id h.trans_lt'

@[to_dual le_or_ge]

Depends on / 依赖: h.trans_lt, le_or_gt, trans_lt
-/
lemma ge_or_lt (h : a <= b) (c : α) : a <= c ∨ c < b := (le_or_gt a c).imp id h.trans_lt'

@[to_dual le_or_ge]
/--
lemma `ge_or_le` / 引理 `ge_or_le`

English:
lemma ge_or_le
  given: (h : a <= b) (c : α)
  statement: a <= c ∨ c <= b
  proof: (h.gt_or_le c).imp le_of_lt id

中文:
引理 ge_or_le
  条件: (h : a <= b) (c : α)
  结论: a <= c ∨ c <= b
  证明: (h.gt_or_le c).imp le_of_lt id

Depends on / 依赖: gt_or_le, h.gt_or_le, le_of_lt
-/
lemma ge_or_le (h : a <= b) (c : α) : a <= c ∨ c <= b := (h.gt_or_le c).imp le_of_lt id

end LE.le

namespace LT.lt

@[to_dual lt_or_gt]
/--
lemma `gt_or_lt` / 引理 `gt_or_lt`

English:
lemma gt_or_lt
  given: (h : a < b) (c : α)
  statement: a < c ∨ c < b
  proof: (le_or_gt b c).imp h.trans_le id

中文:
引理 gt_or_lt
  条件: (h : a < b) (c : α)
  结论: a < c ∨ c < b
  证明: (le_or_gt b c).imp h.trans_le id

Depends on / 依赖: h.trans_le, le_or_gt, trans_le
-/
lemma gt_or_lt (h : a < b) (c : α) : a < c ∨ c < b := (le_or_gt b c).imp h.trans_le id

end LT.lt

@[to_dual gt_or_lt]
/--
theorem `Ne.lt_or_gt` / 定理 `Ne.lt_or_gt`

English:
theorem Ne.lt_or_gt
  given: (h : a != b)
  statement: a < b ∨ b < a
  proof: lt_or_gt_of_ne h

中文:
定理 不等.lt_or_gt
  条件: (h : a != b)
  结论: a < b ∨ b < a
  证明: lt_or_gt_of_ne h

Depends on / 依赖: lt_or_gt_of_ne
-/
theorem Ne.lt_or_gt (h : a != b) : a < b ∨ b < a :=
  lt_or_gt_of_ne h

/-- A version of `ne_iff_lt_or_gt` with LHS and RHS reversed. -/
@[to_dual lt_or_gt_iff_ne', simp]
/--
theorem `lt_or_lt_iff_ne` / 定理 `lt_or_lt_iff_ne`

English:
theorem lt_or_lt_iff_ne
  statement: a < b ∨ b < a ↔ a != b
  proof: ne_iff_lt_or_gt.symm

@[to_dual not_lt_iff_eq_or_lt']

中文:
定理 lt_or_lt_iff_ne
  结论: a < b ∨ b < a ↔ a != b
  证明: ne_iff_lt_or_gt.symm

@[to_dual not_lt_iff_eq_or_lt']

Depends on / 依赖: ne_iff_lt_or_gt, ne_iff_lt_or_gt.symm
-/
theorem lt_or_lt_iff_ne : a < b ∨ b < a ↔ a != b :=
  ne_iff_lt_or_gt.symm

@[to_dual not_lt_iff_eq_or_lt']
/--
theorem `not_lt_iff_eq_or_lt` / 定理 `not_lt_iff_eq_or_lt`

English:
theorem not_lt_iff_eq_or_lt
  statement: ¬a < b ↔ a = b ∨ b < a
  proof: not_lt.trans Decidable.le_iff_eq_or_lt.trans or_congr eq_comm Iff.rfl

@[to_dual exists_le_of_linear]

中文:
定理 not_lt_iff_eq_or_lt
  结论: ¬a < b ↔ a = b ∨ b < a
  证明: not_lt.trans Decidable.le_iff_eq_or_lt.trans or_congr eq_comm Iff.rfl

@[to_dual exists_le_of_linear]

Depends on / 依赖: Decidable, Decidable.le_iff_eq_or_lt.trans, Iff.rfl, eq_comm, le_iff_eq_or_lt, not_lt, not_lt.trans, or_congr
-/
theorem not_lt_iff_eq_or_lt : ¬a < b ↔ a = b ∨ b < a :=
not_lt.trans Decidable.le_iff_eq_or_lt.trans or_congr eq_comm Iff.rfl

@[to_dual exists_le_of_linear]
/--
theorem `exists_ge_of_linear` / 定理 `exists_ge_of_linear`

English:
theorem exists_ge_of_linear
  given: (a b : α)
  statement: exists c, a <= c ∧ b <= c
  proof: match le_total a b with
  | Or.inl h => ⟨_, h, le_rfl⟩
  | Or.inr h => ⟨_, le_rfl, h⟩

@[to_dual exists_forall_le_and]

中文:
定理 存在_ge_of_linear
  条件: (a b : α)
  结论: 存在 c, a <= c ∧ b <= c
  证明: match le_total a b with
  | Or.inl h => ⟨_, h, le_rfl⟩
  | Or.inr h => ⟨_, le_rfl, h⟩

@[to_dual exists_forall_le_and]

Depends on / 依赖: Or.inl, Or.inr, le_rfl, le_total
-/
theorem exists_ge_of_linear (a b : α) : exists c, a <= c ∧ b <= c :=
  match le_total a b with
  | Or.inl h => ⟨_, h, le_rfl⟩
  | Or.inr h => ⟨_, le_rfl, h⟩

@[to_dual exists_forall_le_and]
/--
lemma `exists_forall_ge_and` / 引理 `exists_forall_ge_and`

English:
lemma exists_forall_ge_and
  given: {p q : α -> Prop}
  proof: exists_ge_of_linear a b
⟨c, fun _d hcd => ⟨ha _ hac.trans hcd, hb _ hbc.trans hcd⟩⟩

@[to_dual le_of_forall_gt]

中文:
引理 存在_对任意_ge_and
  条件: {p q : α -> 命题}
  证明: exists_ge_of_linear a b
⟨c, fun _d hcd => ⟨ha _ hac.trans hcd, hb _ hbc.trans hcd⟩⟩

@[to_dual le_of_forall_gt]

Depends on / 依赖: exists_ge_of_linear
-/
lemma exists_forall_ge_and {p q : α -> Prop} :
    (exists i, forall j >= i, p j) -> (exists i, forall j >= i, q j) -> exists i, forall j >= i, p j ∧ q j
  | ⟨a, ha⟩, ⟨b, hb⟩ =>
    let ⟨c, hac, hbc⟩ := exists_ge_of_linear a b
⟨c, fun _d hcd => ⟨ha _ hac.trans hcd, hb _ hbc.trans hcd⟩⟩

@[to_dual le_of_forall_gt]
/--
theorem `le_of_forall_lt` / 定理 `le_of_forall_lt`

English:
theorem le_of_forall_lt
  given: (H : forall c, c < a -> c < b)
  statement: a <= b
  proof: le_of_not_gt fun h => lt_irrefl _ (H _ h)

@[to_dual forall_gt_iff_le]

中文:
定理 le_of_对任意_lt
  条件: (H : 对任意 c, c < a -> c < b)
  结论: a <= b
  证明: le_of_not_gt fun h => lt_irrefl _ (H _ h)

@[to_dual forall_gt_iff_le]

Depends on / 依赖: le_of_not_gt, lt_irrefl
-/
theorem le_of_forall_lt (H : forall c, c < a -> c < b) : a <= b :=
  le_of_not_gt fun h => lt_irrefl _ (H _ h)

@[to_dual forall_gt_iff_le]
/--
theorem `forall_lt_iff_le` / 定理 `forall_lt_iff_le`

English:
theorem forall_lt_iff_le
  statement: (forall ⦃c⦄, c < a -> c < b) ↔ a <= b
  proof: ⟨le_of_forall_lt, fun h _ hca => lt_of_lt_of_le hca h⟩

@[to_dual le_of_forall_gt_imp_ne]

中文:
定理 对任意_lt_iff_le
  结论: (对任意 ⦃c⦄, c < a -> c < b) ↔ a <= b
  证明: ⟨le_of_forall_lt, fun h _ hca => lt_of_lt_of_le hca h⟩

@[to_dual le_of_forall_gt_imp_ne]

Depends on / 依赖: le_of_forall_lt, lt_of_lt_of_le
-/
theorem forall_lt_iff_le : (forall ⦃c⦄, c < a -> c < b) ↔ a <= b :=
  ⟨le_of_forall_lt, fun h _ hca => lt_of_lt_of_le hca h⟩

@[to_dual le_of_forall_gt_imp_ne]
/--
theorem `le_of_forall_lt_imp_ne` / 定理 `le_of_forall_lt_imp_ne`

English:
theorem le_of_forall_lt_imp_ne
  given: (H : forall c < a, c != b)
  statement: a <= b
  proof: le_of_not_gt fun hb => H b hb rfl

@[to_dual lt_of_forall_ge_imp_ne]

中文:
定理 le_of_对任意_lt_imp_ne
  条件: (H : 对任意 c < a, c != b)
  结论: a <= b
  证明: le_of_not_gt fun hb => H b hb rfl

@[to_dual lt_of_forall_ge_imp_ne]

Depends on / 依赖: le_of_not_gt
-/
theorem le_of_forall_lt_imp_ne (H : forall c < a, c != b) : a <= b :=
  le_of_not_gt fun hb => H b hb rfl

@[to_dual lt_of_forall_ge_imp_ne]
/--
theorem `lt_of_forall_le_imp_ne` / 定理 `lt_of_forall_le_imp_ne`

English:
theorem lt_of_forall_le_imp_ne
  given: (H : forall c <= a, c != b)
  statement: a < b
  proof: lt_of_not_ge fun hb => H b hb rfl

@[to_dual forall_gt_imp_ne_iff_le]

中文:
定理 lt_of_对任意_le_imp_ne
  条件: (H : 对任意 c <= a, c != b)
  结论: a < b
  证明: lt_of_not_ge fun hb => H b hb rfl

@[to_dual forall_gt_imp_ne_iff_le]

Depends on / 依赖: lt_of_not_ge
-/
theorem lt_of_forall_le_imp_ne (H : forall c <= a, c != b) : a < b :=
  lt_of_not_ge fun hb => H b hb rfl

@[to_dual forall_gt_imp_ne_iff_le]
/--
theorem `forall_lt_imp_ne_iff_le` / 定理 `forall_lt_imp_ne_iff_le`

English:
theorem forall_lt_imp_ne_iff_le
  statement: (forall c < a, c != b) ↔ a <= b
  proof: ⟨le_of_forall_lt_imp_ne, fun ha _ hc => (hc.trans_le ha).ne⟩

@[to_dual forall_ge_imp_ne_iff_lt]

中文:
定理 对任意_lt_imp_ne_iff_le
  结论: (对任意 c < a, c != b) ↔ a <= b
  证明: ⟨le_of_forall_lt_imp_ne, fun ha _ hc => (hc.trans_le ha).ne⟩

@[to_dual forall_ge_imp_ne_iff_lt]

Depends on / 依赖: hc.trans_le, le_of_forall_lt_imp_ne, trans_le
-/
theorem forall_lt_imp_ne_iff_le : (forall c < a, c != b) ↔ a <= b :=
  ⟨le_of_forall_lt_imp_ne, fun ha _ hc => (hc.trans_le ha).ne⟩

@[to_dual forall_ge_imp_ne_iff_lt]
/--
theorem `forall_le_imp_ne_iff_lt` / 定理 `forall_le_imp_ne_iff_lt`

English:
theorem forall_le_imp_ne_iff_lt
  statement: (forall c <= a, c != b) ↔ a < b
  proof: ⟨lt_of_forall_le_imp_ne, fun ha _ hc => (hc.trans_lt ha).ne⟩

@[to_dual eq_of_forall_gt_iff]

中文:
定理 对任意_le_imp_ne_iff_lt
  结论: (对任意 c <= a, c != b) ↔ a < b
  证明: ⟨lt_of_forall_le_imp_ne, fun ha _ hc => (hc.trans_lt ha).ne⟩

@[to_dual eq_of_forall_gt_iff]

Depends on / 依赖: hc.trans_lt, lt_of_forall_le_imp_ne, trans_lt
-/
theorem forall_le_imp_ne_iff_lt : (forall c <= a, c != b) ↔ a < b :=
  ⟨lt_of_forall_le_imp_ne, fun ha _ hc => (hc.trans_lt ha).ne⟩

@[to_dual eq_of_forall_gt_iff]
/--
theorem `eq_of_forall_lt_iff` / 定理 `eq_of_forall_lt_iff`

English:
theorem eq_of_forall_lt_iff
  given: (h : forall c, c < a ↔ c < b)
  statement: a = b
  proof: (le_of_forall_lt fun _ => (h _).1).antisymm le_of_forall_lt fun _ => (h _).2

@[to_dual self (reorder := ltc gtc)]

中文:
定理 eq_of_对任意_lt_iff
  条件: (h : 对任意 c, c < a ↔ c < b)
  结论: a = b
  证明: (le_of_forall_lt fun _ => (h _).1).antisymm le_of_forall_lt fun _ => (h _).2

@[to_dual self (reorder := ltc gtc)]

Depends on / 依赖: antisymm, le_of_forall_lt
-/
theorem eq_of_forall_lt_iff (h : forall c, c < a ↔ c < b) : a = b :=
(le_of_forall_lt fun _ => (h _).1).antisymm le_of_forall_lt fun _ => (h _).2

@[to_dual self (reorder := ltc gtc)]
/--
lemma `eq_iff_eq_of_lt_iff_lt_of_gt_iff_gt` / 引理 `eq_iff_eq_of_lt_iff_lt_of_gt_iff_gt`

English:
lemma eq_iff_eq_of_lt_iff_lt_of_gt_iff_gt
  statement: {x y x' y' : α}
  proof: by grind

中文:
引理 eq_iff_eq_of_lt_iff_lt_of_gt_iff_gt
  结论: {x y x' y' : α}
  证明: by grind
-/
lemma eq_iff_eq_of_lt_iff_lt_of_gt_iff_gt {x y x' y' : α}
    (ltc : x < y ↔ x' < y') (gtc : y < x ↔ y' < x') :
    x = y ↔ x' = y' := by grind

/-! #### `min`/`max` recursors -/

section MinMaxRec
variable {p : α -> Prop}

@[to_dual]
/--
lemma `min_rec` / 引理 `min_rec`

English:
lemma min_rec
  given: (ha : a <= b -> p a) (hb : b <= a -> p b)
  statement: p (min a b)
  proof: by
  obtain hab | hba := le_total a b <;> simp [min_eq_left, min_eq_right, *]

@[to_dual]

中文:
引理 min_rec
  条件: (ha : a <= b -> p a) (hb : b <= a -> p b)
  结论: p (最小值 a b)
  证明: by
  obtain hab | hba := le_total a b <;> simp [min_eq_left, min_eq_right, *]

@[to_dual]

Depends on / 依赖: le_total, min_eq_left, min_eq_right
-/
lemma min_rec (ha : a <= b -> p a) (hb : b <= a -> p b) : p (min a b) := by
  obtain hab | hba := le_total a b <;> simp [min_eq_left, min_eq_right, *]

@[to_dual]
/--
lemma `min_rec'` / 引理 `min_rec'`

English:
lemma min_rec'
  given: (p : α -> Prop) (ha : p a) (hb : p b)
  statement: p (min a b)
  proof: min_rec (fun _ => ha) fun _ => hb

@[to_dual max_def_lt']

中文:
引理 min_rec'
  条件: (p : α -> 命题) (ha : p a) (hb : p b)
  结论: p (最小值 a b)
  证明: min_rec (fun _ => ha) fun _ => hb

@[to_dual max_def_lt']

Depends on / 依赖: min_rec
-/
lemma min_rec' (p : α -> Prop) (ha : p a) (hb : p b) : p (min a b) :=
  min_rec (fun _ => ha) fun _ => hb

@[to_dual max_def_lt']
/--
lemma `min_def_lt` / 引理 `min_def_lt`

English:
lemma min_def_lt
  given: (a b : α)
  statement: min a b = if a < b then a else b
  proof: by
  rw [min_comm]; rw [min_def]; rw [← ite_not]; simp only [not_le]

@[to_dual min_def_lt']

中文:
引理 min_def_lt
  条件: (a b : α)
  结论: 最小值 a b = if a < b then a else b
  证明: by
  rw [min_comm]; rw [min_def]; rw [← ite_not]; simp only [not_le]

@[to_dual min_def_lt']

Depends on / 依赖: ite_not, min_comm, min_def, not_le
-/
lemma min_def_lt (a b : α) : min a b = if a < b then a else b := by
  rw [min_comm]; rw [min_def]; rw [← ite_not]; simp only [not_le]

@[to_dual min_def_lt']
/--
lemma `max_def_lt` / 引理 `max_def_lt`

English:
lemma max_def_lt
  given: (a b : α)
  statement: max a b = if a < b then b else a
  proof: by
  rw [max_comm]; rw [max_def]; rw [← ite_not]; simp only [not_le]

中文:
引理 max_def_lt
  条件: (a b : α)
  结论: 最大值 a b = if a < b then b else a
  证明: by
  rw [max_comm]; rw [max_def]; rw [← ite_not]; simp only [not_le]

Depends on / 依赖: ite_not, max_comm, max_def, not_le
-/
lemma max_def_lt (a b : α) : max a b = if a < b then b else a := by
  rw [max_comm]; rw [max_def]; rw [← ite_not]; simp only [not_le]

end MinMaxRec
end LinearOrder

/-! ### Implications -/

@[to_dual self]
/--
lemma `lt_imp_lt_of_le_imp_le` / 引理 `lt_imp_lt_of_le_imp_le`

English:
lemma lt_imp_lt_of_le_imp_le
  statement: {β} [LinearOrder α] [Preorder β] {a b : α} {c d : β}
  proof: lt_of_not_ge fun h' => (H h').not_gt h

@[to_dual self]

中文:
引理 lt_imp_lt_of_le_imp_le
  结论: {β} [线性序 α] [预序 β] {a b : α} {c d : β}
  证明: lt_of_not_ge fun h' => (H h').not_gt h

@[to_dual self]

Depends on / 依赖: Nat.le_induction, infer_instance, le_induction, le_total, lt_of_not_ge, not_gt, partialTraj_le, partialTraj_self, partialTraj_succ_of_le
-/
lemma lt_imp_lt_of_le_imp_le {β} [LinearOrder α] [Preorder β] {a b : α} {c d : β}
    (H : a <= b -> c <= d) (h : d < c) : b < a :=
  lt_of_not_ge fun h' => (H h').not_gt h

@[to_dual self]
/--
lemma `le_imp_le_iff_lt_imp_lt` / 引理 `le_imp_le_iff_lt_imp_lt`

English:
lemma le_imp_le_iff_lt_imp_lt
  given: {β} [LinearOrder α] [LinearOrder β] {a b : α} {c d : β}
  proof: ⟨lt_imp_lt_of_le_imp_le, le_imp_le_of_lt_imp_lt⟩

@[to_dual self]

中文:
引理 le_imp_le_iff_lt_imp_lt
  条件: {β} [线性序 α] [线性序 β] {a b : α} {c d : β}
  证明: ⟨lt_imp_lt_of_le_imp_le, le_imp_le_of_lt_imp_lt⟩

@[to_dual self]

Depends on / 依赖: le_imp_le_of_lt_imp_lt, lt_imp_lt_of_le_imp_le
-/
lemma le_imp_le_iff_lt_imp_lt {β} [LinearOrder α] [LinearOrder β] {a b : α} {c d : β} :
    a <= b -> c <= d ↔ d < c -> b < a :=
  ⟨lt_imp_lt_of_le_imp_le, le_imp_le_of_lt_imp_lt⟩

@[to_dual self]
/--
lemma `lt_iff_lt_of_le_iff_le'` / 引理 `lt_iff_lt_of_le_iff_le'`

English:
lemma lt_iff_lt_of_le_iff_le'
  statement: {β} [Preorder α] [Preorder β] {a b : α} {c d : β}
  proof: lt_iff_le_not_ge.trans (and_congr H' (not_congr H)).trans lt_iff_le_not_ge.symm

@[to_dual self]

中文:
引理 lt_iff_lt_of_le_iff_le'
  结论: {β} [预序 α] [预序 β] {a b : α} {c d : β}
  证明: lt_iff_le_not_ge.trans (and_congr H' (not_congr H)).trans lt_iff_le_not_ge.symm

@[to_dual self]

Depends on / 依赖: and_congr, lt_iff_le_not_ge, lt_iff_le_not_ge.symm, lt_iff_le_not_ge.trans, not_congr
-/
lemma lt_iff_lt_of_le_iff_le' {β} [Preorder α] [Preorder β] {a b : α} {c d : β}
    (H : a <= b ↔ c <= d) (H' : b <= a ↔ d <= c) : b < a ↔ d < c :=
lt_iff_le_not_ge.trans (and_congr H' (not_congr H)).trans lt_iff_le_not_ge.symm

@[to_dual self]
/--
lemma `lt_iff_lt_of_le_iff_le` / 引理 `lt_iff_lt_of_le_iff_le`

English:
lemma lt_iff_lt_of_le_iff_le
  statement: {β} [LinearOrder α] [LinearOrder β] {a b : α} {c d : β}
  proof: not_le.symm.trans (not_congr H).trans not_le

@[to_dual self]

中文:
引理 lt_iff_lt_of_le_iff_le
  结论: {β} [线性序 α] [线性序 β] {a b : α} {c d : β}
  证明: not_le.symm.trans (not_congr H).trans not_le

@[to_dual self]

Depends on / 依赖: not_congr, not_le, not_le.symm.trans
-/
lemma lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [LinearOrder β] {a b : α} {c d : β}
(H : a <= b ↔ c <= d) : b < a ↔ d < c := not_le.symm.trans (not_congr H).trans not_le

@[to_dual self]
/--
lemma `le_iff_le_iff_lt_iff_lt` / 引理 `le_iff_le_iff_lt_iff_lt`

English:
lemma le_iff_le_iff_lt_iff_lt
  given: {β} [LinearOrder α] [LinearOrder β] {a b : α} {c d : β}
  proof: ⟨lt_iff_lt_of_le_iff_le, fun H => not_lt.symm.trans (not_congr H).trans not_lt⟩

中文:
引理 le_iff_le_iff_lt_iff_lt
  条件: {β} [线性序 α] [线性序 β] {a b : α} {c d : β}
  证明: ⟨lt_iff_lt_of_le_iff_le, fun H => not_lt.symm.trans (not_congr H).trans not_lt⟩

Depends on / 依赖: lt_iff_lt_of_le_iff_le, not_congr, not_lt, not_lt.symm.trans
-/
lemma le_iff_le_iff_lt_iff_lt {β} [LinearOrder α] [LinearOrder β] {a b : α} {c d : β} :
    (a <= b ↔ c <= d) ↔ (b < a ↔ d < c) :=
⟨lt_iff_lt_of_le_iff_le, fun H => not_lt.symm.trans (not_congr H).trans not_lt⟩

/--
lemma `rel_imp_eq_of_rel_imp_le` / 引理 `rel_imp_eq_of_rel_imp_le`

English:
lemma rel_imp_eq_of_rel_imp_le
  statement: [PartialOrder β] (r : α -> α -> Prop) [Std.Symm r] {f : α -> β}
  proof: fun hab =>
  le_antisymm (h a b hab) (h b a <| symm hab)

中文:
引理 rel_imp_eq_of_rel_imp_le
  结论: [偏序 β] (r : α -> α -> 命题) [Std.Symm r] {f : α -> β}
  证明: fun hab =>
  le_antisymm (h a b hab) (h b a <| symm hab)
-/
lemma rel_imp_eq_of_rel_imp_le [PartialOrder β] (r : α -> α -> Prop) [Std.Symm r] {f : α -> β}
    (h : forall a b, r a b -> f a <= f b) {a b : α} : r a b -> f a = f b := fun hab =>
  le_antisymm (h a b hab) (h b a <| symm hab)

/-! ### Extensionality lemmas -/

@[ext]
/--
lemma `Preorder.toLE_injective` / 引理 `Preorder.toLE_injective`

English:
lemma Preorder.toLE_injective
  statement: Function.Injective (@Preorder.toLE α)
  proof: fun
  | { lt := A_lt, lt_iff_le_not_ge := A_iff, .. },
    { lt := B_lt, lt_iff_le_not_ge := B_iff, .. } => by
    rintro ⟨⟩
    have : A_lt = B_lt := by
      funext a b
      rw [A_iff]; rw [B_iff]
    cases this
    congr

@[ext]

中文:
引理 预序.toLE_injective
  结论: 函数.单射 (@预序.toLE α)
  证明: fun
  | { lt := A_lt, lt_iff_le_not_ge := A_iff, .. },
    { lt := B_lt, lt_iff_le_not_ge := B_iff, .. } => by
    rintro ⟨⟩
    have : A_lt = B_lt := by
      funext a b
      rw [A_iff]; rw [B_iff]
    cases this
    congr

@[ext]

Depends on / 依赖: A_iff, A_lt, B_iff, B_lt, lt_iff_le_not_ge
-/
lemma Preorder.toLE_injective : Function.Injective (@Preorder.toLE α) :=
  fun
  | { lt := A_lt, lt_iff_le_not_ge := A_iff, .. },
    { lt := B_lt, lt_iff_le_not_ge := B_iff, .. } => by
    rintro ⟨⟩
    have : A_lt = B_lt := by
      funext a b
      rw [A_iff]; rw [B_iff]
    cases this
    congr

@[ext]
/--
lemma `PartialOrder.toPreorder_injective` / 引理 `PartialOrder.toPreorder_injective`

English:
lemma PartialOrder.toPreorder_injective
  statement: Function.Injective (@PartialOrder.toPreorder α)
  proof: by
  rintro ⟨⟩ ⟨⟩ ⟨⟩; congr

@[ext]

中文:
引理 偏序.toPreorder_injective
  结论: 函数.单射 (@偏序.toPreorder α)
  证明: by
  rintro ⟨⟩ ⟨⟩ ⟨⟩; congr

@[ext]
-/
lemma PartialOrder.toPreorder_injective : Function.Injective (@PartialOrder.toPreorder α) := by
  rintro ⟨⟩ ⟨⟩ ⟨⟩; congr

@[ext]
/--
lemma `LinearOrder.toPartialOrder_injective` / 引理 `LinearOrder.toPartialOrder_injective`

English:
lemma LinearOrder.toPartialOrder_injective
  statement: Function.Injective (@LinearOrder.toPartialOrder α)
  proof: fun
  | { le := A_le, lt := A_lt,
      toDecidableLE := A_decidableLE, toDecidableEq := A_decidableEq, toDecidableLT := A_decidableLT
      min := A_min, max := A_max, min_def := A_min_def, max_def := A_max_def,
      compare := A_compare, compare_eq_compareOfLessAndEq := A_compare_canonical, .. },

中文:
引理 线性序.toPartialOrder_injective
  结论: 函数.单射 (@线性序.toPartialOrder α)
  证明: fun
  | { le := A_le, lt := A_lt,
      toDecidableLE := A_decidableLE, toDecidableEq := A_decidableEq, toDecidableLT := A_decidableLT
      min := A_min, max := A_max, min_def := A_min_def, max_def := A_max_def,
      compare := A_compare, compare_eq_compareOfLessAndEq := A_compare_canonical, .. },

Depends on / 依赖: A_compare, A_compare_canonical, A_decidableEq, A_decidableLE, A_decidableLT, A_le, A_lt, A_max, A_max_def, A_min, A_min_def, B_compare, B_decidableEq, B_decidableLE, B_decidableLT, B_le, B_lt, B_max, B_max_def, B_min
-/
lemma LinearOrder.toPartialOrder_injective : Function.Injective (@LinearOrder.toPartialOrder α) :=
  fun
  | { le := A_le, lt := A_lt,
      toDecidableLE := A_decidableLE, toDecidableEq := A_decidableEq, toDecidableLT := A_decidableLT
      min := A_min, max := A_max, min_def := A_min_def, max_def := A_max_def,
      compare := A_compare, compare_eq_compareOfLessAndEq := A_compare_canonical, .. },
    { le := B_le, lt := B_lt,
      toDecidableLE := B_decidableLE, toDecidableEq := B_decidableEq, toDecidableLT := B_decidableLT
      min := B_min, max := B_max, min_def := B_min_def, max_def := B_max_def,
      compare := B_compare, compare_eq_compareOfLessAndEq := B_compare_canonical, .. } => by
    rintro ⟨⟩
    obtain rfl : A_decidableLE = B_decidableLE := Subsingleton.elim _ _
    obtain rfl : A_decidableEq = B_decidableEq := Subsingleton.elim _ _
    obtain rfl : A_decidableLT = B_decidableLT := Subsingleton.elim _ _
    have : A_min = B_min := by
      funext a b
      exact (A_min_def _ _).trans (B_min_def _ _).symm
    cases this
    have : A_max = B_max := by
      funext a b
      exact (A_max_def _ _).trans (B_max_def _ _).symm
    cases this
    have : A_compare = B_compare := by
      funext a b
      exact (A_compare_canonical _ _).trans (B_compare_canonical _ _).symm
    congr

@[to_dual self]
/--
lemma `Preorder.ext` / 引理 `Preorder.ext`

English:
lemma Preorder.ext
  given: {A B : Preorder α} (H : forall x y : α, (haveI := A; x <= y) ↔ x <= y)
  statement: A = B
  proof: by
  ext x y; exact H x y

@[to_dual self]

中文:
引理 预序.ext
  条件: {A B : 预序 α} (H : 对任意 x y : α, (haveI := A; x <= y) ↔ x <= y)
  结论: A = B
  证明: by
  ext x y; exact H x y

@[to_dual self]
-/
lemma Preorder.ext {A B : Preorder α} (H : forall x y : α, (haveI := A; x <= y) ↔ x <= y) : A = B := by
  ext x y; exact H x y

@[to_dual self]
/--
lemma `PartialOrder.ext` / 引理 `PartialOrder.ext`

English:
lemma PartialOrder.ext
  given: {A B : PartialOrder α} (H : forall x y : α, (haveI := A; x <= y) ↔ x <= y)
  proof: by ext x y; exact H x y

@[to_dual self]

中文:
引理 偏序.ext
  条件: {A B : 偏序 α} (H : 对任意 x y : α, (haveI := A; x <= y) ↔ x <= y)
  证明: by ext x y; exact H x y

@[to_dual self]
-/
lemma PartialOrder.ext {A B : PartialOrder α} (H : forall x y : α, (haveI := A; x <= y) ↔ x <= y) :
    A = B := by ext x y; exact H x y

@[to_dual self]
/--
lemma `PartialOrder.ext_lt` / 引理 `PartialOrder.ext_lt`

English:
lemma PartialOrder.ext_lt
  given: {A B : PartialOrder α} (H : forall x y : α, (haveI := A; x < y) ↔ x < y)
  proof: by ext x y; rw [le_iff_lt_or_eq, @le_iff_lt_or_eq _ A, H]

@[to_dual self]

中文:
引理 偏序.ext_lt
  条件: {A B : 偏序 α} (H : 对任意 x y : α, (haveI := A; x < y) ↔ x < y)
  证明: by ext x y; rw [le_iff_lt_or_eq, @le_iff_lt_or_eq _ A, H]

@[to_dual self]
-/
lemma PartialOrder.ext_lt {A B : PartialOrder α} (H : forall x y : α, (haveI := A; x < y) ↔ x < y) :
    A = B := by ext x y; rw [le_iff_lt_or_eq, @le_iff_lt_or_eq _ A, H]

@[to_dual self]
/--
lemma `LinearOrder.ext` / 引理 `LinearOrder.ext`

English:
lemma LinearOrder.ext
  given: {A B : LinearOrder α} (H : forall x y : α, (haveI := A; x <= y) ↔ x <= y)
  proof: by ext x y; exact H x y

@[to_dual self]

中文:
引理 线性序.ext
  条件: {A B : 线性序 α} (H : 对任意 x y : α, (haveI := A; x <= y) ↔ x <= y)
  证明: by ext x y; exact H x y

@[to_dual self]
-/
lemma LinearOrder.ext {A B : LinearOrder α} (H : forall x y : α, (haveI := A; x <= y) ↔ x <= y) :
    A = B := by ext x y; exact H x y

@[to_dual self]
/--
lemma `LinearOrder.ext_lt` / 引理 `LinearOrder.ext_lt`

English:
lemma LinearOrder.ext_lt
  given: {A B : LinearOrder α} (H : forall x y : α, (haveI := A; x < y) ↔ x < y)
  proof: LinearOrder.toPartialOrder_injective (PartialOrder.ext_lt H)

中文:
引理 线性序.ext_lt
  条件: {A B : 线性序 α} (H : 对任意 x y : α, (haveI := A; x < y) ↔ x < y)
  证明: LinearOrder.toPartialOrder_injective (PartialOrder.ext_lt H)
-/
lemma LinearOrder.ext_lt {A B : LinearOrder α} (H : forall x y : α, (haveI := A; x < y) ↔ x < y) :
    A = B := LinearOrder.toPartialOrder_injective (PartialOrder.ext_lt H)



/--
Instance `Prop.instCompl` / 实例 `Prop.instCompl`

English:
instance Prop.instCompl
  signature: : Compl Prop
  body: ⟨Not⟩

@[to_dual instHNot]

中文:
实例 命题.instCompl
  签名: : 补集 命题
  定义体: ⟨Not⟩

@[to_dual instHNot]
-/
instance Prop.instCompl : Compl Prop :=
  ⟨Not⟩

@[to_dual instHNot]
/--
Instance `Pi.instCompl` / 实例 `Pi.instCompl`

English:
instance Pi.instCompl
  signature: [forall i, Compl (π i)]
  body: ⟨fun x i => (x i)ᶜ⟩

@[to_dual (attr := push ←) hnot_def]

中文:
实例 依赖函数类型.instCompl
  签名: [对任意 i, 补集 (π i)]
  定义体: ⟨fun x i => (x i)ᶜ⟩

@[to_dual (attr := push ←) hnot_def]
-/
instance Pi.instCompl [forall i, Compl (π i)] : Compl (forall i, π i) :=
  ⟨fun x i => (x i)ᶜ⟩

@[to_dual (attr := push ←) hnot_def]
/--
theorem `Pi.compl_def` / 定理 `Pi.compl_def`

English:
theorem Pi.compl_def
  given: [forall i, Compl (π i)] (x : forall i, π i)
  proof: rfl

@[to_dual (attr := simp) hnot_apply]

中文:
定理 依赖函数类型.compl_def
  条件: [对任意 i, 补集 (π i)] (x : 对任意 i, π i)
  证明: rfl

@[to_dual (attr := simp) hnot_apply]
-/
theorem Pi.compl_def [forall i, Compl (π i)] (x : forall i, π i) :
    xᶜ = fun i => (x i)ᶜ :=
  rfl

@[to_dual (attr := simp) hnot_apply]
/--
theorem `Pi.compl_apply` / 定理 `Pi.compl_apply`

English:
theorem Pi.compl_apply
  given: [forall i, Compl (π i)] (x : forall i, π i) (i : ι)
  proof: rfl

中文:
定理 依赖函数类型.compl_apply
  条件: [对任意 i, 补集 (π i)] (x : 对任意 i, π i) (i : ι)
  证明: rfl
-/
theorem Pi.compl_apply [forall i, Compl (π i)] (x : forall i, π i) (i : ι) :
    xᶜ i = (x i)ᶜ :=
  rfl

/--
Instance `Std.Irrefl.compl` / 实例 `Std.Irrefl.compl`

English:
instance Std.Irrefl.compl
  signature: (r : α -> α -> Prop) [Std.Irrefl r]
  body: ⟨@irrefl α r _⟩

中文:
实例 Std.Irrefl.compl
  签名: (r : α -> α -> 命题) [Std.Irrefl r]
  定义体: ⟨@irrefl α r _⟩

Depends on / 依赖: irrefl
-/
instance Std.Irrefl.compl (r : α -> α -> Prop) [Std.Irrefl r] : Std.Refl rᶜ :=
  ⟨@irrefl α r _⟩

/--
Instance `Std.Refl.compl` / 实例 `Std.Refl.compl`

English:
instance Std.Refl.compl
  signature: (r : α -> α -> Prop) [Std.Refl r]
  body: ⟨fun a => not_not_intro (refl a)⟩

中文:
实例 Std.Refl.compl
  签名: (r : α -> α -> 命题) [Std.Refl r]
  定义体: ⟨fun a => not_not_intro (refl a)⟩

Depends on / 依赖: not_not_intro
-/
instance Std.Refl.compl (r : α -> α -> Prop) [Std.Refl r] : Std.Irrefl rᶜ :=
  ⟨fun a => not_not_intro (refl a)⟩

/--
theorem `compl_lt` / 定理 `compl_lt`

English:
theorem compl_lt
  given: [LinearOrder α]
  statement: (· < · : α -> α -> _)ᶜ = (· >= ·)
  proof: by simp [compl]

中文:
定理 compl_lt
  条件: [线性序 α]
  结论: (· < · : α -> α -> _)ᶜ = (· >= ·)
  证明: by simp [compl]
-/
theorem compl_lt [LinearOrder α] : (· < · : α -> α -> _)ᶜ = (· >= ·) := by simp [compl]
/--
theorem `compl_le` / 定理 `compl_le`

English:
theorem compl_le
  given: [LinearOrder α]
  statement: (· <= · : α -> α -> _)ᶜ = (· > ·)
  proof: by simp [compl]

中文:
定理 compl_le
  条件: [线性序 α]
  结论: (· <= · : α -> α -> _)ᶜ = (· > ·)
  证明: by simp [compl]
-/
theorem compl_le [LinearOrder α] : (· <= · : α -> α -> _)ᶜ = (· > ·) := by simp [compl]
/--
theorem `compl_gt` / 定理 `compl_gt`

English:
theorem compl_gt
  given: [LinearOrder α]
  statement: (· > · : α -> α -> _)ᶜ = (· <= ·)
  proof: by simp [compl]

中文:
定理 compl_gt
  条件: [线性序 α]
  结论: (· > · : α -> α -> _)ᶜ = (· <= ·)
  证明: by simp [compl]
-/
theorem compl_gt [LinearOrder α] : (· > · : α -> α -> _)ᶜ = (· <= ·) := by simp [compl]
/--
theorem `compl_ge` / 定理 `compl_ge`

English:
theorem compl_ge
  given: [LinearOrder α]
  statement: (· >= · : α -> α -> _)ᶜ = (· < ·)
  proof: by simp [compl]

中文:
定理 compl_ge
  条件: [线性序 α]
  结论: (· >= · : α -> α -> _)ᶜ = (· < ·)
  证明: by simp [compl]
-/
theorem compl_ge [LinearOrder α] : (· >= · : α -> α -> _)ᶜ = (· < ·) := by simp [compl]

/--
Instance `Ne.instIsEquiv_compl` / 实例 `Ne.instIsEquiv_compl`

English:
instance Ne.instIsEquiv_compl
  signature: : IsEquiv α (· != ·)ᶜ
  body: by
  convert! eq_isEquiv α
  simp [compl]

中文:
实例 不等.instIsEquiv_compl
  签名: : Is等价 α (· != ·)ᶜ
  定义体: by
  convert! eq_isEquiv α
  simp [compl]

Depends on / 依赖: convert, eq_isEquiv
-/
instance Ne.instIsEquiv_compl : IsEquiv α (· != ·)ᶜ := by
  convert! eq_isEquiv α
  simp [compl]


/--
Instance `Pi.preorder` / 实例 `Pi.preorder`

English:
instance Pi.preorder
  signature: [forall i, Preorder (π i)]
  body: (inferInstance : LE (forall i, π i))
  le_refl := fun a i => le_refl (a i)
  le_trans := fun _ _ _ h₁ h₂ i => le_trans (h₁ i) (h₂ i)

@[to_dual self]

中文:
实例 依赖函数类型.preorder
  签名: [对任意 i, 预序 (π i)]
  定义体: (inferInstance : LE (forall i, π i))
  le_refl := fun a i => le_refl (a i)
  le_trans := fun _ _ _ h₁ h₂ i => le_trans (h₁ i) (h₂ i)

@[to_dual self]
-/
instance Pi.preorder [forall i, Preorder (π i)] : Preorder (forall i, π i) where
  __ := (inferInstance : LE (forall i, π i))
  le_refl := fun a i => le_refl (a i)
  le_trans := fun _ _ _ h₁ h₂ i => le_trans (h₁ i) (h₂ i)

@[to_dual self]
/--
theorem `Pi.lt_def` / 定理 `Pi.lt_def`

English:
theorem Pi.lt_def
  given: [forall i, Preorder (π i)] {x y : forall i, π i}
  proof: by
  simp +contextual [lt_iff_le_not_ge, Pi.le_def]

中文:
定理 依赖函数类型.lt_def
  条件: [对任意 i, 预序 (π i)] {x y : 对任意 i, π i}
  证明: by
  simp +contextual [lt_iff_le_not_ge, Pi.le_def]

Depends on / 依赖: Pi.le_def, contextual, le_def, lt_iff_le_not_ge
-/
theorem Pi.lt_def [forall i, Preorder (π i)] {x y : forall i, π i} :
    x < y ↔ x <= y ∧ exists i, x i < y i := by
  simp +contextual [lt_iff_le_not_ge, Pi.le_def]

/--
Instance `Pi.partialOrder` / 实例 `Pi.partialOrder`

English:
instance Pi.partialOrder
  signature: [forall i, PartialOrder (π i)]
  body: Pi.preorder
  le_antisymm := fun _ _ h1 h2 => funext fun b => (h1 b).antisymm (h2 b)

中文:
实例 依赖函数类型.partialOrder
  签名: [对任意 i, 偏序 (π i)]
  定义体: Pi.preorder
  le_antisymm := fun _ _ h1 h2 => funext fun b => (h1 b).antisymm (h2 b)

Depends on / 依赖: Pi.preorder, preorder
-/
instance Pi.partialOrder [forall i, PartialOrder (π i)] : PartialOrder (forall i, π i) where
  __ := Pi.preorder
  le_antisymm := fun _ _ h1 h2 => funext fun b => (h1 b).antisymm (h2 b)

namespace Sum

variable {α₁ α₂ : Type*} [LE β]

@[simp]
/--
lemma `elim_le_elim_iff` / 引理 `elim_le_elim_iff`

English:
lemma elim_le_elim_iff
  given: {u₁ v₁ : α₁ -> β} {u₂ v₂ : α₂ -> β}
  proof: Sum.forall

中文:
引理 elim_le_elim_iff
  条件: {u₁ v₁ : α₁ -> β} {u₂ v₂ : α₂ -> β}
  证明: Sum.forall

Depends on / 依赖: Sum.forall
-/
lemma elim_le_elim_iff {u₁ v₁ : α₁ -> β} {u₂ v₂ : α₂ -> β} :
    Sum.elim u₁ u₂ <= Sum.elim v₁ v₂ ↔ u₁ <= v₁ ∧ u₂ <= v₂ :=
  Sum.forall

/--
lemma `const_le_elim_iff` / 引理 `const_le_elim_iff`

English:
lemma const_le_elim_iff
  given: {b : β} {v₁ : α₁ -> β} {v₂ : α₂ -> β}
  proof: elim_const_const b ▸ elim_le_elim_iff ..

中文:
引理 const_le_elim_iff
  条件: {b : β} {v₁ : α₁ -> β} {v₂ : α₂ -> β}
  证明: elim_const_const b ▸ elim_le_elim_iff ..

Depends on / 依赖: elim_const_const, elim_le_elim_iff
-/
lemma const_le_elim_iff {b : β} {v₁ : α₁ -> β} {v₂ : α₂ -> β} :
    Function.const _ b <= Sum.elim v₁ v₂ ↔ Function.const _ b <= v₁ ∧ Function.const _ b <= v₂ :=
  elim_const_const b ▸ elim_le_elim_iff ..

/--
lemma `elim_le_const_iff` / 引理 `elim_le_const_iff`

English:
lemma elim_le_const_iff
  given: {b : β} {u₁ : α₁ -> β} {u₂ : α₂ -> β}
  proof: elim_const_const b ▸ elim_le_elim_iff ..

中文:
引理 elim_le_const_iff
  条件: {b : β} {u₁ : α₁ -> β} {u₂ : α₂ -> β}
  证明: elim_const_const b ▸ elim_le_elim_iff ..

Depends on / 依赖: elim_const_const, elim_le_elim_iff
-/
lemma elim_le_const_iff {b : β} {u₁ : α₁ -> β} {u₂ : α₂ -> β} :
    Sum.elim u₁ u₂ <= Function.const _ b ↔ u₁ <= Function.const _ b ∧ u₂ <= Function.const _ b :=
  elim_const_const b ▸ elim_le_elim_iff ..

end Sum

section Pi

/-- A function `a` is strongly less than a function `b` if `a i < b i` for all `i`. -/
@[to_dual self (reorder := a b)]
/--
Definition of `StrongLT` / `StrongLT` 的定义

English:
definition StrongLT
  signature: [forall i, LT (π i)] (a b : forall i, π i)
  body: forall i, a i < b i

@[inherit_doc]
local infixl:50 " ≺ " => StrongLT

中文:
定义 StrongLT
  签名: [对任意 i, LT (π i)] (a b : 对任意 i, π i)
  定义体: forall i, a i < b i

@[inherit_doc]
local infixl:50 " ≺ " => StrongLT
-/
def StrongLT [forall i, LT (π i)] (a b : forall i, π i) : Prop :=
  forall i, a i < b i

@[inherit_doc]
local infixl:50 " ≺ " => StrongLT

variable [forall i, Preorder (π i)] {a b c : forall i, π i}

@[to_dual self]
/--
theorem `le_of_strongLT` / 定理 `le_of_strongLT`

English:
theorem le_of_strongLT
  given: (h : a ≺ b)
  statement: a <= b
  proof: fun _ => (h _).le

@[to_dual self]

中文:
定理 le_of_strongLT
  条件: (h : a ≺ b)
  结论: a <= b
  证明: fun _ => (h _).le

@[to_dual self]
-/
theorem le_of_strongLT (h : a ≺ b) : a <= b := fun _ => (h _).le

@[to_dual self]
/--
theorem `lt_of_strongLT` / 定理 `lt_of_strongLT`

English:
theorem lt_of_strongLT
  given: [Nonempty ι] (h : a ≺ b)
  statement: a < b
  proof: by
  inhabit ι
  exact Pi.lt_def.2 ⟨le_of_strongLT h, default, h _⟩

@[to_dual (reorder := hab hbc) strongLT_of_le_of_strongLT]

中文:
定理 lt_of_strongLT
  条件: [非空 ι] (h : a ≺ b)
  结论: a < b
  证明: by
  inhabit ι
  exact Pi.lt_def.2 ⟨le_of_strongLT h, default, h _⟩

@[to_dual (reorder := hab hbc) strongLT_of_le_of_strongLT]

Depends on / 依赖: Pi.lt_def, inhabit, le_of_strongLT, lt_def
-/
theorem lt_of_strongLT [Nonempty ι] (h : a ≺ b) : a < b := by
  inhabit ι
  exact Pi.lt_def.2 ⟨le_of_strongLT h, default, h _⟩

@[to_dual (reorder := hab hbc) strongLT_of_le_of_strongLT]
/--
theorem `strongLT_of_strongLT_of_le` / 定理 `strongLT_of_strongLT_of_le`

English:
theorem strongLT_of_strongLT_of_le
  given: (hab : a ≺ b) (hbc : b <= c)
  statement: a ≺ c
  proof: fun _ =>
(hab _).trans_le hbc _

@[to_dual self] alias StrongLT.le := le_of_strongLT

@[to_dual self] alias StrongLT.lt := lt_of_strongLT

@[to_dual (reorder := hab hbc) LE.le.trans_strongLT]
alias StrongLT.trans_le := strongLT_of_strongLT_of_le

中文:
定理 strongLT_of_strongLT_of_le
  条件: (hab : a ≺ b) (hbc : b <= c)
  结论: a ≺ c
  证明: fun _ =>
(hab _).trans_le hbc _

@[to_dual self] alias StrongLT.le := le_of_strongLT

@[to_dual self] alias StrongLT.lt := lt_of_strongLT

@[to_dual (reorder := hab hbc) LE.le.trans_strongLT]
alias StrongLT.trans_le := strongLT_of_strongLT_of_le
-/
theorem strongLT_of_strongLT_of_le (hab : a ≺ b) (hbc : b <= c) : a ≺ c := fun _ =>
(hab _).trans_le hbc _

@[to_dual self] alias StrongLT.le := le_of_strongLT

@[to_dual self] alias StrongLT.lt := lt_of_strongLT

@[to_dual (reorder := hab hbc) LE.le.trans_strongLT]
alias StrongLT.trans_le := strongLT_of_strongLT_of_le

end Pi

section Function

variable [DecidableEq ι] [forall i, Preorder (π i)] {x y : forall i, π i} {i : ι} {a b : π i}

@[to_dual update_le_iff]
/--
theorem `le_update_iff` / 定理 `le_update_iff`

English:
theorem le_update_iff
  statement: x <= Function.update y i a ↔ x i <= a ∧ forall (j) (_ : j != i), x j <= y j
  proof: Function.forall_update_iff _ fun j z => x j <= z

@[to_dual self]

中文:
定理 le_update_iff
  结论: x <= 函数.update y i a ↔ x i <= a ∧ 对任意 (j) (_ : j != i), x j <= y j
  证明: Function.forall_update_iff _ fun j z => x j <= z

@[to_dual self]

Depends on / 依赖: Function, Function.forall_update_iff, forall_update_iff
-/
theorem le_update_iff : x <= Function.update y i a ↔ x i <= a ∧ forall (j) (_ : j != i), x j <= y j :=
  Function.forall_update_iff _ fun j z => x j <= z

@[to_dual self]
/--
theorem `update_le_update_iff` / 定理 `update_le_update_iff`

English:
theorem update_le_update_iff
  proof: by
  simp +contextual [update_le_iff]

@[simp, to_dual self]

中文:
定理 update_le_update_iff
  证明: by
  simp +contextual [update_le_iff]

@[simp, to_dual self]

Depends on / 依赖: contextual, update_le_iff
-/
theorem update_le_update_iff :
    Function.update x i a <= Function.update y i b ↔ a <= b ∧ forall (j) (_ : j != i), x j <= y j := by
  simp +contextual [update_le_iff]

@[simp, to_dual self]
/--
theorem `update_le_update_iff'` / 定理 `update_le_update_iff'`

English:
theorem update_le_update_iff'
  statement: update x i a <= update x i b ↔ a <= b
  proof: by
  simp [update_le_update_iff]

@[simp, to_dual self]

中文:
定理 update_le_update_iff'
  结论: update x i a <= update x i b ↔ a <= b
  证明: by
  simp [update_le_update_iff]

@[simp, to_dual self]

Depends on / 依赖: update_le_update_iff
-/
theorem update_le_update_iff' : update x i a <= update x i b ↔ a <= b := by
  simp [update_le_update_iff]

@[simp, to_dual self]
/--
theorem `update_lt_update_iff` / 定理 `update_lt_update_iff`

English:
theorem update_lt_update_iff
  statement: update x i a < update x i b ↔ a < b
  proof: lt_iff_lt_of_le_iff_le' update_le_update_iff' update_le_update_iff'

@[to_dual (attr := simp) update_le_self_iff]

中文:
定理 update_lt_update_iff
  结论: update x i a < update x i b ↔ a < b
  证明: lt_iff_lt_of_le_iff_le' update_le_update_iff' update_le_update_iff'

@[to_dual (attr := simp) update_le_self_iff]

Depends on / 依赖: lt_iff_lt_of_le_iff_le, update_le_update_iff
-/
theorem update_lt_update_iff : update x i a < update x i b ↔ a < b :=
  lt_iff_lt_of_le_iff_le' update_le_update_iff' update_le_update_iff'

@[to_dual (attr := simp) update_le_self_iff]
/--
theorem `le_update_self_iff` / 定理 `le_update_self_iff`

English:
theorem le_update_self_iff
  statement: x <= update x i a ↔ x i <= a
  proof: by simp [le_update_iff]

@[to_dual (attr := simp) update_lt_self_iff]

中文:
定理 le_update_self_iff
  结论: x <= update x i a ↔ x i <= a
  证明: by simp [le_update_iff]

@[to_dual (attr := simp) update_lt_self_iff]

Depends on / 依赖: le_update_iff
-/
theorem le_update_self_iff : x <= update x i a ↔ x i <= a := by simp [le_update_iff]

@[to_dual (attr := simp) update_lt_self_iff]
/--
theorem `lt_update_self_iff` / 定理 `lt_update_self_iff`

English:
theorem lt_update_self_iff
  statement: x < update x i a ↔ x i < a
  proof: by simp [lt_iff_le_not_ge]

中文:
定理 lt_update_self_iff
  结论: x < update x i a ↔ x i < a
  证明: by simp [lt_iff_le_not_ge]

Depends on / 依赖: lt_iff_le_not_ge
-/
theorem lt_update_self_iff : x < update x i a ↔ x i < a := by simp [lt_iff_le_not_ge]

end Function

@[to_dual instHImp]
/--
Instance `Pi.instSDiff` / 实例 `Pi.instSDiff`

English:
instance Pi.instSDiff
  signature: [forall i, SDiff (π i)]
  body: ⟨fun x y i => x i \ y i⟩

@[to_dual (attr := push ←) himp_def]

中文:
实例 依赖函数类型.instSDiff
  签名: [对任意 i, 对称差 (π i)]
  定义体: ⟨fun x y i => x i \ y i⟩

@[to_dual (attr := push ←) himp_def]
-/
instance Pi.instSDiff [forall i, SDiff (π i)] : SDiff (forall i, π i) :=
  ⟨fun x y i => x i \ y i⟩

@[to_dual (attr := push ←) himp_def]
/--
theorem `Pi.sdiff_def` / 定理 `Pi.sdiff_def`

English:
theorem Pi.sdiff_def
  given: [forall i, SDiff (π i)] (x y : forall i, π i)
  proof: rfl

@[to_dual (attr := simp) himp_apply]

中文:
定理 依赖函数类型.sdiff_def
  条件: [对任意 i, 对称差 (π i)] (x y : 对任意 i, π i)
  证明: rfl

@[to_dual (attr := simp) himp_apply]
-/
theorem Pi.sdiff_def [forall i, SDiff (π i)] (x y : forall i, π i) :
    x \ y = fun i => x i \ y i :=
  rfl

@[to_dual (attr := simp) himp_apply]
/--
theorem `Pi.sdiff_apply` / 定理 `Pi.sdiff_apply`

English:
theorem Pi.sdiff_apply
  given: [forall i, SDiff (π i)] (x y : forall i, π i) (i : ι)
  proof: rfl

中文:
定理 依赖函数类型.sdiff_apply
  条件: [对任意 i, 对称差 (π i)] (x y : 对任意 i, π i) (i : ι)
  证明: rfl
-/
theorem Pi.sdiff_apply [forall i, SDiff (π i)] (x y : forall i, π i) (i : ι) :
    (x \ y) i = x i \ y i :=
  rfl

namespace Function

variable [Preorder α] [Nonempty β] {a b : α}

@[simp, to_dual self]
/--
theorem `const_le_const` / 定理 `const_le_const`

English:
theorem const_le_const
  statement: const β a <= const β b ↔ a <= b
  proof: by simp [Pi.le_def]

@[simp, to_dual self]

中文:
定理 const_le_const
  结论: const β a <= const β b ↔ a <= b
  证明: by simp [Pi.le_def]

@[simp, to_dual self]

Depends on / 依赖: Pi.le_def, le_def
-/
theorem const_le_const : const β a <= const β b ↔ a <= b := by simp [Pi.le_def]

@[simp, to_dual self]
/--
theorem `const_lt_const` / 定理 `const_lt_const`

English:
theorem const_lt_const
  statement: const β a < const β b ↔ a < b
  proof: by simpa [Pi.lt_def] using le_of_lt

中文:
定理 const_lt_const
  结论: const β a < const β b ↔ a < b
  证明: by simpa [Pi.lt_def] using le_of_lt

Depends on / 依赖: Pi.lt_def, le_of_lt, lt_def
-/
theorem const_lt_const : const β a < const β b ↔ a < b := by simpa [Pi.lt_def] using le_of_lt

end Function

/-! ### Pullbacks of order instances -/

/-- Pull back a `Preorder` instance along an injective function.

See note [reducible non-instances]. -/
@[to_dual self]
/--
Definition of `Function.Injective.preorder` / `Function.Injective.preorder` 的定义

English:
abbreviation Function.Injective.preorder
  signature: [Preorder β] [LE α] [LT α] (f : α -> β)
  body: le.1 le_refl _
le_trans _ _ _ h₁ h₂ := le.1 le_trans (le.2 h₁) (le.2 h₂)
  lt_iff_le_not_ge _ _ := by
    rw [← le]; rw [← le]; rw [← lt]; rw [lt_iff_le_not_ge]

中文:
缩写 函数.单射.preorder
  签名: [预序 β] [LE α] [LT α] (f : α -> β)
  定义体: le.1 le_refl _
le_trans _ _ _ h₁ h₂ := le.1 le_trans (le.2 h₁) (le.2 h₂)
  lt_iff_le_not_ge _ _ := by
    rw [← le]; rw [← le]; rw [← lt]; rw [lt_iff_le_not_ge]

Depends on / 依赖: le_refl
-/
abbrev Function.Injective.preorder [Preorder β] [LE α] [LT α] (f : α -> β)
    (le : forall {x y}, f x <= f y ↔ x <= y) (lt : forall {x y}, f x < f y ↔ x < y) :
    Preorder α where
le_refl _ := le.1 le_refl _
le_trans _ _ _ h₁ h₂ := le.1 le_trans (le.2 h₁) (le.2 h₂)
  lt_iff_le_not_ge _ _ := by
    rw [← le]; rw [← le]; rw [← lt]; rw [lt_iff_le_not_ge]

/-- Pull back a `PartialOrder` instance along an injective function.

See note [reducible non-instances]. -/
@[to_dual self]
/--
Definition of `Function.Injective.partialOrder` / `Function.Injective.partialOrder` 的定义

English:
abbreviation Function.Injective.partialOrder
  signature: [PartialOrder β] [LE α] [LT α] (f : α -> β)
  body: Function.Injective.preorder f le lt
le_antisymm _ _ h₁ h₂ := hf le_antisymm (le.2 h₁) (le.2 h₂)

中文:
缩写 函数.单射.partialOrder
  签名: [偏序 β] [LE α] [LT α] (f : α -> β)
  定义体: Function.Injective.preorder f le lt
le_antisymm _ _ h₁ h₂ := hf le_antisymm (le.2 h₁) (le.2 h₂)

Depends on / 依赖: Function, Function.Injective.preorder, Injective, preorder
-/
abbrev Function.Injective.partialOrder [PartialOrder β] [LE α] [LT α] (f : α -> β)
    (hf : Function.Injective f)
    (le : forall {x y}, f x <= f y ↔ x <= y) (lt : forall {x y}, f x < f y ↔ x < y) :
    PartialOrder α where
  __ := Function.Injective.preorder f le lt
le_antisymm _ _ h₁ h₂ := hf le_antisymm (le.2 h₁) (le.2 h₂)

/--
Definition of `Function.Injective.linearOrder` / `Function.Injective.linearOrder` 的定义

English:
abbreviation Function.Injective.linearOrder
  signature: [LinearOrder β] [LE α] [LT α] [Max α] [Min α] [Ord α]
  body: hf.partialOrder _ le lt
  toDecidableLE := ‹_›
  toDecidableEq := ‹_›
  toDecidableLT := ‹_›
  le_total _ _ := by simp only [← le, le_total]
  min_def _ _ := by simp_rw [← hf.eq_iff, ← le, apply_ite f, ← min_def, min]
  max_def _ _ := by simp_rw [← hf.eq_iff, ← le, apply_ite f, ← max_def, max]
  com

中文:
缩写 函数.单射.linearOrder
  签名: [线性序 β] [LE α] [LT α] [最大值 α] [最小值 α] [序 α]
  定义体: hf.partialOrder _ le lt
  toDecidableLE := ‹_›
  toDecidableEq := ‹_›
  toDecidableLT := ‹_›
  le_total _ _ := by simp only [← le, le_total]
  min_def _ _ := by simp_rw [← hf.eq_iff, ← le, apply_ite f, ← min_def, min]
  max_def _ _ := by simp_rw [← hf.eq_iff, ← le, apply_ite f, ← max_def, max]
  com

Depends on / 依赖: hf.partialOrder, isProbabilityMeasure_trajFun, partialOrder
-/
abbrev Function.Injective.linearOrder [LinearOrder β] [LE α] [LT α] [Max α] [Min α] [Ord α]
    [DecidableEq α] [DecidableLE α] [DecidableLT α] (f : α -> β)
    (hf : Function.Injective f) (le : forall {x y}, f x <= f y ↔ x <= y) (lt : forall {x y}, f x < f y ↔ x < y)
    (min : forall x y, f (x ⊓ y) = f x ⊓ f y) (max : forall x y, f (x ⊔ y) = f x ⊔ f y)
    (compare : forall x y, compare (f x) (f y) = compare x y) :
    LinearOrder α where
  toPartialOrder := hf.partialOrder _ le lt
  toDecidableLE := ‹_›
  toDecidableEq := ‹_›
  toDecidableLT := ‹_›
  le_total _ _ := by simp only [← le, le_total]
  min_def _ _ := by simp_rw [← hf.eq_iff, ← le, apply_ite f, ← min_def, min]
  max_def _ _ := by simp_rw [← hf.eq_iff, ← le, apply_ite f, ← max_def, max]
  compare_eq_compareOfLessAndEq _ _ := by
    simp_rw [← compare, LinearOrder.compare_eq_compareOfLessAndEq, compareOfLessAndEq, ← lt,
      hf.eq_iff]

/-!
### Lifts of order instances

Unlike the constructions above, these construct new data fields.
They should be avoided if the types already define any order or decidability instances.
-/

/--
Definition of `Preorder.lift` / `Preorder.lift` 的定义

English:
abbreviation Preorder.lift
  signature: [Preorder β] (f : α -> β)
  body: letI _instLE : LE α := ⟨fun a b => f a <= f b⟩
  letI _instLT : LT α := ⟨fun a b => f a < f b⟩
  Function.Injective.preorder f .rfl .rfl

中文:
缩写 预序.lift
  签名: [预序 β] (f : α -> β)
  定义体: letI _instLE : LE α := ⟨fun a b => f a <= f b⟩
  letI _instLT : LT α := ⟨fun a b => f a < f b⟩
  Function.Injective.preorder f .rfl .rfl

Depends on / 依赖: Function, Function.Injective.preorder, Injective, _instLE, _instLT, preorder
-/
abbrev Preorder.lift [Preorder β] (f : α -> β) : Preorder α :=
  letI _instLE : LE α := ⟨fun a b => f a <= f b⟩
  letI _instLT : LT α := ⟨fun a b => f a < f b⟩
  Function.Injective.preorder f .rfl .rfl

/--
Definition of `PartialOrder.lift` / `PartialOrder.lift` 的定义

English:
abbreviation PartialOrder.lift
  signature: [PartialOrder β] (f : α -> β) (inj : Injective f)
  body: letI _instLE : LE α := ⟨fun a b => f a <= f b⟩
  letI _instLT : LT α := ⟨fun a b => f a < f b⟩
  Function.Injective.partialOrder f inj .rfl .rfl

中文:
缩写 偏序.lift
  签名: [偏序 β] (f : α -> β) (inj : 单射 f)
  定义体: letI _instLE : LE α := ⟨fun a b => f a <= f b⟩
  letI _instLT : LT α := ⟨fun a b => f a < f b⟩
  Function.Injective.partialOrder f inj .rfl .rfl

Depends on / 依赖: Function, Function.Injective.partialOrder, Injective, _instLE, _instLT, partialOrder
-/
abbrev PartialOrder.lift [PartialOrder β] (f : α -> β) (inj : Injective f) : PartialOrder α :=
  letI _instLE : LE α := ⟨fun a b => f a <= f b⟩
  letI _instLT : LT α := ⟨fun a b => f a < f b⟩
  Function.Injective.partialOrder f inj .rfl .rfl

/--
theorem `compare_of_injective_eq_compareOfLessAndEq` / 定理 `compare_of_injective_eq_compareOfLessAndEq`

English:
theorem compare_of_injective_eq_compareOfLessAndEq
  statement: (a b : α) [LinearOrder β]
  proof: by
  have h := LinearOrder.compare_eq_compareOfLessAndEq (f a) (f b)
  simp only [h, compareOfLessAndEq]
  split_ifs <;> try (first | rfl | contradiction)
  · have : ¬ f a = f b := by rename_i h; exact inj.ne h
    contradiction
  · grind

中文:
定理 compare_of_injective_eq_compareOfLessAndEq
  结论: (a b : α) [线性序 β]
  证明: by
  have h := LinearOrder.compare_eq_compareOfLessAndEq (f a) (f b)
  simp only [h, compareOfLessAndEq]
  split_ifs <;> try (first | rfl | contradiction)
  · have : ¬ f a = f b := by rename_i h; exact inj.ne h
    contradiction
  · grind

Depends on / 依赖: PartialOrder, PartialOrder.lift
-/
theorem compare_of_injective_eq_compareOfLessAndEq (a b : α) [LinearOrder β]
    [DecidableEq α] (f : α -> β) (inj : Injective f)
    [Decidable (LT.lt (self := PartialOrder.lift f inj |>.toLT) a b)] :
    compare (f a) (f b) =
      @compareOfLessAndEq _ a b (PartialOrder.lift f inj |>.toLT) _ _ := by
  have h := LinearOrder.compare_eq_compareOfLessAndEq (f a) (f b)
  simp only [h, compareOfLessAndEq]
  split_ifs <;> try (first | rfl | contradiction)
  · have : ¬ f a = f b := by rename_i h; exact inj.ne h
    contradiction
  · grind

/-- Transfer a `LinearOrder` on `β` to a `LinearOrder` on `α` using an injective
function `f : α → β`. This version takes `[Max α]` and `[Min α]` as arguments, then uses
them for `max` and `min` fields. See `LinearOrder.lift'` for a version that autogenerates `min` and
`max` fields, and `LinearOrder.liftWithOrd` for one that does not auto-generate `compare`
fields.

See also `Function.Injective.linearOrder` when only the proof fields need to be transferred.

See note [reducible non-instances]. -/
@[to_dual self (reorder := 4 5, hsup hinf)]
/--
Definition of `LinearOrder.lift` / `LinearOrder.lift` 的定义

English:
abbreviation LinearOrder.lift
  signature: [LinearOrder β] [Max α] [Min α] (f : α -> β) (inj : Injective f)
  body: letI _instLE : LE α := ⟨fun a b => f a <= f b⟩
  letI _instLT : LT α := ⟨fun a b => f a < f b⟩
  letI _instOrdα : Ord α := ⟨fun a b => compare (f a) (f b)⟩
  letI _decidableLE := fun x y => (inferInstance : Decidable (f x <= f y))
  letI _decidableLT := fun x y => (inferInstance : Decidable (f x < f

中文:
缩写 线性序.lift
  签名: [线性序 β] [最大值 α] [最小值 α] (f : α -> β) (inj : 单射 f)
  定义体: letI _instLE : LE α := ⟨fun a b => f a <= f b⟩
  letI _instLT : LT α := ⟨fun a b => f a < f b⟩
  letI _instOrdα : Ord α := ⟨fun a b => compare (f a) (f b)⟩
  letI _decidableLE := fun x y => (inferInstance : Decidable (f x <= f y))
  letI _decidableLT := fun x y => (inferInstance : Decidable (f x < f

Depends on / 依赖: Decidable, _decidableEq, _decidableLE, _decidableLT, _instLE, _instLT, compare, decidable_of_iff, eq_iff, inj.eq_iff, inj.linearOrder, linearOrder
-/
abbrev LinearOrder.lift [LinearOrder β] [Max α] [Min α] (f : α -> β) (inj : Injective f)
    (hsup : forall x y, f (x ⊔ y) = max (f x) (f y)) (hinf : forall x y, f (x ⊓ y) = min (f x) (f y)) :
    LinearOrder α :=
  letI _instLE : LE α := ⟨fun a b => f a <= f b⟩
  letI _instLT : LT α := ⟨fun a b => f a < f b⟩
  letI _instOrdα : Ord α := ⟨fun a b => compare (f a) (f b)⟩
  letI _decidableLE := fun x y => (inferInstance : Decidable (f x <= f y))
  letI _decidableLT := fun x y => (inferInstance : Decidable (f x < f y))
  letI _decidableEq := fun x y => decidable_of_iff (f x = f y) inj.eq_iff
  inj.linearOrder _ .rfl .rfl hinf hsup (fun _ _ => rfl)

/--
Definition of `LinearOrder.lift'` / `LinearOrder.lift'` 的定义

English:
abbreviation LinearOrder.lift'
  signature: [LinearOrder β] (f : α -> β) (inj : Injective f)
  body: @LinearOrder.lift α β _ ⟨fun x y => if f x <= f y then y else x⟩
    ⟨fun x y => if f x <= f y then x else y⟩ f inj
    (fun _ _ => (apply_ite f _ _ _).trans (max_def _ _).symm) fun _ _ =>
    (apply_ite f _ _ _).trans (min_def _ _).symm

中文:
缩写 线性序.lift'
  签名: [线性序 β] (f : α -> β) (inj : 单射 f)
  定义体: @LinearOrder.lift α β _ ⟨fun x y => if f x <= f y then y else x⟩
    ⟨fun x y => if f x <= f y then x else y⟩ f inj
    (fun _ _ => (apply_ite f _ _ _).trans (max_def _ _).symm) fun _ _ =>
    (apply_ite f _ _ _).trans (min_def _ _).symm

Depends on / 依赖: LinearOrder, LinearOrder.lift, apply_ite, max_def, min_def
-/
abbrev LinearOrder.lift' [LinearOrder β] (f : α -> β) (inj : Injective f) : LinearOrder α :=
  @LinearOrder.lift α β _ ⟨fun x y => if f x <= f y then y else x⟩
    ⟨fun x y => if f x <= f y then x else y⟩ f inj
    (fun _ _ => (apply_ite f _ _ _).trans (max_def _ _).symm) fun _ _ =>
    (apply_ite f _ _ _).trans (min_def _ _).symm

/-- Transfer a `LinearOrder` on `β` to a `LinearOrder` on `α` using an injective
function `f : α → β`. This version takes `[Max α]` and `[Min α]` as arguments, then uses
them for `max` and `min` fields. It also takes `[Ord α]` as an argument and uses them for `compare`
fields. See `LinearOrder.lift` for a version that autogenerates `compare` fields, and
`LinearOrder.liftWithOrd'` for one that auto-generates `min` and `max` fields.
fields. See note [reducible non-instances]. -/
@[to_dual self (reorder := 4 5, hsup hinf)]
/--
Definition of `LinearOrder.liftWithOrd` / `LinearOrder.liftWithOrd` 的定义

English:
abbreviation LinearOrder.liftWithOrd
  signature: [LinearOrder β] [Max α] [Min α] [Ord α] (f : α -> β)
  body: letI _instLE : LE α := ⟨fun a b => f a <= f b⟩
  letI _instLE : LT α := ⟨fun a b => f a < f b⟩
  letI _decidableLE := fun x y => (inferInstance : Decidable (f x <= f y))
  letI _decidableLT := fun x y => (inferInstance : Decidable (f x < f y))
  letI _decidableEq := fun x y => decidable_of_iff (f x 

中文:
缩写 线性序.liftWithOrd
  签名: [线性序 β] [最大值 α] [最小值 α] [序 α] (f : α -> β)
  定义体: letI _instLE : LE α := ⟨fun a b => f a <= f b⟩
  letI _instLE : LT α := ⟨fun a b => f a < f b⟩
  letI _decidableLE := fun x y => (inferInstance : Decidable (f x <= f y))
  letI _decidableLT := fun x y => (inferInstance : Decidable (f x < f y))
  letI _decidableEq := fun x y => decidable_of_iff (f x 

Depends on / 依赖: Decidable, _decidableEq, _decidableLE, _decidableLT, _instLE, compare_f, decidable_of_iff, eq_iff, inj.eq_iff, inj.linearOrder, linearOrder
-/
abbrev LinearOrder.liftWithOrd [LinearOrder β] [Max α] [Min α] [Ord α] (f : α -> β)
    (inj : Injective f) (hsup : forall x y, f (x ⊔ y) = max (f x) (f y))
    (hinf : forall x y, f (x ⊓ y) = min (f x) (f y))
    (compare_f : forall a b : α, compare a b = compare (f a) (f b)) : LinearOrder α :=
  letI _instLE : LE α := ⟨fun a b => f a <= f b⟩
  letI _instLE : LT α := ⟨fun a b => f a < f b⟩
  letI _decidableLE := fun x y => (inferInstance : Decidable (f x <= f y))
  letI _decidableLT := fun x y => (inferInstance : Decidable (f x < f y))
  letI _decidableEq := fun x y => decidable_of_iff (f x = f y) inj.eq_iff
  inj.linearOrder _ .rfl .rfl hinf hsup (fun _ _ => (compare_f _ _).symm)

/--
Definition of `LinearOrder.liftWithOrd'` / `LinearOrder.liftWithOrd'` 的定义

English:
abbreviation LinearOrder.liftWithOrd'
  signature: [LinearOrder β] [Ord α] (f : α -> β)
  body: @LinearOrder.liftWithOrd α β _ ⟨fun x y => if f x <= f y then y else x⟩
    ⟨fun x y => if f x <= f y then x else y⟩ _ f inj
    (fun _ _ => (apply_ite f _ _ _).trans (max_def _ _).symm)
    (fun _ _ => (apply_ite f _ _ _).trans (min_def _ _).symm)
    compare_f

中文:
缩写 线性序.liftWithOrd'
  签名: [线性序 β] [序 α] (f : α -> β)
  定义体: @LinearOrder.liftWithOrd α β _ ⟨fun x y => if f x <= f y then y else x⟩
    ⟨fun x y => if f x <= f y then x else y⟩ _ f inj
    (fun _ _ => (apply_ite f _ _ _).trans (max_def _ _).symm)
    (fun _ _ => (apply_ite f _ _ _).trans (min_def _ _).symm)
    compare_f

Depends on / 依赖: LinearOrder, LinearOrder.liftWithOrd, apply_ite, compare_f, liftWithOrd, max_def, min_def
-/
abbrev LinearOrder.liftWithOrd' [LinearOrder β] [Ord α] (f : α -> β)
    (inj : Injective f)
    (compare_f : forall a b : α, compare a b = compare (f a) (f b)) : LinearOrder α :=
  @LinearOrder.liftWithOrd α β _ ⟨fun x y => if f x <= f y then y else x⟩
    ⟨fun x y => if f x <= f y then x else y⟩ _ f inj
    (fun _ _ => (apply_ite f _ _ _).trans (max_def _ _).symm)
    (fun _ _ => (apply_ite f _ _ _).trans (min_def _ _).symm)
    compare_f

/-! ### Subtype of an order -/


namespace Subtype

@[simp, gcongr, to_dual self]
/--
theorem `mk_le_mk` / 定理 `mk_le_mk`

English:
theorem mk_le_mk
  given: [LE α] {p : α -> Prop} {x y : α} {hx : p x} {hy : p y}
  proof: Iff.rfl

@[simp, gcongr, to_dual self]

中文:
定理 mk_le_mk
  条件: [LE α] {p : α -> 命题} {x y : α} {hx : p x} {hy : p y}
  证明: Iff.rfl

@[simp, gcongr, to_dual self]

Depends on / 依赖: Iff.rfl
-/
theorem mk_le_mk [LE α] {p : α -> Prop} {x y : α} {hx : p x} {hy : p y} :
    (⟨x, hx⟩ : Subtype p) <= ⟨y, hy⟩ ↔ x <= y :=
  Iff.rfl

@[simp, gcongr, to_dual self]
/--
theorem `mk_lt_mk` / 定理 `mk_lt_mk`

English:
theorem mk_lt_mk
  given: [LT α] {p : α -> Prop} {x y : α} {hx : p x} {hy : p y}
  proof: Iff.rfl

@[simp, norm_cast, gcongr, to_dual self]

中文:
定理 mk_lt_mk
  条件: [LT α] {p : α -> 命题} {x y : α} {hx : p x} {hy : p y}
  证明: Iff.rfl

@[simp, norm_cast, gcongr, to_dual self]

Depends on / 依赖: Iff.rfl
-/
theorem mk_lt_mk [LT α] {p : α -> Prop} {x y : α} {hx : p x} {hy : p y} :
    (⟨x, hx⟩ : Subtype p) < ⟨y, hy⟩ ↔ x < y :=
  Iff.rfl

@[simp, norm_cast, gcongr, to_dual self]
/--
theorem `coe_le_coe` / 定理 `coe_le_coe`

English:
theorem coe_le_coe
  given: [LE α] {p : α -> Prop} {x y : Subtype p}
  statement: (x : α) <= y ↔ x <= y
  proof: Iff.rfl

@[simp, norm_cast, gcongr, to_dual self]

中文:
定理 coe_le_coe
  条件: [LE α] {p : α -> 命题} {x y : 子类型 p}
  结论: (x : α) <= y ↔ x <= y
  证明: Iff.rfl

@[simp, norm_cast, gcongr, to_dual self]

Depends on / 依赖: Iff.rfl
-/
theorem coe_le_coe [LE α] {p : α -> Prop} {x y : Subtype p} : (x : α) <= y ↔ x <= y :=
  Iff.rfl

@[simp, norm_cast, gcongr, to_dual self]
/--
theorem `coe_lt_coe` / 定理 `coe_lt_coe`

English:
theorem coe_lt_coe
  given: [LT α] {p : α -> Prop} {x y : Subtype p}
  statement: (x : α) < y ↔ x < y
  proof: Iff.rfl

中文:
定理 coe_lt_coe
  条件: [LT α] {p : α -> 命题} {x y : 子类型 p}
  结论: (x : α) < y ↔ x < y
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem coe_lt_coe [LT α] {p : α -> Prop} {x y : Subtype p} : (x : α) < y ↔ x < y :=
  Iff.rfl

/--
Instance `preorder` / 实例 `preorder`

English:
instance preorder
  signature: [Preorder α] (p : α -> Prop)
  body: fast_instance% Preorder.lift (fun (a : Subtype p) => (a : α))

中文:
实例 preorder
  签名: [预序 α] (p : α -> 命题)
  定义体: fast_instance% Preorder.lift (fun (a : Subtype p) => (a : α))

Depends on / 依赖: Preorder, Preorder.lift, Subtype, fast_instance
-/
instance preorder [Preorder α] (p : α -> Prop) : Preorder (Subtype p) :=
  fast_instance% Preorder.lift (fun (a : Subtype p) => (a : α))

/--
Instance `partialOrder` / 实例 `partialOrder`

English:
instance partialOrder
  signature: [PartialOrder α] (p : α -> Prop)
  body: fast_instance% PartialOrder.lift (fun (a : Subtype p) => (a : α)) Subtype.coe_injective

中文:
实例 partialOrder
  签名: [偏序 α] (p : α -> 命题)
  定义体: fast_instance% PartialOrder.lift (fun (a : Subtype p) => (a : α)) Subtype.coe_injective
-/
instance partialOrder [PartialOrder α] (p : α -> Prop) : PartialOrder (Subtype p) :=
  fast_instance% PartialOrder.lift (fun (a : Subtype p) => (a : α)) Subtype.coe_injective

/--
Instance `decidableLE` / 实例 `decidableLE`

English:
instance decidableLE
  signature: [Preorder α] [h : DecidableLE α] {p : α -> Prop}
  body: fun a b => h a b

中文:
实例 decidableLE
  签名: [预序 α] [h : DecidableLE α] {p : α -> 命题}
  定义体: fun a b => h a b
-/
instance decidableLE [Preorder α] [h : DecidableLE α] {p : α -> Prop} :
    DecidableLE (Subtype p) := fun a b => h a b

/--
Instance `decidableLT` / 实例 `decidableLT`

English:
instance decidableLT
  signature: [Preorder α] [h : DecidableLT α] {p : α -> Prop}
  body: fun a b => h a b

中文:
实例 decidableLT
  签名: [预序 α] [h : DecidableLT α] {p : α -> 命题}
  定义体: fun a b => h a b
-/
instance decidableLT [Preorder α] [h : DecidableLT α] {p : α -> Prop} :
    DecidableLT (Subtype p) := fun a b => h a b

/--
Instance `instLinearOrder` / 实例 `instLinearOrder`

English:
instance instLinearOrder
  signature: [LinearOrder α] (p : α -> Prop)
  body: fast_instance% @LinearOrder.lift (Subtype p) _ _ ⟨fun x y => ⟨max x y, max_rec' _ x.2 y.2⟩⟩
    ⟨fun x y => ⟨min x y, min_rec' _ x.2 y.2⟩⟩ (fun (a : Subtype p) => (a : α))
    Subtype.coe_injective (fun _ _ => rfl) fun _ _ =>
    rfl

中文:
实例 instLinearOrder
  签名: [线性序 α] (p : α -> 命题)
  定义体: fast_instance% @LinearOrder.lift (Subtype p) _ _ ⟨fun x y => ⟨max x y, max_rec' _ x.2 y.2⟩⟩
    ⟨fun x y => ⟨min x y, min_rec' _ x.2 y.2⟩⟩ (fun (a : Subtype p) => (a : α))
    Subtype.coe_injective (fun _ _ => rfl) fun _ _ =>
    rfl

Depends on / 依赖: LinearOrder, LinearOrder.lift, Subtype, Subtype.coe_injective, coe_injective, fast_instance, max_rec, min_rec
-/
instance instLinearOrder [LinearOrder α] (p : α -> Prop) : LinearOrder (Subtype p) :=
  fast_instance% @LinearOrder.lift (Subtype p) _ _ ⟨fun x y => ⟨max x y, max_rec' _ x.2 y.2⟩⟩
    ⟨fun x y => ⟨min x y, min_rec' _ x.2 y.2⟩⟩ (fun (a : Subtype p) => (a : α))
    Subtype.coe_injective (fun _ _ => rfl) fun _ _ =>
    rfl

end Subtype

/-!
### Pointwise order on `α × β`

The lexicographic order is defined in `Data.Prod.Lex`, and the instances are available via the
type synonym `α ×ₗ β = α × β`.
-/


namespace Prod
section LE
variable [LE α] [LE β] {x y : α × β} {a a₁ a₂ : α} {b b₁ b₂ : β}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LE (α × β)
  body: p.1 <= q.1 ∧ p.2 <= q.2

@[to_dual self]

中文:
实例 :
  签名: LE (α × β)
  定义体: p.1 <= q.1 ∧ p.2 <= q.2

@[to_dual self]
-/
instance : LE (α × β) where le p q := p.1 <= q.1 ∧ p.2 <= q.2

@[to_dual self]
/--
Instance `instDecidableLE` / 实例 `instDecidableLE`

English:
instance instDecidableLE
  signature: [Decidable (x.1 <= y.1)] [Decidable (x.2 <= y.2)]
  body: inferInstanceAs Decidable (x.1 <= y.1 ∧ x.2 <= y.2)

中文:
实例 instDecidableLE
  签名: [可判定 (x.1 <= y.1)] [可判定 (x.2 <= y.2)]
  定义体: inferInstanceAs Decidable (x.1 <= y.1 ∧ x.2 <= y.2)

Depends on / 依赖: Decidable
-/
instance instDecidableLE [Decidable (x.1 <= y.1)] [Decidable (x.2 <= y.2)] : Decidable (x <= y) :=
inferInstanceAs Decidable (x.1 <= y.1 ∧ x.2 <= y.2)

/--
lemma `le_def` / 引理 `le_def`

English:
lemma le_def
  statement: x <= y ↔ x.1 <= y.1 ∧ x.2 <= y.2
  proof: .rfl

中文:
引理 le_def
  结论: x <= y ↔ x.1 <= y.1 ∧ x.2 <= y.2
  证明: .rfl
-/
@[to_dual self] lemma le_def : x <= y ↔ x.1 <= y.1 ∧ x.2 <= y.2 := .rfl

/--
lemma `mk_le_mk` / 引理 `mk_le_mk`

English:
lemma mk_le_mk
  statement: (a₁, b₁) <= (a₂, b₂) ↔ a₁ <= a₂ ∧ b₁ <= b₂
  proof: .rfl

@[gcongr, to_dual self]

中文:
引理 mk_le_mk
  结论: (a₁, b₁) <= (a₂, b₂) ↔ a₁ <= a₂ ∧ b₁ <= b₂
  证明: .rfl

@[gcongr, to_dual self]
-/
@[simp, to_dual self] lemma mk_le_mk : (a₁, b₁) <= (a₂, b₂) ↔ a₁ <= a₂ ∧ b₁ <= b₂ := .rfl

@[gcongr, to_dual self]
/--
lemma `GCongr.mk_le_mk` / 引理 `GCongr.mk_le_mk`

English:
lemma GCongr.mk_le_mk
  given: (ha : a₁ <= a₂) (hb : b₁ <= b₂)
  statement: (a₁, b₁) <= (a₂, b₂)
  proof: ⟨ha, hb⟩

中文:
引理 GCongr.mk_le_mk
  条件: (ha : a₁ <= a₂) (hb : b₁ <= b₂)
  结论: (a₁, b₁) <= (a₂, b₂)
  证明: ⟨ha, hb⟩
-/
lemma GCongr.mk_le_mk (ha : a₁ <= a₂) (hb : b₁ <= b₂) : (a₁, b₁) <= (a₂, b₂) := ⟨ha, hb⟩

/--
lemma `swap_le_swap` / 引理 `swap_le_swap`

English:
lemma swap_le_swap
  statement: x.swap <= y.swap ↔ x <= y
  proof: and_comm

@[to_dual (attr := simp) mk_le_swap]

中文:
引理 swap_le_swap
  结论: x.swap <= y.swap ↔ x <= y
  证明: and_comm

@[to_dual (attr := simp) mk_le_swap]
-/
@[simp, to_dual self] lemma swap_le_swap : x.swap <= y.swap ↔ x <= y := and_comm

@[to_dual (attr := simp) mk_le_swap]
/--
lemma `swap_le_mk` / 引理 `swap_le_mk`

English:
lemma swap_le_mk
  statement: x.swap <= (b, a) ↔ x <= (a, b)
  proof: and_comm

中文:
引理 swap_le_mk
  结论: x.swap <= (b, a) ↔ x <= (a, b)
  证明: and_comm

Depends on / 依赖: and_comm
-/
lemma swap_le_mk : x.swap <= (b, a) ↔ x <= (a, b) := and_comm

end LE

section Preorder

variable [Preorder α] [Preorder β] {a a₁ a₂ : α} {b b₁ b₂ : β} {x y : α × β}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preorder (α × β)
  body: (inferInstance : LE (α × β))
  le_refl := fun ⟨a, b⟩ => ⟨le_refl a, le_refl b⟩
  le_trans := fun ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ ⟨hac, hbd⟩ ⟨hce, hdf⟩ => ⟨le_trans hac hce, le_trans hbd hdf⟩

@[simp, to_dual self]

中文:
实例 :
  签名: 预序 (α × β)
  定义体: (inferInstance : LE (α × β))
  le_refl := fun ⟨a, b⟩ => ⟨le_refl a, le_refl b⟩
  le_trans := fun ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ ⟨hac, hbd⟩ ⟨hce, hdf⟩ => ⟨le_trans hac hce, le_trans hbd hdf⟩

@[simp, to_dual self]
-/
instance : Preorder (α × β) where
  __ := (inferInstance : LE (α × β))
  le_refl := fun ⟨a, b⟩ => ⟨le_refl a, le_refl b⟩
  le_trans := fun ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ ⟨hac, hbd⟩ ⟨hce, hdf⟩ => ⟨le_trans hac hce, le_trans hbd hdf⟩

@[simp, to_dual self]
/--
theorem `swap_lt_swap` / 定理 `swap_lt_swap`

English:
theorem swap_lt_swap
  statement: x.swap < y.swap ↔ x < y
  proof: and_congr swap_le_swap (not_congr swap_le_swap)

@[to_dual (attr := simp) mk_lt_swap]

中文:
定理 swap_lt_swap
  结论: x.swap < y.swap ↔ x < y
  证明: and_congr swap_le_swap (not_congr swap_le_swap)

@[to_dual (attr := simp) mk_lt_swap]

Depends on / 依赖: and_congr, not_congr, swap_le_swap
-/
theorem swap_lt_swap : x.swap < y.swap ↔ x < y :=
  and_congr swap_le_swap (not_congr swap_le_swap)

@[to_dual (attr := simp) mk_lt_swap]
/--
lemma `swap_lt_mk` / 引理 `swap_lt_mk`

English:
lemma swap_lt_mk
  statement: x.swap < (b, a) ↔ x < (a, b)
  proof: by rw [← swap_lt_swap]; simp

@[gcongr, to_dual self]

中文:
引理 swap_lt_mk
  结论: x.swap < (b, a) ↔ x < (a, b)
  证明: by rw [← swap_lt_swap]; simp

@[gcongr, to_dual self]

Depends on / 依赖: swap_lt_swap
-/
lemma swap_lt_mk : x.swap < (b, a) ↔ x < (a, b) := by rw [← swap_lt_swap]; simp

@[gcongr, to_dual self]
/--
theorem `mk_le_mk_iff_left` / 定理 `mk_le_mk_iff_left`

English:
theorem mk_le_mk_iff_left
  statement: (a₁, b) <= (a₂, b) ↔ a₁ <= a₂
  proof: and_iff_left le_rfl

@[gcongr, to_dual self]

中文:
定理 mk_le_mk_iff_left
  结论: (a₁, b) <= (a₂, b) ↔ a₁ <= a₂
  证明: and_iff_left le_rfl

@[gcongr, to_dual self]

Depends on / 依赖: and_iff_left, le_rfl
-/
theorem mk_le_mk_iff_left : (a₁, b) <= (a₂, b) ↔ a₁ <= a₂ :=
  and_iff_left le_rfl

@[gcongr, to_dual self]
/--
theorem `mk_le_mk_iff_right` / 定理 `mk_le_mk_iff_right`

English:
theorem mk_le_mk_iff_right
  statement: (a, b₁) <= (a, b₂) ↔ b₁ <= b₂
  proof: and_iff_right le_rfl

@[gcongr, to_dual self]

中文:
定理 mk_le_mk_iff_right
  结论: (a, b₁) <= (a, b₂) ↔ b₁ <= b₂
  证明: and_iff_right le_rfl

@[gcongr, to_dual self]

Depends on / 依赖: and_iff_right, le_rfl
-/
theorem mk_le_mk_iff_right : (a, b₁) <= (a, b₂) ↔ b₁ <= b₂ :=
  and_iff_right le_rfl

@[gcongr, to_dual self]
/--
theorem `mk_lt_mk_iff_left` / 定理 `mk_lt_mk_iff_left`

English:
theorem mk_lt_mk_iff_left
  statement: (a₁, b) < (a₂, b) ↔ a₁ < a₂
  proof: lt_iff_lt_of_le_iff_le' mk_le_mk_iff_left mk_le_mk_iff_left

@[gcongr, to_dual self]

中文:
定理 mk_lt_mk_iff_left
  结论: (a₁, b) < (a₂, b) ↔ a₁ < a₂
  证明: lt_iff_lt_of_le_iff_le' mk_le_mk_iff_left mk_le_mk_iff_left

@[gcongr, to_dual self]

Depends on / 依赖: lt_iff_lt_of_le_iff_le, mk_le_mk_iff_left
-/
theorem mk_lt_mk_iff_left : (a₁, b) < (a₂, b) ↔ a₁ < a₂ :=
  lt_iff_lt_of_le_iff_le' mk_le_mk_iff_left mk_le_mk_iff_left

@[gcongr, to_dual self]
/--
theorem `mk_lt_mk_iff_right` / 定理 `mk_lt_mk_iff_right`

English:
theorem mk_lt_mk_iff_right
  statement: (a, b₁) < (a, b₂) ↔ b₁ < b₂
  proof: lt_iff_lt_of_le_iff_le' mk_le_mk_iff_right mk_le_mk_iff_right

@[to_dual self]

中文:
定理 mk_lt_mk_iff_right
  结论: (a, b₁) < (a, b₂) ↔ b₁ < b₂
  证明: lt_iff_lt_of_le_iff_le' mk_le_mk_iff_right mk_le_mk_iff_right

@[to_dual self]

Depends on / 依赖: lt_iff_lt_of_le_iff_le, mk_le_mk_iff_right
-/
theorem mk_lt_mk_iff_right : (a, b₁) < (a, b₂) ↔ b₁ < b₂ :=
  lt_iff_lt_of_le_iff_le' mk_le_mk_iff_right mk_le_mk_iff_right

@[to_dual self]
/--
theorem `lt_iff` / 定理 `lt_iff`

English:
theorem lt_iff
  statement: x < y ↔ x.1 < y.1 ∧ x.2 <= y.2 ∨ x.1 <= y.1 ∧ x.2 < y.2
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · by_cases h₁ : y.1 <= x.1
    · exact Or.inr ⟨h.1.1, LE.le.lt_of_not_ge h.1.2 fun h₂ => h.2 ⟨h₁, h₂⟩⟩
    · exact Or.inl ⟨LE.le.lt_of_not_ge h.1.1 h₁, h.1.2⟩
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · exact ⟨⟨h₁.le, h₂⟩, fun h => h₁.not_ge h.1⟩
    · exact ⟨⟨h₁, h₂.le⟩, 

中文:
定理 lt_iff
  结论: x < y ↔ x.1 < y.1 ∧ x.2 <= y.2 ∨ x.1 <= y.1 ∧ x.2 < y.2
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · by_cases h₁ : y.1 <= x.1
    · exact Or.inr ⟨h.1.1, LE.le.lt_of_not_ge h.1.2 fun h₂ => h.2 ⟨h₁, h₂⟩⟩
    · exact Or.inl ⟨LE.le.lt_of_not_ge h.1.1 h₁, h.1.2⟩
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · exact ⟨⟨h₁.le, h₂⟩, fun h => h₁.not_ge h.1⟩
    · exact ⟨⟨h₁, h₂.le⟩, 

Depends on / 依赖: LE.le.lt_of_not_ge, Or.inl, Or.inr, lt_of_not_ge, not_ge
-/
theorem lt_iff : x < y ↔ x.1 < y.1 ∧ x.2 <= y.2 ∨ x.1 <= y.1 ∧ x.2 < y.2 := by
  refine ⟨fun h => ?_, ?_⟩
  · by_cases h₁ : y.1 <= x.1
    · exact Or.inr ⟨h.1.1, LE.le.lt_of_not_ge h.1.2 fun h₂ => h.2 ⟨h₁, h₂⟩⟩
    · exact Or.inl ⟨LE.le.lt_of_not_ge h.1.1 h₁, h.1.2⟩
  · rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · exact ⟨⟨h₁.le, h₂⟩, fun h => h₁.not_ge h.1⟩
    · exact ⟨⟨h₁, h₂.le⟩, fun h => h₂.not_ge h.2⟩

@[simp, to_dual self]
/--
theorem `mk_lt_mk` / 定理 `mk_lt_mk`

English:
theorem mk_lt_mk
  statement: (a₁, b₁) < (a₂, b₂) ↔ a₁ < a₂ ∧ b₁ <= b₂ ∨ a₁ <= a₂ ∧ b₁ < b₂
  proof: lt_iff

@[to_dual self]

中文:
定理 mk_lt_mk
  结论: (a₁, b₁) < (a₂, b₂) ↔ a₁ < a₂ ∧ b₁ <= b₂ ∨ a₁ <= a₂ ∧ b₁ < b₂
  证明: lt_iff

@[to_dual self]

Depends on / 依赖: lt_iff
-/
theorem mk_lt_mk : (a₁, b₁) < (a₂, b₂) ↔ a₁ < a₂ ∧ b₁ <= b₂ ∨ a₁ <= a₂ ∧ b₁ < b₂ :=
  lt_iff

@[to_dual self]
/--
lemma `lt_of_lt_of_le` / 引理 `lt_of_lt_of_le`

English:
lemma lt_of_lt_of_le
  given: (h₁ : x.1 < y.1) (h₂ : x.2 <= y.2)
  statement: x < y
  proof: by simp [lt_iff, *]

@[to_dual self]

中文:
引理 lt_of_lt_of_le
  条件: (h₁ : x.1 < y.1) (h₂ : x.2 <= y.2)
  结论: x < y
  证明: by simp [lt_iff, *]

@[to_dual self]
-/
protected lemma lt_of_lt_of_le (h₁ : x.1 < y.1) (h₂ : x.2 <= y.2) : x < y := by simp [lt_iff, *]

@[to_dual self]
/--
lemma `lt_of_le_of_lt` / 引理 `lt_of_le_of_lt`

English:
lemma lt_of_le_of_lt
  given: (h₁ : x.1 <= y.1) (h₂ : x.2 < y.2)
  statement: x < y
  proof: by simp [lt_iff, *]

@[to_dual self]

中文:
引理 lt_of_le_of_lt
  条件: (h₁ : x.1 <= y.1) (h₂ : x.2 < y.2)
  结论: x < y
  证明: by simp [lt_iff, *]

@[to_dual self]
-/
protected lemma lt_of_le_of_lt (h₁ : x.1 <= y.1) (h₂ : x.2 < y.2) : x < y := by simp [lt_iff, *]

@[to_dual self]
/--
lemma `mk_lt_mk_of_lt_of_le` / 引理 `mk_lt_mk_of_lt_of_le`

English:
lemma mk_lt_mk_of_lt_of_le
  given: (h₁ : a₁ < a₂) (h₂ : b₁ <= b₂)
  statement: (a₁, b₁) < (a₂, b₂)
  proof: by
  simp [lt_iff, *]

@[to_dual self]

中文:
引理 mk_lt_mk_of_lt_of_le
  条件: (h₁ : a₁ < a₂) (h₂ : b₁ <= b₂)
  结论: (a₁, b₁) < (a₂, b₂)
  证明: by
  simp [lt_iff, *]

@[to_dual self]

Depends on / 依赖: lt_iff
-/
lemma mk_lt_mk_of_lt_of_le (h₁ : a₁ < a₂) (h₂ : b₁ <= b₂) : (a₁, b₁) < (a₂, b₂) := by
  simp [lt_iff, *]

@[to_dual self]
/--
lemma `mk_lt_mk_of_le_of_lt` / 引理 `mk_lt_mk_of_le_of_lt`

English:
lemma mk_lt_mk_of_le_of_lt
  given: (h₁ : a₁ <= a₂) (h₂ : b₁ < b₂)
  statement: (a₁, b₁) < (a₂, b₂)
  proof: by
  simp [lt_iff, *]

中文:
引理 mk_lt_mk_of_le_of_lt
  条件: (h₁ : a₁ <= a₂) (h₂ : b₁ < b₂)
  结论: (a₁, b₁) < (a₂, b₂)
  证明: by
  simp [lt_iff, *]

Depends on / 依赖: lt_iff
-/
lemma mk_lt_mk_of_le_of_lt (h₁ : a₁ <= a₂) (h₂ : b₁ < b₂) : (a₁, b₁) < (a₂, b₂) := by
  simp [lt_iff, *]

end Preorder

/--
Instance `instPartialOrder` / 实例 `instPartialOrder`

English:
instance instPartialOrder
  signature: (α β : Type*) [PartialOrder α] [PartialOrder β]
  body: (inferInstance : Preorder (α × β))
  le_antisymm := fun _ _ ⟨hac, hbd⟩ ⟨hca, hdb⟩ => Prod.ext (hac.antisymm hca) (hbd.antisymm hdb)

中文:
实例 instPartialOrder
  签名: (α β : 类型) [偏序 α] [偏序 β]
  定义体: (inferInstance : Preorder (α × β))
  le_antisymm := fun _ _ ⟨hac, hbd⟩ ⟨hca, hdb⟩ => Prod.ext (hac.antisymm hca) (hbd.antisymm hdb)

Depends on / 依赖: Preorder
-/
instance instPartialOrder (α β : Type*) [PartialOrder α] [PartialOrder β] :
    PartialOrder (α × β) where
  __ := (inferInstance : Preorder (α × β))
  le_antisymm := fun _ _ ⟨hac, hbd⟩ ⟨hca, hdb⟩ => Prod.ext (hac.antisymm hca) (hbd.antisymm hdb)

end Prod

/-! ### Additional order classes -/

/--
Definition of `DenselyOrdered` / `DenselyOrdered` 的定义

English:
class DenselyOrdered
  parameters: (α : Type*) [LT α]
  axioms and operations (1):
    - dense : forall a₁ a₂ : α, a₁ < a₂ -> exists a, a₁ < a ∧ a < a₂

中文:
类 稠密序
  参数: (α : 类型) [LT α]
  公理与运算 (1 个):
    - dense : 对任意 a₁ a₂ : α, a₁ < a₂ -> 存在 a, a₁ < a ∧ a < a₂
-/
class DenselyOrdered (α : Type*) [LT α] : Prop where
  /-- An order is dense if there is an element between any pair of distinct elements. -/
  dense : forall a₁ a₂ : α, a₁ < a₂ -> exists a, a₁ < a ∧ a < a₂

@[to_dual existing dense]
/--
theorem `DenselyOrdered.dense'` / 定理 `DenselyOrdered.dense'`

English:
theorem DenselyOrdered.dense'
  given: [LT α] [DenselyOrdered α]
  proof: by
  simp_rw [and_comm]; exact dense

@[to_dual exists_between']

中文:
定理 稠密序.dense'
  条件: [LT α] [稠密序 α]
  证明: by
  simp_rw [and_comm]; exact dense

@[to_dual exists_between']

Depends on / 依赖: and_comm, simp_rw
-/
theorem DenselyOrdered.dense' [LT α] [DenselyOrdered α] :
    forall a₁ a₂ : α, a₁ < a₂ -> exists a, a < a₂ ∧ a₁ < a := by
  simp_rw [and_comm]; exact dense

@[to_dual exists_between']
/--
theorem `exists_between` / 定理 `exists_between`

English:
theorem exists_between
  given: [LT α] [DenselyOrdered α] {a₁ a₂ : α}
  statement: a₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
  proof: DenselyOrdered.dense _ _

中文:
定理 存在_between
  条件: [LT α] [稠密序 α] {a₁ a₂ : α}
  结论: a₁ < a₂ -> 存在 a, a₁ < a ∧ a < a₂
  证明: DenselyOrdered.dense _ _

Depends on / 依赖: DenselyOrdered, DenselyOrdered.dense
-/
theorem exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a₁ < a₂ -> exists a, a₁ < a ∧ a < a₂ :=
  DenselyOrdered.dense _ _


/--
lemma `Subsingleton.instDenselyOrdered` / 引理 `Subsingleton.instDenselyOrdered`

English:
lemma Subsingleton.instDenselyOrdered
  given: {X : Type*} [Subsingleton X] [LT X]
  proof: ⟨fun _ _ h => ⟨_, h.trans_eq (Subsingleton.elim _ _), h⟩⟩

中文:
引理 子单例.instDenselyOrdered
  条件: {X : 类型} [子单例 X] [LT X]
  证明: ⟨fun _ _ h => ⟨_, h.trans_eq (Subsingleton.elim _ _), h⟩⟩

Depends on / 依赖: Subsingleton, Subsingleton.elim, h.trans_eq, trans_eq
-/
lemma Subsingleton.instDenselyOrdered {X : Type*} [Subsingleton X] [LT X] :
    DenselyOrdered X :=
  ⟨fun _ _ h => ⟨_, h.trans_eq (Subsingleton.elim _ _), h⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: α] [Preorder β] [DenselyOrdered α] [DenselyOrdered β] : DenselyOrdered (α × β)
  body: ⟨fun a b => by
    simp_rw [Prod.lt_iff]
    rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · obtain ⟨c, ha, hb⟩ := exists_between h₁
      exact ⟨(c, _), Or.inl ⟨ha, h₂⟩, Or.inl ⟨hb, le_rfl⟩⟩
    · obtain ⟨c, ha, hb⟩ := exists_between h₂
      exact ⟨(_, c), Or.inr ⟨h₁, ha⟩, Or.inr ⟨le_rfl, hb⟩⟩⟩

中文:
实例 [预序
  签名: α] [预序 β] [稠密序 α] [稠密序 β] : 稠密序 (α × β)
  定义体: ⟨fun a b => by
    simp_rw [Prod.lt_iff]
    rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · obtain ⟨c, ha, hb⟩ := exists_between h₁
      exact ⟨(c, _), Or.inl ⟨ha, h₂⟩, Or.inl ⟨hb, le_rfl⟩⟩
    · obtain ⟨c, ha, hb⟩ := exists_between h₂
      exact ⟨(_, c), Or.inr ⟨h₁, ha⟩, Or.inr ⟨le_rfl, hb⟩⟩⟩

Depends on / 依赖: Or.inl, Or.inr, Prod.lt_iff, exists_between, le_rfl, lt_iff, simp_rw
-/
instance [Preorder α] [Preorder β] [DenselyOrdered α] [DenselyOrdered β] : DenselyOrdered (α × β) :=
  ⟨fun a b => by
    simp_rw [Prod.lt_iff]
    rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · obtain ⟨c, ha, hb⟩ := exists_between h₁
      exact ⟨(c, _), Or.inl ⟨ha, h₂⟩, Or.inl ⟨hb, le_rfl⟩⟩
    · obtain ⟨c, ha, hb⟩ := exists_between h₂
      exact ⟨(_, c), Or.inr ⟨h₁, ha⟩, Or.inr ⟨le_rfl, hb⟩⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, Preorder (π i)] [forall i, DenselyOrdered (π i)] :
  body: ⟨fun a b => by
    classical
      simp_rw [Pi.lt_def]
      rintro ⟨hab, i, hi⟩
      obtain ⟨c, ha, hb⟩ := exists_between hi
      exact
        ⟨Function.update a i c,
          ⟨le_update_iff.2 ⟨ha.le, fun _ _ => le_rfl⟩, i, by rwa [update_self]⟩,
          update_le_iff.2 ⟨hb.le, fun _ _ => hab

中文:
实例 [对任意
  签名: i, 预序 (π i)] [对任意 i, 稠密序 (π i)] :
  定义体: ⟨fun a b => by
    classical
      simp_rw [Pi.lt_def]
      rintro ⟨hab, i, hi⟩
      obtain ⟨c, ha, hb⟩ := exists_between hi
      exact
        ⟨Function.update a i c,
          ⟨le_update_iff.2 ⟨ha.le, fun _ _ => le_rfl⟩, i, by rwa [update_self]⟩,
          update_le_iff.2 ⟨hb.le, fun _ _ => hab

Depends on / 依赖: Function, Function.update, Pi.lt_def, classical, exists_between, ha.le, hb.le, le_rfl, le_update_iff, lt_def, simp_rw, update, update_le_iff, update_self
-/
instance [forall i, Preorder (π i)] [forall i, DenselyOrdered (π i)] :
    DenselyOrdered (forall i, π i) :=
  ⟨fun a b => by
    classical
      simp_rw [Pi.lt_def]
      rintro ⟨hab, i, hi⟩
      obtain ⟨c, ha, hb⟩ := exists_between hi
      exact
        ⟨Function.update a i c,
          ⟨le_update_iff.2 ⟨ha.le, fun _ _ => le_rfl⟩, i, by rwa [update_self]⟩,
          update_le_iff.2 ⟨hb.le, fun _ _ => hab _⟩, i, by rwa [update_self]⟩⟩

section LinearOrder
variable [LinearOrder α] [DenselyOrdered α] {a₁ a₂ : α}

@[to_dual le_of_forall_lt_imp_le_of_dense]
/--
theorem `le_of_forall_gt_imp_ge_of_dense` / 定理 `le_of_forall_gt_imp_ge_of_dense`

English:
theorem le_of_forall_gt_imp_ge_of_dense
  given: (h : forall a, a₂ < a -> a₁ <= a)
  statement: a₁ <= a₂
  proof: le_of_not_gt fun ha =>
    let ⟨a, ha₁, ha₂⟩ := exists_between ha
lt_irrefl a lt_of_lt_of_le ‹a < a₁› (h _ ‹a₂ < a›)

@[to_dual forall_lt_imp_le_iff_le_of_dense]

中文:
定理 le_of_对任意_gt_imp_ge_of_dense
  条件: (h : 对任意 a, a₂ < a -> a₁ <= a)
  结论: a₁ <= a₂
  证明: le_of_not_gt fun ha =>
    let ⟨a, ha₁, ha₂⟩ := exists_between ha
lt_irrefl a lt_of_lt_of_le ‹a < a₁› (h _ ‹a₂ < a›)

@[to_dual forall_lt_imp_le_iff_le_of_dense]

Depends on / 依赖: exists_between, le_of_not_gt, lt_irrefl, lt_of_lt_of_le
-/
theorem le_of_forall_gt_imp_ge_of_dense (h : forall a, a₂ < a -> a₁ <= a) : a₁ <= a₂ :=
  le_of_not_gt fun ha =>
    let ⟨a, ha₁, ha₂⟩ := exists_between ha
lt_irrefl a lt_of_lt_of_le ‹a < a₁› (h _ ‹a₂ < a›)

@[to_dual forall_lt_imp_le_iff_le_of_dense]
/--
lemma `forall_gt_imp_ge_iff_le_of_dense` / 引理 `forall_gt_imp_ge_iff_le_of_dense`

English:
lemma forall_gt_imp_ge_iff_le_of_dense
  statement: (forall a, a₂ < a -> a₁ <= a) ↔ a₁ <= a₂
  proof: ⟨le_of_forall_gt_imp_ge_of_dense, fun ha _a ha₂ => ha.trans ha₂.le⟩

中文:
引理 对任意_gt_imp_ge_iff_le_of_dense
  结论: (对任意 a, a₂ < a -> a₁ <= a) ↔ a₁ <= a₂
  证明: ⟨le_of_forall_gt_imp_ge_of_dense, fun ha _a ha₂ => ha.trans ha₂.le⟩

Depends on / 依赖: ha.trans, le_of_forall_gt_imp_ge_of_dense
-/
lemma forall_gt_imp_ge_iff_le_of_dense : (forall a, a₂ < a -> a₁ <= a) ↔ a₁ <= a₂ :=
  ⟨le_of_forall_gt_imp_ge_of_dense, fun ha _a ha₂ => ha.trans ha₂.le⟩

-- TODO: these two lemma names are the wrong way around
@[to_dual eq_of_le_of_forall_gt_imp_ge_of_dense]
/--
lemma `eq_of_le_of_forall_lt_imp_le_of_dense` / 引理 `eq_of_le_of_forall_lt_imp_le_of_dense`

English:
lemma eq_of_le_of_forall_lt_imp_le_of_dense
  given: (h₁ : a₂ <= a₁) (h₂ : forall a, a₂ < a -> a₁ <= a)
  statement: a₁ = a₂
  proof: le_antisymm (le_of_forall_gt_imp_ge_of_dense h₂) h₁

中文:
引理 eq_of_le_of_对任意_lt_imp_le_of_dense
  条件: (h₁ : a₂ <= a₁) (h₂ : 对任意 a, a₂ < a -> a₁ <= a)
  结论: a₁ = a₂
  证明: le_antisymm (le_of_forall_gt_imp_ge_of_dense h₂) h₁

Depends on / 依赖: le_antisymm, le_of_forall_gt_imp_ge_of_dense
-/
lemma eq_of_le_of_forall_lt_imp_le_of_dense (h₁ : a₂ <= a₁) (h₂ : forall a, a₂ < a -> a₁ <= a) : a₁ = a₂ :=
  le_antisymm (le_of_forall_gt_imp_ge_of_dense h₂) h₁

end LinearOrder

@[to_dual dense_or_discrete']
/--
theorem `dense_or_discrete` / 定理 `dense_or_discrete`

English:
theorem dense_or_discrete
  given: [LinearOrder α] (a₁ a₂ : α)
  proof: or_iff_not_imp_left.2 fun h =>
    ⟨fun a ha₁ => le_of_not_gt fun ha₂ => h ⟨a, ha₁, ha₂⟩,
     fun a ha₂ => le_of_not_gt fun ha₁ => h ⟨a, ha₁, ha₂⟩⟩

中文:
定理 dense_or_discrete
  条件: [线性序 α] (a₁ a₂ : α)
  证明: or_iff_not_imp_left.2 fun h =>
    ⟨fun a ha₁ => le_of_not_gt fun ha₂ => h ⟨a, ha₁, ha₂⟩,
     fun a ha₂ => le_of_not_gt fun ha₁ => h ⟨a, ha₁, ha₂⟩⟩

Depends on / 依赖: le_of_not_gt, or_iff_not_imp_left
-/
theorem dense_or_discrete [LinearOrder α] (a₁ a₂ : α) :
    (exists a, a₁ < a ∧ a < a₂) ∨ (forall a, a₁ < a -> a₂ <= a) ∧ forall a < a₂, a <= a₁ :=
  or_iff_not_imp_left.2 fun h =>
    ⟨fun a ha₁ => le_of_not_gt fun ha₂ => h ⟨a, ha₁, ha₂⟩,
     fun a ha₂ => le_of_not_gt fun ha₁ => h ⟨a, ha₁, ha₂⟩⟩

/-- If a linear order has no elements `x < y < z`, then it has at most two elements. -/
@[to_dual self (reorder := h (x z, 4 5))]
/--
lemma `eq_or_eq_or_eq_of_forall_not_lt_lt` / 引理 `eq_or_eq_or_eq_of_forall_not_lt_lt`

English:
lemma eq_or_eq_or_eq_of_forall_not_lt_lt
  statement: [LinearOrder α]
  proof: by
  by_contra hne
  simp only [not_or, ← Ne.eq_def] at hne
  rcases hne.1.lt_or_gt with h₁ | h₁ <;>
  rcases hne.2.1.lt_or_gt with h₂ | h₂ <;>
  rcases hne.2.2.lt_or_gt with h₃ | h₃
  exacts [h h₁ h₂, h h₂ h₃, h h₃ h₂, h h₃ h₁, h h₁ h₃, h h₂ h₃, h h₁ h₃, h h₂ h₁]

中文:
引理 eq_or_eq_or_eq_of_对任意_not_lt_lt
  结论: [线性序 α]
  证明: by
  by_contra hne
  simp only [not_or, ← Ne.eq_def] at hne
  rcases hne.1.lt_or_gt with h₁ | h₁ <;>
  rcases hne.2.1.lt_or_gt with h₂ | h₂ <;>
  rcases hne.2.2.lt_or_gt with h₃ | h₃
  exacts [h h₁ h₂, h h₂ h₃, h h₃ h₂, h h₃ h₁, h h₁ h₃, h h₂ h₃, h h₁ h₃, h h₂ h₁]

Depends on / 依赖: Ne.eq_def, eq_def, exacts, lt_or_gt, not_or
-/
lemma eq_or_eq_or_eq_of_forall_not_lt_lt [LinearOrder α]
    (h : forall ⦃x y z : α⦄, x < y -> y < z -> False) (x y z : α) : x = y ∨ y = z ∨ x = z := by
  by_contra hne
  simp only [not_or, ← Ne.eq_def] at hne
  rcases hne.1.lt_or_gt with h₁ | h₁ <;>
  rcases hne.2.1.lt_or_gt with h₂ | h₂ <;>
  rcases hne.2.2.lt_or_gt with h₃ | h₃
  exacts [h h₁ h₂, h h₂ h₃, h h₃ h₂, h h₃ h₁, h h₁ h₃, h h₂ h₃, h h₁ h₃, h h₂ h₁]

/--
Definition of `LinearOrder.ofSubsingleton` / `LinearOrder.ofSubsingleton` 的定义

English:
abbreviation LinearOrder.ofSubsingleton
  signature: {α : Type*} [Subsingleton α]
  body: True
  lt _ _ := False
  le_refl _ := trivial
  le_trans x y z _ _ := trivial
  le_antisymm x y _ _ := Subsingleton.elim x y
  le_total _ _ := .inl trivial
  lt_iff_le_not_ge _ _ := by simp
  toDecidableLE _ _ := instDecidableTrue

中文:
缩写 线性序.ofSubsingleton
  签名: {α : 类型} [子单例 α]
  定义体: True
  lt _ _ := False
  le_refl _ := trivial
  le_trans x y z _ _ := trivial
  le_antisymm x y _ _ := Subsingleton.elim x y
  le_total _ _ := .inl trivial
  lt_iff_le_not_ge _ _ := by simp
  toDecidableLE _ _ := instDecidableTrue
-/
abbrev LinearOrder.ofSubsingleton {α : Type*} [Subsingleton α] : LinearOrder α where
  le _ _ := True
  lt _ _ := False
  le_refl _ := trivial
  le_trans x y z _ _ := trivial
  le_antisymm x y _ _ := Subsingleton.elim x y
  le_total _ _ := .inl trivial
  lt_iff_le_not_ge _ _ := by simp
  toDecidableLE _ _ := instDecidableTrue

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LinearOrder Empty
  body: .ofSubsingleton

中文:
实例 :
  签名: 线性序 空
  定义体: .ofSubsingleton

Depends on / 依赖: ofSubsingleton
-/
instance : LinearOrder Empty := .ofSubsingleton
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LinearOrder PEmpty
  body: .ofSubsingleton

中文:
实例 :
  签名: 线性序 命题空
  定义体: .ofSubsingleton
-/
instance : LinearOrder PEmpty := .ofSubsingleton

namespace PUnit

variable (a b : PUnit)

/--
Instance `instLinearOrder` / 实例 `instLinearOrder`

English:
instance instLinearOrder
  signature: : LinearOrder PUnit
  body: .ofSubsingleton

@[to_dual]

中文:
实例 instLinearOrder
  签名: : 线性序 命题单元
  定义体: .ofSubsingleton

@[to_dual]

Depends on / 依赖: ofSubsingleton
-/
instance instLinearOrder : LinearOrder PUnit := .ofSubsingleton

@[to_dual]
/--
theorem `max_eq` / 定理 `max_eq`

English:
theorem max_eq
  statement: max a b = unit
  proof: rfl

@[to_dual self]

中文:
定理 max_eq
  结论: 最大值 a b = unit
  证明: rfl

@[to_dual self]
-/
theorem max_eq : max a b = unit :=
  rfl

@[to_dual self]
/--
theorem `le` / 定理 `le`

English:
theorem le
  statement: a <= b
  proof: trivial

@[to_dual self]

中文:
定理 le
  结论: a <= b
  证明: trivial

@[to_dual self]
-/
protected theorem le : a <= b :=
  trivial

@[to_dual self]
/--
theorem `not_lt` / 定理 `not_lt`

English:
theorem not_lt
  statement: ¬a < b
  proof: not_false

中文:
定理 not_lt
  结论: ¬a < b
  证明: not_false

Depends on / 依赖: not_false
-/
theorem not_lt : ¬a < b :=
  not_false

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DenselyOrdered PUnit
  body: ⟨fun _ _ => False.elim⟩

中文:
实例 :
  签名: 稠密序 命题单元
  定义体: ⟨fun _ _ => False.elim⟩

Depends on / 依赖: False.elim
-/
instance : DenselyOrdered PUnit :=
  ⟨fun _ _ => False.elim⟩

end PUnit

section «Prop»

/--
theorem `subrelation_iff_le` / 定理 `subrelation_iff_le`

English:
theorem subrelation_iff_le
  given: {r s : α -> α -> Prop}
  statement: Subrelation r s ↔ r <= s
  proof: Iff.rfl

中文:
定理 subrelation_iff_le
  条件: {r s : α -> α -> 命题}
  结论: Subrelation r s ↔ r <= s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem subrelation_iff_le {r s : α -> α -> Prop} : Subrelation r s ↔ r <= s :=
  Iff.rfl

/--
Instance `Prop.partialOrder` / 实例 `Prop.partialOrder`

English:
instance Prop.partialOrder
  signature: : PartialOrder Prop where
  body: Prop.le
  le_refl _ := id
  le_trans _ _ _ f g := g ∘ f
  le_antisymm _ _ Hab Hba := propext ⟨Hab, Hba⟩

中文:
实例 命题.partialOrder
  签名: : 偏序 命题 where
  定义体: Prop.le
  le_refl _ := id
  le_trans _ _ _ f g := g ∘ f
  le_antisymm _ _ Hab Hba := propext ⟨Hab, Hba⟩

Depends on / 依赖: Prop.le
-/
instance Prop.partialOrder : PartialOrder Prop where
  __ := Prop.le
  le_refl _ := id
  le_trans _ _ _ f g := g ∘ f
  le_antisymm _ _ Hab Hba := propext ⟨Hab, Hba⟩

end «Prop»
