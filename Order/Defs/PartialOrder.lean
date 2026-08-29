/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

public import Batteries.Tactic.Alias
public import Batteries.Tactic.Trans
public import Mathlib.Tactic.ExtendDoc
public import Mathlib.Tactic.ToDual

/-!
# Orders

Defines classes for preorders and partial orders
and proves some basic lemmas about them.

We also define covering relations on a preorder.
We say that `b` *covers* `a` if `a < b` and there is no element in between.
We say that `b` *weakly covers* `a` if `a ≤ b` and there is no element between `a` and `b`.
In a partial order this is equivalent to `a ⋖ b ∨ a = b`,
in a preorder this is equivalent to `a ⋖ b ∨ (a ≤ b ∧ b ≤ a)`

## Notation

* `a ⋖ b` means that `b` covers `a`.
* `a ⩿ b` means that `b` weakly covers `a`.
-/

@[expose] public section

variable {α : Type*}

section Preorder

/-!
### Definition of `Preorder` and lemmas about types with a `Preorder`
-/

/--
Definition of `Preorder` / `Preorder` 的定义

English:
class Preorder
  parameters: (α : Type*)
  extends: LE α, LT α
  axioms and operations (4):
    - le_refl : forall a : α, a <= a
    - le_trans : forall a b c : α, a <= b -> b <= c -> a <= c
    - lt : = fun a b => a <= b ∧ ¬b <= a
    - lt_iff_le_not_ge : forall a b : α, a < b ↔ a <= b ∧ ¬b <= a  [default: by intros; rfl]

中文:
类 预序
  参数: (α : 类型)
  继承: LE α, LT α
  公理与运算 (4 个):
    - le_refl : 对任意 a : α, a <= a
    - le_trans : 对任意 a b c : α, a <= b -> b <= c -> a <= c
    - lt : = fun a b => a <= b ∧ ¬b <= a
    - lt_iff_le_not_ge : 对任意 a b : α, a < b ↔ a <= b ∧ ¬b <= a  [默认: by intros; rfl]
-/
class Preorder (α : Type*) extends LE α, LT α where
  protected le_refl : forall a : α, a <= a
  protected le_trans : forall a b c : α, a <= b -> b <= c -> a <= c
  lt := fun a b => a <= b ∧ ¬b <= a
  protected lt_iff_le_not_ge : forall a b : α, a < b ↔ a <= b ∧ ¬b <= a := by intros; rfl

attribute [to_dual self (reorder := le_trans (a c, 4 5), lt_iff_le_not_ge (a b))] Preorder.mk

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: α] : Std.LawfulOrderLT α where
  body: Preorder.lt_iff_le_not_ge

中文:
实例 [预序
  签名: α] : Std.LawfulOrderLT α where
  定义体: Preorder.lt_iff_le_not_ge

Depends on / 依赖: Preorder, Preorder.lt_iff_le_not_ge, lt_iff_le_not_ge
-/
instance [Preorder α] : Std.LawfulOrderLT α where
  lt_iff := Preorder.lt_iff_le_not_ge

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: α] : Std.IsPreorder α where
  body: Preorder.le_refl
  le_trans := Preorder.le_trans

中文:
实例 [预序
  签名: α] : Std.是预序 α where
  定义体: Preorder.le_refl
  le_trans := Preorder.le_trans

Depends on / 依赖: Preorder, Preorder.le_refl, le_refl
-/
instance [Preorder α] : Std.IsPreorder α where
  le_refl := Preorder.le_refl
  le_trans := Preorder.le_trans

variable [Preorder α] {a b c : α}

/--
lemma `le_refl` / 引理 `le_refl`

English:
lemma le_refl
  statement: forall a : α, a <= a
  proof: Preorder.le_refl

中文:
引理 le_refl
  结论: 对任意 a : α, a <= a
  证明: Preorder.le_refl
-/
@[refl] lemma le_refl : forall a : α, a <= a := Preorder.le_refl

/--
lemma `le_rfl` / 引理 `le_rfl`

English:
lemma le_rfl
  statement: a <= a
  proof: le_refl a

中文:
引理 le_rfl
  结论: a <= a
  证明: le_refl a

Depends on / 依赖: le_refl
-/
lemma le_rfl : a <= a := le_refl a

/--
lemma `le_trans` / 引理 `le_trans`

English:
lemma le_trans
  statement: a <= b -> b <= c -> a <= c
  proof: Preorder.le_trans _ _ _

@[to_dual existing le_trans]

中文:
引理 le_trans
  结论: a <= b -> b <= c -> a <= c
  证明: Preorder.le_trans _ _ _

@[to_dual existing le_trans]

Depends on / 依赖: Preorder, Preorder.le_trans, le_trans
-/
lemma le_trans : a <= b -> b <= c -> a <= c := Preorder.le_trans _ _ _

@[to_dual existing le_trans]
/--
lemma `ge_trans` / 引理 `ge_trans`

English:
lemma ge_trans
  statement: b <= a -> c <= b -> c <= a
  proof: flip le_trans

@[to_dual self]

中文:
引理 ge_trans
  结论: b <= a -> c <= b -> c <= a
  证明: flip le_trans

@[to_dual self]

Depends on / 依赖: le_trans
-/
lemma ge_trans : b <= a -> c <= b -> c <= a := flip le_trans

@[to_dual self]
/--
lemma `lt_iff_le_not_ge` / 引理 `lt_iff_le_not_ge`

English:
lemma lt_iff_le_not_ge
  statement: a < b ↔ a <= b ∧ ¬b <= a
  proof: Preorder.lt_iff_le_not_ge _ _

@[to_dual self]

中文:
引理 lt_iff_le_not_ge
  结论: a < b ↔ a <= b ∧ ¬b <= a
  证明: Preorder.lt_iff_le_not_ge _ _

@[to_dual self]

Depends on / 依赖: Preorder, Preorder.lt_iff_le_not_ge, lt_iff_le_not_ge
-/
lemma lt_iff_le_not_ge : a < b ↔ a <= b ∧ ¬b <= a := Preorder.lt_iff_le_not_ge _ _

@[to_dual self]
/--
lemma `lt_of_le_not_ge` / 引理 `lt_of_le_not_ge`

English:
lemma lt_of_le_not_ge
  given: (hab : a <= b) (hba : ¬ b <= a)
  statement: a < b
  proof: lt_iff_le_not_ge.2 ⟨hab, hba⟩

中文:
引理 lt_of_le_not_ge
  条件: (hab : a <= b) (hba : ¬ b <= a)
  结论: a < b
  证明: lt_iff_le_not_ge.2 ⟨hab, hba⟩

Depends on / 依赖: lt_iff_le_not_ge
-/
lemma lt_of_le_not_ge (hab : a <= b) (hba : ¬ b <= a) : a < b := lt_iff_le_not_ge.2 ⟨hab, hba⟩

/--
lemma `le_of_eq` / 引理 `le_of_eq`

English:
lemma le_of_eq
  given: (hab : a = b)
  statement: a <= b
  proof: by rw [hab]

中文:
引理 le_of_eq
  条件: (hab : a = b)
  结论: a <= b
  证明: by rw [hab]
-/
@[to_dual ge_of_eq] lemma le_of_eq (hab : a = b) : a <= b := by rw [hab]
/--
lemma `le_of_lt` / 引理 `le_of_lt`

English:
lemma le_of_lt
  given: (hab : a < b)
  statement: a <= b
  proof: (lt_iff_le_not_ge.1 hab).1

中文:
引理 le_of_lt
  条件: (hab : a < b)
  结论: a <= b
  证明: (lt_iff_le_not_ge.1 hab).1
-/
@[to_dual self] lemma le_of_lt (hab : a < b) : a <= b := (lt_iff_le_not_ge.1 hab).1
/--
lemma `not_le_of_gt` / 引理 `not_le_of_gt`

English:
lemma not_le_of_gt
  given: (hab : a < b)
  statement: ¬ b <= a
  proof: (lt_iff_le_not_ge.1 hab).2

中文:
引理 not_le_of_gt
  条件: (hab : a < b)
  结论: ¬ b <= a
  证明: (lt_iff_le_not_ge.1 hab).2
-/
@[to_dual self] lemma not_le_of_gt (hab : a < b) : ¬ b <= a := (lt_iff_le_not_ge.1 hab).2
/--
lemma `not_lt_of_ge` / 引理 `not_lt_of_ge`

English:
lemma not_lt_of_ge
  given: (hab : a <= b)
  statement: ¬ b < a
  proof: imp_not_comm.1 not_le_of_gt hab

@[to_dual self] alias LT.lt.not_ge := not_le_of_gt
@[to_dual self] alias LE.le.not_gt := not_lt_of_ge

中文:
引理 not_lt_of_ge
  条件: (hab : a <= b)
  结论: ¬ b < a
  证明: imp_not_comm.1 not_le_of_gt hab

@[to_dual self] alias LT.lt.not_ge := not_le_of_gt
@[to_dual self] alias LE.le.not_gt := not_lt_of_ge
-/
@[to_dual self] lemma not_lt_of_ge (hab : a <= b) : ¬ b < a := imp_not_comm.1 not_le_of_gt hab

@[to_dual self] alias LT.lt.not_ge := not_le_of_gt
@[to_dual self] alias LE.le.not_gt := not_lt_of_ge

/--
lemma `lt_irrefl` / 引理 `lt_irrefl`

English:
lemma lt_irrefl
  given: (a : α)
  statement: ¬a < a
  proof: fun h => not_le_of_gt h le_rfl

@[to_dual lt_of_lt_of_le']

中文:
引理 lt_irrefl
  条件: (a : α)
  结论: ¬a < a
  证明: fun h => not_le_of_gt h le_rfl

@[to_dual lt_of_lt_of_le']

Depends on / 依赖: le_rfl, not_le_of_gt
-/
lemma lt_irrefl (a : α) : ¬a < a := fun h => not_le_of_gt h le_rfl

@[to_dual lt_of_lt_of_le']
/--
lemma `lt_of_lt_of_le` / 引理 `lt_of_lt_of_le`

English:
lemma lt_of_lt_of_le
  given: (hab : a < b) (hbc : b <= c)
  statement: a < c
  proof: lt_of_le_not_ge (le_trans (le_of_lt hab) hbc) fun hca => not_le_of_gt hab (le_trans hbc hca)

@[to_dual lt_of_le_of_lt']

中文:
引理 lt_of_lt_of_le
  条件: (hab : a < b) (hbc : b <= c)
  结论: a < c
  证明: lt_of_le_not_ge (le_trans (le_of_lt hab) hbc) fun hca => not_le_of_gt hab (le_trans hbc hca)

@[to_dual lt_of_le_of_lt']

Depends on / 依赖: le_of_lt, le_trans, lt_of_le_not_ge, not_le_of_gt
-/
lemma lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c :=
  lt_of_le_not_ge (le_trans (le_of_lt hab) hbc) fun hca => not_le_of_gt hab (le_trans hbc hca)

@[to_dual lt_of_le_of_lt']
/--
lemma `lt_of_le_of_lt` / 引理 `lt_of_le_of_lt`

English:
lemma lt_of_le_of_lt
  given: (hab : a <= b) (hbc : b < c)
  statement: a < c
  proof: lt_of_le_not_ge (le_trans hab (le_of_lt hbc)) fun hca => not_le_of_gt hbc (le_trans hca hab)

@[to_dual gt_trans]

中文:
引理 lt_of_le_of_lt
  条件: (hab : a <= b) (hbc : b < c)
  结论: a < c
  证明: lt_of_le_not_ge (le_trans hab (le_of_lt hbc)) fun hca => not_le_of_gt hbc (le_trans hca hab)

@[to_dual gt_trans]

Depends on / 依赖: le_of_lt, le_trans, lt_of_le_not_ge, not_le_of_gt
-/
lemma lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c :=
  lt_of_le_not_ge (le_trans hab (le_of_lt hbc)) fun hca => not_le_of_gt hbc (le_trans hca hab)

@[to_dual gt_trans]
/--
lemma `lt_trans` / 引理 `lt_trans`

English:
lemma lt_trans
  statement: a < b -> b < c -> a < c
  proof: fun h₁ h₂ => lt_of_lt_of_le h₁ (le_of_lt h₂)

@[to_dual ne_of_gt]

中文:
引理 lt_trans
  结论: a < b -> b < c -> a < c
  证明: fun h₁ h₂ => lt_of_lt_of_le h₁ (le_of_lt h₂)

@[to_dual ne_of_gt]

Depends on / 依赖: le_of_lt, lt_of_lt_of_le
-/
lemma lt_trans : a < b -> b < c -> a < c := fun h₁ h₂ => lt_of_lt_of_le h₁ (le_of_lt h₂)

@[to_dual ne_of_gt]
/--
lemma `ne_of_lt` / 引理 `ne_of_lt`

English:
lemma ne_of_lt
  given: (h : a < b)
  statement: a != b
  proof: fun he => absurd h (he ▸ lt_irrefl a)
@[to_dual self]

中文:
引理 ne_of_lt
  条件: (h : a < b)
  结论: a != b
  证明: fun he => absurd h (he ▸ lt_irrefl a)
@[to_dual self]

Depends on / 依赖: absurd, lt_irrefl
-/
lemma ne_of_lt (h : a < b) : a != b := fun he => absurd h (he ▸ lt_irrefl a)
@[to_dual self]
/--
lemma `lt_asymm` / 引理 `lt_asymm`

English:
lemma lt_asymm
  given: (h : a < b)
  statement: ¬b < a
  proof: fun h1 : b < a => lt_irrefl a (lt_trans h h1)

@[to_dual self] alias not_lt_of_gt := lt_asymm

@[to_dual le_of_lt_or_eq']

中文:
引理 lt_asymm
  条件: (h : a < b)
  结论: ¬b < a
  证明: fun h1 : b < a => lt_irrefl a (lt_trans h h1)

@[to_dual self] alias not_lt_of_gt := lt_asymm

@[to_dual le_of_lt_or_eq']

Depends on / 依赖: lt_irrefl, lt_trans
-/
lemma lt_asymm (h : a < b) : ¬b < a := fun h1 : b < a => lt_irrefl a (lt_trans h h1)

@[to_dual self] alias not_lt_of_gt := lt_asymm

@[to_dual le_of_lt_or_eq']
/--
lemma `le_of_lt_or_eq` / 引理 `le_of_lt_or_eq`

English:
lemma le_of_lt_or_eq
  given: (h : a < b ∨ a = b)
  statement: a <= b
  proof: h.elim le_of_lt le_of_eq
@[to_dual le_of_eq_or_lt']

中文:
引理 le_of_lt_or_eq
  条件: (h : a < b ∨ a = b)
  结论: a <= b
  证明: h.elim le_of_lt le_of_eq
@[to_dual le_of_eq_or_lt']

Depends on / 依赖: h.elim, le_of_eq, le_of_lt
-/
lemma le_of_lt_or_eq (h : a < b ∨ a = b) : a <= b := h.elim le_of_lt le_of_eq
@[to_dual le_of_eq_or_lt']
/--
lemma `le_of_eq_or_lt` / 引理 `le_of_eq_or_lt`

English:
lemma le_of_eq_or_lt
  given: (h : a = b ∨ a < b)
  statement: a <= b
  proof: h.elim le_of_eq le_of_lt

@[to_dual self]

中文:
引理 le_of_eq_or_lt
  条件: (h : a = b ∨ a < b)
  结论: a <= b
  证明: h.elim le_of_eq le_of_lt

@[to_dual self]

Depends on / 依赖: h.elim, le_of_eq, le_of_lt
-/
lemma le_of_eq_or_lt (h : a = b ∨ a < b) : a <= b := h.elim le_of_eq le_of_lt

@[to_dual self]
/--
lemma `lt_iff_gt_iff_le_iff_ge` / 引理 `lt_iff_gt_iff_le_iff_ge`

English:
lemma lt_iff_gt_iff_le_iff_ge
  statement: (a < b ↔ b < a) ↔ (a <= b ↔ b <= a)
  proof: by
  grind [= lt_iff_le_not_ge]

@[to_dual self]

中文:
引理 lt_iff_gt_iff_le_iff_ge
  结论: (a < b ↔ b < a) ↔ (a <= b ↔ b <= a)
  证明: by
  grind [= lt_iff_le_not_ge]

@[to_dual self]

Depends on / 依赖: lt_iff_le_not_ge
-/
lemma lt_iff_gt_iff_le_iff_ge : (a < b ↔ b < a) ↔ (a <= b ↔ b <= a) := by
  grind [= lt_iff_le_not_ge]

@[to_dual self]
/--
lemma `lt_iff_le_iff_gt_iff_ge` / 引理 `lt_iff_le_iff_gt_iff_ge`

English:
lemma lt_iff_le_iff_gt_iff_ge
  statement: (a < b ↔ a <= b) ↔ (b < a ↔ b <= a)
  proof: by
  grind [= lt_iff_le_not_ge]

@[to_dual self]

中文:
引理 lt_iff_le_iff_gt_iff_ge
  结论: (a < b ↔ a <= b) ↔ (b < a ↔ b <= a)
  证明: by
  grind [= lt_iff_le_not_ge]

@[to_dual self]

Depends on / 依赖: lt_iff_le_not_ge
-/
lemma lt_iff_le_iff_gt_iff_ge : (a < b ↔ a <= b) ↔ (b < a ↔ b <= a) := by
  grind [= lt_iff_le_not_ge]

@[to_dual self]
/--
lemma `lt_iff_ge_iff_gt_iff_le` / 引理 `lt_iff_ge_iff_gt_iff_le`

English:
lemma lt_iff_ge_iff_gt_iff_le
  statement: (a < b ↔ b <= a) ↔ (b < a ↔ a <= b)
  proof: by
  grind [= lt_iff_le_not_ge]

中文:
引理 lt_iff_ge_iff_gt_iff_le
  结论: (a < b ↔ b <= a) ↔ (b < a ↔ a <= b)
  证明: by
  grind [= lt_iff_le_not_ge]

Depends on / 依赖: lt_iff_le_not_ge
-/
lemma lt_iff_ge_iff_gt_iff_le : (a < b ↔ b <= a) ↔ (b < a ↔ a <= b) := by
  grind [= lt_iff_le_not_ge]

/--
Instance `instTransLE` / 实例 `instTransLE`

English:
instance instTransLE
  signature: : @Trans α α α LE.le LE.le LE.le
  body: ⟨le_trans⟩

中文:
实例 instTransLE
  签名: : @Trans α α α LE.le LE.le LE.le
  定义体: ⟨le_trans⟩

Depends on / 依赖: le_trans
-/
instance instTransLE : @Trans α α α LE.le LE.le LE.le := ⟨le_trans⟩
/--
Instance `instTransLT` / 实例 `instTransLT`

English:
instance instTransLT
  signature: : @Trans α α α LT.lt LT.lt LT.lt
  body: ⟨lt_trans⟩

中文:
实例 instTransLT
  签名: : @Trans α α α LT.lt LT.lt LT.lt
  定义体: ⟨lt_trans⟩

Depends on / 依赖: lt_trans
-/
instance instTransLT : @Trans α α α LT.lt LT.lt LT.lt := ⟨lt_trans⟩
/--
Instance `instTransLTLE` / 实例 `instTransLTLE`

English:
instance instTransLTLE
  signature: : @Trans α α α LT.lt LE.le LT.lt
  body: ⟨lt_of_lt_of_le⟩

中文:
实例 instTransLTLE
  签名: : @Trans α α α LT.lt LE.le LT.lt
  定义体: ⟨lt_of_lt_of_le⟩

Depends on / 依赖: lt_of_lt_of_le
-/
instance instTransLTLE : @Trans α α α LT.lt LE.le LT.lt := ⟨lt_of_lt_of_le⟩
/--
Instance `instTransLELT` / 实例 `instTransLELT`

English:
instance instTransLELT
  signature: : @Trans α α α LE.le LT.lt LT.lt
  body: ⟨lt_of_le_of_lt⟩

中文:
实例 instTransLELT
  签名: : @Trans α α α LE.le LT.lt LT.lt
  定义体: ⟨lt_of_le_of_lt⟩

Depends on / 依赖: lt_of_le_of_lt
-/
instance instTransLELT : @Trans α α α LE.le LT.lt LT.lt := ⟨lt_of_le_of_lt⟩
-- we have to express the following 4 instances in terms of `≥` instead of flipping the arguments
-- to `≤`, because otherwise `calc` gets confused.
@[to_dual existing instTransLE]
/--
Instance `instTransGE` / 实例 `instTransGE`

English:
instance instTransGE
  signature: : @Trans α α α GE.ge GE.ge GE.ge
  body: ⟨ge_trans⟩
@[to_dual existing instTransLT]

中文:
实例 instTransGE
  签名: : @Trans α α α GE.ge GE.ge GE.ge
  定义体: ⟨ge_trans⟩
@[to_dual existing instTransLT]

Depends on / 依赖: ge_trans
-/
instance instTransGE : @Trans α α α GE.ge GE.ge GE.ge := ⟨ge_trans⟩
@[to_dual existing instTransLT]
/--
Instance `instTransGT` / 实例 `instTransGT`

English:
instance instTransGT
  signature: : @Trans α α α GT.gt GT.gt GT.gt
  body: ⟨gt_trans⟩
@[to_dual existing instTransLTLE]

中文:
实例 instTransGT
  签名: : @Trans α α α GT.gt GT.gt GT.gt
  定义体: ⟨gt_trans⟩
@[to_dual existing instTransLTLE]

Depends on / 依赖: gt_trans
-/
instance instTransGT : @Trans α α α GT.gt GT.gt GT.gt := ⟨gt_trans⟩
@[to_dual existing instTransLTLE]
/--
Instance `instTransGTGE` / 实例 `instTransGTGE`

English:
instance instTransGTGE
  signature: : @Trans α α α GT.gt GE.ge GT.gt
  body: ⟨lt_of_lt_of_le'⟩
@[to_dual existing instTransLELT]

中文:
实例 instTransGTGE
  签名: : @Trans α α α GT.gt GE.ge GT.gt
  定义体: ⟨lt_of_lt_of_le'⟩
@[to_dual existing instTransLELT]

Depends on / 依赖: lt_of_lt_of_le
-/
instance instTransGTGE : @Trans α α α GT.gt GE.ge GT.gt := ⟨lt_of_lt_of_le'⟩
@[to_dual existing instTransLELT]
/--
Instance `instTransGEGT` / 实例 `instTransGEGT`

English:
instance instTransGEGT
  signature: : @Trans α α α GE.ge GT.gt GT.gt
  body: ⟨lt_of_le_of_lt'⟩

中文:
实例 instTransGEGT
  签名: : @Trans α α α GE.ge GT.gt GT.gt
  定义体: ⟨lt_of_le_of_lt'⟩

Depends on / 依赖: lt_of_le_of_lt
-/
instance instTransGEGT : @Trans α α α GE.ge GT.gt GT.gt := ⟨lt_of_le_of_lt'⟩

/-- `<` is decidable if `≤` is. -/
@[instance_reducible]
/--
Definition of `decidableLTOfDecidableLE` / `decidableLTOfDecidableLE` 的定义

English:
definition decidableLTOfDecidableLE
  signature: [DecidableLE α]
  body: fun _ _ => decidable_of_iff _ lt_iff_le_not_ge.symm

中文:
定义 decidableLTOfDecidableLE
  签名: [DecidableLE α]
  定义体: fun _ _ => decidable_of_iff _ lt_iff_le_not_ge.symm

Depends on / 依赖: decidable_of_iff, lt_iff_le_not_ge, lt_iff_le_not_ge.symm
-/
def decidableLTOfDecidableLE [DecidableLE α] : DecidableLT α :=
  fun _ _ => decidable_of_iff _ lt_iff_le_not_ge.symm

/-- `WCovBy a b` means that `a = b` or `b` covers `a`.
This means that `a ≤ b` and there is no element in between. This is denoted `a ⩿ b`.
-/
@[to_dual self (reorder := 3 4)]
/--
Definition of `WCovBy` / `WCovBy` 的定义

English:
definition WCovBy
  signature: (a b : α)
  body: a <= b ∧ forall ⦃c⦄, a < c -> ¬c < b

to_dual_insert_cast WCovBy := by grind

@[inherit_doc]
infixl:50 " ⩿ " => WCovBy

中文:
定义 WCovBy
  签名: (a b : α)
  定义体: a <= b ∧ forall ⦃c⦄, a < c -> ¬c < b

to_dual_insert_cast WCovBy := by grind

@[inherit_doc]
infixl:50 " ⩿ " => WCovBy
-/
def WCovBy (a b : α) : Prop :=
  a <= b ∧ forall ⦃c⦄, a < c -> ¬c < b

to_dual_insert_cast WCovBy := by grind

@[inherit_doc]
infixl:50 " ⩿ " => WCovBy

/-- `CovBy a b` means that `b` covers `a`. This means that `a < b` and there is no element in
between. This is denoted `a ⋖ b`. -/
@[to_dual self (reorder := 3 4)]
/--
Definition of `CovBy` / `CovBy` 的定义

English:
definition CovBy
  signature: {α : Type*} [LT α] (a b : α)
  body: a < b ∧ forall ⦃c⦄, a < c -> ¬c < b

to_dual_insert_cast CovBy := by grind

@[inherit_doc]
infixl:50 " ⋖ " => CovBy

中文:
定义 CovBy
  签名: {α : 类型} [LT α] (a b : α)
  定义体: a < b ∧ forall ⦃c⦄, a < c -> ¬c < b

to_dual_insert_cast CovBy := by grind

@[inherit_doc]
infixl:50 " ⋖ " => CovBy
-/
def CovBy {α : Type*} [LT α] (a b : α) : Prop :=
  a < b ∧ forall ⦃c⦄, a < c -> ¬c < b

to_dual_insert_cast CovBy := by grind

@[inherit_doc]
infixl:50 " ⋖ " => CovBy

end Preorder

section PartialOrder

/-!
### Definition of `PartialOrder` and lemmas about types with a partial order
-/

/--
Definition of `PartialOrder` / `PartialOrder` 的定义

English:
class PartialOrder
  parameters: (α : Type*)
  extends: Preorder α
  axioms and operations (1):
    - le_antisymm : forall a b : α, a <= b -> b <= a -> a = b

中文:
类 偏序
  参数: (α : 类型)
  继承: 预序 α
  公理与运算 (1 个):
    - le_antisymm : 对任意 a b : α, a <= b -> b <= a -> a = b

Depends on / 依赖: PartialOrder, PartialOrder.mk, le_antisymm
-/
class PartialOrder (α : Type*) extends Preorder α where
  protected le_antisymm : forall a b : α, a <= b -> b <= a -> a = b

attribute [to_dual self (reorder := le_antisymm (3 4))] PartialOrder.mk

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PartialOrder
  signature: α] : Std.IsPartialOrder α where
  body: PartialOrder.le_antisymm

中文:
实例 [偏序
  签名: α] : Std.是偏序 α where
  定义体: PartialOrder.le_antisymm

Depends on / 依赖: PartialOrder, PartialOrder.le_antisymm, le_antisymm
-/
instance [PartialOrder α] : Std.IsPartialOrder α where
  le_antisymm := PartialOrder.le_antisymm

variable [PartialOrder α] {a b : α}

/--
lemma `le_antisymm` / 引理 `le_antisymm`

English:
lemma le_antisymm
  statement: a <= b -> b <= a -> a = b
  proof: PartialOrder.le_antisymm _ _

@[to_dual existing le_antisymm]

中文:
引理 le_antisymm
  结论: a <= b -> b <= a -> a = b
  证明: PartialOrder.le_antisymm _ _

@[to_dual existing le_antisymm]

Depends on / 依赖: PartialOrder, PartialOrder.le_antisymm, le_antisymm
-/
lemma le_antisymm : a <= b -> b <= a -> a = b := PartialOrder.le_antisymm _ _

@[to_dual existing le_antisymm]
/--
lemma `ge_antisymm` / 引理 `ge_antisymm`

English:
lemma ge_antisymm
  statement: b <= a -> a <= b -> a = b
  proof: flip le_antisymm

@[to_dual eq_of_ge_of_le]
alias eq_of_le_of_ge := le_antisymm

@[to_dual ge_antisymm_iff]

中文:
引理 ge_antisymm
  结论: b <= a -> a <= b -> a = b
  证明: flip le_antisymm

@[to_dual eq_of_ge_of_le]
alias eq_of_le_of_ge := le_antisymm

@[to_dual ge_antisymm_iff]

Depends on / 依赖: le_antisymm
-/
lemma ge_antisymm : b <= a -> a <= b -> a = b := flip le_antisymm

@[to_dual eq_of_ge_of_le]
alias eq_of_le_of_ge := le_antisymm

@[to_dual ge_antisymm_iff]
/--
lemma `le_antisymm_iff` / 引理 `le_antisymm_iff`

English:
lemma le_antisymm_iff
  statement: a = b ↔ a <= b ∧ b <= a
  proof: ⟨fun e => ⟨le_of_eq e, le_of_eq e.symm⟩, fun ⟨h1, h2⟩ => le_antisymm h1 h2⟩

@[to_dual lt_of_le_of_ne']

中文:
引理 le_antisymm_iff
  结论: a = b ↔ a <= b ∧ b <= a
  证明: ⟨fun e => ⟨le_of_eq e, le_of_eq e.symm⟩, fun ⟨h1, h2⟩ => le_antisymm h1 h2⟩

@[to_dual lt_of_le_of_ne']

Depends on / 依赖: e.symm, le_antisymm, le_of_eq
-/
lemma le_antisymm_iff : a = b ↔ a <= b ∧ b <= a :=
  ⟨fun e => ⟨le_of_eq e, le_of_eq e.symm⟩, fun ⟨h1, h2⟩ => le_antisymm h1 h2⟩

@[to_dual lt_of_le_of_ne']
/--
lemma `lt_of_le_of_ne` / 引理 `lt_of_le_of_ne`

English:
lemma lt_of_le_of_ne
  statement: a <= b -> a != b -> a < b
  proof: fun h₁ h₂ =>
lt_of_le_not_ge h₁ mt (le_antisymm h₁) h₂

@[to_dual lt_of_ne_of_le']

中文:
引理 lt_of_le_of_ne
  结论: a <= b -> a != b -> a < b
  证明: fun h₁ h₂ =>
lt_of_le_not_ge h₁ mt (le_antisymm h₁) h₂

@[to_dual lt_of_ne_of_le']
-/
lemma lt_of_le_of_ne : a <= b -> a != b -> a < b := fun h₁ h₂ =>
lt_of_le_not_ge h₁ mt (le_antisymm h₁) h₂

@[to_dual lt_of_ne_of_le']
/--
lemma `lt_of_ne_of_le` / 引理 `lt_of_ne_of_le`

English:
lemma lt_of_ne_of_le
  statement: a != b -> a <= b -> a < b
  proof: flip lt_of_le_of_ne

中文:
引理 lt_of_ne_of_le
  结论: a != b -> a <= b -> a < b
  证明: flip lt_of_le_of_ne

Depends on / 依赖: lt_of_le_of_ne
-/
lemma lt_of_ne_of_le : a != b -> a <= b -> a < b := flip lt_of_le_of_ne

/--
Definition of `decidableEqOfDecidableLE` / `decidableEqOfDecidableLE` 的定义

English:
definition decidableEqOfDecidableLE
  signature: [DecidableLE α]

中文:
定义 decidableEqOfDecidableLE
  签名: [DecidableLE α]
-/
def decidableEqOfDecidableLE [DecidableLE α] : DecidableEq α
  | a, b =>
    if hab : a <= b then
      if hba : b <= a then isTrue (le_antisymm hab hba) else isFalse fun heq => hba (heq ▸ le_refl _)
    else isFalse fun heq => hab (heq ▸ le_refl _)

-- See Note [decidable namespace]
@[to_dual Decidable.lt_or_eq_of_le']
/--
lemma `Decidable.lt_or_eq_of_le` / 引理 `Decidable.lt_or_eq_of_le`

English:
lemma Decidable.lt_or_eq_of_le
  given: [DecidableLE α] (hab : a <= b)
  statement: a < b ∨ a = b
  proof: if hba : b <= a then Or.inr (le_antisymm hab hba) else Or.inl (lt_of_le_not_ge hab hba)

@[to_dual Decidable.le_iff_lt_or_eq']

中文:
引理 可判定.lt_or_eq_of_le
  条件: [DecidableLE α] (hab : a <= b)
  结论: a < b ∨ a = b
  证明: if hba : b <= a then Or.inr (le_antisymm hab hba) else Or.inl (lt_of_le_not_ge hab hba)

@[to_dual Decidable.le_iff_lt_or_eq']

Depends on / 依赖: CommRing, CommRing.orzechProperty, orzechProperty
-/
protected lemma Decidable.lt_or_eq_of_le [DecidableLE α] (hab : a <= b) : a < b ∨ a = b :=
  if hba : b <= a then Or.inr (le_antisymm hab hba) else Or.inl (lt_of_le_not_ge hab hba)

@[to_dual Decidable.le_iff_lt_or_eq']
/--
lemma `Decidable.le_iff_lt_or_eq` / 引理 `Decidable.le_iff_lt_or_eq`

English:
lemma Decidable.le_iff_lt_or_eq
  given: [DecidableLE α]
  statement: a <= b ↔ a < b ∨ a = b
  proof: ⟨Decidable.lt_or_eq_of_le, le_of_lt_or_eq⟩

@[to_dual lt_or_eq_of_le']

中文:
引理 可判定.le_iff_lt_or_eq
  条件: [DecidableLE α]
  结论: a <= b ↔ a < b ∨ a = b
  证明: ⟨Decidable.lt_or_eq_of_le, le_of_lt_or_eq⟩

@[to_dual lt_or_eq_of_le']
-/
protected lemma Decidable.le_iff_lt_or_eq [DecidableLE α] : a <= b ↔ a < b ∨ a = b :=
  ⟨Decidable.lt_or_eq_of_le, le_of_lt_or_eq⟩

@[to_dual lt_or_eq_of_le']
/--
lemma `lt_or_eq_of_le` / 引理 `lt_or_eq_of_le`

English:
lemma lt_or_eq_of_le
  statement: a <= b -> a < b ∨ a = b
  proof: open scoped Classical in Decidable.lt_or_eq_of_le
@[to_dual le_iff_lt_or_eq']

中文:
引理 lt_or_eq_of_le
  结论: a <= b -> a < b ∨ a = b
  证明: open scoped Classical in Decidable.lt_or_eq_of_le
@[to_dual le_iff_lt_or_eq']

Depends on / 依赖: Classical, Decidable, Decidable.lt_or_eq_of_le, lt_or_eq_of_le, scoped
-/
lemma lt_or_eq_of_le : a <= b -> a < b ∨ a = b := open scoped Classical in Decidable.lt_or_eq_of_le
@[to_dual le_iff_lt_or_eq']
/--
lemma `le_iff_lt_or_eq` / 引理 `le_iff_lt_or_eq`

English:
lemma le_iff_lt_or_eq
  statement: a <= b ↔ a < b ∨ a = b
  proof: open scoped Classical in Decidable.le_iff_lt_or_eq

中文:
引理 le_iff_lt_or_eq
  结论: a <= b ↔ a < b ∨ a = b
  证明: open scoped Classical in Decidable.le_iff_lt_or_eq

Depends on / 依赖: Classical, Decidable, Decidable.le_iff_lt_or_eq, le_iff_lt_or_eq, scoped
-/
lemma le_iff_lt_or_eq : a <= b ↔ a < b ∨ a = b := open scoped Classical in Decidable.le_iff_lt_or_eq

end PartialOrder
