/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
module

public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Tactic.DeriveFintype -- shake: keep (deriving handlers not tracked yet)
public import Mathlib.Data.Multiset.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Int.Defs

/-!
# Sign type

This file defines the type of signs $\{-1, 0, 1\}$ and its basic arithmetic instances.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false in
-- Don't generate unnecessary `sizeOf_spec` lemmas which the `simpNF` linter will complain about.
set_option genSizeOfSpec false in
/--
Inductive type `SignType` / 归纳类型 `SignType`

English:
inductive SignType
  constructors (3):
    - zero: 
    - neg: 
    - pos: 

中文:
归纳类型 SignType
  构造子 (3 个):
    - zero: 
    - neg: 
    - pos: 
-/
inductive SignType
  | zero
  | neg
  | pos
  deriving DecidableEq, Inhabited, Fintype

namespace SignType

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero SignType
  body: ⟨zero⟩

中文:
实例 :
  签名: Zero SignType
  定义体: ⟨zero⟩
-/
instance : Zero SignType :=
  ⟨zero⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One SignType
  body: ⟨pos⟩

中文:
实例 :
  签名: One SignType
  定义体: ⟨pos⟩
-/
instance : One SignType :=
  ⟨pos⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg SignType
  body: ⟨fun s =>
    match s with
    | neg => pos
    | zero => zero
    | pos => neg⟩

@[simp]

中文:
实例 :
  签名: Neg SignType
  定义体: ⟨fun s =>
    match s with
    | neg => pos
    | zero => zero
    | pos => neg⟩

@[simp]
-/
instance : Neg SignType :=
  ⟨fun s =>
    match s with
    | neg => pos
    | zero => zero
    | pos => neg⟩

@[simp]
/--
theorem `zero_eq_zero` / 定理 `zero_eq_zero`

English:
theorem zero_eq_zero
  statement: zero = 0
  proof: rfl

@[simp]

中文:
定理 zero_eq_zero
  结论: zero = 0
  证明: rfl

@[simp]
-/
theorem zero_eq_zero : zero = 0 :=
  rfl

@[simp]
/--
theorem `neg_eq_neg_one` / 定理 `neg_eq_neg_one`

English:
theorem neg_eq_neg_one
  statement: neg = -1
  proof: rfl

@[simp]

中文:
定理 neg_eq_neg_one
  结论: neg = -1
  证明: rfl

@[simp]
-/
theorem neg_eq_neg_one : neg = -1 :=
  rfl

@[simp]
/--
theorem `pos_eq_one` / 定理 `pos_eq_one`

English:
theorem pos_eq_one
  statement: pos = 1
  proof: rfl

中文:
定理 pos_eq_one
  结论: pos = 1
  证明: rfl
-/
theorem pos_eq_one : pos = 1 :=
  rfl

/--
theorem `trichotomy` / 定理 `trichotomy`

English:
theorem trichotomy
  given: (a : SignType)
  statement: a = -1 ∨ a = 0 ∨ a = 1
  proof: by
  cases a <;> simp

中文:
定理 trichotomy
  条件: (a : SignType)
  结论: a = -1 ∨ a = 0 ∨ a = 1
  证明: by
  cases a <;> simp
-/
theorem trichotomy (a : SignType) : a = -1 ∨ a = 0 ∨ a = 1 := by
  cases a <;> simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul SignType
  body: ⟨fun x y =>
    match x with
    | neg => -y
    | zero => zero
    | pos => y⟩

中文:
实例 :
  签名: Mul SignType
  定义体: ⟨fun x y =>
    match x with
    | neg => -y
    | zero => zero
    | pos => y⟩

Depends on / 依赖: upperCentralSeriesAux
-/
instance : Mul SignType :=
  ⟨fun x y =>
    match x with
    | neg => -y
    | zero => zero
    | pos => y⟩

/--
Inductive type `LE` / 归纳类型 `LE`

English:
inductive LE
  parameters: : SignType -> SignType -> Prop
  constructors (3):
    - of_neg: (a) : SignType.LE neg a
    - zero: SignType.LE zero zero
    - of_pos: (a) : SignType.LE a pos

中文:
归纳类型 LE
  参数: : SignType -> SignType -> 命题
  构造子 (3 个):
    - of_neg: (a) : SignType.LE neg a
    - zero: SignType.LE zero zero
    - of_pos: (a) : SignType.LE a pos
-/
protected inductive LE : SignType -> SignType -> Prop
  | of_neg (a) : SignType.LE neg a
  | zero : SignType.LE zero zero
  | of_pos (a) : SignType.LE a pos

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LE SignType
  body: ⟨SignType.LE⟩

中文:
实例 :
  签名: LE SignType
  定义体: ⟨SignType.LE⟩

Depends on / 依赖: SignType, SignType.LE
-/
instance : LE SignType :=
  ⟨SignType.LE⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DecidableLE SignType
  body: fun a b => by
  cases a <;> cases b <;> first | exact isTrue (by constructor) | exact isFalse (by rintro ⟨_⟩)

中文:
实例 :
  签名: DecidableLE SignType
  定义体: fun a b => by
  cases a <;> cases b <;> first | exact isTrue (by constructor) | exact isFalse (by rintro ⟨_⟩)

Depends on / 依赖: isFalse, isTrue
-/
instance : DecidableLE SignType := fun a b => by
  cases a <;> cases b <;> first | exact isTrue (by constructor) | exact isFalse (by rintro ⟨_⟩)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommGroupWithZero SignType
  body: id
  mul_zero a := by cases a <;> rfl
  zero_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl
  one_mul a := by cases a <;> rfl
  mul_inv_cancel a ha := by cases a <;> trivial
  mul_comm := by decide
  mul_assoc := by decide
  exists_pair_ne := ⟨0, 1, by rintro ⟨_⟩⟩
  inv_zero := rfl

中文:
实例 :
  签名: CommGroupWithZero SignType
  定义体: id
  mul_zero a := by cases a <;> rfl
  zero_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl
  one_mul a := by cases a <;> rfl
  mul_inv_cancel a ha := by cases a <;> trivial
  mul_comm := by decide
  mul_assoc := by decide
  exists_pair_ne := ⟨0, 1, by rintro ⟨_⟩⟩
  inv_zero := rfl
-/
instance : CommGroupWithZero SignType where
  inv := id
  mul_zero a := by cases a <;> rfl
  zero_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl
  one_mul a := by cases a <;> rfl
  mul_inv_cancel a ha := by cases a <;> trivial
  mul_comm := by decide
  mul_assoc := by decide
  exists_pair_ne := ⟨0, 1, by rintro ⟨_⟩⟩
  inv_zero := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LinearOrder SignType
  body: by cases a <;> constructor
  le_total := by decide
  le_antisymm := by decide
  le_trans := by decide
  toDecidableLE := instDecidableLE

中文:
实例 :
  签名: LinearOrder SignType
  定义体: by cases a <;> constructor
  le_total := by decide
  le_antisymm := by decide
  le_trans := by decide
  toDecidableLE := instDecidableLE

Depends on / 依赖: instDecidableLE, le_antisymm, le_total, le_trans, toDecidableLE
-/
instance : LinearOrder SignType where
  le_refl a := by cases a <;> constructor
  le_total := by decide
  le_antisymm := by decide
  le_trans := by decide
  toDecidableLE := instDecidableLE

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BoundedOrder SignType
  body: 1
  le_top := LE.of_pos
  bot := -1
  bot_le :=
    #adaptation_note /-- https://github.com/leanprover/lean4/pull/6053
    Added `by exact`, but don't understand why it was needed. -/
    LE.of_neg

中文:
实例 :
  签名: BoundedOrder SignType
  定义体: 1
  le_top := LE.of_pos
  bot := -1
  bot_le :=
    #adaptation_note /-- https://github.com/leanprover/lean4/pull/6053
    Added `by exact`, but don't understand why it was needed. -/
    LE.of_neg

Depends on / 依赖: Group.IsNilpotent.nilpotent, IsNilpotent, nilpotent
-/
instance : BoundedOrder SignType where
  top := 1
  le_top := LE.of_pos
  bot := -1
  bot_le :=
    #adaptation_note /-- https://github.com/leanprover/lean4/pull/6053
    Added `by exact`, but don't understand why it was needed. -/
    LE.of_neg

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasDistribNeg SignType
  body: by rintro ⟨_⟩ <;> rfl
  neg_mul := by rintro ⟨_⟩ ⟨_⟩ <;> rfl
  mul_neg := by rintro ⟨_⟩ ⟨_⟩ <;> rfl

中文:
实例 :
  签名: HasDistribNeg SignType
  定义体: by rintro ⟨_⟩ <;> rfl
  neg_mul := by rintro ⟨_⟩ ⟨_⟩ <;> rfl
  mul_neg := by rintro ⟨_⟩ ⟨_⟩ <;> rfl

Depends on / 依赖: mul_neg, neg_mul
-/
instance : HasDistribNeg SignType where
  neg_neg := by rintro ⟨_⟩ <;> rfl
  neg_mul := by rintro ⟨_⟩ ⟨_⟩ <;> rfl
  mul_neg := by rintro ⟨_⟩ ⟨_⟩ <;> rfl

/--
Definition of `fin3Equiv` / `fin3Equiv` 的定义

English:
definition fin3Equiv
  signature: : SignType ≃* Fin 3 where
  body: match a with
    | 0 => ⟨0, by simp⟩
    | 1 => ⟨1, by simp⟩
    | -1 => ⟨2, by simp⟩
  invFun a :=
    match a with
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 1
    | ⟨2, _⟩ => -1
  left_inv a := by cases a <;> rfl
  right_inv a :=
    match a with
    | ⟨0, _⟩ => by simp
    | ⟨1, _⟩ => by simp
    | ⟨2, _

中文:
定义 fin3Equiv
  签名: : SignType ≃* Fin 3 where
  定义体: match a with
    | 0 => ⟨0, by simp⟩
    | 1 => ⟨1, by simp⟩
    | -1 => ⟨2, by simp⟩
  invFun a :=
    match a with
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 1
    | ⟨2, _⟩ => -1
  left_inv a := by cases a <;> rfl
  right_inv a :=
    match a with
    | ⟨0, _⟩ => by simp
    | ⟨1, _⟩ => by simp
    | ⟨2, _

Depends on / 依赖: invFun, left_inv, map_mul, right_inv
-/
def fin3Equiv : SignType ≃* Fin 3 where
  toFun a :=
    match a with
    | 0 => ⟨0, by simp⟩
    | 1 => ⟨1, by simp⟩
    | -1 => ⟨2, by simp⟩
  invFun a :=
    match a with
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 1
    | ⟨2, _⟩ => -1
  left_inv a := by cases a <;> rfl
  right_inv a :=
    match a with
    | ⟨0, _⟩ => by simp
    | ⟨1, _⟩ => by simp
    | ⟨2, _⟩ => by simp
  map_mul' a b := by
    cases a <;> cases b <;> rfl

section CaseBashing

/--
theorem `nonneg_iff` / 定理 `nonneg_iff`

English:
theorem nonneg_iff
  given: {a : SignType}
  statement: 0 <= a ↔ a = 0 ∨ a = 1
  proof: by decide +revert

中文:
定理 nonneg_iff
  条件: {a : SignType}
  结论: 0 <= a ↔ a = 0 ∨ a = 1
  证明: by decide +revert

Depends on / 依赖: revert
-/
theorem nonneg_iff {a : SignType} : 0 <= a ↔ a = 0 ∨ a = 1 := by decide +revert

/--
theorem `nonneg_iff_ne_neg_one` / 定理 `nonneg_iff_ne_neg_one`

English:
theorem nonneg_iff_ne_neg_one
  given: {a : SignType}
  statement: 0 <= a ↔ a != -1
  proof: by decide +revert

中文:
定理 nonneg_iff_ne_neg_one
  条件: {a : SignType}
  结论: 0 <= a ↔ a != -1
  证明: by decide +revert

Depends on / 依赖: revert
-/
theorem nonneg_iff_ne_neg_one {a : SignType} : 0 <= a ↔ a != -1 := by decide +revert

/--
theorem `neg_one_lt_iff` / 定理 `neg_one_lt_iff`

English:
theorem neg_one_lt_iff
  given: {a : SignType}
  statement: -1 < a ↔ 0 <= a
  proof: by decide +revert

中文:
定理 neg_one_lt_iff
  条件: {a : SignType}
  结论: -1 < a ↔ 0 <= a
  证明: by decide +revert

Depends on / 依赖: revert
-/
theorem neg_one_lt_iff {a : SignType} : -1 < a ↔ 0 <= a := by decide +revert

/--
theorem `nonpos_iff` / 定理 `nonpos_iff`

English:
theorem nonpos_iff
  given: {a : SignType}
  statement: a <= 0 ↔ a = -1 ∨ a = 0
  proof: by decide +revert

中文:
定理 nonpos_iff
  条件: {a : SignType}
  结论: a <= 0 ↔ a = -1 ∨ a = 0
  证明: by decide +revert

Depends on / 依赖: revert
-/
theorem nonpos_iff {a : SignType} : a <= 0 ↔ a = -1 ∨ a = 0 := by decide +revert

/--
theorem `nonpos_iff_ne_one` / 定理 `nonpos_iff_ne_one`

English:
theorem nonpos_iff_ne_one
  given: {a : SignType}
  statement: a <= 0 ↔ a != 1
  proof: by decide +revert

中文:
定理 nonpos_iff_ne_one
  条件: {a : SignType}
  结论: a <= 0 ↔ a != 1
  证明: by decide +revert

Depends on / 依赖: revert
-/
theorem nonpos_iff_ne_one {a : SignType} : a <= 0 ↔ a != 1 := by decide +revert

/--
theorem `lt_one_iff` / 定理 `lt_one_iff`

English:
theorem lt_one_iff
  given: {a : SignType}
  statement: a < 1 ↔ a <= 0
  proof: by decide +revert

@[simp]

中文:
定理 lt_one_iff
  条件: {a : SignType}
  结论: a < 1 ↔ a <= 0
  证明: by decide +revert

@[simp]

Depends on / 依赖: revert
-/
theorem lt_one_iff {a : SignType} : a < 1 ↔ a <= 0 := by decide +revert

@[simp]
/--
theorem `neg_iff` / 定理 `neg_iff`

English:
theorem neg_iff
  given: {a : SignType}
  statement: a < 0 ↔ a = -1
  proof: by decide +revert

@[simp]

中文:
定理 neg_iff
  条件: {a : SignType}
  结论: a < 0 ↔ a = -1
  证明: by decide +revert

@[simp]

Depends on / 依赖: revert
-/
theorem neg_iff {a : SignType} : a < 0 ↔ a = -1 := by decide +revert

@[simp]
/--
theorem `le_neg_one_iff` / 定理 `le_neg_one_iff`

English:
theorem le_neg_one_iff
  given: {a : SignType}
  statement: a <= -1 ↔ a = -1
  proof: le_bot_iff

@[simp]

中文:
定理 le_neg_one_iff
  条件: {a : SignType}
  结论: a <= -1 ↔ a = -1
  证明: le_bot_iff

@[simp]

Depends on / 依赖: le_bot_iff
-/
theorem le_neg_one_iff {a : SignType} : a <= -1 ↔ a = -1 :=
  le_bot_iff

@[simp]
/--
theorem `pos_iff` / 定理 `pos_iff`

English:
theorem pos_iff
  given: {a : SignType}
  statement: 0 < a ↔ a = 1
  proof: by decide +revert

@[simp]

中文:
定理 pos_iff
  条件: {a : SignType}
  结论: 0 < a ↔ a = 1
  证明: by decide +revert

@[simp]

Depends on / 依赖: revert
-/
theorem pos_iff {a : SignType} : 0 < a ↔ a = 1 := by decide +revert

@[simp]
/--
theorem `one_le_iff` / 定理 `one_le_iff`

English:
theorem one_le_iff
  given: {a : SignType}
  statement: 1 <= a ↔ a = 1
  proof: top_le_iff

@[simp]

中文:
定理 one_le_iff
  条件: {a : SignType}
  结论: 1 <= a ↔ a = 1
  证明: top_le_iff

@[simp]

Depends on / 依赖: top_le_iff
-/
theorem one_le_iff {a : SignType} : 1 <= a ↔ a = 1 :=
  top_le_iff

@[simp]
/--
theorem `neg_one_le` / 定理 `neg_one_le`

English:
theorem neg_one_le
  given: (a : SignType)
  statement: -1 <= a
  proof: bot_le

@[simp]

中文:
定理 neg_one_le
  条件: (a : SignType)
  结论: -1 <= a
  证明: bot_le

@[simp]

Depends on / 依赖: bot_le
-/
theorem neg_one_le (a : SignType) : -1 <= a :=
  bot_le

@[simp]
/--
theorem `le_one` / 定理 `le_one`

English:
theorem le_one
  given: (a : SignType)
  statement: a <= 1
  proof: le_top

@[simp]

中文:
定理 le_one
  条件: (a : SignType)
  结论: a <= 1
  证明: le_top

@[simp]

Depends on / 依赖: le_top
-/
theorem le_one (a : SignType) : a <= 1 :=
  le_top

@[simp]
/--
theorem `not_lt_neg_one` / 定理 `not_lt_neg_one`

English:
theorem not_lt_neg_one
  given: (a : SignType)
  statement: ¬a < -1
  proof: not_lt_bot

@[simp]

中文:
定理 not_lt_neg_one
  条件: (a : SignType)
  结论: ¬a < -1
  证明: not_lt_bot

@[simp]

Depends on / 依赖: not_lt_bot
-/
theorem not_lt_neg_one (a : SignType) : ¬a < -1 :=
  not_lt_bot

@[simp]
/--
theorem `not_one_lt` / 定理 `not_one_lt`

English:
theorem not_one_lt
  given: (a : SignType)
  statement: ¬1 < a
  proof: not_top_lt

@[simp]

中文:
定理 not_one_lt
  条件: (a : SignType)
  结论: ¬1 < a
  证明: not_top_lt

@[simp]

Depends on / 依赖: not_top_lt
-/
theorem not_one_lt (a : SignType) : ¬1 < a :=
  not_top_lt

@[simp]
/--
theorem `self_eq_neg_iff` / 定理 `self_eq_neg_iff`

English:
theorem self_eq_neg_iff
  given: {a : SignType}
  statement: a = -a ↔ a = 0
  proof: by decide +revert

@[simp]

中文:
定理 self_eq_neg_iff
  条件: {a : SignType}
  结论: a = -a ↔ a = 0
  证明: by decide +revert

@[simp]

Depends on / 依赖: revert
-/
theorem self_eq_neg_iff {a : SignType} : a = -a ↔ a = 0 := by decide +revert

@[simp]
/--
theorem `neg_eq_self_iff` / 定理 `neg_eq_self_iff`

English:
theorem neg_eq_self_iff
  given: {a : SignType}
  statement: -a = a ↔ a = 0
  proof: by decide +revert

@[simp]

中文:
定理 neg_eq_self_iff
  条件: {a : SignType}
  结论: -a = a ↔ a = 0
  证明: by decide +revert

@[simp]

Depends on / 依赖: revert
-/
theorem neg_eq_self_iff {a : SignType} : -a = a ↔ a = 0 := by decide +revert

@[simp]
/--
theorem `neg_eq_zero_iff` / 定理 `neg_eq_zero_iff`

English:
theorem neg_eq_zero_iff
  given: {a : SignType}
  statement: -a = 0 ↔ a = 0
  proof: by decide +revert

@[simp]

中文:
定理 neg_eq_zero_iff
  条件: {a : SignType}
  结论: -a = 0 ↔ a = 0
  证明: by decide +revert

@[simp]

Depends on / 依赖: revert
-/
theorem neg_eq_zero_iff {a : SignType} : -a = 0 ↔ a = 0 := by decide +revert

@[simp]
/--
theorem `neg_one_lt_one` / 定理 `neg_one_lt_one`

English:
theorem neg_one_lt_one
  statement: (-1 : SignType) < 1
  proof: bot_lt_top

@[simp]

中文:
定理 neg_one_lt_one
  结论: (-1 : SignType) < 1
  证明: bot_lt_top

@[simp]

Depends on / 依赖: bot_lt_top
-/
theorem neg_one_lt_one : (-1 : SignType) < 1 :=
  bot_lt_top

@[simp]
/--
theorem `neg_le_neg_iff` / 定理 `neg_le_neg_iff`

English:
theorem neg_le_neg_iff
  given: {a b : SignType}
  statement: -a <= -b ↔ b <= a
  proof: by decide +revert

@[simp]

中文:
定理 neg_le_neg_iff
  条件: {a b : SignType}
  结论: -a <= -b ↔ b <= a
  证明: by decide +revert

@[simp]
-/
protected theorem neg_le_neg_iff {a b : SignType} : -a <= -b ↔ b <= a := by decide +revert

@[simp]
/--
theorem `neg_lt_neg_iff` / 定理 `neg_lt_neg_iff`

English:
theorem neg_lt_neg_iff
  given: {a b : SignType}
  statement: -a < -b ↔ b < a
  proof: by decide +revert

中文:
定理 neg_lt_neg_iff
  条件: {a b : SignType}
  结论: -a < -b ↔ b < a
  证明: by decide +revert
-/
protected theorem neg_lt_neg_iff {a b : SignType} : -a < -b ↔ b < a := by decide +revert

end CaseBashing

section cast

variable {α : Type*} [Zero α] [One α] [Neg α]

/-- Turn a `SignType` into zero, one, or minus one. This is a coercion instance. -/
@[coe]
/--
Definition of `cast` / `cast` 的定义

English:
definition cast
  signature: : SignType -> α

中文:
定义 cast
  签名: : SignType -> α
-/
def cast : SignType -> α
  | zero => 0
  | pos => 1
  | neg => -1

/--
This can't be a `CoeTail` or `Coe` instance because we don't want it to fire when `SignType` isn't
involved in the coercion (or `CoeHead` or `CoeOut` because of `outParam`s). The only other
user-exposed option is `CoeDep` then, which allows us to match on both given and expected type.
-/
instance (s : SignType) : CoeDep SignType s α :=
  ⟨cast s⟩

/--
lemma `map_cast'` / 引理 `map_cast'`

English:
lemma map_cast'
  statement: {β : Type*} [One β] [Neg β] [Zero β]
  proof: by
  cases s <;> simp only [SignType.cast, h₁, h₂, h₃]

中文:
引理 map_cast'
  结论: {β : 类型} [One β] [Neg β] [Zero β]
  证明: by
  cases s <;> simp only [SignType.cast, h₁, h₂, h₃]

Depends on / 依赖: SignType, SignType.cast
-/
lemma map_cast' {β : Type*} [One β] [Neg β] [Zero β]
    (f : α -> β) (h₁ : f 1 = 1) (h₂ : f 0 = 0) (h₃ : f (-1) = -1) (s : SignType) :
    f s = s := by
  cases s <;> simp only [SignType.cast, h₁, h₂, h₃]

/--
lemma `map_cast` / 引理 `map_cast`

English:
lemma map_cast
  statement: {α β F : Type*} [AddGroupWithOne α] [One β] [SubtractionMonoid β]
  proof: by
  apply map_cast' <;> simp

@[simp]

中文:
引理 map_cast
  结论: {α β F : 类型} [AddGroupWithOne α] [One β] [SubtractionMonoid β]
  证明: by
  apply map_cast' <;> simp

@[simp]

Depends on / 依赖: map_cast
-/
lemma map_cast {α β F : Type*} [AddGroupWithOne α] [One β] [SubtractionMonoid β]
    [FunLike F α β] [AddMonoidHomClass F α β] [OneHomClass F α β] (f : F) (s : SignType) :
    f s = s := by
  apply map_cast' <;> simp

@[simp]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ↑(0 : SignType) = (0 : α)
  proof: rfl

@[simp]

中文:
定理 coe_zero
  结论: ↑(0 : SignType) = (0 : α)
  证明: rfl

@[simp]
-/
theorem coe_zero : ↑(0 : SignType) = (0 : α) :=
  rfl

@[simp]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ↑(1 : SignType) = (1 : α)
  proof: rfl

@[simp]

中文:
定理 coe_one
  结论: ↑(1 : SignType) = (1 : α)
  证明: rfl

@[simp]
-/
theorem coe_one : ↑(1 : SignType) = (1 : α) :=
  rfl

@[simp]
/--
theorem `coe_neg_one` / 定理 `coe_neg_one`

English:
theorem coe_neg_one
  statement: ↑(-1 : SignType) = (-1 : α)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_neg_one
  结论: ↑(-1 : SignType) = (-1 : α)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_neg_one : ↑(-1 : SignType) = (-1 : α) :=
  rfl

@[simp, norm_cast]
/--
lemma `coe_neg` / 引理 `coe_neg`

English:
lemma coe_neg
  given: {α : Type*} [One α] [SubtractionMonoid α] (s : SignType)
  proof: by
  cases s <;> simp

中文:
引理 coe_neg
  条件: {α : 类型} [One α] [SubtractionMonoid α] (s : SignType)
  证明: by
  cases s <;> simp
-/
lemma coe_neg {α : Type*} [One α] [SubtractionMonoid α] (s : SignType) :
    (↑(-s) : α) = -↑s := by
  cases s <;> simp

end cast

end SignType

variable {α : Type*}

open SignType

section Preorder

variable [Zero α] [Preorder α] [DecidableLT α] {a : α}

/--
Definition of `SignType.sign` / `SignType.sign` 的定义

English:
definition SignType.sign
  signature: : α ->o SignType
  body: ⟨fun a => if 0 < a then 1 else if a < 0 then -1 else 0, fun a b h => by
    dsimp
    split_ifs with h₁ h₂ h₃ h₄ _ _ h₂ h₃ <;> try constructor
    · cases lt_irrefl 0 (h₁.trans <| h.trans_lt h₃)
    · cases h₂ (h₁.trans_le h)
    · cases h₄ (h.trans_lt h₃)⟩

中文:
定义 SignType.sign
  签名: : α ->o SignType
  定义体: ⟨fun a => if 0 < a then 1 else if a < 0 then -1 else 0, fun a b h => by
    dsimp
    split_ifs with h₁ h₂ h₃ h₄ _ _ h₂ h₃ <;> try constructor
    · cases lt_irrefl 0 (h₁.trans <| h.trans_lt h₃)
    · cases h₂ (h₁.trans_le h)
    · cases h₄ (h.trans_lt h₃)⟩

Depends on / 依赖: h.trans_lt, lt_irrefl, split_ifs, trans_le, trans_lt
-/
def SignType.sign : α ->o SignType :=
  ⟨fun a => if 0 < a then 1 else if a < 0 then -1 else 0, fun a b h => by
    dsimp
    split_ifs with h₁ h₂ h₃ h₄ _ _ h₂ h₃ <;> try constructor
    · cases lt_irrefl 0 (h₁.trans <| h.trans_lt h₃)
    · cases h₂ (h₁.trans_le h)
    · cases h₄ (h.trans_lt h₃)⟩

/--
theorem `sign_apply` / 定理 `sign_apply`

English:
theorem sign_apply
  statement: sign a = ite (0 < a) 1 (ite (a < 0) (-1) 0)
  proof: rfl

@[simp]

中文:
定理 sign_apply
  结论: sign a = ite (0 < a) 1 (ite (a < 0) (-1) 0)
  证明: rfl

@[simp]
-/
theorem sign_apply : sign a = ite (0 < a) 1 (ite (a < 0) (-1) 0) :=
  rfl

@[simp]
/--
theorem `sign_zero` / 定理 `sign_zero`

English:
theorem sign_zero
  statement: sign (0 : α) = 0
  proof: by simp [sign_apply]

@[simp]

中文:
定理 sign_zero
  结论: sign (0 : α) = 0
  证明: by simp [sign_apply]

@[simp]

Depends on / 依赖: sign_apply
-/
theorem sign_zero : sign (0 : α) = 0 := by simp [sign_apply]

@[simp]
/--
theorem `sign_pos` / 定理 `sign_pos`

English:
theorem sign_pos
  given: (ha : 0 < a)
  statement: sign a = 1
  proof: by rwa [sign_apply, if_pos]

@[simp]

中文:
定理 sign_pos
  条件: (ha : 0 < a)
  结论: sign a = 1
  证明: by rwa [sign_apply, if_pos]

@[simp]

Depends on / 依赖: if_pos, sign_apply
-/
theorem sign_pos (ha : 0 < a) : sign a = 1 := by rwa [sign_apply, if_pos]

@[simp]
/--
theorem `sign_neg` / 定理 `sign_neg`

English:
theorem sign_neg
  given: (ha : a < 0)
  statement: sign a = -1
  proof: by rwa [sign_apply, if_neg <| asymm ha, if_pos]

中文:
定理 sign_neg
  条件: (ha : a < 0)
  结论: sign a = -1
  证明: by rwa [sign_apply, if_neg <| asymm ha, if_pos]

Depends on / 依赖: if_neg, if_pos, sign_apply
-/
theorem sign_neg (ha : a < 0) : sign a = -1 := by rwa [sign_apply, if_neg <| asymm ha, if_pos]

/--
theorem `sign_eq_one_iff` / 定理 `sign_eq_one_iff`

English:
theorem sign_eq_one_iff
  statement: sign a = 1 ↔ 0 < a
  proof: by
  refine ⟨fun h => ?_, fun h => sign_pos h⟩
  by_contra hn
  rw [sign_apply]; rw [if_neg hn] at h
  split_ifs at h

中文:
定理 sign_eq_one_iff
  结论: sign a = 1 ↔ 0 < a
  证明: by
  refine ⟨fun h => ?_, fun h => sign_pos h⟩
  by_contra hn
  rw [sign_apply]; rw [if_neg hn] at h
  split_ifs at h

Depends on / 依赖: if_neg, sign_apply, sign_pos, split_ifs
-/
theorem sign_eq_one_iff : sign a = 1 ↔ 0 < a := by
  refine ⟨fun h => ?_, fun h => sign_pos h⟩
  by_contra hn
  rw [sign_apply]; rw [if_neg hn] at h
  split_ifs at h

/--
theorem `sign_eq_neg_one_iff` / 定理 `sign_eq_neg_one_iff`

English:
theorem sign_eq_neg_one_iff
  statement: sign a = -1 ↔ a < 0
  proof: by
  refine ⟨fun h => ?_, fun h => sign_neg h⟩
  rw [sign_apply] at h
  split_ifs at h
  assumption

中文:
定理 sign_eq_neg_one_iff
  结论: sign a = -1 ↔ a < 0
  证明: by
  refine ⟨fun h => ?_, fun h => sign_neg h⟩
  rw [sign_apply] at h
  split_ifs at h
  assumption

Depends on / 依赖: sign_apply, sign_neg, split_ifs
-/
theorem sign_eq_neg_one_iff : sign a = -1 ↔ a < 0 := by
  refine ⟨fun h => ?_, fun h => sign_neg h⟩
  rw [sign_apply] at h
  split_ifs at h
  assumption

end Preorder

section LinearOrder

variable [Zero α] [LinearOrder α] {a : α}

/--
lemma `StrictMono.sign_comp` / 引理 `StrictMono.sign_comp`

English:
lemma StrictMono.sign_comp
  statement: {β F : Type*} [Zero β] [Preorder β] [DecidableLT β]
  proof: by
  simp only [sign_apply, ← map_zero f, hf.lt_iff_lt]

@[simp]

中文:
引理 StrictMono.sign_comp
  结论: {β F : 类型} [Zero β] [Preorder β] [DecidableLT β]
  证明: by
  simp only [sign_apply, ← map_zero f, hf.lt_iff_lt]

@[simp]

Depends on / 依赖: hf.lt_iff_lt, lt_iff_lt, map_zero, sign_apply
-/
lemma StrictMono.sign_comp {β F : Type*} [Zero β] [Preorder β] [DecidableLT β]
    [FunLike F α β] [ZeroHomClass F α β] {f : F} (hf : StrictMono f) (a : α) :
    sign (f a) = sign a := by
  simp only [sign_apply, ← map_zero f, hf.lt_iff_lt]

@[simp]
/--
theorem `sign_eq_zero_iff` / 定理 `sign_eq_zero_iff`

English:
theorem sign_eq_zero_iff
  statement: sign a = 0 ↔ a = 0
  proof: by
  refine ⟨fun h => ?_, fun h => h.symm ▸ sign_zero⟩
  rw [sign_apply] at h
  split_ifs at h with h_1 h_2
  cases h
  exact (le_of_not_gt h_1).eq_of_not_lt h_2

中文:
定理 sign_eq_zero_iff
  结论: sign a = 0 ↔ a = 0
  证明: by
  refine ⟨fun h => ?_, fun h => h.symm ▸ sign_zero⟩
  rw [sign_apply] at h
  split_ifs at h with h_1 h_2
  cases h
  exact (le_of_not_gt h_1).eq_of_not_lt h_2

Depends on / 依赖: eq_of_not_lt, h.symm, le_of_not_gt, sign_apply, sign_zero, split_ifs
-/
theorem sign_eq_zero_iff : sign a = 0 ↔ a = 0 := by
  refine ⟨fun h => ?_, fun h => h.symm ▸ sign_zero⟩
  rw [sign_apply] at h
  split_ifs at h with h_1 h_2
  cases h
  exact (le_of_not_gt h_1).eq_of_not_lt h_2

/--
theorem `sign_ne_zero` / 定理 `sign_ne_zero`

English:
theorem sign_ne_zero
  statement: sign a != 0 ↔ a != 0
  proof: sign_eq_zero_iff.not

@[simp]

中文:
定理 sign_ne_zero
  结论: sign a != 0 ↔ a != 0
  证明: sign_eq_zero_iff.not

@[simp]

Depends on / 依赖: sign_eq_zero_iff, sign_eq_zero_iff.not
-/
theorem sign_ne_zero : sign a != 0 ↔ a != 0 :=
  sign_eq_zero_iff.not

@[simp]
/--
theorem `sign_nonneg_iff` / 定理 `sign_nonneg_iff`

English:
theorem sign_nonneg_iff
  statement: 0 <= sign a ↔ 0 <= a
  proof: by
  rcases lt_trichotomy 0 a with (h | h | h)
  · simp [h, h.le]
  · simp [← h]
  · simp [h, h.not_ge]

@[simp]

中文:
定理 sign_nonneg_iff
  结论: 0 <= sign a ↔ 0 <= a
  证明: by
  rcases lt_trichotomy 0 a with (h | h | h)
  · simp [h, h.le]
  · simp [← h]
  · simp [h, h.not_ge]

@[simp]

Depends on / 依赖: h.le, h.not_ge, lt_trichotomy, not_ge
-/
theorem sign_nonneg_iff : 0 <= sign a ↔ 0 <= a := by
  rcases lt_trichotomy 0 a with (h | h | h)
  · simp [h, h.le]
  · simp [← h]
  · simp [h, h.not_ge]

@[simp]
/--
theorem `sign_nonpos_iff` / 定理 `sign_nonpos_iff`

English:
theorem sign_nonpos_iff
  statement: sign a <= 0 ↔ a <= 0
  proof: by
  rcases lt_trichotomy 0 a with (h | h | h)
  · simp [h, h.not_ge]
  · simp [← h]
  · simp [h, h.le]

中文:
定理 sign_nonpos_iff
  结论: sign a <= 0 ↔ a <= 0
  证明: by
  rcases lt_trichotomy 0 a with (h | h | h)
  · simp [h, h.not_ge]
  · simp [← h]
  · simp [h, h.le]

Depends on / 依赖: h.le, h.not_ge, lt_trichotomy, not_ge
-/
theorem sign_nonpos_iff : sign a <= 0 ↔ a <= 0 := by
  rcases lt_trichotomy 0 a with (h | h | h)
  · simp [h, h.not_ge]
  · simp [← h]
  · simp [h, h.le]

/--
lemma `sign_eq_sign_or_eq_neg` / 引理 `sign_eq_sign_or_eq_neg`

English:
lemma sign_eq_sign_or_eq_neg
  given: {b : α} (ha : a != 0) (hb : b != 0)
  proof: by
  rcases trichotomy (sign a) with hsa | hsa | hsa <;>
    rcases trichotomy (sign b) with hsb | hsb | hsb <;>
    simp_all

中文:
引理 sign_eq_sign_or_eq_neg
  条件: {b : α} (ha : a != 0) (hb : b != 0)
  证明: by
  rcases trichotomy (sign a) with hsa | hsa | hsa <;>
    rcases trichotomy (sign b) with hsb | hsb | hsb <;>
    simp_all

Depends on / 依赖: trichotomy
-/
lemma sign_eq_sign_or_eq_neg {b : α} (ha : a != 0) (hb : b != 0) :
    sign a = sign b ∨ sign a = -sign b := by
  rcases trichotomy (sign a) with hsa | hsa | hsa <;>
    rcases trichotomy (sign b) with hsb | hsb | hsb <;>
    simp_all

end LinearOrder

section OrderedSemiring

variable [Semiring α] [PartialOrder α] [IsOrderedRing α] [DecidableLT α] [Nontrivial α]

/--
theorem `sign_one` / 定理 `sign_one`

English:
theorem sign_one
  statement: sign (1 : α) = 1
  proof: sign_pos zero_lt_one

中文:
定理 sign_one
  结论: sign (1 : α) = 1
  证明: sign_pos zero_lt_one

Depends on / 依赖: sign_pos, zero_lt_one
-/
theorem sign_one : sign (1 : α) = 1 :=
  sign_pos zero_lt_one

end OrderedSemiring

section AddGroup

variable [AddGroup α] [Preorder α] [DecidableLT α]

/--
theorem `Left.sign_neg` / 定理 `Left.sign_neg`

English:
theorem Left.sign_neg
  given: [AddLeftStrictMono α] (a : α)
  statement: sign (-a) = -sign a
  proof: by
  simp_rw [sign_apply, Left.neg_pos_iff, Left.neg_neg_iff]
  split_ifs with h h'
  · exact False.elim (lt_asymm h h')
  · simp
  · simp
  · simp

中文:
定理 Left.sign_neg
  条件: [AddLeftStrictMono α] (a : α)
  结论: sign (-a) = -sign a
  证明: by
  simp_rw [sign_apply, Left.neg_pos_iff, Left.neg_neg_iff]
  split_ifs with h h'
  · exact False.elim (lt_asymm h h')
  · simp
  · simp
  · simp

Depends on / 依赖: False.elim, Left.neg_neg_iff, Left.neg_pos_iff, Subsingleton, _root_, _root_.Group.isNilpotent_of_subsingleton, isNilpotent_of_subsingleton, lt_asymm, neg_neg_iff, neg_pos_iff, sign_apply, simp_rw, split_ifs
-/
theorem Left.sign_neg [AddLeftStrictMono α] (a : α) : sign (-a) = -sign a := by
  simp_rw [sign_apply, Left.neg_pos_iff, Left.neg_neg_iff]
  split_ifs with h h'
  · exact False.elim (lt_asymm h h')
  · simp
  · simp
  · simp

/--
theorem `Right.sign_neg` / 定理 `Right.sign_neg`

English:
theorem Right.sign_neg
  given: [AddRightStrictMono α] (a : α)
  proof: by
  simp_rw [sign_apply, Right.neg_pos_iff, Right.neg_neg_iff]
  split_ifs with h h'
  · exact False.elim (lt_asymm h h')
  · simp
  · simp
  · simp

中文:
定理 Right.sign_neg
  条件: [AddRightStrictMono α] (a : α)
  证明: by
  simp_rw [sign_apply, Right.neg_pos_iff, Right.neg_neg_iff]
  split_ifs with h h'
  · exact False.elim (lt_asymm h h')
  · simp
  · simp
  · simp

Depends on / 依赖: False.elim, Right.neg_neg_iff, Right.neg_pos_iff, lt_asymm, neg_neg_iff, neg_pos_iff, sign_apply, simp_rw, split_ifs
-/
theorem Right.sign_neg [AddRightStrictMono α] (a : α) :
    sign (-a) = -sign a := by
  simp_rw [sign_apply, Right.neg_pos_iff, Right.neg_neg_iff]
  split_ifs with h h'
  · exact False.elim (lt_asymm h h')
  · simp
  · simp
  · simp

end AddGroup

/--
theorem `Int.sign_eq_sign` / 定理 `Int.sign_eq_sign`

English:
theorem Int.sign_eq_sign
  given: (n : Int)
  statement: Int.sign n = SignType.sign n
  proof: by
  obtain (n | _) | _ := n <;> simp [sign, negSucc_lt_zero]

中文:
定理 Int.sign_eq_sign
  条件: (n : 整数)
  结论: 整数.sign n = SignType.sign n
  证明: by
  obtain (n | _) | _ := n <;> simp [sign, negSucc_lt_zero]

Depends on / 依赖: negSucc_lt_zero
-/
theorem Int.sign_eq_sign (n : Int) : Int.sign n = SignType.sign n := by
  obtain (n | _) | _ := n <;> simp [sign, negSucc_lt_zero]
