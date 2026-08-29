/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Monoid.WithTop
public import Mathlib.Algebra.Regular.Basic


/-!
# Linearly ordered commutative additive groups and monoids with a top element adjoined

This file sets up a special class of linearly ordered commutative additive monoids
that show up as the target of so-called “valuations” in algebraic number theory.

Usually, in the informal literature, these objects are constructed
by taking a linearly ordered commutative additive group Γ and formally adjoining a
top element: `Γ ∪ {⊤}`.

The disadvantage is that a type such as `ENNReal` is not of that form,
whereas it is a very common target for valuations.
The solutions is to use a typeclass, and that is exactly what we do in this file.
-/

public section

variable {G α : Type*}

/--
Definition of `LinearOrderedAddCommMonoidWithTop` / `LinearOrderedAddCommMonoidWithTop` 的定义

English:
class LinearOrderedAddCommMonoidWithTop
  parameters: (α : Type*)
  axioms and operations (2):
    - top_add' : forall x : α, ⊤ + x = ⊤
    - isAddLeftRegular_of_ne_top(⦃x) : α⦄ : x != ⊤ -> IsAddLeftRegular x

中文:
类 LinearOrderedAddCommMonoidWithTop
  参数: (α : 类型)
  公理与运算 (2 个):
    - top_add' : 对任意 x : α, ⊤ + x = ⊤
    - isAddLeftRegular_of_ne_top(⦃x) : α⦄ : x != ⊤ -> IsAddLeftRegular x
-/
class LinearOrderedAddCommMonoidWithTop (α : Type*) extends
    AddCommMonoid α, LinearOrder α, IsOrderedAddMonoid α, OrderTop α where
  /-- In a `LinearOrderedAddCommMonoidWithTop`, the `⊤` element is invariant under addition. -/
  protected top_add' : forall x : α, ⊤ + x = ⊤
  protected isAddLeftRegular_of_ne_top ⦃x : α⦄ : x != ⊤ -> IsAddLeftRegular x

-- We do not extend `LinearOrderedAddCommMonoidWithTop` as that would bring in the unnecessary
-- `isAddLeftRegular_of_ne_top` field.
/--
Definition of `LinearOrderedAddCommGroupWithTop` / `LinearOrderedAddCommGroupWithTop` 的定义

English:
class LinearOrderedAddCommGroupWithTop
  parameters: (α : Type*)
  extends: AddCommMonoid α, LinearOrder α, IsOrderedAddMonoid α, OrderTop α, SubNegMonoid α, 
  axioms and operations (3):
    - top_add'((x : α)) : ⊤ + x = ⊤
    - neg_top : -(⊤ : α) = ⊤
    - add_neg_cancel_of_ne_top(⦃x) : α⦄ : x != ⊤ -> x + -x = 0

中文:
类 LinearOrderedAddCommGroupWithTop
  参数: (α : 类型)
  继承: AddCommMonoid α, LinearOrder α, IsOrderedAddMonoid α, OrderTop α, SubNegMonoid α, 
  公理与运算 (3 个):
    - top_add'((x : α)) : ⊤ + x = ⊤
    - neg_top : -(⊤ : α) = ⊤
    - add_neg_cancel_of_ne_top(⦃x) : α⦄ : x != ⊤ -> x + -x = 0
-/
class LinearOrderedAddCommGroupWithTop (α : Type*)
    extends AddCommMonoid α, LinearOrder α, IsOrderedAddMonoid α, OrderTop α, SubNegMonoid α,
    Nontrivial α where
  /-- In a `LinearOrderedAddCommMonoidWithTop`, the `⊤` element is invariant under addition. -/
  protected top_add' (x : α) : ⊤ + x = ⊤
  neg_top : -(⊤ : α) = ⊤
  add_neg_cancel_of_ne_top ⦃x : α⦄ : x != ⊤ -> x + -x = 0

section LinearOrderedAddCommMonoidWithTop
variable [LinearOrderedAddCommMonoidWithTop α] {a b c : α}

@[simp]
/--
theorem `top_add` / 定理 `top_add`

English:
theorem top_add
  given: (a : α)
  statement: ⊤ + a = ⊤
  proof: LinearOrderedAddCommMonoidWithTop.top_add' a

@[simp]

中文:
定理 top_add
  条件: (a : α)
  结论: ⊤ + a = ⊤
  证明: LinearOrderedAddCommMonoidWithTop.top_add' a

@[simp]

Depends on / 依赖: LinearOrderedAddCommMonoidWithTop, LinearOrderedAddCommMonoidWithTop.top_add, top_add
-/
theorem top_add (a : α) : ⊤ + a = ⊤ :=
  LinearOrderedAddCommMonoidWithTop.top_add' a

@[simp]
/--
theorem `add_top` / 定理 `add_top`

English:
theorem add_top
  given: (a : α)
  statement: a + ⊤ = ⊤
  proof: Trans.trans (add_comm _ _) (top_add _)

中文:
定理 add_top
  条件: (a : α)
  结论: a + ⊤ = ⊤
  证明: Trans.trans (add_comm _ _) (top_add _)

Depends on / 依赖: Trans.trans, add_comm, top_add
-/
theorem add_top (a : α) : a + ⊤ = ⊤ :=
  Trans.trans (add_comm _ _) (top_add _)

/--
lemma `IsAddRegular.of_ne_top` / 引理 `IsAddRegular.of_ne_top`

English:
lemma IsAddRegular.of_ne_top
  given: (ha : a != ⊤)
  statement: IsAddRegular a
  proof: by
  simpa using LinearOrderedAddCommMonoidWithTop.isAddLeftRegular_of_ne_top ha

中文:
引理 IsAddRegular.of_ne_top
  条件: (ha : a != ⊤)
  结论: IsAddRegular a
  证明: by
  simpa using LinearOrderedAddCommMonoidWithTop.isAddLeftRegular_of_ne_top ha
-/
@[simp] lemma IsAddRegular.of_ne_top (ha : a != ⊤) : IsAddRegular a := by
  simpa using LinearOrderedAddCommMonoidWithTop.isAddLeftRegular_of_ne_top ha

/--
lemma `add_left_injective_of_ne_top` / 引理 `add_left_injective_of_ne_top`

English:
lemma add_left_injective_of_ne_top
  given: (b : α) (h : b != ⊤)
  statement: Function.Injective (fun x => x + b)
  proof: (IsAddRegular.of_ne_top h).2

中文:
引理 add_left_injective_of_ne_top
  条件: (b : α) (h : b != ⊤)
  结论: Function.Injective (fun x => x + b)
  证明: (IsAddRegular.of_ne_top h).2

Depends on / 依赖: IsAddRegular, IsAddRegular.of_ne_top, of_ne_top
-/
lemma add_left_injective_of_ne_top (b : α) (h : b != ⊤) : Function.Injective (fun x => x + b) :=
  (IsAddRegular.of_ne_top h).2

/--
lemma `add_right_injective_of_ne_top` / 引理 `add_right_injective_of_ne_top`

English:
lemma add_right_injective_of_ne_top
  given: (b : α) (h : b != ⊤)
  statement: Function.Injective (fun x => b + x)
  proof: (IsAddRegular.of_ne_top h).1

@[simp]

中文:
引理 add_right_injective_of_ne_top
  条件: (b : α) (h : b != ⊤)
  结论: Function.Injective (fun x => b + x)
  证明: (IsAddRegular.of_ne_top h).1

@[simp]

Depends on / 依赖: IsAddRegular, IsAddRegular.of_ne_top, of_ne_top
-/
lemma add_right_injective_of_ne_top (b : α) (h : b != ⊤) : Function.Injective (fun x => b + x) :=
  (IsAddRegular.of_ne_top h).1

@[simp]
/--
lemma `add_left_inj_of_ne_top` / 引理 `add_left_inj_of_ne_top`

English:
lemma add_left_inj_of_ne_top
  given: (h : a != ⊤)
  statement: b + a = c + a ↔ b = c
  proof: (add_left_injective_of_ne_top _ h).eq_iff

@[simp]

中文:
引理 add_left_inj_of_ne_top
  条件: (h : a != ⊤)
  结论: b + a = c + a ↔ b = c
  证明: (add_left_injective_of_ne_top _ h).eq_iff

@[simp]

Depends on / 依赖: add_left_injective_of_ne_top, eq_iff
-/
lemma add_left_inj_of_ne_top (h : a != ⊤) : b + a = c + a ↔ b = c :=
  (add_left_injective_of_ne_top _ h).eq_iff

@[simp]
/--
lemma `add_right_inj_of_ne_top` / 引理 `add_right_inj_of_ne_top`

English:
lemma add_right_inj_of_ne_top
  given: (h : a != ⊤)
  statement: a + b = a + c ↔ b = c
  proof: (add_right_injective_of_ne_top _ h).eq_iff

中文:
引理 add_right_inj_of_ne_top
  条件: (h : a != ⊤)
  结论: a + b = a + c ↔ b = c
  证明: (add_right_injective_of_ne_top _ h).eq_iff

Depends on / 依赖: add_right_injective_of_ne_top, eq_iff
-/
lemma add_right_inj_of_ne_top (h : a != ⊤) : a + b = a + c ↔ b = c :=
  (add_right_injective_of_ne_top _ h).eq_iff

/--
lemma `add_left_strictMono_of_ne_top` / 引理 `add_left_strictMono_of_ne_top`

English:
lemma add_left_strictMono_of_ne_top
  given: (h : b != ⊤)
  statement: StrictMono (fun x => x + b)
  proof: add_left_mono.strictMono_of_injective add_left_injective_of_ne_top _ h

中文:
引理 add_left_strictMono_of_ne_top
  条件: (h : b != ⊤)
  结论: StrictMono (fun x => x + b)
  证明: add_left_mono.strictMono_of_injective add_left_injective_of_ne_top _ h

Depends on / 依赖: add_left_injective_of_ne_top, add_left_mono, add_left_mono.strictMono_of_injective, strictMono_of_injective
-/
lemma add_left_strictMono_of_ne_top (h : b != ⊤) : StrictMono (fun x => x + b) :=
add_left_mono.strictMono_of_injective add_left_injective_of_ne_top _ h

/--
lemma `add_right_strictMono_of_ne_top` / 引理 `add_right_strictMono_of_ne_top`

English:
lemma add_right_strictMono_of_ne_top
  given: (h : b != ⊤)
  statement: StrictMono (fun x => b + x)
  proof: add_right_mono.strictMono_of_injective add_right_injective_of_ne_top _ h

@[simp]

中文:
引理 add_right_strictMono_of_ne_top
  条件: (h : b != ⊤)
  结论: StrictMono (fun x => b + x)
  证明: add_right_mono.strictMono_of_injective add_right_injective_of_ne_top _ h

@[simp]

Depends on / 依赖: add_right_injective_of_ne_top, add_right_mono, add_right_mono.strictMono_of_injective, strictMono_of_injective
-/
lemma add_right_strictMono_of_ne_top (h : b != ⊤) : StrictMono (fun x => b + x) :=
add_right_mono.strictMono_of_injective add_right_injective_of_ne_top _ h

@[simp]
/--
lemma `add_le_add_iff_left_of_ne_top` / 引理 `add_le_add_iff_left_of_ne_top`

English:
lemma add_le_add_iff_left_of_ne_top
  given: (h : a != ⊤)
  statement: b + a <= c + a ↔ b <= c
  proof: (add_left_strictMono_of_ne_top h).le_iff_le

@[simp]

中文:
引理 add_le_add_iff_left_of_ne_top
  条件: (h : a != ⊤)
  结论: b + a <= c + a ↔ b <= c
  证明: (add_left_strictMono_of_ne_top h).le_iff_le

@[simp]

Depends on / 依赖: add_left_strictMono_of_ne_top, le_iff_le
-/
lemma add_le_add_iff_left_of_ne_top (h : a != ⊤) : b + a <= c + a ↔ b <= c :=
  (add_left_strictMono_of_ne_top h).le_iff_le

@[simp]
/--
lemma `add_le_add_iff_right_of_ne_top` / 引理 `add_le_add_iff_right_of_ne_top`

English:
lemma add_le_add_iff_right_of_ne_top
  given: (h : a != ⊤)
  statement: a + b <= a + c ↔ b <= c
  proof: (add_right_strictMono_of_ne_top h).le_iff_le

@[simp]

中文:
引理 add_le_add_iff_right_of_ne_top
  条件: (h : a != ⊤)
  结论: a + b <= a + c ↔ b <= c
  证明: (add_right_strictMono_of_ne_top h).le_iff_le

@[simp]

Depends on / 依赖: add_right_strictMono_of_ne_top, le_iff_le
-/
lemma add_le_add_iff_right_of_ne_top (h : a != ⊤) : a + b <= a + c ↔ b <= c :=
  (add_right_strictMono_of_ne_top h).le_iff_le

@[simp]
/--
lemma `add_lt_add_iff_left_of_ne_top` / 引理 `add_lt_add_iff_left_of_ne_top`

English:
lemma add_lt_add_iff_left_of_ne_top
  given: (h : a != ⊤)
  statement: b + a < c + a ↔ b < c
  proof: (add_left_strictMono_of_ne_top h).lt_iff_lt

@[simp]

中文:
引理 add_lt_add_iff_left_of_ne_top
  条件: (h : a != ⊤)
  结论: b + a < c + a ↔ b < c
  证明: (add_left_strictMono_of_ne_top h).lt_iff_lt

@[simp]

Depends on / 依赖: add_left_strictMono_of_ne_top, lt_iff_lt
-/
lemma add_lt_add_iff_left_of_ne_top (h : a != ⊤) : b + a < c + a ↔ b < c :=
  (add_left_strictMono_of_ne_top h).lt_iff_lt

@[simp]
/--
lemma `add_lt_add_iff_right_of_ne_top` / 引理 `add_lt_add_iff_right_of_ne_top`

English:
lemma add_lt_add_iff_right_of_ne_top
  given: (h : a != ⊤)
  statement: a + b < a + c ↔ b < c
  proof: (add_right_strictMono_of_ne_top h).lt_iff_lt

中文:
引理 add_lt_add_iff_right_of_ne_top
  条件: (h : a != ⊤)
  结论: a + b < a + c ↔ b < c
  证明: (add_right_strictMono_of_ne_top h).lt_iff_lt

Depends on / 依赖: add_right_strictMono_of_ne_top, lt_iff_lt
-/
lemma add_lt_add_iff_right_of_ne_top (h : a != ⊤) : a + b < a + c ↔ b < c :=
  (add_right_strictMono_of_ne_top h).lt_iff_lt

end LinearOrderedAddCommMonoidWithTop

namespace LinearOrderedAddCommGroupWithTop

variable [LinearOrderedAddCommGroupWithTop α] {a b c : α}

attribute [simp] neg_top


/--
lemma `neg_add_cancel_of_ne_top` / 引理 `neg_add_cancel_of_ne_top`

English:
lemma neg_add_cancel_of_ne_top
  given: (ha : a != ⊤)
  statement: -a + a = 0
  proof: by
  simp [add_comm, add_neg_cancel_of_ne_top ha]

中文:
引理 neg_add_cancel_of_ne_top
  条件: (ha : a != ⊤)
  结论: -a + a = 0
  证明: by
  simp [add_comm, add_neg_cancel_of_ne_top ha]

Depends on / 依赖: add_comm, add_neg_cancel_of_ne_top
-/
lemma neg_add_cancel_of_ne_top (ha : a != ⊤) : -a + a = 0 := by
  simp [add_comm, add_neg_cancel_of_ne_top ha]

/--
lemma `add_neg_cancel_left_of_ne_top` / 引理 `add_neg_cancel_left_of_ne_top`

English:
lemma add_neg_cancel_left_of_ne_top
  given: (ha : a != ⊤) (b : α)
  statement: a + (-a + b) = b
  proof: by
  simp [← add_assoc, add_neg_cancel_of_ne_top ha]

中文:
引理 add_neg_cancel_left_of_ne_top
  条件: (ha : a != ⊤) (b : α)
  结论: a + (-a + b) = b
  证明: by
  simp [← add_assoc, add_neg_cancel_of_ne_top ha]

Depends on / 依赖: add_assoc, add_neg_cancel_of_ne_top
-/
lemma add_neg_cancel_left_of_ne_top (ha : a != ⊤) (b : α) : a + (-a + b) = b := by
  simp [← add_assoc, add_neg_cancel_of_ne_top ha]

/--
lemma `neg_add_cancel_left_of_ne_top` / 引理 `neg_add_cancel_left_of_ne_top`

English:
lemma neg_add_cancel_left_of_ne_top
  given: (ha : a != ⊤) (b : α)
  statement: -a + (a + b) = b
  proof: by
  simp [← add_assoc, neg_add_cancel_of_ne_top ha]

中文:
引理 neg_add_cancel_left_of_ne_top
  条件: (ha : a != ⊤) (b : α)
  结论: -a + (a + b) = b
  证明: by
  simp [← add_assoc, neg_add_cancel_of_ne_top ha]

Depends on / 依赖: add_assoc, neg_add_cancel_of_ne_top
-/
lemma neg_add_cancel_left_of_ne_top (ha : a != ⊤) (b : α) : -a + (a + b) = b := by
  simp [← add_assoc, neg_add_cancel_of_ne_top ha]

/--
lemma `add_neg_cancel_right_of_ne_top` / 引理 `add_neg_cancel_right_of_ne_top`

English:
lemma add_neg_cancel_right_of_ne_top
  given: (hb : b != ⊤) (a : α)
  statement: a + b + -b = a
  proof: by
  simp [add_assoc, add_neg_cancel_of_ne_top hb]

中文:
引理 add_neg_cancel_right_of_ne_top
  条件: (hb : b != ⊤) (a : α)
  结论: a + b + -b = a
  证明: by
  simp [add_assoc, add_neg_cancel_of_ne_top hb]

Depends on / 依赖: add_assoc, add_neg_cancel_of_ne_top
-/
lemma add_neg_cancel_right_of_ne_top (hb : b != ⊤) (a : α) : a + b + -b = a := by
  simp [add_assoc, add_neg_cancel_of_ne_top hb]

/--
lemma `neg_add_cancel_right_of_ne_top` / 引理 `neg_add_cancel_right_of_ne_top`

English:
lemma neg_add_cancel_right_of_ne_top
  given: (hb : b != ⊤) (a : α)
  statement: a + -b + b = a
  proof: by
  simp [add_assoc, neg_add_cancel_of_ne_top hb]

中文:
引理 neg_add_cancel_right_of_ne_top
  条件: (hb : b != ⊤) (a : α)
  结论: a + -b + b = a
  证明: by
  simp [add_assoc, neg_add_cancel_of_ne_top hb]

Depends on / 依赖: add_assoc, neg_add_cancel_of_ne_top
-/
lemma neg_add_cancel_right_of_ne_top (hb : b != ⊤) (a : α) : a + -b + b = a := by
  simp [add_assoc, neg_add_cancel_of_ne_top hb]

/--
lemma `top_ne_zero` / 引理 `top_ne_zero`

English:
lemma top_ne_zero
  statement: (⊤ : α) != 0
  proof: by
  intro h
  obtain ⟨a, ha⟩ := exists_ne (0 : α)
  rw [← zero_add a] at ha
  simp [LinearOrderedAddCommGroupWithTop.top_add', -zero_add, ← h] at ha

中文:
引理 top_ne_zero
  结论: (⊤ : α) != 0
  证明: by
  intro h
  obtain ⟨a, ha⟩ := exists_ne (0 : α)
  rw [← zero_add a] at ha
  simp [LinearOrderedAddCommGroupWithTop.top_add', -zero_add, ← h] at ha
-/
@[simp] lemma top_ne_zero : (⊤ : α) != 0 := by
  intro h
  obtain ⟨a, ha⟩ := exists_ne (0 : α)
  rw [← zero_add a] at ha
  simp [LinearOrderedAddCommGroupWithTop.top_add', -zero_add, ← h] at ha

/--
lemma `zero_ne_top` / 引理 `zero_ne_top`

English:
lemma zero_ne_top
  statement: 0 != (⊤ : α)
  proof: top_ne_zero.symm

中文:
引理 zero_ne_top
  结论: 0 != (⊤ : α)
  证明: top_ne_zero.symm
-/
@[simp] lemma zero_ne_top : 0 != (⊤ : α) := top_ne_zero.symm

/--
lemma `top_pos` / 引理 `top_pos`

English:
lemma top_pos
  statement: (0 : α) < ⊤
  proof: lt_top_iff_ne_top.2 top_ne_zero.symm

中文:
引理 top_pos
  结论: (0 : α) < ⊤
  证明: lt_top_iff_ne_top.2 top_ne_zero.symm
-/
@[simp] lemma top_pos : (0 : α) < ⊤ := lt_top_iff_ne_top.2 top_ne_zero.symm

/--
lemma `isAddUnit_iff` / 引理 `isAddUnit_iff`

English:
lemma isAddUnit_iff
  statement: IsAddUnit a ↔ a != ⊤ where
  proof: by rintro ⟨⟨b, c, hbc, -⟩, rfl⟩ rfl; simp [LinearOrderedAddCommGroupWithTop.top_add'] at hbc
mpr ha := .of_add_eq_zero (-a) by simp [ha, add_neg_cancel_of_ne_top]

中文:
引理 isAddUnit_iff
  结论: IsAddUnit a ↔ a != ⊤ where
  证明: by rintro ⟨⟨b, c, hbc, -⟩, rfl⟩ rfl; simp [LinearOrderedAddCommGroupWithTop.top_add'] at hbc
mpr ha := .of_add_eq_zero (-a) by simp [ha, add_neg_cancel_of_ne_top]
-/
@[simp] lemma isAddUnit_iff : IsAddUnit a ↔ a != ⊤ where
  mp := by rintro ⟨⟨b, c, hbc, -⟩, rfl⟩ rfl; simp [LinearOrderedAddCommGroupWithTop.top_add'] at hbc
mpr ha := .of_add_eq_zero (-a) by simp [ha, add_neg_cancel_of_ne_top]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LinearOrderedAddCommMonoidWithTop α
  body: LinearOrderedAddCommGroupWithTop.top_add'
  isAddLeftRegular_of_ne_top _a ha := (isAddUnit_iff.2 ha).isAddRegular.1

中文:
实例 :
  签名: LinearOrderedAddCommMonoidWithTop α
  定义体: LinearOrderedAddCommGroupWithTop.top_add'
  isAddLeftRegular_of_ne_top _a ha := (isAddUnit_iff.2 ha).isAddRegular.1

Depends on / 依赖: LinearOrderedAddCommGroupWithTop, LinearOrderedAddCommGroupWithTop.top_add, top_add
-/
instance : LinearOrderedAddCommMonoidWithTop α where
  top_add' := LinearOrderedAddCommGroupWithTop.top_add'
  isAddLeftRegular_of_ne_top _a ha := (isAddUnit_iff.2 ha).isAddRegular.1

/--
lemma `add_ne_top` / 引理 `add_ne_top`

English:
lemma add_ne_top
  statement: a + b != ⊤ ↔ a != ⊤ ∧ b != ⊤
  proof: by simp [← isAddUnit_iff]

中文:
引理 add_ne_top
  结论: a + b != ⊤ ↔ a != ⊤ ∧ b != ⊤
  证明: by simp [← isAddUnit_iff]

Depends on / 依赖: isAddUnit_iff
-/
lemma add_ne_top : a + b != ⊤ ↔ a != ⊤ ∧ b != ⊤ := by simp [← isAddUnit_iff]

/--
lemma `add_eq_top` / 引理 `add_eq_top`

English:
lemma add_eq_top
  statement: a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤
  proof: by
  rw [← not_iff_not]; rw [not_or]; exact add_ne_top

中文:
引理 add_eq_top
  结论: a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤
  证明: by
  rw [← not_iff_not]; rw [not_or]; exact add_ne_top
-/
@[simp] lemma add_eq_top : a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤ := by
  rw [← not_iff_not]; rw [not_or]; exact add_ne_top

/--
lemma `add_lt_top` / 引理 `add_lt_top`

English:
lemma add_lt_top
  statement: a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤
  proof: by simp [lt_top_iff_ne_top]

中文:
引理 add_lt_top
  结论: a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤
  证明: by simp [lt_top_iff_ne_top]
-/
@[simp] lemma add_lt_top : a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤ := by simp [lt_top_iff_ne_top]

/--
lemma `neg_eq_top` / 引理 `neg_eq_top`

English:
lemma neg_eq_top
  statement: -a = ⊤ ↔ a = ⊤ where
  proof: by simpa [h] using add_neg_cancel_of_ne_top (x := a)
  mpr h := by simp [h]

中文:
引理 neg_eq_top
  结论: -a = ⊤ ↔ a = ⊤ where
  证明: by simpa [h] using add_neg_cancel_of_ne_top (x := a)
  mpr h := by simp [h]
-/
@[simp] lemma neg_eq_top : -a = ⊤ ↔ a = ⊤ where
  mp h := by simpa [h] using add_neg_cancel_of_ne_top (x := a)
  mpr h := by simp [h]

/--
lemma `sub_top` / 引理 `sub_top`

English:
lemma sub_top
  statement: a - ⊤ = ⊤
  proof: by simp [sub_eq_add_neg]

中文:
引理 sub_top
  结论: a - ⊤ = ⊤
  证明: by simp [sub_eq_add_neg]
-/
@[simp] lemma sub_top : a - ⊤ = ⊤ := by simp [sub_eq_add_neg]

instance (priority := 100) toSubtractionMonoid : SubtractionMonoid α where
  neg_neg a := by
    obtain rfl | ha := eq_or_ne a ⊤
    · simp
    · apply left_neg_eq_right_neg (a := -a) <;> simp [add_comm, add_neg_cancel_of_ne_top, ha]
  neg_add_rev a b := by
    obtain rfl | ha := eq_or_ne a ⊤
    · simp
    obtain rfl | hb := eq_or_ne b ⊤
    · simp
    · exact left_neg_eq_right_neg (a := a + b) (by simp [neg_add_cancel_of_ne_top, *])
        (by simp [add_assoc, add_neg_cancel_of_ne_top, add_neg_cancel_left_of_ne_top, *])
  neg_eq_of_add a b h := by
    have ha : a != ⊤ := by rintro rfl; simp at h
    exact left_neg_eq_right_neg (a := a) (by simp [neg_add_cancel_of_ne_top, *]) h

/--
lemma `sub_left_injective_of_ne_top` / 引理 `sub_left_injective_of_ne_top`

English:
lemma sub_left_injective_of_ne_top
  given: (h : b != ⊤)
  statement: Function.Injective fun x => x - b
  proof: by
  simpa [sub_eq_add_neg] using add_left_injective_of_ne_top (-b) (by simpa)

中文:
引理 sub_left_injective_of_ne_top
  条件: (h : b != ⊤)
  结论: Function.Injective fun x => x - b
  证明: by
  simpa [sub_eq_add_neg] using add_left_injective_of_ne_top (-b) (by simpa)

Depends on / 依赖: add_left_injective_of_ne_top, sub_eq_add_neg
-/
lemma sub_left_injective_of_ne_top (h : b != ⊤) : Function.Injective fun x => x - b := by
  simpa [sub_eq_add_neg] using add_left_injective_of_ne_top (-b) (by simpa)

/--
lemma `sub_right_injective_of_ne_top` / 引理 `sub_right_injective_of_ne_top`

English:
lemma sub_right_injective_of_ne_top
  given: (h : b != ⊤)
  statement: Function.Injective fun x => b - x
  proof: by
  simpa [sub_eq_add_neg] using! (add_right_injective_of_ne_top b h).comp neg_injective

@[simp]

中文:
引理 sub_right_injective_of_ne_top
  条件: (h : b != ⊤)
  结论: Function.Injective fun x => b - x
  证明: by
  simpa [sub_eq_add_neg] using! (add_right_injective_of_ne_top b h).comp neg_injective

@[simp]

Depends on / 依赖: add_right_injective_of_ne_top, neg_injective, sub_eq_add_neg
-/
lemma sub_right_injective_of_ne_top (h : b != ⊤) : Function.Injective fun x => b - x := by
  simpa [sub_eq_add_neg] using! (add_right_injective_of_ne_top b h).comp neg_injective

@[simp]
/--
lemma `sub_left_inj_of_ne_top` / 引理 `sub_left_inj_of_ne_top`

English:
lemma sub_left_inj_of_ne_top
  given: (h : a != ⊤)
  statement: b - a = c - a ↔ b = c
  proof: (sub_left_injective_of_ne_top h).eq_iff

@[simp]

中文:
引理 sub_left_inj_of_ne_top
  条件: (h : a != ⊤)
  结论: b - a = c - a ↔ b = c
  证明: (sub_left_injective_of_ne_top h).eq_iff

@[simp]

Depends on / 依赖: eq_iff, sub_left_injective_of_ne_top
-/
lemma sub_left_inj_of_ne_top (h : a != ⊤) : b - a = c - a ↔ b = c :=
  (sub_left_injective_of_ne_top h).eq_iff

@[simp]
/--
lemma `sub_right_inj_of_ne_top` / 引理 `sub_right_inj_of_ne_top`

English:
lemma sub_right_inj_of_ne_top
  given: (h : a != ⊤)
  statement: a - b = a - c ↔ b = c
  proof: (sub_right_injective_of_ne_top h).eq_iff

中文:
引理 sub_right_inj_of_ne_top
  条件: (h : a != ⊤)
  结论: a - b = a - c ↔ b = c
  证明: (sub_right_injective_of_ne_top h).eq_iff

Depends on / 依赖: eq_iff, sub_right_injective_of_ne_top
-/
lemma sub_right_inj_of_ne_top (h : a != ⊤) : a - b = a - c ↔ b = c :=
  (sub_right_injective_of_ne_top h).eq_iff

/--
lemma `sub_left_strictMono_of_ne_top` / 引理 `sub_left_strictMono_of_ne_top`

English:
lemma sub_left_strictMono_of_ne_top
  given: (h : b != ⊤)
  statement: StrictMono fun x => x - b
  proof: by
  simpa [sub_eq_add_neg] using add_left_strictMono_of_ne_top (b := -b) (by simpa)

@[simp]

中文:
引理 sub_left_strictMono_of_ne_top
  条件: (h : b != ⊤)
  结论: StrictMono fun x => x - b
  证明: by
  simpa [sub_eq_add_neg] using add_left_strictMono_of_ne_top (b := -b) (by simpa)

@[simp]

Depends on / 依赖: add_left_strictMono_of_ne_top, sub_eq_add_neg
-/
lemma sub_left_strictMono_of_ne_top (h : b != ⊤) : StrictMono fun x => x - b := by
  simpa [sub_eq_add_neg] using add_left_strictMono_of_ne_top (b := -b) (by simpa)

@[simp]
/--
lemma `sub_le_sub_iff_left_of_ne_top` / 引理 `sub_le_sub_iff_left_of_ne_top`

English:
lemma sub_le_sub_iff_left_of_ne_top
  given: (h : a != ⊤)
  statement: b - a <= c - a ↔ b <= c
  proof: (sub_left_strictMono_of_ne_top h).le_iff_le

@[simp]

中文:
引理 sub_le_sub_iff_left_of_ne_top
  条件: (h : a != ⊤)
  结论: b - a <= c - a ↔ b <= c
  证明: (sub_left_strictMono_of_ne_top h).le_iff_le

@[simp]

Depends on / 依赖: le_iff_le, sub_left_strictMono_of_ne_top
-/
lemma sub_le_sub_iff_left_of_ne_top (h : a != ⊤) : b - a <= c - a ↔ b <= c :=
  (sub_left_strictMono_of_ne_top h).le_iff_le

@[simp]
/--
lemma `sub_lt_sub_iff_left_of_ne_top` / 引理 `sub_lt_sub_iff_left_of_ne_top`

English:
lemma sub_lt_sub_iff_left_of_ne_top
  given: (h : a != ⊤)
  statement: b - a < c - a ↔ b < c
  proof: (sub_left_strictMono_of_ne_top h).lt_iff_lt

@[simp]

中文:
引理 sub_lt_sub_iff_left_of_ne_top
  条件: (h : a != ⊤)
  结论: b - a < c - a ↔ b < c
  证明: (sub_left_strictMono_of_ne_top h).lt_iff_lt

@[simp]

Depends on / 依赖: lt_iff_lt, sub_left_strictMono_of_ne_top
-/
lemma sub_lt_sub_iff_left_of_ne_top (h : a != ⊤) : b - a < c - a ↔ b < c :=
  (sub_left_strictMono_of_ne_top h).lt_iff_lt

@[simp]
/--
lemma `add_neg_cancel_iff_ne_top` / 引理 `add_neg_cancel_iff_ne_top`

English:
lemma add_neg_cancel_iff_ne_top
  statement: a + -a = 0 ↔ a != ⊤ where
  proof: by contrapose; simp +contextual
  mpr h := add_neg_cancel_of_ne_top h

@[simp]

中文:
引理 add_neg_cancel_iff_ne_top
  结论: a + -a = 0 ↔ a != ⊤ where
  证明: by contrapose; simp +contextual
  mpr h := add_neg_cancel_of_ne_top h

@[simp]

Depends on / 依赖: add_neg_cancel_of_ne_top, contextual, contrapose
-/
lemma add_neg_cancel_iff_ne_top : a + -a = 0 ↔ a != ⊤ where
  mp := by contrapose; simp +contextual
  mpr h := add_neg_cancel_of_ne_top h

@[simp]
/--
lemma `sub_self_eq_zero_iff_ne_top` / 引理 `sub_self_eq_zero_iff_ne_top`

English:
lemma sub_self_eq_zero_iff_ne_top
  statement: a - a = 0 ↔ a != ⊤
  proof: by
  rw [sub_eq_add_neg]; rw [add_neg_cancel_iff_ne_top]

alias ⟨_, sub_self_eq_zero_of_ne_top⟩ := sub_self_eq_zero_iff_ne_top

中文:
引理 sub_self_eq_zero_iff_ne_top
  结论: a - a = 0 ↔ a != ⊤
  证明: by
  rw [sub_eq_add_neg]; rw [add_neg_cancel_iff_ne_top]

alias ⟨_, sub_self_eq_zero_of_ne_top⟩ := sub_self_eq_zero_iff_ne_top

Depends on / 依赖: add_neg_cancel_iff_ne_top, sub_eq_add_neg
-/
lemma sub_self_eq_zero_iff_ne_top : a - a = 0 ↔ a != ⊤ := by
  rw [sub_eq_add_neg]; rw [add_neg_cancel_iff_ne_top]

alias ⟨_, sub_self_eq_zero_of_ne_top⟩ := sub_self_eq_zero_iff_ne_top

/--
lemma `sub_pos` / 引理 `sub_pos`

English:
lemma sub_pos
  statement: 0 < a - b ↔ b < a ∨ b = ⊤
  proof: by
  obtain rfl | hb := eq_or_ne b ⊤
  · simp
  · simp [← sub_self_eq_zero_of_ne_top hb, hb]

@[simp]

中文:
引理 sub_pos
  结论: 0 < a - b ↔ b < a ∨ b = ⊤
  证明: by
  obtain rfl | hb := eq_or_ne b ⊤
  · simp
  · simp [← sub_self_eq_zero_of_ne_top hb, hb]

@[simp]

Depends on / 依赖: eq_or_ne, sub_self_eq_zero_of_ne_top
-/
lemma sub_pos : 0 < a - b ↔ b < a ∨ b = ⊤ := by
  obtain rfl | hb := eq_or_ne b ⊤
  · simp
  · simp [← sub_self_eq_zero_of_ne_top hb, hb]

@[simp]
/--
lemma `neg_pos` / 引理 `neg_pos`

English:
lemma neg_pos
  statement: 0 < -a ↔ a < 0 ∨ a = ⊤
  proof: by
  simpa using sub_pos (a := 0) (b := a)

@[simp]

中文:
引理 neg_pos
  结论: 0 < -a ↔ a < 0 ∨ a = ⊤
  证明: by
  simpa using sub_pos (a := 0) (b := a)

@[simp]

Depends on / 依赖: sub_pos
-/
lemma neg_pos : 0 < -a ↔ a < 0 ∨ a = ⊤ := by
  simpa using sub_pos (a := 0) (b := a)

@[simp]
/--
lemma `sub_self_nonneg` / 引理 `sub_self_nonneg`

English:
lemma sub_self_nonneg
  statement: 0 <= a - a
  proof: by
  obtain rfl | ha := eq_or_ne a ⊤
  · simp
  · rw [sub_self_eq_zero_of_ne_top ha]

@[simp]

中文:
引理 sub_self_nonneg
  结论: 0 <= a - a
  证明: by
  obtain rfl | ha := eq_or_ne a ⊤
  · simp
  · rw [sub_self_eq_zero_of_ne_top ha]

@[simp]

Depends on / 依赖: eq_or_ne, sub_self_eq_zero_of_ne_top
-/
lemma sub_self_nonneg : 0 <= a - a := by
  obtain rfl | ha := eq_or_ne a ⊤
  · simp
  · rw [sub_self_eq_zero_of_ne_top ha]

@[simp]
/--
lemma `sub_eq_zero` / 引理 `sub_eq_zero`

English:
lemma sub_eq_zero
  given: (ha : a != ⊤)
  statement: b - a = 0 ↔ b = a
  proof: by
  rw [← sub_self_eq_zero_of_ne_top ha]; rw [sub_left_inj_of_ne_top ha]

中文:
引理 sub_eq_zero
  条件: (ha : a != ⊤)
  结论: b - a = 0 ↔ b = a
  证明: by
  rw [← sub_self_eq_zero_of_ne_top ha]; rw [sub_left_inj_of_ne_top ha]

Depends on / 依赖: sub_left_inj_of_ne_top, sub_self_eq_zero_of_ne_top
-/
lemma sub_eq_zero (ha : a != ⊤) : b - a = 0 ↔ b = a := by
  rw [← sub_self_eq_zero_of_ne_top ha]; rw [sub_left_inj_of_ne_top ha]

end LinearOrderedAddCommGroupWithTop

namespace WithTop

/--
Instance `linearOrderedAddCommMonoidWithTop` / 实例 `linearOrderedAddCommMonoidWithTop`

English:
instance linearOrderedAddCommMonoidWithTop
  signature: [AddCancelCommMonoid α] [LinearOrder α]
  body: WithTop.top_add
  isAddLeftRegular_of_ne_top _a ha _b _c := WithTop.add_left_cancel ha

中文:
实例 linearOrderedAddCommMonoidWithTop
  签名: [AddCancelCommMonoid α] [LinearOrder α]
  定义体: WithTop.top_add
  isAddLeftRegular_of_ne_top _a ha _b _c := WithTop.add_left_cancel ha

Depends on / 依赖: WithTop, WithTop.top_add, top_add
-/
instance linearOrderedAddCommMonoidWithTop [AddCancelCommMonoid α] [LinearOrder α]
    [IsOrderedAddMonoid α] : LinearOrderedAddCommMonoidWithTop (WithTop α) where
  top_add' := WithTop.top_add
  isAddLeftRegular_of_ne_top _a ha _b _c := WithTop.add_left_cancel ha

namespace LinearOrderedAddCommGroup
variable [AddCommGroup G] {x y : WithTop G}

/--
Instance `instNeg` / 实例 `instNeg`

English:
instance instNeg
  signature: : Neg (WithTop G) where
  body: .map fun a => -a

中文:
实例 instNeg
  签名: : Neg (WithTop G) where
  定义体: .map fun a => -a
-/
instance instNeg : Neg (WithTop G) where
  neg := .map fun a => -a

/--
Instance `instSub` / 实例 `instSub`

English:
instance instSub
  signature: : Sub (WithTop G) where

中文:
实例 instSub
  签名: : Sub (WithTop G) where
-/
instance instSub : Sub (WithTop G) where
  sub
  | _, ⊤ => ⊤
  | ⊤, (b : G) => ⊤
  | (a : G), (b : G) => (a - b : G)

/--
lemma `coe_neg` / 引理 `coe_neg`

English:
lemma coe_neg
  given: (a : G)
  statement: (↑(-a) : WithTop G) = -a
  proof: rfl

中文:
引理 coe_neg
  条件: (a : G)
  结论: (↑(-a) : WithTop G) = -a
  证明: rfl
-/
@[simp, norm_cast] lemma coe_neg (a : G) : (↑(-a) : WithTop G) = -a := rfl
/--
lemma `coe_sub` / 引理 `coe_sub`

English:
lemma coe_sub
  given: (a b : G)
  statement: (↑(a - b) : WithTop G) = ↑a - ↑b
  proof: rfl

中文:
引理 coe_sub
  条件: (a b : G)
  结论: (↑(a - b) : WithTop G) = ↑a - ↑b
  证明: rfl
-/
@[simp, norm_cast] lemma coe_sub (a b : G) : (↑(a - b) : WithTop G) = ↑a - ↑b := rfl

/--
lemma `neg_top` / 引理 `neg_top`

English:
lemma neg_top
  statement: -(⊤ : WithTop G) = ⊤
  proof: rfl

中文:
引理 neg_top
  结论: -(⊤ : WithTop G) = ⊤
  证明: rfl
-/
@[simp] lemma neg_top : -(⊤ : WithTop G) = ⊤ := rfl

/--
lemma `top_sub` / 引理 `top_sub`

English:
lemma top_sub
  given: (x : WithTop G)
  statement: ⊤ - x = ⊤
  proof: by cases x <;> rfl

中文:
引理 top_sub
  条件: (x : WithTop G)
  结论: ⊤ - x = ⊤
  证明: by cases x <;> rfl
-/
@[simp] lemma top_sub (x : WithTop G) : ⊤ - x = ⊤ := by cases x <;> rfl
/--
lemma `sub_top` / 引理 `sub_top`

English:
lemma sub_top
  given: (x : WithTop G)
  statement: x - ⊤ = ⊤
  proof: by cases x <;> rfl

中文:
引理 sub_top
  条件: (x : WithTop G)
  结论: x - ⊤ = ⊤
  证明: by cases x <;> rfl
-/
@[simp] lemma sub_top (x : WithTop G) : x - ⊤ = ⊤ := by cases x <;> rfl

/--
lemma `sub_eq_top_iff` / 引理 `sub_eq_top_iff`

English:
lemma sub_eq_top_iff
  statement: x - y = ⊤ ↔ x = ⊤ ∨ y = ⊤
  proof: by
  cases x <;> cases y <;> simp [← coe_sub]

中文:
引理 sub_eq_top_iff
  结论: x - y = ⊤ ↔ x = ⊤ ∨ y = ⊤
  证明: by
  cases x <;> cases y <;> simp [← coe_sub]
-/
@[simp] lemma sub_eq_top_iff : x - y = ⊤ ↔ x = ⊤ ∨ y = ⊤ := by
  cases x <;> cases y <;> simp [← coe_sub]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LinearOrder
  signature: G] [IsOrderedAddMonoid G] : LinearOrderedAddCommGroupWithTop (WithTop G) where
  body: WithTop.linearOrderedAddCommMonoidWithTop
  sub_eq_add_neg a b := by cases a <;> cases b <;> simp [← coe_sub, ← coe_neg, sub_eq_add_neg]
  neg_top := WithTop.map_top _
  zsmul := zsmulRec
  add_neg_cancel_of_ne_top | (a : G), _ => mod_cast add_neg_cancel a

中文:
实例 [LinearOrder
  签名: G] [IsOrderedAddMonoid G] : LinearOrderedAddCommGroupWithTop (WithTop G) where
  定义体: WithTop.linearOrderedAddCommMonoidWithTop
  sub_eq_add_neg a b := by cases a <;> cases b <;> simp [← coe_sub, ← coe_neg, sub_eq_add_neg]
  neg_top := WithTop.map_top _
  zsmul := zsmulRec
  add_neg_cancel_of_ne_top | (a : G), _ => mod_cast add_neg_cancel a

Depends on / 依赖: WithTop, WithTop.linearOrderedAddCommMonoidWithTop, linearOrderedAddCommMonoidWithTop
-/
instance [LinearOrder G] [IsOrderedAddMonoid G] : LinearOrderedAddCommGroupWithTop (WithTop G) where
  __ := WithTop.linearOrderedAddCommMonoidWithTop
  sub_eq_add_neg a b := by cases a <;> cases b <;> simp [← coe_sub, ← coe_neg, sub_eq_add_neg]
  neg_top := WithTop.map_top _
  zsmul := zsmulRec
  add_neg_cancel_of_ne_top | (a : G), _ => mod_cast add_neg_cancel a

end WithTop.LinearOrderedAddCommGroup
