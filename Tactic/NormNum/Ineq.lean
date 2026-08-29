/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Invertible
public import Mathlib.Algebra.Order.Ring.Cast
public import Mathlib.Tactic.NormNum.Eq
public meta import Mathlib.Tactic.NormNum.Result

/-!
# `norm_num` extensions for inequalities.
-/

public meta section

open Lean Meta Qq

namespace Mathlib.Meta.NormNum

variable {u : Level}

/--
Definition of `inferOrderedSemiring` / `inferOrderedSemiring` 的定义

English:
definition inferOrderedSemiring
  signature: (α : Q(Type u))
  body: let go := do
    let semiring ← synthInstanceQ q(Semiring $α)
    let partialOrder ← synthInstanceQ q(PartialOrder $α)
    let isOrderedRing ← synthInstanceQ q(IsOrderedRing $α)
    return ⟨semiring, partialOrder, isOrderedRing⟩
go > throwError "not an ordered semiring"

中文:
定义 inferOrderedSemiring
  签名: (α : Q(类型u))
  定义体: let go := do
    let semiring ← synthInstanceQ q(Semiring $α)
    let partialOrder ← synthInstanceQ q(PartialOrder $α)
    let isOrderedRing ← synthInstanceQ q(IsOrderedRing $α)
    return ⟨semiring, partialOrder, isOrderedRing⟩
go > throwError "not an ordered semiring"

Depends on / 依赖: IsOrderedRing, PartialOrder, Semiring, isOrderedRing, ordered, partialOrder, return, semiring, synthInstanceQ, throwError
-/
def inferOrderedSemiring (α : Q(Type u)) : MetaM
    (_ : Q(Semiring $α)) × (_ : Q(PartialOrder $α)) × Q(IsOrderedRing $α) :=
  let go := do
    let semiring ← synthInstanceQ q(Semiring $α)
    let partialOrder ← synthInstanceQ q(PartialOrder $α)
    let isOrderedRing ← synthInstanceQ q(IsOrderedRing $α)
    return ⟨semiring, partialOrder, isOrderedRing⟩
go > throwError "not an ordered semiring"

/--
Definition of `inferOrderedRing` / `inferOrderedRing` 的定义

English:
definition inferOrderedRing
  signature: (α : Q(Type u))
  body: let go := do
    let ring ← synthInstanceQ q(Ring $α)
    let partialOrder ← synthInstanceQ q(PartialOrder $α)
    let isOrderedRing ← synthInstanceQ q(IsOrderedRing $α)
    return ⟨ring, partialOrder, isOrderedRing⟩
go > throwError "not an ordered ring"

中文:
定义 inferOrderedRing
  签名: (α : Q(类型u))
  定义体: let go := do
    let ring ← synthInstanceQ q(Ring $α)
    let partialOrder ← synthInstanceQ q(PartialOrder $α)
    let isOrderedRing ← synthInstanceQ q(IsOrderedRing $α)
    return ⟨ring, partialOrder, isOrderedRing⟩
go > throwError "not an ordered ring"

Depends on / 依赖: IsOrderedRing, PartialOrder, isOrderedRing, ordered, partialOrder, return, synthInstanceQ, throwError
-/
def inferOrderedRing (α : Q(Type u)) : MetaM
    (_ : Q(Ring $α)) × (_ : Q(PartialOrder $α)) × Q(IsOrderedRing $α) :=
  let go := do
    let ring ← synthInstanceQ q(Ring $α)
    let partialOrder ← synthInstanceQ q(PartialOrder $α)
    let isOrderedRing ← synthInstanceQ q(IsOrderedRing $α)
    return ⟨ring, partialOrder, isOrderedRing⟩
go > throwError "not an ordered ring"

/--
Definition of `inferLinearOrderedSemifield` / `inferLinearOrderedSemifield` 的定义

English:
definition inferLinearOrderedSemifield
  signature: (α : Q(Type u))
  body: let go := do
    let semifield ← synthInstanceQ q(Semifield $α)
    let linearOrder ← synthInstanceQ q(LinearOrder $α)
    let isStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $α)
    return ⟨semifield, linearOrder, isStrictOrderedRing⟩
go > throwError "not a linear ordered semifield"

中文:
定义 inferLinearOrderedSemifield
  签名: (α : Q(类型u))
  定义体: let go := do
    let semifield ← synthInstanceQ q(Semifield $α)
    let linearOrder ← synthInstanceQ q(LinearOrder $α)
    let isStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $α)
    return ⟨semifield, linearOrder, isStrictOrderedRing⟩
go > throwError "not a linear ordered semifield"

Depends on / 依赖: IsStrictOrderedRing, LinearOrder, Semifield, isStrictOrderedRing, linear, linearOrder, ordered, return, semifield, synthInstanceQ, throwError
-/
def inferLinearOrderedSemifield (α : Q(Type u)) : MetaM
    (_ : Q(Semifield $α)) × (_ : Q(LinearOrder $α)) × Q(IsStrictOrderedRing $α) :=
  let go := do
    let semifield ← synthInstanceQ q(Semifield $α)
    let linearOrder ← synthInstanceQ q(LinearOrder $α)
    let isStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $α)
    return ⟨semifield, linearOrder, isStrictOrderedRing⟩
go > throwError "not a linear ordered semifield"

/--
Definition of `inferLinearOrderedField` / `inferLinearOrderedField` 的定义

English:
definition inferLinearOrderedField
  signature: (α : Q(Type u))
  body: let go := do
    let field ← synthInstanceQ q(Field $α)
    let linearOrder ← synthInstanceQ q(LinearOrder $α)
    let isStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $α)
    return ⟨field, linearOrder, isStrictOrderedRing⟩
go > throwError "not a linear ordered field"

中文:
定义 inferLinearOrderedField
  签名: (α : Q(类型u))
  定义体: let go := do
    let field ← synthInstanceQ q(Field $α)
    let linearOrder ← synthInstanceQ q(LinearOrder $α)
    let isStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $α)
    return ⟨field, linearOrder, isStrictOrderedRing⟩
go > throwError "not a linear ordered field"

Depends on / 依赖: IsStrictOrderedRing, LinearOrder, T1Space, T2Space, T2Space.t1Space, isStrictOrderedRing, linear, linearOrder, ordered, return, synthInstanceQ, t1Space, throwError
-/
def inferLinearOrderedField (α : Q(Type u)) : MetaM
    (_ : Q(Field $α)) × (_ : Q(LinearOrder $α)) × Q(IsStrictOrderedRing $α) :=
  let go := do
    let field ← synthInstanceQ q(Field $α)
    let linearOrder ← synthInstanceQ q(LinearOrder $α)
    let isStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $α)
    return ⟨field, linearOrder, isStrictOrderedRing⟩
go > throwError "not a linear ordered field"

variable {α : Type*}

/--
theorem `isNat_le_true` / 定理 `isNat_le_true`

English:
theorem isNat_le_true
  given: [Semiring α] [PartialOrder α] [IsOrderedRing α]
  statement: {a b : α} -> {a' b' : Nat} ->

中文:
定理 is自然数_le_true
  条件: [半环 α] [偏序 α] [是Ordered环 α]
  结论: {a b : α} -> {a' b' : 自然数} ->

Depends on / 依赖: R1Space, T2Space, T2Space.r1Space, r1Space
-/
theorem isNat_le_true [Semiring α] [PartialOrder α] [IsOrderedRing α] : {a b : α} -> {a' b' : Nat} ->
    IsNat a a' -> IsNat b b' -> Nat.ble a' b' = true -> a <= b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => Nat.mono_cast (Nat.le_of_ble_eq_true h)

/--
theorem `isNat_lt_false` / 定理 `isNat_lt_false`

English:
theorem isNat_lt_false
  statement: [Semiring α] [PartialOrder α] [IsOrderedRing α] {a b : α} {a' b' : Nat}
  proof: not_lt_of_ge (isNat_le_true hb ha h)

中文:
定理 is自然数_lt_false
  结论: [半环 α] [偏序 α] [是Ordered环 α] {a b : α} {a' b' : 自然数}
  证明: not_lt_of_ge (isNat_le_true hb ha h)

Depends on / 依赖: isNat_le_true, not_lt_of_ge
-/
theorem isNat_lt_false [Semiring α] [PartialOrder α] [IsOrderedRing α] {a b : α} {a' b' : Nat}
    (ha : IsNat a a') (hb : IsNat b b') (h : Nat.ble b' a' = true) : ¬a < b :=
  not_lt_of_ge (isNat_le_true hb ha h)

/--
theorem `isNNRat_le_true` / 定理 `isNNRat_le_true`

English:
theorem isNNRat_le_true
  given: [Semiring α] [LinearOrder α] [IsStrictOrderedRing α]
  proof: (Nat.cast_le (α := α)).mpr of_decide_eq_true h
have ha : 0 <= ⅟(da : α) := invOf_nonneg.mpr Nat.cast_nonneg da
have hb : 0 <= ⅟(db : α) := invOf_nonneg.mpr Nat.cast_nonneg db
have h := (mul_le_mul_of_nonneg_left · hb) mul_le_mul_of_nonneg_right h ha
    rw [← mul_assoc]; rw [Nat.commute_cast] at h
    simp only [Nat.mul_eq, Nat.cast_mul, mul_invOf_cancel_right'] at h
    rwa [Nat.commute_cast] at h

中文:
定理 isNNRat_le_true
  条件: [半环 α] [线性序 α] [是StrictOrdered环 α]
  证明: (Nat.cast_le (α := α)).mpr of_decide_eq_true h
have ha : 0 <= ⅟(da : α) := invOf_nonneg.mpr Nat.cast_nonneg da
have hb : 0 <= ⅟(db : α) := invOf_nonneg.mpr Nat.cast_nonneg db
have h := (mul_le_mul_of_nonneg_left · hb) mul_le_mul_of_nonneg_right h ha
    rw [← mul_assoc]; rw [Nat.commute_cast] at h
    simp only [Nat.mul_eq, Nat.cast_mul, mul_invOf_cancel_right'] at h
    rwa [Nat.commute_cast] at h

Depends on / 依赖: Nat.cast_le, cast_le, of_decide_eq_true
-/
theorem isNNRat_le_true [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] :
    {a b : α} -> {na nb : Nat} -> {da db : Nat} ->
    IsNNRat a na da -> IsNNRat b nb db ->
    decide (Nat.mul na (db) <= Nat.mul nb (da)) -> a <= b
  | _, _, _, _, da, db, ⟨_, rfl⟩, ⟨_, rfl⟩, h => by
have h := (Nat.cast_le (α := α)).mpr of_decide_eq_true h
have ha : 0 <= ⅟(da : α) := invOf_nonneg.mpr Nat.cast_nonneg da
have hb : 0 <= ⅟(db : α) := invOf_nonneg.mpr Nat.cast_nonneg db
have h := (mul_le_mul_of_nonneg_left · hb) mul_le_mul_of_nonneg_right h ha
    rw [← mul_assoc]; rw [Nat.commute_cast] at h
    simp only [Nat.mul_eq, Nat.cast_mul, mul_invOf_cancel_right'] at h
    rwa [Nat.commute_cast] at h

/--
theorem `isNNRat_lt_true` / 定理 `isNNRat_lt_true`

English:
theorem isNNRat_lt_true
  given: [Semiring α] [LinearOrder α] [IsStrictOrderedRing α]
  proof: (Nat.cast_lt (α := α)).mpr of_decide_eq_true h
    have ha : 0 < ⅟(da : α) := pos_invOf_of_invertible_cast da
    have hb : 0 < ⅟(db : α) := pos_invOf_of_invertible_cast db
have h := (mul_lt_mul_of_pos_left · hb) mul_lt_mul_of_pos_right h ha
    rw [← mul_assoc]; rw [Nat.commute_cast] at h
    simp? at h says simp only [Nat.cast_mul, mul_invOf_cancel_right'] at h
    rwa [Nat.commute_cast] at h

中文:
定理 isNNRat_lt_true
  条件: [半环 α] [线性序 α] [是StrictOrdered环 α]
  证明: (Nat.cast_lt (α := α)).mpr of_decide_eq_true h
    have ha : 0 < ⅟(da : α) := pos_invOf_of_invertible_cast da
    have hb : 0 < ⅟(db : α) := pos_invOf_of_invertible_cast db
have h := (mul_lt_mul_of_pos_left · hb) mul_lt_mul_of_pos_right h ha
    rw [← mul_assoc]; rw [Nat.commute_cast] at h
    simp? at h says simp only [Nat.cast_mul, mul_invOf_cancel_right'] at h
    rwa [Nat.commute_cast] at h

Depends on / 依赖: Nat.cast_lt, R1Space, T0Space, T2Space, cast_lt, of_decide_eq_true
-/
theorem isNNRat_lt_true [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] :
    {a b : α} -> {na nb : Nat} -> {da db : Nat} ->
    IsNNRat a na da -> IsNNRat b nb db -> decide (na * db < nb * da) -> a < b
  | _, _, _, _, da, db, ⟨_, rfl⟩, ⟨_, rfl⟩, h => by
have h := (Nat.cast_lt (α := α)).mpr of_decide_eq_true h
    have ha : 0 < ⅟(da : α) := pos_invOf_of_invertible_cast da
    have hb : 0 < ⅟(db : α) := pos_invOf_of_invertible_cast db
have h := (mul_lt_mul_of_pos_left · hb) mul_lt_mul_of_pos_right h ha
    rw [← mul_assoc]; rw [Nat.commute_cast] at h
    simp? at h says simp only [Nat.cast_mul, mul_invOf_cancel_right'] at h
    rwa [Nat.commute_cast] at h

/--
theorem `isNNRat_le_false` / 定理 `isNNRat_le_false`

English:
theorem isNNRat_le_false
  statement: [Semiring α] [LinearOrder α] [IsStrictOrderedRing α]
  proof: not_le_of_gt (isNNRat_lt_true hb ha h)

中文:
定理 isNNRat_le_false
  结论: [半环 α] [线性序 α] [是StrictOrdered环 α]
  证明: not_le_of_gt (isNNRat_lt_true hb ha h)

Depends on / 依赖: isNNRat_lt_true, not_le_of_gt
-/
theorem isNNRat_le_false [Semiring α] [LinearOrder α] [IsStrictOrderedRing α]
    {a b : α} {na nb : Nat} {da db : Nat}
    (ha : IsNNRat a na da) (hb : IsNNRat b nb db) (h : decide (nb * da < na * db)) : ¬a <= b :=
  not_le_of_gt (isNNRat_lt_true hb ha h)

/--
theorem `isNNRat_lt_false` / 定理 `isNNRat_lt_false`

English:
theorem isNNRat_lt_false
  statement: [Semiring α] [LinearOrder α] [IsStrictOrderedRing α]
  proof: not_lt_of_ge (isNNRat_le_true hb ha h)

中文:
定理 isNNRat_lt_false
  结论: [半环 α] [线性序 α] [是StrictOrdered环 α]
  证明: not_lt_of_ge (isNNRat_le_true hb ha h)

Depends on / 依赖: isNNRat_le_true, not_lt_of_ge
-/
theorem isNNRat_lt_false [Semiring α] [LinearOrder α] [IsStrictOrderedRing α]
    {a b : α} {na nb : Nat} {da db : Nat}
    (ha : IsNNRat a na da) (hb : IsNNRat b nb db) (h : decide (nb * da <= na * db)) : ¬a < b :=
  not_lt_of_ge (isNNRat_le_true hb ha h)

/--
theorem `isRat_le_true` / 定理 `isRat_le_true`

English:
theorem isRat_le_true
  given: [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  proof: Int.cast_mono (R := α) of_decide_eq_true h
have ha : 0 <= ⅟(da : α) := invOf_nonneg.mpr Nat.cast_nonneg da
have hb : 0 <= ⅟(db : α) := invOf_nonneg.mpr Nat.cast_nonneg db
have h := (mul_le_mul_of_nonneg_left · hb) mul_le_mul_of_nonneg_right h ha
    rw [← mul_assoc]; rw [Int.commute_cast] at h
    simp only [Int.ofNat_eq_natCast, Int.mul_def, Int.cast_mul, Int.cast_natCast,
      mul_invOf_cancel_right'] at h
    rwa [Int.commute_cast] at h

中文:
定理 isRat_le_true
  条件: [环 α] [线性序 α] [是StrictOrdered环 α]
  证明: Int.cast_mono (R := α) of_decide_eq_true h
have ha : 0 <= ⅟(da : α) := invOf_nonneg.mpr Nat.cast_nonneg da
have hb : 0 <= ⅟(db : α) := invOf_nonneg.mpr Nat.cast_nonneg db
have h := (mul_le_mul_of_nonneg_left · hb) mul_le_mul_of_nonneg_right h ha
    rw [← mul_assoc]; rw [Int.commute_cast] at h
    simp only [Int.ofNat_eq_natCast, Int.mul_def, Int.cast_mul, Int.cast_natCast,
      mul_invOf_cancel_right'] at h
    rwa [Int.commute_cast] at h

Depends on / 依赖: Int.cast_mono, cast_mono, of_decide_eq_true
-/
theorem isRat_le_true [Ring α] [LinearOrder α] [IsStrictOrderedRing α] :
    {a b : α} -> {na nb : Int} -> {da db : Nat} ->
    IsRat a na da -> IsRat b nb db ->
    decide (Int.mul na (.ofNat db) <= Int.mul nb (.ofNat da)) -> a <= b
  | _, _, _, _, da, db, ⟨_, rfl⟩, ⟨_, rfl⟩, h => by
have h := Int.cast_mono (R := α) of_decide_eq_true h
have ha : 0 <= ⅟(da : α) := invOf_nonneg.mpr Nat.cast_nonneg da
have hb : 0 <= ⅟(db : α) := invOf_nonneg.mpr Nat.cast_nonneg db
have h := (mul_le_mul_of_nonneg_left · hb) mul_le_mul_of_nonneg_right h ha
    rw [← mul_assoc]; rw [Int.commute_cast] at h
    simp only [Int.ofNat_eq_natCast, Int.mul_def, Int.cast_mul, Int.cast_natCast,
      mul_invOf_cancel_right'] at h
    rwa [Int.commute_cast] at h

/--
theorem `isRat_lt_true` / 定理 `isRat_lt_true`

English:
theorem isRat_lt_true
  given: [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  proof: Int.cast_strictMono (R := α) of_decide_eq_true h
    have ha : 0 < ⅟(da : α) := pos_invOf_of_invertible_cast da
    have hb : 0 < ⅟(db : α) := pos_invOf_of_invertible_cast db
have h := (mul_lt_mul_of_pos_left · hb) mul_lt_mul_of_pos_right h ha
    rw [← mul_assoc]; rw [Int.commute_cast] at h
    simp? at h says simp only [Int.cast_mul, Int.cast_natCast, mul_invOf_cancel_right'] at h
    rwa [Int.commute_cast] at h

中文:
定理 isRat_lt_true
  条件: [环 α] [线性序 α] [是StrictOrdered环 α]
  证明: Int.cast_strictMono (R := α) of_decide_eq_true h
    have ha : 0 < ⅟(da : α) := pos_invOf_of_invertible_cast da
    have hb : 0 < ⅟(db : α) := pos_invOf_of_invertible_cast db
have h := (mul_lt_mul_of_pos_left · hb) mul_lt_mul_of_pos_right h ha
    rw [← mul_assoc]; rw [Int.commute_cast] at h
    simp? at h says simp only [Int.cast_mul, Int.cast_natCast, mul_invOf_cancel_right'] at h
    rwa [Int.commute_cast] at h

Depends on / 依赖: Int.cast_strictMono, cast_strictMono, of_decide_eq_true
-/
theorem isRat_lt_true [Ring α] [LinearOrder α] [IsStrictOrderedRing α] :
    {a b : α} -> {na nb : Int} -> {da db : Nat} ->
    IsRat a na da -> IsRat b nb db -> decide (na * db < nb * da) -> a < b
  | _, _, _, _, da, db, ⟨_, rfl⟩, ⟨_, rfl⟩, h => by
have h := Int.cast_strictMono (R := α) of_decide_eq_true h
    have ha : 0 < ⅟(da : α) := pos_invOf_of_invertible_cast da
    have hb : 0 < ⅟(db : α) := pos_invOf_of_invertible_cast db
have h := (mul_lt_mul_of_pos_left · hb) mul_lt_mul_of_pos_right h ha
    rw [← mul_assoc]; rw [Int.commute_cast] at h
    simp? at h says simp only [Int.cast_mul, Int.cast_natCast, mul_invOf_cancel_right'] at h
    rwa [Int.commute_cast] at h

/--
theorem `isRat_le_false` / 定理 `isRat_le_false`

English:
theorem isRat_le_false
  statement: [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  proof: not_le_of_gt (isRat_lt_true hb ha h)

中文:
定理 isRat_le_false
  结论: [环 α] [线性序 α] [是StrictOrdered环 α]
  证明: not_le_of_gt (isRat_lt_true hb ha h)

Depends on / 依赖: isRat_lt_true, not_le_of_gt
-/
theorem isRat_le_false [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
    {a b : α} {na nb : Int} {da db : Nat}
    (ha : IsRat a na da) (hb : IsRat b nb db) (h : decide (nb * da < na * db)) : ¬a <= b :=
  not_le_of_gt (isRat_lt_true hb ha h)

/--
theorem `isRat_lt_false` / 定理 `isRat_lt_false`

English:
theorem isRat_lt_false
  statement: [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
  proof: not_lt_of_ge (isRat_le_true hb ha h)

中文:
定理 isRat_lt_false
  结论: [环 α] [线性序 α] [是StrictOrdered环 α]
  证明: not_lt_of_ge (isRat_le_true hb ha h)

Depends on / 依赖: isRat_le_true, not_lt_of_ge
-/
theorem isRat_lt_false [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
    {a b : α} {na nb : Int} {da db : Nat}
    (ha : IsRat a na da) (hb : IsRat b nb db) (h : decide (nb * da <= na * db)) : ¬a < b :=
  not_lt_of_ge (isRat_le_true hb ha h)


/--
theorem `isNat_lt_true` / 定理 `isNat_lt_true`

English:
theorem isNat_lt_true
  given: [Semiring α] [PartialOrder α] [IsOrderedRing α] [CharZero α]

中文:
定理 is自然数_lt_true
  条件: [半环 α] [偏序 α] [是Ordered环 α] [特征零 α]
-/
theorem isNat_lt_true [Semiring α] [PartialOrder α] [IsOrderedRing α] [CharZero α] :
    {a b : α} -> {a' b' : Nat} ->
    IsNat a a' -> IsNat b b' -> Nat.ble b' a' = false -> a < b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h =>
Nat.cast_lt.2 ble_eq_false.1 h

/--
theorem `isNat_le_false` / 定理 `isNat_le_false`

English:
theorem isNat_le_false
  statement: [Semiring α] [PartialOrder α] [IsOrderedRing α] [CharZero α]
  proof: not_le_of_gt (isNat_lt_true hb ha h)

中文:
定理 is自然数_le_false
  结论: [半环 α] [偏序 α] [是Ordered环 α] [特征零 α]
  证明: not_le_of_gt (isNat_lt_true hb ha h)

Depends on / 依赖: isNat_lt_true, not_le_of_gt
-/
theorem isNat_le_false [Semiring α] [PartialOrder α] [IsOrderedRing α] [CharZero α]
    {a b : α} {a' b' : Nat}
    (ha : IsNat a a') (hb : IsNat b b') (h : Nat.ble a' b' = false) : ¬a <= b :=
  not_le_of_gt (isNat_lt_true hb ha h)

/--
theorem `isInt_le_true` / 定理 `isInt_le_true`

English:
theorem isInt_le_true
  given: [Ring α] [PartialOrder α] [IsOrderedRing α]
  statement: {a b : α} -> {a' b' : Int} ->

中文:
定理 is整数_le_true
  条件: [环 α] [偏序 α] [是Ordered环 α]
  结论: {a b : α} -> {a' b' : 整数} ->
-/
theorem isInt_le_true [Ring α] [PartialOrder α] [IsOrderedRing α] : {a b : α} -> {a' b' : Int} ->
    IsInt a a' -> IsInt b b' -> decide (a' <= b') -> a <= b
| _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => Int.cast_mono of_decide_eq_true h

/--
theorem `isInt_lt_true` / 定理 `isInt_lt_true`

English:
theorem isInt_lt_true
  given: [Ring α] [PartialOrder α] [IsOrderedRing α] [Nontrivial α]

中文:
定理 is整数_lt_true
  条件: [环 α] [偏序 α] [是Ordered环 α] [非平凡 α]
-/
theorem isInt_lt_true [Ring α] [PartialOrder α] [IsOrderedRing α] [Nontrivial α] :
    {a b : α} -> {a' b' : Int} ->
    IsInt a a' -> IsInt b b' -> decide (a' < b') -> a < b
| _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => Int.cast_lt.2 of_decide_eq_true h

/--
theorem `isInt_le_false` / 定理 `isInt_le_false`

English:
theorem isInt_le_false
  statement: [Ring α] [PartialOrder α] [IsOrderedRing α] [Nontrivial α]
  proof: not_le_of_gt (isInt_lt_true hb ha h)

中文:
定理 is整数_le_false
  结论: [环 α] [偏序 α] [是Ordered环 α] [非平凡 α]
  证明: not_le_of_gt (isInt_lt_true hb ha h)

Depends on / 依赖: isInt_lt_true, not_le_of_gt
-/
theorem isInt_le_false [Ring α] [PartialOrder α] [IsOrderedRing α] [Nontrivial α]
    {a b : α} {a' b' : Int}
    (ha : IsInt a a') (hb : IsInt b b') (h : decide (b' < a')) : ¬a <= b :=
  not_le_of_gt (isInt_lt_true hb ha h)

/--
theorem `isInt_lt_false` / 定理 `isInt_lt_false`

English:
theorem isInt_lt_false
  statement: [Ring α] [PartialOrder α] [IsOrderedRing α] {a b : α} {a' b' : Int}
  proof: not_lt_of_ge (isInt_le_true hb ha h)

中文:
定理 is整数_lt_false
  结论: [环 α] [偏序 α] [是Ordered环 α] {a b : α} {a' b' : 整数}
  证明: not_lt_of_ge (isInt_le_true hb ha h)

Depends on / 依赖: isInt_le_true, not_lt_of_ge
-/
theorem isInt_lt_false [Ring α] [PartialOrder α] [IsOrderedRing α] {a b : α} {a' b' : Int}
    (ha : IsInt a a') (hb : IsInt b b') (h : decide (b' <= a')) : ¬a < b :=
  not_lt_of_ge (isInt_le_true hb ha h)

attribute [local instance] monadLiftOptionMetaM in
/--
Definition of `evalLE` / `evalLE` 的定义

English:
definition evalLE
  signature: : NormNumExt where eval {v β} e
  body: do
haveI' : v =QL 0 := ⟨⟩; haveI' : β =Q Prop := ⟨⟩
  let .app (.app f a) b ← whnfR e | failure
  let ⟨u, α, a⟩ ← inferTypeQ' a
  have b : Q($α) := b
  let ra ← derive a; let rb ← derive b
  let lα ← synthInstanceQ q(LE $α)
guard ← withNewMCtxDepth isDefEq f q(LE.le (α := $α))
  core lα ra rb

中文:
定义 evalLE
  签名: : NormNumExt where eval {v β} e
  定义体: do
haveI' : v =QL 0 := ⟨⟩; haveI' : β =Q Prop := ⟨⟩
  let .app (.app f a) b ← whnfR e | failure
  let ⟨u, α, a⟩ ← inferTypeQ' a
  have b : Q($α) := b
  let ra ← derive a; let rb ← derive b
  let lα ← synthInstanceQ q(LE $α)
guard ← withNewMCtxDepth isDefEq f q(LE.le (α := $α))
  core lα ra rb
-/
@[norm_num _ <= _] def evalLE : NormNumExt where eval {v β} e := do
haveI' : v =QL 0 := ⟨⟩; haveI' : β =Q Prop := ⟨⟩
  let .app (.app f a) b ← whnfR e | failure
  let ⟨u, α, a⟩ ← inferTypeQ' a
  have b : Q($α) := b
  let ra ← derive a; let rb ← derive b
  let lα ← synthInstanceQ q(LE $α)
guard ← withNewMCtxDepth isDefEq f q(LE.le (α := $α))
  core lα ra rb
where
  /-- Identify (as `true` or `false`) expressions of the form `a ≤ b`, where `a` and `b` are numeric
  expressions whose evaluations to `NormNum.Result` have already been computed. -/
  core {u : Level} {α : Q(Type u)} (lα : Q(LE $α)) {a b : Q($α)}
    (ra : NormNum.Result a) (rb : NormNum.Result b) : MetaM (NormNum.Result q($a <= $b)) := do
  let e := q($a <= $b)
  let rec intArm : MetaM (Result e) := do
    let ⟨_ir, _, _i⟩ ← inferOrderedRing α
haveI' : e =Q ($a <= $b) := ⟨⟩
    let ⟨za, na, pa⟩ ← ra.toInt q($_ir)
    let ⟨zb, nb, pb⟩ ← rb.toInt q($_ir)
    assumeInstancesCommute
    if decide (za <= zb) then
      let r : Q(decide ($na <= $nb) = true) := (q(Eq.refl true) : Expr)
      return .isTrue q(isInt_le_true $pa $pb $r)
    else if let .some _i ← trySynthInstanceQ q(Nontrivial $α) then
      let r : Q(decide ($nb < $na) = true) := (q(Eq.refl true) : Expr)
      return .isFalse q(isInt_le_false $pa $pb $r)
    else
      failure
  let rec ratArm : MetaM (Result e) := do
    let ⟨_if, _, _i⟩ ← inferLinearOrderedField α
haveI' : e =Q ($a <= $b) := ⟨⟩
    let ⟨qa, na, da, pa⟩ ← ra.toRat' q(Field.toDivisionRing)
    let ⟨qb, nb, db, pb⟩ ← rb.toRat' q(Field.toDivisionRing)
    assumeInstancesCommute
    if decide (qa <= qb) then
      let r : Q(decide ($na * $db <= $nb * $da) = true) := (q(Eq.refl true) : Expr)
      return (.isTrue q(isRat_le_true $pa $pb $r))
    else
      let _i : Q(Nontrivial $α) := q(IsStrictOrderedRing.toNontrivial)
      let r : Q(decide ($nb * $da < $na * $db) = true) := (q(Eq.refl true) : Expr)
      return .isFalse q(isRat_le_false $pa $pb $r)
  match ra, rb with
  | .isBool .., _ | _, .isBool .. => failure
  | .isNNRat _ .., _ | _, .isNNRat _ .. => ratArm
  | .isNegNNRat _ .., _ | _, .isNegNNRat _ .. => ratArm
  | .isNegNat _ .., _ | _, .isNegNat _ .. => intArm
  | .isNat ra na pa, .isNat rb nb pb =>
    let ⟨_, _, _i⟩ ← inferOrderedSemiring α
haveI' : ra =Q by clear! ra rb; infer_instance := ⟨⟩
haveI' : rb =Q by clear! ra rb; infer_instance := ⟨⟩
haveI' : e =Q ($a <= $b) := ⟨⟩
    assumeInstancesCommute
    if na.natLit! <= nb.natLit! then
      let r : Q(Nat.ble $na $nb = true) := (q(Eq.refl true) : Expr)
      return .isTrue q(isNat_le_true $pa $pb $r)
    else if let .some _i ← trySynthInstanceQ q(CharZero $α) then
      let r : Q(Nat.ble $na $nb = false) := (q(Eq.refl false) : Expr)
      return .isFalse q(isNat_le_false $pa $pb $r)
    else -- Nats can appear in an ordered ring without `CharZero`.
      intArm

attribute [local instance] monadLiftOptionMetaM in
/--
Definition of `evalLT` / `evalLT` 的定义

English:
definition evalLT
  signature: : NormNumExt where eval {v β} e
  body: do
haveI' : v =QL 0 := ⟨⟩; haveI' : β =Q Prop := ⟨⟩
  let .app (.app f a) b ← whnfR e | failure
  let ⟨u, α, a⟩ ← inferTypeQ' a
  have b : Q($α) := b
  let ra ← derive a; let rb ← derive b
  let lα ← synthInstanceQ q(LT $α)
guard ← withNewMCtxDepth isDefEq f q(LT.lt (α := $α))
  core lα ra rb

中文:
定义 evalLT
  签名: : NormNumExt where eval {v β} e
  定义体: do
haveI' : v =QL 0 := ⟨⟩; haveI' : β =Q Prop := ⟨⟩
  let .app (.app f a) b ← whnfR e | failure
  let ⟨u, α, a⟩ ← inferTypeQ' a
  have b : Q($α) := b
  let ra ← derive a; let rb ← derive b
  let lα ← synthInstanceQ q(LT $α)
guard ← withNewMCtxDepth isDefEq f q(LT.lt (α := $α))
  core lα ra rb
-/
@[norm_num _ < _] def evalLT : NormNumExt where eval {v β} e := do
haveI' : v =QL 0 := ⟨⟩; haveI' : β =Q Prop := ⟨⟩
  let .app (.app f a) b ← whnfR e | failure
  let ⟨u, α, a⟩ ← inferTypeQ' a
  have b : Q($α) := b
  let ra ← derive a; let rb ← derive b
  let lα ← synthInstanceQ q(LT $α)
guard ← withNewMCtxDepth isDefEq f q(LT.lt (α := $α))
  core lα ra rb
where
  /-- Identify (as `true` or `false`) expressions of the form `a < b`, where `a` and `b` are numeric
  expressions whose evaluations to `NormNum.Result` have already been computed. -/
  core {u : Level} {α : Q(Type u)} (lα : Q(LT $α)) {a b : Q($α)}
    (ra : NormNum.Result a) (rb : NormNum.Result b) : MetaM (NormNum.Result q($a < $b)) := do
  let e := q($a < $b)
  let rec intArm : MetaM (Result e) := do
    let ⟨_ir, _, _i⟩ ← inferOrderedRing α
haveI' : e =Q ($a < $b) := ⟨⟩
    let ⟨za, na, pa⟩ ← ra.toInt q($_ir)
    let ⟨zb, nb, pb⟩ ← rb.toInt q($_ir)
    assumeInstancesCommute
    if za < zb then
      if let .some _i ← trySynthInstanceQ q(Nontrivial $α) then
        let r : Q(decide ($na < $nb) = true) := (q(Eq.refl true) : Expr)
        return .isTrue q(isInt_lt_true $pa $pb $r)
      else
        failure
    else
      let r : Q(decide ($nb <= $na) = true) := (q(Eq.refl true) : Expr)
      return .isFalse q(isInt_lt_false $pa $pb $r)
  let rec nnratArm : MetaM (Result e) := do
    let ⟨_, _, _⟩ ← inferLinearOrderedSemifield α
    assumeInstancesCommute
haveI' : e =Q ($a < $b) := ⟨⟩
    let ⟨qa, na, da, pa⟩ ← ra.toNNRat' q(Semifield.toDivisionSemiring)
    let ⟨qb, nb, db, pb⟩ ← rb.toNNRat' q(Semifield.toDivisionSemiring)
    if qa < qb then
      let r : Q(decide ($na * $db < $nb * $da) = true) := (q(Eq.refl true) : Expr)
      return .isTrue q(isNNRat_lt_true $pa $pb $r)
    else
      let r : Q(decide ($nb * $da <= $na * $db) = true) := (q(Eq.refl true) : Expr)
      return .isFalse q(isNNRat_lt_false $pa $pb $r)
  let rec ratArm : MetaM (Result e) := do
    let ⟨_, _, _i⟩ ← inferLinearOrderedField α
    assumeInstancesCommute
haveI' : e =Q ($a < $b) := ⟨⟩
    let ⟨qa, na, da, pa⟩ ← ra.toRat' q(Field.toDivisionRing)
    let ⟨qb, nb, db, pb⟩ ← rb.toRat' q(Field.toDivisionRing)
    if qa < qb then
      let r : Q(decide ($na * $db < $nb * $da) = true) := (q(Eq.refl true) : Expr)
      return .isTrue q(isRat_lt_true $pa $pb $r)
    else
      let r : Q(decide ($nb * $da <= $na * $db) = true) := (q(Eq.refl true) : Expr)
      return .isFalse q(isRat_lt_false $pa $pb $r)
  match ra, rb with
  | .isBool .., _ | _, .isBool .. => failure
  | .isNegNNRat _ .., _ | _, .isNegNNRat _ .. => ratArm
    -- mixing positive rationals and negative naturals means we need to use the full rat handler
  | .isNNRat _ .., .isNegNat _ .. | .isNegNat _ .., .isNNRat _ .. => ratArm
  | .isNNRat _ .., _ | _, .isNNRat _ .. => nnratArm
  | .isNegNat _ .., _ | _, .isNegNat _ .. => intArm
  | .isNat ra na pa, .isNat rb nb pb =>
    let ⟨_, _, _i⟩ ← inferOrderedSemiring α
haveI' : ra =Q by clear! ra rb; infer_instance := ⟨⟩
haveI' : rb =Q by clear! ra rb; infer_instance := ⟨⟩
haveI' : e =Q ($a < $b) := ⟨⟩
    assumeInstancesCommute
    if na.natLit! < nb.natLit! then
      if let .some _i ← trySynthInstanceQ q(CharZero $α) then
        let r : Q(Nat.ble $nb $na = false) := (q(Eq.refl false) : Expr)
        return .isTrue q(isNat_lt_true $pa $pb $r)
      else -- Nats can appear in an ordered ring without `CharZero`.
        intArm
    else
      let r : Q(Nat.ble $nb $na = true) := (q(Eq.refl true) : Expr)
      return .isFalse q(isNat_lt_false $pa $pb $r)

end Mathlib.Meta.NormNum
