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

/-- Helper function to synthesize typed `Semiring α` `PartialOrder α` `IsOrderedRing α`
expressions. -/
/-
**Mathlib.Meta.NormNum.inferOrderedSemiring** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.M
eta.NormNum`。
形式化陈述：inferOrderedSemiring (α : Q(Type u)) : MetaM (_ : Q(Semiring $α)) × (_ : Q
(PartialOrder $α)) × Q(IsOrderedRing $α)
参数：α : Q(Type u)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Helper function to synthesize typed `Semiring α` `PartialOrder α` `IsOrderedRing
 α`
expressions.
-/
def inferOrderedSemiring (α : Q(Type u)) : MetaM <|
    (_ : Q(Semiring $α)) × (_ : Q(PartialOrder $α)) × Q(IsOrderedRing $α) :=
  let go := do
    let semiring ← synthInstanceQ q(Semiring $α)
    let partialOrder ← synthInstanceQ q(PartialOrder $α)
    let isOrderedRing ← synthInstanceQ q(IsOrderedRing $α)
    return ⟨semiring, partialOrder, isOrderedRing⟩
  go <|> throwError "not an ordered semiring"

/-- Helper function to synthesize typed `Ring α` `PartialOrder α` `IsOrderedRing α`
expressions. -/
/-
**Mathlib.Meta.NormNum.inferOrderedRing** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.
NormNum`。
形式化陈述：inferOrderedRing (α : Q(Type u)) : MetaM (_ : Q(Ring $α)) × (_ : Q(Partial
Order $α)) × Q(IsOrderedRing $α)
参数：α : Q(Type u)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Helper function to synthesize typed `Ring α` `PartialOrder α` `IsOrderedRing α`
expressions.
-/
def inferOrderedRing (α : Q(Type u)) : MetaM <|
    (_ : Q(Ring $α)) × (_ : Q(PartialOrder $α)) × Q(IsOrderedRing $α) :=
  let go := do
    let ring ← synthInstanceQ q(Ring $α)
    let partialOrder ← synthInstanceQ q(PartialOrder $α)
    let isOrderedRing ← synthInstanceQ q(IsOrderedRing $α)
    return ⟨ring, partialOrder, isOrderedRing⟩
  go <|> throwError "not an ordered ring"

/-- Helper function to synthesize typed `Semifield α` `LinearOrder α` `IsStrictOrderedRing α`
expressions. -/
/-
**Mathlib.Meta.NormNum.inferLinearOrderedSemifield** 是 Mathlib 中的一个定义，位于命名空间 `Ma
thlib.Meta.NormNum`。
形式化陈述：inferLinearOrderedSemifield (α : Q(Type u)) : MetaM (_ : Q(Semifield $α)) 
× (_ : Q(LinearOrder $α)) × Q(IsStrictOrderedRing $α)
参数：α : Q(Type u)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Helper function to synthesize typed `Semifield α` `LinearOrder α` `IsStrictOrder
edRing α`
expressions.
-/
def inferLinearOrderedSemifield (α : Q(Type u)) : MetaM <|
    (_ : Q(Semifield $α)) × (_ : Q(LinearOrder $α)) × Q(IsStrictOrderedRing $α) :=
  let go := do
    let semifield ← synthInstanceQ q(Semifield $α)
    let linearOrder ← synthInstanceQ q(LinearOrder $α)
    let isStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $α)
    return ⟨semifield, linearOrder, isStrictOrderedRing⟩
  go <|> throwError "not a linear ordered semifield"

/-- Helper function to synthesize typed `Field α` `LinearOrder α` `IsStrictOrderedRing α`
expressions. -/
/-
**Mathlib.Meta.NormNum.inferLinearOrderedField** 是 Mathlib 中的一个定义，位于命名空间 `Mathli
b.Meta.NormNum`。
形式化陈述：inferLinearOrderedField (α : Q(Type u)) : MetaM (_ : Q(Field $α)) × (_ : Q
(LinearOrder $α)) × Q(IsStrictOrderedRing $α)
参数：α : Q(Type u)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Helper function to synthesize typed `Field α` `LinearOrder α` `IsStrictOrderedRi
ng α`
expressions.
-/
def inferLinearOrderedField (α : Q(Type u)) : MetaM <|
    (_ : Q(Field $α)) × (_ : Q(LinearOrder $α)) × Q(IsStrictOrderedRing $α) :=
  let go := do
    let field ← synthInstanceQ q(Field $α)
    let linearOrder ← synthInstanceQ q(LinearOrder $α)
    let isStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $α)
    return ⟨field, linearOrder, isStrictOrderedRing⟩
  go <|> throwError "not a linear ordered field"

variable {α : Type*}
/-
**Mathlib.Meta.NormNum.isNat_le_true** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Nor
mNum`。
形式化陈述：∀ {α : Type u_1} [inst : Semiring α] [inst_1 : PartialOrder α] [IsOrderedR
ing α] {a b : α} {a' b' : ℕ},   Mathlib.Meta.NormNum.IsNat a a' → Mathlib.Meta.N
ormNum.IsNat b b' → a'.ble b' = true → a ≤ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.mono_cast`：mono_cast : Monotone (Nat.cast : Nat -> α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Nat.le_of_ble_eq_true`：∀ {n m : ℕ}, n.ble m = true → n ≤ m
-/
theorem isNat_le_true [Semiring α] [PartialOrder α] [IsOrderedRing α] : {a b : α} → {a' b' : ℕ} →
    IsNat a a' → IsNat b b' → Nat.ble a' b' = true → a ≤ b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => Nat.mono_cast (Nat.le_of_ble_eq_true h)
/-
**Mathlib.Meta.NormNum.isNat_lt_false** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：isNat_lt_false [Semiring α] [PartialOrder α] [IsOrderedRing α] {a b : α} {
a' b' : Nat} (ha : IsNat a a') (hb : IsNat b b') (h : Nat.ble b' a' = true) : ¬a
 < b
参数：ha : IsNat a a'；hb : IsNat b b'；h : Nat.ble b' a' = true。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_lt_of_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Mathlib.Meta.NormNum.isNat_le_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] {a b : α} {a' b' : ℕ},   Mathlib.Me
ta.NormNum.IsNat a a' → …
-/
theorem isNat_lt_false [Semiring α] [PartialOrder α] [IsOrderedRing α] {a b : α} {a' b' : ℕ}
    (ha : IsNat a a') (hb : IsNat b b') (h : Nat.ble b' a' = true) : ¬a < b :=
  not_lt_of_ge (isNat_le_true hb ha h)
/-
**Mathlib.Meta.NormNum.isNNRat_le_true** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.N
ormNum`。
形式化陈述：isNNRat_le_true [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] : {a 
b : α} -> {na nb : Nat} -> {da db : Nat} -> IsNNRat a na da -> IsNNRat b nb db -
> decide (Nat.mul na (db) <= Nat.mul nb (da)) -> a <= b | _, _, _, _, da, db, ⟨_
, rfl⟩, ⟨_, rfl⟩, h => by have h
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `invOf_nonneg`：invOf_nonneg [Invertible a] : 0 <= ⅟a ↔ 0 <= a
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.commute_cast`：commute_cast (x : α) (n : Nat) : Commute x n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `mul_invOf_cancel_right'`：mul_invOf_cancel_right' {_ : Invertible b} : a 
* b * ⅟b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem isNNRat_le_true [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] :
    {a b : α} → {na nb : ℕ} → {da db : ℕ} →
    IsNNRat a na da → IsNNRat b nb db →
    decide (Nat.mul na (db) ≤ Nat.mul nb (da)) → a ≤ b
  | _, _, _, _, da, db, ⟨_, rfl⟩, ⟨_, rfl⟩, h => by
    have h := (Nat.cast_le (α := α)).mpr <| of_decide_eq_true h
    have ha : 0 ≤ ⅟(da : α) := invOf_nonneg.mpr <| Nat.cast_nonneg da
    have hb : 0 ≤ ⅟(db : α) := invOf_nonneg.mpr <| Nat.cast_nonneg db
    have h := (mul_le_mul_of_nonneg_left · hb) <| mul_le_mul_of_nonneg_right h ha
    rw [← mul_assoc, Nat.commute_cast] at h
    simp only [Nat.mul_eq, Nat.cast_mul, mul_invOf_cancel_right'] at h
    rwa [Nat.commute_cast] at h
/-
**Mathlib.Meta.NormNum.isNNRat_lt_true** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.N
ormNum`。
形式化陈述：isNNRat_lt_true [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] : {a 
b : α} -> {na nb : Nat} -> {da db : Nat} -> IsNNRat a na da -> IsNNRat b nb db -
> decide (na * db < nb * da) -> a < b | _, _, _, _, da, db, ⟨_, rfl⟩, ⟨_, rfl⟩, 
h => by have h
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `pos_invOf_of_invertible_cast`：pos_invOf_of_invertible_cast (n : Nat) [In
vertible (n : R)] : 0 < ⅟(n : R)
· 使用定理 `mul_lt_mul_of_pos_left`：mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc
 : b < c) (ha : 0 < a) : a * b < a * c
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `mul_lt_mul_of_pos_right`：mul_lt_mul_of_pos_right [MulPosStrictMono α] (h
bc : b < c) (ha : 0 < a) : b * a < c * a
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.commute_cast`：commute_cast (x : α) (n : Nat) : Commute x n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `mul_invOf_cancel_right'`：mul_invOf_cancel_right' {_ : Invertible b} : a 
* b * ⅟b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem isNNRat_lt_true [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] :
    {a b : α} → {na nb : ℕ} → {da db : ℕ} →
    IsNNRat a na da → IsNNRat b nb db → decide (na * db < nb * da) → a < b
  | _, _, _, _, da, db, ⟨_, rfl⟩, ⟨_, rfl⟩, h => by
    have h := (Nat.cast_lt (α := α)).mpr <| of_decide_eq_true h
    have ha : 0 < ⅟(da : α) := pos_invOf_of_invertible_cast da
    have hb : 0 < ⅟(db : α) := pos_invOf_of_invertible_cast db
    have h := (mul_lt_mul_of_pos_left · hb) <| mul_lt_mul_of_pos_right h ha
    rw [← mul_assoc, Nat.commute_cast] at h
    simp? at h says simp only [Nat.cast_mul, mul_invOf_cancel_right'] at h
    rwa [Nat.commute_cast] at h
/-
**Mathlib.Meta.NormNum.isNNRat_le_false** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.
NormNum`。
形式化陈述：isNNRat_le_false [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] {a b
 : α} {na nb : Nat} {da db : Nat} (ha : IsNNRat a na da) (hb : IsNNRat b nb db) 
(h : decide (nb * da < na * db)) : ¬a <= b
参数：ha : IsNNRat a na da；hb : IsNNRat b nb db；h : decide (nb * da < na * db)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_lt_true`：isNNRat_lt_true [Semiring α] [Line
arOrder α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Nat} -> {da db : Nat}
 -> IsNNRat a na da -> IsN…
-/
theorem isNNRat_le_false [Semiring α] [LinearOrder α] [IsStrictOrderedRing α]
    {a b : α} {na nb : ℕ} {da db : ℕ}
    (ha : IsNNRat a na da) (hb : IsNNRat b nb db) (h : decide (nb * da < na * db)) : ¬a ≤ b :=
  not_le_of_gt (isNNRat_lt_true hb ha h)
/-
**Mathlib.Meta.NormNum.isNNRat_lt_false** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.
NormNum`。
形式化陈述：isNNRat_lt_false [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] {a b
 : α} {na nb : Nat} {da db : Nat} (ha : IsNNRat a na da) (hb : IsNNRat b nb db) 
(h : decide (nb * da <= na * db)) : ¬a < b
参数：ha : IsNNRat a na da；hb : IsNNRat b nb db；h : decide (nb * da <= na * db)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_lt_of_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_le_true`：isNNRat_le_true [Semiring α] [Line
arOrder α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Nat} -> {da db : Nat}
 -> IsNNRat a na da -> IsN…
-/
theorem isNNRat_lt_false [Semiring α] [LinearOrder α] [IsStrictOrderedRing α]
    {a b : α} {na nb : ℕ} {da db : ℕ}
    (ha : IsNNRat a na da) (hb : IsNNRat b nb db) (h : decide (nb * da ≤ na * db)) : ¬a < b :=
  not_lt_of_ge (isNNRat_le_true hb ha h)
/-
**Mathlib.Meta.NormNum.isRat_le_true** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Nor
mNum`。
形式化陈述：isRat_le_true [Ring α] [LinearOrder α] [IsStrictOrderedRing α] : {a b : α}
 -> {na nb : Int} -> {da db : Nat} -> IsRat a na da -> IsRat b nb db -> decide (
Int.mul na (.ofNat db) <= Int.mul nb (.ofNat da)) -> a <= b | _, _, _, _, da, db
, ⟨_, rfl⟩, ⟨_, rfl⟩, h => by have h
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Int.cast_mono`：cast_mono : Monotone (Int.cast : Int -> R)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `invOf_nonneg`：invOf_nonneg [Invertible a] : 0 <= ⅟a ↔ 0 <= a
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Int.commute_cast`：commute_cast (a : α) (n : Int) : Commute a n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `mul_invOf_cancel_right'`：mul_invOf_cancel_right' {_ : Invertible b} : a 
* b * ⅟b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem isRat_le_true [Ring α] [LinearOrder α] [IsStrictOrderedRing α] :
    {a b : α} → {na nb : ℤ} → {da db : ℕ} →
    IsRat a na da → IsRat b nb db →
    decide (Int.mul na (.ofNat db) ≤ Int.mul nb (.ofNat da)) → a ≤ b
  | _, _, _, _, da, db, ⟨_, rfl⟩, ⟨_, rfl⟩, h => by
    have h := Int.cast_mono (R := α) <| of_decide_eq_true h
    have ha : 0 ≤ ⅟(da : α) := invOf_nonneg.mpr <| Nat.cast_nonneg da
    have hb : 0 ≤ ⅟(db : α) := invOf_nonneg.mpr <| Nat.cast_nonneg db
    have h := (mul_le_mul_of_nonneg_left · hb) <| mul_le_mul_of_nonneg_right h ha
    rw [← mul_assoc, Int.commute_cast] at h
    simp only [Int.ofNat_eq_natCast, Int.mul_def, Int.cast_mul, Int.cast_natCast,
      mul_invOf_cancel_right'] at h
    rwa [Int.commute_cast] at h
/-
**Mathlib.Meta.NormNum.isRat_lt_true** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Nor
mNum`。
形式化陈述：isRat_lt_true [Ring α] [LinearOrder α] [IsStrictOrderedRing α] : {a b : α}
 -> {na nb : Int} -> {da db : Nat} -> IsRat a na da -> IsRat b nb db -> decide (
na * db < nb * da) -> a < b | _, _, _, _, da, db, ⟨_, rfl⟩, ⟨_, rfl⟩, h => by ha
ve h
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Int.cast_strictMono`：cast_strictMono : StrictMono (fun x : Int => (x : R
))
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `pos_invOf_of_invertible_cast`：pos_invOf_of_invertible_cast (n : Nat) [In
vertible (n : R)] : 0 < ⅟(n : R)
· 使用定理 `mul_lt_mul_of_pos_left`：mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc
 : b < c) (ha : 0 < a) : a * b < a * c
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `mul_lt_mul_of_pos_right`：mul_lt_mul_of_pos_right [MulPosStrictMono α] (h
bc : b < c) (ha : 0 < a) : b * a < c * a
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Int.commute_cast`：commute_cast (a : α) (n : Int) : Commute a n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `mul_invOf_cancel_right'`：mul_invOf_cancel_right' {_ : Invertible b} : a 
* b * ⅟b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem isRat_lt_true [Ring α] [LinearOrder α] [IsStrictOrderedRing α] :
    {a b : α} → {na nb : ℤ} → {da db : ℕ} →
    IsRat a na da → IsRat b nb db → decide (na * db < nb * da) → a < b
  | _, _, _, _, da, db, ⟨_, rfl⟩, ⟨_, rfl⟩, h => by
    have h := Int.cast_strictMono (R := α) <| of_decide_eq_true h
    have ha : 0 < ⅟(da : α) := pos_invOf_of_invertible_cast da
    have hb : 0 < ⅟(db : α) := pos_invOf_of_invertible_cast db
    have h := (mul_lt_mul_of_pos_left · hb) <| mul_lt_mul_of_pos_right h ha
    rw [← mul_assoc, Int.commute_cast] at h
    simp? at h says simp only [Int.cast_mul, Int.cast_natCast, mul_invOf_cancel_right'] at h
    rwa [Int.commute_cast] at h
/-
**Mathlib.Meta.NormNum.isRat_le_false** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：isRat_le_false [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {a b : α} 
{na nb : Int} {da db : Nat} (ha : IsRat a na da) (hb : IsRat b nb db) (h : decid
e (nb * da < na * db)) : ¬a <= b
参数：ha : IsRat a na da；hb : IsRat b nb db；h : decide (nb * da < na * db)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Mathlib.Meta.NormNum.isRat_lt_true`：isRat_lt_true [Ring α] [LinearOrder 
α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Int} -> {da db : Nat} -> IsRa
t a na da -> IsRat b nb …
-/
theorem isRat_le_false [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
    {a b : α} {na nb : ℤ} {da db : ℕ}
    (ha : IsRat a na da) (hb : IsRat b nb db) (h : decide (nb * da < na * db)) : ¬a ≤ b :=
  not_le_of_gt (isRat_lt_true hb ha h)
/-
**Mathlib.Meta.NormNum.isRat_lt_false** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：isRat_lt_false [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {a b : α} 
{na nb : Int} {da db : Nat} (ha : IsRat a na da) (hb : IsRat b nb db) (h : decid
e (nb * da <= na * db)) : ¬a < b
参数：ha : IsRat a na da；hb : IsRat b nb db；h : decide (nb * da <= na * db)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_lt_of_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Mathlib.Meta.NormNum.isRat_le_true`：isRat_le_true [Ring α] [LinearOrder 
α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Int} -> {da db : Nat} -> IsRa
t a na da -> IsRat b nb …
-/
theorem isRat_lt_false [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
    {a b : α} {na nb : ℤ} {da db : ℕ}
    (ha : IsRat a na da) (hb : IsRat b nb db) (h : decide (nb * da ≤ na * db)) : ¬a < b :=
  not_lt_of_ge (isRat_le_true hb ha h)

/-! ### (In)equalities -/

/-
**Mathlib.Meta.NormNum.isNat_lt_true** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Nor
mNum`。
形式化陈述：∀ {α : Type u_1} [inst : Semiring α] [inst_1 : PartialOrder α] [IsOrderedR
ing α] [CharZero α] {a b : α} {a' b' : ℕ},   Mathlib.Meta.NormNum.IsNat a a' → M
athlib.Meta.NormNum.IsNat b b' → b'.ble a' = false → a < b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Mathlib.Meta.NormNum.ble_eq_false`：ble_eq_false {x y : Nat} : x.ble y = 
false ↔ y < x

--- 原说明 ---
### (In)equalities
-/
theorem isNat_lt_true [Semiring α] [PartialOrder α] [IsOrderedRing α] [CharZero α] :
    {a b : α} → {a' b' : ℕ} →
    IsNat a a' → IsNat b b' → Nat.ble b' a' = false → a < b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h =>
    Nat.cast_lt.2 <| ble_eq_false.1 h
/-
**Mathlib.Meta.NormNum.isNat_le_false** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：isNat_le_false [Semiring α] [PartialOrder α] [IsOrderedRing α] [CharZero α
] {a b : α} {a' b' : Nat} (ha : IsNat a a') (hb : IsNat b b') (h : Nat.ble a' b'
 = false) : ¬a <= b
参数：ha : IsNat a a'；hb : IsNat b b'；h : Nat.ble a' b' = false。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Mathlib.Meta.NormNum.isNat_lt_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] [CharZero α] {a b : α} {a' b' : ℕ},
   Mathlib.Meta.NormNum.…
-/
theorem isNat_le_false [Semiring α] [PartialOrder α] [IsOrderedRing α] [CharZero α]
    {a b : α} {a' b' : ℕ}
    (ha : IsNat a a') (hb : IsNat b b') (h : Nat.ble a' b' = false) : ¬a ≤ b :=
  not_le_of_gt (isNat_lt_true hb ha h)
/-
**Mathlib.Meta.NormNum.isInt_le_true** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Nor
mNum`。
形式化陈述：∀ {α : Type u_1} [inst : Ring α] [inst_1 : PartialOrder α] [IsOrderedRing 
α] {a b : α} {a' b' : ℤ},   Mathlib.Meta.NormNum.IsInt a a' → Mathlib.Meta.NormN
um.IsInt b b' → decide (a' ≤ b') = true → a ≤ b
参数：a' ≤ b'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Int.cast_mono`：cast_mono : Monotone (Int.cast : Int -> R)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem isInt_le_true [Ring α] [PartialOrder α] [IsOrderedRing α] : {a b : α} → {a' b' : ℤ} →
    IsInt a a' → IsInt b b' → decide (a' ≤ b') → a ≤ b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => Int.cast_mono <| of_decide_eq_true h
/-
**Mathlib.Meta.NormNum.isInt_lt_true** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Nor
mNum`。
形式化陈述：∀ {α : Type u_1} [inst : Ring α] [inst_1 : PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {a b : α} {a' b' : ℤ},   Mathlib.Meta.NormNum.IsInt a a' → Mat
hlib.Meta.NormNum.IsInt b b' → decide (a' < b') = true → a < b
参数：a' < b'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.cast_lt`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_1 : P
artialOrder R] [AddLeftMono R] [ZeroLEOneClass R] [NeZero 1]   {m n : ℤ}, ↑m < ↑
n…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem isInt_lt_true [Ring α] [PartialOrder α] [IsOrderedRing α] [Nontrivial α] :
    {a b : α} → {a' b' : ℤ} →
    IsInt a a' → IsInt b b' → decide (a' < b') → a < b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, h => Int.cast_lt.2 <| of_decide_eq_true h
/-
**Mathlib.Meta.NormNum.isInt_le_false** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：isInt_le_false [Ring α] [PartialOrder α] [IsOrderedRing α] [Nontrivial α] 
{a b : α} {a' b' : Int} (ha : IsInt a a') (hb : IsInt b b') (h : decide (b' < a'
)) : ¬a <= b
参数：ha : IsInt a a'；hb : IsInt b b'；h : decide (b' < a')。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Mathlib.Meta.NormNum.isInt_lt_true`：∀ {α : Type u_1} [inst : Ring α] [in
st_1 : PartialOrder α] [IsOrderedRing α] [Nontrivial α] {a b : α} {a' b' : ℤ},  
 Mathlib.Meta.NormNum.Is…
-/
theorem isInt_le_false [Ring α] [PartialOrder α] [IsOrderedRing α] [Nontrivial α]
    {a b : α} {a' b' : ℤ}
    (ha : IsInt a a') (hb : IsInt b b') (h : decide (b' < a')) : ¬a ≤ b :=
  not_le_of_gt (isInt_lt_true hb ha h)
/-
**Mathlib.Meta.NormNum.isInt_lt_false** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.No
rmNum`。
形式化陈述：isInt_lt_false [Ring α] [PartialOrder α] [IsOrderedRing α] {a b : α} {a' b
' : Int} (ha : IsInt a a') (hb : IsInt b b') (h : decide (b' <= a')) : ¬a < b
参数：ha : IsInt a a'；hb : IsInt b b'；h : decide (b' <= a')。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_lt_of_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Mathlib.Meta.NormNum.isInt_le_true`：∀ {α : Type u_1} [inst : Ring α] [in
st_1 : PartialOrder α] [IsOrderedRing α] {a b : α} {a' b' : ℤ},   Mathlib.Meta.N
ormNum.IsInt a a' → Math…
-/
theorem isInt_lt_false [Ring α] [PartialOrder α] [IsOrderedRing α] {a b : α} {a' b' : ℤ}
    (ha : IsInt a a') (hb : IsInt b b') (h : decide (b' ≤ a')) : ¬a < b :=
  not_lt_of_ge (isInt_le_true hb ha h)

attribute [local instance] monadLiftOptionMetaM in
/-- The `norm_num` extension which identifies expressions of the form `a ≤ b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
/-
**Mathlib.Meta.NormNum.evalLE** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNum`。
形式化陈述：Mathlib.Meta.NormNum.NormNumExt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension which identifies expressions of the form `a ≤ b`,
such that `norm_num` successfully recognises both `a` and `b`.
-/
@[norm_num _ ≤ _] def evalLE : NormNumExt where eval {v β} e := do
  haveI' : v =QL 0 := ⟨⟩; haveI' : $β =Q Prop := ⟨⟩
  let .app (.app f a) b ← whnfR e | failure
  let ⟨u, α, a⟩ ← inferTypeQ' a
  have b : Q($α) := b
  let ra ← derive a; let rb ← derive b
  let lα ← synthInstanceQ q(LE $α)
  guard <|← withNewMCtxDepth <| isDefEq f q(LE.le (α := $α))
  core lα ra rb
where
  /-- Identify (as `true` or `false`) expressions of the form `a ≤ b`, where `a` and `b` are numeric
  expressions whose evaluations to `NormNum.Result` have already been computed. -/
  core {u : Level} {α : Q(Type u)} (lα : Q(LE $α)) {a b : Q($α)}
    (ra : NormNum.Result a) (rb : NormNum.Result b) : MetaM (NormNum.Result q($a ≤ $b)) := do
  let e := q($a ≤ $b)
  let rec intArm : MetaM (Result e) := do
    let ⟨_ir, _, _i⟩ ← inferOrderedRing α
    haveI' : $e =Q ($a ≤ $b) := ⟨⟩
    let ⟨za, na, pa⟩ ← ra.toInt q($_ir)
    let ⟨zb, nb, pb⟩ ← rb.toInt q($_ir)
    assumeInstancesCommute
    if decide (za ≤ zb) then
      let r : Q(decide ($na ≤ $nb) = true) := (q(Eq.refl true) : Expr)
      return .isTrue q(isInt_le_true $pa $pb $r)
    else if let .some _i ← trySynthInstanceQ q(Nontrivial $α) then
      let r : Q(decide ($nb < $na) = true) := (q(Eq.refl true) : Expr)
      return .isFalse q(isInt_le_false $pa $pb $r)
    else
      failure
  let rec ratArm : MetaM (Result e) := do
    let ⟨_if, _, _i⟩ ← inferLinearOrderedField α
    haveI' : $e =Q ($a ≤ $b) := ⟨⟩
    let ⟨qa, na, da, pa⟩ ← ra.toRat' q(Field.toDivisionRing)
    let ⟨qb, nb, db, pb⟩ ← rb.toRat' q(Field.toDivisionRing)
    assumeInstancesCommute
    if decide (qa ≤ qb) then
      let r : Q(decide ($na * $db ≤ $nb * $da) = true) := (q(Eq.refl true) : Expr)
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
    haveI' : $ra =Q by clear! $ra $rb; infer_instance := ⟨⟩
    haveI' : $rb =Q by clear! $ra $rb; infer_instance := ⟨⟩
    haveI' : $e =Q ($a ≤ $b) := ⟨⟩
    assumeInstancesCommute
    if na.natLit! ≤ nb.natLit! then
      let r : Q(Nat.ble $na $nb = true) := (q(Eq.refl true) : Expr)
      return .isTrue q(isNat_le_true $pa $pb $r)
    else if let .some _i ← trySynthInstanceQ q(CharZero $α) then
      let r : Q(Nat.ble $na $nb = false) := (q(Eq.refl false) : Expr)
      return .isFalse q(isNat_le_false $pa $pb $r)
    else -- Nats can appear in an ordered ring without `CharZero`.
      intArm

attribute [local instance] monadLiftOptionMetaM in
/-- The `norm_num` extension which identifies expressions of the form `a < b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
/-
**Mathlib.Meta.NormNum.evalLT** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNum`。
形式化陈述：Mathlib.Meta.NormNum.NormNumExt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension which identifies expressions of the form `a < b`,
such that `norm_num` successfully recognises both `a` and `b`.
-/
@[norm_num _ < _] def evalLT : NormNumExt where eval {v β} e := do
  haveI' : v =QL 0 := ⟨⟩; haveI' : $β =Q Prop := ⟨⟩
  let .app (.app f a) b ← whnfR e | failure
  let ⟨u, α, a⟩ ← inferTypeQ' a
  have b : Q($α) := b
  let ra ← derive a; let rb ← derive b
  let lα ← synthInstanceQ q(LT $α)
  guard <|← withNewMCtxDepth <| isDefEq f q(LT.lt (α := $α))
  core lα ra rb
where
  /-- Identify (as `true` or `false`) expressions of the form `a < b`, where `a` and `b` are numeric
  expressions whose evaluations to `NormNum.Result` have already been computed. -/
  core {u : Level} {α : Q(Type u)} (lα : Q(LT $α)) {a b : Q($α)}
    (ra : NormNum.Result a) (rb : NormNum.Result b) : MetaM (NormNum.Result q($a < $b)) := do
  let e := q($a < $b)
  let rec intArm : MetaM (Result e) := do
    let ⟨_ir, _, _i⟩ ← inferOrderedRing α
    haveI' : $e =Q ($a < $b) := ⟨⟩
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
      let r : Q(decide ($nb ≤ $na) = true) := (q(Eq.refl true) : Expr)
      return .isFalse q(isInt_lt_false $pa $pb $r)
  let rec nnratArm : MetaM (Result e) := do
    let ⟨_, _, _⟩ ← inferLinearOrderedSemifield α
    assumeInstancesCommute
    haveI' : $e =Q ($a < $b) := ⟨⟩
    let ⟨qa, na, da, pa⟩ ← ra.toNNRat' q(Semifield.toDivisionSemiring)
    let ⟨qb, nb, db, pb⟩ ← rb.toNNRat' q(Semifield.toDivisionSemiring)
    if qa < qb then
      let r : Q(decide ($na * $db < $nb * $da) = true) := (q(Eq.refl true) : Expr)
      return .isTrue q(isNNRat_lt_true $pa $pb $r)
    else
      let r : Q(decide ($nb * $da ≤ $na * $db) = true) := (q(Eq.refl true) : Expr)
      return .isFalse q(isNNRat_lt_false $pa $pb $r)
  let rec ratArm : MetaM (Result e) := do
    let ⟨_, _, _i⟩ ← inferLinearOrderedField α
    assumeInstancesCommute
    haveI' : $e =Q ($a < $b) := ⟨⟩
    let ⟨qa, na, da, pa⟩ ← ra.toRat' q(Field.toDivisionRing)
    let ⟨qb, nb, db, pb⟩ ← rb.toRat' q(Field.toDivisionRing)
    if qa < qb then
      let r : Q(decide ($na * $db < $nb * $da) = true) := (q(Eq.refl true) : Expr)
      return .isTrue q(isRat_lt_true $pa $pb $r)
    else
      let r : Q(decide ($nb * $da ≤ $na * $db) = true) := (q(Eq.refl true) : Expr)
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
    haveI' : $ra =Q by clear! $ra $rb; infer_instance := ⟨⟩
    haveI' : $rb =Q by clear! $ra $rb; infer_instance := ⟨⟩
    haveI' : $e =Q ($a < $b) := ⟨⟩
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

