/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
module

public meta import Batteries.Tactic.Lint.Basic
public meta import Mathlib.Data.Ineq
public import Mathlib.Data.Ineq
public import Mathlib.Data.Nat.Cast.Order.Ring
public meta import Mathlib.Tactic.ToAdditive

/-!
# Lemmas for `linarith`.

Those in the `Linarith` namespace should stay here.

Those outside the `Linarith` namespace may be deleted as they are ported to mathlib4.
-/

public meta section

namespace Mathlib.Tactic.Linarith

universe u
/-
**Mathlib.Tactic.Linarith.lt_irrefl** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Li
narith`。
形式化陈述：lt_irrefl {α : Type u} [Preorder α] {a : α} : ¬a < a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
-/
theorem lt_irrefl {α : Type u} [Preorder α] {a : α} : ¬a < a := _root_.lt_irrefl a
/-
**Mathlib.Tactic.Linarith.eq_of_eq_of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tact
ic.Linarith`。
形式化陈述：eq_of_eq_of_eq {α} [Semiring α] {a b : α} (ha : a = 0) (hb : b = 0) : a + 
b = 0
参数：ha : a = 0；hb : b = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eq_of_eq_of_eq {α} [Semiring α] {a b : α} (ha : a = 0) (hb : b = 0) : a + b = 0 := by
  simp [*]

section Semiring
variable {α : Type u} [Semiring α] [PartialOrder α]

/-
**Mathlib.Tactic.Linarith.zero_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.
Linarith`。
形式化陈述：zero_lt_one [IsStrictOrderedRing α] : (0:α) < 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
-/
theorem zero_lt_one [IsStrictOrderedRing α] : (0:α) < 1 :=
  _root_.zero_lt_one
/-
**Mathlib.Tactic.Linarith.le_of_eq_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tact
ic.Linarith`。
形式化陈述：le_of_eq_of_le {a b : α} (ha : a = 0) (hb : b <= 0) : a + b <= 0
参数：ha : a = 0；hb : b <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem le_of_eq_of_le {a b : α} (ha : a = 0) (hb : b ≤ 0) : a + b ≤ 0 := by
  simp [*]
/-
**Mathlib.Tactic.Linarith.lt_of_eq_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tact
ic.Linarith`。
形式化陈述：lt_of_eq_of_lt {a b : α} (ha : a = 0) (hb : b < 0) : a + b < 0
参数：ha : a = 0；hb : b < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem lt_of_eq_of_lt {a b : α} (ha : a = 0) (hb : b < 0) : a + b < 0 := by
  simp [*]
/-
**Mathlib.Tactic.Linarith.le_of_le_of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tact
ic.Linarith`。
形式化陈述：le_of_le_of_eq {a b : α} (ha : a <= 0) (hb : b = 0) : a + b <= 0
参数：ha : a <= 0；hb : b = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem le_of_le_of_eq {a b : α} (ha : a ≤ 0) (hb : b = 0) : a + b ≤ 0 := by
  simp [*]
/-
**Mathlib.Tactic.Linarith.lt_of_lt_of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tact
ic.Linarith`。
形式化陈述：lt_of_lt_of_eq {a b : α} (ha : a < 0) (hb : b = 0) : a + b < 0
参数：ha : a < 0；hb : b = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem lt_of_lt_of_eq {a b : α} (ha : a < 0) (hb : b = 0) : a + b < 0 := by
  simp [*]
/-
**Mathlib.Tactic.Linarith.add_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.L
inarith`。
形式化陈述：add_nonpos [IsOrderedRing α] {a b : α} (ha : a <= 0) (hb : b <= 0) : a + b
 <= 0
参数：ha : a <= 0；hb : b <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_nonpos`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, a ≤ 0 → b ≤ 0 → a + b ≤ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
-/
theorem add_nonpos [IsOrderedRing α] {a b : α} (ha : a ≤ 0) (hb : b ≤ 0) :
    a + b ≤ 0 :=
  _root_.add_nonpos ha hb
/-
**Mathlib.Tactic.Linarith.add_lt_of_le_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib
.Tactic.Linarith`。
形式化陈述：add_lt_of_le_of_neg [IsStrictOrderedRing α] {a b c : α} (hbc : b <= c) (ha
 : a < 0) : b + a < c
参数：hbc : b <= c；ha : a < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_lt_of_le_of_neg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
Preorder α] [AddLeftStrictMono α] {a b c : α},   b ≤ c → a < 0 → b + a < c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
theorem add_lt_of_le_of_neg [IsStrictOrderedRing α] {a b c : α} (hbc : b ≤ c)
    (ha : a < 0) : b + a < c :=
  _root_.add_lt_of_le_of_neg hbc ha
/-
**Mathlib.Tactic.Linarith.add_lt_of_neg_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib
.Tactic.Linarith`。
形式化陈述：add_lt_of_neg_of_le [IsStrictOrderedRing α] {a b c : α} (ha : a < 0) (hbc 
: b <= c) : a + b < c
参数：ha : a < 0；hbc : b <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_lt_of_neg_of_le`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
Preorder α] [AddRightStrictMono α] {a b c : α},   a < 0 → b ≤ c → a + b < c
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
theorem add_lt_of_neg_of_le [IsStrictOrderedRing α] {a b c : α} (ha : a < 0)
    (hbc : b ≤ c) : a + b < c :=
  _root_.add_lt_of_neg_of_le ha hbc
/-
**Mathlib.Tactic.Linarith.add_neg** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Lina
rith`。
形式化陈述：add_neg [IsStrictOrderedRing α] {a b : α} (ha : a < 0) (hb : b < 0) : a + 
b < 0
参数：ha : a < 0；hb : b < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_neg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder α] 
[AddLeftStrictMono α] {a b : α},   a < 0 → b < 0 → a + b < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
theorem add_neg [IsStrictOrderedRing α] {a b : α} (ha : a < 0)
    (hb : b < 0) : a + b < 0 :=
  _root_.add_neg ha hb

variable (α) in
/-
**Mathlib.Tactic.Linarith.natCast_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Tact
ic.Linarith`。
形式化陈述：natCast_nonneg [IsOrderedRing α] (n : Nat) : (0 : α) <= n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
-/
lemma natCast_nonneg [IsOrderedRing α] (n : ℕ) : (0 : α) ≤ n := Nat.cast_nonneg n

-- used alongside `mul_neg` and `mul_nonpos`, so has the same argument pattern for uniformity
@[nolint unusedArguments]
/-
**Mathlib.Tactic.Linarith.mul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Linar
ith`。
形式化陈述：mul_eq [IsOrderedRing α] {a b : α} (ha : a = 0) (_ : 0 < b) : b * a = 0
参数：ha : a = 0；_ : 0 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_eq [IsOrderedRing α] {a b : α} (ha : a = 0) (_ : 0 < b) : b * a = 0 := by
  simp [*]

end Semiring

section Ring
variable {α : Type u} [Ring α] [PartialOrder α]

/-
**Mathlib.Tactic.Linarith.mul_neg** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.Lina
rith`。
形式化陈述：mul_neg [IsStrictOrderedRing α] {a b : α} (ha : a < 0) (hb : 0 < b) : b * 
a < 0
参数：ha : a < 0；hb : 0 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_pos_of_neg_of_neg`：mul_pos_of_neg_of_neg [ExistsAddOfLE R] [MulPosSt
rictMono R] [AddRightStrictMono R] [AddRightReflectLT R] {a b : R} (ha : a < 0) 
(hb : b < 0…
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `neg_neg_of_pos`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : Partial
Order α] [IsOrderedAddMonoid α] {a : α}, 0 < a → -a < 0
· 使用定理 `neg_of_neg_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddL
eftStrictMono α] {a : α}, 0 < -a → a < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
-/
theorem mul_neg [IsStrictOrderedRing α] {a b : α} (ha : a < 0) (hb : 0 < b) : b * a < 0 :=
  have : (-b)*a > 0 := mul_pos_of_neg_of_neg (neg_neg_of_pos hb) ha
  neg_of_neg_pos (by simpa)
/-
**Mathlib.Tactic.Linarith.mul_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tactic.L
inarith`。
形式化陈述：mul_nonpos [IsOrderedRing α] {a b : α} (ha : a <= 0) (hb : 0 < b) : b * a 
<= 0
参数：ha : a <= 0；hb : 0 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_nonneg_of_nonpos_of_nonpos`：mul_nonneg_of_nonpos_of_nonpos [ExistsAd
dOfLE R] [MulPosMono R] [AddRightMono R] [AddRightReflectLE R] (ha : a <= 0) (hb
 : b <= 0) : 0 <= a …
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `neg_neg_of_pos`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : Partial
Order α] [IsOrderedAddMonoid α] {a : α}, 0 < a → -a < 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
-/
theorem mul_nonpos [IsOrderedRing α] {a b : α} (ha : a ≤ 0) (hb : 0 < b) : b * a ≤ 0 :=
  have : (-b)*a ≥ 0 := mul_nonneg_of_nonpos_of_nonpos (le_of_lt (neg_neg_of_pos hb)) ha
  by simpa
/-
**Mathlib.Tactic.Linarith.sub_nonpos_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Ta
ctic.Linarith`。
形式化陈述：sub_nonpos_of_le [IsOrderedRing α] {a b : α} : a <= b -> a - b <= 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sub_nonpos_of_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Ad
dRightMono α] {a b : α}, a ≤ b → a - b ≤ 0
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
-/
theorem sub_nonpos_of_le [IsOrderedRing α] {a b : α} : a ≤ b → a - b ≤ 0 :=
  _root_.sub_nonpos_of_le
/-
**Mathlib.Tactic.Linarith.sub_neg_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tacti
c.Linarith`。
形式化陈述：sub_neg_of_lt [IsOrderedRing α] {a b : α} : a < b -> a - b < 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sub_neg_of_lt`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRi
ghtStrictMono α] {a b : α}, a < b → a - b < 0
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem sub_neg_of_lt [IsOrderedRing α] {a b : α} : a < b → a - b < 0 :=
  _root_.sub_neg_of_lt

end Ring

/-- Finds the name of a multiplicative lemma corresponding to an inequality strength. -/
/-
**Mathlib.Tactic.Linarith._root_.Mathlib.Ineq.toConstMulName** 是 Mathlib 中的一个定义，
位于命名空间 `Mathlib.Tactic.Linarith`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Finds the name of a multiplicative lemma corresponding to an inequality strength
.
-/
def _root_.Mathlib.Ineq.toConstMulName : Ineq → Lean.Name
  | .lt => ``mul_neg
  | .le => ``mul_nonpos
  | .eq => ``mul_eq
/-
**Mathlib.Tactic.Linarith.eq_of_not_lt_of_not_gt** 是 Mathlib 中的一个引理，位于命名空间 `Math
lib.Tactic.Linarith`。
形式化陈述：eq_of_not_lt_of_not_gt {α} [LinearOrder α] (a b : α) (h1 : ¬ a < b) (h2 : 
¬ b < a) : a = b
参数：a b : α；h1 : ¬ a < b；h2 : ¬ b < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
-/
lemma eq_of_not_lt_of_not_gt {α} [LinearOrder α] (a b : α) (h1 : ¬ a < b) (h2 : ¬ b < a) : a = b :=
  le_antisymm (le_of_not_gt h2) (le_of_not_gt h1)

-- used in the `nlinarith` normalization steps. The `_` argument is for uniformity.
@[nolint unusedArguments]
/-
**Mathlib.Tactic.Linarith.mul_zero_eq** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Tactic.
Linarith`。
形式化陈述：mul_zero_eq {α} {R : α -> α -> Prop} [Semiring α] {a b : α} (_ : R a 0) (h
 : b = 0) : a * b = 0
参数：_ : R a 0；h : b = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mul_zero_eq {α} {R : α → α → Prop} [Semiring α] {a b : α} (_ : R a 0) (h : b = 0) :
    a * b = 0 := by
  simp [h]

-- used in the `nlinarith` normalization steps. The `_` argument is for uniformity.
@[nolint unusedArguments]
/-
**Mathlib.Tactic.Linarith.zero_mul_eq** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Tactic.
Linarith`。
形式化陈述：zero_mul_eq {α} {R : α -> α -> Prop} [Semiring α] {a b : α} (h : a = 0) (_
 : R b 0) : a * b = 0
参数：h : a = 0；_ : R b 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma zero_mul_eq {α} {R : α → α → Prop} [Semiring α] {a b : α} (h : a = 0) (_ : R b 0) :
    a * b = 0 := by
  simp [h]

end Mathlib.Tactic.Linarith

