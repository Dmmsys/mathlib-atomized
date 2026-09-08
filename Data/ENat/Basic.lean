/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Nat.Units
public import Mathlib.Algebra.Order.AddGroupWithTop
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Ring.WithTop
public import Mathlib.Algebra.Order.Sub.WithTop
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.SuccPred

/-!
# Definition and basic properties of extended natural numbers

In this file we define `ENat` (notation: `ℕ∞`) to be `WithTop ℕ` and prove some basic lemmas
about this type.

## Implementation details

There are two natural coercions from `ℕ` to `WithTop ℕ = ENat`: `WithTop.some` and `Nat.cast`.  In
Lean 3, this difference was hidden in typeclass instances. Since these instances were definitionally
equal, we did not duplicate generic lemmas about `WithTop α` and `WithTop.some` coercion for `ENat`
and `Nat.cast` coercion. If you need to apply a lemma about `WithTop`, you may either rewrite back
and forth using `ENat.some_eq_natCast`, or restate the lemma for `ENat`.

## TODO

Unify `ENat.add_iSup`/`ENat.iSup_add` with `ENNReal.add_iSup`/`ENNReal.iSup_add`. The key property
of `ENat` and `ENNReal` we are using is that all `a` are either absorbing for addition (`a + b = a`
for all `b`), or that it's order-cancellable (`a + b ≤ a + c → b ≤ c` for all `b`, `c`), and
similarly for multiplication.
-/

@[expose] public section

open Function

assert_not_exists Field

deriving instance Nontrivial,
  Add, Sub, LE, LT, Bot,
  Preorder, LinearOrder, OrderTop, OrderBot, WellFoundedLT, SuccOrder,
  AddMonoidWithOne, CommSemiring, LinearOrderedAddCommMonoidWithTop,
  ZeroLEOneClass, OrderedSub, CanonicallyOrderedAdd, IsOrderedRing,
  CharZero, NoZeroDivisors
  for ENat

namespace ENat

variable {a b c d m n : ℕ∞}

/-- Lemmas about `WithTop` expect (and can output) `WithTop.some` but the normal form for coercion
`ℕ → ℕ∞` is `Nat.cast`. -/
/-
**ENat.some_eq_natCast** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：WithTop.some = Nat.cast
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lemmas about `WithTop` expect (and can output) `WithTop.some` but the normal for
m for coercion
`ℕ → ℕ∞` is `Nat.cast`.
-/
@[simp] theorem some_eq_natCast : (WithTop.some : ℕ → ℕ∞) = Nat.cast := rfl

@[deprecated (since := "2026-07-17")] alias some_eq_coe := some_eq_natCast
/-
**ENat.natCast_inj** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：natCast_inj {a b : Nat} : (a : Nat∞) = b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.coe_inj`：∀ {α : Type u_1} {a b : α}, ↑a = ↑b ↔ a = b

--- 原说明 ---
Lemmas about `WithTop` expect (and can output) `WithTop.some` but the normal for
m for coercion
`ℕ → ℕ∞` is `Nat.cast`.
-/
theorem natCast_inj {a b : ℕ} : (a : ℕ∞) = b ↔ a = b := WithTop.coe_inj

@[deprecated (since := "2026-07-17")] alias coe_inj := natCast_inj
/-
**ENat.succ_natCast** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (n : ℕ), SuccOrder.succ ↑n = ↑(n + 1)
参数：n : ℕ；n + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.succ_coe`：succ_coe [NoMaxOrder α] {a : α} : succ (↑a : WithTop α
) = ↑(succ a)
-/
@[simp] theorem succ_natCast (n : ℕ) : SuccOrder.succ (n : ℕ∞) = (n + 1 : ℕ) := WithTop.succ_coe

@[deprecated (since := "2026-07-17")] alias succ_coe := succ_natCast
/-
**ENat.succ_top** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：SuccOrder.succ ⊤ = ⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem succ_top : SuccOrder.succ (⊤ : ℕ∞) = ⊤ := rfl
/-
**ENat.** 是 Mathlib 中的一个实例，位于命名空间 `ENat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SuccAddOrder ℕ∞ where
  succ_eq_add_one x := by cases x <;> simp
/-
**ENat.natCast_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：natCast_zero : ((0 : Nat) : Nat∞) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem natCast_zero : ((0 : ℕ) : ℕ∞) = 0 :=
  rfl

@[deprecated (since := "2026-07-17")] alias coe_zero := natCast_zero
/-
**ENat.natCast_one** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：natCast_one : ((1 : Nat) : Nat∞) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem natCast_one : ((1 : ℕ) : ℕ∞) = 1 :=
  rfl

@[deprecated (since := "2026-07-17")] alias coe_one := natCast_one
/-
**ENat.natCast_add** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：natCast_add (m n : Nat) : ↑(m + n) = (m + n : Nat∞)
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem natCast_add (m n : ℕ) : ↑(m + n) = (m + n : ℕ∞) :=
  rfl

@[deprecated (since := "2026-07-17")] alias coe_add := natCast_add

@[simp, norm_cast]
/-
**ENat.natCast_sub** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：natCast_sub (m n : Nat) : ↑(m - n) = (m - n : Nat∞)
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem natCast_sub (m n : ℕ) : ↑(m - n) = (m - n : ℕ∞) :=
  rfl

@[deprecated (since := "2026-07-17")] alias coe_sub := natCast_sub
/-
**ENat.natCast_mul** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (m n : ℕ), ↑(m * n) = ↑m * ↑n
参数：m n : ℕ；m * n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma natCast_mul (m n : ℕ) : ↑(m * n) = (m * n : ℕ∞) := rfl

@[deprecated (since := "2026-07-17")] alias coe_mul := natCast_mul
/-
**ENat.mul_top** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {m : ℕ∞}, m ≠ 0 → m * ⊤ = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.mul_top`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZe
roClass α] {a : WithTop α}, a ≠ 0 → a * ⊤ = ⊤
-/
@[simp] theorem mul_top (hm : m ≠ 0) : m * ⊤ = ⊤ := WithTop.mul_top hm
/-
**ENat.top_mul** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {m : ℕ∞}, m ≠ 0 → ⊤ * m = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.top_mul`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZe
roClass α] {b : WithTop α}, b ≠ 0 → ⊤ * b = ⊤
-/
@[simp] theorem top_mul (hm : m ≠ 0) : ⊤ * m = ⊤ := WithTop.top_mul hm

/-- A version of `mul_top` where the RHS is stated as an `ite` -/
/-
**ENat.mul_top'** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：mul_top' : m * ⊤ = if m = 0 then 0 else ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.mul_top'`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZ
eroClass α] (a : WithTop α), a * ⊤ = if a = 0 then 0 else ⊤

--- 原说明 ---
A version of `mul_top` where the RHS is stated as an `ite`
-/
theorem mul_top' : m * ⊤ = if m = 0 then 0 else ⊤ := WithTop.mul_top' m

/-- A version of `top_mul` where the RHS is stated as an `ite` -/
/-
**ENat.top_mul'** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：top_mul' : ⊤ * m = if m = 0 then 0 else ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.top_mul'`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZ
eroClass α] (b : WithTop α), ⊤ * b = if b = 0 then 0 else ⊤

--- 原说明 ---
A version of `top_mul` where the RHS is stated as an `ite`
-/
theorem top_mul' : ⊤ * m = if m = 0 then 0 else ⊤ := WithTop.top_mul' m
/-
**ENat.top_pow** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {n : ℕ}, n ≠ 0 → ⊤ ^ n = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.top_pow`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : Monoi
dWithZero α] [inst_2 : NoZeroDivisors α] [inst_3 : Nontrivial α]   {n : ℕ}, n ≠ 
0 → ⊤…
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Nat.instIsDomain`：IsDomain ℕ
-/
@[simp] lemma top_pow {n : ℕ} (hn : n ≠ 0) : (⊤ : ℕ∞) ^ n = ⊤ := WithTop.top_pow hn
/-
**ENat.pow_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {a : ℕ∞} {n : ℕ}, a ^ n = ⊤ ↔ a = ⊤ ∧ n ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.pow_eq_top_iff`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 
: MonoidWithZero α] [inst_2 : NoZeroDivisors α] [inst_3 : Nontrivial α]   {x : W
ithTop α} {n…
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Nat.instIsDomain`：IsDomain ℕ
-/
@[simp] lemma pow_eq_top_iff {n : ℕ} : a ^ n = ⊤ ↔ a = ⊤ ∧ n ≠ 0 := WithTop.pow_eq_top_iff
/-
**ENat.pow_ne_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：pow_ne_top_iff {n : Nat} : a ^ n != ⊤ ↔ a != ⊤ ∨ n = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithTop.pow_ne_top_iff`：pow_ne_top_iff : x ^ n != ⊤ ↔ x != ⊤ ∨ n = 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Nat.instIsDomain`：IsDomain ℕ
-/
lemma pow_ne_top_iff {n : ℕ} : a ^ n ≠ ⊤ ↔ a ≠ ⊤ ∨ n = 0 := WithTop.pow_ne_top_iff
/-
**ENat.pow_lt_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {a : ℕ∞} {n : ℕ}, a ^ n < ⊤ ↔ a < ⊤ ∨ n = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.pow_lt_top_iff`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 
: MonoidWithZero α] [inst_2 : NoZeroDivisors α] [inst_3 : Nontrivial α]   {x : W
ithTop α} {n…
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Nat.instIsDomain`：IsDomain ℕ
-/
@[simp] lemma pow_lt_top_iff {n : ℕ} : a ^ n < ⊤ ↔ a < ⊤ ∨ n = 0 := WithTop.pow_lt_top_iff
/-
**ENat.eq_top_of_pow** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：eq_top_of_pow (n : Nat) (ha : a ^ n = ⊤) : a = ⊤
参数：n : Nat；ha : a ^ n = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithTop.eq_top_of_pow`：eq_top_of_pow (n : Nat) (hx : x ^ n = ⊤) : x = ⊤
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Nat.instIsDomain`：IsDomain ℕ
-/
lemma eq_top_of_pow (n : ℕ) (ha : a ^ n = ⊤) : a = ⊤ := WithTop.eq_top_of_pow n ha

/-- Convert a `ℕ∞` to a `ℕ` using a proof that it is not infinite. -/
/-
**ENat.lift** 是 Mathlib 中的一个定义，位于命名空间 `ENat`。
形式化陈述：lift (x : Nat∞) (h : x < ⊤) : Nat
参数：x : Nat∞；h : x < ⊤。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convert a `ℕ∞` to a `ℕ` using a proof that it is not infinite.
-/
def lift (x : ℕ∞) (h : x < ⊤) : ℕ := WithTop.untop x (WithTop.lt_top_iff_ne_top.mp h)
/-
**ENat.natCast_lift** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (x : ℕ∞) (h : x < ⊤), ↑(x.lift h) = x
参数：x : ℕ∞；h : x < ⊤；x.lift h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.coe_untop`：∀ {α : Type u_1} (x : WithTop α) (hx : x ≠ ⊤), ↑(x.un
top hx) = x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `WithTop.lt_top_iff_ne_top`：∀ {α : Type u_1} [inst : LT α] {x : WithTop α
}, x < ⊤ ↔ x ≠ ⊤
-/
@[simp] theorem natCast_lift (x : ℕ∞) (h : x < ⊤) : (lift x h : ℕ∞) = x :=
  WithTop.coe_untop x (WithTop.lt_top_iff_ne_top.mp h)

@[deprecated (since := "2026-07-17")] alias coe_lift := natCast_lift
/-
**ENat.lift_natCast** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (n : ℕ), (↑n).lift ⋯ = n
参数：n : ℕ；↑n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.natCast_lt_top`：∀ {α : Type u} [inst : AddMonoidWithOne α] [inst
_1 : LT α] (n : ℕ), ↑n < ⊤
-/
@[simp] theorem lift_natCast (n : ℕ) : lift (n : ℕ∞) (WithTop.natCast_lt_top n) = n := rfl
/-
**ENat.lift_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {x : ℕ∞} {h : x < ⊤} {n : ℕ}, x.lift h < n ↔ x < ↑n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.untop_lt_iff`：∀ {α : Type u_1} {a : α} [inst : LT α] {x : WithTo
p α} (hx : x ≠ ⊤), x.untop hx < a ↔ x < ↑a
-/
@[simp] theorem lift_lt_iff {x : ℕ∞} {h} {n : ℕ} : lift x h < n ↔ x < n := WithTop.untop_lt_iff _
/-
**ENat.lift_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {x : ℕ∞} {h : x < ⊤} {n : ℕ}, x.lift h ≤ n ↔ x ≤ ↑n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.untop_le_iff`：∀ {α : Type u_1} {a : α} [inst : LE α] {x : WithTo
p α} (hx : x ≠ ⊤), x.untop hx ≤ a ↔ x ≤ ↑a
-/
@[simp] theorem lift_le_iff {x : ℕ∞} {h} {n : ℕ} : lift x h ≤ n ↔ x ≤ n := WithTop.untop_le_iff _
/-
**ENat.lt_lift_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {x : ℕ} {n : ℕ∞} {h : n < ⊤}, x < n.lift h ↔ ↑x < n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.lt_untop_iff`：∀ {α : Type u_1} {b : α} [inst : LT α] {x : WithTo
p α} (hx : x ≠ ⊤), b < x.untop hx ↔ ↑b < x
-/
@[simp] theorem lt_lift_iff {x : ℕ} {n : ℕ∞} {h} : x < lift n h ↔ x < n := WithTop.lt_untop_iff _
/-
**ENat.le_lift_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {x : ℕ} {n : ℕ∞} {h : n < ⊤}, x ≤ n.lift h ↔ ↑x ≤ n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.le_untop_iff`：∀ {α : Type u_1} {a : α} [inst : LE α] {x : WithTo
p α} (hx : x ≠ ⊤), a ≤ x.untop hx ↔ ↑a ≤ x
-/
@[simp] theorem le_lift_iff {x : ℕ} {n : ℕ∞} {h} : x ≤ lift n h ↔ x ≤ n := WithTop.le_untop_iff _

@[deprecated (since := "2026-07-17")] alias lift_coe := lift_natCast
/-
**ENat.lift_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：ENat.lift 0 ⋯ = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.natCast_lt_top`：∀ {α : Type u} [inst : AddMonoidWithOne α] [inst
_1 : LT α] (n : ℕ), ↑n < ⊤
-/
@[simp] theorem lift_zero : lift 0 (WithTop.natCast_lt_top 0) = 0 := rfl
/-
**ENat.lift_one** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：ENat.lift 1 ⋯ = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.natCast_lt_top`：∀ {α : Type u} [inst : AddMonoidWithOne α] [inst
_1 : LT α] (n : ℕ), ↑n < ⊤
-/
@[simp] theorem lift_one : lift 1 (WithTop.natCast_lt_top 1) = 1 := rfl
/-
**ENat.lift_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (n : ℕ) [inst : n.AtLeastTwo], (OfNat.ofNat n).lift ⋯ = OfNat.ofNat n
参数：n : ℕ；OfNat.ofNat n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.natCast_lt_top`：∀ {α : Type u} [inst : AddMonoidWithOne α] [inst
_1 : LT α] (n : ℕ), ↑n < ⊤
-/
@[simp] theorem lift_ofNat (n : ℕ) [n.AtLeastTwo] :
    lift ofNat(n) (WithTop.natCast_lt_top n) = OfNat.ofNat n := rfl
/-
**ENat.add_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {a b : ℕ∞}, a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithTop.add_lt_top`：add_lt_top [LT α] : x + y < ⊤ ↔ x < ⊤ ∧ y < ⊤
-/
@[simp] theorem add_lt_top {a b : ℕ∞} : a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤ := WithTop.add_lt_top
/-
**ENat.add_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {a b : ℕ∞}, a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.add_eq_top`：∀ {α : Type u} [inst : Add α] {x y : WithTop α}, x +
 y = ⊤ ↔ x = ⊤ ∨ y = ⊤
-/
@[simp] theorem add_eq_top {a b : ℕ∞} : a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤ := WithTop.add_eq_top
/-
**ENat.lift_add** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (a b : ℕ∞) (h : a + b < ⊤), (a + b).lift h = a.lift ⋯ + b.lift ⋯
参数：a b : ℕ∞；h : a + b < ⊤；a + b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ENat.add_lt_top`：∀ {a b : ℕ∞}, a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ENat.natCast_inj`：natCast_inj {a b : Nat} : (a : Nat∞) = b ↔ a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENat.natCast_lift`：∀ (x : ℕ∞) (h : x < ⊤), ↑(x.lift h) = x
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem lift_add (a b : ℕ∞) (h : a + b < ⊤) :
    lift (a + b) h = lift a (add_lt_top.1 h).1 + lift b (add_lt_top.1 h).2 := by
  apply natCast_inj.1
  simp
/-
**ENat.canLift** 是 Mathlib 中的一个实例，位于命名空间 `ENat`。
形式化陈述：canLift : CanLift Nat∞ Nat (↑) (· != ⊤)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.canLift`：∀ {α : Type u_1}, CanLift (WithTop α) α WithTop.some fu
n r => r ≠ ⊤
-/
instance canLift : CanLift ℕ∞ ℕ (↑) (· ≠ ⊤) := WithTop.canLift
/-
**ENat.** 是 Mathlib 中的一个实例，位于命名空间 `ENat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : WellFoundedRelation ℕ∞ :=
  WellFoundedLT.toWellFoundedRelation

/-- Conversion of `ℕ∞` to `ℕ` sending `∞` to `0`. -/
/-
**ENat.toNat** 是 Mathlib 中的一个定义，位于命名空间 `ENat`。
形式化陈述：toNat : Nat∞ -> Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Conversion of `ℕ∞` to `ℕ` sending `∞` to `0`.
-/
def toNat : ℕ∞ → ℕ := WithTop.untopD 0

/-- Homomorphism from `ℕ∞` to `ℕ` sending `∞` to `0`. -/
/-
**ENat.toNatHom** 是 Mathlib 中的一个定义，位于命名空间 `ENat`。
形式化陈述：toNatHom : MonoidWithZeroHom Nat∞ Nat where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `WithTop.untopD_zero_mul`：untopD_zero_mul (a b : WithTop α) : (a * b).unt
opD 0 = a.untopD 0 * b.untopD 0

--- 原说明 ---
Homomorphism from `ℕ∞` to `ℕ` sending `∞` to `0`.
-/
def toNatHom : MonoidWithZeroHom ℕ∞ ℕ where
  toFun := toNat
  map_one' := rfl
  map_zero' := rfl
  map_mul' := WithTop.untopD_zero_mul
/-
**ENat.coe_toNatHom** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：⇑ENat.toNatHom = ENat.toNat
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_toNatHom : toNatHom = toNat := rfl
/-
**ENat.toNatHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：toNatHom_apply (n : Nat) : toNatHom n = toNat n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toNatHom_apply (n : ℕ) : toNatHom n = toNat n := rfl

@[simp]
/-
**ENat.toNat_natCast** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：toNat_natCast (n : Nat) : toNat n = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toNat_natCast (n : ℕ) : toNat n = n :=
  rfl

@[deprecated (since := "2026-07-17")] alias toNat_coe := toNat_natCast

@[simp]
/-
**ENat.toNat_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：toNat_zero : toNat 0 = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toNat_zero : toNat 0 = 0 :=
  rfl

@[simp]
/-
**ENat.toNat_one** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：toNat_one : toNat 1 = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toNat_one : toNat 1 = 1 :=
  rfl

@[simp]
/-
**ENat.toNat_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：toNat_ofNat (n : Nat) [n.AtLeastTwo] : toNat ofNat(n) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toNat_ofNat (n : ℕ) [n.AtLeastTwo] : toNat ofNat(n) = n :=
  rfl

@[simp]
/-
**ENat.toNat_top** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：toNat_top : toNat ⊤ = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toNat_top : toNat ⊤ = 0 :=
  rfl
/-
**ENat.toNat_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {n : ℕ∞}, n.toNat = 0 ↔ n = 0 ∨ n = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.untopD_eq_self_iff`：∀ {α : Type u_1} {d : α} {x : WithTop α}, Wi
thTop.untopD d x = d ↔ x = ↑d ∨ x = ⊤
-/
@[simp] theorem toNat_eq_zero : toNat n = 0 ↔ n = 0 ∨ n = ⊤ := WithTop.untopD_eq_self_iff
/-
**ENat.toNat_pos** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：toNat_pos (hn0 : n != 0) (hxt : n != ⊤) : 0 < n.toNat
参数：hn0 : n != 0；hxt : n != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `ENat.toNat_eq_zero`：∀ {n : ℕ∞}, n.toNat = 0 ↔ n = 0 ∨ n = ⊤
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
-/
theorem toNat_pos (hn0 : n ≠ 0) (hxt : n ≠ ⊤) : 0 < n.toNat := by
  rw [pos_iff_ne_zero, ne_eq, ENat.toNat_eq_zero, not_or]
  exact ⟨hn0, hxt⟩
/-
**ENat.lift_eq_toNat_of_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：lift_eq_toNat_of_lt_top {x : Nat∞} (hx : x < ⊤) : x.lift hx = x.toNat
参数：hx : x < ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem lift_eq_toNat_of_lt_top {x : ℕ∞} (hx : x < ⊤) : x.lift hx = x.toNat := by
  rcases x with ⟨⟩ | x
  · contradiction
  · rfl

@[simp]
/-
**ENat.recTopCoe_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：recTopCoe_zero {C : Nat∞ -> Sort*} (d : C ⊤) (f : forall a : Nat, C a) : @
recTopCoe C d f 0 = f 0
参数：d : C ⊤；f : forall a : Nat, C a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem recTopCoe_zero {C : ℕ∞ → Sort*} (d : C ⊤) (f : ∀ a : ℕ, C a) : @recTopCoe C d f 0 = f 0 :=
  rfl

@[simp]
/-
**ENat.recTopCoe_one** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：recTopCoe_one {C : Nat∞ -> Sort*} (d : C ⊤) (f : forall a : Nat, C a) : @r
ecTopCoe C d f 1 = f 1
参数：d : C ⊤；f : forall a : Nat, C a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem recTopCoe_one {C : ℕ∞ → Sort*} (d : C ⊤) (f : ∀ a : ℕ, C a) : @recTopCoe C d f 1 = f 1 :=
  rfl

@[simp]
/-
**ENat.recTopCoe_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：recTopCoe_ofNat {C : Nat∞ -> Sort*} (d : C ⊤) (f : forall a : Nat, C a) (x
 : Nat) [x.AtLeastTwo] : @recTopCoe C d f ofNat(x) = f (OfNat.ofNat x)
参数：d : C ⊤；f : forall a : Nat, C a；x : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem recTopCoe_ofNat {C : ℕ∞ → Sort*} (d : C ⊤) (f : ∀ a : ℕ, C a) (x : ℕ) [x.AtLeastTwo] :
    @recTopCoe C d f ofNat(x) = f (OfNat.ofNat x) :=
  rfl

@[simp]
/-
**ENat.top_ne_natCast** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：top_ne_natCast (a : Nat) : ⊤ != (a : Nat∞)
参数：a : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem top_ne_natCast (a : ℕ) : ⊤ ≠ (a : ℕ∞) :=
  nofun

@[deprecated (since := "2026-07-17")] alias top_ne_coe := top_ne_natCast

@[simp]
/-
**ENat.top_ne_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：top_ne_ofNat (a : Nat) [a.AtLeastTwo] : ⊤ != (ofNat(a) : Nat∞)
参数：a : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem top_ne_ofNat (a : ℕ) [a.AtLeastTwo] : ⊤ ≠ (ofNat(a) : ℕ∞) :=
  nofun
/-
**ENat.top_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：⊤ ≠ 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma top_ne_zero : (⊤ : ℕ∞) ≠ 0 := nofun
/-
**ENat.top_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：⊤ ≠ 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma top_ne_one : (⊤ : ℕ∞) ≠ 1 := nofun

@[simp]
/-
**ENat.natCast_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：natCast_ne_top (a : Nat) : (a : Nat∞) != ⊤
参数：a : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem natCast_ne_top (a : ℕ) : (a : ℕ∞) ≠ ⊤ :=
  nofun

@[deprecated (since := "2026-07-17")] alias coe_ne_top := natCast_ne_top

@[simp]
/-
**ENat.ofNat_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：ofNat_ne_top (a : Nat) [a.AtLeastTwo] : (ofNat(a) : Nat∞) != ⊤
参数：a : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofNat_ne_top (a : ℕ) [a.AtLeastTwo] : (ofNat(a) : ℕ∞) ≠ ⊤ :=
  nofun
/-
**ENat.zero_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：0 ≠ ⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma zero_ne_top : 0 ≠ (⊤ : ℕ∞) := nofun
/-
**ENat.one_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：1 ≠ ⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma one_ne_top : 1 ≠ (⊤ : ℕ∞) := nofun

@[simp]
/-
**ENat.top_sub_natCast** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：top_sub_natCast (a : Nat) : (⊤ : Nat∞) - a = ⊤
参数：a : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem top_sub_natCast (a : ℕ) : (⊤ : ℕ∞) - a = ⊤ :=
  rfl

@[deprecated (since := "2026-07-17")] alias top_sub_coe := top_sub_natCast

@[simp]
/-
**ENat.top_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：top_sub_one : (⊤ : Nat∞) - 1 = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem top_sub_one : (⊤ : ℕ∞) - 1 = ⊤ :=
  rfl

@[simp]
/-
**ENat.top_sub_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：top_sub_ofNat (a : Nat) [a.AtLeastTwo] : (⊤ : Nat∞) - ofNat(a) = ⊤
参数：a : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem top_sub_ofNat (a : ℕ) [a.AtLeastTwo] : (⊤ : ℕ∞) - ofNat(a) = ⊤ :=
  rfl

@[simp]
/-
**ENat.top_pos** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：top_pos : (0 : Nat∞) < ⊤
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.top_pos`：∀ {α : Type u} [inst : Zero α] [inst_1 : LT α], 0 < ⊤
-/
theorem top_pos : (0 : ℕ∞) < ⊤ :=
  WithTop.top_pos

@[simp]
/-
**ENat.one_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：one_lt_top : (1 : Nat∞) < ⊤
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.one_lt_top`：one_lt_top [One α] [LT α] : (1 : WithTop α) < ⊤
-/
theorem one_lt_top : (1 : ℕ∞) < ⊤ :=
  WithTop.one_lt_top
/-
**ENat.sub_top** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (a : ℕ∞), a - ⊤ = 0
参数：a : ℕ∞。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.sub_top`：sub_top {a : WithTop α} : a - ⊤ = (⊥ : α)
-/
@[simp] theorem sub_top (a : ℕ∞) : a - ⊤ = 0 := WithTop.sub_top

@[simp]
/-
**ENat.natCast_toNat_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：natCast_toNat_eq_self : ENat.toNat n = n ↔ n != ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem natCast_toNat_eq_self : ENat.toNat n = n ↔ n ≠ ⊤ :=
  ENat.recTopCoe (by decide) (fun _ => by simp [toNat_natCast]) n

@[deprecated (since := "2026-07-17")] alias coe_toNat_eq_self := natCast_toNat_eq_self

alias ⟨_, natCast_toNat⟩ := natCast_toNat_eq_self

@[deprecated (since := "2026-07-17")] alias coe_toNat := natCast_toNat
/-
**ENat.toNat_eq_iff_eq_natCast** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (n : ℕ∞) (m : ℕ) [NeZero m], n.toNat = m ↔ n = ↑m
参数：n : ℕ∞；m : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `NeZero.ne'`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], 0 ≠
 n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma toNat_eq_iff_eq_natCast (n : ℕ∞) (m : ℕ) [NeZero m] :
    n.toNat = m ↔ n = m := by
  cases n
  · simpa using NeZero.ne' m
  · simp

@[deprecated (since := "2026-07-17")] alias toNat_eq_iff_eq_coe := toNat_eq_iff_eq_natCast
/-
**ENat.natCast_toNat_le_self** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：natCast_toNat_le_self (n : Nat∞) : ↑(toNat n) <= n
参数：n : Nat∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem natCast_toNat_le_self (n : ℕ∞) : ↑(toNat n) ≤ n :=
  ENat.recTopCoe le_top (fun _ => le_rfl) n

@[deprecated (since := "2026-07-17")] alias coe_toNat_le_self := natCast_toNat_le_self
/-
**ENat.toNat_add** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：toNat_add {m n : Nat∞} (hm : m != ⊤) (hn : n != ⊤) : toNat (m + n) = toNat
 m + toNat n
参数：hm : m != ⊤；hn : n != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
-/
theorem toNat_add {m n : ℕ∞} (hm : m ≠ ⊤) (hn : n ≠ ⊤) : toNat (m + n) = toNat m + toNat n := by
  lift m to ℕ using hm
  lift n to ℕ using hn
  rfl
/-
**ENat.toNat_sub** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：toNat_sub {n : Nat∞} (hn : n != ⊤) (m : Nat∞) : toNat (m - n) = toNat m - 
toNat n
参数：hn : n != ⊤；m : Nat∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENat.top_sub_natCast`：top_sub_natCast (a : Nat) : (⊤ : Nat∞) - a = ⊤
· 使用定理 `ENat.toNat_top`：toNat_top : toNat ⊤ = 0
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.natCast_sub`：natCast_sub (m n : Nat) : ↑(m - n) = (m - n : Nat∞)
· 使用定理 `ENat.toNat_natCast`：toNat_natCast (n : Nat) : toNat n = n
-/
theorem toNat_sub {n : ℕ∞} (hn : n ≠ ⊤) (m : ℕ∞) : toNat (m - n) = toNat m - toNat n := by
  lift n to ℕ using hn
  induction m
  · rw [top_sub_natCast, toNat_top, zero_tsub]
  · rw [← natCast_sub, toNat_natCast, toNat_natCast, toNat_natCast]
/-
**ENat.toNat_mul** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (a b : ℕ∞), (a * b).toNat = a.toNat * b.toNat
参数：a b : ℕ∞；a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENat.mul_top`：∀ {m : ℕ∞}, m ≠ 0 → m * ⊤ = ⊤
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `ENat.top_mul`：∀ {m : ℕ∞}, m ≠ 0 → ⊤ * m = ⊤
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENat.natCast_mul`：∀ (m n : ℕ), ↑(m * n) = ↑m * ↑n
· 使用定理 `ENat.toNat_natCast`：toNat_natCast (n : Nat) : toNat n = n
-/
@[simp] theorem toNat_mul (a b : ℕ∞) : (a * b).toNat = a.toNat * b.toNat := by
  cases a <;> cases b
  · simp
  · rename_i b; cases b <;> simp
  · rename_i a; cases a <;> simp
  · simp only [toNat_natCast]; rw [← natCast_mul, toNat_natCast]
/-
**ENat.toNat_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：toNat_eq_iff {m : Nat∞} {n : Nat} (hn : n != 0) : toNat m = n ↔ m = n
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
theorem toNat_eq_iff {m : ℕ∞} {n : ℕ} (hn : n ≠ 0) : toNat m = n ↔ m = n := by
  induction m <;> simp [hn.symm]
/-
**ENat.toNat_le_of_le_natCast** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：toNat_le_of_le_natCast {m : Nat∞} {n : Nat} (h : m <= n) : toNat m <= n
参数：h : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `ENat.natCast_ne_top`：natCast_ne_top (a : Nat) : (a : Nat∞) != ⊤
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
lemma toNat_le_of_le_natCast {m : ℕ∞} {n : ℕ} (h : m ≤ n) : toNat m ≤ n := by
  lift m to ℕ using ne_top_of_le_ne_top (natCast_ne_top n) h
  simpa using h

@[deprecated (since := "2026-07-17")] alias toNat_le_of_le_coe := toNat_le_of_le_natCast

@[gcongr]
/-
**ENat.toNat_le_toNat** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：toNat_le_toNat {m n : Nat∞} (h : m <= n) (hn : n != ⊤) : toNat m <= toNat 
n
参数：h : m <= n；hn : n != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENat.toNat_le_of_le_natCast`：toNat_le_of_le_natCast {m : Nat∞} {n : Nat}
 (h : m <= n) : toNat m <= n
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.natCast_toNat`：∀ {n : ℕ∞}, n ≠ ⊤ → ↑n.toNat = n
-/
lemma toNat_le_toNat {m n : ℕ∞} (h : m ≤ n) (hn : n ≠ ⊤) : toNat m ≤ toNat n :=
  toNat_le_of_le_natCast <| h.trans_eq (natCast_toNat hn).symm

@[deprecated Order.succ_eq_add_one (since := "2026-05-25")]
/-
**ENat.succ_def** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：succ_def (m : Nat∞) : Order.succ m = m + 1
参数：m : Nat∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.succ_eq_add_one`：succ_eq_add_one (x : α) : succ x = x + 1
-/
theorem succ_def (m : ℕ∞) : Order.succ m = m + 1 :=
  Order.succ_eq_add_one m
/-
**ENat.add_one_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：add_one_le_iff (hm : m != ⊤) : m + 1 <= n ↔ m < n
参数：hm : m != ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.add_one_le_iff_of_not_isMax`：add_one_le_iff_of_not_isMax (hx : ¬ I
sMax x) : x + 1 <= y ↔ x < y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_isMax_iff_ne_top`：not_isMax_iff_ne_top : ¬IsMax a ↔ a != ⊤
-/
theorem add_one_le_iff (hm : m ≠ ⊤) : m + 1 ≤ n ↔ m < n :=
  Order.add_one_le_iff_of_not_isMax (not_isMax_iff_ne_top.mpr hm)
/-
**ENat.add_one_le_iff'** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：add_one_le_iff' (hn : n != ⊤) : m + 1 <= n ↔ m < n
参数：hn : n != ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.add_one_le_iff_of_not_isMax'`：add_one_le_iff_of_not_isMax' (hy : ¬
 IsMax y) : x + 1 <= y ↔ x < y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_isMax_iff_ne_top`：not_isMax_iff_ne_top : ¬IsMax a ↔ a != ⊤
-/
theorem add_one_le_iff' (hn : n ≠ ⊤) : m + 1 ≤ n ↔ m < n :=
  Order.add_one_le_iff_of_not_isMax' (not_isMax_iff_ne_top.mpr hn)
/-
**ENat.natCast_add_one_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：natCast_add_one_le_iff {m : Nat} {n : Nat∞} : m + 1 <= n ↔ m < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENat.add_one_le_iff`：add_one_le_iff (hm : m != ⊤) : m + 1 <= n ↔ m < n
· 使用定理 `ENat.natCast_ne_top`：natCast_ne_top (a : Nat) : (a : Nat∞) != ⊤
-/
theorem natCast_add_one_le_iff {m : ℕ} {n : ℕ∞} : m + 1 ≤ n ↔ m < n :=
  add_one_le_iff <| natCast_ne_top m

@[deprecated (since := "2026-07-17")] alias coe_add_one_le_iff := natCast_add_one_le_iff
/-
**ENat.add_one_le_natCast_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：add_one_le_natCast_iff {m : Nat∞} {n : Nat} : m + 1 <= n ↔ m < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENat.add_one_le_iff'`：add_one_le_iff' (hn : n != ⊤) : m + 1 <= n ↔ m < n
· 使用定理 `ENat.natCast_ne_top`：natCast_ne_top (a : Nat) : (a : Nat∞) != ⊤
-/
theorem add_one_le_natCast_iff {m : ℕ∞} {n : ℕ} : m + 1 ≤ n ↔ m < n :=
  add_one_le_iff' <| natCast_ne_top n

@[deprecated (since := "2026-07-17")] alias add_one_le_coe_iff := add_one_le_natCast_iff

@[deprecated Order.one_le_iff_ne_zero (since := "2026-05-25")]
/-
**ENat.one_le_iff_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {n : ℕ∞}, 1 ≤ n ↔ n ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.one_le_iff_ne_zero`：one_le_iff_ne_zero [AddMonoidWithOne α] [NeZer
o (1 : α)] [SuccAddOrder α] [IsBotZeroClass α] : 1 <= x ↔ x != 0
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
-/
protected theorem one_le_iff_ne_zero : 1 ≤ n ↔ n ≠ 0 :=
  Order.one_le_iff_ne_zero

@[deprecated Order.lt_one_iff (since := "2026-05-25")]
/-
**ENat.lt_one_iff_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：lt_one_iff_eq_zero : n < 1 ↔ n = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.lt_one_iff`：lt_one_iff : x < 1 ↔ x = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
-/
lemma lt_one_iff_eq_zero : n < 1 ↔ n = 0 :=
  Order.lt_one_iff

@[deprecated Order.le_one_iff (since := "2026-05-25")]
/-
**ENat.le_one_iff_eq_zero_or_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：le_one_iff_eq_zero_or_eq_one : n <= 1 ↔ n = 0 ∨ n = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.le_one_iff`：le_one_iff : x <= 1 ↔ x = 0 ∨ x = 1
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
-/
lemma le_one_iff_eq_zero_or_eq_one : n ≤ 1 ↔ n = 0 ∨ n = 1 :=
  Order.le_one_iff
/-
**ENat.lt_add_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：lt_add_one_iff (hn : n != ⊤) : m < n + 1 ↔ m <= n
参数：hn : n != ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.lt_add_one_iff_of_not_isMax`：lt_add_one_iff_of_not_isMax (hy : ¬ I
sMax y) : x < y + 1 ↔ x <= y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_isMax_iff_ne_top`：not_isMax_iff_ne_top : ¬IsMax a ↔ a != ⊤
-/
theorem lt_add_one_iff (hn : n ≠ ⊤) : m < n + 1 ↔ m ≤ n :=
  Order.lt_add_one_iff_of_not_isMax (not_isMax_iff_ne_top.mpr hn)
/-
**ENat.lt_add_one_iff'** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：lt_add_one_iff' (hm : m != ⊤) : m < n + 1 ↔ m <= n
参数：hm : m != ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.lt_add_one_iff_of_not_isMax'`：lt_add_one_iff_of_not_isMax' (hx : ¬
 IsMax x) : x < y + 1 ↔ x <= y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_isMax_iff_ne_top`：not_isMax_iff_ne_top : ¬IsMax a ↔ a != ⊤
-/
theorem lt_add_one_iff' (hm : m ≠ ⊤) : m < n + 1 ↔ m ≤ n :=
  Order.lt_add_one_iff_of_not_isMax' (not_isMax_iff_ne_top.mpr hm)

@[simp]
/-
**ENat.lt_two_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：lt_two_iff : n < 2 ↔ n <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
· 使用定理 `ENat.lt_add_one_iff`：lt_add_one_iff (hn : n != ⊤) : m < n + 1 ↔ m <= n
· 使用定理 `ENat.one_ne_top`：1 ≠ ⊤
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_two_iff : n < 2 ↔ n ≤ 1 := by
  rw [← one_add_one_eq_two, lt_add_one_iff one_ne_top]
/-
**ENat.add_le_add_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：add_le_add_iff_left {m n k : ENat} (h : k != ⊤) : k + n <= k + m ↔ n <= m
参数：h : k != ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.add_le_add_iff_left`：∀ {α : Type u} [inst : Add α] {x y z : With
Top α} [inst_1 : LE α] [AddLeftMono α] [AddLeftReflectLE α],   x ≠ ⊤ → (x + y ≤ 
x + z ↔ y ≤ z)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
-/
theorem add_le_add_iff_left {m n k : ENat} (h : k ≠ ⊤) :
    k + n ≤ k + m ↔ n ≤ m :=
  WithTop.add_le_add_iff_left h
/-
**ENat.add_le_add_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：add_le_add_iff_right {m n k : ENat} (h : k != ⊤) : n + k <= m + k ↔ n <= m
参数：h : k != ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.add_le_add_iff_right`：∀ {α : Type u} [inst : Add α] {x y z : Wit
hTop α} [inst_1 : LE α] [AddRightMono α] [AddRightReflectLE α],   z ≠ ⊤ → (x + z
 ≤ y + z ↔ x ≤ y)
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
-/
theorem add_le_add_iff_right {m n k : ENat} (h : k ≠ ⊤) :
    n + k ≤ m + k ↔ n ≤ m :=
  WithTop.add_le_add_iff_right h
/-
**ENat.lt_natCast_add_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：lt_natCast_add_one_iff {m : Nat∞} {n : Nat} : m < n + 1 ↔ m <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENat.lt_add_one_iff`：lt_add_one_iff (hn : n != ⊤) : m < n + 1 ↔ m <= n
· 使用定理 `ENat.natCast_ne_top`：natCast_ne_top (a : Nat) : (a : Nat∞) != ⊤
-/
theorem lt_natCast_add_one_iff {m : ℕ∞} {n : ℕ} : m < n + 1 ↔ m ≤ n :=
  lt_add_one_iff (natCast_ne_top n)

@[deprecated (since := "2026-07-17")] alias lt_coe_add_one_iff := lt_natCast_add_one_iff
/-
**ENat.natCast_lt_add_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：natCast_lt_add_one_iff {m : Nat} {n : Nat∞} : m < n + 1 ↔ m <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENat.lt_add_one_iff'`：lt_add_one_iff' (hm : m != ⊤) : m < n + 1 ↔ m <= n
· 使用定理 `ENat.natCast_ne_top`：natCast_ne_top (a : Nat) : (a : Nat∞) != ⊤
-/
theorem natCast_lt_add_one_iff {m : ℕ} {n : ℕ∞} : m < n + 1 ↔ m ≤ n :=
  lt_add_one_iff' (natCast_ne_top m)

@[deprecated (since := "2026-07-17")] alias coe_lt_add_one_iff := natCast_lt_add_one_iff
/-
**ENat.le_natCast_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：le_natCast_iff {n : Nat∞} {k : Nat} : n <= ↑k ↔ exists (n₀ : Nat), n = n₀ 
∧ n₀ <= k
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.le_coe_iff`：∀ {α : Type u_1} {a : α} [inst : LE α] {x : WithTop 
α}, x ≤ ↑a ↔ ∃ b, x = ↑b ∧ b ≤ a
-/
theorem le_natCast_iff {n : ℕ∞} {k : ℕ} : n ≤ ↑k ↔ ∃ (n₀ : ℕ), n = n₀ ∧ n₀ ≤ k :=
  WithTop.le_coe_iff

@[deprecated (since := "2026-07-17")] alias le_coe_iff := le_natCast_iff

@[simp]
/-
**ENat.natCast_lt_top** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：natCast_lt_top (n : Nat) : (n : Nat∞) < ⊤
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.natCast_lt_top`：∀ {α : Type u} [inst : AddMonoidWithOne α] [inst
_1 : LT α] (n : ℕ), ↑n < ⊤
-/
lemma natCast_lt_top (n : ℕ) : (n : ℕ∞) < ⊤ :=
  WithTop.natCast_lt_top n

@[deprecated (since := "2026-07-17")] alias coe_lt_top := natCast_lt_top
/-
**ENat.natCast_lt_natCast** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：natCast_lt_natCast {n m : Nat} : (n : Nat∞) < (m : Nat∞) ↔ n < m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma natCast_lt_natCast {n m : ℕ} : (n : ℕ∞) < (m : ℕ∞) ↔ n < m := by simp

@[deprecated (since := "2026-07-17")] alias coe_lt_coe := natCast_lt_natCast
/-
**ENat.natCast_le_natCast** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：natCast_le_natCast {n m : Nat} : (n : Nat∞) <= (m : Nat∞) ↔ n <= m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma natCast_le_natCast {n m : ℕ} : (n : ℕ∞) ≤ (m : ℕ∞) ↔ n ≤ m := by simp

@[deprecated (since := "2026-07-17")] alias coe_le_coe := natCast_le_natCast

@[elab_as_elim]
/-
**ENat.nat_induction** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：nat_induction {motive : Nat∞ -> Prop} (a : Nat∞) (zero : motive 0) (succ :
 forall n : Nat, motive n -> motive n.succ) (top : (forall n : Nat, motive n) ->
 motive ⊤) : motive a
参数：a : Nat∞；zero : motive 0；succ : forall n : Nat, motive n -> motive n.succ；top
 : (forall n : Nat, motive n) -> motive ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem nat_induction {motive : ℕ∞ → Prop} (a : ℕ∞) (zero : motive 0)
    (succ : ∀ n : ℕ, motive n → motive n.succ)
    (top : (∀ n : ℕ, motive n) → motive ⊤) : motive a := by
  have A : ∀ n : ℕ, motive n := fun n => Nat.recOn n zero succ
  cases a
  · exact top A
  · exact A _

@[deprecated add_pos_of_right (since := "2026-05-25")]
/-
**ENat.add_one_pos** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：add_one_pos : 0 < n + 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_pos_of_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Pre
order α] [IsBotZeroClass α] [AddRightMono α] {b : α},   0 < b → ∀ (a : α), 0 < a
 + b
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
-/
lemma add_one_pos : 0 < n + 1 :=
  add_pos_of_right zero_lt_one n
/-
**ENat.natCast_lt_succ** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：natCast_lt_succ {n : Nat} : (n : Nat∞) < (n : Nat∞) + 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用引理 `ENat.natCast_lt_natCast`：natCast_lt_natCast {n m : Nat} : (n : Nat∞) < (
m : Nat∞) ↔ n < m
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
lemma natCast_lt_succ {n : ℕ} :
    (n : ℕ∞) < (n : ℕ∞) + 1 := by
  rw [← Nat.cast_one, ← Nat.cast_add, natCast_lt_natCast]
  exact lt_add_one n
/-
**ENat.add_lt_add_iff_right** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：add_lt_add_iff_right {k : Nat∞} (h : k != ⊤) : n + k < m + k ↔ n < m
参数：h : k != ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.add_lt_add_iff_right`：∀ {α : Type u} [inst : Add α] {x y z : Wit
hTop α} [inst_1 : LT α] [AddRightStrictMono α] [AddRightReflectLT α],   z ≠ ⊤ → 
(x + z < y + z ↔ x…
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
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
-/
lemma add_lt_add_iff_right {k : ℕ∞} (h : k ≠ ⊤) : n + k < m + k ↔ n < m :=
  WithTop.add_lt_add_iff_right h
/-
**ENat.add_lt_add_iff_left** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：add_lt_add_iff_left {k : Nat∞} (h : k != ⊤) : k + n < k + m ↔ n < m
参数：h : k != ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.add_lt_add_iff_left`：∀ {α : Type u} [inst : Add α] {x y z : With
Top α} [inst_1 : LT α] [AddLeftStrictMono α] [AddLeftReflectLT α],   x ≠ ⊤ → (x 
+ y < x + z ↔ y <…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
lemma add_lt_add_iff_left {k : ℕ∞} (h : k ≠ ⊤) : k + n < k + m ↔ n < m :=
  WithTop.add_lt_add_iff_left h
/-
**ENat.add_lt_add** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {a b c d : ℕ∞}, a < c → b < d → a + b < c + d
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.add_lt_add`：∀ {α : Type u} [inst : Add α] {w x y z : WithTop α} 
[inst_1 : Preorder α] [AddLeftStrictMono α] [AddRightStrictMono α],   x < z → y 
< w → x …
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
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
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
protected lemma add_lt_add (hac : a < c) (hbd : b < d) : a + b < c + d :=
  WithTop.add_lt_add hac hbd
/-
**ENat.add_lt_add_of_le_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {a b c d : ℕ∞}, a ≠ ⊤ → a ≤ b → c < d → a + c < b + d
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.add_lt_add_of_le_of_lt`：∀ {α : Type u} [inst : Add α] {w x y z :
 WithTop α} [inst_1 : Preorder α] [AddLeftStrictMono α] [AddRightMono α],   w ≠ 
⊤ → w ≤ y → x < z → …
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
protected theorem add_lt_add_of_le_of_lt : a ≠ ⊤ → a ≤ b → c < d → a + c < b + d :=
  WithTop.add_lt_add_of_le_of_lt
/-
**ENat.add_lt_add_of_lt_of_le** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {a b c d : ℕ∞}, c ≠ ⊤ → a < b → c ≤ d → a + c < b + d
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.add_lt_add_of_lt_of_le`：∀ {α : Type u} [inst : Add α] {w x y z :
 WithTop α} [inst_1 : Preorder α] [AddLeftMono α] [AddRightStrictMono α],   x ≠ 
⊤ → w < y → x ≤ z → …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
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
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
protected theorem add_lt_add_of_lt_of_le : c ≠ ⊤ → a < b → c ≤ d → a + c < b + d :=
  WithTop.add_lt_add_of_lt_of_le
/-
**ENat.ne_top_iff_exists** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：ne_top_iff_exists : n != ⊤ ↔ exists m : Nat, ↑m = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.ne_top_iff_exists`：∀ {α : Type u_1} {x : WithTop α}, x ≠ ⊤ ↔ ∃ a
, ↑a = x
-/
lemma ne_top_iff_exists : n ≠ ⊤ ↔ ∃ m : ℕ, ↑m = n := WithTop.ne_top_iff_exists
/-
**ENat.eq_top_iff_forall_ne** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：eq_top_iff_forall_ne : n = ⊤ ↔ forall m : Nat, ↑m != n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.eq_top_iff_forall_ne`：∀ {α : Type u_1} {x : WithTop α}, x = ⊤ ↔ 
∀ (a : α), ↑a ≠ x
-/
lemma eq_top_iff_forall_ne : n = ⊤ ↔ ∀ m : ℕ, ↑m ≠ n := WithTop.eq_top_iff_forall_ne
/-
**ENat.forall_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：forall_ne_top {p : Nat∞ -> Prop} : (forall x, x != ⊤ -> p x) ↔ forall x : 
Nat, p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.forall_ne_top`：∀ {α : Type u_1} {p : WithTop α → Prop}, (∀ (x : 
WithTop α), x ≠ ⊤ → p x) ↔ ∀ (x : α), p ↑x
-/
lemma forall_ne_top {p : ℕ∞ → Prop} : (∀ x, x ≠ ⊤ → p x) ↔ ∀ x : ℕ, p x := WithTop.forall_ne_top
/-
**ENat.exists_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：exists_ne_top {p : Nat∞ -> Prop} : (exists x != ⊤, p x) ↔ exists x : Nat, 
p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.exists_ne_top`：∀ {α : Type u_1} {p : WithTop α → Prop}, (∃ x, x 
≠ ⊤ ∧ p x) ↔ ∃ x, p ↑x
-/
lemma exists_ne_top {p : ℕ∞ → Prop} : (∃ x ≠ ⊤, p x) ↔ ∃ x : ℕ, p x := WithTop.exists_ne_top
/-
**ENat.eq_top_iff_forall_gt** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：eq_top_iff_forall_gt : n = ⊤ ↔ forall m : Nat, m < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.eq_top_iff_forall_gt`：∀ {α : Type u_1} [inst : Preorder α] {x : 
WithTop α}, x = ⊤ ↔ ∀ (b : α), ↑b < x
-/
lemma eq_top_iff_forall_gt : n = ⊤ ↔ ∀ m : ℕ, m < n := WithTop.eq_top_iff_forall_gt
/-
**ENat.eq_top_iff_forall_ge** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：eq_top_iff_forall_ge : n = ⊤ ↔ forall m : Nat, m <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.eq_top_iff_forall_ge`：∀ {α : Type u_1} [inst : Preorder α] {x : 
WithTop α} [NoTopOrder α], x = ⊤ ↔ ∀ (b : α), ↑b ≤ x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
-/
lemma eq_top_iff_forall_ge : n = ⊤ ↔ ∀ m : ℕ, m ≤ n := WithTop.eq_top_iff_forall_ge

/-- Version of `WithTop.forall_natCast_le_iff_le` using `Nat.cast` rather than `WithTop.some`. -/
/-
**ENat.forall_natCast_le_iff_le** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：forall_natCast_le_iff_le : (forall a : Nat, a <= m -> a <= n) ↔ m <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.forall_coe_le_iff_le`：∀ {α : Type u_1} [inst : Preorder α] {x y 
: WithTop α} [NoTopOrder α], (∀ (a : α), ↑a ≤ y → ↑a ≤ x) ↔ y ≤ x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α

--- 原说明 ---
Version of `WithTop.forall_natCast_le_iff_le` using `Nat.cast` rather than `With
Top.some`.
-/
lemma forall_natCast_le_iff_le : (∀ a : ℕ, a ≤ m → a ≤ n) ↔ m ≤ n := WithTop.forall_coe_le_iff_le

/-- Version of `WithTop.eq_of_forall_natCast_le_iff` using `Nat.cast` rather than `WithTop.some`. -/
/-
**ENat.eq_of_forall_natCast_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：eq_of_forall_natCast_le_iff (hm : forall a : Nat, a <= m ↔ a <= n) : m = n
参数：hm : forall a : Nat, a <= m ↔ a <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.eq_of_forall_coe_le_iff`：∀ {α : Type u_1} [inst : PartialOrder α
] {x y : WithTop α} [NoTopOrder α], (∀ (a : α), ↑a ≤ x ↔ ↑a ≤ y) → x = y
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α

--- 原说明 ---
Version of `WithTop.eq_of_forall_natCast_le_iff` using `Nat.cast` rather than `W
ithTop.some`.
-/
lemma eq_of_forall_natCast_le_iff (hm : ∀ a : ℕ, a ≤ m ↔ a ≤ n) : m = n :=
  WithTop.eq_of_forall_coe_le_iff hm
/-
**ENat.exists_nat_gt** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {n : ℕ∞}, n ≠ ⊤ → ∃ m, n < ↑m
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `Function.mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `ENat.eq_top_iff_forall_ge`：eq_top_iff_forall_ge : n = ⊤ ↔ forall m : Nat
, m <= n
-/
protected lemma exists_nat_gt (hn : n ≠ ⊤) : ∃ m : ℕ, n < m := by
  simp_rw [lt_iff_not_ge]
  exact not_forall.mp <| eq_top_iff_forall_ge.2.mt hn
/-
**ENat.sub_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {a b : ℕ∞}, a - b = ⊤ ↔ a = ⊤ ∧ b ≠ ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.sub_eq_top_iff`：∀ {α : Type u_1} [inst : Sub α] [inst_1 : Bot α]
 {a b : WithTop α}, a - b = ⊤ ↔ a = ⊤ ∧ b ≠ ⊤
-/
@[simp] lemma sub_eq_top_iff : a - b = ⊤ ↔ a = ⊤ ∧ b ≠ ⊤ := WithTop.sub_eq_top_iff
/-
**ENat.sub_ne_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：sub_ne_top_iff : a - b != ⊤ ↔ a != ⊤ ∨ b = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithTop.sub_ne_top_iff`：sub_ne_top_iff {a b : WithTop α} : a - b != ⊤ ↔ 
a != ⊤ ∨ b = ⊤
-/
lemma sub_ne_top_iff : a - b ≠ ⊤ ↔ a ≠ ⊤ ∨ b = ⊤ := WithTop.sub_ne_top_iff
/-
**ENat.addLECancellable_of_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：addLECancellable_of_ne_top : a != ⊤ -> AddLECancellable a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithTop.addLECancellable_of_ne_top`：addLECancellable_of_ne_top [LE α] [A
ddLeftReflectLE α] (hx : x != ⊤) : AddLECancellable x
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
lemma addLECancellable_of_ne_top : a ≠ ⊤ → AddLECancellable a := WithTop.addLECancellable_of_ne_top
/-
**ENat.addLECancellable_of_lt_top** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：addLECancellable_of_lt_top : a < ⊤ -> AddLECancellable a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithTop.addLECancellable_of_lt_top`：addLECancellable_of_lt_top [Preorder
 α] [AddLeftReflectLE α] (hx : x < ⊤) : AddLECancellable x
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
lemma addLECancellable_of_lt_top : a < ⊤ → AddLECancellable a := WithTop.addLECancellable_of_lt_top
/-
**ENat.addLECancellable_natCast** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：addLECancellable_natCast (a : Nat) : AddLECancellable (a : Nat∞)
参数：a : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithTop.addLECancellable_coe`：addLECancellable_coe [LE α] [AddLeftReflec
tLE α] (a : α) : AddLECancellable (a : WithTop α)
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
lemma addLECancellable_natCast (a : ℕ) : AddLECancellable (a : ℕ∞) := WithTop.addLECancellable_coe _

@[deprecated (since := "2026-07-17")] alias addLECancellable_coe := addLECancellable_natCast
/-
**ENat.le_sub_of_add_le_left** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {a b c : ℕ∞}, a ≠ ⊤ → a + b ≤ c → b ≤ c - a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.le_tsub_of_add_le_left`：∀ {α : Type u_1} [inst : Preord
er α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c : α},
   AddLECancellable a → a + b…
· 使用定理 `instOrderedSubENat`：OrderedSub ℕ∞
· 使用引理 `ENat.addLECancellable_of_ne_top`：addLECancellable_of_ne_top : a != ⊤ -> 
AddLECancellable a
-/
protected lemma le_sub_of_add_le_left (ha : a ≠ ⊤) : a + b ≤ c → b ≤ c - a :=
  (addLECancellable_of_ne_top ha).le_tsub_of_add_le_left
/-
**ENat.le_sub_of_add_le_right** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {a b c : ℕ∞}, b ≠ ⊤ → a + b ≤ c → a ≤ c - b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.le_tsub_of_add_le_right`：∀ {α : Type u_1} [inst : Preor
der α] [inst_1 : AddCommSemigroup α] [inst_2 : Sub α] [OrderedSub α] {a b c : α}
,   AddLECancellable b → a + b…
· 使用定理 `instOrderedSubENat`：OrderedSub ℕ∞
· 使用引理 `ENat.addLECancellable_of_ne_top`：addLECancellable_of_ne_top : a != ⊤ -> 
AddLECancellable a
-/
protected lemma le_sub_of_add_le_right (hb : b ≠ ⊤) : a + b ≤ c → a ≤ c - b :=
  (addLECancellable_of_ne_top hb).le_tsub_of_add_le_right
/-
**ENat.le_sub_one_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {a b : ℕ∞}, a < b → a ≤ b - 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.le_sub_of_add_le_right`：∀ {a b c : ℕ∞}, b ≠ ⊤ → a + b ≤ c → a ≤ c -
 b
· 使用定理 `ENat.one_ne_top`：1 ≠ ⊤
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENat.lt_natCast_add_one_iff`：lt_natCast_add_one_iff {m : Nat∞} {n : Nat}
 : m < n + 1 ↔ m <= n
· 使用定理 `lt_tsub_iff_right`：lt_tsub_iff_right : a < b - c ↔ a + c < b
· 使用定理 `instOrderedSubENat`：OrderedSub ℕ∞
-/
protected lemma le_sub_one_of_lt (h : a < b) : a ≤ b - 1 := by
  cases b
  · simp
  · exact ENat.le_sub_of_add_le_right one_ne_top <| lt_natCast_add_one_iff.mp <|
      lt_tsub_iff_right.mp h
/-
**ENat.lt_add_left** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：lt_add_left {n k : Nat∞} (h : n != ⊤) (h' : 0 < k) : n < k + n
参数：h : n != ⊤；h' : 0 < k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `ENat.add_lt_add_iff_right`：add_lt_add_iff_right {k : Nat∞} (h : k != ⊤) 
: n + k < m + k ↔ n < m
-/
lemma lt_add_left {n k : ℕ∞} (h : n ≠ ⊤) (h' : 0 < k) : n < k + n := calc
    _ = 0 + n := (zero_add n).symm
    _ < k + n := (add_lt_add_iff_right h).mpr h'
/-
**ENat.sub_sub_cancel** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {a b : ℕ∞}, a ≠ ⊤ → b ≤ a → a - (a - b) = b
参数：a - b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.tsub_tsub_cancel_of_le`：∀ {α : Type u_1} [inst : AddCom
mSemigroup α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]   [ins
t_4 : Sub α] [OrderedSub α] {…
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instOrderedSubENat`：OrderedSub ℕ∞
· 使用引理 `ENat.addLECancellable_of_ne_top`：addLECancellable_of_ne_top : a != ⊤ -> 
AddLECancellable a
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `tsub_le_self`：tsub_le_self : a - b <= a
-/
protected lemma sub_sub_cancel (h : a ≠ ⊤) (h2 : b ≤ a) : a - (a - b) = b :=
  (addLECancellable_of_ne_top <| ne_top_of_le_ne_top h tsub_le_self).tsub_tsub_cancel_of_le h2
/-
**ENat.add_left_injective_of_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：add_left_injective_of_ne_top {n : Nat∞} (hn : n != ⊤) : Function.Injective
 (· + n)
参数：hn : n != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `WithTop.add_le_add_iff_right`：∀ {α : Type u} [inst : Add α] {x y z : Wit
hTop α} [inst_1 : LE α] [AddRightMono α] [AddRightReflectLE α],   z ≠ ⊤ → (x + z
 ≤ y + z ↔ x ≤ y)
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
-/
lemma add_left_injective_of_ne_top {n : ℕ∞} (hn : n ≠ ⊤) : Function.Injective (· + n) := by
  intro a b e
  exact le_antisymm
    ((WithTop.add_le_add_iff_right hn).mp e.le)
    ((WithTop.add_le_add_iff_right hn).mp e.ge)
/-
**ENat.add_right_injective_of_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：add_right_injective_of_ne_top {n : Nat∞} (hn : n != ⊤) : Function.Injectiv
e (n + ·)
参数：hn : n != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `ENat.add_left_injective_of_ne_top`：add_left_injective_of_ne_top {n : Nat
∞} (hn : n != ⊤) : Function.Injective (· + n)
-/
lemma add_right_injective_of_ne_top {n : ℕ∞} (hn : n ≠ ⊤) : Function.Injective (n + ·) := by
  simp_rw [add_comm n _]
  exact add_left_injective_of_ne_top hn
/-
**ENat.mul_right_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：mul_right_strictMono (ha : a != 0) (h_top : a != ⊤) : StrictMono (a * ·)
参数：ha : a != 0；h_top : a != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.mul_right_strictMono`：∀ {α : Type u_1} [inst : DecidableEq α] [i
nst_1 : MulZeroClass α] {a : WithTop α} [inst_2 : Preorder α]   [PosMulStrictMon
o α], 0 < a → a ≠ …
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `WithTop.instIsBotZeroClass`：∀ {α : Type u} [inst : Zero α] [inst_1 : LE 
α] [IsBotZeroClass α], IsBotZeroClass (WithTop α)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
lemma mul_right_strictMono (ha : a ≠ 0) (h_top : a ≠ ⊤) : StrictMono (a * ·) :=
  WithTop.mul_right_strictMono (pos_iff_ne_zero.2 ha) h_top
/-
**ENat.mul_left_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：mul_left_strictMono (ha : a != 0) (h_top : a != ⊤) : StrictMono (· * a)
参数：ha : a != 0；h_top : a != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.mul_left_strictMono`：∀ {α : Type u_1} [inst : DecidableEq α] [in
st_1 : MulZeroClass α] {a : WithTop α} [inst_2 : Preorder α]   [MulPosStrictMono
 α], 0 < a → a ≠ …
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `WithTop.instIsBotZeroClass`：∀ {α : Type u} [inst : Zero α] [inst_1 : LE 
α] [IsBotZeroClass α], IsBotZeroClass (WithTop α)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
lemma mul_left_strictMono (ha : a ≠ 0) (h_top : a ≠ ⊤) : StrictMono (· * a) :=
  WithTop.mul_left_strictMono (pos_iff_ne_zero.2 ha) h_top

@[simp]
/-
**ENat.mul_le_mul_left_iff** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：mul_le_mul_left_iff {x y : Nat∞} (ha : a != 0) (h_top : a != ⊤) : a * x <=
 a * y ↔ x <= y
参数：ha : a != 0；h_top : a != ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用引理 `ENat.mul_right_strictMono`：mul_right_strictMono (ha : a != 0) (h_top : a
 != ⊤) : StrictMono (a * ·)
-/
lemma mul_le_mul_left_iff {x y : ℕ∞} (ha : a ≠ 0) (h_top : a ≠ ⊤) : a * x ≤ a * y ↔ x ≤ y :=
  (ENat.mul_right_strictMono ha h_top).le_iff_le

@[simp]
/-
**ENat.mul_le_mul_right_iff** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：mul_le_mul_right_iff {x y : Nat∞} (ha : a != 0) (h_top : a != ⊤) : x * a <
= y * a ↔ x <= y
参数：ha : a != 0；h_top : a != ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用引理 `ENat.mul_left_strictMono`：mul_left_strictMono (ha : a != 0) (h_top : a !
= ⊤) : StrictMono (· * a)
-/
lemma mul_le_mul_right_iff {x y : ℕ∞} (ha : a ≠ 0) (h_top : a ≠ ⊤) : x * a ≤ y * a ↔ x ≤ y :=
  (ENat.mul_left_strictMono ha h_top).le_iff_le

@[gcongr]
/-
**ENat.mul_le_mul_of_le_right** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：mul_le_mul_of_le_right {x y : Nat∞} (hxy : x <= y) (ha : a != 0) (h_top : 
a != ⊤) : x * a <= y * a
参数：hxy : x <= y；ha : a != 0；h_top : a != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma mul_le_mul_of_le_right {x y : ℕ∞} (hxy : x ≤ y) (ha : a ≠ 0) (h_top : a ≠ ⊤) :
    x * a ≤ y * a := by
  simpa [ha, h_top]
/-
**ENat.self_le_mul_right** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：self_le_mul_right (a : Nat∞) (hc : c != 0) : a <= a * c
参数：a : Nat∞；hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENat.top_mul`：∀ {m : ℕ∞}, m ≠ 0 → ⊤ * m = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `ENat.mul_le_mul_left_iff`：mul_le_mul_left_iff {x y : Nat∞} (ha : a != 0)
 (h_top : a != ⊤) : a * x <= a * y ↔ x <= y
· 使用定理 `Order.one_le_iff_ne_zero`：one_le_iff_ne_zero [AddMonoidWithOne α] [NeZer
o (1 : α)] [SuccAddOrder α] [IsBotZeroClass α] : 1 <= x ↔ x != 0
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
-/
lemma self_le_mul_right (a : ℕ∞) (hc : c ≠ 0) : a ≤ a * c := by
  obtain rfl | hne := eq_or_ne a ⊤
  · simp [top_mul hc]
  obtain rfl | h0 := eq_or_ne a 0
  · simp
  nth_rewrite 1 [← mul_one a, ENat.mul_le_mul_left_iff h0 hne, Order.one_le_iff_ne_zero]
  assumption
/-
**ENat.self_le_mul_left** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：self_le_mul_left (a : Nat∞) (hc : c != 0) : a <= c * a
参数：a : Nat∞；hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `ENat.self_le_mul_right`：self_le_mul_right (a : Nat∞) (hc : c != 0) : a <
= a * c
-/
lemma self_le_mul_left (a : ℕ∞) (hc : c ≠ 0) : a ≤ c * a := by
  rw [mul_comm]
  exact ENat.self_le_mul_right a hc
/-
**ENat.** 是 Mathlib 中的一个实例，位于命名空间 `ENat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Unique ℕ∞ˣ where
  uniq x := by
    have := x.val_inv
    have x_top : x.val ≠ ⊤ := by
      intro h
      simp [h] at this
    have x_inv_top : x.inv ≠ ⊤ := by
      intro h
      simp only [h, ne_eq, x.ne_zero, not_false_eq_true, mul_top, top_ne_one] at this
    obtain ⟨y, x_y⟩ := ne_top_iff_exists.1 x_top
    obtain ⟨z, x_z⟩ := ne_top_iff_exists.1 x_inv_top
    replace x_y := x_y.symm
    rw [x_y, ← x_z, ← natCast_mul, ← natCast_one, natCast_inj, _root_.mul_eq_one] at this
    rwa [this.1, Nat.cast_one, Units.val_eq_one] at x_y

section withTop_enat

/-
**ENat.add_one_natCast_le_withTop_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：add_one_natCast_le_withTop_of_lt {m : Nat} {n : WithTop Nat∞} (h : m < n) 
: (m + 1 : Nat) <= n
参数：h : m < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `WithTop.coe_le_coe`：∀ {α : Type u_1} {a b : α} [inst : LE α], ↑b ≤ ↑a ↔ 
b ≤ a
· 使用定理 `OrderTop.le_top`：∀ {α : Type u} {inst : LE α} [self : OrderTop α] (a : α
), a ≤ ⊤
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
lemma add_one_natCast_le_withTop_of_lt {m : ℕ} {n : WithTop ℕ∞} (h : m < n) : (m + 1 : ℕ) ≤ n := by
  match n with
  | ⊤ => exact le_top
  | (⊤ : ℕ∞) => exact WithTop.coe_le_coe.2 (OrderTop.le_top _)
  | (n : ℕ) => simpa only [Nat.cast_le, ge_iff_le, Nat.cast_lt] using! h
/-
**ENat.coe_top_add_one** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：↑⊤ + 1 = ↑⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_top_add_one : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 = (⊤ : ℕ∞) := rfl
/-
**ENat.add_one_eq_coe_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {n : WithTop ℕ∞}, n + 1 = ↑⊤ ↔ n = ↑⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
-/
@[simp] lemma add_one_eq_coe_top_iff {n : WithTop ℕ∞} : n + 1 = (⊤ : ℕ∞) ↔ n = (⊤ : ℕ∞) := by
  match n with
  | ⊤ => exact Iff.rfl
  | (⊤ : ℕ∞) => simp
  | (n : ℕ) =>
    norm_cast
    simp only [natCast_ne_top]
/-
**ENat.natCast_ne_coe_top** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ (n : ℕ), ↑n ≠ ↑⊤
参数：n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma natCast_ne_coe_top (n : ℕ) : (n : WithTop ℕ∞) ≠ (⊤ : ℕ∞) := nofun
/-
**ENat.one_le_iff_ne_zero_withTop** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：one_le_iff_ne_zero_withTop {n : WithTop Nat∞} : 1 <= n ↔ n != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `WithTop.nontrivial`：∀ {α : Type u_1} [Nonempty α], Nontrivial (WithTop α
)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `ENat.add_one_natCast_le_withTop_of_lt`：add_one_natCast_le_withTop_of_lt 
{m : Nat} {n : WithTop Nat∞} (h : m < n) : (m + 1 : Nat) <= n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `WithTop.instIsBotZeroClass`：∀ {α : Type u} [inst : Zero α] [inst_1 : LE 
α] [IsBotZeroClass α], IsBotZeroClass (WithTop α)
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
-/
lemma one_le_iff_ne_zero_withTop {n : WithTop ℕ∞} : 1 ≤ n ↔ n ≠ 0 :=
  ⟨fun h ↦ (zero_lt_one.trans_le h).ne',
    fun h ↦ add_one_natCast_le_withTop_of_lt (pos_iff_ne_zero.mpr h)⟩
/-
**ENat.natCast_le_of_coe_top_le_withTop** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：natCast_le_of_coe_top_le_withTop {N : WithTop Nat∞} (hN : (⊤ : Nat∞) <= N)
 (n : Nat) : n <= N
参数：hN : (⊤ : Nat∞) <= N；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_top`：le_top : a <= ⊤
-/
lemma natCast_le_of_coe_top_le_withTop {N : WithTop ℕ∞} (hN : (⊤ : ℕ∞) ≤ N) (n : ℕ) : n ≤ N :=
  le_trans (mod_cast le_top) hN
/-
**ENat.natCast_lt_of_coe_top_le_withTop** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：natCast_lt_of_coe_top_le_withTop {N : WithTop Nat∞} (hN : (⊤ : Nat∞) <= N)
 (n : Nat) : n < N
参数：hN : (⊤ : Nat∞) <= N；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用引理 `ENat.natCast_le_of_coe_top_le_withTop`：natCast_le_of_coe_top_le_withTop 
{N : WithTop Nat∞} (hN : (⊤ : Nat∞) <= N) (n : Nat) : n <= N
-/
lemma natCast_lt_of_coe_top_le_withTop {N : WithTop ℕ∞} (hN : (⊤ : ℕ∞) ≤ N) (n : ℕ) : n < N :=
  lt_of_lt_of_le (mod_cast lt_add_one n) (natCast_le_of_coe_top_le_withTop hN (n + 1))

end withTop_enat

variable {α : Type*}

/--
Specialization of `WithTop.map` to `ENat`.
-/
/-
**ENat.map** 是 Mathlib 中的一个定义，位于命名空间 `ENat`。
形式化陈述：map (f : Nat -> α) (k : Nat∞) : WithTop α
参数：f : Nat -> α；k : Nat∞。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Specialization of `WithTop.map` to `ENat`.
-/
def map (f : ℕ → α) (k : ℕ∞) : WithTop α := WithTop.map f k

@[simp]
/-
**ENat.map_top** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：map_top (f : Nat -> α) : map f ⊤ = ⊤
参数：f : Nat -> α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_top (f : ℕ → α) : map f ⊤ = ⊤ := rfl

@[simp]
/-
**ENat.map_natCast** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：map_natCast (f : Nat -> α) (a : Nat) : map f a = f a
参数：f : Nat -> α；a : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_natCast (f : ℕ → α) (a : ℕ) : map f a = f a := rfl

@[deprecated (since := "2026-07-17")] alias map_coe := map_natCast

@[simp]
/-
**ENat.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {α : Type u_1} (f : ℕ → α), ENat.map f 0 = ↑(f 0)
参数：f : ℕ → α；f 0。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem map_zero (f : ℕ → α) : map f 0 = f 0 := rfl

@[simp]
/-
**ENat.map_one** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {α : Type u_1} (f : ℕ → α), ENat.map f 1 = ↑(f 1)
参数：f : ℕ → α；f 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem map_one (f : ℕ → α) : map f 1 = f 1 := rfl

@[simp]
/-
**ENat.map_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：map_ofNat (f : Nat -> α) (n : Nat) [n.AtLeastTwo] : map f ofNat(n) = f n
参数：f : Nat -> α；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_ofNat (f : ℕ → α) (n : ℕ) [n.AtLeastTwo] : map f ofNat(n) = f n := rfl

@[simp]
/-
**ENat.map_eq_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：map_eq_top_iff {f : Nat -> α} : map f n = ⊤ ↔ n = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.map_eq_top_iff`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {a :
 WithTop α}, WithTop.map f a = ⊤ ↔ a = ⊤
-/
lemma map_eq_top_iff {f : ℕ → α} : map f n = ⊤ ↔ n = ⊤ := WithTop.map_eq_top_iff

@[simp]
/-
**ENat.strictMono_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：strictMono_map_iff {f : Nat -> α} [Preorder α] : StrictMono (ENat.map f) ↔
 StrictMono f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.strictMono_map_iff`：∀ {α : Type u_1} {β : Type u_2} [inst : Preo
rder α] [inst_1 : Preorder β] {f : α → β},   StrictMono (WithTop.map f) ↔ Strict
Mono f
-/
theorem strictMono_map_iff {f : ℕ → α} [Preorder α] : StrictMono (ENat.map f) ↔ StrictMono f :=
  WithTop.strictMono_map_iff

@[simp]
/-
**ENat.monotone_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：monotone_map_iff {f : Nat -> α} [Preorder α] : Monotone (ENat.map f) ↔ Mon
otone f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.monotone_map_iff`：∀ {α : Type u_1} {β : Type u_2} [inst : Preord
er α] [inst_1 : Preorder β] {f : α → β},   Monotone (WithTop.map f) ↔ Monotone f
-/
theorem monotone_map_iff {f : ℕ → α} [Preorder α] : Monotone (ENat.map f) ↔ Monotone f :=
  WithTop.monotone_map_iff

section AddMonoidWithOne
variable [AddMonoidWithOne α] [PartialOrder α] [AddLeftMono α] [ZeroLEOneClass α]

/-
**ENat.map_natCast_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {n : ℕ∞} {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : PartialOrd
er α] [AddLeftMono α] [ZeroLEOneClass α],   0 ≤ ENat.map Nat.cast n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma map_natCast_nonneg : 0 ≤ n.map (Nat.cast : ℕ → α) := by cases n <;> simp

variable [CharZero α]
/-
**ENat.map_natCast_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：map_natCast_strictMono : StrictMono (map (Nat.cast : Nat -> α))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENat.strictMono_map_iff`：strictMono_map_iff {f : Nat -> α} [Preorder α] 
: StrictMono (ENat.map f) ↔ StrictMono f
· 使用定理 `Nat.strictMono_cast`：strictMono_cast : StrictMono (Nat.cast : Nat -> α)
-/
lemma map_natCast_strictMono : StrictMono (map (Nat.cast : ℕ → α)) :=
  strictMono_map_iff.2 Nat.strictMono_cast
/-
**ENat.map_natCast_injective** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：map_natCast_injective : Injective (map (Nat.cast : Nat -> α))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用引理 `ENat.map_natCast_strictMono`：map_natCast_strictMono : StrictMono (map (N
at.cast : Nat -> α))
-/
lemma map_natCast_injective : Injective (map (Nat.cast : ℕ → α)) := map_natCast_strictMono.injective
/-
**ENat.map_natCast_inj** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {m n : ℕ∞} {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : PartialO
rder α] [AddLeftMono α] [ZeroLEOneClass α]   [CharZero α], ENat.map Nat.cast m =
 ENat.map Nat.cast n ↔ m = n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `ENat.map_natCast_injective`：map_natCast_injective : Injective (map (Nat.
cast : Nat -> α))
-/
@[simp] lemma map_natCast_inj : m.map (Nat.cast : ℕ → α) = n.map Nat.cast ↔ m = n :=
  map_natCast_injective.eq_iff
/-
**ENat.map_natCast_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {n : ℕ∞} {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : PartialOrd
er α] [AddLeftMono α] [ZeroLEOneClass α]   [CharZero α], ENat.map Nat.cast n = 0
 ↔ n = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.map_natCast_inj`：∀ {m n : ℕ∞} {α : Type u_1} [inst : AddMonoidWithO
ne α] [inst_1 : PartialOrder α] [AddLeftMono α] [ZeroLEOneClass α]   [CharZero α
], ENat.ma…
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma map_natCast_eq_zero : n.map (Nat.cast : ℕ → α) = 0 ↔ n = 0 := by
  simp [← map_natCast_inj (α := α)]

end AddMonoidWithOne

@[simp]
/-
**ENat.map_add** 是 Mathlib 中的一个定理，位于命名空间 `ENat`。
形式化陈述：∀ {β : Type u_2} {F : Type u_3} [inst : Add β] [inst_1 : FunLike F ℕ β] [A
ddHomClass F ℕ β] (f : F) (a b : ℕ∞),   ENat.map (⇑f) (a + b) = ENat.map (⇑f) a 
+ ENat.map (⇑f) b
参数：f : F；a b : ℕ∞；⇑f；a + b；⇑f；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.map_add`：∀ {α : Type u} {β : Type v} [inst : Add α] {F : Type u_
1} [inst_1 : Add β] [inst_2 : FunLike F α β] [AddHomClass F α β]   (f : F) (a b 
: Wit…
-/
protected theorem map_add {β F} [Add β] [FunLike F ℕ β] [AddHomClass F ℕ β]
    (f : F) (a b : ℕ∞) : (a + b).map f = a.map f + b.map f :=
  WithTop.map_add f a b

/-- A version of `ENat.map` for `OneHom`s. -/
-- @[to_additive (attr := simps -fullyApplied)
--   "A version of `ENat.map` for `ZeroHom`s"]
/-
**ENat._root_.OneHom.ENatMap** 是 Mathlib 中的一个定义，位于命名空间 `ENat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def _root_.OneHom.ENatMap {N : Type*} [One N] (f : OneHom ℕ N) :
    OneHom ℕ∞ (WithTop N) where
  toFun := ENat.map f
  map_one' := by simp

/-- A version of `ENat.map` for `ZeroHom`s. -/
/-
**ENat._root_.ZeroHom.ENatMap** 是 Mathlib 中的一个定义，位于命名空间 `ENat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `ENat.map` for `ZeroHom`s.
-/
protected def _root_.ZeroHom.ENatMap {N : Type*} [Zero N] (f : ZeroHom ℕ N) :
    ZeroHom ℕ∞ (WithTop N) where
  toFun := ENat.map f
  map_zero' := by simp

/-- A version of `WithTop.map` for `AddHom`s. -/
@[simps -fullyApplied]
/-
**ENat._root_.AddHom.ENatMap** 是 Mathlib 中的一个定义，位于命名空间 `ENat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `WithTop.map` for `AddHom`s.
-/
protected def _root_.AddHom.ENatMap {N : Type*} [Add N] (f : AddHom ℕ N) :
    AddHom ℕ∞ (WithTop N) where
  toFun := ENat.map f
  map_add' := ENat.map_add f

/-- A version of `WithTop.map` for `AddMonoidHom`s. -/
@[simps -fullyApplied]
/-
**ENat._root_.AddMonoidHom.ENatMap** 是 Mathlib 中的一个定义，位于命名空间 `ENat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `WithTop.map` for `AddMonoidHom`s.
-/
protected def _root_.AddMonoidHom.ENatMap {N : Type*} [AddZeroClass N]
    (f : ℕ →+ N) : ℕ∞ →+ WithTop N :=
  { ZeroHom.ENatMap f.toZeroHom, AddHom.ENatMap f.toAddHom with toFun := ENat.map f }

/-- A version of `ENat.map` for `MonoidWithZeroHom`s. -/
@[simps -fullyApplied]
/-
**ENat._root_.MonoidWithZeroHom.ENatMap** 是 Mathlib 中的一个定义，位于命名空间 `ENat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `ENat.map` for `MonoidWithZeroHom`s.
-/
protected def _root_.MonoidWithZeroHom.ENatMap {S : Type*} [MulZeroOneClass S] [DecidableEq S]
    [Nontrivial S] (f : ℕ →*₀ S)
    (hf : Function.Injective f) : ℕ∞ →*₀ WithTop S :=
  { f.toZeroHom.ENatMap, f.toMonoidHom.toOneHom.ENatMap with
    toFun := ENat.map f
    map_mul' := fun x y => by
      have : ∀ z, map f z = 0 ↔ z = 0 := fun z =>
        (WithTop.map_injective hf).eq_iff' f.toZeroHom.ENatMap.map_zero
      rcases Decidable.eq_or_ne x 0 with (rfl | hx)
      · simp
      rcases Decidable.eq_or_ne y 0 with (rfl | hy)
      · simp
      induction x with
      | top => simp [hy, this]
      | coe x =>
        induction y with
        | top =>
          have : (f x : WithTop S) ≠ 0 := by simpa [hf.eq_iff' (map_zero f)] using hx
          simp [mul_top hx, WithTop.mul_top this]
        | coe y => simp [← Nat.cast_mul, -natCast_mul] }

/-- A version of `ENat.map` for `RingHom`s. -/
@[simps -fullyApplied]
/-
**ENat._root_.RingHom.ENatMap** 是 Mathlib 中的一个定义，位于命名空间 `ENat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `ENat.map` for `RingHom`s.
-/
protected def _root_.RingHom.ENatMap {S : Type*} [CommSemiring S] [PartialOrder S]
    [CanonicallyOrderedAdd S]
    [DecidableEq S] [Nontrivial S] (f : ℕ →+* S) (hf : Function.Injective f) : ℕ∞ →+* WithTop S :=
  { MonoidWithZeroHom.ENatMap f.toMonoidWithZeroHom hf, f.toAddMonoidHom.ENatMap with }

@[simp]
/-
**ENat.map_natCast_mul** 是 Mathlib 中的一个引理，位于命名空间 `ENat`。
形式化陈述：map_natCast_mul {R : Type*} [NonAssocSemiring R] [DecidableEq R] [CharZero
 R] (a b : Nat∞) : (map Nat.cast (a * b) : WithTop R) = map Nat.cast a * map Nat
.cast b
参数：a b : Nat∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Nat.cast_injective`：cast_injective : Function.Injective (Nat.cast : Nat 
-> R)
-/
lemma map_natCast_mul {R : Type*} [NonAssocSemiring R] [DecidableEq R] [CharZero R] (a b : ℕ∞) :
    (map Nat.cast (a * b) : WithTop R) = map Nat.cast a * map Nat.cast b :=
  map_mul ((.ofClass (Nat.castRingHom R) : ℕ →*₀ R).ENatMap Nat.cast_injective) a b

end ENat

namespace ENat.WithBot

@[simp]
/-
**ENat.WithBot.coe_eq_natCast** 是 Mathlib 中的一个引理，位于命名空间 `ENat.WithBot`。
形式化陈述：coe_eq_natCast (n : Nat) : (n : Nat∞) = (n : WithBot Nat∞)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_eq_natCast (n : ℕ) : (n : ℕ∞) = (n : WithBot ℕ∞) := rfl
/-
**ENat.WithBot.eq_top_iff_forall_ge** 是 Mathlib 中的一个引理，位于命名空间 `ENat.WithBot`。
形式化陈述：eq_top_iff_forall_ge {n : WithBot Nat∞} : n = ⊤ ↔ forall m : Nat, m <= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithBot.eq_top_iff_forall_ge`：eq_top_iff_forall_ge [Nonempty α] [NoTopOr
der α] {x : WithBot (WithTop α)} : x = ⊤ ↔ forall a : α, a <= x
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
-/
lemma eq_top_iff_forall_ge {n : WithBot ℕ∞} : n = ⊤ ↔ ∀ m : ℕ, m ≤ n :=
  _root_.WithBot.eq_top_iff_forall_ge
/-
**ENat.WithBot.lt_add_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `ENat.WithBot`。
形式化陈述：lt_add_one_iff {n : WithBot Nat∞} {m : Nat} : n < m + 1 ↔ n <= m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithBot.coe_one`：∀ {α : Type u} [inst : One α], ↑1 = 1
· 使用定理 `ENat.natCast_one`：natCast_one : ((1 : Nat) : Nat∞) = 1
· 使用定理 `WithBot.coe_natCast`：∀ {α : Type u} [inst : AddMonoidWithOne α] (n : ℕ),
 ↑↑n = ↑n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `WithBot.coe_lt_coe`：coe_lt_coe : (a : WithBot α) < b ↔ a < b
· 使用定理 `ENat.lt_add_one_iff`：lt_add_one_iff (hn : n != ⊤) : m < n + 1 ↔ m <= n
· 使用定理 `ENat.natCast_ne_top`：natCast_ne_top (a : Nat) : (a : Nat∞) != ⊤
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma lt_add_one_iff {n : WithBot ℕ∞} {m : ℕ} : n < m + 1 ↔ n ≤ m := by
  rw [← WithBot.coe_one, ← ENat.natCast_one, WithBot.coe_natCast, ← Nat.cast_add,
    ← WithBot.coe_natCast]
  cases n
  · simp only [bot_le, WithBot.bot_lt_coe]
  · rw [WithBot.coe_lt_coe, Nat.cast_add, natCast_one, ENat.lt_add_one_iff (natCast_ne_top _),
      ← WithBot.coe_le_coe, WithBot.coe_natCast]
/-
**ENat.WithBot.add_one_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `ENat.WithBot`。
形式化陈述：add_one_le_iff {n : Nat} {m : WithBot Nat∞} : n + 1 <= m ↔ n < m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithBot.coe_one`：∀ {α : Type u} [inst : One α], ↑1 = 1
· 使用定理 `ENat.natCast_one`：natCast_one : ((1 : Nat) : Nat∞) = 1
· 使用定理 `WithBot.coe_natCast`：∀ {α : Type u} [inst : AddMonoidWithOne α] (n : ℕ),
 ↑↑n = ↑n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用定理 `ENat.natCast_add`：natCast_add (m n : Nat) : ↑(m + n) = (m + n : Nat∞)
· 使用定理 `ENat.add_one_le_iff`：add_one_le_iff (hm : m != ⊤) : m + 1 <= n ↔ m < n
· 使用定理 `ENat.natCast_ne_top`：natCast_ne_top (a : Nat) : (a : Nat∞) != ⊤
· 使用引理 `WithBot.coe_lt_coe`：coe_lt_coe : (a : WithBot α) < b ↔ a < b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma add_one_le_iff {n : ℕ} {m : WithBot ℕ∞} : n + 1 ≤ m ↔ n < m := by
  rw [← WithBot.coe_one, ← natCast_one, WithBot.coe_natCast, ← Nat.cast_add, ← WithBot.coe_natCast]
  cases m
  · simp
  · rw [WithBot.coe_le_coe, natCast_add, natCast_one, ENat.add_one_le_iff (natCast_ne_top n),
      ← WithBot.coe_lt_coe, WithBot.coe_natCast]
/-
**ENat.WithBot.add_one_le_natCast_iff** 是 Mathlib 中的一个引理，位于命名空间 `ENat.WithBot`。
形式化陈述：add_one_le_natCast_iff {n : WithBot Nat∞} {m : Nat} : n + 1 <= m ↔ n < m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma add_one_le_natCast_iff {n : WithBot ℕ∞} {m : ℕ} : n + 1 ≤ m ↔ n < m := by
  induction n with
  | bot => simp
  | coe n =>
    norm_cast
    simp [add_one_le_iff']

@[simp]
/-
**ENat.WithBot.add_one_le_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `ENat.WithBot`。
形式化陈述：add_one_le_zero_iff (n : WithBot Nat∞) : n + 1 <= 0 ↔ n = ⊥
参数：n : WithBot Nat∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `ENat.WithBot.add_one_le_natCast_iff`：add_one_le_natCast_iff {n : WithBot
 Nat∞} {m : Nat} : n + 1 <= m ↔ n < m
· 使用引理 `WithBot.lt_zero_iff_eq_bot`：lt_zero_iff_eq_bot {α : Type*} [AddMonoid α]
 [Preorder α] [CanonicallyOrderedAdd α] (a : WithBot α) : a < 0 ↔ a = ⊥
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
-/
lemma add_one_le_zero_iff (n : WithBot ℕ∞) : n + 1 ≤ 0 ↔ n = ⊥ :=
  add_one_le_natCast_iff.trans (WithBot.lt_zero_iff_eq_bot n)

@[simp]
/-
**ENat.WithBot.add_natCast_cancel** 是 Mathlib 中的一个引理，位于命名空间 `ENat.WithBot`。
形式化陈述：add_natCast_cancel {a b : WithBot Nat∞} {c : Nat} : a + c = b + c ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `IsAddRightRegular.withBot`：∀ {α : Type u} [inst : Add α] {a : α}, IsAddR
ightRegular a → IsAddRightRegular ↑a
· 使用定理 `IsAddRightRegular.withTop`：∀ {α : Type u} [inst : Add α] {a : α}, IsAddR
ightRegular a → IsAddRightRegular ↑a
· 使用定理 `IsAddRightRegular.all`：∀ {R : Type u_2} [inst : Add R] [IsRightCancelAdd
 R] (g : R), IsAddRightRegular g
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
lemma add_natCast_cancel {a b : WithBot ℕ∞} {c : ℕ} : a + c = b + c ↔ a = b :=
  (IsAddRightRegular.all c).withTop.withBot.eq_iff

@[simp]
/-
**ENat.WithBot.add_one_cancel** 是 Mathlib 中的一个引理，位于命名空间 `ENat.WithBot`。
形式化陈述：add_one_cancel {a b : WithBot Nat∞} : a + 1 = b + 1 ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `IsAddRightRegular.withBot`：∀ {α : Type u} [inst : Add α] {a : α}, IsAddR
ightRegular a → IsAddRightRegular ↑a
· 使用定理 `IsAddRightRegular.withTop`：∀ {α : Type u} [inst : Add α] {a : α}, IsAddR
ightRegular a → IsAddRightRegular ↑a
· 使用定理 `IsAddRightRegular.all`：∀ {R : Type u_2} [inst : Add R] [IsRightCancelAdd
 R] (g : R), IsAddRightRegular g
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
lemma add_one_cancel {a b : WithBot ℕ∞} : a + 1 = b + 1 ↔ a = b :=
  (IsAddRightRegular.all 1).withTop.withBot.eq_iff
/-
**ENat.WithBot.add_ofNat_cancel** 是 Mathlib 中的一个引理，位于命名空间 `ENat.WithBot`。
形式化陈述：add_ofNat_cancel {a b : WithBot Nat∞} {c : Nat} [c.AtLeastTwo] : a + ofNat
(c) = b + ofNat(c) ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENat.WithBot.add_natCast_cancel`：add_natCast_cancel {a b : WithBot Nat∞}
 {c : Nat} : a + c = b + c ↔ a = b
-/
lemma add_ofNat_cancel {a b : WithBot ℕ∞} {c : ℕ} [c.AtLeastTwo] :
    a + ofNat(c) = b + ofNat(c) ↔ a = b :=
  WithBot.add_natCast_cancel

@[simp]
/-
**ENat.WithBot.natCast_add_cancel** 是 Mathlib 中的一个引理，位于命名空间 `ENat.WithBot`。
形式化陈述：natCast_add_cancel {a b : WithBot Nat∞} {c : Nat} : c + a = c + b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `IsAddLeftRegular.withBot`：∀ {α : Type u} [inst : Add α] {a : α}, IsAddLe
ftRegular a → IsAddLeftRegular ↑a
· 使用定理 `IsAddLeftRegular.withTop`：∀ {α : Type u} [inst : Add α] {a : α}, IsAddLe
ftRegular a → IsAddLeftRegular ↑a
· 使用定理 `IsAddLeftRegular.all`：∀ {R : Type u_2} [inst : Add R] [IsLeftCancelAdd R
] (g : R), IsAddLeftRegular g
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
-/
lemma natCast_add_cancel {a b : WithBot ℕ∞} {c : ℕ} : c + a = c + b ↔ a = b :=
  (IsAddLeftRegular.all c).withTop.withBot.eq_iff

@[simp]
/-
**ENat.WithBot.one_add_cancel** 是 Mathlib 中的一个引理，位于命名空间 `ENat.WithBot`。
形式化陈述：one_add_cancel {a b : WithBot Nat∞} : 1 + a = 1 + b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `IsAddLeftRegular.withBot`：∀ {α : Type u} [inst : Add α] {a : α}, IsAddLe
ftRegular a → IsAddLeftRegular ↑a
· 使用定理 `IsAddLeftRegular.withTop`：∀ {α : Type u} [inst : Add α] {a : α}, IsAddLe
ftRegular a → IsAddLeftRegular ↑a
· 使用定理 `IsAddLeftRegular.all`：∀ {R : Type u_2} [inst : Add R] [IsLeftCancelAdd R
] (g : R), IsAddLeftRegular g
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
-/
lemma one_add_cancel {a b : WithBot ℕ∞} : 1 + a = 1 + b ↔ a = b :=
  (IsAddLeftRegular.all 1).withTop.withBot.eq_iff
/-
**ENat.WithBot.ofNat_add_cancel** 是 Mathlib 中的一个引理，位于命名空间 `ENat.WithBot`。
形式化陈述：ofNat_add_cancel {a b : WithBot Nat∞} {c : Nat} [c.AtLeastTwo] : ofNat(c) 
+ a = ofNat(c) + b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENat.WithBot.natCast_add_cancel`：natCast_add_cancel {a b : WithBot Nat∞}
 {c : Nat} : c + a = c + b ↔ a = b
-/
lemma ofNat_add_cancel {a b : WithBot ℕ∞} {c : ℕ} [c.AtLeastTwo] :
    ofNat(c) + a = ofNat(c) + b ↔ a = b :=
  WithBot.natCast_add_cancel
/-
**ENat.WithBot.add_le_add_natCast_right_iff** 是 Mathlib 中的一个引理，位于命名空间 `ENat.With
Bot`。
形式化陈述：add_le_add_natCast_right_iff {a b : WithBot Nat∞} {c : Nat} : a + c <= b +
 c ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddLECancellable.add_le_add_iff_right`：∀ {α : Type u_1} [inst : LE α] [i
nst_1 : Add α] [IsAddCommutative α] [AddLeftMono α] {a b c : α},   AddLECancella
ble a → (b + a ≤ c + a ↔ b …
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `AddLECancellable.withBot`：∀ {α : Type u} [inst : Add α] {a : α} [inst_1 
: LE α], AddLECancellable a → AddLECancellable ↑a
· 使用定理 `AddLECancellable.withTop`：∀ {α : Type u} [inst : Add α] {a : α} [inst_1 
: LE α], AddLECancellable a → AddLECancellable ↑a
· 使用定理 `Contravariant.AddLECancellable`：∀ {α : Type u_1} [inst : Add α] [inst_1 
: LE α] [AddLeftReflectLE α] {a : α}, AddLECancellable a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
-/
lemma add_le_add_natCast_right_iff {a b : WithBot ℕ∞} {c : ℕ} : a + c ≤ b + c ↔ a ≤ b :=
  (Contravariant.AddLECancellable (a := c)).withTop.withBot.add_le_add_iff_right
/-
**ENat.WithBot.add_le_add_one_right_iff** 是 Mathlib 中的一个引理，位于命名空间 `ENat.WithBot`
。
形式化陈述：add_le_add_one_right_iff {a b : WithBot Nat∞} : a + 1 <= b + 1 ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENat.WithBot.add_le_add_natCast_right_iff`：add_le_add_natCast_right_iff 
{a b : WithBot Nat∞} {c : Nat} : a + c <= b + c ↔ a <= b
-/
lemma add_le_add_one_right_iff {a b : WithBot ℕ∞} : a + 1 ≤ b + 1 ↔ a ≤ b :=
  WithBot.add_le_add_natCast_right_iff
/-
**ENat.WithBot.add_le_add_natCast_left_iff** 是 Mathlib 中的一个引理，位于命名空间 `ENat.WithB
ot`。
形式化陈述：add_le_add_natCast_left_iff {a b : WithBot Nat∞} {c : Nat} : c + a <= c + 
b ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `ENat.WithBot.add_le_add_natCast_right_iff`：add_le_add_natCast_right_iff 
{a b : WithBot Nat∞} {c : Nat} : a + c <= b + c ↔ a <= b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma add_le_add_natCast_left_iff {a b : WithBot ℕ∞} {c : ℕ} : c + a ≤ c + b ↔ a ≤ b := by
  rw [add_comm _ a, add_comm _ b, WithBot.add_le_add_natCast_right_iff]
/-
**ENat.WithBot.add_le_add_one_left_iff** 是 Mathlib 中的一个引理，位于命名空间 `ENat.WithBot`。
形式化陈述：add_le_add_one_left_iff {a b : WithBot Nat∞} : 1 + a <= 1 + b ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENat.WithBot.add_le_add_natCast_left_iff`：add_le_add_natCast_left_iff {a
 b : WithBot Nat∞} {c : Nat} : c + a <= c + b ↔ a <= b
-/
lemma add_le_add_one_left_iff {a b : WithBot ℕ∞} : 1 + a ≤ 1 + b ↔ a ≤ b :=
  WithBot.add_le_add_natCast_left_iff

end ENat.WithBot

