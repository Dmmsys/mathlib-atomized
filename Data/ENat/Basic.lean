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

There are two natural coercions from `ℕ` to `WithTop ℕ = ENat`: `WithTop.some` and `Nat.cast`. In
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

variable {a b c d m n : Nat∞}

/--
theorem `some_eq_natCast` / 定理 `some_eq_natCast`

English:
theorem some_eq_natCast
  statement: (WithTop.some : Nat -> Nat∞) = Nat.cast
  proof: rfl

@[deprecated (since := "2026-07-17")] alias some_eq_coe := some_eq_natCast

中文:
定理 some_eq_natCast
  结论: (WithTop.some : 自然数 -> 自然数∞) = 自然数.cast
  证明: rfl

@[deprecated (since := "2026-07-17")] alias some_eq_coe := some_eq_natCast
-/
@[simp] theorem some_eq_natCast : (WithTop.some : Nat -> Nat∞) = Nat.cast := rfl

@[deprecated (since := "2026-07-17")] alias some_eq_coe := some_eq_natCast

/--
theorem `natCast_inj` / 定理 `natCast_inj`

English:
theorem natCast_inj
  given: {a b : Nat}
  statement: (a : Nat∞) = b ↔ a = b
  proof: WithTop.coe_inj

@[deprecated (since := "2026-07-17")] alias coe_inj := natCast_inj

中文:
定理 natCast_inj
  条件: {a b : 自然数}
  结论: (a : 自然数∞) = b ↔ a = b
  证明: WithTop.coe_inj

@[deprecated (since := "2026-07-17")] alias coe_inj := natCast_inj

Depends on / 依赖: WithTop, WithTop.coe_inj, coe_inj
-/
theorem natCast_inj {a b : Nat} : (a : Nat∞) = b ↔ a = b := WithTop.coe_inj

@[deprecated (since := "2026-07-17")] alias coe_inj := natCast_inj

/--
theorem `succ_natCast` / 定理 `succ_natCast`

English:
theorem succ_natCast
  given: (n : Nat)
  statement: SuccOrder.succ (n : Nat∞) = (n + 1 : Nat)
  proof: WithTop.succ_coe

@[deprecated (since := "2026-07-17")] alias succ_coe := succ_natCast

中文:
定理 succ_natCast
  条件: (n : 自然数)
  结论: Succ序.succ (n : 自然数∞) = (n + 1 : 自然数)
  证明: WithTop.succ_coe

@[deprecated (since := "2026-07-17")] alias succ_coe := succ_natCast
-/
@[simp] theorem succ_natCast (n : Nat) : SuccOrder.succ (n : Nat∞) = (n + 1 : Nat) := WithTop.succ_coe

@[deprecated (since := "2026-07-17")] alias succ_coe := succ_natCast

/--
theorem `succ_top` / 定理 `succ_top`

English:
theorem succ_top
  statement: SuccOrder.succ (⊤ : Nat∞) = ⊤
  proof: rfl

中文:
定理 succ_top
  结论: Succ序.succ (⊤ : 自然数∞) = ⊤
  证明: rfl
-/
@[simp] theorem succ_top : SuccOrder.succ (⊤ : Nat∞) = ⊤ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SuccAddOrder Nat∞
  body: by cases x <;> simp

中文:
实例 :
  签名: SuccAdd序 自然数∞
  定义体: by cases x <;> simp
-/
instance : SuccAddOrder Nat∞ where
  succ_eq_add_one x := by cases x <;> simp

/--
theorem `natCast_zero` / 定理 `natCast_zero`

English:
theorem natCast_zero
  statement: ((0 : Nat) : Nat∞) = 0
  proof: rfl

@[deprecated (since := "2026-07-17")] alias coe_zero := natCast_zero

中文:
定理 natCast_zero
  结论: ((0 : 自然数) : 自然数∞) = 0
  证明: rfl

@[deprecated (since := "2026-07-17")] alias coe_zero := natCast_zero
-/
theorem natCast_zero : ((0 : Nat) : Nat∞) = 0 :=
  rfl

@[deprecated (since := "2026-07-17")] alias coe_zero := natCast_zero

/--
theorem `natCast_one` / 定理 `natCast_one`

English:
theorem natCast_one
  statement: ((1 : Nat) : Nat∞) = 1
  proof: rfl

@[deprecated (since := "2026-07-17")] alias coe_one := natCast_one

中文:
定理 natCast_one
  结论: ((1 : 自然数) : 自然数∞) = 1
  证明: rfl

@[deprecated (since := "2026-07-17")] alias coe_one := natCast_one
-/
theorem natCast_one : ((1 : Nat) : Nat∞) = 1 :=
  rfl

@[deprecated (since := "2026-07-17")] alias coe_one := natCast_one

/--
theorem `natCast_add` / 定理 `natCast_add`

English:
theorem natCast_add
  given: (m n : Nat)
  statement: ↑(m + n) = (m + n : Nat∞)
  proof: rfl

@[deprecated (since := "2026-07-17")] alias coe_add := natCast_add

@[simp, norm_cast]

中文:
定理 natCast_add
  条件: (m n : 自然数)
  结论: ↑(m + n) = (m + n : 自然数∞)
  证明: rfl

@[deprecated (since := "2026-07-17")] alias coe_add := natCast_add

@[simp, norm_cast]
-/
theorem natCast_add (m n : Nat) : ↑(m + n) = (m + n : Nat∞) :=
  rfl

@[deprecated (since := "2026-07-17")] alias coe_add := natCast_add

@[simp, norm_cast]
/--
theorem `natCast_sub` / 定理 `natCast_sub`

English:
theorem natCast_sub
  given: (m n : Nat)
  statement: ↑(m - n) = (m - n : Nat∞)
  proof: rfl

@[deprecated (since := "2026-07-17")] alias coe_sub := natCast_sub

中文:
定理 natCast_sub
  条件: (m n : 自然数)
  结论: ↑(m - n) = (m - n : 自然数∞)
  证明: rfl

@[deprecated (since := "2026-07-17")] alias coe_sub := natCast_sub
-/
theorem natCast_sub (m n : Nat) : ↑(m - n) = (m - n : Nat∞) :=
  rfl

@[deprecated (since := "2026-07-17")] alias coe_sub := natCast_sub

/--
lemma `natCast_mul` / 引理 `natCast_mul`

English:
lemma natCast_mul
  given: (m n : Nat)
  statement: ↑(m * n) = (m * n : Nat∞)
  proof: rfl

@[deprecated (since := "2026-07-17")] alias coe_mul := natCast_mul

中文:
引理 natCast_mul
  条件: (m n : 自然数)
  结论: ↑(m * n) = (m * n : 自然数∞)
  证明: rfl

@[deprecated (since := "2026-07-17")] alias coe_mul := natCast_mul
-/
@[simp] lemma natCast_mul (m n : Nat) : ↑(m * n) = (m * n : Nat∞) := rfl

@[deprecated (since := "2026-07-17")] alias coe_mul := natCast_mul

/--
theorem `mul_top` / 定理 `mul_top`

English:
theorem mul_top
  given: (hm : m != 0)
  statement: m * ⊤ = ⊤
  proof: WithTop.mul_top hm

中文:
定理 mul_top
  条件: (hm : m != 0)
  结论: m * ⊤ = ⊤
  证明: WithTop.mul_top hm
-/
@[simp] theorem mul_top (hm : m != 0) : m * ⊤ = ⊤ := WithTop.mul_top hm
/--
theorem `top_mul` / 定理 `top_mul`

English:
theorem top_mul
  given: (hm : m != 0)
  statement: ⊤ * m = ⊤
  proof: WithTop.top_mul hm

中文:
定理 top_mul
  条件: (hm : m != 0)
  结论: ⊤ * m = ⊤
  证明: WithTop.top_mul hm
-/
@[simp] theorem top_mul (hm : m != 0) : ⊤ * m = ⊤ := WithTop.top_mul hm

/--
theorem `mul_top'` / 定理 `mul_top'`

English:
theorem mul_top'
  statement: m * ⊤ = if m = 0 then 0 else ⊤
  proof: WithTop.mul_top' m

中文:
定理 mul_top'
  结论: m * ⊤ = if m = 0 then 0 else ⊤
  证明: WithTop.mul_top' m

Depends on / 依赖: WithTop, WithTop.mul_top, mul_top
-/
theorem mul_top' : m * ⊤ = if m = 0 then 0 else ⊤ := WithTop.mul_top' m

/--
theorem `top_mul'` / 定理 `top_mul'`

English:
theorem top_mul'
  statement: ⊤ * m = if m = 0 then 0 else ⊤
  proof: WithTop.top_mul' m

中文:
定理 top_mul'
  结论: ⊤ * m = if m = 0 then 0 else ⊤
  证明: WithTop.top_mul' m

Depends on / 依赖: WithTop, WithTop.top_mul, top_mul
-/
theorem top_mul' : ⊤ * m = if m = 0 then 0 else ⊤ := WithTop.top_mul' m

/--
lemma `top_pow` / 引理 `top_pow`

English:
lemma top_pow
  given: {n : Nat} (hn : n != 0)
  statement: (⊤ : Nat∞) ^ n = ⊤
  proof: WithTop.top_pow hn

中文:
引理 top_pow
  条件: {n : 自然数} (hn : n != 0)
  结论: (⊤ : 自然数∞) ^ n = ⊤
  证明: WithTop.top_pow hn
-/
@[simp] lemma top_pow {n : Nat} (hn : n != 0) : (⊤ : Nat∞) ^ n = ⊤ := WithTop.top_pow hn

/--
lemma `pow_eq_top_iff` / 引理 `pow_eq_top_iff`

English:
lemma pow_eq_top_iff
  given: {n : Nat}
  statement: a ^ n = ⊤ ↔ a = ⊤ ∧ n != 0
  proof: WithTop.pow_eq_top_iff

中文:
引理 pow_eq_top_iff
  条件: {n : 自然数}
  结论: a ^ n = ⊤ ↔ a = ⊤ ∧ n != 0
  证明: WithTop.pow_eq_top_iff
-/
@[simp] lemma pow_eq_top_iff {n : Nat} : a ^ n = ⊤ ↔ a = ⊤ ∧ n != 0 := WithTop.pow_eq_top_iff

/--
lemma `pow_ne_top_iff` / 引理 `pow_ne_top_iff`

English:
lemma pow_ne_top_iff
  given: {n : Nat}
  statement: a ^ n != ⊤ ↔ a != ⊤ ∨ n = 0
  proof: WithTop.pow_ne_top_iff

中文:
引理 pow_ne_top_iff
  条件: {n : 自然数}
  结论: a ^ n != ⊤ ↔ a != ⊤ ∨ n = 0
  证明: WithTop.pow_ne_top_iff

Depends on / 依赖: WithTop, WithTop.pow_ne_top_iff, pow_ne_top_iff
-/
lemma pow_ne_top_iff {n : Nat} : a ^ n != ⊤ ↔ a != ⊤ ∨ n = 0 := WithTop.pow_ne_top_iff

/--
lemma `pow_lt_top_iff` / 引理 `pow_lt_top_iff`

English:
lemma pow_lt_top_iff
  given: {n : Nat}
  statement: a ^ n < ⊤ ↔ a < ⊤ ∨ n = 0
  proof: WithTop.pow_lt_top_iff

中文:
引理 pow_lt_top_iff
  条件: {n : 自然数}
  结论: a ^ n < ⊤ ↔ a < ⊤ ∨ n = 0
  证明: WithTop.pow_lt_top_iff
-/
@[simp] lemma pow_lt_top_iff {n : Nat} : a ^ n < ⊤ ↔ a < ⊤ ∨ n = 0 := WithTop.pow_lt_top_iff

/--
lemma `eq_top_of_pow` / 引理 `eq_top_of_pow`

English:
lemma eq_top_of_pow
  given: (n : Nat) (ha : a ^ n = ⊤)
  statement: a = ⊤
  proof: WithTop.eq_top_of_pow n ha

中文:
引理 eq_top_of_pow
  条件: (n : 自然数) (ha : a ^ n = ⊤)
  结论: a = ⊤
  证明: WithTop.eq_top_of_pow n ha

Depends on / 依赖: WithTop, WithTop.eq_top_of_pow, eq_top_of_pow
-/
lemma eq_top_of_pow (n : Nat) (ha : a ^ n = ⊤) : a = ⊤ := WithTop.eq_top_of_pow n ha

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (x : Nat∞) (h : x < ⊤)
  body: WithTop.untop x (WithTop.lt_top_iff_ne_top.mp h)

中文:
定义 lift
  签名: (x : 自然数∞) (h : x < ⊤)
  定义体: WithTop.untop x (WithTop.lt_top_iff_ne_top.mp h)

Depends on / 依赖: WithTop, WithTop.lt_top_iff_ne_top.mp, WithTop.untop, lt_top_iff_ne_top
-/
def lift (x : Nat∞) (h : x < ⊤) : Nat := WithTop.untop x (WithTop.lt_top_iff_ne_top.mp h)

/--
theorem `natCast_lift` / 定理 `natCast_lift`

English:
theorem natCast_lift
  given: (x : Nat∞) (h : x < ⊤)
  statement: (lift x h : Nat∞) = x
  proof: WithTop.coe_untop x (WithTop.lt_top_iff_ne_top.mp h)

@[deprecated (since := "2026-07-17")] alias coe_lift := natCast_lift

中文:
定理 natCast_lift
  条件: (x : 自然数∞) (h : x < ⊤)
  结论: (lift x h : 自然数∞) = x
  证明: WithTop.coe_untop x (WithTop.lt_top_iff_ne_top.mp h)

@[deprecated (since := "2026-07-17")] alias coe_lift := natCast_lift
-/
@[simp] theorem natCast_lift (x : Nat∞) (h : x < ⊤) : (lift x h : Nat∞) = x :=
  WithTop.coe_untop x (WithTop.lt_top_iff_ne_top.mp h)

@[deprecated (since := "2026-07-17")] alias coe_lift := natCast_lift

/--
theorem `lift_natCast` / 定理 `lift_natCast`

English:
theorem lift_natCast
  given: (n : Nat)
  statement: lift (n : Nat∞) (WithTop.natCast_lt_top n) = n
  proof: rfl

中文:
定理 lift_natCast
  条件: (n : 自然数)
  结论: lift (n : 自然数∞) (WithTop.natCast_lt_top n) = n
  证明: rfl
-/
@[simp] theorem lift_natCast (n : Nat) : lift (n : Nat∞) (WithTop.natCast_lt_top n) = n := rfl
/--
theorem `lift_lt_iff` / 定理 `lift_lt_iff`

English:
theorem lift_lt_iff
  given: {x : Nat∞} {h} {n : Nat}
  statement: lift x h < n ↔ x < n
  proof: WithTop.untop_lt_iff _

中文:
定理 lift_lt_iff
  条件: {x : 自然数∞} {h} {n : 自然数}
  结论: lift x h < n ↔ x < n
  证明: WithTop.untop_lt_iff _
-/
@[simp] theorem lift_lt_iff {x : Nat∞} {h} {n : Nat} : lift x h < n ↔ x < n := WithTop.untop_lt_iff _
/--
theorem `lift_le_iff` / 定理 `lift_le_iff`

English:
theorem lift_le_iff
  given: {x : Nat∞} {h} {n : Nat}
  statement: lift x h <= n ↔ x <= n
  proof: WithTop.untop_le_iff _

中文:
定理 lift_le_iff
  条件: {x : 自然数∞} {h} {n : 自然数}
  结论: lift x h <= n ↔ x <= n
  证明: WithTop.untop_le_iff _
-/
@[simp] theorem lift_le_iff {x : Nat∞} {h} {n : Nat} : lift x h <= n ↔ x <= n := WithTop.untop_le_iff _
/--
theorem `lt_lift_iff` / 定理 `lt_lift_iff`

English:
theorem lt_lift_iff
  given: {x : Nat} {n : Nat∞} {h}
  statement: x < lift n h ↔ x < n
  proof: WithTop.lt_untop_iff _

中文:
定理 lt_lift_iff
  条件: {x : 自然数} {n : 自然数∞} {h}
  结论: x < lift n h ↔ x < n
  证明: WithTop.lt_untop_iff _
-/
@[simp] theorem lt_lift_iff {x : Nat} {n : Nat∞} {h} : x < lift n h ↔ x < n := WithTop.lt_untop_iff _
/--
theorem `le_lift_iff` / 定理 `le_lift_iff`

English:
theorem le_lift_iff
  given: {x : Nat} {n : Nat∞} {h}
  statement: x <= lift n h ↔ x <= n
  proof: WithTop.le_untop_iff _

@[deprecated (since := "2026-07-17")] alias lift_coe := lift_natCast

中文:
定理 le_lift_iff
  条件: {x : 自然数} {n : 自然数∞} {h}
  结论: x <= lift n h ↔ x <= n
  证明: WithTop.le_untop_iff _

@[deprecated (since := "2026-07-17")] alias lift_coe := lift_natCast
-/
@[simp] theorem le_lift_iff {x : Nat} {n : Nat∞} {h} : x <= lift n h ↔ x <= n := WithTop.le_untop_iff _

@[deprecated (since := "2026-07-17")] alias lift_coe := lift_natCast

/--
theorem `lift_zero` / 定理 `lift_zero`

English:
theorem lift_zero
  statement: lift 0 (WithTop.natCast_lt_top 0) = 0
  proof: rfl

中文:
定理 lift_zero
  结论: lift 0 (WithTop.natCast_lt_top 0) = 0
  证明: rfl
-/
@[simp] theorem lift_zero : lift 0 (WithTop.natCast_lt_top 0) = 0 := rfl
/--
theorem `lift_one` / 定理 `lift_one`

English:
theorem lift_one
  statement: lift 1 (WithTop.natCast_lt_top 1) = 1
  proof: rfl

中文:
定理 lift_one
  结论: lift 1 (WithTop.natCast_lt_top 1) = 1
  证明: rfl
-/
@[simp] theorem lift_one : lift 1 (WithTop.natCast_lt_top 1) = 1 := rfl
/--
theorem `lift_ofNat` / 定理 `lift_ofNat`

English:
theorem lift_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  proof: rfl

中文:
定理 lift_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  证明: rfl

Depends on / 依赖: Perm.permutations, Perm.refl, h.mem_iff, mem_iff, mem_permutations, permutations
-/
@[simp] theorem lift_ofNat (n : Nat) [n.AtLeastTwo] :
    lift ofNat(n) (WithTop.natCast_lt_top n) = OfNat.ofNat n := rfl

/--
theorem `add_lt_top` / 定理 `add_lt_top`

English:
theorem add_lt_top
  given: {a b : Nat∞}
  statement: a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤
  proof: WithTop.add_lt_top

中文:
定理 add_lt_top
  条件: {a b : 自然数∞}
  结论: a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤
  证明: WithTop.add_lt_top
-/
@[simp] theorem add_lt_top {a b : Nat∞} : a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤ := WithTop.add_lt_top
/--
theorem `add_eq_top` / 定理 `add_eq_top`

English:
theorem add_eq_top
  given: {a b : Nat∞}
  statement: a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤
  proof: WithTop.add_eq_top

中文:
定理 add_eq_top
  条件: {a b : 自然数∞}
  结论: a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤
  证明: WithTop.add_eq_top
-/
@[simp] theorem add_eq_top {a b : Nat∞} : a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤ := WithTop.add_eq_top

/--
theorem `lift_add` / 定理 `lift_add`

English:
theorem lift_add
  given: (a b : Nat∞) (h : a + b < ⊤)
  proof: by
  apply natCast_inj.1
  simp

中文:
定理 lift_add
  条件: (a b : 自然数∞) (h : a + b < ⊤)
  证明: by
  apply natCast_inj.1
  simp
-/
@[simp] theorem lift_add (a b : Nat∞) (h : a + b < ⊤) :
    lift (a + b) h = lift a (add_lt_top.1 h).1 + lift b (add_lt_top.1 h).2 := by
  apply natCast_inj.1
  simp

/--
Instance `canLift` / 实例 `canLift`

English:
instance canLift
  signature: : CanLift Nat∞ Nat (↑) (· != ⊤)
  body: WithTop.canLift

中文:
实例 canLift
  签名: : CanLift 自然数∞ 自然数 (↑) (· != ⊤)
  定义体: WithTop.canLift

Depends on / 依赖: WithTop, WithTop.canLift, canLift
-/
instance canLift : CanLift Nat∞ Nat (↑) (· != ⊤) := WithTop.canLift

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: WellFoundedRelation Nat∞
  body: WellFoundedLT.toWellFoundedRelation

中文:
实例 :
  签名: 良基关系 自然数∞
  定义体: WellFoundedLT.toWellFoundedRelation

Depends on / 依赖: WellFoundedLT, WellFoundedLT.toWellFoundedRelation, toWellFoundedRelation
-/
instance : WellFoundedRelation Nat∞ :=
  WellFoundedLT.toWellFoundedRelation

/--
Definition of `toNat` / `toNat` 的定义

English:
definition toNat
  signature: : Nat∞ -> Nat
  body: WithTop.untopD 0

中文:
定义 to自然数
  签名: : 自然数∞ -> 自然数
  定义体: WithTop.untopD 0

Depends on / 依赖: WithTop, WithTop.untopD, untopD
-/
def toNat : Nat∞ -> Nat := WithTop.untopD 0

/--
Definition of `toNatHom` / `toNatHom` 的定义

English:
definition toNatHom
  signature: : MonoidWithZeroHom Nat∞ Nat where
  body: toNat
  map_one' := rfl
  map_zero' := rfl
  map_mul' := WithTop.untopD_zero_mul

中文:
定义 to自然数Hom
  签名: : 带零幺半群态射 自然数∞ 自然数 where
  定义体: toNat
  map_one' := rfl
  map_zero' := rfl
  map_mul' := WithTop.untopD_zero_mul

Depends on / 依赖: Aux_of_notMem, Fin.mk.inj_iff, Nat.lt_succ_iff, get_of_mem, get_permutations, hk.le, inj_iff, insertIdx, k.succ_ne_self.symm, length, lt_succ_iff, nodup_iff_injective_get, nodup_permutations, permutations, s.insertIdx, succ_ne_self
-/
def toNatHom : MonoidWithZeroHom Nat∞ Nat where
  toFun := toNat
  map_one' := rfl
  map_zero' := rfl
  map_mul' := WithTop.untopD_zero_mul

/--
lemma `coe_toNatHom` / 引理 `coe_toNatHom`

English:
lemma coe_toNatHom
  statement: toNatHom = toNat
  proof: rfl

中文:
引理 coe_to自然数Hom
  结论: to自然数Hom = to自然数
  证明: rfl
-/
@[simp, norm_cast] lemma coe_toNatHom : toNatHom = toNat := rfl

/--
lemma `toNatHom_apply` / 引理 `toNatHom_apply`

English:
lemma toNatHom_apply
  given: (n : Nat)
  statement: toNatHom n = toNat n
  proof: rfl

@[simp]

中文:
引理 to自然数Hom_apply
  条件: (n : 自然数)
  结论: to自然数Hom n = to自然数 n
  证明: rfl

@[simp]
-/
lemma toNatHom_apply (n : Nat) : toNatHom n = toNat n := rfl

@[simp]
/--
theorem `toNat_natCast` / 定理 `toNat_natCast`

English:
theorem toNat_natCast
  given: (n : Nat)
  statement: toNat n = n
  proof: rfl

@[deprecated (since := "2026-07-17")] alias toNat_coe := toNat_natCast

@[simp]

中文:
定理 to自然数_natCast
  条件: (n : 自然数)
  结论: to自然数 n = n
  证明: rfl

@[deprecated (since := "2026-07-17")] alias toNat_coe := toNat_natCast

@[simp]
-/
theorem toNat_natCast (n : Nat) : toNat n = n :=
  rfl

@[deprecated (since := "2026-07-17")] alias toNat_coe := toNat_natCast

@[simp]
/--
theorem `toNat_zero` / 定理 `toNat_zero`

English:
theorem toNat_zero
  statement: toNat 0 = 0
  proof: rfl

@[simp]

中文:
定理 to自然数_zero
  结论: to自然数 0 = 0
  证明: rfl

@[simp]
-/
theorem toNat_zero : toNat 0 = 0 :=
  rfl

@[simp]
/--
theorem `toNat_one` / 定理 `toNat_one`

English:
theorem toNat_one
  statement: toNat 1 = 1
  proof: rfl

@[simp]

中文:
定理 to自然数_one
  结论: to自然数 1 = 1
  证明: rfl

@[simp]
-/
theorem toNat_one : toNat 1 = 1 :=
  rfl

@[simp]
/--
theorem `toNat_ofNat` / 定理 `toNat_ofNat`

English:
theorem toNat_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: toNat ofNat(n) = n
  proof: rfl

@[simp]

中文:
定理 to自然数_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: to自然数 of自然数(n) = n
  证明: rfl

@[simp]
-/
theorem toNat_ofNat (n : Nat) [n.AtLeastTwo] : toNat ofNat(n) = n :=
  rfl

@[simp]
/--
theorem `toNat_top` / 定理 `toNat_top`

English:
theorem toNat_top
  statement: toNat ⊤ = 0
  proof: rfl

中文:
定理 to自然数_top
  结论: to自然数 ⊤ = 0
  证明: rfl
-/
theorem toNat_top : toNat ⊤ = 0 :=
  rfl

/--
theorem `toNat_eq_zero` / 定理 `toNat_eq_zero`

English:
theorem toNat_eq_zero
  statement: toNat n = 0 ↔ n = 0 ∨ n = ⊤
  proof: WithTop.untopD_eq_self_iff

中文:
定理 to自然数_eq_zero
  结论: to自然数 n = 0 ↔ n = 0 ∨ n = ⊤
  证明: WithTop.untopD_eq_self_iff
-/
@[simp] theorem toNat_eq_zero : toNat n = 0 ↔ n = 0 ∨ n = ⊤ := WithTop.untopD_eq_self_iff

/--
theorem `toNat_pos` / 定理 `toNat_pos`

English:
theorem toNat_pos
  given: (hn0 : n != 0) (hxt : n != ⊤)
  statement: 0 < n.toNat
  proof: by
  rw [pos_iff_ne_zero]; rw [ne_eq]; rw [ENat.toNat_eq_zero]; rw [not_or]
  exact ⟨hn0, hxt⟩

中文:
定理 to自然数_pos
  条件: (hn0 : n != 0) (hxt : n != ⊤)
  结论: 0 < n.to自然数
  证明: by
  rw [pos_iff_ne_zero]; rw [ne_eq]; rw [ENat.toNat_eq_zero]; rw [not_or]
  exact ⟨hn0, hxt⟩

Depends on / 依赖: ENat.toNat_eq_zero, ne_eq, not_or, pos_iff_ne_zero, toNat_eq_zero
-/
theorem toNat_pos (hn0 : n != 0) (hxt : n != ⊤) : 0 < n.toNat := by
  rw [pos_iff_ne_zero]; rw [ne_eq]; rw [ENat.toNat_eq_zero]; rw [not_or]
  exact ⟨hn0, hxt⟩

/--
theorem `lift_eq_toNat_of_lt_top` / 定理 `lift_eq_toNat_of_lt_top`

English:
theorem lift_eq_toNat_of_lt_top
  given: {x : Nat∞} (hx : x < ⊤)
  statement: x.lift hx = x.toNat
  proof: by
  rcases x with ⟨⟩ | x
  · contradiction
  · rfl

@[simp]

中文:
定理 lift_eq_to自然数_of_lt_top
  条件: {x : 自然数∞} (hx : x < ⊤)
  结论: x.lift hx = x.to自然数
  证明: by
  rcases x with ⟨⟩ | x
  · contradiction
  · rfl

@[simp]
-/
theorem lift_eq_toNat_of_lt_top {x : Nat∞} (hx : x < ⊤) : x.lift hx = x.toNat := by
  rcases x with ⟨⟩ | x
  · contradiction
  · rfl

@[simp]
/--
theorem `recTopCoe_zero` / 定理 `recTopCoe_zero`

English:
theorem recTopCoe_zero
  given: {C : Nat∞ -> Sort*} (d : C ⊤) (f : forall a : Nat, C a)
  statement: @recTopCoe C d f 0 = f 0
  proof: rfl

@[simp]

中文:
定理 recTopCoe_zero
  条件: {C : 自然数∞ -> 类型层*} (d : C ⊤) (f : 对任意 a : 自然数, C a)
  结论: @recTopCoe C d f 0 = f 0
  证明: rfl

@[simp]
-/
theorem recTopCoe_zero {C : Nat∞ -> Sort*} (d : C ⊤) (f : forall a : Nat, C a) : @recTopCoe C d f 0 = f 0 :=
  rfl

@[simp]
/--
theorem `recTopCoe_one` / 定理 `recTopCoe_one`

English:
theorem recTopCoe_one
  given: {C : Nat∞ -> Sort*} (d : C ⊤) (f : forall a : Nat, C a)
  statement: @recTopCoe C d f 1 = f 1
  proof: rfl

@[simp]

中文:
定理 recTopCoe_one
  条件: {C : 自然数∞ -> 类型层*} (d : C ⊤) (f : 对任意 a : 自然数, C a)
  结论: @recTopCoe C d f 1 = f 1
  证明: rfl

@[simp]
-/
theorem recTopCoe_one {C : Nat∞ -> Sort*} (d : C ⊤) (f : forall a : Nat, C a) : @recTopCoe C d f 1 = f 1 :=
  rfl

@[simp]
/--
theorem `recTopCoe_ofNat` / 定理 `recTopCoe_ofNat`

English:
theorem recTopCoe_ofNat
  given: {C : Nat∞ -> Sort*} (d : C ⊤) (f : forall a : Nat, C a) (x : Nat) [x.AtLeastTwo]
  proof: rfl

@[simp]

中文:
定理 recTopCoe_of自然数
  条件: {C : 自然数∞ -> 类型层*} (d : C ⊤) (f : 对任意 a : 自然数, C a) (x : 自然数) [x.AtLeastTwo]
  证明: rfl

@[simp]
-/
theorem recTopCoe_ofNat {C : Nat∞ -> Sort*} (d : C ⊤) (f : forall a : Nat, C a) (x : Nat) [x.AtLeastTwo] :
    @recTopCoe C d f ofNat(x) = f (OfNat.ofNat x) :=
  rfl

@[simp]
/--
theorem `top_ne_natCast` / 定理 `top_ne_natCast`

English:
theorem top_ne_natCast
  given: (a : Nat)
  statement: ⊤ != (a : Nat∞)
  proof: nofun

@[deprecated (since := "2026-07-17")] alias top_ne_coe := top_ne_natCast

@[simp]

中文:
定理 top_ne_natCast
  条件: (a : 自然数)
  结论: ⊤ != (a : 自然数∞)
  证明: nofun

@[deprecated (since := "2026-07-17")] alias top_ne_coe := top_ne_natCast

@[simp]
-/
theorem top_ne_natCast (a : Nat) : ⊤ != (a : Nat∞) :=
  nofun

@[deprecated (since := "2026-07-17")] alias top_ne_coe := top_ne_natCast

@[simp]
/--
theorem `top_ne_ofNat` / 定理 `top_ne_ofNat`

English:
theorem top_ne_ofNat
  given: (a : Nat) [a.AtLeastTwo]
  statement: ⊤ != (ofNat(a) : Nat∞)
  proof: nofun

中文:
定理 top_ne_of自然数
  条件: (a : 自然数) [a.AtLeastTwo]
  结论: ⊤ != (of自然数(a) : 自然数∞)
  证明: nofun
-/
theorem top_ne_ofNat (a : Nat) [a.AtLeastTwo] : ⊤ != (ofNat(a) : Nat∞) :=
  nofun

/--
lemma `top_ne_zero` / 引理 `top_ne_zero`

English:
lemma top_ne_zero
  statement: (⊤ : Nat∞) != 0
  proof: nofun

中文:
引理 top_ne_zero
  结论: (⊤ : 自然数∞) != 0
  证明: nofun
-/
@[simp] lemma top_ne_zero : (⊤ : Nat∞) != 0 := nofun
/--
lemma `top_ne_one` / 引理 `top_ne_one`

English:
lemma top_ne_one
  statement: (⊤ : Nat∞) != 1
  proof: nofun

@[simp]

中文:
引理 top_ne_one
  结论: (⊤ : 自然数∞) != 1
  证明: nofun

@[simp]
-/
@[simp] lemma top_ne_one : (⊤ : Nat∞) != 1 := nofun

@[simp]
/--
theorem `natCast_ne_top` / 定理 `natCast_ne_top`

English:
theorem natCast_ne_top
  given: (a : Nat)
  statement: (a : Nat∞) != ⊤
  proof: nofun

@[deprecated (since := "2026-07-17")] alias coe_ne_top := natCast_ne_top

@[simp]

中文:
定理 natCast_ne_top
  条件: (a : 自然数)
  结论: (a : 自然数∞) != ⊤
  证明: nofun

@[deprecated (since := "2026-07-17")] alias coe_ne_top := natCast_ne_top

@[simp]
-/
theorem natCast_ne_top (a : Nat) : (a : Nat∞) != ⊤ :=
  nofun

@[deprecated (since := "2026-07-17")] alias coe_ne_top := natCast_ne_top

@[simp]
/--
theorem `ofNat_ne_top` / 定理 `ofNat_ne_top`

English:
theorem ofNat_ne_top
  given: (a : Nat) [a.AtLeastTwo]
  statement: (ofNat(a) : Nat∞) != ⊤
  proof: nofun

中文:
定理 of自然数_ne_top
  条件: (a : 自然数) [a.AtLeastTwo]
  结论: (of自然数(a) : 自然数∞) != ⊤
  证明: nofun
-/
theorem ofNat_ne_top (a : Nat) [a.AtLeastTwo] : (ofNat(a) : Nat∞) != ⊤ :=
  nofun

/--
lemma `zero_ne_top` / 引理 `zero_ne_top`

English:
lemma zero_ne_top
  statement: 0 != (⊤ : Nat∞)
  proof: nofun

中文:
引理 zero_ne_top
  结论: 0 != (⊤ : 自然数∞)
  证明: nofun
-/
@[simp] lemma zero_ne_top : 0 != (⊤ : Nat∞) := nofun
/--
lemma `one_ne_top` / 引理 `one_ne_top`

English:
lemma one_ne_top
  statement: 1 != (⊤ : Nat∞)
  proof: nofun

@[simp]

中文:
引理 one_ne_top
  结论: 1 != (⊤ : 自然数∞)
  证明: nofun

@[simp]
-/
@[simp] lemma one_ne_top : 1 != (⊤ : Nat∞) := nofun

@[simp]
/--
theorem `top_sub_natCast` / 定理 `top_sub_natCast`

English:
theorem top_sub_natCast
  given: (a : Nat)
  statement: (⊤ : Nat∞) - a = ⊤
  proof: rfl

@[deprecated (since := "2026-07-17")] alias top_sub_coe := top_sub_natCast

@[simp]

中文:
定理 top_sub_natCast
  条件: (a : 自然数)
  结论: (⊤ : 自然数∞) - a = ⊤
  证明: rfl

@[deprecated (since := "2026-07-17")] alias top_sub_coe := top_sub_natCast

@[simp]
-/
theorem top_sub_natCast (a : Nat) : (⊤ : Nat∞) - a = ⊤ :=
  rfl

@[deprecated (since := "2026-07-17")] alias top_sub_coe := top_sub_natCast

@[simp]
/--
theorem `top_sub_one` / 定理 `top_sub_one`

English:
theorem top_sub_one
  statement: (⊤ : Nat∞) - 1 = ⊤
  proof: rfl

@[simp]

中文:
定理 top_sub_one
  结论: (⊤ : 自然数∞) - 1 = ⊤
  证明: rfl

@[simp]
-/
theorem top_sub_one : (⊤ : Nat∞) - 1 = ⊤ :=
  rfl

@[simp]
/--
theorem `top_sub_ofNat` / 定理 `top_sub_ofNat`

English:
theorem top_sub_ofNat
  given: (a : Nat) [a.AtLeastTwo]
  statement: (⊤ : Nat∞) - ofNat(a) = ⊤
  proof: rfl

@[simp]

中文:
定理 top_sub_of自然数
  条件: (a : 自然数) [a.AtLeastTwo]
  结论: (⊤ : 自然数∞) - of自然数(a) = ⊤
  证明: rfl

@[simp]
-/
theorem top_sub_ofNat (a : Nat) [a.AtLeastTwo] : (⊤ : Nat∞) - ofNat(a) = ⊤ :=
  rfl

@[simp]
/--
theorem `top_pos` / 定理 `top_pos`

English:
theorem top_pos
  statement: (0 : Nat∞) < ⊤
  proof: WithTop.top_pos

@[simp]

中文:
定理 top_pos
  结论: (0 : 自然数∞) < ⊤
  证明: WithTop.top_pos

@[simp]

Depends on / 依赖: WithTop, WithTop.top_pos, top_pos
-/
theorem top_pos : (0 : Nat∞) < ⊤ :=
  WithTop.top_pos

@[simp]
/--
theorem `one_lt_top` / 定理 `one_lt_top`

English:
theorem one_lt_top
  statement: (1 : Nat∞) < ⊤
  proof: WithTop.one_lt_top

中文:
定理 one_lt_top
  结论: (1 : 自然数∞) < ⊤
  证明: WithTop.one_lt_top

Depends on / 依赖: WithTop, WithTop.one_lt_top, one_lt_top
-/
theorem one_lt_top : (1 : Nat∞) < ⊤ :=
  WithTop.one_lt_top

/--
theorem `sub_top` / 定理 `sub_top`

English:
theorem sub_top
  given: (a : Nat∞)
  statement: a - ⊤ = 0
  proof: WithTop.sub_top

@[simp]

中文:
定理 sub_top
  条件: (a : 自然数∞)
  结论: a - ⊤ = 0
  证明: WithTop.sub_top

@[simp]
-/
@[simp] theorem sub_top (a : Nat∞) : a - ⊤ = 0 := WithTop.sub_top

@[simp]
/--
theorem `natCast_toNat_eq_self` / 定理 `natCast_toNat_eq_self`

English:
theorem natCast_toNat_eq_self
  statement: ENat.toNat n = n ↔ n != ⊤
  proof: ENat.recTopCoe (by decide) (fun _ => by simp [toNat_natCast]) n

@[deprecated (since := "2026-07-17")] alias coe_toNat_eq_self := natCast_toNat_eq_self

alias ⟨_, natCast_toNat⟩ := natCast_toNat_eq_self

@[deprecated (since := "2026-07-17")] alias coe_toNat := natCast_toNat

中文:
定理 natCast_to自然数_eq_self
  结论: E自然数.to自然数 n = n ↔ n != ⊤
  证明: ENat.recTopCoe (by decide) (fun _ => by simp [toNat_natCast]) n

@[deprecated (since := "2026-07-17")] alias coe_toNat_eq_self := natCast_toNat_eq_self

alias ⟨_, natCast_toNat⟩ := natCast_toNat_eq_self

@[deprecated (since := "2026-07-17")] alias coe_toNat := natCast_toNat

Depends on / 依赖: ENat.recTopCoe, recTopCoe, toNat_natCast
-/
theorem natCast_toNat_eq_self : ENat.toNat n = n ↔ n != ⊤ :=
  ENat.recTopCoe (by decide) (fun _ => by simp [toNat_natCast]) n

@[deprecated (since := "2026-07-17")] alias coe_toNat_eq_self := natCast_toNat_eq_self

alias ⟨_, natCast_toNat⟩ := natCast_toNat_eq_self

@[deprecated (since := "2026-07-17")] alias coe_toNat := natCast_toNat

/--
lemma `toNat_eq_iff_eq_natCast` / 引理 `toNat_eq_iff_eq_natCast`

English:
lemma toNat_eq_iff_eq_natCast
  given: (n : Nat∞) (m : Nat) [NeZero m]
  proof: by
  cases n
  · simpa using NeZero.ne' m
  · simp

@[deprecated (since := "2026-07-17")] alias toNat_eq_iff_eq_coe := toNat_eq_iff_eq_natCast

中文:
引理 to自然数_eq_iff_eq_natCast
  条件: (n : 自然数∞) (m : 自然数) [NeZero m]
  证明: by
  cases n
  · simpa using NeZero.ne' m
  · simp

@[deprecated (since := "2026-07-17")] alias toNat_eq_iff_eq_coe := toNat_eq_iff_eq_natCast
-/
@[simp] lemma toNat_eq_iff_eq_natCast (n : Nat∞) (m : Nat) [NeZero m] :
    n.toNat = m ↔ n = m := by
  cases n
  · simpa using NeZero.ne' m
  · simp

@[deprecated (since := "2026-07-17")] alias toNat_eq_iff_eq_coe := toNat_eq_iff_eq_natCast

/--
theorem `natCast_toNat_le_self` / 定理 `natCast_toNat_le_self`

English:
theorem natCast_toNat_le_self
  given: (n : Nat∞)
  statement: ↑(toNat n) <= n
  proof: ENat.recTopCoe le_top (fun _ => le_rfl) n

@[deprecated (since := "2026-07-17")] alias coe_toNat_le_self := natCast_toNat_le_self

中文:
定理 natCast_to自然数_le_self
  条件: (n : 自然数∞)
  结论: ↑(to自然数 n) <= n
  证明: ENat.recTopCoe le_top (fun _ => le_rfl) n

@[deprecated (since := "2026-07-17")] alias coe_toNat_le_self := natCast_toNat_le_self

Depends on / 依赖: ENat.recTopCoe, le_rfl, le_top, recTopCoe
-/
theorem natCast_toNat_le_self (n : Nat∞) : ↑(toNat n) <= n :=
  ENat.recTopCoe le_top (fun _ => le_rfl) n

@[deprecated (since := "2026-07-17")] alias coe_toNat_le_self := natCast_toNat_le_self

/--
theorem `toNat_add` / 定理 `toNat_add`

English:
theorem toNat_add
  given: {m n : Nat∞} (hm : m != ⊤) (hn : n != ⊤)
  statement: toNat (m + n) = toNat m + toNat n
  proof: by
  lift m to Nat using hm
  lift n to Nat using hn
  rfl

中文:
定理 to自然数_add
  条件: {m n : 自然数∞} (hm : m != ⊤) (hn : n != ⊤)
  结论: to自然数 (m + n) = to自然数 m + to自然数 n
  证明: by
  lift m to Nat using hm
  lift n to Nat using hn
  rfl
-/
theorem toNat_add {m n : Nat∞} (hm : m != ⊤) (hn : n != ⊤) : toNat (m + n) = toNat m + toNat n := by
  lift m to Nat using hm
  lift n to Nat using hn
  rfl

/--
theorem `toNat_sub` / 定理 `toNat_sub`

English:
theorem toNat_sub
  given: {n : Nat∞} (hn : n != ⊤) (m : Nat∞)
  statement: toNat (m - n) = toNat m - toNat n
  proof: by
  lift n to Nat using hn
  induction m
  · rw [top_sub_natCast, toNat_top, zero_tsub]
  · rw [← natCast_sub, toNat_natCast, toNat_natCast, toNat_natCast]

中文:
定理 to自然数_sub
  条件: {n : 自然数∞} (hn : n != ⊤) (m : 自然数∞)
  结论: to自然数 (m - n) = to自然数 m - to自然数 n
  证明: by
  lift n to Nat using hn
  induction m
  · rw [top_sub_natCast, toNat_top, zero_tsub]
  · rw [← natCast_sub, toNat_natCast, toNat_natCast, toNat_natCast]

Depends on / 依赖: natCast_sub, toNat_natCast, toNat_top, top_sub_natCast, zero_tsub
-/
theorem toNat_sub {n : Nat∞} (hn : n != ⊤) (m : Nat∞) : toNat (m - n) = toNat m - toNat n := by
  lift n to Nat using hn
  induction m
  · rw [top_sub_natCast, toNat_top, zero_tsub]
  · rw [← natCast_sub, toNat_natCast, toNat_natCast, toNat_natCast]

/--
theorem `toNat_mul` / 定理 `toNat_mul`

English:
theorem toNat_mul
  given: (a b : Nat∞)
  statement: (a * b).toNat = a.toNat * b.toNat
  proof: by
  cases a <;> cases b
  · simp
  · rename_i b; cases b <;> simp
  · rename_i a; cases a <;> simp
  · simp only [toNat_natCast]; rw [← natCast_mul, toNat_natCast]

中文:
定理 to自然数_mul
  条件: (a b : 自然数∞)
  结论: (a * b).to自然数 = a.to自然数 * b.to自然数
  证明: by
  cases a <;> cases b
  · simp
  · rename_i b; cases b <;> simp
  · rename_i a; cases a <;> simp
  · simp only [toNat_natCast]; rw [← natCast_mul, toNat_natCast]
-/
@[simp] theorem toNat_mul (a b : Nat∞) : (a * b).toNat = a.toNat * b.toNat := by
  cases a <;> cases b
  · simp
  · rename_i b; cases b <;> simp
  · rename_i a; cases a <;> simp
  · simp only [toNat_natCast]; rw [← natCast_mul, toNat_natCast]

/--
theorem `toNat_eq_iff` / 定理 `toNat_eq_iff`

English:
theorem toNat_eq_iff
  given: {m : Nat∞} {n : Nat} (hn : n != 0)
  statement: toNat m = n ↔ m = n
  proof: by
  induction m <;> simp [hn.symm]

中文:
定理 to自然数_eq_iff
  条件: {m : 自然数∞} {n : 自然数} (hn : n != 0)
  结论: to自然数 m = n ↔ m = n
  证明: by
  induction m <;> simp [hn.symm]

Depends on / 依赖: hn.symm
-/
theorem toNat_eq_iff {m : Nat∞} {n : Nat} (hn : n != 0) : toNat m = n ↔ m = n := by
  induction m <;> simp [hn.symm]

/--
lemma `toNat_le_of_le_natCast` / 引理 `toNat_le_of_le_natCast`

English:
lemma toNat_le_of_le_natCast
  given: {m : Nat∞} {n : Nat} (h : m <= n)
  statement: toNat m <= n
  proof: by
  lift m to Nat using ne_top_of_le_ne_top (natCast_ne_top n) h
  simpa using h

@[deprecated (since := "2026-07-17")] alias toNat_le_of_le_coe := toNat_le_of_le_natCast

@[gcongr]

中文:
引理 to自然数_le_of_le_natCast
  条件: {m : 自然数∞} {n : 自然数} (h : m <= n)
  结论: to自然数 m <= n
  证明: by
  lift m to Nat using ne_top_of_le_ne_top (natCast_ne_top n) h
  simpa using h

@[deprecated (since := "2026-07-17")] alias toNat_le_of_le_coe := toNat_le_of_le_natCast

@[gcongr]

Depends on / 依赖: natCast_ne_top, ne_top_of_le_ne_top
-/
lemma toNat_le_of_le_natCast {m : Nat∞} {n : Nat} (h : m <= n) : toNat m <= n := by
  lift m to Nat using ne_top_of_le_ne_top (natCast_ne_top n) h
  simpa using h

@[deprecated (since := "2026-07-17")] alias toNat_le_of_le_coe := toNat_le_of_le_natCast

@[gcongr]
/--
lemma `toNat_le_toNat` / 引理 `toNat_le_toNat`

English:
lemma toNat_le_toNat
  given: {m n : Nat∞} (h : m <= n) (hn : n != ⊤)
  statement: toNat m <= toNat n
  proof: toNat_le_of_le_natCast h.trans_eq (natCast_toNat hn).symm

@[deprecated Order.succ_eq_add_one (since := "2026-05-25")]

中文:
引理 to自然数_le_to自然数
  条件: {m n : 自然数∞} (h : m <= n) (hn : n != ⊤)
  结论: to自然数 m <= to自然数 n
  证明: toNat_le_of_le_natCast h.trans_eq (natCast_toNat hn).symm

@[deprecated Order.succ_eq_add_one (since := "2026-05-25")]

Depends on / 依赖: h.trans_eq, natCast_toNat, toNat_le_of_le_natCast, trans_eq
-/
lemma toNat_le_toNat {m n : Nat∞} (h : m <= n) (hn : n != ⊤) : toNat m <= toNat n :=
toNat_le_of_le_natCast h.trans_eq (natCast_toNat hn).symm

@[deprecated Order.succ_eq_add_one (since := "2026-05-25")]
/--
theorem `succ_def` / 定理 `succ_def`

English:
theorem succ_def
  given: (m : Nat∞)
  statement: Order.succ m = m + 1
  proof: Order.succ_eq_add_one m

中文:
定理 succ_def
  条件: (m : 自然数∞)
  结论: Order.succ m = m + 1
  证明: Order.succ_eq_add_one m

Depends on / 依赖: Order.succ_eq_add_one, succ_eq_add_one
-/
theorem succ_def (m : Nat∞) : Order.succ m = m + 1 :=
  Order.succ_eq_add_one m

/--
theorem `add_one_le_iff` / 定理 `add_one_le_iff`

English:
theorem add_one_le_iff
  given: (hm : m != ⊤)
  statement: m + 1 <= n ↔ m < n
  proof: Order.add_one_le_iff_of_not_isMax (not_isMax_iff_ne_top.mpr hm)

中文:
定理 add_one_le_iff
  条件: (hm : m != ⊤)
  结论: m + 1 <= n ↔ m < n
  证明: Order.add_one_le_iff_of_not_isMax (not_isMax_iff_ne_top.mpr hm)

Depends on / 依赖: Order.add_one_le_iff_of_not_isMax, add_one_le_iff_of_not_isMax, not_isMax_iff_ne_top, not_isMax_iff_ne_top.mpr
-/
theorem add_one_le_iff (hm : m != ⊤) : m + 1 <= n ↔ m < n :=
  Order.add_one_le_iff_of_not_isMax (not_isMax_iff_ne_top.mpr hm)

/--
theorem `add_one_le_iff'` / 定理 `add_one_le_iff'`

English:
theorem add_one_le_iff'
  given: (hn : n != ⊤)
  statement: m + 1 <= n ↔ m < n
  proof: Order.add_one_le_iff_of_not_isMax' (not_isMax_iff_ne_top.mpr hn)

中文:
定理 add_one_le_iff'
  条件: (hn : n != ⊤)
  结论: m + 1 <= n ↔ m < n
  证明: Order.add_one_le_iff_of_not_isMax' (not_isMax_iff_ne_top.mpr hn)

Depends on / 依赖: Order.add_one_le_iff_of_not_isMax, add_one_le_iff_of_not_isMax, not_isMax_iff_ne_top, not_isMax_iff_ne_top.mpr
-/
theorem add_one_le_iff' (hn : n != ⊤) : m + 1 <= n ↔ m < n :=
  Order.add_one_le_iff_of_not_isMax' (not_isMax_iff_ne_top.mpr hn)

/--
theorem `natCast_add_one_le_iff` / 定理 `natCast_add_one_le_iff`

English:
theorem natCast_add_one_le_iff
  given: {m : Nat} {n : Nat∞}
  statement: m + 1 <= n ↔ m < n
  proof: add_one_le_iff natCast_ne_top m

@[deprecated (since := "2026-07-17")] alias coe_add_one_le_iff := natCast_add_one_le_iff

中文:
定理 natCast_add_one_le_iff
  条件: {m : 自然数} {n : 自然数∞}
  结论: m + 1 <= n ↔ m < n
  证明: add_one_le_iff natCast_ne_top m

@[deprecated (since := "2026-07-17")] alias coe_add_one_le_iff := natCast_add_one_le_iff

Depends on / 依赖: add_one_le_iff, natCast_ne_top
-/
theorem natCast_add_one_le_iff {m : Nat} {n : Nat∞} : m + 1 <= n ↔ m < n :=
add_one_le_iff natCast_ne_top m

@[deprecated (since := "2026-07-17")] alias coe_add_one_le_iff := natCast_add_one_le_iff

/--
theorem `add_one_le_natCast_iff` / 定理 `add_one_le_natCast_iff`

English:
theorem add_one_le_natCast_iff
  given: {m : Nat∞} {n : Nat}
  statement: m + 1 <= n ↔ m < n
  proof: add_one_le_iff' natCast_ne_top n

@[deprecated (since := "2026-07-17")] alias add_one_le_coe_iff := add_one_le_natCast_iff

@[deprecated Order.one_le_iff_ne_zero (since := "2026-05-25")]

中文:
定理 add_one_le_natCast_iff
  条件: {m : 自然数∞} {n : 自然数}
  结论: m + 1 <= n ↔ m < n
  证明: add_one_le_iff' natCast_ne_top n

@[deprecated (since := "2026-07-17")] alias add_one_le_coe_iff := add_one_le_natCast_iff

@[deprecated Order.one_le_iff_ne_zero (since := "2026-05-25")]

Depends on / 依赖: add_one_le_iff, natCast_ne_top
-/
theorem add_one_le_natCast_iff {m : Nat∞} {n : Nat} : m + 1 <= n ↔ m < n :=
add_one_le_iff' natCast_ne_top n

@[deprecated (since := "2026-07-17")] alias add_one_le_coe_iff := add_one_le_natCast_iff

@[deprecated Order.one_le_iff_ne_zero (since := "2026-05-25")]
/--
theorem `one_le_iff_ne_zero` / 定理 `one_le_iff_ne_zero`

English:
theorem one_le_iff_ne_zero
  statement: 1 <= n ↔ n != 0
  proof: Order.one_le_iff_ne_zero

@[deprecated Order.lt_one_iff (since := "2026-05-25")]

中文:
定理 one_le_iff_ne_zero
  结论: 1 <= n ↔ n != 0
  证明: Order.one_le_iff_ne_zero

@[deprecated Order.lt_one_iff (since := "2026-05-25")]
-/
protected theorem one_le_iff_ne_zero : 1 <= n ↔ n != 0 :=
  Order.one_le_iff_ne_zero

@[deprecated Order.lt_one_iff (since := "2026-05-25")]
/--
lemma `lt_one_iff_eq_zero` / 引理 `lt_one_iff_eq_zero`

English:
lemma lt_one_iff_eq_zero
  statement: n < 1 ↔ n = 0
  proof: Order.lt_one_iff

@[deprecated Order.le_one_iff (since := "2026-05-25")]

中文:
引理 lt_one_iff_eq_zero
  结论: n < 1 ↔ n = 0
  证明: Order.lt_one_iff

@[deprecated Order.le_one_iff (since := "2026-05-25")]

Depends on / 依赖: Order.lt_one_iff, lt_one_iff
-/
lemma lt_one_iff_eq_zero : n < 1 ↔ n = 0 :=
  Order.lt_one_iff

@[deprecated Order.le_one_iff (since := "2026-05-25")]
/--
lemma `le_one_iff_eq_zero_or_eq_one` / 引理 `le_one_iff_eq_zero_or_eq_one`

English:
lemma le_one_iff_eq_zero_or_eq_one
  statement: n <= 1 ↔ n = 0 ∨ n = 1
  proof: Order.le_one_iff

中文:
引理 le_one_iff_eq_zero_or_eq_one
  结论: n <= 1 ↔ n = 0 ∨ n = 1
  证明: Order.le_one_iff

Depends on / 依赖: Order.le_one_iff, le_one_iff
-/
lemma le_one_iff_eq_zero_or_eq_one : n <= 1 ↔ n = 0 ∨ n = 1 :=
  Order.le_one_iff

/--
theorem `lt_add_one_iff` / 定理 `lt_add_one_iff`

English:
theorem lt_add_one_iff
  given: (hn : n != ⊤)
  statement: m < n + 1 ↔ m <= n
  proof: Order.lt_add_one_iff_of_not_isMax (not_isMax_iff_ne_top.mpr hn)

中文:
定理 lt_add_one_iff
  条件: (hn : n != ⊤)
  结论: m < n + 1 ↔ m <= n
  证明: Order.lt_add_one_iff_of_not_isMax (not_isMax_iff_ne_top.mpr hn)

Depends on / 依赖: Order.lt_add_one_iff_of_not_isMax, lt_add_one_iff_of_not_isMax, not_isMax_iff_ne_top, not_isMax_iff_ne_top.mpr
-/
theorem lt_add_one_iff (hn : n != ⊤) : m < n + 1 ↔ m <= n :=
  Order.lt_add_one_iff_of_not_isMax (not_isMax_iff_ne_top.mpr hn)

/--
theorem `lt_add_one_iff'` / 定理 `lt_add_one_iff'`

English:
theorem lt_add_one_iff'
  given: (hm : m != ⊤)
  statement: m < n + 1 ↔ m <= n
  proof: Order.lt_add_one_iff_of_not_isMax' (not_isMax_iff_ne_top.mpr hm)

@[simp]

中文:
定理 lt_add_one_iff'
  条件: (hm : m != ⊤)
  结论: m < n + 1 ↔ m <= n
  证明: Order.lt_add_one_iff_of_not_isMax' (not_isMax_iff_ne_top.mpr hm)

@[simp]

Depends on / 依赖: Order.lt_add_one_iff_of_not_isMax, lt_add_one_iff_of_not_isMax, not_isMax_iff_ne_top, not_isMax_iff_ne_top.mpr
-/
theorem lt_add_one_iff' (hm : m != ⊤) : m < n + 1 ↔ m <= n :=
  Order.lt_add_one_iff_of_not_isMax' (not_isMax_iff_ne_top.mpr hm)

@[simp]
/--
theorem `lt_two_iff` / 定理 `lt_two_iff`

English:
theorem lt_two_iff
  statement: n < 2 ↔ n <= 1
  proof: by
  rw [← one_add_one_eq_two]; rw [lt_add_one_iff one_ne_top]

中文:
定理 lt_two_iff
  结论: n < 2 ↔ n <= 1
  证明: by
  rw [← one_add_one_eq_two]; rw [lt_add_one_iff one_ne_top]

Depends on / 依赖: lt_add_one_iff, one_add_one_eq_two, one_ne_top
-/
theorem lt_two_iff : n < 2 ↔ n <= 1 := by
  rw [← one_add_one_eq_two]; rw [lt_add_one_iff one_ne_top]

/--
theorem `add_le_add_iff_left` / 定理 `add_le_add_iff_left`

English:
theorem add_le_add_iff_left
  given: {m n k : ENat} (h : k != ⊤)
  proof: WithTop.add_le_add_iff_left h

中文:
定理 add_le_add_iff_left
  条件: {m n k : E自然数} (h : k != ⊤)
  证明: WithTop.add_le_add_iff_left h

Depends on / 依赖: WithTop, WithTop.add_le_add_iff_left, add_le_add_iff_left
-/
theorem add_le_add_iff_left {m n k : ENat} (h : k != ⊤) :
    k + n <= k + m ↔ n <= m :=
  WithTop.add_le_add_iff_left h

/--
theorem `add_le_add_iff_right` / 定理 `add_le_add_iff_right`

English:
theorem add_le_add_iff_right
  given: {m n k : ENat} (h : k != ⊤)
  proof: WithTop.add_le_add_iff_right h

中文:
定理 add_le_add_iff_right
  条件: {m n k : E自然数} (h : k != ⊤)
  证明: WithTop.add_le_add_iff_right h

Depends on / 依赖: WithTop, WithTop.add_le_add_iff_right, add_le_add_iff_right
-/
theorem add_le_add_iff_right {m n k : ENat} (h : k != ⊤) :
    n + k <= m + k ↔ n <= m :=
  WithTop.add_le_add_iff_right h

/--
theorem `lt_natCast_add_one_iff` / 定理 `lt_natCast_add_one_iff`

English:
theorem lt_natCast_add_one_iff
  given: {m : Nat∞} {n : Nat}
  statement: m < n + 1 ↔ m <= n
  proof: lt_add_one_iff (natCast_ne_top n)

@[deprecated (since := "2026-07-17")] alias lt_coe_add_one_iff := lt_natCast_add_one_iff

中文:
定理 lt_natCast_add_one_iff
  条件: {m : 自然数∞} {n : 自然数}
  结论: m < n + 1 ↔ m <= n
  证明: lt_add_one_iff (natCast_ne_top n)

@[deprecated (since := "2026-07-17")] alias lt_coe_add_one_iff := lt_natCast_add_one_iff

Depends on / 依赖: lt_add_one_iff, natCast_ne_top
-/
theorem lt_natCast_add_one_iff {m : Nat∞} {n : Nat} : m < n + 1 ↔ m <= n :=
  lt_add_one_iff (natCast_ne_top n)

@[deprecated (since := "2026-07-17")] alias lt_coe_add_one_iff := lt_natCast_add_one_iff

/--
theorem `natCast_lt_add_one_iff` / 定理 `natCast_lt_add_one_iff`

English:
theorem natCast_lt_add_one_iff
  given: {m : Nat} {n : Nat∞}
  statement: m < n + 1 ↔ m <= n
  proof: lt_add_one_iff' (natCast_ne_top m)

@[deprecated (since := "2026-07-17")] alias coe_lt_add_one_iff := natCast_lt_add_one_iff

中文:
定理 natCast_lt_add_one_iff
  条件: {m : 自然数} {n : 自然数∞}
  结论: m < n + 1 ↔ m <= n
  证明: lt_add_one_iff' (natCast_ne_top m)

@[deprecated (since := "2026-07-17")] alias coe_lt_add_one_iff := natCast_lt_add_one_iff

Depends on / 依赖: lt_add_one_iff, natCast_ne_top
-/
theorem natCast_lt_add_one_iff {m : Nat} {n : Nat∞} : m < n + 1 ↔ m <= n :=
  lt_add_one_iff' (natCast_ne_top m)

@[deprecated (since := "2026-07-17")] alias coe_lt_add_one_iff := natCast_lt_add_one_iff

/--
theorem `le_natCast_iff` / 定理 `le_natCast_iff`

English:
theorem le_natCast_iff
  given: {n : Nat∞} {k : Nat}
  statement: n <= ↑k ↔ exists (n₀ : Nat), n = n₀ ∧ n₀ <= k
  proof: WithTop.le_coe_iff

@[deprecated (since := "2026-07-17")] alias le_coe_iff := le_natCast_iff

@[simp]

中文:
定理 le_natCast_iff
  条件: {n : 自然数∞} {k : 自然数}
  结论: n <= ↑k ↔ 存在 (n₀ : 自然数), n = n₀ ∧ n₀ <= k
  证明: WithTop.le_coe_iff

@[deprecated (since := "2026-07-17")] alias le_coe_iff := le_natCast_iff

@[simp]

Depends on / 依赖: WithTop, WithTop.le_coe_iff, le_coe_iff
-/
theorem le_natCast_iff {n : Nat∞} {k : Nat} : n <= ↑k ↔ exists (n₀ : Nat), n = n₀ ∧ n₀ <= k :=
  WithTop.le_coe_iff

@[deprecated (since := "2026-07-17")] alias le_coe_iff := le_natCast_iff

@[simp]
/--
lemma `natCast_lt_top` / 引理 `natCast_lt_top`

English:
lemma natCast_lt_top
  given: (n : Nat)
  statement: (n : Nat∞) < ⊤
  proof: WithTop.natCast_lt_top n

@[deprecated (since := "2026-07-17")] alias coe_lt_top := natCast_lt_top

中文:
引理 natCast_lt_top
  条件: (n : 自然数)
  结论: (n : 自然数∞) < ⊤
  证明: WithTop.natCast_lt_top n

@[deprecated (since := "2026-07-17")] alias coe_lt_top := natCast_lt_top

Depends on / 依赖: WithTop, WithTop.natCast_lt_top, natCast_lt_top
-/
lemma natCast_lt_top (n : Nat) : (n : Nat∞) < ⊤ :=
  WithTop.natCast_lt_top n

@[deprecated (since := "2026-07-17")] alias coe_lt_top := natCast_lt_top

/--
lemma `natCast_lt_natCast` / 引理 `natCast_lt_natCast`

English:
lemma natCast_lt_natCast
  given: {n m : Nat}
  statement: (n : Nat∞) < (m : Nat∞) ↔ n < m
  proof: by simp

@[deprecated (since := "2026-07-17")] alias coe_lt_coe := natCast_lt_natCast

中文:
引理 natCast_lt_natCast
  条件: {n m : 自然数}
  结论: (n : 自然数∞) < (m : 自然数∞) ↔ n < m
  证明: by simp

@[deprecated (since := "2026-07-17")] alias coe_lt_coe := natCast_lt_natCast
-/
lemma natCast_lt_natCast {n m : Nat} : (n : Nat∞) < (m : Nat∞) ↔ n < m := by simp

@[deprecated (since := "2026-07-17")] alias coe_lt_coe := natCast_lt_natCast

/--
lemma `natCast_le_natCast` / 引理 `natCast_le_natCast`

English:
lemma natCast_le_natCast
  given: {n m : Nat}
  statement: (n : Nat∞) <= (m : Nat∞) ↔ n <= m
  proof: by simp

@[deprecated (since := "2026-07-17")] alias coe_le_coe := natCast_le_natCast

@[elab_as_elim]

中文:
引理 natCast_le_natCast
  条件: {n m : 自然数}
  结论: (n : 自然数∞) <= (m : 自然数∞) ↔ n <= m
  证明: by simp

@[deprecated (since := "2026-07-17")] alias coe_le_coe := natCast_le_natCast

@[elab_as_elim]
-/
lemma natCast_le_natCast {n m : Nat} : (n : Nat∞) <= (m : Nat∞) ↔ n <= m := by simp

@[deprecated (since := "2026-07-17")] alias coe_le_coe := natCast_le_natCast

@[elab_as_elim]
/--
theorem `nat_induction` / 定理 `nat_induction`

English:
theorem nat_induction
  statement: {motive : Nat∞ -> Prop} (a : Nat∞) (zero : motive 0)
  proof: by
  have A : forall n : Nat, motive n := fun n => Nat.recOn n zero succ
  cases a
  · exact top A
  · exact A _

@[deprecated add_pos_of_right (since := "2026-05-25")]

中文:
定理 nat_induction
  结论: {motive : 自然数∞ -> 命题} (a : 自然数∞) (zero : motive 0)
  证明: by
  have A : forall n : Nat, motive n := fun n => Nat.recOn n zero succ
  cases a
  · exact top A
  · exact A _

@[deprecated add_pos_of_right (since := "2026-05-25")]

Depends on / 依赖: Nat.recOn, motive, rotate
-/
theorem nat_induction {motive : Nat∞ -> Prop} (a : Nat∞) (zero : motive 0)
    (succ : forall n : Nat, motive n -> motive n.succ)
    (top : (forall n : Nat, motive n) -> motive ⊤) : motive a := by
  have A : forall n : Nat, motive n := fun n => Nat.recOn n zero succ
  cases a
  · exact top A
  · exact A _

@[deprecated add_pos_of_right (since := "2026-05-25")]
/--
lemma `add_one_pos` / 引理 `add_one_pos`

English:
lemma add_one_pos
  statement: 0 < n + 1
  proof: add_pos_of_right zero_lt_one n

中文:
引理 add_one_pos
  结论: 0 < n + 1
  证明: add_pos_of_right zero_lt_one n

Depends on / 依赖: add_pos_of_right, le_of_succ_le_succ, zero_lt_one
-/
lemma add_one_pos : 0 < n + 1 :=
  add_pos_of_right zero_lt_one n

/--
lemma `natCast_lt_succ` / 引理 `natCast_lt_succ`

English:
lemma natCast_lt_succ
  given: {n : Nat}
  proof: by
  rw [← Nat.cast_one]; rw [← Nat.cast_add]; rw [natCast_lt_natCast]
  exact lt_add_one n

中文:
引理 natCast_lt_succ
  条件: {n : 自然数}
  证明: by
  rw [← Nat.cast_one]; rw [← Nat.cast_add]; rw [natCast_lt_natCast]
  exact lt_add_one n

Depends on / 依赖: Nat.cast_add, Nat.cast_one, _eq_drop_append_take, cast_add, cast_one, le_rfl, lt_add_one, natCast_lt_natCast, rotate
-/
lemma natCast_lt_succ {n : Nat} :
    (n : Nat∞) < (n : Nat∞) + 1 := by
  rw [← Nat.cast_one]; rw [← Nat.cast_add]; rw [natCast_lt_natCast]
  exact lt_add_one n

/--
lemma `add_lt_add_iff_right` / 引理 `add_lt_add_iff_right`

English:
lemma add_lt_add_iff_right
  given: {k : Nat∞} (h : k != ⊤)
  statement: n + k < m + k ↔ n < m
  proof: WithTop.add_lt_add_iff_right h

中文:
引理 add_lt_add_iff_right
  条件: {k : 自然数∞} (h : k != ⊤)
  结论: n + k < m + k ↔ n < m
  证明: WithTop.add_lt_add_iff_right h

Depends on / 依赖: Nat.mul_succ, WithTop, WithTop.add_lt_add_iff_right, _length, _length_mul, _rotate, add_lt_add_iff_right, mul_succ, rotate
-/
lemma add_lt_add_iff_right {k : Nat∞} (h : k != ⊤) : n + k < m + k ↔ n < m :=
  WithTop.add_lt_add_iff_right h

/--
lemma `add_lt_add_iff_left` / 引理 `add_lt_add_iff_left`

English:
lemma add_lt_add_iff_left
  given: {k : Nat∞} (h : k != ⊤)
  statement: k + n < k + m ↔ n < m
  proof: WithTop.add_lt_add_iff_left h

中文:
引理 add_lt_add_iff_left
  条件: {k : 自然数∞} (h : k != ⊤)
  结论: k + n < k + m ↔ n < m
  证明: WithTop.add_lt_add_iff_left h

Depends on / 依赖: Nat.mod_add_div, WithTop, WithTop.add_lt_add_iff_left, _length_mul, _rotate, add_lt_add_iff_left, l.length, l.rotate, length, length_rotate, mod_add_div, rotate
-/
lemma add_lt_add_iff_left {k : Nat∞} (h : k != ⊤) : k + n < k + m ↔ n < m :=
  WithTop.add_lt_add_iff_left h

/--
lemma `add_lt_add` / 引理 `add_lt_add`

English:
lemma add_lt_add
  given: (hac : a < c) (hbd : b < d)
  statement: a + b < c + d
  proof: WithTop.add_lt_add hac hbd

中文:
引理 add_lt_add
  条件: (hac : a < c) (hbd : b < d)
  结论: a + b < c + d
  证明: WithTop.add_lt_add hac hbd
-/
protected lemma add_lt_add (hac : a < c) (hbd : b < d) : a + b < c + d :=
  WithTop.add_lt_add hac hbd

/--
theorem `add_lt_add_of_le_of_lt` / 定理 `add_lt_add_of_le_of_lt`

English:
theorem add_lt_add_of_le_of_lt
  statement: a != ⊤ -> a <= b -> c < d -> a + c < b + d
  proof: WithTop.add_lt_add_of_le_of_lt

中文:
定理 add_lt_add_of_le_of_lt
  结论: a != ⊤ -> a <= b -> c < d -> a + c < b + d
  证明: WithTop.add_lt_add_of_le_of_lt
-/
protected theorem add_lt_add_of_le_of_lt : a != ⊤ -> a <= b -> c < d -> a + c < b + d :=
  WithTop.add_lt_add_of_le_of_lt

/--
theorem `add_lt_add_of_lt_of_le` / 定理 `add_lt_add_of_lt_of_le`

English:
theorem add_lt_add_of_lt_of_le
  statement: c != ⊤ -> a < b -> c <= d -> a + c < b + d
  proof: WithTop.add_lt_add_of_lt_of_le

中文:
定理 add_lt_add_of_lt_of_le
  结论: c != ⊤ -> a < b -> c <= d -> a + c < b + d
  证明: WithTop.add_lt_add_of_lt_of_le
-/
protected theorem add_lt_add_of_lt_of_le : c != ⊤ -> a < b -> c <= d -> a + c < b + d :=
  WithTop.add_lt_add_of_lt_of_le

/--
lemma `ne_top_iff_exists` / 引理 `ne_top_iff_exists`

English:
lemma ne_top_iff_exists
  statement: n != ⊤ ↔ exists m : Nat, ↑m = n
  proof: WithTop.ne_top_iff_exists

中文:
引理 ne_top_iff_存在
  结论: n != ⊤ ↔ 存在 m : 自然数, ↑m = n
  证明: WithTop.ne_top_iff_exists

Depends on / 依赖: WithTop, WithTop.ne_top_iff_exists, ne_top_iff_exists
-/
lemma ne_top_iff_exists : n != ⊤ ↔ exists m : Nat, ↑m = n := WithTop.ne_top_iff_exists

/--
lemma `eq_top_iff_forall_ne` / 引理 `eq_top_iff_forall_ne`

English:
lemma eq_top_iff_forall_ne
  statement: n = ⊤ ↔ forall m : Nat, ↑m != n
  proof: WithTop.eq_top_iff_forall_ne

中文:
引理 eq_top_iff_对任意_ne
  结论: n = ⊤ ↔ 对任意 m : 自然数, ↑m != n
  证明: WithTop.eq_top_iff_forall_ne

Depends on / 依赖: WithTop, WithTop.eq_top_iff_forall_ne, eq_top_iff_forall_ne
-/
lemma eq_top_iff_forall_ne : n = ⊤ ↔ forall m : Nat, ↑m != n := WithTop.eq_top_iff_forall_ne
/--
lemma `forall_ne_top` / 引理 `forall_ne_top`

English:
lemma forall_ne_top
  given: {p : Nat∞ -> Prop}
  statement: (forall x, x != ⊤ -> p x) ↔ forall x : Nat, p x
  proof: WithTop.forall_ne_top

中文:
引理 对任意_ne_top
  条件: {p : 自然数∞ -> 命题}
  结论: (对任意 x, x != ⊤ -> p x) ↔ 对任意 x : 自然数, p x
  证明: WithTop.forall_ne_top

Depends on / 依赖: WithTop, WithTop.forall_ne_top, forall_ne_top
-/
lemma forall_ne_top {p : Nat∞ -> Prop} : (forall x, x != ⊤ -> p x) ↔ forall x : Nat, p x := WithTop.forall_ne_top
/--
lemma `exists_ne_top` / 引理 `exists_ne_top`

English:
lemma exists_ne_top
  given: {p : Nat∞ -> Prop}
  statement: (exists x != ⊤, p x) ↔ exists x : Nat, p x
  proof: WithTop.exists_ne_top

中文:
引理 存在_ne_top
  条件: {p : 自然数∞ -> 命题}
  结论: (存在 x != ⊤, p x) ↔ 存在 x : 自然数, p x
  证明: WithTop.exists_ne_top

Depends on / 依赖: WithTop, WithTop.exists_ne_top, exists_ne_top
-/
lemma exists_ne_top {p : Nat∞ -> Prop} : (exists x != ⊤, p x) ↔ exists x : Nat, p x := WithTop.exists_ne_top
/--
lemma `eq_top_iff_forall_gt` / 引理 `eq_top_iff_forall_gt`

English:
lemma eq_top_iff_forall_gt
  statement: n = ⊤ ↔ forall m : Nat, m < n
  proof: WithTop.eq_top_iff_forall_gt

中文:
引理 eq_top_iff_对任意_gt
  结论: n = ⊤ ↔ 对任意 m : 自然数, m < n
  证明: WithTop.eq_top_iff_forall_gt

Depends on / 依赖: WithTop, WithTop.eq_top_iff_forall_gt, eq_top_iff_forall_gt
-/
lemma eq_top_iff_forall_gt : n = ⊤ ↔ forall m : Nat, m < n := WithTop.eq_top_iff_forall_gt
/--
lemma `eq_top_iff_forall_ge` / 引理 `eq_top_iff_forall_ge`

English:
lemma eq_top_iff_forall_ge
  statement: n = ⊤ ↔ forall m : Nat, m <= n
  proof: WithTop.eq_top_iff_forall_ge

中文:
引理 eq_top_iff_对任意_ge
  结论: n = ⊤ ↔ 对任意 m : 自然数, m <= n
  证明: WithTop.eq_top_iff_forall_ge

Depends on / 依赖: WithTop, WithTop.eq_top_iff_forall_ge, eq_top_iff_forall_ge
-/
lemma eq_top_iff_forall_ge : n = ⊤ ↔ forall m : Nat, m <= n := WithTop.eq_top_iff_forall_ge

/--
lemma `forall_natCast_le_iff_le` / 引理 `forall_natCast_le_iff_le`

English:
lemma forall_natCast_le_iff_le
  statement: (forall a : Nat, a <= m -> a <= n) ↔ m <= n
  proof: WithTop.forall_coe_le_iff_le

中文:
引理 对任意_natCast_le_iff_le
  结论: (对任意 a : 自然数, a <= m -> a <= n) ↔ m <= n
  证明: WithTop.forall_coe_le_iff_le

Depends on / 依赖: WithTop, WithTop.forall_coe_le_iff_le, forall_coe_le_iff_le
-/
lemma forall_natCast_le_iff_le : (forall a : Nat, a <= m -> a <= n) ↔ m <= n := WithTop.forall_coe_le_iff_le

/--
lemma `eq_of_forall_natCast_le_iff` / 引理 `eq_of_forall_natCast_le_iff`

English:
lemma eq_of_forall_natCast_le_iff
  given: (hm : forall a : Nat, a <= m ↔ a <= n)
  statement: m = n
  proof: WithTop.eq_of_forall_coe_le_iff hm

中文:
引理 eq_of_对任意_natCast_le_iff
  条件: (hm : 对任意 a : 自然数, a <= m ↔ a <= n)
  结论: m = n
  证明: WithTop.eq_of_forall_coe_le_iff hm

Depends on / 依赖: WithTop, WithTop.eq_of_forall_coe_le_iff, eq_of_forall_coe_le_iff
-/
lemma eq_of_forall_natCast_le_iff (hm : forall a : Nat, a <= m ↔ a <= n) : m = n :=
  WithTop.eq_of_forall_coe_le_iff hm

/--
lemma `exists_nat_gt` / 引理 `exists_nat_gt`

English:
lemma exists_nat_gt
  given: (hn : n != ⊤)
  statement: exists m : Nat, n < m
  proof: by
  simp_rw [lt_iff_not_ge]
exact not_forall.mp eq_top_iff_forall_ge.2.mt hn

中文:
引理 存在_nat_gt
  条件: (hn : n != ⊤)
  结论: 存在 m : 自然数, n < m
  证明: by
  simp_rw [lt_iff_not_ge]
exact not_forall.mp eq_top_iff_forall_ge.2.mt hn
-/
protected lemma exists_nat_gt (hn : n != ⊤) : exists m : Nat, n < m := by
  simp_rw [lt_iff_not_ge]
exact not_forall.mp eq_top_iff_forall_ge.2.mt hn

/--
lemma `sub_eq_top_iff` / 引理 `sub_eq_top_iff`

English:
lemma sub_eq_top_iff
  statement: a - b = ⊤ ↔ a = ⊤ ∧ b != ⊤
  proof: WithTop.sub_eq_top_iff

中文:
引理 sub_eq_top_iff
  结论: a - b = ⊤ ↔ a = ⊤ ∧ b != ⊤
  证明: WithTop.sub_eq_top_iff
-/
@[simp] lemma sub_eq_top_iff : a - b = ⊤ ↔ a = ⊤ ∧ b != ⊤ := WithTop.sub_eq_top_iff
/--
lemma `sub_ne_top_iff` / 引理 `sub_ne_top_iff`

English:
lemma sub_ne_top_iff
  statement: a - b != ⊤ ↔ a != ⊤ ∨ b = ⊤
  proof: WithTop.sub_ne_top_iff

中文:
引理 sub_ne_top_iff
  结论: a - b != ⊤ ↔ a != ⊤ ∨ b = ⊤
  证明: WithTop.sub_ne_top_iff

Depends on / 依赖: WithTop, WithTop.sub_ne_top_iff, sub_ne_top_iff
-/
lemma sub_ne_top_iff : a - b != ⊤ ↔ a != ⊤ ∨ b = ⊤ := WithTop.sub_ne_top_iff

/--
lemma `addLECancellable_of_ne_top` / 引理 `addLECancellable_of_ne_top`

English:
lemma addLECancellable_of_ne_top
  statement: a != ⊤ -> AddLECancellable a
  proof: WithTop.addLECancellable_of_ne_top

中文:
引理 addLECancellable_of_ne_top
  结论: a != ⊤ -> AddLECancellable a
  证明: WithTop.addLECancellable_of_ne_top

Depends on / 依赖: WithTop, WithTop.addLECancellable_of_ne_top, addLECancellable_of_ne_top
-/
lemma addLECancellable_of_ne_top : a != ⊤ -> AddLECancellable a := WithTop.addLECancellable_of_ne_top
/--
lemma `addLECancellable_of_lt_top` / 引理 `addLECancellable_of_lt_top`

English:
lemma addLECancellable_of_lt_top
  statement: a < ⊤ -> AddLECancellable a
  proof: WithTop.addLECancellable_of_lt_top

中文:
引理 addLECancellable_of_lt_top
  结论: a < ⊤ -> AddLECancellable a
  证明: WithTop.addLECancellable_of_lt_top

Depends on / 依赖: WithTop, WithTop.addLECancellable_of_lt_top, addLECancellable_of_lt_top
-/
lemma addLECancellable_of_lt_top : a < ⊤ -> AddLECancellable a := WithTop.addLECancellable_of_lt_top
/--
lemma `addLECancellable_natCast` / 引理 `addLECancellable_natCast`

English:
lemma addLECancellable_natCast
  given: (a : Nat)
  statement: AddLECancellable (a : Nat∞)
  proof: WithTop.addLECancellable_coe _

@[deprecated (since := "2026-07-17")] alias addLECancellable_coe := addLECancellable_natCast

中文:
引理 addLECancellable_natCast
  条件: (a : 自然数)
  结论: AddLECancellable (a : 自然数∞)
  证明: WithTop.addLECancellable_coe _

@[deprecated (since := "2026-07-17")] alias addLECancellable_coe := addLECancellable_natCast

Depends on / 依赖: Nat.add_comm, Nat.lt_sub_iff_add_lt, Nat.sub_le_iff_le_add, WithTop, WithTop.addLECancellable_coe, _append_left, _append_right, _drop, _take_of_lt, addLECancellable_coe, add_comm, add_mod_mod, getElem, l.drop, l.length, length, length_drop, lt_or_ge, lt_sub_iff_add_lt, m.zero_le.trans_lt
-/
lemma addLECancellable_natCast (a : Nat) : AddLECancellable (a : Nat∞) := WithTop.addLECancellable_coe _

@[deprecated (since := "2026-07-17")] alias addLECancellable_coe := addLECancellable_natCast

/--
lemma `le_sub_of_add_le_left` / 引理 `le_sub_of_add_le_left`

English:
lemma le_sub_of_add_le_left
  given: (ha : a != ⊤)
  statement: a + b <= c -> b <= c - a
  proof: (addLECancellable_of_ne_top ha).le_tsub_of_add_le_left

中文:
引理 le_sub_of_add_le_left
  条件: (ha : a != ⊤)
  结论: a + b <= c -> b <= c - a
  证明: (addLECancellable_of_ne_top ha).le_tsub_of_add_le_left
-/
protected lemma le_sub_of_add_le_left (ha : a != ⊤) : a + b <= c -> b <= c - a :=
  (addLECancellable_of_ne_top ha).le_tsub_of_add_le_left

/--
lemma `le_sub_of_add_le_right` / 引理 `le_sub_of_add_le_right`

English:
lemma le_sub_of_add_le_right
  given: (hb : b != ⊤)
  statement: a + b <= c -> a <= c - b
  proof: (addLECancellable_of_ne_top hb).le_tsub_of_add_le_right

中文:
引理 le_sub_of_add_le_right
  条件: (hb : b != ⊤)
  结论: a + b <= c -> a <= c - b
  证明: (addLECancellable_of_ne_top hb).le_tsub_of_add_le_right
-/
protected lemma le_sub_of_add_le_right (hb : b != ⊤) : a + b <= c -> a <= c - b :=
  (addLECancellable_of_ne_top hb).le_tsub_of_add_le_right

/--
lemma `le_sub_one_of_lt` / 引理 `le_sub_one_of_lt`

English:
lemma le_sub_one_of_lt
  given: (h : a < b)
  statement: a <= b - 1
  proof: by
  cases b
  · simp
· exact ENat.le_sub_of_add_le_right one_ne_top lt_natCast_add_one_iff.mp
      lt_tsub_iff_right.mp h

中文:
引理 le_sub_one_of_lt
  条件: (h : a < b)
  结论: a <= b - 1
  证明: by
  cases b
  · simp
· exact ENat.le_sub_of_add_le_right one_ne_top lt_natCast_add_one_iff.mp
      lt_tsub_iff_right.mp h

Depends on / 依赖: Nat.mod_eq_of_lt, Nat.zero_add, _eq_getElem, _rotate, getElem, mod_eq_of_lt, n.zero_le.trans_lt, trans_lt, zero_add, zero_le
-/
protected lemma le_sub_one_of_lt (h : a < b) : a <= b - 1 := by
  cases b
  · simp
· exact ENat.le_sub_of_add_le_right one_ne_top lt_natCast_add_one_iff.mp
      lt_tsub_iff_right.mp h

/--
lemma `lt_add_left` / 引理 `lt_add_left`

English:
lemma lt_add_left
  given: {n k : Nat∞} (h : n != ⊤) (h' : 0 < k)
  statement: n < k + n
  proof: calc
    _ = 0 + n := (zero_add n).symm
    _ < k + n := (add_lt_add_iff_right h).mpr h'

中文:
引理 lt_add_left
  条件: {n k : 自然数∞} (h : n != ⊤) (h' : 0 < k)
  结论: n < k + n
  证明: calc
    _ = 0 + n := (zero_add n).symm
    _ < k + n := (add_lt_add_iff_right h).mpr h'
-/
lemma lt_add_left {n k : Nat∞} (h : n != ⊤) (h' : 0 < k) : n < k + n := calc
    _ = 0 + n := (zero_add n).symm
    _ < k + n := (add_lt_add_iff_right h).mpr h'

/--
lemma `sub_sub_cancel` / 引理 `sub_sub_cancel`

English:
lemma sub_sub_cancel
  given: (h : a != ⊤) (h2 : b <= a)
  statement: a - (a - b) = b
  proof: (addLECancellable_of_ne_top <| ne_top_of_le_ne_top h tsub_le_self).tsub_tsub_cancel_of_le h2

中文:
引理 sub_sub_cancel
  条件: (h : a != ⊤) (h2 : b <= a)
  结论: a - (a - b) = b
  证明: (addLECancellable_of_ne_top <| ne_top_of_le_ne_top h tsub_le_self).tsub_tsub_cancel_of_le h2
-/
protected lemma sub_sub_cancel (h : a != ⊤) (h2 : b <= a) : a - (a - b) = b :=
  (addLECancellable_of_ne_top <| ne_top_of_le_ne_top h tsub_le_self).tsub_tsub_cancel_of_le h2

/--
lemma `add_left_injective_of_ne_top` / 引理 `add_left_injective_of_ne_top`

English:
lemma add_left_injective_of_ne_top
  given: {n : Nat∞} (hn : n != ⊤)
  statement: Function.Injective (· + n)
  proof: by
  intro a b e
  exact le_antisymm
    ((WithTop.add_le_add_iff_right hn).mp e.le)
    ((WithTop.add_le_add_iff_right hn).mp e.ge)

中文:
引理 add_left_injective_of_ne_top
  条件: {n : 自然数∞} (hn : n != ⊤)
  结论: 函数.单射 (· + n)
  证明: by
  intro a b e
  exact le_antisymm
    ((WithTop.add_le_add_iff_right hn).mp e.le)
    ((WithTop.add_le_add_iff_right hn).mp e.ge)

Depends on / 依赖: WithTop, WithTop.add_le_add_iff_right, add_le_add_iff_right, e.ge, e.le, le_antisymm
-/
lemma add_left_injective_of_ne_top {n : Nat∞} (hn : n != ⊤) : Function.Injective (· + n) := by
  intro a b e
  exact le_antisymm
    ((WithTop.add_le_add_iff_right hn).mp e.le)
    ((WithTop.add_le_add_iff_right hn).mp e.ge)

/--
lemma `add_right_injective_of_ne_top` / 引理 `add_right_injective_of_ne_top`

English:
lemma add_right_injective_of_ne_top
  given: {n : Nat∞} (hn : n != ⊤)
  statement: Function.Injective (n + ·)
  proof: by
  simp_rw [add_comm n _]
  exact add_left_injective_of_ne_top hn

中文:
引理 add_right_injective_of_ne_top
  条件: {n : 自然数∞} (hn : n != ⊤)
  结论: 函数.单射 (n + ·)
  证明: by
  simp_rw [add_comm n _]
  exact add_left_injective_of_ne_top hn

Depends on / 依赖: add_comm, add_left_injective_of_ne_top, simp_rw
-/
lemma add_right_injective_of_ne_top {n : Nat∞} (hn : n != ⊤) : Function.Injective (n + ·) := by
  simp_rw [add_comm n _]
  exact add_left_injective_of_ne_top hn

/--
lemma `mul_right_strictMono` / 引理 `mul_right_strictMono`

English:
lemma mul_right_strictMono
  given: (ha : a != 0) (h_top : a != ⊤)
  statement: StrictMono (a * ·)
  proof: WithTop.mul_right_strictMono (pos_iff_ne_zero.2 ha) h_top

中文:
引理 mul_right_strictMono
  条件: (ha : a != 0) (h_top : a != ⊤)
  结论: 严格递增 (a * ·)
  证明: WithTop.mul_right_strictMono (pos_iff_ne_zero.2 ha) h_top

Depends on / 依赖: WithTop, WithTop.mul_right_strictMono, h_top, mul_right_strictMono, pos_iff_ne_zero
-/
lemma mul_right_strictMono (ha : a != 0) (h_top : a != ⊤) : StrictMono (a * ·) :=
  WithTop.mul_right_strictMono (pos_iff_ne_zero.2 ha) h_top

/--
lemma `mul_left_strictMono` / 引理 `mul_left_strictMono`

English:
lemma mul_left_strictMono
  given: (ha : a != 0) (h_top : a != ⊤)
  statement: StrictMono (· * a)
  proof: WithTop.mul_left_strictMono (pos_iff_ne_zero.2 ha) h_top

@[simp]

中文:
引理 mul_left_strictMono
  条件: (ha : a != 0) (h_top : a != ⊤)
  结论: 严格递增 (· * a)
  证明: WithTop.mul_left_strictMono (pos_iff_ne_zero.2 ha) h_top

@[simp]

Depends on / 依赖: WithTop, WithTop.mul_left_strictMono, h_top, mul_left_strictMono, pos_iff_ne_zero
-/
lemma mul_left_strictMono (ha : a != 0) (h_top : a != ⊤) : StrictMono (· * a) :=
  WithTop.mul_left_strictMono (pos_iff_ne_zero.2 ha) h_top

@[simp]
/--
lemma `mul_le_mul_left_iff` / 引理 `mul_le_mul_left_iff`

English:
lemma mul_le_mul_left_iff
  given: {x y : Nat∞} (ha : a != 0) (h_top : a != ⊤)
  statement: a * x <= a * y ↔ x <= y
  proof: (ENat.mul_right_strictMono ha h_top).le_iff_le

@[simp]

中文:
引理 mul_le_mul_left_iff
  条件: {x y : 自然数∞} (ha : a != 0) (h_top : a != ⊤)
  结论: a * x <= a * y ↔ x <= y
  证明: (ENat.mul_right_strictMono ha h_top).le_iff_le

@[simp]

Depends on / 依赖: ENat.mul_right_strictMono, h_top, le_iff_le, mul_right_strictMono
-/
lemma mul_le_mul_left_iff {x y : Nat∞} (ha : a != 0) (h_top : a != ⊤) : a * x <= a * y ↔ x <= y :=
  (ENat.mul_right_strictMono ha h_top).le_iff_le

@[simp]
/--
lemma `mul_le_mul_right_iff` / 引理 `mul_le_mul_right_iff`

English:
lemma mul_le_mul_right_iff
  given: {x y : Nat∞} (ha : a != 0) (h_top : a != ⊤)
  statement: x * a <= y * a ↔ x <= y
  proof: (ENat.mul_left_strictMono ha h_top).le_iff_le

@[gcongr]

中文:
引理 mul_le_mul_right_iff
  条件: {x y : 自然数∞} (ha : a != 0) (h_top : a != ⊤)
  结论: x * a <= y * a ↔ x <= y
  证明: (ENat.mul_left_strictMono ha h_top).le_iff_le

@[gcongr]

Depends on / 依赖: ENat.mul_left_strictMono, h_top, le_iff_le, mul_left_strictMono
-/
lemma mul_le_mul_right_iff {x y : Nat∞} (ha : a != 0) (h_top : a != ⊤) : x * a <= y * a ↔ x <= y :=
  (ENat.mul_left_strictMono ha h_top).le_iff_le

@[gcongr]
/--
lemma `mul_le_mul_of_le_right` / 引理 `mul_le_mul_of_le_right`

English:
lemma mul_le_mul_of_le_right
  given: {x y : Nat∞} (hxy : x <= y) (ha : a != 0) (h_top : a != ⊤)
  proof: by
  simpa [ha, h_top]

中文:
引理 mul_le_mul_of_le_right
  条件: {x y : 自然数∞} (hxy : x <= y) (ha : a != 0) (h_top : a != ⊤)
  证明: by
  simpa [ha, h_top]

Depends on / 依赖: h_top
-/
lemma mul_le_mul_of_le_right {x y : Nat∞} (hxy : x <= y) (ha : a != 0) (h_top : a != ⊤) :
    x * a <= y * a := by
  simpa [ha, h_top]

/--
lemma `self_le_mul_right` / 引理 `self_le_mul_right`

English:
lemma self_le_mul_right
  given: (a : Nat∞) (hc : c != 0)
  statement: a <= a * c
  proof: by
  obtain rfl | hne := eq_or_ne a ⊤
  · simp [top_mul hc]
  obtain rfl | h0 := eq_or_ne a 0
  · simp
  nth_rewrite 1 [← mul_one a, ENat.mul_le_mul_left_iff h0 hne, Order.one_le_iff_ne_zero]
  assumption

中文:
引理 self_le_mul_right
  条件: (a : 自然数∞) (hc : c != 0)
  结论: a <= a * c
  证明: by
  obtain rfl | hne := eq_or_ne a ⊤
  · simp [top_mul hc]
  obtain rfl | h0 := eq_or_ne a 0
  · simp
  nth_rewrite 1 [← mul_one a, ENat.mul_le_mul_left_iff h0 hne, Order.one_le_iff_ne_zero]
  assumption

Depends on / 依赖: ENat.mul_le_mul_left_iff, Order.one_le_iff_ne_zero, eq_or_ne, mul_le_mul_left_iff, mul_one, nth_rewrite, one_le_iff_ne_zero, top_mul
-/
lemma self_le_mul_right (a : Nat∞) (hc : c != 0) : a <= a * c := by
  obtain rfl | hne := eq_or_ne a ⊤
  · simp [top_mul hc]
  obtain rfl | h0 := eq_or_ne a 0
  · simp
  nth_rewrite 1 [← mul_one a, ENat.mul_le_mul_left_iff h0 hne, Order.one_le_iff_ne_zero]
  assumption

/--
lemma `self_le_mul_left` / 引理 `self_le_mul_left`

English:
lemma self_le_mul_left
  given: (a : Nat∞) (hc : c != 0)
  statement: a <= c * a
  proof: by
  rw [mul_comm]
  exact ENat.self_le_mul_right a hc

中文:
引理 self_le_mul_left
  条件: (a : 自然数∞) (hc : c != 0)
  结论: a <= c * a
  证明: by
  rw [mul_comm]
  exact ENat.self_le_mul_right a hc

Depends on / 依赖: ENat.self_le_mul_right, mul_comm, self_le_mul_right
-/
lemma self_le_mul_left (a : Nat∞) (hc : c != 0) : a <= c * a := by
  rw [mul_comm]
  exact ENat.self_le_mul_right a hc

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Unique Nat∞ˣ
  body: by
    have := x.val_inv
    have x_top : x.val != ⊤ := by
      intro h
      simp [h] at this
    have x_inv_top : x.inv != ⊤ := by
      intro h
      simp only [h, ne_eq, x.ne_zero, not_false_eq_true, mul_top, top_ne_one] at this
    obtain ⟨y, x_y⟩ := ne_top_iff_exists.1 x_top
    obtain ⟨z, x_

中文:
实例 :
  签名: 唯一 自然数∞ˣ
  定义体: by
    have := x.val_inv
    have x_top : x.val != ⊤ := by
      intro h
      simp [h] at this
    have x_inv_top : x.inv != ⊤ := by
      intro h
      simp only [h, ne_eq, x.ne_zero, not_false_eq_true, mul_top, top_ne_one] at this
    obtain ⟨y, x_y⟩ := ne_top_iff_exists.1 x_top
    obtain ⟨z, x_

Depends on / 依赖: Nat.cast_one, Units.val_eq_one, _root_, _root_.mul_eq_one, cast_one, mul_eq_one, mul_top, natCast_inj, natCast_mul, natCast_one, ne_eq, ne_top_iff_exists, ne_zero, not_false_eq_true, replace, top_ne_one, val_eq_one, val_inv, x.inv, x.ne_zero
-/
instance : Unique Nat∞ˣ where
  uniq x := by
    have := x.val_inv
    have x_top : x.val != ⊤ := by
      intro h
      simp [h] at this
    have x_inv_top : x.inv != ⊤ := by
      intro h
      simp only [h, ne_eq, x.ne_zero, not_false_eq_true, mul_top, top_ne_one] at this
    obtain ⟨y, x_y⟩ := ne_top_iff_exists.1 x_top
    obtain ⟨z, x_z⟩ := ne_top_iff_exists.1 x_inv_top
    replace x_y := x_y.symm
    rw [x_y]; rw [← x_z]; rw [← natCast_mul]; rw [← natCast_one]; rw [natCast_inj]; rw [_root_.mul_eq_one] at this
    rwa [this.1, Nat.cast_one, Units.val_eq_one] at x_y

section withTop_enat

/--
lemma `add_one_natCast_le_withTop_of_lt` / 引理 `add_one_natCast_le_withTop_of_lt`

English:
lemma add_one_natCast_le_withTop_of_lt
  given: {m : Nat} {n : WithTop Nat∞} (h : m < n)
  statement: (m + 1 : Nat) <= n
  proof: by
  match n with
  | ⊤ => exact le_top
  | (⊤ : Nat∞) => exact WithTop.coe_le_coe.2 (OrderTop.le_top _)
  | (n : Nat) => simpa only [Nat.cast_le, ge_iff_le, Nat.cast_lt] using! h

中文:
引理 add_one_natCast_le_withTop_of_lt
  条件: {m : 自然数} {n : WithTop 自然数∞} (h : m < n)
  结论: (m + 1 : 自然数) <= n
  证明: by
  match n with
  | ⊤ => exact le_top
  | (⊤ : Nat∞) => exact WithTop.coe_le_coe.2 (OrderTop.le_top _)
  | (n : Nat) => simpa only [Nat.cast_le, ge_iff_le, Nat.cast_lt] using! h

Depends on / 依赖: Nat.cast_le, Nat.cast_lt, OrderTop, OrderTop.le_top, WithTop, WithTop.coe_le_coe, cast_le, cast_lt, coe_le_coe, ge_iff_le, le_top
-/
lemma add_one_natCast_le_withTop_of_lt {m : Nat} {n : WithTop Nat∞} (h : m < n) : (m + 1 : Nat) <= n := by
  match n with
  | ⊤ => exact le_top
  | (⊤ : Nat∞) => exact WithTop.coe_le_coe.2 (OrderTop.le_top _)
  | (n : Nat) => simpa only [Nat.cast_le, ge_iff_le, Nat.cast_lt] using! h

/--
lemma `coe_top_add_one` / 引理 `coe_top_add_one`

English:
lemma coe_top_add_one
  statement: ((⊤ : Nat∞) : WithTop Nat∞) + 1 = (⊤ : Nat∞)
  proof: rfl

中文:
引理 coe_top_add_one
  结论: ((⊤ : 自然数∞) : WithTop 自然数∞) + 1 = (⊤ : 自然数∞)
  证明: rfl
-/
@[simp] lemma coe_top_add_one : ((⊤ : Nat∞) : WithTop Nat∞) + 1 = (⊤ : Nat∞) := rfl

/--
lemma `add_one_eq_coe_top_iff` / 引理 `add_one_eq_coe_top_iff`

English:
lemma add_one_eq_coe_top_iff
  given: {n : WithTop Nat∞}
  statement: n + 1 = (⊤ : Nat∞) ↔ n = (⊤ : Nat∞)
  proof: by
  match n with
  | ⊤ => exact Iff.rfl
  | (⊤ : Nat∞) => simp
  | (n : Nat) =>
    norm_cast
    simp only [natCast_ne_top]

中文:
引理 add_one_eq_coe_top_iff
  条件: {n : WithTop 自然数∞}
  结论: n + 1 = (⊤ : 自然数∞) ↔ n = (⊤ : 自然数∞)
  证明: by
  match n with
  | ⊤ => exact Iff.rfl
  | (⊤ : Nat∞) => simp
  | (n : Nat) =>
    norm_cast
    simp only [natCast_ne_top]
-/
@[simp] lemma add_one_eq_coe_top_iff {n : WithTop Nat∞} : n + 1 = (⊤ : Nat∞) ↔ n = (⊤ : Nat∞) := by
  match n with
  | ⊤ => exact Iff.rfl
  | (⊤ : Nat∞) => simp
  | (n : Nat) =>
    norm_cast
    simp only [natCast_ne_top]

/--
lemma `natCast_ne_coe_top` / 引理 `natCast_ne_coe_top`

English:
lemma natCast_ne_coe_top
  given: (n : Nat)
  statement: (n : WithTop Nat∞) != (⊤ : Nat∞)
  proof: nofun

中文:
引理 natCast_ne_coe_top
  条件: (n : 自然数)
  结论: (n : WithTop 自然数∞) != (⊤ : 自然数∞)
  证明: nofun
-/
@[simp] lemma natCast_ne_coe_top (n : Nat) : (n : WithTop Nat∞) != (⊤ : Nat∞) := nofun

/--
lemma `one_le_iff_ne_zero_withTop` / 引理 `one_le_iff_ne_zero_withTop`

English:
lemma one_le_iff_ne_zero_withTop
  given: {n : WithTop Nat∞}
  statement: 1 <= n ↔ n != 0
  proof: ⟨fun h => (zero_lt_one.trans_le h).ne',
    fun h => add_one_natCast_le_withTop_of_lt (pos_iff_ne_zero.mpr h)⟩

中文:
引理 one_le_iff_ne_zero_withTop
  条件: {n : WithTop 自然数∞}
  结论: 1 <= n ↔ n != 0
  证明: ⟨fun h => (zero_lt_one.trans_le h).ne',
    fun h => add_one_natCast_le_withTop_of_lt (pos_iff_ne_zero.mpr h)⟩

Depends on / 依赖: add_one_natCast_le_withTop_of_lt, pos_iff_ne_zero, pos_iff_ne_zero.mpr, trans_le, zero_lt_one, zero_lt_one.trans_le
-/
lemma one_le_iff_ne_zero_withTop {n : WithTop Nat∞} : 1 <= n ↔ n != 0 :=
  ⟨fun h => (zero_lt_one.trans_le h).ne',
    fun h => add_one_natCast_le_withTop_of_lt (pos_iff_ne_zero.mpr h)⟩

/--
lemma `natCast_le_of_coe_top_le_withTop` / 引理 `natCast_le_of_coe_top_le_withTop`

English:
lemma natCast_le_of_coe_top_le_withTop
  given: {N : WithTop Nat∞} (hN : (⊤ : Nat∞) <= N) (n : Nat)
  statement: n <= N
  proof: le_trans (mod_cast le_top) hN

中文:
引理 natCast_le_of_coe_top_le_withTop
  条件: {N : WithTop 自然数∞} (hN : (⊤ : 自然数∞) <= N) (n : 自然数)
  结论: n <= N
  证明: le_trans (mod_cast le_top) hN

Depends on / 依赖: le_top, le_trans, mod_cast
-/
lemma natCast_le_of_coe_top_le_withTop {N : WithTop Nat∞} (hN : (⊤ : Nat∞) <= N) (n : Nat) : n <= N :=
  le_trans (mod_cast le_top) hN

/--
lemma `natCast_lt_of_coe_top_le_withTop` / 引理 `natCast_lt_of_coe_top_le_withTop`

English:
lemma natCast_lt_of_coe_top_le_withTop
  given: {N : WithTop Nat∞} (hN : (⊤ : Nat∞) <= N) (n : Nat)
  statement: n < N
  proof: lt_of_lt_of_le (mod_cast lt_add_one n) (natCast_le_of_coe_top_le_withTop hN (n + 1))

中文:
引理 natCast_lt_of_coe_top_le_withTop
  条件: {N : WithTop 自然数∞} (hN : (⊤ : 自然数∞) <= N) (n : 自然数)
  结论: n < N
  证明: lt_of_lt_of_le (mod_cast lt_add_one n) (natCast_le_of_coe_top_le_withTop hN (n + 1))

Depends on / 依赖: lt_add_one, lt_of_lt_of_le, mod_cast, natCast_le_of_coe_top_le_withTop
-/
lemma natCast_lt_of_coe_top_le_withTop {N : WithTop Nat∞} (hN : (⊤ : Nat∞) <= N) (n : Nat) : n < N :=
  lt_of_lt_of_le (mod_cast lt_add_one n) (natCast_le_of_coe_top_le_withTop hN (n + 1))

end withTop_enat

variable {α : Type*}

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : Nat -> α) (k : Nat∞)
  body: WithTop.map f k

@[simp]

中文:
定义 map
  签名: (f : 自然数 -> α) (k : 自然数∞)
  定义体: WithTop.map f k

@[simp]

Depends on / 依赖: WithTop, WithTop.map
-/
def map (f : Nat -> α) (k : Nat∞) : WithTop α := WithTop.map f k

@[simp]
/--
theorem `map_top` / 定理 `map_top`

English:
theorem map_top
  given: (f : Nat -> α)
  statement: map f ⊤ = ⊤
  proof: rfl

@[simp]

中文:
定理 map_top
  条件: (f : 自然数 -> α)
  结论: map f ⊤ = ⊤
  证明: rfl

@[simp]
-/
theorem map_top (f : Nat -> α) : map f ⊤ = ⊤ := rfl

@[simp]
/--
theorem `map_natCast` / 定理 `map_natCast`

English:
theorem map_natCast
  given: (f : Nat -> α) (a : Nat)
  statement: map f a = f a
  proof: rfl

@[deprecated (since := "2026-07-17")] alias map_coe := map_natCast

@[simp]

中文:
定理 map_natCast
  条件: (f : 自然数 -> α) (a : 自然数)
  结论: map f a = f a
  证明: rfl

@[deprecated (since := "2026-07-17")] alias map_coe := map_natCast

@[simp]
-/
theorem map_natCast (f : Nat -> α) (a : Nat) : map f a = f a := rfl

@[deprecated (since := "2026-07-17")] alias map_coe := map_natCast

@[simp]
/--
theorem `map_zero` / 定理 `map_zero`

English:
theorem map_zero
  given: (f : Nat -> α)
  statement: map f 0 = f 0
  proof: rfl

@[simp]

中文:
定理 map_zero
  条件: (f : 自然数 -> α)
  结论: map f 0 = f 0
  证明: rfl

@[simp]
-/
protected theorem map_zero (f : Nat -> α) : map f 0 = f 0 := rfl

@[simp]
/--
theorem `map_one` / 定理 `map_one`

English:
theorem map_one
  given: (f : Nat -> α)
  statement: map f 1 = f 1
  proof: rfl

@[simp]

中文:
定理 map_one
  条件: (f : 自然数 -> α)
  结论: map f 1 = f 1
  证明: rfl

@[simp]
-/
protected theorem map_one (f : Nat -> α) : map f 1 = f 1 := rfl

@[simp]
/--
theorem `map_ofNat` / 定理 `map_ofNat`

English:
theorem map_ofNat
  given: (f : Nat -> α) (n : Nat) [n.AtLeastTwo]
  statement: map f ofNat(n) = f n
  proof: rfl

@[simp]

中文:
定理 map_of自然数
  条件: (f : 自然数 -> α) (n : 自然数) [n.AtLeastTwo]
  结论: map f of自然数(n) = f n
  证明: rfl

@[simp]
-/
theorem map_ofNat (f : Nat -> α) (n : Nat) [n.AtLeastTwo] : map f ofNat(n) = f n := rfl

@[simp]
/--
lemma `map_eq_top_iff` / 引理 `map_eq_top_iff`

English:
lemma map_eq_top_iff
  given: {f : Nat -> α}
  statement: map f n = ⊤ ↔ n = ⊤
  proof: WithTop.map_eq_top_iff

@[simp]

中文:
引理 map_eq_top_iff
  条件: {f : 自然数 -> α}
  结论: map f n = ⊤ ↔ n = ⊤
  证明: WithTop.map_eq_top_iff

@[simp]

Depends on / 依赖: WithTop, WithTop.map_eq_top_iff, map_eq_top_iff
-/
lemma map_eq_top_iff {f : Nat -> α} : map f n = ⊤ ↔ n = ⊤ := WithTop.map_eq_top_iff

@[simp]
/--
theorem `strictMono_map_iff` / 定理 `strictMono_map_iff`

English:
theorem strictMono_map_iff
  given: {f : Nat -> α} [Preorder α]
  statement: StrictMono (ENat.map f) ↔ StrictMono f
  proof: WithTop.strictMono_map_iff

@[simp]

中文:
定理 strictMono_map_iff
  条件: {f : 自然数 -> α} [预序 α]
  结论: 严格递增 (E自然数.map f) ↔ 严格递增 f
  证明: WithTop.strictMono_map_iff

@[simp]

Depends on / 依赖: WithTop, WithTop.strictMono_map_iff, strictMono_map_iff
-/
theorem strictMono_map_iff {f : Nat -> α} [Preorder α] : StrictMono (ENat.map f) ↔ StrictMono f :=
  WithTop.strictMono_map_iff

@[simp]
/--
theorem `monotone_map_iff` / 定理 `monotone_map_iff`

English:
theorem monotone_map_iff
  given: {f : Nat -> α} [Preorder α]
  statement: Monotone (ENat.map f) ↔ Monotone f
  proof: WithTop.monotone_map_iff

中文:
定理 monotone_map_iff
  条件: {f : 自然数 -> α} [预序 α]
  结论: 递增 (E自然数.map f) ↔ 递增 f
  证明: WithTop.monotone_map_iff

Depends on / 依赖: WithTop, WithTop.monotone_map_iff, monotone_map_iff
-/
theorem monotone_map_iff {f : Nat -> α} [Preorder α] : Monotone (ENat.map f) ↔ Monotone f :=
  WithTop.monotone_map_iff

section AddMonoidWithOne
variable [AddMonoidWithOne α] [PartialOrder α] [AddLeftMono α] [ZeroLEOneClass α]

/--
lemma `map_natCast_nonneg` / 引理 `map_natCast_nonneg`

English:
lemma map_natCast_nonneg
  statement: 0 <= n.map (Nat.cast : Nat -> α)
  proof: by cases n <;> simp

中文:
引理 map_natCast_nonneg
  结论: 0 <= n.map (自然数.cast : 自然数 -> α)
  证明: by cases n <;> simp
-/
@[simp] lemma map_natCast_nonneg : 0 <= n.map (Nat.cast : Nat -> α) := by cases n <;> simp

variable [CharZero α]

/--
lemma `map_natCast_strictMono` / 引理 `map_natCast_strictMono`

English:
lemma map_natCast_strictMono
  statement: StrictMono (map (Nat.cast : Nat -> α))
  proof: strictMono_map_iff.2 Nat.strictMono_cast

中文:
引理 map_natCast_strictMono
  结论: 严格递增 (map (自然数.cast : 自然数 -> α))
  证明: strictMono_map_iff.2 Nat.strictMono_cast

Depends on / 依赖: Nat.strictMono_cast, strictMono_cast, strictMono_map_iff
-/
lemma map_natCast_strictMono : StrictMono (map (Nat.cast : Nat -> α)) :=
  strictMono_map_iff.2 Nat.strictMono_cast

/--
lemma `map_natCast_injective` / 引理 `map_natCast_injective`

English:
lemma map_natCast_injective
  statement: Injective (map (Nat.cast : Nat -> α))
  proof: map_natCast_strictMono.injective

中文:
引理 map_natCast_injective
  结论: 单射 (map (自然数.cast : 自然数 -> α))
  证明: map_natCast_strictMono.injective

Depends on / 依赖: injective, map_natCast_strictMono, map_natCast_strictMono.injective
-/
lemma map_natCast_injective : Injective (map (Nat.cast : Nat -> α)) := map_natCast_strictMono.injective

/--
lemma `map_natCast_inj` / 引理 `map_natCast_inj`

English:
lemma map_natCast_inj
  statement: m.map (Nat.cast : Nat -> α) = n.map Nat.cast ↔ m = n
  proof: map_natCast_injective.eq_iff

中文:
引理 map_natCast_inj
  结论: m.map (自然数.cast : 自然数 -> α) = n.map 自然数.cast ↔ m = n
  证明: map_natCast_injective.eq_iff
-/
@[simp] lemma map_natCast_inj : m.map (Nat.cast : Nat -> α) = n.map Nat.cast ↔ m = n :=
  map_natCast_injective.eq_iff

/--
lemma `map_natCast_eq_zero` / 引理 `map_natCast_eq_zero`

English:
lemma map_natCast_eq_zero
  statement: n.map (Nat.cast : Nat -> α) = 0 ↔ n = 0
  proof: by
  simp [← map_natCast_inj (α := α)]

中文:
引理 map_natCast_eq_zero
  结论: n.map (自然数.cast : 自然数 -> α) = 0 ↔ n = 0
  证明: by
  simp [← map_natCast_inj (α := α)]
-/
@[simp] lemma map_natCast_eq_zero : n.map (Nat.cast : Nat -> α) = 0 ↔ n = 0 := by
  simp [← map_natCast_inj (α := α)]

end AddMonoidWithOne

@[simp]
/--
theorem `map_add` / 定理 `map_add`

English:
theorem map_add
  statement: {β F} [Add β] [FunLike F Nat β] [AddHomClass F Nat β]
  proof: WithTop.map_add f a b

中文:
定理 map_add
  结论: {β F} [加法 β] [函数状 F 自然数 β] [加法态射类 F 自然数 β]
  证明: WithTop.map_add f a b
-/
protected theorem map_add {β F} [Add β] [FunLike F Nat β] [AddHomClass F Nat β]
    (f : F) (a b : Nat∞) : (a + b).map f = a.map f + b.map f :=
  WithTop.map_add f a b

-- @[to_additive (attr := simps -fullyApplied)
-- "A version of `ENat.map` for `ZeroHom`s"]
/--
Definition of `_root_.OneHom.ENatMap` / `_root_.OneHom.ENatMap` 的定义

English:
definition _root_.OneHom.ENatMap
  signature: {N : Type*} [One N] (f : OneHom Nat N)
  body: ENat.map f
  map_one' := by simp

中文:
定义 _root_.幺态射.E自然数Map
  签名: {N : 类型} [幺 N] (f : 幺态射 自然数 N)
  定义体: ENat.map f
  map_one' := by simp
-/
protected def _root_.OneHom.ENatMap {N : Type*} [One N] (f : OneHom Nat N) :
    OneHom Nat∞ (WithTop N) where
  toFun := ENat.map f
  map_one' := by simp

/--
Definition of `_root_.ZeroHom.ENatMap` / `_root_.ZeroHom.ENatMap` 的定义

English:
definition _root_.ZeroHom.ENatMap
  signature: {N : Type*} [Zero N] (f : ZeroHom Nat N)
  body: ENat.map f
  map_zero' := by simp

中文:
定义 _root_.保零态射.E自然数Map
  签名: {N : 类型} [零 N] (f : 保零态射 自然数 N)
  定义体: ENat.map f
  map_zero' := by simp
-/
protected def _root_.ZeroHom.ENatMap {N : Type*} [Zero N] (f : ZeroHom Nat N) :
    ZeroHom Nat∞ (WithTop N) where
  toFun := ENat.map f
  map_zero' := by simp

/-- A version of `WithTop.map` for `AddHom`s. -/
@[simps -fullyApplied]
/--
Definition of `_root_.AddHom.ENatMap` / `_root_.AddHom.ENatMap` 的定义

English:
definition _root_.AddHom.ENatMap
  signature: {N : Type*} [Add N] (f : AddHom Nat N)
  body: ENat.map f
  map_add' := ENat.map_add f

中文:
定义 _root_.加法半群态射.E自然数Map
  签名: {N : 类型} [加法 N] (f : 加法半群态射 自然数 N)
  定义体: ENat.map f
  map_add' := ENat.map_add f
-/
protected def _root_.AddHom.ENatMap {N : Type*} [Add N] (f : AddHom Nat N) :
    AddHom Nat∞ (WithTop N) where
  toFun := ENat.map f
  map_add' := ENat.map_add f

/-- A version of `WithTop.map` for `AddMonoidHom`s. -/
@[simps -fullyApplied]
/--
Definition of `_root_.AddMonoidHom.ENatMap` / `_root_.AddMonoidHom.ENatMap` 的定义

English:
definition _root_.AddMonoidHom.ENatMap
  signature: {N : Type*} [AddZeroClass N]
  body: { ZeroHom.ENatMap f.toZeroHom, AddHom.ENatMap f.toAddHom with toFun := ENat.map f }

中文:
定义 _root_.加法幺半群态射.E自然数Map
  签名: {N : 类型} [加法零类 N]
  定义体: { ZeroHom.ENatMap f.toZeroHom, AddHom.ENatMap f.toAddHom with toFun := ENat.map f }
-/
protected def _root_.AddMonoidHom.ENatMap {N : Type*} [AddZeroClass N]
    (f : Nat ->+ N) : Nat∞ ->+ WithTop N :=
  { ZeroHom.ENatMap f.toZeroHom, AddHom.ENatMap f.toAddHom with toFun := ENat.map f }

/-- A version of `ENat.map` for `MonoidWithZeroHom`s. -/
@[simps -fullyApplied]
/--
Definition of `_root_.MonoidWithZeroHom.ENatMap` / `_root_.MonoidWithZeroHom.ENatMap` 的定义

English:
definition _root_.MonoidWithZeroHom.ENatMap
  signature: {S : Type*} [MulZeroOneClass S] [DecidableEq S]
  body: { f.toZeroHom.ENatMap, f.toMonoidHom.toOneHom.ENatMap with
    toFun := ENat.map f
    map_mul' := fun x y => by
      have : forall z, map f z = 0 ↔ z = 0 := fun z =>
        (WithTop.map_injective hf).eq_iff' f.toZeroHom.ENatMap.map_zero
      rcases Decidable.eq_or_ne x 0 with (rfl | hx)
      · 

中文:
定义 _root_.带零幺半群态射.E自然数Map
  签名: {S : 类型} [乘零幺类 S] [DecidableEq S]
  定义体: { f.toZeroHom.ENatMap, f.toMonoidHom.toOneHom.ENatMap with
    toFun := ENat.map f
    map_mul' := fun x y => by
      have : forall z, map f z = 0 ↔ z = 0 := fun z =>
        (WithTop.map_injective hf).eq_iff' f.toZeroHom.ENatMap.map_zero
      rcases Decidable.eq_or_ne x 0 with (rfl | hx)
      · 
-/
protected def _root_.MonoidWithZeroHom.ENatMap {S : Type*} [MulZeroOneClass S] [DecidableEq S]
    [Nontrivial S] (f : Nat ->*₀ S)
    (hf : Function.Injective f) : Nat∞ ->*₀ WithTop S :=
  { f.toZeroHom.ENatMap, f.toMonoidHom.toOneHom.ENatMap with
    toFun := ENat.map f
    map_mul' := fun x y => by
      have : forall z, map f z = 0 ↔ z = 0 := fun z =>
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
          have : (f x : WithTop S) != 0 := by simpa [hf.eq_iff' (map_zero f)] using hx
          simp [mul_top hx, WithTop.mul_top this]
        | coe y => simp [← Nat.cast_mul, -natCast_mul] }

/-- A version of `ENat.map` for `RingHom`s. -/
@[simps -fullyApplied]
/--
Definition of `_root_.RingHom.ENatMap` / `_root_.RingHom.ENatMap` 的定义

English:
definition _root_.RingHom.ENatMap
  signature: {S : Type*} [CommSemiring S] [PartialOrder S]
  body: { MonoidWithZeroHom.ENatMap f.toMonoidWithZeroHom hf, f.toAddMonoidHom.ENatMap with }

@[simp]

中文:
定义 _root_.环态射.E自然数Map
  签名: {S : 类型} [交换半环 S] [偏序 S]
  定义体: { MonoidWithZeroHom.ENatMap f.toMonoidWithZeroHom hf, f.toAddMonoidHom.ENatMap with }

@[simp]
-/
protected def _root_.RingHom.ENatMap {S : Type*} [CommSemiring S] [PartialOrder S]
    [CanonicallyOrderedAdd S]
    [DecidableEq S] [Nontrivial S] (f : Nat ->+* S) (hf : Function.Injective f) : Nat∞ ->+* WithTop S :=
  { MonoidWithZeroHom.ENatMap f.toMonoidWithZeroHom hf, f.toAddMonoidHom.ENatMap with }

@[simp]
/--
lemma `map_natCast_mul` / 引理 `map_natCast_mul`

English:
lemma map_natCast_mul
  given: {R : Type*} [NonAssocSemiring R] [DecidableEq R] [CharZero R] (a b : Nat∞)
  proof: map_mul ((.ofClass (Nat.castRingHom R) : Nat ->*₀ R).ENatMap Nat.cast_injective) a b

中文:
引理 map_natCast_mul
  条件: {R : 类型} [非结合半环 R] [DecidableEq R] [特征零 R] (a b : 自然数∞)
  证明: map_mul ((.ofClass (Nat.castRingHom R) : Nat ->*₀ R).ENatMap Nat.cast_injective) a b

Depends on / 依赖: ENatMap, Nat.castRingHom, Nat.cast_injective, castRingHom, cast_injective, map_mul, ofClass
-/
lemma map_natCast_mul {R : Type*} [NonAssocSemiring R] [DecidableEq R] [CharZero R] (a b : Nat∞) :
    (map Nat.cast (a * b) : WithTop R) = map Nat.cast a * map Nat.cast b :=
  map_mul ((.ofClass (Nat.castRingHom R) : Nat ->*₀ R).ENatMap Nat.cast_injective) a b

end ENat

namespace ENat.WithBot

@[simp]
/--
lemma `coe_eq_natCast` / 引理 `coe_eq_natCast`

English:
lemma coe_eq_natCast
  given: (n : Nat)
  statement: (n : Nat∞) = (n : WithBot Nat∞)
  proof: rfl

中文:
引理 coe_eq_natCast
  条件: (n : 自然数)
  结论: (n : 自然数∞) = (n : WithBot 自然数∞)
  证明: rfl
-/
lemma coe_eq_natCast (n : Nat) : (n : Nat∞) = (n : WithBot Nat∞) := rfl

/--
lemma `eq_top_iff_forall_ge` / 引理 `eq_top_iff_forall_ge`

English:
lemma eq_top_iff_forall_ge
  given: {n : WithBot Nat∞}
  statement: n = ⊤ ↔ forall m : Nat, m <= n
  proof: _root_.WithBot.eq_top_iff_forall_ge

中文:
引理 eq_top_iff_对任意_ge
  条件: {n : WithBot 自然数∞}
  结论: n = ⊤ ↔ 对任意 m : 自然数, m <= n
  证明: _root_.WithBot.eq_top_iff_forall_ge

Depends on / 依赖: WithBot, _root_, _root_.WithBot.eq_top_iff_forall_ge, eq_top_iff_forall_ge
-/
lemma eq_top_iff_forall_ge {n : WithBot Nat∞} : n = ⊤ ↔ forall m : Nat, m <= n :=
  _root_.WithBot.eq_top_iff_forall_ge

/--
lemma `lt_add_one_iff` / 引理 `lt_add_one_iff`

English:
lemma lt_add_one_iff
  given: {n : WithBot Nat∞} {m : Nat}
  statement: n < m + 1 ↔ n <= m
  proof: by
  rw [← WithBot.coe_one]; rw [← ENat.natCast_one]; rw [WithBot.coe_natCast]; rw [← Nat.cast_add]; rw [← WithBot.coe_natCast]
  cases n
  · simp only [bot_le, WithBot.bot_lt_coe]
  · rw [WithBot.coe_lt_coe, Nat.cast_add, natCast_one, ENat.lt_add_one_iff (natCast_ne_top _),
      ← WithBot.coe_le_c

中文:
引理 lt_add_one_iff
  条件: {n : WithBot 自然数∞} {m : 自然数}
  结论: n < m + 1 ↔ n <= m
  证明: by
  rw [← WithBot.coe_one]; rw [← ENat.natCast_one]; rw [WithBot.coe_natCast]; rw [← Nat.cast_add]; rw [← WithBot.coe_natCast]
  cases n
  · simp only [bot_le, WithBot.bot_lt_coe]
  · rw [WithBot.coe_lt_coe, Nat.cast_add, natCast_one, ENat.lt_add_one_iff (natCast_ne_top _),
      ← WithBot.coe_le_c

Depends on / 依赖: ENat.lt_add_one_iff, ENat.natCast_one, Nat.cast_add, WithBot, WithBot.bot_lt_coe, WithBot.coe_le_coe, WithBot.coe_lt_coe, WithBot.coe_natCast, WithBot.coe_one, bot_le, bot_lt_coe, cast_add, coe_le_coe, coe_lt_coe, coe_natCast, coe_one, lt_add_one_iff, natCast_ne_top, natCast_one
-/
lemma lt_add_one_iff {n : WithBot Nat∞} {m : Nat} : n < m + 1 ↔ n <= m := by
  rw [← WithBot.coe_one]; rw [← ENat.natCast_one]; rw [WithBot.coe_natCast]; rw [← Nat.cast_add]; rw [← WithBot.coe_natCast]
  cases n
  · simp only [bot_le, WithBot.bot_lt_coe]
  · rw [WithBot.coe_lt_coe, Nat.cast_add, natCast_one, ENat.lt_add_one_iff (natCast_ne_top _),
      ← WithBot.coe_le_coe, WithBot.coe_natCast]

/--
lemma `add_one_le_iff` / 引理 `add_one_le_iff`

English:
lemma add_one_le_iff
  given: {n : Nat} {m : WithBot Nat∞}
  statement: n + 1 <= m ↔ n < m
  proof: by
  rw [← WithBot.coe_one]; rw [← natCast_one]; rw [WithBot.coe_natCast]; rw [← Nat.cast_add]; rw [← WithBot.coe_natCast]
  cases m
  · simp
  · rw [WithBot.coe_le_coe, natCast_add, natCast_one, ENat.add_one_le_iff (natCast_ne_top n),
      ← WithBot.coe_lt_coe, WithBot.coe_natCast]

中文:
引理 add_one_le_iff
  条件: {n : 自然数} {m : WithBot 自然数∞}
  结论: n + 1 <= m ↔ n < m
  证明: by
  rw [← WithBot.coe_one]; rw [← natCast_one]; rw [WithBot.coe_natCast]; rw [← Nat.cast_add]; rw [← WithBot.coe_natCast]
  cases m
  · simp
  · rw [WithBot.coe_le_coe, natCast_add, natCast_one, ENat.add_one_le_iff (natCast_ne_top n),
      ← WithBot.coe_lt_coe, WithBot.coe_natCast]

Depends on / 依赖: ENat.add_one_le_iff, Nat.cast_add, WithBot, WithBot.coe_le_coe, WithBot.coe_lt_coe, WithBot.coe_natCast, WithBot.coe_one, add_one_le_iff, cast_add, coe_le_coe, coe_lt_coe, coe_natCast, coe_one, natCast_add, natCast_ne_top, natCast_one
-/
lemma add_one_le_iff {n : Nat} {m : WithBot Nat∞} : n + 1 <= m ↔ n < m := by
  rw [← WithBot.coe_one]; rw [← natCast_one]; rw [WithBot.coe_natCast]; rw [← Nat.cast_add]; rw [← WithBot.coe_natCast]
  cases m
  · simp
  · rw [WithBot.coe_le_coe, natCast_add, natCast_one, ENat.add_one_le_iff (natCast_ne_top n),
      ← WithBot.coe_lt_coe, WithBot.coe_natCast]

/--
lemma `add_one_le_natCast_iff` / 引理 `add_one_le_natCast_iff`

English:
lemma add_one_le_natCast_iff
  given: {n : WithBot Nat∞} {m : Nat}
  statement: n + 1 <= m ↔ n < m
  proof: by
  induction n with
  | bot => simp
  | coe n =>
    norm_cast
    simp [add_one_le_iff']

@[simp]

中文:
引理 add_one_le_natCast_iff
  条件: {n : WithBot 自然数∞} {m : 自然数}
  结论: n + 1 <= m ↔ n < m
  证明: by
  induction n with
  | bot => simp
  | coe n =>
    norm_cast
    simp [add_one_le_iff']

@[simp]

Depends on / 依赖: add_one_le_iff
-/
lemma add_one_le_natCast_iff {n : WithBot Nat∞} {m : Nat} : n + 1 <= m ↔ n < m := by
  induction n with
  | bot => simp
  | coe n =>
    norm_cast
    simp [add_one_le_iff']

@[simp]
/--
lemma `add_one_le_zero_iff` / 引理 `add_one_le_zero_iff`

English:
lemma add_one_le_zero_iff
  given: (n : WithBot Nat∞)
  statement: n + 1 <= 0 ↔ n = ⊥
  proof: add_one_le_natCast_iff.trans (WithBot.lt_zero_iff_eq_bot n)

@[simp]

中文:
引理 add_one_le_zero_iff
  条件: (n : WithBot 自然数∞)
  结论: n + 1 <= 0 ↔ n = ⊥
  证明: add_one_le_natCast_iff.trans (WithBot.lt_zero_iff_eq_bot n)

@[simp]

Depends on / 依赖: WithBot, WithBot.lt_zero_iff_eq_bot, add_one_le_natCast_iff, add_one_le_natCast_iff.trans, lt_zero_iff_eq_bot
-/
lemma add_one_le_zero_iff (n : WithBot Nat∞) : n + 1 <= 0 ↔ n = ⊥ :=
  add_one_le_natCast_iff.trans (WithBot.lt_zero_iff_eq_bot n)

@[simp]
/--
lemma `add_natCast_cancel` / 引理 `add_natCast_cancel`

English:
lemma add_natCast_cancel
  given: {a b : WithBot Nat∞} {c : Nat}
  statement: a + c = b + c ↔ a = b
  proof: (IsAddRightRegular.all c).withTop.withBot.eq_iff

@[simp]

中文:
引理 add_natCast_cancel
  条件: {a b : WithBot 自然数∞} {c : 自然数}
  结论: a + c = b + c ↔ a = b
  证明: (IsAddRightRegular.all c).withTop.withBot.eq_iff

@[simp]

Depends on / 依赖: IsAddRightRegular, IsAddRightRegular.all, _eq_some_head, cyclicPermutations_ne_nil, eq_iff, head_cyclicPermutations, withBot, withTop, withTop.withBot.eq_iff
-/
lemma add_natCast_cancel {a b : WithBot Nat∞} {c : Nat} : a + c = b + c ↔ a = b :=
  (IsAddRightRegular.all c).withTop.withBot.eq_iff

@[simp]
/--
lemma `add_one_cancel` / 引理 `add_one_cancel`

English:
lemma add_one_cancel
  given: {a b : WithBot Nat∞}
  statement: a + 1 = b + 1 ↔ a = b
  proof: (IsAddRightRegular.all 1).withTop.withBot.eq_iff

中文:
引理 add_one_cancel
  条件: {a b : WithBot 自然数∞}
  结论: a + 1 = b + 1 ↔ a = b
  证明: (IsAddRightRegular.all 1).withTop.withBot.eq_iff

Depends on / 依赖: IsAddRightRegular, IsAddRightRegular.all, eq_iff, withBot, withTop, withTop.withBot.eq_iff
-/
lemma add_one_cancel {a b : WithBot Nat∞} : a + 1 = b + 1 ↔ a = b :=
  (IsAddRightRegular.all 1).withTop.withBot.eq_iff

/--
lemma `add_ofNat_cancel` / 引理 `add_ofNat_cancel`

English:
lemma add_ofNat_cancel
  given: {a b : WithBot Nat∞} {c : Nat} [c.AtLeastTwo]
  proof: WithBot.add_natCast_cancel

@[simp]

中文:
引理 add_of自然数_cancel
  条件: {a b : WithBot 自然数∞} {c : 自然数} [c.AtLeastTwo]
  证明: WithBot.add_natCast_cancel

@[simp]

Depends on / 依赖: WithBot, WithBot.add_natCast_cancel, add_natCast_cancel
-/
lemma add_ofNat_cancel {a b : WithBot Nat∞} {c : Nat} [c.AtLeastTwo] :
    a + ofNat(c) = b + ofNat(c) ↔ a = b :=
  WithBot.add_natCast_cancel

@[simp]
/--
lemma `natCast_add_cancel` / 引理 `natCast_add_cancel`

English:
lemma natCast_add_cancel
  given: {a b : WithBot Nat∞} {c : Nat}
  statement: c + a = c + b ↔ a = b
  proof: (IsAddLeftRegular.all c).withTop.withBot.eq_iff

@[simp]

中文:
引理 natCast_add_cancel
  条件: {a b : WithBot 自然数∞} {c : 自然数}
  结论: c + a = c + b ↔ a = b
  证明: (IsAddLeftRegular.all c).withTop.withBot.eq_iff

@[simp]

Depends on / 依赖: IsAddLeftRegular, IsAddLeftRegular.all, eq_iff, withBot, withTop, withTop.withBot.eq_iff
-/
lemma natCast_add_cancel {a b : WithBot Nat∞} {c : Nat} : c + a = c + b ↔ a = b :=
  (IsAddLeftRegular.all c).withTop.withBot.eq_iff

@[simp]
/--
lemma `one_add_cancel` / 引理 `one_add_cancel`

English:
lemma one_add_cancel
  given: {a b : WithBot Nat∞}
  statement: 1 + a = 1 + b ↔ a = b
  proof: (IsAddLeftRegular.all 1).withTop.withBot.eq_iff

中文:
引理 one_add_cancel
  条件: {a b : WithBot 自然数∞}
  结论: 1 + a = 1 + b ↔ a = b
  证明: (IsAddLeftRegular.all 1).withTop.withBot.eq_iff

Depends on / 依赖: IsAddLeftRegular, IsAddLeftRegular.all, eq_iff, withBot, withTop, withTop.withBot.eq_iff
-/
lemma one_add_cancel {a b : WithBot Nat∞} : 1 + a = 1 + b ↔ a = b :=
  (IsAddLeftRegular.all 1).withTop.withBot.eq_iff

/--
lemma `ofNat_add_cancel` / 引理 `ofNat_add_cancel`

English:
lemma ofNat_add_cancel
  given: {a b : WithBot Nat∞} {c : Nat} [c.AtLeastTwo]
  proof: WithBot.natCast_add_cancel

中文:
引理 of自然数_add_cancel
  条件: {a b : WithBot 自然数∞} {c : 自然数} [c.AtLeastTwo]
  证明: WithBot.natCast_add_cancel

Depends on / 依赖: WithBot, WithBot.natCast_add_cancel, natCast_add_cancel
-/
lemma ofNat_add_cancel {a b : WithBot Nat∞} {c : Nat} [c.AtLeastTwo] :
    ofNat(c) + a = ofNat(c) + b ↔ a = b :=
  WithBot.natCast_add_cancel

/--
lemma `add_le_add_natCast_right_iff` / 引理 `add_le_add_natCast_right_iff`

English:
lemma add_le_add_natCast_right_iff
  given: {a b : WithBot Nat∞} {c : Nat}
  statement: a + c <= b + c ↔ a <= b
  proof: (Contravariant.AddLECancellable (a := c)).withTop.withBot.add_le_add_iff_right

中文:
引理 add_le_add_natCast_right_iff
  条件: {a b : WithBot 自然数∞} {c : 自然数}
  结论: a + c <= b + c ↔ a <= b
  证明: (Contravariant.AddLECancellable (a := c)).withTop.withBot.add_le_add_iff_right

Depends on / 依赖: AddLECancellable, Contravariant, Contravariant.AddLECancellable, add_le_add_iff_right, withBot, withTop, withTop.withBot.add_le_add_iff_right
-/
lemma add_le_add_natCast_right_iff {a b : WithBot Nat∞} {c : Nat} : a + c <= b + c ↔ a <= b :=
  (Contravariant.AddLECancellable (a := c)).withTop.withBot.add_le_add_iff_right

/--
lemma `add_le_add_one_right_iff` / 引理 `add_le_add_one_right_iff`

English:
lemma add_le_add_one_right_iff
  given: {a b : WithBot Nat∞}
  statement: a + 1 <= b + 1 ↔ a <= b
  proof: WithBot.add_le_add_natCast_right_iff

中文:
引理 add_le_add_one_right_iff
  条件: {a b : WithBot 自然数∞}
  结论: a + 1 <= b + 1 ↔ a <= b
  证明: WithBot.add_le_add_natCast_right_iff

Depends on / 依赖: WithBot, WithBot.add_le_add_natCast_right_iff, add_le_add_natCast_right_iff
-/
lemma add_le_add_one_right_iff {a b : WithBot Nat∞} : a + 1 <= b + 1 ↔ a <= b :=
  WithBot.add_le_add_natCast_right_iff

/--
lemma `add_le_add_natCast_left_iff` / 引理 `add_le_add_natCast_left_iff`

English:
lemma add_le_add_natCast_left_iff
  given: {a b : WithBot Nat∞} {c : Nat}
  statement: c + a <= c + b ↔ a <= b
  proof: by
  rw [add_comm _ a]; rw [add_comm _ b]; rw [WithBot.add_le_add_natCast_right_iff]

中文:
引理 add_le_add_natCast_left_iff
  条件: {a b : WithBot 自然数∞} {c : 自然数}
  结论: c + a <= c + b ↔ a <= b
  证明: by
  rw [add_comm _ a]; rw [add_comm _ b]; rw [WithBot.add_le_add_natCast_right_iff]

Depends on / 依赖: WithBot, WithBot.add_le_add_natCast_right_iff, add_comm, add_le_add_natCast_right_iff
-/
lemma add_le_add_natCast_left_iff {a b : WithBot Nat∞} {c : Nat} : c + a <= c + b ↔ a <= b := by
  rw [add_comm _ a]; rw [add_comm _ b]; rw [WithBot.add_le_add_natCast_right_iff]

/--
lemma `add_le_add_one_left_iff` / 引理 `add_le_add_one_left_iff`

English:
lemma add_le_add_one_left_iff
  given: {a b : WithBot Nat∞}
  statement: 1 + a <= 1 + b ↔ a <= b
  proof: WithBot.add_le_add_natCast_left_iff

中文:
引理 add_le_add_one_left_iff
  条件: {a b : WithBot 自然数∞}
  结论: 1 + a <= 1 + b ↔ a <= b
  证明: WithBot.add_le_add_natCast_left_iff

Depends on / 依赖: WithBot, WithBot.add_le_add_natCast_left_iff, add_le_add_natCast_left_iff
-/
lemma add_le_add_one_left_iff {a b : WithBot Nat∞} : 1 + a <= 1 + b ↔ a <= b :=
  WithBot.add_le_add_natCast_left_iff

end ENat.WithBot
