/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Order.Ring.WithTop
public import Mathlib.Algebra.Order.Sub.WithTop
public import Mathlib.Data.NNReal.Defs
public import Mathlib.Order.Interval.Set.WithBotTop

/-!
# Extended non-negative reals

We define `ENNReal = ℝ≥0∞ := WithTop ℝ≥0` to be the type of extended nonnegative real numbers,
i.e., the interval `[0, +∞]`. This type is used as the codomain of a `MeasureTheory.Measure`,
and of the extended distance `edist` in an `EMetricSpace`.

In this file we set up many of the instances on `ℝ≥0∞`, and provide relationships between `ℝ≥0∞` and
`ℝ≥0`, and between `ℝ≥0∞` and `ℝ`. In particular, we provide a coercion from `ℝ≥0` to `ℝ≥0∞` as well
as functions `ENNReal.toNNReal`, `ENNReal.ofReal` and `ENNReal.toReal`, all of which take the value
zero wherever they cannot be the identity. Also included is the relationship between `ℝ≥0∞` and `ℕ`.
The interaction of these functions, especially `ENNReal.ofReal` and `ENNReal.toReal`, with the
algebraic and lattice structure can be found in `Data.ENNReal.Real`.

This file proves many of the order properties of `ℝ≥0∞`, with the exception of the ways those relate
to the algebraic structure, which are included in `Data.ENNReal.Operations`.
This file also defines inversion and division: this includes `Inv` and `Div` instances on `ℝ≥0∞`
making it into a `DivInvOneMonoid`.
As a consequence of being a `DivInvOneMonoid`, `ℝ≥0∞` inherits a power operation with integer
exponent: this and other properties is shown in `Data.ENNReal.Inv`.


## Main definitions

* `ℝ≥0∞`: the extended nonnegative real numbers `[0, ∞]`; defined as `WithTop ℝ≥0`; it is
  equipped with the following structures:

  - coercion from `ℝ≥0` defined in the natural way;

  - the natural structure of a complete dense linear order: `↑p ≤ ↑q ↔ p ≤ q` and `∀ a, a ≤ ∞`;

  - `a + b` is defined so that `↑p + ↑q = ↑(p + q)` for `(p q : ℝ≥0)` and `a + ∞ = ∞ + a = ∞`;

  - `a * b` is defined so that `↑p * ↑q = ↑(p * q)` for `(p q : ℝ≥0)`, `0 * ∞ = ∞ * 0 = 0`, and
    `a * ∞ = ∞ * a = ∞` for `a ≠ 0`;

  - `a - b` is defined as the minimal `d` such that `a ≤ d + b`; this way we have
    `↑p - ↑q = ↑(p - q)`, `∞ - ↑p = ∞`, `↑p - ∞ = ∞ - ∞ = 0`; note that there is no negation, only
    subtraction;

  The addition and multiplication defined this way together with `0 = ↑0` and `1 = ↑1` turn
  `ℝ≥0∞` into a canonically ordered commutative semiring of characteristic zero.

  - `a⁻¹` is defined as `Inf {b | 1 ≤ a * b}`. This way we have `(↑p)⁻¹ = ↑(p⁻¹)` for
    `p : ℝ≥0`, `p ≠ 0`, `0⁻¹ = ∞`, and `∞⁻¹ = 0`.
  - `a / b` is defined as `a * b⁻¹`.

  This inversion and division include `Inv` and `Div` instances on `ℝ≥0∞`,
  making it into a `DivInvOneMonoid`. Further properties of these are shown in `Data.ENNReal.Inv`.

* Coercions to/from other types:

  - coercion `ℝ≥0 → ℝ≥0∞` is defined as `Coe`, so one can use `(p : ℝ≥0)` in a context that
    expects `a : ℝ≥0∞`, and Lean will apply `coe` automatically;

  - `ENNReal.toNNReal` sends `↑p` to `p` and `∞` to `0`;

  - `ENNReal.toReal := coe ∘ ENNReal.toNNReal` sends `↑p`, `p : ℝ≥0` to `(↑p : ℝ)` and `∞` to `0`;

  - `ENNReal.ofReal := coe ∘ Real.toNNReal` sends `x : ℝ` to `↑⟨max x 0, _⟩`

  - `ENNReal.neTopEquivNNReal` is an equivalence between `{a : ℝ≥0∞ // a ≠ 0}` and `ℝ≥0`.

## Implementation notes

We define a `CanLift ℝ≥0∞ ℝ≥0` instance, so one of the ways to prove theorems about an `ℝ≥0∞`
number `a` is to consider the cases `a = ∞` and `a ≠ ∞`, and use the tactic `lift a to ℝ≥0 using ha`
in the second case. This instance is even more useful if one already has `ha : a ≠ ∞` in the
context, or if we have `(f : α → ℝ≥0∞) (hf : ∀ x, f x ≠ ∞)`.

## Notation

* `ℝ≥0∞`: the type of the extended nonnegative real numbers;
* `ℝ≥0`: the type of nonnegative real numbers `[0, ∞)`; defined in `Data.Real.NNReal`;
* `∞`: a localized notation in `ENNReal` for `⊤ : ℝ≥0∞`.

-/

@[expose] public section

assert_not_exists Finset

open Function Set NNReal

variable {α : Type*}

/--
Definition of `ENNReal` / `ENNReal` 的定义

English:
definition ENNReal
  body: WithTop Real>=0

@[inherit_doc]
scoped[ENNReal] notation "Real>=0∞" => ENNReal

中文:
定义 广义非负实数
  定义体: WithTop Real>=0

@[inherit_doc]
scoped[ENNReal] notation "Real>=0∞" => ENNReal

Depends on / 依赖: WithTop
-/
def ENNReal := WithTop Real>=0

@[inherit_doc]
scoped[ENNReal] notation "Real>=0∞" => ENNReal

-- note: using notation3 rather than notation means that `∞` pretty-prints
-- as `∞` rather than `top`. Despite this, we still use `top` in the names of lemmas.
/-- Notation for infinity as an `ENNReal` number. -/
scoped[ENNReal] notation3 "∞" => (⊤ : ENNReal)

namespace ENNReal

/--
Definition of `ofNNReal` / `ofNNReal` 的定义

English:
definition ofNNReal
  signature: : Real>=0 -> Real>=0∞
  body: WithTop.some

中文:
定义 ofNN实数
  签名: : 实数>=0 -> 实数>=0∞
  定义体: WithTop.some
-/
@[coe, match_pattern] def ofNNReal : Real>=0 -> Real>=0∞ := WithTop.some

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe Real>=0 Real>=0∞
  body: ⟨ofNNReal⟩

中文:
实例 :
  签名: Coe 实数>=0 实数>=0∞
  定义体: ⟨ofNNReal⟩

Depends on / 依赖: ofNNReal
-/
instance : Coe Real>=0 Real>=0∞ := ⟨ofNNReal⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero Real>=0∞
  body: ⟨ofNNReal 0⟩

中文:
实例 :
  签名: 零 实数>=0∞
  定义体: ⟨ofNNReal 0⟩

Depends on / 依赖: ofNNReal
-/
instance : Zero Real>=0∞ := ⟨ofNNReal 0⟩
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One Real>=0∞
  body: ⟨ofNNReal 1⟩

中文:
实例 :
  签名: 幺 实数>=0∞
  定义体: ⟨ofNNReal 1⟩

Depends on / 依赖: ofNNReal
-/
instance : One Real>=0∞ := ⟨ofNNReal 1⟩
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bot Real>=0∞
  body: ⟨0⟩

example : (0 : Real>=0∞) = ⊥ := by with_reducible_and_instances rfl

deriving instance Top, LE, PartialOrder, Add, AddCommMonoidWithOne, SemilatticeSup, DistribLattice,
  Nontrivial for ENNReal

中文:
实例 :
  签名: 底元素 实数>=0∞
  定义体: ⟨0⟩

example : (0 : Real>=0∞) = ⊥ := by with_reducible_and_instances rfl

deriving instance Top, LE, PartialOrder, Add, AddCommMonoidWithOne, SemilatticeSup, DistribLattice,
  Nontrivial for ENNReal
-/
instance : Bot Real>=0∞ := ⟨0⟩

example : (0 : Real>=0∞) = ⊥ := by with_reducible_and_instances rfl

deriving instance Top, LE, PartialOrder, Add, AddCommMonoidWithOne, SemilatticeSup, DistribLattice,
  Nontrivial for ENNReal

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderBot Real>=0∞
  body: inferInstanceAs (OrderBot (WithTop Real>=0))

中文:
实例 :
  签名: 有底序 实数>=0∞
  定义体: inferInstanceAs (OrderBot (WithTop Real>=0))

Depends on / 依赖: OrderBot, WithTop
-/
instance : OrderBot Real>=0∞ := inferInstanceAs (OrderBot (WithTop Real>=0))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderTop Real>=0∞
  body: inferInstanceAs (OrderTop (WithTop Real>=0))

中文:
实例 :
  签名: 有顶序 实数>=0∞
  定义体: inferInstanceAs (OrderTop (WithTop Real>=0))

Depends on / 依赖: OrderTop, WithTop
-/
instance : OrderTop Real>=0∞ := inferInstanceAs (OrderTop (WithTop Real>=0))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BoundedOrder Real>=0∞
  body: inferInstanceAs (BoundedOrder (WithTop Real>=0))

中文:
实例 :
  签名: 有界序 实数>=0∞
  定义体: inferInstanceAs (BoundedOrder (WithTop Real>=0))

Depends on / 依赖: BoundedOrder, WithTop
-/
instance : BoundedOrder Real>=0∞ := inferInstanceAs (BoundedOrder (WithTop Real>=0))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CharZero Real>=0∞
  body: inferInstanceAs (CharZero (WithTop Real>=0))

中文:
实例 :
  签名: 特征零 实数>=0∞
  定义体: inferInstanceAs (CharZero (WithTop Real>=0))

Depends on / 依赖: CharZero, WithTop
-/
instance : CharZero Real>=0∞ := inferInstanceAs (CharZero (WithTop Real>=0))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min Real>=0∞
  body: SemilatticeInf.toMin

中文:
实例 :
  签名: 最小值 实数>=0∞
  定义体: SemilatticeInf.toMin

Depends on / 依赖: SemilatticeInf, SemilatticeInf.toMin
-/
instance : Min Real>=0∞ := SemilatticeInf.toMin

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Max Real>=0∞
  body: SemilatticeSup.toMax

中文:
实例 :
  签名: 最大值 实数>=0∞
  定义体: SemilatticeSup.toMax

Depends on / 依赖: SemilatticeSup, SemilatticeSup.toMax
-/
instance : Max Real>=0∞ := SemilatticeSup.toMax

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommSemiring Real>=0∞
  body: inferInstanceAs (CommSemiring (WithTop Real>=0))

中文:
实例 :
  签名: 交换半环 实数>=0∞
  定义体: inferInstanceAs (CommSemiring (WithTop Real>=0))

Depends on / 依赖: CommSemiring, WithTop
-/
noncomputable instance : CommSemiring Real>=0∞ :=
  inferInstanceAs (CommSemiring (WithTop Real>=0))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsOrderedRing Real>=0∞
  body: inferInstanceAs (IsOrderedRing (WithTop Real>=0))

中文:
实例 :
  签名: 是Ordered环 实数>=0∞
  定义体: inferInstanceAs (IsOrderedRing (WithTop Real>=0))

Depends on / 依赖: IsOrderedRing, WithTop
-/
instance : IsOrderedRing Real>=0∞ :=
  inferInstanceAs (IsOrderedRing (WithTop Real>=0))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CanonicallyOrderedAdd Real>=0∞
  body: inferInstanceAs (CanonicallyOrderedAdd (WithTop Real>=0))

中文:
实例 :
  签名: 典范有序加法 实数>=0∞
  定义体: inferInstanceAs (CanonicallyOrderedAdd (WithTop Real>=0))

Depends on / 依赖: CanonicallyOrderedAdd, WithTop
-/
instance : CanonicallyOrderedAdd Real>=0∞ :=
  inferInstanceAs (CanonicallyOrderedAdd (WithTop Real>=0))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NoZeroDivisors Real>=0∞
  body: inferInstanceAs (NoZeroDivisors (WithTop Real>=0))

中文:
实例 :
  签名: 无零因子 实数>=0∞
  定义体: inferInstanceAs (NoZeroDivisors (WithTop Real>=0))

Depends on / 依赖: NoZeroDivisors, WithTop
-/
instance : NoZeroDivisors Real>=0∞ :=
  inferInstanceAs (NoZeroDivisors (WithTop Real>=0))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLinearOrder Real>=0∞
  body: inferInstanceAs (CompleteLinearOrder (WithTop Real>=0))

中文:
实例 :
  签名: 完备线性序 实数>=0∞
  定义体: inferInstanceAs (CompleteLinearOrder (WithTop Real>=0))

Depends on / 依赖: CompleteLinearOrder, WithTop
-/
noncomputable instance : CompleteLinearOrder Real>=0∞ :=
  inferInstanceAs (CompleteLinearOrder (WithTop Real>=0))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DenselyOrdered Real>=0∞
  body: inferInstanceAs (DenselyOrdered (WithTop Real>=0))

中文:
实例 :
  签名: 稠密序 实数>=0∞
  定义体: inferInstanceAs (DenselyOrdered (WithTop Real>=0))

Depends on / 依赖: DenselyOrdered, WithTop
-/
instance : DenselyOrdered Real>=0∞ := inferInstanceAs (DenselyOrdered (WithTop Real>=0))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommMonoid Real>=0∞
  body: inferInstanceAs (AddCommMonoid (WithTop Real>=0))

中文:
实例 :
  签名: 加法交换幺半群 实数>=0∞
  定义体: inferInstanceAs (AddCommMonoid (WithTop Real>=0))

Depends on / 依赖: AddCommMonoid, WithTop
-/
noncomputable instance : AddCommMonoid Real>=0∞ :=
  inferInstanceAs (AddCommMonoid (WithTop Real>=0))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LinearOrder Real>=0∞
  body: inferInstanceAs (LinearOrder (WithTop Real>=0))

中文:
实例 :
  签名: 线性序 实数>=0∞
  定义体: inferInstanceAs (LinearOrder (WithTop Real>=0))

Depends on / 依赖: LinearOrder, WithTop
-/
noncomputable instance : LinearOrder Real>=0∞ :=
  inferInstanceAs (LinearOrder (WithTop Real>=0))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsOrderedAddMonoid Real>=0∞
  body: inferInstanceAs (IsOrderedAddMonoid (WithTop Real>=0))

中文:
实例 :
  签名: 是OrderedAdd幺半群 实数>=0∞
  定义体: inferInstanceAs (IsOrderedAddMonoid (WithTop Real>=0))

Depends on / 依赖: IsOrderedAddMonoid, WithTop
-/
instance : IsOrderedAddMonoid Real>=0∞ :=
  inferInstanceAs (IsOrderedAddMonoid (WithTop Real>=0))

/--
Instance `instSub` / 实例 `instSub`

English:
instance instSub
  signature: : Sub Real>=0∞
  body: inferInstanceAs (Sub (WithTop Real>=0))

中文:
实例 instSub
  签名: : 减法 实数>=0∞
  定义体: inferInstanceAs (Sub (WithTop Real>=0))

Depends on / 依赖: WithTop
-/
instance instSub : Sub Real>=0∞ := inferInstanceAs (Sub (WithTop Real>=0))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderedSub Real>=0∞
  body: inferInstanceAs (OrderedSub (WithTop Real>=0))

中文:
实例 :
  签名: OrderedSub 实数>=0∞
  定义体: inferInstanceAs (OrderedSub (WithTop Real>=0))

Depends on / 依赖: OrderedSub, WithTop
-/
instance : OrderedSub Real>=0∞ := inferInstanceAs (OrderedSub (WithTop Real>=0))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LinearOrderedAddCommMonoidWithTop Real>=0∞
  body: inferInstanceAs (LinearOrderedAddCommMonoidWithTop (WithTop Real>=0))

中文:
实例 :
  签名: LinearOrderedAddComm幺半群带顶 实数>=0∞
  定义体: inferInstanceAs (LinearOrderedAddCommMonoidWithTop (WithTop Real>=0))

Depends on / 依赖: LinearOrderedAddCommMonoidWithTop, WithTop
-/
noncomputable instance : LinearOrderedAddCommMonoidWithTop Real>=0∞ :=
  inferInstanceAs (LinearOrderedAddCommMonoidWithTop (WithTop Real>=0))

-- RFC: redefine using pattern matching?
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inv Real>=0∞
  body: ⟨fun a => sInf { b | 1 <= a * b }⟩

中文:
实例 :
  签名: 取逆 实数>=0∞
  定义体: ⟨fun a => sInf { b | 1 <= a * b }⟩
-/
noncomputable instance : Inv Real>=0∞ := ⟨fun a => sInf { b | 1 <= a * b }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DivInvMonoid Real>=0∞

中文:
实例 :
  签名: 除逆幺半群 实数>=0∞
-/
noncomputable instance : DivInvMonoid Real>=0∞ where

variable {a b c d : Real>=0∞} {r p q : Real>=0} {n : Nat}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsOrderedMonoid Real>=0∞
  body: mul_le_mul_left

中文:
实例 :
  签名: 是Ordered幺半群 实数>=0∞
  定义体: mul_le_mul_left

Depends on / 依赖: mul_le_mul_left
-/
instance : IsOrderedMonoid Real>=0∞ where
  mul_le_mul_left _ _ := mul_le_mul_left

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Unique (AddUnits Real>=0∞)
  body: 0
uniq a := AddUnits.ext nonpos_iff_eq_zero.1 by rw [← a.add_neg]; exact le_self_add

中文:
实例 :
  签名: 唯一 (加法单位群 实数>=0∞)
  定义体: 0
uniq a := AddUnits.ext nonpos_iff_eq_zero.1 by rw [← a.add_neg]; exact le_self_add
-/
instance : Unique (AddUnits Real>=0∞) where
  default := 0
uniq a := AddUnits.ext nonpos_iff_eq_zero.1 by rw [← a.add_neg]; exact le_self_add

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited Real>=0∞
  body: ⟨0⟩

中文:
实例 :
  签名: 可居 实数>=0∞
  定义体: ⟨0⟩
-/
instance : Inhabited Real>=0∞ := ⟨0⟩

/-- A version of `WithTop.recTopCoe` that uses `ENNReal.ofNNReal`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
/--
Definition of `recTopCoe` / `recTopCoe` 的定义

English:
definition recTopCoe
  signature: {C : Real>=0∞ -> Sort*} (top : C ∞) (coe : forall x : Real>=0, C x) (x : Real>=0∞)
  body: WithTop.recTopCoe top coe x

中文:
定义 recTopCoe
  签名: {C : 实数>=0∞ -> 类型层*} (top : C ∞) (coe : 对任意 x : 实数>=0, C x) (x : 实数>=0∞)
  定义体: WithTop.recTopCoe top coe x

Depends on / 依赖: WithTop, WithTop.recTopCoe, recTopCoe
-/
def recTopCoe {C : Real>=0∞ -> Sort*} (top : C ∞) (coe : forall x : Real>=0, C x) (x : Real>=0∞) : C x :=
  WithTop.recTopCoe top coe x

/--
lemma `recTopCoe_top` / 引理 `recTopCoe_top`

English:
lemma recTopCoe_top
  given: {C : Real>=0∞ -> Sort*} (top : C ∞) (coe : forall x : Real>=0, C x)
  proof: rfl

中文:
引理 recTopCoe_top
  条件: {C : 实数>=0∞ -> 类型层*} (top : C ∞) (coe : 对任意 x : 实数>=0, C x)
  证明: rfl
-/
@[simp] lemma recTopCoe_top {C : Real>=0∞ -> Sort*} (top : C ∞) (coe : forall x : Real>=0, C x) :
    recTopCoe top coe ∞ = top := rfl

/--
lemma `recTopCoe_ofNNReal` / 引理 `recTopCoe_ofNNReal`

English:
lemma recTopCoe_ofNNReal
  given: {C : Real>=0∞ -> Sort*} (top : C ∞) (coe : forall x : Real>=0, C x) (x : Real>=0)
  proof: rfl

中文:
引理 recTopCoe_ofNN实数
  条件: {C : 实数>=0∞ -> 类型层*} (top : C ∞) (coe : 对任意 x : 实数>=0, C x) (x : 实数>=0)
  证明: rfl
-/
@[simp] lemma recTopCoe_ofNNReal {C : Real>=0∞ -> Sort*} (top : C ∞) (coe : forall x : Real>=0, C x) (x : Real>=0) :
    recTopCoe top coe x = coe x := rfl

/--
Instance `canLift` / 实例 `canLift`

English:
instance canLift
  signature: : CanLift Real>=0∞ Real>=0 ofNNReal (· != ∞)
  body: WithTop.canLift

中文:
实例 canLift
  签名: : CanLift 实数>=0∞ 实数>=0 ofNN实数 (· != ∞)
  定义体: WithTop.canLift

Depends on / 依赖: WithTop, WithTop.canLift, canLift
-/
instance canLift : CanLift Real>=0∞ Real>=0 ofNNReal (· != ∞) := WithTop.canLift

/--
theorem `none_eq_top` / 定理 `none_eq_top`

English:
theorem none_eq_top
  statement: (none : Real>=0∞) = ∞
  proof: rfl

中文:
定理 none_eq_top
  结论: (none : 实数>=0∞) = ∞
  证明: rfl
-/
@[simp] theorem none_eq_top : (none : Real>=0∞) = ∞ := rfl

/--
theorem `some_eq_coe` / 定理 `some_eq_coe`

English:
theorem some_eq_coe
  given: (a : Real>=0)
  statement: (Option.some a : Real>=0∞) = (↑a : Real>=0∞)
  proof: rfl

中文:
定理 some_eq_coe
  条件: (a : 实数>=0)
  结论: (选项类型.some a : 实数>=0∞) = (↑a : 实数>=0∞)
  证明: rfl
-/
@[simp] theorem some_eq_coe (a : Real>=0) : (Option.some a : Real>=0∞) = (↑a : Real>=0∞) := rfl

/--
theorem `some_eq_coe'` / 定理 `some_eq_coe'`

English:
theorem some_eq_coe'
  given: (a : Real>=0)
  statement: (WithTop.some a : Real>=0∞) = (↑a : Real>=0∞)
  proof: rfl

中文:
定理 some_eq_coe'
  条件: (a : 实数>=0)
  结论: (WithTop.some a : 实数>=0∞) = (↑a : 实数>=0∞)
  证明: rfl
-/
@[simp] theorem some_eq_coe' (a : Real>=0) : (WithTop.some a : Real>=0∞) = (↑a : Real>=0∞) := rfl

/--
lemma `coe_injective` / 引理 `coe_injective`

English:
lemma coe_injective
  statement: Injective ((↑) : Real>=0 -> Real>=0∞)
  proof: WithTop.coe_injective

中文:
引理 coe_injective
  结论: 单射 ((↑) : 实数>=0 -> 实数>=0∞)
  证明: WithTop.coe_injective

Depends on / 依赖: WithTop, WithTop.coe_injective, coe_injective
-/
lemma coe_injective : Injective ((↑) : Real>=0 -> Real>=0∞) := WithTop.coe_injective

/--
lemma `coe_inj` / 引理 `coe_inj`

English:
lemma coe_inj
  statement: (p : Real>=0∞) = q ↔ p = q
  proof: coe_injective.eq_iff

中文:
引理 coe_inj
  结论: (p : 实数>=0∞) = q ↔ p = q
  证明: coe_injective.eq_iff
-/
@[simp, norm_cast] lemma coe_inj : (p : Real>=0∞) = q ↔ p = q := coe_injective.eq_iff

/--
lemma `coe_ne_coe` / 引理 `coe_ne_coe`

English:
lemma coe_ne_coe
  statement: (p : Real>=0∞) != q ↔ p != q
  proof: coe_inj.not

中文:
引理 coe_ne_coe
  结论: (p : 实数>=0∞) != q ↔ p != q
  证明: coe_inj.not

Depends on / 依赖: coe_inj, coe_inj.not
-/
lemma coe_ne_coe : (p : Real>=0∞) != q ↔ p != q := coe_inj.not

/--
theorem `range_coe'` / 定理 `range_coe'`

English:
theorem range_coe'
  statement: range ofNNReal = Iio ∞
  proof: WithTop.range_coe

中文:
定理 range_coe'
  结论: range ofNN实数 = 左无界右开区间 ∞
  证明: WithTop.range_coe

Depends on / 依赖: WithTop, WithTop.range_coe, range_coe
-/
theorem range_coe' : range ofNNReal = Iio ∞ := WithTop.range_coe
/--
theorem `range_coe` / 定理 `range_coe`

English:
theorem range_coe
  statement: range ofNNReal = {∞}ᶜ
  proof: (isCompl_range_some_none Real>=0).symm.compl_eq.symm

中文:
定理 range_coe
  结论: range ofNN实数 = {∞}ᶜ
  证明: (isCompl_range_some_none Real>=0).symm.compl_eq.symm

Depends on / 依赖: compl_eq, isCompl_range_some_none, symm.compl_eq.symm
-/
theorem range_coe : range ofNNReal = {∞}ᶜ := (isCompl_range_some_none Real>=0).symm.compl_eq.symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NNRatCast Real>=0∞
  body: ofNNReal r

@[norm_cast]

中文:
实例 :
  签名: 非负有理数嵌入 实数>=0∞
  定义体: ofNNReal r

@[norm_cast]

Depends on / 依赖: ofNNReal
-/
instance : NNRatCast Real>=0∞ where
  nnratCast r := ofNNReal r

@[norm_cast]
/--
theorem `coe_nnratCast` / 定理 `coe_nnratCast`

English:
theorem coe_nnratCast
  given: (q : Rat>=0)
  statement: ↑(q : Real>=0) = (q : Real>=0∞)
  proof: rfl

中文:
定理 coe_nnratCast
  条件: (q : 有理数>=0)
  结论: ↑(q : 实数>=0) = (q : 实数>=0∞)
  证明: rfl
-/
theorem coe_nnratCast (q : Rat>=0) : ↑(q : Real>=0) = (q : Real>=0∞) := rfl

/--
Definition of `toNNReal` / `toNNReal` 的定义

English:
definition toNNReal
  signature: : Real>=0∞ -> Real>=0
  body: WithTop.untopD 0

中文:
定义 toNN实数
  签名: : 实数>=0∞ -> 实数>=0
  定义体: WithTop.untopD 0
-/
protected def toNNReal : Real>=0∞ -> Real>=0 := WithTop.untopD 0

/--
Definition of `toReal` / `toReal` 的定义

English:
definition toReal
  signature: (a : Real>=0∞)
  body: a.toNNReal

中文:
定义 to实数
  签名: (a : 实数>=0∞)
  定义体: a.toNNReal
-/
protected def toReal (a : Real>=0∞) : Real := a.toNNReal

/--
Definition of `ofReal` / `ofReal` 的定义

English:
definition ofReal
  signature: (r : Real)
  body: r.toNNReal

中文:
定义 of实数
  签名: (r : 实数)
  定义体: r.toNNReal
-/
protected def ofReal (r : Real) : Real>=0∞ := r.toNNReal

/--
lemma `toNNReal_coe` / 引理 `toNNReal_coe`

English:
lemma toNNReal_coe
  given: (r : Real>=0)
  statement: (r : Real>=0∞).toNNReal = r
  proof: rfl

@[simp]

中文:
引理 toNN实数_coe
  条件: (r : 实数>=0)
  结论: (r : 实数>=0∞).toNN实数 = r
  证明: rfl

@[simp]
-/
@[simp, norm_cast] lemma toNNReal_coe (r : Real>=0) : (r : Real>=0∞).toNNReal = r := rfl

@[simp]
/--
theorem `coe_toNNReal` / 定理 `coe_toNNReal`

English:
theorem coe_toNNReal
  statement: forall {a : Real>=0∞}, a != ∞ -> ↑a.toNNReal = a

中文:
定理 coe_toNN实数
  结论: 对任意 {a : 实数>=0∞}, a != ∞ -> ↑a.toNN实数 = a
-/
theorem coe_toNNReal : forall {a : Real>=0∞}, a != ∞ -> ↑a.toNNReal = a
  | ofNNReal _, _ => rfl
  | ⊤, h => (h rfl).elim

@[simp]
/--
theorem `coe_comp_toNNReal_comp` / 定理 `coe_comp_toNNReal_comp`

English:
theorem coe_comp_toNNReal_comp
  given: {ι : Type*} {f : ι -> Real>=0∞} (hf : forall x, f x != ∞)
  proof: by
  ext x
  simp [coe_toNNReal (hf x)]

@[simp]

中文:
定理 coe_comp_toNN实数_comp
  条件: {ι : 类型} {f : ι -> 实数>=0∞} (hf : 对任意 x, f x != ∞)
  证明: by
  ext x
  simp [coe_toNNReal (hf x)]

@[simp]

Depends on / 依赖: coe_toNNReal
-/
theorem coe_comp_toNNReal_comp {ι : Type*} {f : ι -> Real>=0∞} (hf : forall x, f x != ∞) :
    (fun (x : Real>=0) => (x : Real>=0∞)) ∘ ENNReal.toNNReal ∘ f = f := by
  ext x
  simp [coe_toNNReal (hf x)]

@[simp]
/--
theorem `ofReal_toReal` / 定理 `ofReal_toReal`

English:
theorem ofReal_toReal
  given: {a : Real>=0∞} (h : a != ∞)
  statement: ENNReal.ofReal a.toReal = a
  proof: by
  simp [ENNReal.toReal, ENNReal.ofReal, h]

@[simp]

中文:
定理 of实数_to实数
  条件: {a : 实数>=0∞} (h : a != ∞)
  结论: 广义非负实数.of实数 a.to实数 = a
  证明: by
  simp [ENNReal.toReal, ENNReal.ofReal, h]

@[simp]

Depends on / 依赖: ENNReal, ENNReal.ofReal, ENNReal.toReal, ofReal, toReal
-/
theorem ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNReal.ofReal a.toReal = a := by
  simp [ENNReal.toReal, ENNReal.ofReal, h]

@[simp]
/--
theorem `toReal_ofReal` / 定理 `toReal_ofReal`

English:
theorem toReal_ofReal
  given: {r : Real} (h : 0 <= r)
  statement: (ENNReal.ofReal r).toReal = r
  proof: max_eq_left h

中文:
定理 to实数_of实数
  条件: {r : 实数} (h : 0 <= r)
  结论: (广义非负实数.of实数 r).to实数 = r
  证明: max_eq_left h

Depends on / 依赖: max_eq_left
-/
theorem toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.ofReal r).toReal = r :=
  max_eq_left h

/--
theorem `toReal_ofReal'` / 定理 `toReal_ofReal'`

English:
theorem toReal_ofReal'
  given: {r : Real}
  statement: (ENNReal.ofReal r).toReal = max r 0
  proof: rfl

中文:
定理 to实数_of实数'
  条件: {r : 实数}
  结论: (广义非负实数.of实数 r).to实数 = 最大值 r 0
  证明: rfl
-/
theorem toReal_ofReal' {r : Real} : (ENNReal.ofReal r).toReal = max r 0 := rfl

/--
theorem `coe_toNNReal_le_self` / 定理 `coe_toNNReal_le_self`

English:
theorem coe_toNNReal_le_self
  statement: forall {a : Real>=0∞}, ↑a.toNNReal <= a

中文:
定理 coe_toNN实数_le_self
  结论: 对任意 {a : 实数>=0∞}, ↑a.toNN实数 <= a
-/
theorem coe_toNNReal_le_self : forall {a : Real>=0∞}, ↑a.toNNReal <= a
  | ofNNReal r => by rw [toNNReal_coe]
  | ⊤ => le_top

/--
theorem `coe_nnreal_eq` / 定理 `coe_nnreal_eq`

English:
theorem coe_nnreal_eq
  given: (r : Real>=0)
  statement: (r : Real>=0∞) = ENNReal.ofReal r
  proof: by
  rw [ENNReal.ofReal]; rw [Real.toNNReal_coe]

中文:
定理 coe_nnreal_eq
  条件: (r : 实数>=0)
  结论: (r : 实数>=0∞) = 广义非负实数.of实数 r
  证明: by
  rw [ENNReal.ofReal]; rw [Real.toNNReal_coe]

Depends on / 依赖: ENNReal, ENNReal.ofReal, Real.toNNReal_coe, ofReal, toNNReal_coe
-/
theorem coe_nnreal_eq (r : Real>=0) : (r : Real>=0∞) = ENNReal.ofReal r := by
  rw [ENNReal.ofReal]; rw [Real.toNNReal_coe]

/--
theorem `ofReal_eq_coe_nnreal` / 定理 `ofReal_eq_coe_nnreal`

English:
theorem ofReal_eq_coe_nnreal
  given: {x : Real} (h : 0 <= x)
  proof: (coe_nnreal_eq ⟨x, h⟩).symm

中文:
定理 of实数_eq_coe_nnreal
  条件: {x : 实数} (h : 0 <= x)
  证明: (coe_nnreal_eq ⟨x, h⟩).symm

Depends on / 依赖: coe_nnreal_eq
-/
theorem ofReal_eq_coe_nnreal {x : Real} (h : 0 <= x) :
    ENNReal.ofReal x = ofNNReal (NNReal.mk x h) :=
  (coe_nnreal_eq ⟨x, h⟩).symm

/--
theorem `ofNNReal_toNNReal` / 定理 `ofNNReal_toNNReal`

English:
theorem ofNNReal_toNNReal
  given: (x : Real)
  statement: (Real.toNNReal x : Real>=0∞) = ENNReal.ofReal x
  proof: rfl

中文:
定理 ofNN实数_toNN实数
  条件: (x : 实数)
  结论: (实数.toNN实数 x : 实数>=0∞) = 广义非负实数.of实数 x
  证明: rfl
-/
theorem ofNNReal_toNNReal (x : Real) : (Real.toNNReal x : Real>=0∞) = ENNReal.ofReal x := rfl

/--
theorem `ofReal_coe_nnreal` / 定理 `ofReal_coe_nnreal`

English:
theorem ofReal_coe_nnreal
  statement: ENNReal.ofReal p = p
  proof: (coe_nnreal_eq p).symm

中文:
定理 of实数_coe_nnreal
  结论: 广义非负实数.of实数 p = p
  证明: (coe_nnreal_eq p).symm
-/
@[simp] theorem ofReal_coe_nnreal : ENNReal.ofReal p = p := (coe_nnreal_eq p).symm

/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ↑(0 : Real>=0) = (0 : Real>=0∞)
  proof: rfl

中文:
定理 coe_zero
  结论: ↑(0 : 实数>=0) = (0 : 实数>=0∞)
  证明: rfl
-/
@[simp, norm_cast] theorem coe_zero : ↑(0 : Real>=0) = (0 : Real>=0∞) := rfl

/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ↑(1 : Real>=0) = (1 : Real>=0∞)
  proof: rfl

中文:
定理 coe_one
  结论: ↑(1 : 实数>=0) = (1 : 实数>=0∞)
  证明: rfl
-/
@[simp, norm_cast] theorem coe_one : ↑(1 : Real>=0) = (1 : Real>=0∞) := rfl

/--
theorem `toReal_nonneg` / 定理 `toReal_nonneg`

English:
theorem toReal_nonneg
  given: {a : Real>=0∞}
  statement: 0 <= a.toReal
  proof: a.toNNReal.2

中文:
定理 to实数_nonneg
  条件: {a : 实数>=0∞}
  结论: 0 <= a.to实数
  证明: a.toNNReal.2
-/
@[simp] theorem toReal_nonneg {a : Real>=0∞} : 0 <= a.toReal := a.toNNReal.2

/--
theorem `coe_toNNReal_eq_toReal` / 定理 `coe_toNNReal_eq_toReal`

English:
theorem coe_toNNReal_eq_toReal
  given: (z : Real>=0∞)
  statement: (z.toNNReal : Real) = z.toReal
  proof: rfl

中文:
定理 coe_toNN实数_eq_to实数
  条件: (z : 实数>=0∞)
  结论: (z.toNN实数 : 实数) = z.to实数
  证明: rfl
-/
@[norm_cast] theorem coe_toNNReal_eq_toReal (z : Real>=0∞) : (z.toNNReal : Real) = z.toReal := rfl

/--
theorem `toNNReal_toReal_eq` / 定理 `toNNReal_toReal_eq`

English:
theorem toNNReal_toReal_eq
  given: (z : Real>=0∞)
  statement: z.toReal.toNNReal = z.toNNReal
  proof: by
  ext; simp [coe_toNNReal_eq_toReal]

中文:
定理 toNN实数_to实数_eq
  条件: (z : 实数>=0∞)
  结论: z.to实数.toNN实数 = z.toNN实数
  证明: by
  ext; simp [coe_toNNReal_eq_toReal]
-/
@[simp] theorem toNNReal_toReal_eq (z : Real>=0∞) : z.toReal.toNNReal = z.toNNReal := by
  ext; simp [coe_toNNReal_eq_toReal]

/--
theorem `toNNReal_top` / 定理 `toNNReal_top`

English:
theorem toNNReal_top
  statement: ∞.toNNReal = 0
  proof: rfl

中文:
定理 toNN实数_top
  结论: ∞.toNN实数 = 0
  证明: rfl
-/
@[simp] theorem toNNReal_top : ∞.toNNReal = 0 := rfl

/--
theorem `toReal_top` / 定理 `toReal_top`

English:
theorem toReal_top
  statement: ∞.toReal = 0
  proof: rfl

中文:
定理 to实数_top
  结论: ∞.to实数 = 0
  证明: rfl
-/
@[simp] theorem toReal_top : ∞.toReal = 0 := rfl

/--
theorem `toReal_one` / 定理 `toReal_one`

English:
theorem toReal_one
  statement: (1 : Real>=0∞).toReal = 1
  proof: rfl

中文:
定理 to实数_one
  结论: (1 : 实数>=0∞).to实数 = 1
  证明: rfl
-/
@[simp] theorem toReal_one : (1 : Real>=0∞).toReal = 1 := rfl

/--
theorem `toNNReal_one` / 定理 `toNNReal_one`

English:
theorem toNNReal_one
  statement: (1 : Real>=0∞).toNNReal = 1
  proof: rfl

中文:
定理 toNN实数_one
  结论: (1 : 实数>=0∞).toNN实数 = 1
  证明: rfl
-/
@[simp] theorem toNNReal_one : (1 : Real>=0∞).toNNReal = 1 := rfl

/--
theorem `coe_toReal` / 定理 `coe_toReal`

English:
theorem coe_toReal
  given: (r : Real>=0)
  statement: (r : Real>=0∞).toReal = r
  proof: rfl

中文:
定理 coe_to实数
  条件: (r : 实数>=0)
  结论: (r : 实数>=0∞).to实数 = r
  证明: rfl
-/
@[simp] theorem coe_toReal (r : Real>=0) : (r : Real>=0∞).toReal = r := rfl

/--
theorem `toNNReal_zero` / 定理 `toNNReal_zero`

English:
theorem toNNReal_zero
  statement: (0 : Real>=0∞).toNNReal = 0
  proof: rfl

中文:
定理 toNN实数_zero
  结论: (0 : 实数>=0∞).toNN实数 = 0
  证明: rfl
-/
@[simp] theorem toNNReal_zero : (0 : Real>=0∞).toNNReal = 0 := rfl

/--
theorem `toReal_zero` / 定理 `toReal_zero`

English:
theorem toReal_zero
  statement: (0 : Real>=0∞).toReal = 0
  proof: rfl

中文:
定理 to实数_zero
  结论: (0 : 实数>=0∞).to实数 = 0
  证明: rfl
-/
@[simp] theorem toReal_zero : (0 : Real>=0∞).toReal = 0 := rfl

/--
theorem `ofReal_zero` / 定理 `ofReal_zero`

English:
theorem ofReal_zero
  statement: ENNReal.ofReal (0 : Real) = 0
  proof: by simp [ENNReal.ofReal]

中文:
定理 of实数_zero
  结论: 广义非负实数.of实数 (0 : 实数) = 0
  证明: by simp [ENNReal.ofReal]
-/
@[simp] theorem ofReal_zero : ENNReal.ofReal (0 : Real) = 0 := by simp [ENNReal.ofReal]

/--
theorem `ofReal_one` / 定理 `ofReal_one`

English:
theorem ofReal_one
  statement: ENNReal.ofReal (1 : Real) = (1 : Real>=0∞)
  proof: by simp [ENNReal.ofReal]

中文:
定理 of实数_one
  结论: 广义非负实数.of实数 (1 : 实数) = (1 : 实数>=0∞)
  证明: by simp [ENNReal.ofReal]
-/
@[simp] theorem ofReal_one : ENNReal.ofReal (1 : Real) = (1 : Real>=0∞) := by simp [ENNReal.ofReal]

/--
theorem `ofReal_toReal_le` / 定理 `ofReal_toReal_le`

English:
theorem ofReal_toReal_le
  given: {a : Real>=0∞}
  statement: ENNReal.ofReal a.toReal <= a
  proof: if ha : a = ∞ then ha.symm ▸ le_top else le_of_eq (ofReal_toReal ha)

中文:
定理 of实数_to实数_le
  条件: {a : 实数>=0∞}
  结论: 广义非负实数.of实数 a.to实数 <= a
  证明: if ha : a = ∞ then ha.symm ▸ le_top else le_of_eq (ofReal_toReal ha)

Depends on / 依赖: ha.symm, le_of_eq, le_top, ofReal_toReal
-/
theorem ofReal_toReal_le {a : Real>=0∞} : ENNReal.ofReal a.toReal <= a :=
  if ha : a = ∞ then ha.symm ▸ le_top else le_of_eq (ofReal_toReal ha)

/--
theorem `forall_ennreal` / 定理 `forall_ennreal`

English:
theorem forall_ennreal
  given: {p : Real>=0∞ -> Prop}
  statement: (forall a, p a) ↔ (forall r : Real>=0, p r) ∧ p ∞
  proof: WithTop.forall.trans and_comm

中文:
定理 对任意_ennreal
  条件: {p : 实数>=0∞ -> 命题}
  结论: (对任意 a, p a) ↔ (对任意 r : 实数>=0, p r) ∧ p ∞
  证明: WithTop.forall.trans and_comm

Depends on / 依赖: WithTop, WithTop.forall.trans, and_comm
-/
theorem forall_ennreal {p : Real>=0∞ -> Prop} : (forall a, p a) ↔ (forall r : Real>=0, p r) ∧ p ∞ :=
  WithTop.forall.trans and_comm

/--
theorem `forall_ne_top` / 定理 `forall_ne_top`

English:
theorem forall_ne_top
  given: {p : Real>=0∞ -> Prop}
  statement: (forall x != ∞, p x) ↔ forall x : Real>=0, p x
  proof: WithTop.forall_ne_top

中文:
定理 对任意_ne_top
  条件: {p : 实数>=0∞ -> 命题}
  结论: (对任意 x != ∞, p x) ↔ 对任意 x : 实数>=0, p x
  证明: WithTop.forall_ne_top

Depends on / 依赖: WithTop, WithTop.forall_ne_top, forall_ne_top
-/
theorem forall_ne_top {p : Real>=0∞ -> Prop} : (forall x != ∞, p x) ↔ forall x : Real>=0, p x :=
  WithTop.forall_ne_top

/--
theorem `exists_ne_top` / 定理 `exists_ne_top`

English:
theorem exists_ne_top
  given: {p : Real>=0∞ -> Prop}
  statement: (exists x != ∞, p x) ↔ exists x : Real>=0, p x
  proof: WithTop.exists_ne_top

中文:
定理 存在_ne_top
  条件: {p : 实数>=0∞ -> 命题}
  结论: (存在 x != ∞, p x) ↔ 存在 x : 实数>=0, p x
  证明: WithTop.exists_ne_top

Depends on / 依赖: WithTop, WithTop.exists_ne_top, exists_ne_top
-/
theorem exists_ne_top {p : Real>=0∞ -> Prop} : (exists x != ∞, p x) ↔ exists x : Real>=0, p x :=
  WithTop.exists_ne_top

/--
theorem `toNNReal_eq_zero_iff` / 定理 `toNNReal_eq_zero_iff`

English:
theorem toNNReal_eq_zero_iff
  given: (x : Real>=0∞)
  statement: x.toNNReal = 0 ↔ x = 0 ∨ x = ∞
  proof: WithTop.untopD_eq_self_iff

中文:
定理 toNN实数_eq_zero_iff
  条件: (x : 实数>=0∞)
  结论: x.toNN实数 = 0 ↔ x = 0 ∨ x = ∞
  证明: WithTop.untopD_eq_self_iff

Depends on / 依赖: WithTop, WithTop.untopD_eq_self_iff, untopD_eq_self_iff
-/
theorem toNNReal_eq_zero_iff (x : Real>=0∞) : x.toNNReal = 0 ↔ x = 0 ∨ x = ∞ :=
  WithTop.untopD_eq_self_iff

/--
theorem `toReal_eq_zero_iff` / 定理 `toReal_eq_zero_iff`

English:
theorem toReal_eq_zero_iff
  given: (x : Real>=0∞)
  statement: x.toReal = 0 ↔ x = 0 ∨ x = ∞
  proof: by
  simp [ENNReal.toReal, toNNReal_eq_zero_iff]

中文:
定理 to实数_eq_zero_iff
  条件: (x : 实数>=0∞)
  结论: x.to实数 = 0 ↔ x = 0 ∨ x = ∞
  证明: by
  simp [ENNReal.toReal, toNNReal_eq_zero_iff]

Depends on / 依赖: ENNReal, ENNReal.toReal, toNNReal_eq_zero_iff, toReal
-/
theorem toReal_eq_zero_iff (x : Real>=0∞) : x.toReal = 0 ↔ x = 0 ∨ x = ∞ := by
  simp [ENNReal.toReal, toNNReal_eq_zero_iff]

/--
theorem `toNNReal_ne_zero` / 定理 `toNNReal_ne_zero`

English:
theorem toNNReal_ne_zero
  statement: a.toNNReal != 0 ↔ a != 0 ∧ a != ∞
  proof: a.toNNReal_eq_zero_iff.not.trans not_or

中文:
定理 toNN实数_ne_zero
  结论: a.toNN实数 != 0 ↔ a != 0 ∧ a != ∞
  证明: a.toNNReal_eq_zero_iff.not.trans not_or

Depends on / 依赖: a.toNNReal_eq_zero_iff.not.trans, not_or, toNNReal_eq_zero_iff
-/
theorem toNNReal_ne_zero : a.toNNReal != 0 ↔ a != 0 ∧ a != ∞ :=
  a.toNNReal_eq_zero_iff.not.trans not_or

/--
theorem `toReal_ne_zero` / 定理 `toReal_ne_zero`

English:
theorem toReal_ne_zero
  statement: a.toReal != 0 ↔ a != 0 ∧ a != ∞
  proof: a.toReal_eq_zero_iff.not.trans not_or

中文:
定理 to实数_ne_zero
  结论: a.to实数 != 0 ↔ a != 0 ∧ a != ∞
  证明: a.toReal_eq_zero_iff.not.trans not_or

Depends on / 依赖: a.toReal_eq_zero_iff.not.trans, not_or, toReal_eq_zero_iff
-/
theorem toReal_ne_zero : a.toReal != 0 ↔ a != 0 ∧ a != ∞ :=
  a.toReal_eq_zero_iff.not.trans not_or

set_option backward.isDefEq.respectTransparency false in
/--
theorem `toNNReal_eq_one_iff` / 定理 `toNNReal_eq_one_iff`

English:
theorem toNNReal_eq_one_iff
  given: (x : Real>=0∞)
  statement: x.toNNReal = 1 ↔ x = 1
  proof: WithTop.untopD_eq_iff.trans by simp

中文:
定理 toNN实数_eq_one_iff
  条件: (x : 实数>=0∞)
  结论: x.toNN实数 = 1 ↔ x = 1
  证明: WithTop.untopD_eq_iff.trans by simp

Depends on / 依赖: WithTop, WithTop.untopD_eq_iff.trans, untopD_eq_iff
-/
theorem toNNReal_eq_one_iff (x : Real>=0∞) : x.toNNReal = 1 ↔ x = 1 :=
WithTop.untopD_eq_iff.trans by simp

/--
theorem `toReal_eq_one_iff` / 定理 `toReal_eq_one_iff`

English:
theorem toReal_eq_one_iff
  given: (x : Real>=0∞)
  statement: x.toReal = 1 ↔ x = 1
  proof: by
  rw [ENNReal.toReal]; rw [NNReal.coe_eq_one]; rw [ENNReal.toNNReal_eq_one_iff]

中文:
定理 to实数_eq_one_iff
  条件: (x : 实数>=0∞)
  结论: x.to实数 = 1 ↔ x = 1
  证明: by
  rw [ENNReal.toReal]; rw [NNReal.coe_eq_one]; rw [ENNReal.toNNReal_eq_one_iff]

Depends on / 依赖: ENNReal, ENNReal.toNNReal_eq_one_iff, ENNReal.toReal, NNReal, NNReal.coe_eq_one, coe_eq_one, toNNReal_eq_one_iff, toReal
-/
theorem toReal_eq_one_iff (x : Real>=0∞) : x.toReal = 1 ↔ x = 1 := by
  rw [ENNReal.toReal]; rw [NNReal.coe_eq_one]; rw [ENNReal.toNNReal_eq_one_iff]

/--
theorem `toNNReal_ne_one` / 定理 `toNNReal_ne_one`

English:
theorem toNNReal_ne_one
  statement: a.toNNReal != 1 ↔ a != 1
  proof: a.toNNReal_eq_one_iff.not

中文:
定理 toNN实数_ne_one
  结论: a.toNN实数 != 1 ↔ a != 1
  证明: a.toNNReal_eq_one_iff.not

Depends on / 依赖: a.toNNReal_eq_one_iff.not, toNNReal_eq_one_iff
-/
theorem toNNReal_ne_one : a.toNNReal != 1 ↔ a != 1 :=
  a.toNNReal_eq_one_iff.not

/--
theorem `toReal_ne_one` / 定理 `toReal_ne_one`

English:
theorem toReal_ne_one
  statement: a.toReal != 1 ↔ a != 1
  proof: a.toReal_eq_one_iff.not

@[simp, aesop (rule_sets := [finiteness]) safe apply]

中文:
定理 to实数_ne_one
  结论: a.to实数 != 1 ↔ a != 1
  证明: a.toReal_eq_one_iff.not

@[simp, aesop (rule_sets := [finiteness]) safe apply]

Depends on / 依赖: a.toReal_eq_one_iff.not, toReal_eq_one_iff
-/
theorem toReal_ne_one : a.toReal != 1 ↔ a != 1 :=
  a.toReal_eq_one_iff.not

@[simp, aesop (rule_sets := [finiteness]) safe apply]
/--
theorem `coe_ne_top` / 定理 `coe_ne_top`

English:
theorem coe_ne_top
  statement: (r : Real>=0∞) != ∞
  proof: WithTop.coe_ne_top

中文:
定理 coe_ne_top
  结论: (r : 实数>=0∞) != ∞
  证明: WithTop.coe_ne_top

Depends on / 依赖: WithTop, WithTop.coe_ne_top, coe_ne_top
-/
theorem coe_ne_top : (r : Real>=0∞) != ∞ := WithTop.coe_ne_top

/--
theorem `top_ne_coe` / 定理 `top_ne_coe`

English:
theorem top_ne_coe
  statement: ∞ != (r : Real>=0∞)
  proof: WithTop.top_ne_coe

中文:
定理 top_ne_coe
  结论: ∞ != (r : 实数>=0∞)
  证明: WithTop.top_ne_coe
-/
@[simp] theorem top_ne_coe : ∞ != (r : Real>=0∞) := WithTop.top_ne_coe

/--
theorem `coe_lt_top` / 定理 `coe_lt_top`

English:
theorem coe_lt_top
  statement: (r : Real>=0∞) < ∞
  proof: WithTop.coe_lt_top r

@[simp, aesop (rule_sets := [finiteness]) safe apply]

中文:
定理 coe_lt_top
  结论: (r : 实数>=0∞) < ∞
  证明: WithTop.coe_lt_top r

@[simp, aesop (rule_sets := [finiteness]) safe apply]
-/
@[simp] theorem coe_lt_top : (r : Real>=0∞) < ∞ := WithTop.coe_lt_top r

@[simp, aesop (rule_sets := [finiteness]) safe apply]
/--
theorem `ofReal_ne_top` / 定理 `ofReal_ne_top`

English:
theorem ofReal_ne_top
  given: {r : Real}
  statement: ENNReal.ofReal r != ∞
  proof: coe_ne_top

中文:
定理 of实数_ne_top
  条件: {r : 实数}
  结论: 广义非负实数.of实数 r != ∞
  证明: coe_ne_top

Depends on / 依赖: coe_ne_top
-/
theorem ofReal_ne_top {r : Real} : ENNReal.ofReal r != ∞ := coe_ne_top

/--
theorem `ofReal_lt_top` / 定理 `ofReal_lt_top`

English:
theorem ofReal_lt_top
  given: {r : Real}
  statement: ENNReal.ofReal r < ∞
  proof: coe_lt_top

中文:
定理 of实数_lt_top
  条件: {r : 实数}
  结论: 广义非负实数.of实数 r < ∞
  证明: coe_lt_top
-/
@[simp] theorem ofReal_lt_top {r : Real} : ENNReal.ofReal r < ∞ := coe_lt_top

/--
theorem `top_ne_ofReal` / 定理 `top_ne_ofReal`

English:
theorem top_ne_ofReal
  given: {r : Real}
  statement: ∞ != ENNReal.ofReal r
  proof: top_ne_coe

@[simp]

中文:
定理 top_ne_of实数
  条件: {r : 实数}
  结论: ∞ != 广义非负实数.of实数 r
  证明: top_ne_coe

@[simp]
-/
@[simp] theorem top_ne_ofReal {r : Real} : ∞ != ENNReal.ofReal r := top_ne_coe

@[simp]
/--
theorem `ofReal_toReal_eq_iff` / 定理 `ofReal_toReal_eq_iff`

English:
theorem ofReal_toReal_eq_iff
  statement: ENNReal.ofReal a.toReal = a ↔ a != ⊤
  proof: ⟨fun h => by
    rw [← h]
    exact ofReal_ne_top, ofReal_toReal⟩

@[simp]

中文:
定理 of实数_to实数_eq_iff
  结论: 广义非负实数.of实数 a.to实数 = a ↔ a != ⊤
  证明: ⟨fun h => by
    rw [← h]
    exact ofReal_ne_top, ofReal_toReal⟩

@[simp]

Depends on / 依赖: ofReal_ne_top, ofReal_toReal
-/
theorem ofReal_toReal_eq_iff : ENNReal.ofReal a.toReal = a ↔ a != ⊤ :=
  ⟨fun h => by
    rw [← h]
    exact ofReal_ne_top, ofReal_toReal⟩

@[simp]
/--
theorem `toReal_ofReal_eq_iff` / 定理 `toReal_ofReal_eq_iff`

English:
theorem toReal_ofReal_eq_iff
  given: {a : Real}
  statement: (ENNReal.ofReal a).toReal = a ↔ 0 <= a
  proof: ⟨fun h => by
    rw [← h]
    exact toReal_nonneg, toReal_ofReal⟩

@[simp, aesop (rule_sets := [finiteness]) safe apply] theorem zero_ne_top : 0 != ∞ := coe_ne_top

中文:
定理 to实数_of实数_eq_iff
  条件: {a : 实数}
  结论: (广义非负实数.of实数 a).to实数 = a ↔ 0 <= a
  证明: ⟨fun h => by
    rw [← h]
    exact toReal_nonneg, toReal_ofReal⟩

@[simp, aesop (rule_sets := [finiteness]) safe apply] theorem zero_ne_top : 0 != ∞ := coe_ne_top

Depends on / 依赖: toReal_nonneg, toReal_ofReal
-/
theorem toReal_ofReal_eq_iff {a : Real} : (ENNReal.ofReal a).toReal = a ↔ 0 <= a :=
  ⟨fun h => by
    rw [← h]
    exact toReal_nonneg, toReal_ofReal⟩

@[simp, aesop (rule_sets := [finiteness]) safe apply] theorem zero_ne_top : 0 != ∞ := coe_ne_top

/--
theorem `top_ne_zero` / 定理 `top_ne_zero`

English:
theorem top_ne_zero
  statement: ∞ != 0
  proof: top_ne_coe

@[simp, aesop (rule_sets := [finiteness]) safe apply] theorem one_ne_top : 1 != ∞ := coe_ne_top

中文:
定理 top_ne_zero
  结论: ∞ != 0
  证明: top_ne_coe

@[simp, aesop (rule_sets := [finiteness]) safe apply] theorem one_ne_top : 1 != ∞ := coe_ne_top
-/
@[simp] theorem top_ne_zero : ∞ != 0 := top_ne_coe

@[simp, aesop (rule_sets := [finiteness]) safe apply] theorem one_ne_top : 1 != ∞ := coe_ne_top

/--
theorem `top_ne_one` / 定理 `top_ne_one`

English:
theorem top_ne_one
  statement: ∞ != 1
  proof: top_ne_coe

中文:
定理 top_ne_one
  结论: ∞ != 1
  证明: top_ne_coe
-/
@[simp] theorem top_ne_one : ∞ != 1 := top_ne_coe

/--
theorem `zero_lt_top` / 定理 `zero_lt_top`

English:
theorem zero_lt_top
  statement: 0 < ∞
  proof: coe_lt_top

中文:
定理 zero_lt_top
  结论: 0 < ∞
  证明: coe_lt_top
-/
@[simp] theorem zero_lt_top : 0 < ∞ := coe_lt_top

/--
theorem `coe_le_coe` / 定理 `coe_le_coe`

English:
theorem coe_le_coe
  statement: (↑r : Real>=0∞) <= ↑q ↔ r <= q
  proof: WithTop.coe_le_coe

中文:
定理 coe_le_coe
  结论: (↑r : 实数>=0∞) <= ↑q ↔ r <= q
  证明: WithTop.coe_le_coe
-/
@[simp, norm_cast, gcongr] theorem coe_le_coe : (↑r : Real>=0∞) <= ↑q ↔ r <= q := WithTop.coe_le_coe

/--
theorem `coe_lt_coe` / 定理 `coe_lt_coe`

English:
theorem coe_lt_coe
  statement: (↑r : Real>=0∞) < ↑q ↔ r < q
  proof: WithTop.coe_lt_coe

@[deprecated (since := "2026-08-04")] alias ⟨_, coe_le_coe_of_le⟩ := coe_le_coe

@[deprecated (since := "2026-08-04")] alias ⟨_, coe_lt_coe_of_lt⟩ := coe_lt_coe

中文:
定理 coe_lt_coe
  结论: (↑r : 实数>=0∞) < ↑q ↔ r < q
  证明: WithTop.coe_lt_coe

@[deprecated (since := "2026-08-04")] alias ⟨_, coe_le_coe_of_le⟩ := coe_le_coe

@[deprecated (since := "2026-08-04")] alias ⟨_, coe_lt_coe_of_lt⟩ := coe_lt_coe
-/
@[simp, norm_cast, gcongr] theorem coe_lt_coe : (↑r : Real>=0∞) < ↑q ↔ r < q := WithTop.coe_lt_coe

@[deprecated (since := "2026-08-04")] alias ⟨_, coe_le_coe_of_le⟩ := coe_le_coe

@[deprecated (since := "2026-08-04")] alias ⟨_, coe_lt_coe_of_lt⟩ := coe_lt_coe

/--
theorem `coe_mono` / 定理 `coe_mono`

English:
theorem coe_mono
  statement: Monotone ofNNReal
  proof: fun _ _ => coe_le_coe.2

中文:
定理 coe_mono
  结论: 递增 ofNN实数
  证明: fun _ _ => coe_le_coe.2

Depends on / 依赖: coe_le_coe
-/
theorem coe_mono : Monotone ofNNReal := fun _ _ => coe_le_coe.2

/--
theorem `coe_strictMono` / 定理 `coe_strictMono`

English:
theorem coe_strictMono
  statement: StrictMono ofNNReal
  proof: fun _ _ => coe_lt_coe.2

中文:
定理 coe_strictMono
  结论: 严格递增 ofNN实数
  证明: fun _ _ => coe_lt_coe.2

Depends on / 依赖: coe_lt_coe
-/
theorem coe_strictMono : StrictMono ofNNReal := fun _ _ => coe_lt_coe.2

/--
theorem `coe_eq_zero` / 定理 `coe_eq_zero`

English:
theorem coe_eq_zero
  statement: (↑r : Real>=0∞) = 0 ↔ r = 0
  proof: coe_inj

中文:
定理 coe_eq_zero
  结论: (↑r : 实数>=0∞) = 0 ↔ r = 0
  证明: coe_inj
-/
@[simp, norm_cast] theorem coe_eq_zero : (↑r : Real>=0∞) = 0 ↔ r = 0 := coe_inj

/--
theorem `zero_eq_coe` / 定理 `zero_eq_coe`

English:
theorem zero_eq_coe
  statement: 0 = (↑r : Real>=0∞) ↔ 0 = r
  proof: coe_inj

中文:
定理 zero_eq_coe
  结论: 0 = (↑r : 实数>=0∞) ↔ 0 = r
  证明: coe_inj
-/
@[simp, norm_cast] theorem zero_eq_coe : 0 = (↑r : Real>=0∞) ↔ 0 = r := coe_inj

/--
theorem `coe_eq_one` / 定理 `coe_eq_one`

English:
theorem coe_eq_one
  statement: (↑r : Real>=0∞) = 1 ↔ r = 1
  proof: coe_inj

中文:
定理 coe_eq_one
  结论: (↑r : 实数>=0∞) = 1 ↔ r = 1
  证明: coe_inj
-/
@[simp, norm_cast] theorem coe_eq_one : (↑r : Real>=0∞) = 1 ↔ r = 1 := coe_inj

/--
theorem `one_eq_coe` / 定理 `one_eq_coe`

English:
theorem one_eq_coe
  statement: 1 = (↑r : Real>=0∞) ↔ 1 = r
  proof: coe_inj

中文:
定理 one_eq_coe
  结论: 1 = (↑r : 实数>=0∞) ↔ 1 = r
  证明: coe_inj
-/
@[simp, norm_cast] theorem one_eq_coe : 1 = (↑r : Real>=0∞) ↔ 1 = r := coe_inj

/--
theorem `coe_pos` / 定理 `coe_pos`

English:
theorem coe_pos
  statement: 0 < (r : Real>=0∞) ↔ 0 < r
  proof: coe_lt_coe

中文:
定理 coe_pos
  结论: 0 < (r : 实数>=0∞) ↔ 0 < r
  证明: coe_lt_coe
-/
@[simp, norm_cast] theorem coe_pos : 0 < (r : Real>=0∞) ↔ 0 < r := coe_lt_coe

/--
theorem `coe_ne_zero` / 定理 `coe_ne_zero`

English:
theorem coe_ne_zero
  statement: (r : Real>=0∞) != 0 ↔ r != 0
  proof: WithTop.coe_ne_zero

中文:
定理 coe_ne_zero
  结论: (r : 实数>=0∞) != 0 ↔ r != 0
  证明: WithTop.coe_ne_zero

Depends on / 依赖: WithTop, WithTop.coe_ne_zero, coe_ne_zero
-/
theorem coe_ne_zero : (r : Real>=0∞) != 0 ↔ r != 0 := WithTop.coe_ne_zero

/--
lemma `coe_ne_one` / 引理 `coe_ne_one`

English:
lemma coe_ne_one
  statement: (r : Real>=0∞) != 1 ↔ r != 1
  proof: WithTop.coe_ne_one

中文:
引理 coe_ne_one
  结论: (r : 实数>=0∞) != 1 ↔ r != 1
  证明: WithTop.coe_ne_one

Depends on / 依赖: WithTop, WithTop.coe_ne_one, coe_ne_one
-/
lemma coe_ne_one : (r : Real>=0∞) != 1 ↔ r != 1 := WithTop.coe_ne_one

/--
lemma `coe_add` / 引理 `coe_add`

English:
lemma coe_add
  given: (x y : Real>=0)
  statement: (↑(x + y) : Real>=0∞) = x + y
  proof: rfl

中文:
引理 coe_add
  条件: (x y : 实数>=0)
  结论: (↑(x + y) : 实数>=0∞) = x + y
  证明: rfl
-/
@[simp, norm_cast] lemma coe_add (x y : Real>=0) : (↑(x + y) : Real>=0∞) = x + y := rfl

/--
lemma `coe_mul` / 引理 `coe_mul`

English:
lemma coe_mul
  given: (x y : Real>=0)
  statement: (↑(x * y) : Real>=0∞) = x * y
  proof: rfl

中文:
引理 coe_mul
  条件: (x y : 实数>=0)
  结论: (↑(x * y) : 实数>=0∞) = x * y
  证明: rfl
-/
@[simp, norm_cast] lemma coe_mul (x y : Real>=0) : (↑(x * y) : Real>=0∞) = x * y := rfl

/--
lemma `coe_nsmul` / 引理 `coe_nsmul`

English:
lemma coe_nsmul
  given: (n : Nat) (x : Real>=0)
  statement: (↑(n • x) : Real>=0∞) = n • x
  proof: rfl

中文:
引理 coe_nsmul
  条件: (n : 自然数) (x : 实数>=0)
  结论: (↑(n • x) : 实数>=0∞) = n • x
  证明: rfl
-/
@[norm_cast] lemma coe_nsmul (n : Nat) (x : Real>=0) : (↑(n • x) : Real>=0∞) = n • x := rfl

/--
lemma `coe_pow` / 引理 `coe_pow`

English:
lemma coe_pow
  given: (x : Real>=0) (n : Nat)
  statement: (↑(x ^ n) : Real>=0∞) = x ^ n
  proof: rfl

@[simp, norm_cast]

中文:
引理 coe_pow
  条件: (x : 实数>=0) (n : 自然数)
  结论: (↑(x ^ n) : 实数>=0∞) = x ^ n
  证明: rfl

@[simp, norm_cast]
-/
@[simp, norm_cast] lemma coe_pow (x : Real>=0) (n : Nat) : (↑(x ^ n) : Real>=0∞) = x ^ n := rfl

@[simp, norm_cast]
/--
theorem `coe_ofNat` / 定理 `coe_ofNat`

English:
theorem coe_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: ((ofNat(n) : Real>=0) : Real>=0∞) = ofNat(n)
  proof: rfl

中文:
定理 coe_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: ((of自然数(n) : 实数>=0) : 实数>=0∞) = of自然数(n)
  证明: rfl
-/
theorem coe_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Real>=0) : Real>=0∞) = ofNat(n) := rfl

-- TODO: add lemmas about `OfNat.ofNat` and `<`/`≤`

/--
theorem `coe_two` / 定理 `coe_two`

English:
theorem coe_two
  statement: ((2 : Real>=0) : Real>=0∞) = 2
  proof: rfl

中文:
定理 coe_two
  结论: ((2 : 实数>=0) : 实数>=0∞) = 2
  证明: rfl
-/
theorem coe_two : ((2 : Real>=0) : Real>=0∞) = 2 := rfl

/--
theorem `toNNReal_eq_toNNReal_iff` / 定理 `toNNReal_eq_toNNReal_iff`

English:
theorem toNNReal_eq_toNNReal_iff
  given: (x y : Real>=0∞)
  proof: WithTop.untopD_eq_untopD_iff

中文:
定理 toNN实数_eq_toNN实数_iff
  条件: (x y : 实数>=0∞)
  证明: WithTop.untopD_eq_untopD_iff

Depends on / 依赖: WithTop, WithTop.untopD_eq_untopD_iff, untopD_eq_untopD_iff
-/
theorem toNNReal_eq_toNNReal_iff (x y : Real>=0∞) :
    x.toNNReal = y.toNNReal ↔ x = y ∨ x = 0 ∧ y = ⊤ ∨ x = ⊤ ∧ y = 0 :=
  WithTop.untopD_eq_untopD_iff

/--
theorem `toReal_eq_toReal_iff` / 定理 `toReal_eq_toReal_iff`

English:
theorem toReal_eq_toReal_iff
  given: (x y : Real>=0∞)
  proof: by
  simp only [ENNReal.toReal, NNReal.coe_inj, toNNReal_eq_toNNReal_iff]

中文:
定理 to实数_eq_to实数_iff
  条件: (x y : 实数>=0∞)
  证明: by
  simp only [ENNReal.toReal, NNReal.coe_inj, toNNReal_eq_toNNReal_iff]

Depends on / 依赖: ENNReal, ENNReal.toReal, NNReal, NNReal.coe_inj, coe_inj, toNNReal_eq_toNNReal_iff, toReal
-/
theorem toReal_eq_toReal_iff (x y : Real>=0∞) :
    x.toReal = y.toReal ↔ x = y ∨ x = 0 ∧ y = ⊤ ∨ x = ⊤ ∧ y = 0 := by
  simp only [ENNReal.toReal, NNReal.coe_inj, toNNReal_eq_toNNReal_iff]

/--
theorem `toNNReal_eq_toNNReal_iff'` / 定理 `toNNReal_eq_toNNReal_iff'`

English:
theorem toNNReal_eq_toNNReal_iff'
  given: {x y : Real>=0∞} (hx : x != ⊤) (hy : y != ⊤)
  proof: by
  simp only [ENNReal.toNNReal_eq_toNNReal_iff x y, hx, hy, and_false, false_and, or_false]

中文:
定理 toNN实数_eq_toNN实数_iff'
  条件: {x y : 实数>=0∞} (hx : x != ⊤) (hy : y != ⊤)
  证明: by
  simp only [ENNReal.toNNReal_eq_toNNReal_iff x y, hx, hy, and_false, false_and, or_false]

Depends on / 依赖: ENNReal, ENNReal.toNNReal_eq_toNNReal_iff, and_false, false_and, or_false, toNNReal_eq_toNNReal_iff
-/
theorem toNNReal_eq_toNNReal_iff' {x y : Real>=0∞} (hx : x != ⊤) (hy : y != ⊤) :
    x.toNNReal = y.toNNReal ↔ x = y := by
  simp only [ENNReal.toNNReal_eq_toNNReal_iff x y, hx, hy, and_false, false_and, or_false]

/--
theorem `toReal_eq_toReal_iff'` / 定理 `toReal_eq_toReal_iff'`

English:
theorem toReal_eq_toReal_iff'
  given: {x y : Real>=0∞} (hx : x != ⊤) (hy : y != ⊤)
  proof: by
  simp only [ENNReal.toReal, NNReal.coe_inj, toNNReal_eq_toNNReal_iff' hx hy]

中文:
定理 to实数_eq_to实数_iff'
  条件: {x y : 实数>=0∞} (hx : x != ⊤) (hy : y != ⊤)
  证明: by
  simp only [ENNReal.toReal, NNReal.coe_inj, toNNReal_eq_toNNReal_iff' hx hy]

Depends on / 依赖: ENNReal, ENNReal.toReal, NNReal, NNReal.coe_inj, coe_inj, toNNReal_eq_toNNReal_iff, toReal
-/
theorem toReal_eq_toReal_iff' {x y : Real>=0∞} (hx : x != ⊤) (hy : y != ⊤) :
    x.toReal = y.toReal ↔ x = y := by
  simp only [ENNReal.toReal, NNReal.coe_inj, toNNReal_eq_toNNReal_iff' hx hy]

/--
theorem `one_lt_two` / 定理 `one_lt_two`

English:
theorem one_lt_two
  statement: (1 : Real>=0∞) < 2
  proof: Nat.one_lt_ofNat

中文:
定理 one_lt_two
  结论: (1 : 实数>=0∞) < 2
  证明: Nat.one_lt_ofNat

Depends on / 依赖: Nat.one_lt_ofNat, one_lt_ofNat
-/
theorem one_lt_two : (1 : Real>=0∞) < 2 := Nat.one_lt_ofNat

/--
Instance `_root_.fact_one_le_one_ennreal` / 实例 `_root_.fact_one_le_one_ennreal`

English:
instance _root_.fact_one_le_one_ennreal
  signature: : Fact ((1 : Real>=0∞) <= 1)
  body: ⟨le_rfl⟩

中文:
实例 _root_.fact_one_le_one_ennreal
  签名: : Fact ((1 : 实数>=0∞) <= 1)
  定义体: ⟨le_rfl⟩

Depends on / 依赖: le_rfl
-/
instance _root_.fact_one_le_one_ennreal : Fact ((1 : Real>=0∞) <= 1) :=
  ⟨le_rfl⟩

/--
Instance `_root_.fact_one_le_two_ennreal` / 实例 `_root_.fact_one_le_two_ennreal`

English:
instance _root_.fact_one_le_two_ennreal
  signature: : Fact ((1 : Real>=0∞) <= 2)
  body: ⟨one_le_two⟩

中文:
实例 _root_.fact_one_le_two_ennreal
  签名: : Fact ((1 : 实数>=0∞) <= 2)
  定义体: ⟨one_le_two⟩

Depends on / 依赖: one_le_two
-/
instance _root_.fact_one_le_two_ennreal : Fact ((1 : Real>=0∞) <= 2) :=
  ⟨one_le_two⟩

/--
Instance `_root_.fact_one_le_top_ennreal` / 实例 `_root_.fact_one_le_top_ennreal`

English:
instance _root_.fact_one_le_top_ennreal
  signature: : Fact ((1 : Real>=0∞) <= ∞)
  body: ⟨le_top⟩

中文:
实例 _root_.fact_one_le_top_ennreal
  签名: : Fact ((1 : 实数>=0∞) <= ∞)
  定义体: ⟨le_top⟩

Depends on / 依赖: le_top
-/
instance _root_.fact_one_le_top_ennreal : Fact ((1 : Real>=0∞) <= ∞) :=
  ⟨le_top⟩

/--
Definition of `neTopEquivNNReal` / `neTopEquivNNReal` 的定义

English:
definition neTopEquivNNReal
  signature: : { a | a != ∞ } ≃ Real>=0 where
  body: ENNReal.toNNReal x
  invFun x := ⟨x, coe_ne_top⟩
left_inv := fun x => Subtype.ext coe_toNNReal x.2
  right_inv := toNNReal_coe

中文:
定义 neTopEquivNN实数
  签名: : { a | a != ∞ } ≃ 实数>=0 where
  定义体: ENNReal.toNNReal x
  invFun x := ⟨x, coe_ne_top⟩
left_inv := fun x => Subtype.ext coe_toNNReal x.2
  right_inv := toNNReal_coe

Depends on / 依赖: ENNReal, ENNReal.toNNReal, toNNReal
-/
def neTopEquivNNReal : { a | a != ∞ } ≃ Real>=0 where
  toFun x := ENNReal.toNNReal x
  invFun x := ⟨x, coe_ne_top⟩
left_inv := fun x => Subtype.ext coe_toNNReal x.2
  right_inv := toNNReal_coe

/--
theorem `cinfi_ne_top` / 定理 `cinfi_ne_top`

English:
theorem cinfi_ne_top
  given: [InfSet α] (f : Real>=0∞ -> α)
  statement: ⨅ x : { x // x != ∞ }, f x = ⨅ x : Real>=0, f x
  proof: Eq.symm neTopEquivNNReal.symm.surjective.iInf_congr _ fun _ => rfl

中文:
定理 cinfi_ne_top
  条件: [下确界集 α] (f : 实数>=0∞ -> α)
  结论: ⨅ x : { x // x != ∞ }, f x = ⨅ x : 实数>=0, f x
  证明: Eq.symm neTopEquivNNReal.symm.surjective.iInf_congr _ fun _ => rfl

Depends on / 依赖: Eq.symm, iInf_congr, neTopEquivNNReal, neTopEquivNNReal.symm.surjective.iInf_congr, surjective
-/
theorem cinfi_ne_top [InfSet α] (f : Real>=0∞ -> α) : ⨅ x : { x // x != ∞ }, f x = ⨅ x : Real>=0, f x :=
Eq.symm neTopEquivNNReal.symm.surjective.iInf_congr _ fun _ => rfl

/--
theorem `iInf_ne_top` / 定理 `iInf_ne_top`

English:
theorem iInf_ne_top
  given: [CompleteLattice α] (f : Real>=0∞ -> α)
  proof: by rw [iInf_subtype', cinfi_ne_top]

中文:
定理 iInf_ne_top
  条件: [完备格 α] (f : 实数>=0∞ -> α)
  证明: by rw [iInf_subtype', cinfi_ne_top]

Depends on / 依赖: cinfi_ne_top, iInf_subtype
-/
theorem iInf_ne_top [CompleteLattice α] (f : Real>=0∞ -> α) :
    ⨅ (x) (_ : x != ∞), f x = ⨅ x : Real>=0, f x := by rw [iInf_subtype', cinfi_ne_top]

/--
theorem `csupr_ne_top` / 定理 `csupr_ne_top`

English:
theorem csupr_ne_top
  given: [SupSet α] (f : Real>=0∞ -> α)
  statement: ⨆ x : { x // x != ∞ }, f x = ⨆ x : Real>=0, f x
  proof: @cinfi_ne_top αᵒᵈ _ _

中文:
定理 csupr_ne_top
  条件: [上确界集 α] (f : 实数>=0∞ -> α)
  结论: ⨆ x : { x // x != ∞ }, f x = ⨆ x : 实数>=0, f x
  证明: @cinfi_ne_top αᵒᵈ _ _

Depends on / 依赖: cinfi_ne_top
-/
theorem csupr_ne_top [SupSet α] (f : Real>=0∞ -> α) : ⨆ x : { x // x != ∞ }, f x = ⨆ x : Real>=0, f x :=
  @cinfi_ne_top αᵒᵈ _ _

/--
theorem `iSup_ne_top` / 定理 `iSup_ne_top`

English:
theorem iSup_ne_top
  given: [CompleteLattice α] (f : Real>=0∞ -> α)
  proof: @iInf_ne_top αᵒᵈ _ _

中文:
定理 iSup_ne_top
  条件: [完备格 α] (f : 实数>=0∞ -> α)
  证明: @iInf_ne_top αᵒᵈ _ _

Depends on / 依赖: iInf_ne_top
-/
theorem iSup_ne_top [CompleteLattice α] (f : Real>=0∞ -> α) :
    ⨆ (x) (_ : x != ∞), f x = ⨆ x : Real>=0, f x :=
  @iInf_ne_top αᵒᵈ _ _

/--
theorem `iInf_ennreal` / 定理 `iInf_ennreal`

English:
theorem iInf_ennreal
  given: {α : Type*} [CompleteLattice α] {f : Real>=0∞ -> α}
  proof: (iInf_option f).trans (inf_comm _ _)

中文:
定理 iInf_ennreal
  条件: {α : 类型} [完备格 α] {f : 实数>=0∞ -> α}
  证明: (iInf_option f).trans (inf_comm _ _)

Depends on / 依赖: iInf_option, inf_comm
-/
theorem iInf_ennreal {α : Type*} [CompleteLattice α] {f : Real>=0∞ -> α} :
    ⨅ n, f n = (⨅ n : Real>=0, f n) ⊓ f ∞ :=
  (iInf_option f).trans (inf_comm _ _)

/--
theorem `iSup_ennreal` / 定理 `iSup_ennreal`

English:
theorem iSup_ennreal
  given: {α : Type*} [CompleteLattice α] {f : Real>=0∞ -> α}
  proof: @iInf_ennreal αᵒᵈ _ _

中文:
定理 iSup_ennreal
  条件: {α : 类型} [完备格 α] {f : 实数>=0∞ -> α}
  证明: @iInf_ennreal αᵒᵈ _ _

Depends on / 依赖: iInf_ennreal
-/
theorem iSup_ennreal {α : Type*} [CompleteLattice α] {f : Real>=0∞ -> α} :
    ⨆ n, f n = (⨆ n : Real>=0, f n) ⊔ f ∞ :=
  @iInf_ennreal αᵒᵈ _ _

/--
Definition of `ofNNRealHom` / `ofNNRealHom` 的定义

English:
definition ofNNRealHom
  signature: : Real>=0 ->+* Real>=0∞ where
  body: WithTop.some
  map_one' := coe_one
  map_mul' _ _ := coe_mul _ _
  map_zero' := coe_zero
  map_add' _ _ := coe_add _ _

中文:
定义 ofNN实数Hom
  签名: : 实数>=0 ->+* 实数>=0∞ where
  定义体: WithTop.some
  map_one' := coe_one
  map_mul' _ _ := coe_mul _ _
  map_zero' := coe_zero
  map_add' _ _ := coe_add _ _

Depends on / 依赖: WithTop, WithTop.some
-/
noncomputable def ofNNRealHom : Real>=0 ->+* Real>=0∞ where
  toFun := WithTop.some
  map_one' := coe_one
  map_mul' _ _ := coe_mul _ _
  map_zero' := coe_zero
  map_add' _ _ := coe_add _ _

/--
theorem `coe_ofNNRealHom` / 定理 `coe_ofNNRealHom`

English:
theorem coe_ofNNRealHom
  statement: ⇑ofNNRealHom = WithTop.some
  proof: rfl

中文:
定理 coe_ofNN实数Hom
  结论: ⇑ofNN实数Hom = WithTop.some
  证明: rfl

Depends on / 依赖: toArray
-/
@[simp] theorem coe_ofNNRealHom : ⇑ofNNRealHom = WithTop.some := rfl

section Order

/--
theorem `bot_eq_zero` / 定理 `bot_eq_zero`

English:
theorem bot_eq_zero
  statement: (⊥ : Real>=0∞) = 0
  proof: rfl

中文:
定理 bot_eq_zero
  结论: (⊥ : 实数>=0∞) = 0
  证明: rfl

Depends on / 依赖: Array.toList, Aux_eq_array_foldl, List.foldr_hom, foldr_hom, intros, sublists, toList
-/
theorem bot_eq_zero : (⊥ : Real>=0∞) = 0 := rfl

-- `coe_lt_top` moved up

/--
theorem `not_top_le_coe` / 定理 `not_top_le_coe`

English:
theorem not_top_le_coe
  statement: ¬∞ <= ↑r
  proof: WithTop.not_top_le_coe r

@[simp, norm_cast]

中文:
定理 not_top_le_coe
  结论: ¬∞ <= ↑r
  证明: WithTop.not_top_le_coe r

@[simp, norm_cast]

Depends on / 依赖: List.reverseRecOn, WithTop, WithTop.not_top_le_coe, append_assoc, foldl_append, map_append, map_singleton, not_top_le_coe, reverseRecOn, sublists
-/
theorem not_top_le_coe : ¬∞ <= ↑r := WithTop.not_top_le_coe r

@[simp, norm_cast]
/--
theorem `one_le_coe_iff` / 定理 `one_le_coe_iff`

English:
theorem one_le_coe_iff
  statement: (1 : Real>=0∞) <= ↑r ↔ 1 <= r
  proof: coe_le_coe

@[simp, norm_cast]

中文:
定理 one_le_coe_iff
  结论: (1 : 实数>=0∞) <= ↑r ↔ 1 <= r
  证明: coe_le_coe

@[simp, norm_cast]

Depends on / 依赖: Aux_eq_map, _eq_sublists, coe_le_coe, foldr_cons, sublists
-/
theorem one_le_coe_iff : (1 : Real>=0∞) <= ↑r ↔ 1 <= r := coe_le_coe

@[simp, norm_cast]
/--
theorem `coe_le_one_iff` / 定理 `coe_le_one_iff`

English:
theorem coe_le_one_iff
  statement: ↑r <= (1 : Real>=0∞) ↔ r <= 1
  proof: coe_le_coe

@[simp, norm_cast]

中文:
定理 coe_le_one_iff
  结论: ↑r <= (1 : 实数>=0∞) ↔ r <= 1
  证明: coe_le_coe

@[simp, norm_cast]

Depends on / 依赖: coe_le_coe
-/
theorem coe_le_one_iff : ↑r <= (1 : Real>=0∞) ↔ r <= 1 := coe_le_coe

@[simp, norm_cast]
/--
theorem `coe_lt_one_iff` / 定理 `coe_lt_one_iff`

English:
theorem coe_lt_one_iff
  statement: (↑p : Real>=0∞) < 1 ↔ p < 1
  proof: coe_lt_coe

@[simp, norm_cast]

中文:
定理 coe_lt_one_iff
  结论: (↑p : 实数>=0∞) < 1 ↔ p < 1
  证明: coe_lt_coe

@[simp, norm_cast]

Depends on / 依赖: coe_lt_coe
-/
theorem coe_lt_one_iff : (↑p : Real>=0∞) < 1 ↔ p < 1 := coe_lt_coe

@[simp, norm_cast]
/--
theorem `one_lt_coe_iff` / 定理 `one_lt_coe_iff`

English:
theorem one_lt_coe_iff
  statement: 1 < (↑p : Real>=0∞) ↔ 1 < p
  proof: coe_lt_coe

@[simp, norm_cast]

中文:
定理 one_lt_coe_iff
  结论: 1 < (↑p : 实数>=0∞) ↔ 1 < p
  证明: coe_lt_coe

@[simp, norm_cast]

Depends on / 依赖: coe_lt_coe
-/
theorem one_lt_coe_iff : 1 < (↑p : Real>=0∞) ↔ 1 < p := coe_lt_coe

@[simp, norm_cast]
/--
theorem `coe_natCast` / 定理 `coe_natCast`

English:
theorem coe_natCast
  given: (n : Nat)
  statement: ((n : Real>=0) : Real>=0∞) = n
  proof: rfl

中文:
定理 coe_natCast
  条件: (n : 自然数)
  结论: ((n : 实数>=0) : 实数>=0∞) = n
  证明: rfl
-/
theorem coe_natCast (n : Nat) : ((n : Real>=0) : Real>=0∞) = n := rfl

/--
lemma `ofReal_natCast` / 引理 `ofReal_natCast`

English:
lemma ofReal_natCast
  given: (n : Nat)
  statement: ENNReal.ofReal n = n
  proof: by simp [ENNReal.ofReal]

中文:
引理 of实数_natCast
  条件: (n : 自然数)
  结论: 广义非负实数.of实数 n = n
  证明: by simp [ENNReal.ofReal]
-/
@[simp, norm_cast] lemma ofReal_natCast (n : Nat) : ENNReal.ofReal n = n := by simp [ENNReal.ofReal]

/--
theorem `ofReal_ofNat` / 定理 `ofReal_ofNat`

English:
theorem ofReal_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: ENNReal.ofReal ofNat(n) = ofNat(n)
  proof: ofReal_natCast n

@[simp, aesop (rule_sets := [finiteness]) safe apply]

中文:
定理 of实数_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: 广义非负实数.of实数 of自然数(n) = of自然数(n)
  证明: ofReal_natCast n

@[simp, aesop (rule_sets := [finiteness]) safe apply]
-/
@[simp] theorem ofReal_ofNat (n : Nat) [n.AtLeastTwo] : ENNReal.ofReal ofNat(n) = ofNat(n) :=
  ofReal_natCast n

@[simp, aesop (rule_sets := [finiteness]) safe apply]
/--
theorem `natCast_ne_top` / 定理 `natCast_ne_top`

English:
theorem natCast_ne_top
  given: (n : Nat)
  statement: (n : Real>=0∞) != ∞
  proof: WithTop.natCast_ne_top n

中文:
定理 natCast_ne_top
  条件: (n : 自然数)
  结论: (n : 实数>=0∞) != ∞
  证明: WithTop.natCast_ne_top n

Depends on / 依赖: WithTop, WithTop.natCast_ne_top, natCast_ne_top
-/
theorem natCast_ne_top (n : Nat) : (n : Real>=0∞) != ∞ := WithTop.natCast_ne_top n

/--
theorem `natCast_lt_top` / 定理 `natCast_lt_top`

English:
theorem natCast_lt_top
  given: (n : Nat)
  statement: (n : Real>=0∞) < ∞
  proof: WithTop.natCast_lt_top n

@[simp, aesop (rule_sets := [finiteness]) safe apply]

中文:
定理 natCast_lt_top
  条件: (n : 自然数)
  结论: (n : 实数>=0∞) < ∞
  证明: WithTop.natCast_lt_top n

@[simp, aesop (rule_sets := [finiteness]) safe apply]
-/
@[simp] theorem natCast_lt_top (n : Nat) : (n : Real>=0∞) < ∞ := WithTop.natCast_lt_top n

@[simp, aesop (rule_sets := [finiteness]) safe apply]
/--
lemma `ofNat_ne_top` / 引理 `ofNat_ne_top`

English:
lemma ofNat_ne_top
  given: {n : Nat} [Nat.AtLeastTwo n]
  statement: ofNat(n) != ∞
  proof: natCast_ne_top n

@[simp]

中文:
引理 of自然数_ne_top
  条件: {n : 自然数} [自然数.AtLeastTwo n]
  结论: of自然数(n) != ∞
  证明: natCast_ne_top n

@[simp]

Depends on / 依赖: natCast_ne_top
-/
lemma ofNat_ne_top {n : Nat} [Nat.AtLeastTwo n] : ofNat(n) != ∞ := natCast_ne_top n

@[simp]
/--
lemma `ofNat_lt_top` / 引理 `ofNat_lt_top`

English:
lemma ofNat_lt_top
  given: {n : Nat} [Nat.AtLeastTwo n]
  statement: ofNat(n) < ∞
  proof: natCast_lt_top n

中文:
引理 of自然数_lt_top
  条件: {n : 自然数} [自然数.AtLeastTwo n]
  结论: of自然数(n) < ∞
  证明: natCast_lt_top n

Depends on / 依赖: natCast_lt_top
-/
lemma ofNat_lt_top {n : Nat} [Nat.AtLeastTwo n] : ofNat(n) < ∞ := natCast_lt_top n

/--
theorem `top_ne_natCast` / 定理 `top_ne_natCast`

English:
theorem top_ne_natCast
  given: (n : Nat)
  statement: ∞ != n
  proof: WithTop.top_ne_natCast n

中文:
定理 top_ne_natCast
  条件: (n : 自然数)
  结论: ∞ != n
  证明: WithTop.top_ne_natCast n
-/
@[simp] theorem top_ne_natCast (n : Nat) : ∞ != n := WithTop.top_ne_natCast n

/--
theorem `top_ne_ofNat` / 定理 `top_ne_ofNat`

English:
theorem top_ne_ofNat
  given: {n : Nat} [n.AtLeastTwo]
  statement: ∞ != ofNat(n)
  proof: ofNat_ne_top.symm

中文:
定理 top_ne_of自然数
  条件: {n : 自然数} [n.AtLeastTwo]
  结论: ∞ != of自然数(n)
  证明: ofNat_ne_top.symm

Depends on / 依赖: Function, Function.comp_def, comp_def, map_id, map_map, reverse_reverse, sublists_eq_sublists
-/
@[simp] theorem top_ne_ofNat {n : Nat} [n.AtLeastTwo] : ∞ != ofNat(n) :=
  ofNat_ne_top.symm

/--
lemma `natCast_le_ofNNReal` / 引理 `natCast_le_ofNNReal`

English:
lemma natCast_le_ofNNReal
  statement: (n : Real>=0∞) <= r ↔ n <= r
  proof: by simp [← coe_le_coe]

中文:
引理 natCast_le_ofNN实数
  结论: (n : 实数>=0∞) <= r ↔ n <= r
  证明: by simp [← coe_le_coe]

Depends on / 依赖: _reverse, reverse_reverse, sublists
-/
@[simp, norm_cast] lemma natCast_le_ofNNReal : (n : Real>=0∞) <= r ↔ n <= r := by simp [← coe_le_coe]
/--
lemma `ofNNReal_le_natCast` / 引理 `ofNNReal_le_natCast`

English:
lemma ofNNReal_le_natCast
  statement: r <= (n : Real>=0∞) ↔ r <= n
  proof: by simp [← coe_le_coe]

中文:
引理 ofNN实数_le_natCast
  结论: r <= (n : 实数>=0∞) ↔ r <= n
  证明: by simp [← coe_le_coe]
-/
@[simp, norm_cast] lemma ofNNReal_le_natCast : r <= (n : Real>=0∞) ↔ r <= n := by simp [← coe_le_coe]

/--
lemma `ofNNReal_add_natCast` / 引理 `ofNNReal_add_natCast`

English:
lemma ofNNReal_add_natCast
  given: (r : Real>=0) (n : Nat)
  statement: ofNNReal (r + n) = r + n
  proof: rfl

中文:
引理 ofNN实数_add_natCast
  条件: (r : 实数>=0) (n : 自然数)
  结论: ofNN实数 (r + n) = r + n
  证明: rfl
-/
@[simp, norm_cast] lemma ofNNReal_add_natCast (r : Real>=0) (n : Nat) : ofNNReal (r + n) = r + n := rfl
/--
lemma `ofNNReal_natCast_add` / 引理 `ofNNReal_natCast_add`

English:
lemma ofNNReal_natCast_add
  given: (n : Nat) (r : Real>=0)
  statement: ofNNReal (n + r) = n + r
  proof: rfl

中文:
引理 ofNN实数_natCast_add
  条件: (n : 自然数) (r : 实数>=0)
  结论: ofNN实数 (n + r) = n + r
  证明: rfl
-/
@[simp, norm_cast] lemma ofNNReal_natCast_add (n : Nat) (r : Real>=0) : ofNNReal (n + r) = n + r := rfl

/--
lemma `ofNNReal_sub_natCast` / 引理 `ofNNReal_sub_natCast`

English:
lemma ofNNReal_sub_natCast
  given: (r : Real>=0) (n : Nat)
  statement: ofNNReal (r - n) = r - n
  proof: rfl

中文:
引理 ofNN实数_sub_natCast
  条件: (r : 实数>=0) (n : 自然数)
  结论: ofNN实数 (r - n) = r - n
  证明: rfl
-/
@[simp, norm_cast] lemma ofNNReal_sub_natCast (r : Real>=0) (n : Nat) : ofNNReal (r - n) = r - n := rfl
/--
lemma `ofNNReal_natCast_sub` / 引理 `ofNNReal_natCast_sub`

English:
lemma ofNNReal_natCast_sub
  given: (n : Nat) (r : Real>=0)
  statement: ofNNReal (n - r) = n - r
  proof: rfl

中文:
引理 ofNN实数_natCast_sub
  条件: (n : 自然数) (r : 实数>=0)
  结论: ofNN实数 (n - r) = n - r
  证明: rfl
-/
@[simp, norm_cast] lemma ofNNReal_natCast_sub (n : Nat) (r : Real>=0) : ofNNReal (n - r) = n - r := rfl

/--
theorem `one_lt_top` / 定理 `one_lt_top`

English:
theorem one_lt_top
  statement: 1 < ∞
  proof: coe_lt_top

@[simp, norm_cast]

中文:
定理 one_lt_top
  结论: 1 < ∞
  证明: coe_lt_top

@[simp, norm_cast]
-/
@[simp] theorem one_lt_top : 1 < ∞ := coe_lt_top

@[simp, norm_cast]
/--
theorem `toNNReal_natCast` / 定理 `toNNReal_natCast`

English:
theorem toNNReal_natCast
  given: (n : Nat)
  statement: (n : Real>=0∞).toNNReal = n
  proof: by
  rw [← ENNReal.coe_natCast n]; rw [ENNReal.toNNReal_coe]

中文:
定理 toNN实数_natCast
  条件: (n : 自然数)
  结论: (n : 实数>=0∞).toNN实数 = n
  证明: by
  rw [← ENNReal.coe_natCast n]; rw [ENNReal.toNNReal_coe]

Depends on / 依赖: ENNReal, ENNReal.coe_natCast, ENNReal.toNNReal_coe, coe_natCast, toNNReal_coe
-/
theorem toNNReal_natCast (n : Nat) : (n : Real>=0∞).toNNReal = n := by
  rw [← ENNReal.coe_natCast n]; rw [ENNReal.toNNReal_coe]

/--
theorem `toNNReal_ofNat` / 定理 `toNNReal_ofNat`

English:
theorem toNNReal_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: ENNReal.toNNReal ofNat(n) = ofNat(n)
  proof: toNNReal_natCast n

@[simp, norm_cast]

中文:
定理 toNN实数_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: 广义非负实数.toNN实数 of自然数(n) = of自然数(n)
  证明: toNNReal_natCast n

@[simp, norm_cast]

Depends on / 依赖: toNNReal_natCast
-/
theorem toNNReal_ofNat (n : Nat) [n.AtLeastTwo] : ENNReal.toNNReal ofNat(n) = ofNat(n) :=
  toNNReal_natCast n

@[simp, norm_cast]
/--
theorem `toReal_natCast` / 定理 `toReal_natCast`

English:
theorem toReal_natCast
  given: (n : Nat)
  statement: (n : Real>=0∞).toReal = n
  proof: by
  rw [← ENNReal.ofReal_natCast n]; rw [ENNReal.toReal_ofReal (Nat.cast_nonneg _)]

中文:
定理 to实数_natCast
  条件: (n : 自然数)
  结论: (n : 实数>=0∞).to实数 = n
  证明: by
  rw [← ENNReal.ofReal_natCast n]; rw [ENNReal.toReal_ofReal (Nat.cast_nonneg _)]

Depends on / 依赖: ENNReal, ENNReal.ofReal_natCast, ENNReal.toReal_ofReal, Nat.cast_nonneg, cast_nonneg, ofReal_natCast, toReal_ofReal
-/
theorem toReal_natCast (n : Nat) : (n : Real>=0∞).toReal = n := by
  rw [← ENNReal.ofReal_natCast n]; rw [ENNReal.toReal_ofReal (Nat.cast_nonneg _)]

/--
theorem `toReal_ofNat` / 定理 `toReal_ofNat`

English:
theorem toReal_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: ENNReal.toReal ofNat(n) = ofNat(n)
  proof: toReal_natCast n

中文:
定理 to实数_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: 广义非负实数.to实数 of自然数(n) = of自然数(n)
  证明: toReal_natCast n
-/
@[simp] theorem toReal_ofNat (n : Nat) [n.AtLeastTwo] : ENNReal.toReal ofNat(n) = ofNat(n) :=
  toReal_natCast n

/--
lemma `toNNReal_natCast_eq_toNNReal` / 引理 `toNNReal_natCast_eq_toNNReal`

English:
lemma toNNReal_natCast_eq_toNNReal
  given: (n : Nat)
  proof: by
  rw [Real.toNNReal_of_nonneg (by positivity)]; rw [ENNReal.toNNReal_natCast]; rw [mk_natCast]

中文:
引理 toNN实数_natCast_eq_toNN实数
  条件: (n : 自然数)
  证明: by
  rw [Real.toNNReal_of_nonneg (by positivity)]; rw [ENNReal.toNNReal_natCast]; rw [mk_natCast]

Depends on / 依赖: ENNReal, ENNReal.toNNReal_natCast, Real.toNNReal_of_nonneg, mk_natCast, toNNReal_natCast, toNNReal_of_nonneg
-/
lemma toNNReal_natCast_eq_toNNReal (n : Nat) :
    (n : Real>=0∞).toNNReal = (n : Real).toNNReal := by
  rw [Real.toNNReal_of_nonneg (by positivity)]; rw [ENNReal.toNNReal_natCast]; rw [mk_natCast]

/--
theorem `le_coe_iff` / 定理 `le_coe_iff`

English:
theorem le_coe_iff
  statement: a <= ↑r ↔ exists p : Real>=0, a = p ∧ p <= r
  proof: WithTop.le_coe_iff

中文:
定理 le_coe_iff
  结论: a <= ↑r ↔ 存在 p : 实数>=0, a = p ∧ p <= r
  证明: WithTop.le_coe_iff

Depends on / 依赖: WithTop, WithTop.le_coe_iff, le_coe_iff
-/
theorem le_coe_iff : a <= ↑r ↔ exists p : Real>=0, a = p ∧ p <= r := WithTop.le_coe_iff

/--
theorem `coe_le_iff` / 定理 `coe_le_iff`

English:
theorem coe_le_iff
  statement: ↑r <= a ↔ forall p : Real>=0, a = p -> r <= p
  proof: WithTop.coe_le_iff

中文:
定理 coe_le_iff
  结论: ↑r <= a ↔ 对任意 p : 实数>=0, a = p -> r <= p
  证明: WithTop.coe_le_iff

Depends on / 依赖: WithTop, WithTop.coe_le_iff, coe_le_iff
-/
theorem coe_le_iff : ↑r <= a ↔ forall p : Real>=0, a = p -> r <= p := WithTop.coe_le_iff

/--
theorem `lt_iff_exists_coe` / 定理 `lt_iff_exists_coe`

English:
theorem lt_iff_exists_coe
  statement: a < b ↔ exists p : Real>=0, a = p ∧ ↑p < b
  proof: WithTop.lt_iff_exists_coe

中文:
定理 lt_iff_存在_coe
  结论: a < b ↔ 存在 p : 实数>=0, a = p ∧ ↑p < b
  证明: WithTop.lt_iff_exists_coe

Depends on / 依赖: WithTop, WithTop.lt_iff_exists_coe, lt_iff_exists_coe
-/
theorem lt_iff_exists_coe : a < b ↔ exists p : Real>=0, a = p ∧ ↑p < b :=
  WithTop.lt_iff_exists_coe

/--
theorem `toReal_le_coe_of_le_coe` / 定理 `toReal_le_coe_of_le_coe`

English:
theorem toReal_le_coe_of_le_coe
  given: {a : Real>=0∞} {b : Real>=0} (h : a <= b)
  statement: a.toReal <= b
  proof: by
  lift a to Real>=0 using ne_top_of_le_ne_top coe_ne_top h
  simpa using h

@[deprecated max_eq_zero (since := "2026-05-07")]

中文:
定理 to实数_le_coe_of_le_coe
  条件: {a : 实数>=0∞} {b : 实数>=0} (h : a <= b)
  结论: a.to实数 <= b
  证明: by
  lift a to Real>=0 using ne_top_of_le_ne_top coe_ne_top h
  simpa using h

@[deprecated max_eq_zero (since := "2026-05-07")]

Depends on / 依赖: coe_ne_top, ne_top_of_le_ne_top
-/
theorem toReal_le_coe_of_le_coe {a : Real>=0∞} {b : Real>=0} (h : a <= b) : a.toReal <= b := by
  lift a to Real>=0 using ne_top_of_le_ne_top coe_ne_top h
  simpa using h

@[deprecated max_eq_zero (since := "2026-05-07")]
/--
theorem `max_eq_zero_iff` / 定理 `max_eq_zero_iff`

English:
theorem max_eq_zero_iff
  statement: max a b = 0 ↔ a = 0 ∧ b = 0
  proof: max_eq_bot

@[deprecated min_eq_zero (since := "2026-05-07")]

中文:
定理 max_eq_zero_iff
  结论: 最大值 a b = 0 ↔ a = 0 ∧ b = 0
  证明: max_eq_bot

@[deprecated min_eq_zero (since := "2026-05-07")]

Depends on / 依赖: max_eq_bot
-/
theorem max_eq_zero_iff : max a b = 0 ↔ a = 0 ∧ b = 0 := max_eq_bot

@[deprecated min_eq_zero (since := "2026-05-07")]
/--
theorem `min_eq_zero_iff` / 定理 `min_eq_zero_iff`

English:
theorem min_eq_zero_iff
  statement: min a b = 0 ↔ a = 0 ∨ b = 0
  proof: min_eq_bot

@[deprecated zero_max (since := "2026-05-07")]

中文:
定理 min_eq_zero_iff
  结论: 最小值 a b = 0 ↔ a = 0 ∨ b = 0
  证明: min_eq_bot

@[deprecated zero_max (since := "2026-05-07")]

Depends on / 依赖: min_eq_bot
-/
theorem min_eq_zero_iff : min a b = 0 ↔ a = 0 ∨ b = 0 := min_eq_bot

@[deprecated zero_max (since := "2026-05-07")]
/--
theorem `max_zero_left` / 定理 `max_zero_left`

English:
theorem max_zero_left
  statement: max 0 a = a
  proof: max_eq_right zero_le

@[deprecated max_zero (since := "2026-05-07")]

中文:
定理 max_zero_left
  结论: 最大值 0 a = a
  证明: max_eq_right zero_le

@[deprecated max_zero (since := "2026-05-07")]

Depends on / 依赖: max_eq_right, zero_le
-/
theorem max_zero_left : max 0 a = a :=
  max_eq_right zero_le

@[deprecated max_zero (since := "2026-05-07")]
/--
theorem `max_zero_right` / 定理 `max_zero_right`

English:
theorem max_zero_right
  statement: max a 0 = a
  proof: max_eq_left zero_le

中文:
定理 max_zero_right
  结论: 最大值 a 0 = a
  证明: max_eq_left zero_le

Depends on / 依赖: max_eq_left, zero_le
-/
theorem max_zero_right : max a 0 = a :=
  max_eq_left zero_le

/--
theorem `lt_iff_exists_rat_btwn` / 定理 `lt_iff_exists_rat_btwn`

English:
theorem lt_iff_exists_rat_btwn
  proof: ⟨fun h => by
    rcases lt_iff_exists_coe.1 h with ⟨p, rfl, _⟩
    rcases exists_between h with ⟨c, pc, cb⟩
    rcases lt_iff_exists_coe.1 cb with ⟨r, rfl, _⟩
    rcases (NNReal.lt_iff_exists_rat_btwn _ _).1 (coe_lt_coe.1 pc) with ⟨q, hq0, pq, qr⟩
    exact ⟨q, hq0, coe_lt_coe.2 pq, lt_trans (coe_lt

中文:
定理 lt_iff_存在_rat_btwn
  证明: ⟨fun h => by
    rcases lt_iff_exists_coe.1 h with ⟨p, rfl, _⟩
    rcases exists_between h with ⟨c, pc, cb⟩
    rcases lt_iff_exists_coe.1 cb with ⟨r, rfl, _⟩
    rcases (NNReal.lt_iff_exists_rat_btwn _ _).1 (coe_lt_coe.1 pc) with ⟨q, hq0, pq, qr⟩
    exact ⟨q, hq0, coe_lt_coe.2 pq, lt_trans (coe_lt

Depends on / 依赖: NNReal, NNReal.lt_iff_exists_rat_btwn, coe_lt_coe, exists_between, lt_iff_exists_coe, lt_iff_exists_rat_btwn, lt_trans
-/
theorem lt_iff_exists_rat_btwn :
    a < b ↔ exists q : Rat, 0 <= q ∧ a < Real.toNNReal q ∧ (Real.toNNReal q : Real>=0∞) < b :=
  ⟨fun h => by
    rcases lt_iff_exists_coe.1 h with ⟨p, rfl, _⟩
    rcases exists_between h with ⟨c, pc, cb⟩
    rcases lt_iff_exists_coe.1 cb with ⟨r, rfl, _⟩
    rcases (NNReal.lt_iff_exists_rat_btwn _ _).1 (coe_lt_coe.1 pc) with ⟨q, hq0, pq, qr⟩
    exact ⟨q, hq0, coe_lt_coe.2 pq, lt_trans (coe_lt_coe.2 qr) cb⟩,
      fun ⟨_, _, qa, qb⟩ => lt_trans qa qb⟩

/--
theorem `lt_iff_exists_real_btwn` / 定理 `lt_iff_exists_real_btwn`

English:
theorem lt_iff_exists_real_btwn
  proof: ⟨fun h =>
    let ⟨q, q0, aq, qb⟩ := ENNReal.lt_iff_exists_rat_btwn.1 h
    ⟨q, Rat.cast_nonneg.2 q0, aq, qb⟩,
    fun ⟨_, _, qa, qb⟩ => lt_trans qa qb⟩

中文:
定理 lt_iff_存在_real_btwn
  证明: ⟨fun h =>
    let ⟨q, q0, aq, qb⟩ := ENNReal.lt_iff_exists_rat_btwn.1 h
    ⟨q, Rat.cast_nonneg.2 q0, aq, qb⟩,
    fun ⟨_, _, qa, qb⟩ => lt_trans qa qb⟩

Depends on / 依赖: ENNReal, ENNReal.lt_iff_exists_rat_btwn, Rat.cast_nonneg, Sublist, Sublist.sublists, cast_nonneg, lt_iff_exists_rat_btwn, lt_trans, sublists
-/
theorem lt_iff_exists_real_btwn :
    a < b ↔ exists r : Real, 0 <= r ∧ a < ENNReal.ofReal r ∧ (ENNReal.ofReal r : Real>=0∞) < b :=
  ⟨fun h =>
    let ⟨q, q0, aq, qb⟩ := ENNReal.lt_iff_exists_rat_btwn.1 h
    ⟨q, Rat.cast_nonneg.2 q0, aq, qb⟩,
    fun ⟨_, _, qa, qb⟩ => lt_trans qa qb⟩

/--
theorem `lt_iff_exists_nnreal_btwn` / 定理 `lt_iff_exists_nnreal_btwn`

English:
theorem lt_iff_exists_nnreal_btwn
  statement: a < b ↔ exists r : Real>=0, a < r ∧ (r : Real>=0∞) < b
  proof: WithTop.lt_iff_exists_coe_btwn

中文:
定理 lt_iff_存在_nnreal_btwn
  结论: a < b ↔ 存在 r : 实数>=0, a < r ∧ (r : 实数>=0∞) < b
  证明: WithTop.lt_iff_exists_coe_btwn

Depends on / 依赖: WithTop, WithTop.lt_iff_exists_coe_btwn, lt_iff_exists_coe_btwn
-/
theorem lt_iff_exists_nnreal_btwn : a < b ↔ exists r : Real>=0, a < r ∧ (r : Real>=0∞) < b :=
  WithTop.lt_iff_exists_coe_btwn

/--
theorem `lt_iff_exists_add_pos_lt` / 定理 `lt_iff_exists_add_pos_lt`

English:
theorem lt_iff_exists_add_pos_lt
  statement: a < b ↔ exists r : Real>=0, 0 < r ∧ a + r < b
  proof: by
  refine ⟨fun hab => ?_, fun ⟨r, _, hr⟩ => lt_of_le_of_lt le_self_add hr⟩
  rcases lt_iff_exists_nnreal_btwn.1 hab with ⟨c, ac, cb⟩
  lift a to Real>=0 using ac.ne_top
  rw [coe_lt_coe] at ac
  refine ⟨c - a, tsub_pos_iff_lt.2 ac, ?_⟩
  rwa [← coe_add, add_tsub_cancel_of_le ac.le]

中文:
定理 lt_iff_存在_add_pos_lt
  结论: a < b ↔ 存在 r : 实数>=0, 0 < r ∧ a + r < b
  证明: by
  refine ⟨fun hab => ?_, fun ⟨r, _, hr⟩ => lt_of_le_of_lt le_self_add hr⟩
  rcases lt_iff_exists_nnreal_btwn.1 hab with ⟨c, ac, cb⟩
  lift a to Real>=0 using ac.ne_top
  rw [coe_lt_coe] at ac
  refine ⟨c - a, tsub_pos_iff_lt.2 ac, ?_⟩
  rwa [← coe_add, add_tsub_cancel_of_le ac.le]

Depends on / 依赖: ac.le, ac.ne_top, add_tsub_cancel_of_le, coe_add, coe_lt_coe, le_self_add, lt_iff_exists_nnreal_btwn, lt_of_le_of_lt, ne_top, tsub_pos_iff_lt
-/
theorem lt_iff_exists_add_pos_lt : a < b ↔ exists r : Real>=0, 0 < r ∧ a + r < b := by
  refine ⟨fun hab => ?_, fun ⟨r, _, hr⟩ => lt_of_le_of_lt le_self_add hr⟩
  rcases lt_iff_exists_nnreal_btwn.1 hab with ⟨c, ac, cb⟩
  lift a to Real>=0 using ac.ne_top
  rw [coe_lt_coe] at ac
  refine ⟨c - a, tsub_pos_iff_lt.2 ac, ?_⟩
  rwa [← coe_add, add_tsub_cancel_of_le ac.le]

/--
theorem `le_of_forall_pos_le_add` / 定理 `le_of_forall_pos_le_add`

English:
theorem le_of_forall_pos_le_add
  given: (h : forall ε : Real>=0, 0 < ε -> b < ∞ -> a <= b + ε)
  statement: a <= b
  proof: by
  contrapose! h
  rcases lt_iff_exists_add_pos_lt.1 h with ⟨r, hr0, hr⟩
  exact ⟨r, hr0, h.trans_le le_top, hr⟩

中文:
定理 le_of_对任意_pos_le_add
  条件: (h : 对任意 ε : 实数>=0, 0 < ε -> b < ∞ -> a <= b + ε)
  结论: a <= b
  证明: by
  contrapose! h
  rcases lt_iff_exists_add_pos_lt.1 h with ⟨r, hr0, hr⟩
  exact ⟨r, hr0, h.trans_le le_top, hr⟩

Depends on / 依赖: contrapose, h.trans_le, le_top, lt_iff_exists_add_pos_lt, trans_le
-/
theorem le_of_forall_pos_le_add (h : forall ε : Real>=0, 0 < ε -> b < ∞ -> a <= b + ε) : a <= b := by
  contrapose! h
  rcases lt_iff_exists_add_pos_lt.1 h with ⟨r, hr0, hr⟩
  exact ⟨r, hr0, h.trans_le le_top, hr⟩

/--
theorem `natCast_lt_coe` / 定理 `natCast_lt_coe`

English:
theorem natCast_lt_coe
  given: {n : Nat}
  statement: n < (r : Real>=0∞) ↔ n < r
  proof: ENNReal.coe_natCast n ▸ coe_lt_coe

中文:
定理 natCast_lt_coe
  条件: {n : 自然数}
  结论: n < (r : 实数>=0∞) ↔ n < r
  证明: ENNReal.coe_natCast n ▸ coe_lt_coe

Depends on / 依赖: ENNReal, ENNReal.coe_natCast, coe_lt_coe, coe_natCast
-/
theorem natCast_lt_coe {n : Nat} : n < (r : Real>=0∞) ↔ n < r := ENNReal.coe_natCast n ▸ coe_lt_coe

/--
theorem `coe_lt_natCast` / 定理 `coe_lt_natCast`

English:
theorem coe_lt_natCast
  given: {n : Nat}
  statement: (r : Real>=0∞) < n ↔ r < n
  proof: ENNReal.coe_natCast n ▸ coe_lt_coe

中文:
定理 coe_lt_natCast
  条件: {n : 自然数}
  结论: (r : 实数>=0∞) < n ↔ r < n
  证明: ENNReal.coe_natCast n ▸ coe_lt_coe

Depends on / 依赖: ENNReal, ENNReal.coe_natCast, coe_lt_coe, coe_natCast
-/
theorem coe_lt_natCast {n : Nat} : (r : Real>=0∞) < n ↔ r < n := ENNReal.coe_natCast n ▸ coe_lt_coe

/--
theorem `exists_nat_gt` / 定理 `exists_nat_gt`

English:
theorem exists_nat_gt
  given: {r : Real>=0∞} (h : r != ∞)
  statement: exists n : Nat, r < n
  proof: by
  lift r to Real>=0 using h
  rcases exists_nat_gt r with ⟨n, hn⟩
  exact ⟨n, coe_lt_natCast.2 hn⟩

@[simp]

中文:
定理 存在_nat_gt
  条件: {r : 实数>=0∞} (h : r != ∞)
  结论: 存在 n : 自然数, r < n
  证明: by
  lift r to Real>=0 using h
  rcases exists_nat_gt r with ⟨n, hn⟩
  exact ⟨n, coe_lt_natCast.2 hn⟩

@[simp]
-/
protected theorem exists_nat_gt {r : Real>=0∞} (h : r != ∞) : exists n : Nat, r < n := by
  lift r to Real>=0 using h
  rcases exists_nat_gt r with ⟨n, hn⟩
  exact ⟨n, coe_lt_natCast.2 hn⟩

@[simp]
/--
theorem `iUnion_Iio_coe_nat` / 定理 `iUnion_Iio_coe_nat`

English:
theorem iUnion_Iio_coe_nat
  statement: ⋃ n : Nat, Iio (n : Real>=0∞) = {∞}ᶜ
  proof: by
  ext x
  rw [mem_iUnion]
  exact ⟨fun ⟨n, hn⟩ => ne_top_of_lt hn, ENNReal.exists_nat_gt⟩

@[simp]

中文:
定理 iUnion_Iio_coe_nat
  结论: ⋃ n : 自然数, 左无界右开区间 (n : 实数>=0∞) = {∞}ᶜ
  证明: by
  ext x
  rw [mem_iUnion]
  exact ⟨fun ⟨n, hn⟩ => ne_top_of_lt hn, ENNReal.exists_nat_gt⟩

@[simp]

Depends on / 依赖: ENNReal, ENNReal.exists_nat_gt, exists_nat_gt, mem_iUnion, ne_top_of_lt
-/
theorem iUnion_Iio_coe_nat : ⋃ n : Nat, Iio (n : Real>=0∞) = {∞}ᶜ := by
  ext x
  rw [mem_iUnion]
  exact ⟨fun ⟨n, hn⟩ => ne_top_of_lt hn, ENNReal.exists_nat_gt⟩

@[simp]
/--
theorem `iUnion_Iic_coe_nat` / 定理 `iUnion_Iic_coe_nat`

English:
theorem iUnion_Iic_coe_nat
  statement: ⋃ n : Nat, Iic (n : Real>=0∞) = {∞}ᶜ
  proof: Subset.antisymm (iUnion_subset fun n _x hx => ne_top_of_le_ne_top (natCast_ne_top n) hx)
    iUnion_Iio_coe_nat ▸ iUnion_mono fun _ => Iio_subset_Iic_self

@[simp]

中文:
定理 iUnion_Iic_coe_nat
  结论: ⋃ n : 自然数, 左无界右闭区间 (n : 实数>=0∞) = {∞}ᶜ
  证明: Subset.antisymm (iUnion_subset fun n _x hx => ne_top_of_le_ne_top (natCast_ne_top n) hx)
    iUnion_Iio_coe_nat ▸ iUnion_mono fun _ => Iio_subset_Iic_self

@[simp]

Depends on / 依赖: Iio_subset_Iic_self, Subset, Subset.antisymm, antisymm, iUnion_Iio_coe_nat, iUnion_mono, iUnion_subset, natCast_ne_top, ne_top_of_le_ne_top
-/
theorem iUnion_Iic_coe_nat : ⋃ n : Nat, Iic (n : Real>=0∞) = {∞}ᶜ :=
Subset.antisymm (iUnion_subset fun n _x hx => ne_top_of_le_ne_top (natCast_ne_top n) hx)
    iUnion_Iio_coe_nat ▸ iUnion_mono fun _ => Iio_subset_Iic_self

@[simp]
/--
theorem `iUnion_Ioc_coe_nat` / 定理 `iUnion_Ioc_coe_nat`

English:
theorem iUnion_Ioc_coe_nat
  statement: ⋃ n : Nat, Ioc a n = Ioi a \ {∞}
  proof: by
  simp only [← Ioi_inter_Iic, ← inter_iUnion, iUnion_Iic_coe_nat, sdiff_eq]

@[simp]

中文:
定理 iUnion_Ioc_coe_nat
  结论: ⋃ n : 自然数, 左开右闭区间 a n = 左开右无界区间 a \ {∞}
  证明: by
  simp only [← Ioi_inter_Iic, ← inter_iUnion, iUnion_Iic_coe_nat, sdiff_eq]

@[simp]

Depends on / 依赖: Ioi_inter_Iic, iUnion_Iic_coe_nat, inter_iUnion, sdiff_eq
-/
theorem iUnion_Ioc_coe_nat : ⋃ n : Nat, Ioc a n = Ioi a \ {∞} := by
  simp only [← Ioi_inter_Iic, ← inter_iUnion, iUnion_Iic_coe_nat, sdiff_eq]

@[simp]
/--
theorem `iUnion_Ioo_coe_nat` / 定理 `iUnion_Ioo_coe_nat`

English:
theorem iUnion_Ioo_coe_nat
  statement: ⋃ n : Nat, Ioo a n = Ioi a \ {∞}
  proof: by
  simp only [← Ioi_inter_Iio, ← inter_iUnion, iUnion_Iio_coe_nat, sdiff_eq]

@[simp]

中文:
定理 iUnion_Ioo_coe_nat
  结论: ⋃ n : 自然数, 开区间 a n = 左开右无界区间 a \ {∞}
  证明: by
  simp only [← Ioi_inter_Iio, ← inter_iUnion, iUnion_Iio_coe_nat, sdiff_eq]

@[simp]

Depends on / 依赖: Ioi_inter_Iio, iUnion_Iio_coe_nat, inter_iUnion, sdiff_eq
-/
theorem iUnion_Ioo_coe_nat : ⋃ n : Nat, Ioo a n = Ioi a \ {∞} := by
  simp only [← Ioi_inter_Iio, ← inter_iUnion, iUnion_Iio_coe_nat, sdiff_eq]

@[simp]
/--
theorem `iUnion_Icc_coe_nat` / 定理 `iUnion_Icc_coe_nat`

English:
theorem iUnion_Icc_coe_nat
  statement: ⋃ n : Nat, Icc a n = Ici a \ {∞}
  proof: by
  simp only [← Ici_inter_Iic, ← inter_iUnion, iUnion_Iic_coe_nat, sdiff_eq]

@[simp]

中文:
定理 iUnion_Icc_coe_nat
  结论: ⋃ n : 自然数, 闭区间 a n = 左闭右无界区间 a \ {∞}
  证明: by
  simp only [← Ici_inter_Iic, ← inter_iUnion, iUnion_Iic_coe_nat, sdiff_eq]

@[simp]

Depends on / 依赖: Ici_inter_Iic, iUnion_Iic_coe_nat, inter_iUnion, sdiff_eq
-/
theorem iUnion_Icc_coe_nat : ⋃ n : Nat, Icc a n = Ici a \ {∞} := by
  simp only [← Ici_inter_Iic, ← inter_iUnion, iUnion_Iic_coe_nat, sdiff_eq]

@[simp]
/--
theorem `iUnion_Ico_coe_nat` / 定理 `iUnion_Ico_coe_nat`

English:
theorem iUnion_Ico_coe_nat
  statement: ⋃ n : Nat, Ico a n = Ici a \ {∞}
  proof: by
  simp only [← Ici_inter_Iio, ← inter_iUnion, iUnion_Iio_coe_nat, sdiff_eq]

@[simp]

中文:
定理 iUnion_Ico_coe_nat
  结论: ⋃ n : 自然数, 左闭右开区间 a n = 左闭右无界区间 a \ {∞}
  证明: by
  simp only [← Ici_inter_Iio, ← inter_iUnion, iUnion_Iio_coe_nat, sdiff_eq]

@[simp]

Depends on / 依赖: Ici_inter_Iio, iUnion_Iio_coe_nat, inter_iUnion, sdiff_eq
-/
theorem iUnion_Ico_coe_nat : ⋃ n : Nat, Ico a n = Ici a \ {∞} := by
  simp only [← Ici_inter_Iio, ← inter_iUnion, iUnion_Iio_coe_nat, sdiff_eq]

@[simp]
/--
theorem `iInter_Ici_coe_nat` / 定理 `iInter_Ici_coe_nat`

English:
theorem iInter_Ici_coe_nat
  statement: ⋂ n : Nat, Ici (n : Real>=0∞) = {∞}
  proof: by
  simp only [← compl_Iio, ← compl_iUnion, iUnion_Iio_coe_nat, compl_compl]

@[simp]

中文:
定理 i整数er_Ici_coe_nat
  结论: ⋂ n : 自然数, 左闭右无界区间 (n : 实数>=0∞) = {∞}
  证明: by
  simp only [← compl_Iio, ← compl_iUnion, iUnion_Iio_coe_nat, compl_compl]

@[simp]

Depends on / 依赖: compl_Iio, compl_compl, compl_iUnion, iUnion_Iio_coe_nat
-/
theorem iInter_Ici_coe_nat : ⋂ n : Nat, Ici (n : Real>=0∞) = {∞} := by
  simp only [← compl_Iio, ← compl_iUnion, iUnion_Iio_coe_nat, compl_compl]

@[simp]
/--
theorem `iInter_Ioi_coe_nat` / 定理 `iInter_Ioi_coe_nat`

English:
theorem iInter_Ioi_coe_nat
  statement: ⋂ n : Nat, Ioi (n : Real>=0∞) = {∞}
  proof: by
  simp only [← compl_Iic, ← compl_iUnion, iUnion_Iic_coe_nat, compl_compl]

@[simp, norm_cast]

中文:
定理 i整数er_Ioi_coe_nat
  结论: ⋂ n : 自然数, 左开右无界区间 (n : 实数>=0∞) = {∞}
  证明: by
  simp only [← compl_Iic, ← compl_iUnion, iUnion_Iic_coe_nat, compl_compl]

@[simp, norm_cast]

Depends on / 依赖: compl_Iic, compl_compl, compl_iUnion, iUnion_Iic_coe_nat
-/
theorem iInter_Ioi_coe_nat : ⋂ n : Nat, Ioi (n : Real>=0∞) = {∞} := by
  simp only [← compl_Iic, ← compl_iUnion, iUnion_Iic_coe_nat, compl_compl]

@[simp, norm_cast]
/--
theorem `coe_min` / 定理 `coe_min`

English:
theorem coe_min
  given: (r p : Real>=0)
  statement: ((min r p : Real>=0) : Real>=0∞) = min (r : Real>=0∞) p
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_min
  条件: (r p : 实数>=0)
  结论: ((最小值 r p : 实数>=0) : 实数>=0∞) = 最小值 (r : 实数>=0∞) p
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_min (r p : Real>=0) : ((min r p : Real>=0) : Real>=0∞) = min (r : Real>=0∞) p := rfl

@[simp, norm_cast]
/--
theorem `coe_max` / 定理 `coe_max`

English:
theorem coe_max
  given: (r p : Real>=0)
  statement: ((max r p : Real>=0) : Real>=0∞) = max (r : Real>=0∞) p
  proof: rfl

中文:
定理 coe_max
  条件: (r p : 实数>=0)
  结论: ((最大值 r p : 实数>=0) : 实数>=0∞) = 最大值 (r : 实数>=0∞) p
  证明: rfl
-/
theorem coe_max (r p : Real>=0) : ((max r p : Real>=0) : Real>=0∞) = max (r : Real>=0∞) p := rfl

/--
theorem `le_of_top_imp_top_of_toNNReal_le` / 定理 `le_of_top_imp_top_of_toNNReal_le`

English:
theorem le_of_top_imp_top_of_toNNReal_le
  statement: {a b : Real>=0∞} (h : a = ⊤ -> b = ⊤)
  proof: by
  by_contra! hlt
  lift b to Real>=0 using hlt.ne_top
  lift a to Real>=0 using mt h coe_ne_top
  refine hlt.not_ge ?_
  simpa using h_nnreal

@[simp]

中文:
定理 le_of_top_imp_top_of_toNN实数_le
  结论: {a b : 实数>=0∞} (h : a = ⊤ -> b = ⊤)
  证明: by
  by_contra! hlt
  lift b to Real>=0 using hlt.ne_top
  lift a to Real>=0 using mt h coe_ne_top
  refine hlt.not_ge ?_
  simpa using h_nnreal

@[simp]

Depends on / 依赖: coe_ne_top, h_nnreal, hlt.ne_top, hlt.not_ge, ne_top, not_ge
-/
theorem le_of_top_imp_top_of_toNNReal_le {a b : Real>=0∞} (h : a = ⊤ -> b = ⊤)
    (h_nnreal : a != ⊤ -> b != ⊤ -> a.toNNReal <= b.toNNReal) : a <= b := by
  by_contra! hlt
  lift b to Real>=0 using hlt.ne_top
  lift a to Real>=0 using mt h coe_ne_top
  refine hlt.not_ge ?_
  simpa using h_nnreal

@[simp]
/--
theorem `abs_toReal` / 定理 `abs_toReal`

English:
theorem abs_toReal
  given: {x : Real>=0∞}
  statement: |x.toReal| = x.toReal
  proof: by cases x <;> simp

中文:
定理 abs_to实数
  条件: {x : 实数>=0∞}
  结论: |x.to实数| = x.to实数
  证明: by cases x <;> simp
-/
theorem abs_toReal {x : Real>=0∞} : |x.toReal| = x.toReal := by cases x <;> simp

end Order

section CompleteLattice
variable {ι : Sort*} {f : ι -> Real>=0}

/--
theorem `coe_sSup` / 定理 `coe_sSup`

English:
theorem coe_sSup
  given: {s : Set Real>=0}
  statement: BddAbove s -> (↑(sSup s) : Real>=0∞) = ⨆ a in s, ↑a
  proof: WithTop.coe_sSup

中文:
定理 coe_sSup
  条件: {s : 集合 实数>=0}
  结论: BddAbove s -> (↑(sSup s) : 实数>=0∞) = ⨆ a in s, ↑a
  证明: WithTop.coe_sSup

Depends on / 依赖: WithTop, WithTop.coe_sSup, coe_sSup
-/
theorem coe_sSup {s : Set Real>=0} : BddAbove s -> (↑(sSup s) : Real>=0∞) = ⨆ a in s, ↑a :=
  WithTop.coe_sSup

/--
theorem `coe_sInf` / 定理 `coe_sInf`

English:
theorem coe_sInf
  given: {s : Set Real>=0} (hs : s.Nonempty)
  statement: (↑(sInf s) : Real>=0∞) = ⨅ a in s, ↑a
  proof: WithTop.coe_sInf hs (OrderBot.bddBelow s)

中文:
定理 coe_sInf
  条件: {s : 集合 实数>=0} (hs : s.非空)
  结论: (↑(sInf s) : 实数>=0∞) = ⨅ a in s, ↑a
  证明: WithTop.coe_sInf hs (OrderBot.bddBelow s)

Depends on / 依赖: OrderBot, OrderBot.bddBelow, WithTop, WithTop.coe_sInf, bddBelow, coe_sInf
-/
theorem coe_sInf {s : Set Real>=0} (hs : s.Nonempty) : (↑(sInf s) : Real>=0∞) = ⨅ a in s, ↑a :=
  WithTop.coe_sInf hs (OrderBot.bddBelow s)

/--
theorem `coe_iSup` / 定理 `coe_iSup`

English:
theorem coe_iSup
  given: {ι : Sort*} {f : ι -> Real>=0} (hf : BddAbove (range f))
  proof: WithTop.coe_iSup _ hf

@[norm_cast]

中文:
定理 coe_iSup
  条件: {ι : 类型层*} {f : ι -> 实数>=0} (hf : BddAbove (range f))
  证明: WithTop.coe_iSup _ hf

@[norm_cast]

Depends on / 依赖: WithTop, WithTop.coe_iSup, coe_iSup
-/
theorem coe_iSup {ι : Sort*} {f : ι -> Real>=0} (hf : BddAbove (range f)) :
    (↑(iSup f) : Real>=0∞) = ⨆ a, ↑(f a) :=
  WithTop.coe_iSup _ hf

@[norm_cast]
/--
theorem `coe_iInf` / 定理 `coe_iInf`

English:
theorem coe_iInf
  given: {ι : Sort*} [Nonempty ι] (f : ι -> Real>=0)
  statement: (↑(iInf f) : Real>=0∞) = ⨅ a, ↑(f a)
  proof: WithTop.coe_iInf (OrderBot.bddBelow _)

中文:
定理 coe_iInf
  条件: {ι : 类型层*} [非空 ι] (f : ι -> 实数>=0)
  结论: (↑(iInf f) : 实数>=0∞) = ⨅ a, ↑(f a)
  证明: WithTop.coe_iInf (OrderBot.bddBelow _)

Depends on / 依赖: OrderBot, OrderBot.bddBelow, WithTop, WithTop.coe_iInf, bddBelow, coe_iInf
-/
theorem coe_iInf {ι : Sort*} [Nonempty ι] (f : ι -> Real>=0) : (↑(iInf f) : Real>=0∞) = ⨅ a, ↑(f a) :=
  WithTop.coe_iInf (OrderBot.bddBelow _)

/--
theorem `coe_mem_upperBounds` / 定理 `coe_mem_upperBounds`

English:
theorem coe_mem_upperBounds
  given: {s : Set Real>=0}
  proof: by
  simp +contextual [upperBounds, forall_mem_image, -mem_image, *]

中文:
定理 coe_mem_upperBounds
  条件: {s : 集合 实数>=0}
  证明: by
  simp +contextual [upperBounds, forall_mem_image, -mem_image, *]

Depends on / 依赖: contextual, forall_mem_image, mem_image, upperBounds
-/
theorem coe_mem_upperBounds {s : Set Real>=0} :
    ↑r in upperBounds (ofNNReal '' s) ↔ r in upperBounds s := by
  simp +contextual [upperBounds, forall_mem_image, -mem_image, *]

/--
lemma `iSup_coe_eq_top` / 引理 `iSup_coe_eq_top`

English:
lemma iSup_coe_eq_top
  statement: ⨆ i, (f i : Real>=0∞) = ⊤ ↔ ¬ BddAbove (range f)
  proof: WithTop.iSup_coe_eq_top

中文:
引理 iSup_coe_eq_top
  结论: ⨆ i, (f i : 实数>=0∞) = ⊤ ↔ ¬ BddAbove (range f)
  证明: WithTop.iSup_coe_eq_top

Depends on / 依赖: WithTop, WithTop.iSup_coe_eq_top, iSup_coe_eq_top
-/
lemma iSup_coe_eq_top : ⨆ i, (f i : Real>=0∞) = ⊤ ↔ ¬ BddAbove (range f) := WithTop.iSup_coe_eq_top
/--
lemma `iSup_coe_lt_top` / 引理 `iSup_coe_lt_top`

English:
lemma iSup_coe_lt_top
  statement: ⨆ i, (f i : Real>=0∞) < ⊤ ↔ BddAbove (range f)
  proof: WithTop.iSup_coe_lt_top

中文:
引理 iSup_coe_lt_top
  结论: ⨆ i, (f i : 实数>=0∞) < ⊤ ↔ BddAbove (range f)
  证明: WithTop.iSup_coe_lt_top

Depends on / 依赖: WithTop, WithTop.iSup_coe_lt_top, iSup_coe_lt_top
-/
lemma iSup_coe_lt_top : ⨆ i, (f i : Real>=0∞) < ⊤ ↔ BddAbove (range f) := WithTop.iSup_coe_lt_top
/--
lemma `iInf_coe_eq_top` / 引理 `iInf_coe_eq_top`

English:
lemma iInf_coe_eq_top
  statement: ⨅ i, (f i : Real>=0∞) = ⊤ ↔ IsEmpty ι
  proof: WithTop.iInf_coe_eq_top

中文:
引理 iInf_coe_eq_top
  结论: ⨅ i, (f i : 实数>=0∞) = ⊤ ↔ 是空 ι
  证明: WithTop.iInf_coe_eq_top

Depends on / 依赖: WithTop, WithTop.iInf_coe_eq_top, iInf_coe_eq_top
-/
lemma iInf_coe_eq_top : ⨅ i, (f i : Real>=0∞) = ⊤ ↔ IsEmpty ι := WithTop.iInf_coe_eq_top
/--
lemma `iInf_coe_lt_top` / 引理 `iInf_coe_lt_top`

English:
lemma iInf_coe_lt_top
  statement: ⨅ i, (f i : Real>=0∞) < ⊤ ↔ Nonempty ι
  proof: WithTop.iInf_coe_lt_top

中文:
引理 iInf_coe_lt_top
  结论: ⨅ i, (f i : 实数>=0∞) < ⊤ ↔ 非空 ι
  证明: WithTop.iInf_coe_lt_top

Depends on / 依赖: WithTop, WithTop.iInf_coe_lt_top, iInf_coe_lt_top
-/
lemma iInf_coe_lt_top : ⨅ i, (f i : Real>=0∞) < ⊤ ↔ Nonempty ι := WithTop.iInf_coe_lt_top

end CompleteLattice

-- TODO: add lemmas about `OfNat.ofNat`

end ENNReal

open ENNReal

namespace Set

namespace OrdConnected

variable {s : Set Real} {t : Set Real>=0} {u : Set Real>=0∞}

/--
theorem `preimage_coe_nnreal_ennreal` / 定理 `preimage_coe_nnreal_ennreal`

English:
theorem preimage_coe_nnreal_ennreal
  given: (h : u.OrdConnected)
  statement: ((↑) ⁻¹' u : Set Real>=0).OrdConnected
  proof: h.preimage_mono ENNReal.coe_mono

中文:
定理 preimage_coe_nnreal_ennreal
  条件: (h : u.序连通)
  结论: ((↑) ⁻¹' u : 集合 实数>=0).序连通
  证明: h.preimage_mono ENNReal.coe_mono

Depends on / 依赖: ENNReal, ENNReal.coe_mono, coe_mono, h.preimage_mono, preimage_mono
-/
theorem preimage_coe_nnreal_ennreal (h : u.OrdConnected) : ((↑) ⁻¹' u : Set Real>=0).OrdConnected :=
  h.preimage_mono ENNReal.coe_mono

-- TODO: generalize to `WithTop`
/--
theorem `image_coe_nnreal_ennreal` / 定理 `image_coe_nnreal_ennreal`

English:
theorem image_coe_nnreal_ennreal
  given: (h : t.OrdConnected)
  statement: ((↑) '' t : Set Real>=0∞).OrdConnected
  proof: by
  refine ⟨forall_mem_image.2 fun x hx => forall_mem_image.2 fun y hy z hz => ?_⟩
  rcases ENNReal.le_coe_iff.1 hz.2 with ⟨z, rfl, -⟩
  exact mem_image_of_mem _ (h.out hx hy ⟨ENNReal.coe_le_coe.1 hz.1, ENNReal.coe_le_coe.1 hz.2⟩)

中文:
定理 image_coe_nnreal_ennreal
  条件: (h : t.序连通)
  结论: ((↑) '' t : 集合 实数>=0∞).序连通
  证明: by
  refine ⟨forall_mem_image.2 fun x hx => forall_mem_image.2 fun y hy z hz => ?_⟩
  rcases ENNReal.le_coe_iff.1 hz.2 with ⟨z, rfl, -⟩
  exact mem_image_of_mem _ (h.out hx hy ⟨ENNReal.coe_le_coe.1 hz.1, ENNReal.coe_le_coe.1 hz.2⟩)

Depends on / 依赖: ENNReal, ENNReal.coe_le_coe, ENNReal.le_coe_iff, coe_le_coe, forall_mem_image, h.out, le_coe_iff, mem_image_of_mem
-/
theorem image_coe_nnreal_ennreal (h : t.OrdConnected) : ((↑) '' t : Set Real>=0∞).OrdConnected := by
  refine ⟨forall_mem_image.2 fun x hx => forall_mem_image.2 fun y hy z hz => ?_⟩
  rcases ENNReal.le_coe_iff.1 hz.2 with ⟨z, rfl, -⟩
  exact mem_image_of_mem _ (h.out hx hy ⟨ENNReal.coe_le_coe.1 hz.1, ENNReal.coe_le_coe.1 hz.2⟩)

/--
theorem `preimage_ennreal_ofReal` / 定理 `preimage_ennreal_ofReal`

English:
theorem preimage_ennreal_ofReal
  given: (h : u.OrdConnected)
  statement: (ENNReal.ofReal ⁻¹' u).OrdConnected
  proof: h.preimage_coe_nnreal_ennreal.preimage_real_toNNReal

中文:
定理 preimage_ennreal_of实数
  条件: (h : u.序连通)
  结论: (广义非负实数.of实数 ⁻¹' u).序连通
  证明: h.preimage_coe_nnreal_ennreal.preimage_real_toNNReal

Depends on / 依赖: h.preimage_coe_nnreal_ennreal.preimage_real_toNNReal, preimage_coe_nnreal_ennreal, preimage_real_toNNReal
-/
theorem preimage_ennreal_ofReal (h : u.OrdConnected) : (ENNReal.ofReal ⁻¹' u).OrdConnected :=
  h.preimage_coe_nnreal_ennreal.preimage_real_toNNReal

/--
theorem `image_ennreal_ofReal` / 定理 `image_ennreal_ofReal`

English:
theorem image_ennreal_ofReal
  given: (h : s.OrdConnected)
  statement: (ENNReal.ofReal '' s).OrdConnected
  proof: by
  simpa only [image_image] using! h.image_real_toNNReal.image_coe_nnreal_ennreal

中文:
定理 image_ennreal_of实数
  条件: (h : s.序连通)
  结论: (广义非负实数.of实数 '' s).序连通
  证明: by
  simpa only [image_image] using! h.image_real_toNNReal.image_coe_nnreal_ennreal

Depends on / 依赖: h.image_real_toNNReal.image_coe_nnreal_ennreal, image_coe_nnreal_ennreal, image_image, image_real_toNNReal
-/
theorem image_ennreal_ofReal (h : s.OrdConnected) : (ENNReal.ofReal '' s).OrdConnected := by
  simpa only [image_image] using! h.image_real_toNNReal.image_coe_nnreal_ennreal

end OrdConnected

end Set

/-- While not very useful, this instance uses the same representation as `Real.instRepr`. -/
unsafe instance : Repr Real>=0∞ where
  reprPrec
  | (r : Real>=0), p => Repr.addAppParen f!"ENNReal.ofReal ({repr r.val})" p
  | ∞, _ => "∞"

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

/-- Extension for the `positivity` tactic: `ENNReal.toReal`. -/
@[positivity ENNReal.toReal _]
meta def evalENNRealtoReal : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Real), ~q(ENNReal.toReal $a) =>
    assertInstancesCommute
    pure (.nonnegative q(ENNReal.toReal_nonneg))
  | _, _, _ => throwError "not ENNReal.toReal"

/-- Extension for the `positivity` tactic: `ENNReal.ofNNReal`. -/
@[positivity ENNReal.ofNNReal _]
meta def evalENNRealOfNNReal : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Real>=0∞), ~q(ENNReal.ofNNReal $a) =>
    assertInstancesCommute
    let ra ← core q(inferInstance) (some q(inferInstance)) a
    match ra with
| .positive pa => pure .positive q(ENNReal.coe_pos.mpr $pa)
    | _ => pure .none
  | _, _, _ => throwError "not ENNReal.ofNNReal"

end Mathlib.Meta.Positivity
