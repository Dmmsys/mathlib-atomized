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

/-- The extended nonnegative real numbers. This is usually denoted [0, ∞],
  and is relevant as the codomain of a measure. -/
/-
**ENNReal** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ENNReal
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The extended nonnegative real numbers. This is usually denoted [0, ∞],
  and is relevant as the codomain of a measure.
-/
def ENNReal := WithTop ℝ≥0

@[inherit_doc]
scoped[ENNReal] notation "ℝ≥0∞" => ENNReal

-- note: using notation3 rather than notation means that `∞` pretty-prints
-- as `∞` rather than `top`. Despite this, we still use `top` in the names of lemmas.
/-- Notation for infinity as an `ENNReal` number. -/
scoped[ENNReal] notation3 "∞" => (⊤ : ENNReal)

namespace ENNReal

/-- Coercion from `ℝ≥0` to `ℝ≥0∞`. -/
/-
**ENNReal.ofNNReal** 是 Mathlib 中的一个定义，位于命名空间 `ENNReal`。
形式化陈述：NNReal → ENNReal
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion from `ℝ≥0` to `ℝ≥0∞`.
-/
@[coe, match_pattern] def ofNNReal : ℝ≥0 → ℝ≥0∞ := WithTop.some
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion from `ℝ≥0` to `ℝ≥0∞`.
-/
instance : Coe ℝ≥0 ℝ≥0∞ := ⟨ofNNReal⟩

/- Declare these instances by hand for good defeqs -/
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Declare these instances by hand for good defeqs
-/
instance : Zero ℝ≥0∞ := ⟨ofNNReal 0⟩
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One ℝ≥0∞ := ⟨ofNNReal 1⟩
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Bot ℝ≥0∞ := ⟨0⟩
/-
**ENNReal.** 是 Mathlib 中的一个示例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : (0 : ℝ≥0∞) = ⊥ := by with_reducible_and_instances rfl

deriving instance Top, LE, PartialOrder, Add, AddCommMonoidWithOne, SemilatticeSup, DistribLattice,
  Nontrivial for ENNReal
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderBot ℝ≥0∞ := inferInstanceAs (OrderBot (WithTop ℝ≥0))
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderTop ℝ≥0∞ := inferInstanceAs (OrderTop (WithTop ℝ≥0))
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : BoundedOrder ℝ≥0∞ := inferInstanceAs (BoundedOrder (WithTop ℝ≥0))
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CharZero ℝ≥0∞ := inferInstanceAs (CharZero (WithTop ℝ≥0))
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Min ℝ≥0∞ := SemilatticeInf.toMin
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Max ℝ≥0∞ := SemilatticeSup.toMax
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : CommSemiring ℝ≥0∞ :=
  inferInstanceAs (CommSemiring (WithTop ℝ≥0))
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsOrderedRing ℝ≥0∞ :=
  inferInstanceAs (IsOrderedRing (WithTop ℝ≥0))
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CanonicallyOrderedAdd ℝ≥0∞ :=
  inferInstanceAs (CanonicallyOrderedAdd (WithTop ℝ≥0))
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NoZeroDivisors ℝ≥0∞ :=
  inferInstanceAs (NoZeroDivisors (WithTop ℝ≥0))
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : CompleteLinearOrder ℝ≥0∞ :=
  inferInstanceAs (CompleteLinearOrder (WithTop ℝ≥0))
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DenselyOrdered ℝ≥0∞ := inferInstanceAs (DenselyOrdered (WithTop ℝ≥0))
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : AddCommMonoid ℝ≥0∞ :=
  inferInstanceAs (AddCommMonoid (WithTop ℝ≥0))
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : LinearOrder ℝ≥0∞ :=
  inferInstanceAs (LinearOrder (WithTop ℝ≥0))
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsOrderedAddMonoid ℝ≥0∞ :=
  inferInstanceAs (IsOrderedAddMonoid (WithTop ℝ≥0))
/-
**ENNReal.instSub** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
形式化陈述：instSub : Sub Real>=0∞
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSub : Sub ℝ≥0∞ := inferInstanceAs (Sub (WithTop ℝ≥0))
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderedSub ℝ≥0∞ := inferInstanceAs (OrderedSub (WithTop ℝ≥0))
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : LinearOrderedAddCommMonoidWithTop ℝ≥0∞ :=
  inferInstanceAs (LinearOrderedAddCommMonoidWithTop (WithTop ℝ≥0))

-- RFC: redefine using pattern matching?
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Inv ℝ≥0∞ := ⟨fun a => sInf { b | 1 ≤ a * b }⟩
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : DivInvMonoid ℝ≥0∞ where

variable {a b c d : ℝ≥0∞} {r p q : ℝ≥0} {n : ℕ}
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsOrderedMonoid ℝ≥0∞ where
  mul_le_mul_left _ _ := mul_le_mul_left
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Unique (AddUnits ℝ≥0∞) where
  default := 0
  uniq a := AddUnits.ext <| nonpos_iff_eq_zero.1 <| by rw [← a.add_neg]; exact le_self_add
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited ℝ≥0∞ := ⟨0⟩

/-- A version of `WithTop.recTopCoe` that uses `ENNReal.ofNNReal`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
/-
**ENNReal.recTopCoe** 是 Mathlib 中的一个定义，位于命名空间 `ENNReal`。
形式化陈述：recTopCoe {C : Real>=0∞ -> Sort*} (top : C ∞) (coe : forall x : Real>=0, C
 x) (x : Real>=0∞) : C x
参数：top : C ∞；coe : forall x : Real>=0, C x；x : Real>=0∞。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `WithTop.recTopCoe` that uses `ENNReal.ofNNReal`.
-/
def recTopCoe {C : ℝ≥0∞ → Sort*} (top : C ∞) (coe : ∀ x : ℝ≥0, C x) (x : ℝ≥0∞) : C x :=
  WithTop.recTopCoe top coe x
/-
**ENNReal.recTopCoe_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {C : ENNReal → Sort u_2} (top : C ⊤) (coe : (x : NNReal) → C ↑x), ENNRea
l.recTopCoe top coe ⊤ = top
参数：top : C ⊤；coe : (x : NNReal) → C ↑x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma recTopCoe_top {C : ℝ≥0∞ → Sort*} (top : C ∞) (coe : ∀ x : ℝ≥0, C x) :
    recTopCoe top coe ∞ = top := rfl
/-
**ENNReal.recTopCoe_ofNNReal** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {C : ENNReal → Sort u_2} (top : C ⊤) (coe : (x : NNReal) → C ↑x) (x : NN
Real), ENNReal.recTopCoe top coe ↑x = coe x
参数：top : C ⊤；coe : (x : NNReal) → C ↑x；x : NNReal。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma recTopCoe_ofNNReal {C : ℝ≥0∞ → Sort*} (top : C ∞) (coe : ∀ x : ℝ≥0, C x) (x : ℝ≥0) :
    recTopCoe top coe x = coe x := rfl
/-
**ENNReal.canLift** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
形式化陈述：canLift : CanLift Real>=0∞ Real>=0 ofNNReal (· != ∞)
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.canLift`：∀ {α : Type u_1}, CanLift (WithTop α) α WithTop.some fu
n r => r ≠ ⊤
-/
instance canLift : CanLift ℝ≥0∞ ℝ≥0 ofNNReal (· ≠ ∞) := WithTop.canLift
/-
**ENNReal.none_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：none = ⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem none_eq_top : (none : ℝ≥0∞) = ∞ := rfl
/-
**ENNReal.some_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (a : NNReal), some a = ↑a
参数：a : NNReal。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem some_eq_coe (a : ℝ≥0) : (Option.some a : ℝ≥0∞) = (↑a : ℝ≥0∞) := rfl
/-
**ENNReal.some_eq_coe'** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (a : NNReal), ↑a = ↑a
参数：a : NNReal。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem some_eq_coe' (a : ℝ≥0) : (WithTop.some a : ℝ≥0∞) = (↑a : ℝ≥0∞) := rfl
/-
**ENNReal.coe_injective** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：coe_injective : Injective ((↑) : Real>=0 -> Real>=0∞)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.coe_injective`：∀ {α : Type u_1}, Function.Injective WithTop.some
-/
lemma coe_injective : Injective ((↑) : ℝ≥0 → ℝ≥0∞) := WithTop.coe_injective
/-
**ENNReal.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {p q : NNReal}, ↑p = ↑q ↔ p = q
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `ENNReal.coe_injective`：coe_injective : Injective ((↑) : Real>=0 -> Real>
=0∞)
-/
@[simp, norm_cast] lemma coe_inj : (p : ℝ≥0∞) = q ↔ p = q := coe_injective.eq_iff
/-
**ENNReal.coe_ne_coe** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：coe_ne_coe : (p : Real>=0∞) != q ↔ p != q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `ENNReal.coe_inj`：∀ {p q : NNReal}, ↑p = ↑q ↔ p = q
-/
lemma coe_ne_coe : (p : ℝ≥0∞) ≠ q ↔ p ≠ q := coe_inj.not
/-
**ENNReal.range_coe'** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：range_coe' : range ofNNReal = Iio ∞
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.range_coe`：range_coe : range (some : α -> WithTop α) = Iio ⊤
-/
theorem range_coe' : range ofNNReal = Iio ∞ := WithTop.range_coe
/-
**ENNReal.range_coe** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：range_coe : range ofNNReal = {∞}ᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsCompl.compl_eq`：IsCompl.compl_eq (h : IsCompl a b) : aᶜ = b
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `Set.isCompl_range_some_none`：isCompl_range_some_none (α : Type*) : IsCom
pl (range (some : α -> Option α)) {none}
-/
theorem range_coe : range ofNNReal = {∞}ᶜ := (isCompl_range_some_none ℝ≥0).symm.compl_eq.symm
/-
**ENNReal.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NNRatCast ℝ≥0∞ where
  nnratCast r := ofNNReal r

@[norm_cast]
/-
**ENNReal.coe_nnratCast** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：coe_nnratCast (q : Rat>=0) : ↑(q : Real>=0) = (q : Real>=0∞)
参数：q : Rat>=0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_nnratCast (q : ℚ≥0) : ↑(q : ℝ≥0) = (q : ℝ≥0∞) := rfl

/-- `toNNReal x` returns `x` if it is real, otherwise 0. -/
/-
**ENNReal.toNNReal** 是 Mathlib 中的一个定义，位于命名空间 `ENNReal`。
形式化陈述：ENNReal → NNReal
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`toNNReal x` returns `x` if it is real, otherwise 0.
-/
protected def toNNReal : ℝ≥0∞ → ℝ≥0 := WithTop.untopD 0

/-- `toReal x` returns `x` if it is real, `0` otherwise. -/
/-
**ENNReal.toReal** 是 Mathlib 中的一个定义，位于命名空间 `ENNReal`。
形式化陈述：ENNReal → ℝ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`toReal x` returns `x` if it is real, `0` otherwise.
-/
protected def toReal (a : ℝ≥0∞) : Real := a.toNNReal

/-- `ofReal x` returns `x` if it is nonnegative, `0` otherwise. -/
/-
**ENNReal.ofReal** 是 Mathlib 中的一个定义，位于命名空间 `ENNReal`。
形式化陈述：ℝ → ENNReal
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ofReal x` returns `x` if it is nonnegative, `0` otherwise.
-/
protected def ofReal (r : Real) : ℝ≥0∞ := r.toNNReal
/-
**ENNReal.toNNReal_coe** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (r : NNReal), (↑r).toNNReal = r
参数：r : NNReal；↑r。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma toNNReal_coe (r : ℝ≥0) : (r : ℝ≥0∞).toNNReal = r := rfl

@[simp]
/-
**ENNReal.coe_toNNReal** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a : ENNReal}, a ≠ ⊤ → ↑a.toNNReal = a
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toNNReal : ∀ {a : ℝ≥0∞}, a ≠ ∞ → ↑a.toNNReal = a
  | ofNNReal _, _ => rfl
  | ⊤, h => (h rfl).elim

@[simp]
/-
**ENNReal.coe_comp_toNNReal_comp** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：coe_comp_toNNReal_comp {ι : Type*} {f : ι -> Real>=0∞} (hf : forall x, f x
 != ∞) : (fun (x : Real>=0) => (x : Real>=0∞)) ∘ ENNReal.toNNReal ∘ f = f
参数：hf : forall x, f x != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.coe_toNNReal`：∀ {a : ENNReal}, a ≠ ⊤ → ↑a.toNNReal = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_comp_toNNReal_comp {ι : Type*} {f : ι → ℝ≥0∞} (hf : ∀ x, f x ≠ ∞) :
    (fun (x : ℝ≥0) => (x : ℝ≥0∞)) ∘ ENNReal.toNNReal ∘ f = f := by
  ext x
  simp [coe_toNNReal (hf x)]

@[simp]
/-
**ENNReal.ofReal_toReal** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNReal.ofReal a.toReal = a
参数：h : a != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.toNNReal_coe`：∀ {r : NNReal}, (↑r).toNNReal = r
· 使用定理 `ENNReal.coe_toNNReal`：∀ {a : ENNReal}, a ≠ ⊤ → ↑a.toNNReal = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofReal_toReal {a : ℝ≥0∞} (h : a ≠ ∞) : ENNReal.ofReal a.toReal = a := by
  simp [ENNReal.toReal, ENNReal.ofReal, h]

@[simp]
/-
**ENNReal.toReal_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.ofReal r).toReal = r
参数：h : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
-/
theorem toReal_ofReal {r : ℝ} (h : 0 ≤ r) : (ENNReal.ofReal r).toReal = r :=
  max_eq_left h
/-
**ENNReal.toReal_ofReal'** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toReal_ofReal' {r : Real} : (ENNReal.ofReal r).toReal = max r 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toReal_ofReal' {r : ℝ} : (ENNReal.ofReal r).toReal = max r 0 := rfl
/-
**ENNReal.coe_toNNReal_le_self** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a : ENNReal}, ↑a.toNNReal ≤ a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.toNNReal_coe`：∀ (r : NNReal), (↑r).toNNReal = r
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem coe_toNNReal_le_self : ∀ {a : ℝ≥0∞}, ↑a.toNNReal ≤ a
  | ofNNReal r => by rw [toNNReal_coe]
  | ⊤ => le_top
/-
**ENNReal.coe_nnreal_eq** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：coe_nnreal_eq (r : Real>=0) : (r : Real>=0∞) = ENNReal.ofReal r
参数：r : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.ofReal.eq_1`：∀ (r : ℝ), ENNReal.ofReal r = ↑r.toNNReal
· 使用定理 `Real.toNNReal_coe`：∀ {r : NNReal}, (↑r).toNNReal = r
-/
theorem coe_nnreal_eq (r : ℝ≥0) : (r : ℝ≥0∞) = ENNReal.ofReal r := by
  rw [ENNReal.ofReal, Real.toNNReal_coe]
/-
**ENNReal.ofReal_eq_coe_nnreal** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_eq_coe_nnreal {x : Real} (h : 0 <= x) : ENNReal.ofReal x = ofNNReal
 (NNReal.mk x h)
参数：h : 0 <= x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_nnreal_eq`：coe_nnreal_eq (r : Real>=0) : (r : Real>=0∞) = EN
NReal.ofReal r
-/
theorem ofReal_eq_coe_nnreal {x : ℝ} (h : 0 ≤ x) :
    ENNReal.ofReal x = ofNNReal (NNReal.mk x h) :=
  (coe_nnreal_eq ⟨x, h⟩).symm
/-
**ENNReal.ofNNReal_toNNReal** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：ofNNReal_toNNReal (x : Real) : (Real.toNNReal x : Real>=0∞) = ENNReal.ofRe
al x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofNNReal_toNNReal (x : ℝ) : (Real.toNNReal x : ℝ≥0∞) = ENNReal.ofReal x := rfl
/-
**ENNReal.ofReal_coe_nnreal** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {p : NNReal}, ENNReal.ofReal ↑p = ↑p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_nnreal_eq`：coe_nnreal_eq (r : Real>=0) : (r : Real>=0∞) = EN
NReal.ofReal r
-/
@[simp] theorem ofReal_coe_nnreal : ENNReal.ofReal p = p := (coe_nnreal_eq p).symm
/-
**ENNReal.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：↑0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] theorem coe_zero : ↑(0 : ℝ≥0) = (0 : ℝ≥0∞) := rfl
/-
**ENNReal.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：↑1 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] theorem coe_one : ↑(1 : ℝ≥0) = (1 : ℝ≥0∞) := rfl
/-
**ENNReal.toReal_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {a : ENNReal}, 0 ≤ a.toReal
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
@[simp] theorem toReal_nonneg {a : ℝ≥0∞} : 0 ≤ a.toReal := a.toNNReal.2
/-
**ENNReal.coe_toNNReal_eq_toReal** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (z : ENNReal), ↑z.toNNReal = z.toReal
参数：z : ENNReal。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[norm_cast] theorem coe_toNNReal_eq_toReal (z : ℝ≥0∞) : (z.toNNReal : ℝ) = z.toReal := rfl
/-
**ENNReal.toNNReal_toReal_eq** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (z : ENNReal), z.toReal.toNNReal = z.toNNReal
参数：z : ENNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem toNNReal_toReal_eq (z : ℝ≥0∞) : z.toReal.toNNReal = z.toNNReal := by
  ext; simp [coe_toNNReal_eq_toReal]
/-
**ENNReal.toNNReal_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：⊤.toNNReal = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toNNReal_top : ∞.toNNReal = 0 := rfl
/-
**ENNReal.toReal_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：⊤.toReal = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toReal_top : ∞.toReal = 0 := rfl
/-
**ENNReal.toReal_one** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：ENNReal.toReal 1 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toReal_one : (1 : ℝ≥0∞).toReal = 1 := rfl
/-
**ENNReal.toNNReal_one** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：ENNReal.toNNReal 1 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toNNReal_one : (1 : ℝ≥0∞).toNNReal = 1 := rfl
/-
**ENNReal.coe_toReal** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (r : NNReal), (↑r).toReal = ↑r
参数：r : NNReal；↑r。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_toReal (r : ℝ≥0) : (r : ℝ≥0∞).toReal = r := rfl
/-
**ENNReal.toNNReal_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：ENNReal.toNNReal 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toNNReal_zero : (0 : ℝ≥0∞).toNNReal = 0 := rfl
/-
**ENNReal.toReal_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：ENNReal.toReal 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toReal_zero : (0 : ℝ≥0∞).toReal = 0 := rfl
/-
**ENNReal.ofReal_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：ENNReal.ofReal 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.toNNReal_zero`：toNNReal_zero : Real.toNNReal 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem ofReal_zero : ENNReal.ofReal (0 : ℝ) = 0 := by simp [ENNReal.ofReal]
/-
**ENNReal.ofReal_one** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：ENNReal.ofReal 1 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.toNNReal_one`：toNNReal_one : Real.toNNReal 1 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem ofReal_one : ENNReal.ofReal (1 : ℝ) = (1 : ℝ≥0∞) := by simp [ENNReal.ofReal]
/-
**ENNReal.ofReal_toReal_le** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_toReal_le {a : Real>=0∞} : ENNReal.ofReal a.toReal <= a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
-/
theorem ofReal_toReal_le {a : ℝ≥0∞} : ENNReal.ofReal a.toReal ≤ a :=
  if ha : a = ∞ then ha.symm ▸ le_top else le_of_eq (ofReal_toReal ha)
/-
**ENNReal.forall_ennreal** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：forall_ennreal {p : Real>=0∞ -> Prop} : (forall a, p a) ↔ (forall r : Real
>=0, p r) ∧ p ∞
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `WithTop.forall`：∀ {α : Type u_1} {p : WithTop α → Prop}, (∀ (x : WithTop
 α), p x) ↔ p ⊤ ∧ ∀ (x : α), p ↑x
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
-/
theorem forall_ennreal {p : ℝ≥0∞ → Prop} : (∀ a, p a) ↔ (∀ r : ℝ≥0, p r) ∧ p ∞ :=
  WithTop.forall.trans and_comm
/-
**ENNReal.forall_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：forall_ne_top {p : Real>=0∞ -> Prop} : (forall x != ∞, p x) ↔ forall x : R
eal>=0, p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.forall_ne_top`：∀ {α : Type u_1} {p : WithTop α → Prop}, (∀ (x : 
WithTop α), x ≠ ⊤ → p x) ↔ ∀ (x : α), p ↑x
-/
theorem forall_ne_top {p : ℝ≥0∞ → Prop} : (∀ x ≠ ∞, p x) ↔ ∀ x : ℝ≥0, p x :=
  WithTop.forall_ne_top
/-
**ENNReal.exists_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：exists_ne_top {p : Real>=0∞ -> Prop} : (exists x != ∞, p x) ↔ exists x : R
eal>=0, p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.exists_ne_top`：∀ {α : Type u_1} {p : WithTop α → Prop}, (∃ x, x 
≠ ⊤ ∧ p x) ↔ ∃ x, p ↑x
-/
theorem exists_ne_top {p : ℝ≥0∞ → Prop} : (∃ x ≠ ∞, p x) ↔ ∃ x : ℝ≥0, p x :=
  WithTop.exists_ne_top
/-
**ENNReal.toNNReal_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toNNReal_eq_zero_iff (x : Real>=0∞) : x.toNNReal = 0 ↔ x = 0 ∨ x = ∞
参数：x : Real>=0∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.untopD_eq_self_iff`：∀ {α : Type u_1} {d : α} {x : WithTop α}, Wi
thTop.untopD d x = d ↔ x = ↑d ∨ x = ⊤
-/
theorem toNNReal_eq_zero_iff (x : ℝ≥0∞) : x.toNNReal = 0 ↔ x = 0 ∨ x = ∞ :=
  WithTop.untopD_eq_self_iff
/-
**ENNReal.toReal_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toReal_eq_zero_iff (x : Real>=0∞) : x.toReal = 0 ↔ x = 0 ∨ x = ∞
参数：x : Real>=0∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toReal_eq_zero_iff (x : ℝ≥0∞) : x.toReal = 0 ↔ x = 0 ∨ x = ∞ := by
  simp [ENNReal.toReal, toNNReal_eq_zero_iff]
/-
**ENNReal.toNNReal_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toNNReal_ne_zero : a.toNNReal != 0 ↔ a != 0 ∧ a != ∞
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `ENNReal.toNNReal_eq_zero_iff`：toNNReal_eq_zero_iff (x : Real>=0∞) : x.to
NNReal = 0 ↔ x = 0 ∨ x = ∞
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
-/
theorem toNNReal_ne_zero : a.toNNReal ≠ 0 ↔ a ≠ 0 ∧ a ≠ ∞ :=
  a.toNNReal_eq_zero_iff.not.trans not_or
/-
**ENNReal.toReal_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toReal_ne_zero : a.toReal != 0 ↔ a != 0 ∧ a != ∞
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `ENNReal.toReal_eq_zero_iff`：toReal_eq_zero_iff (x : Real>=0∞) : x.toReal
 = 0 ↔ x = 0 ∨ x = ∞
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
-/
theorem toReal_ne_zero : a.toReal ≠ 0 ↔ a ≠ 0 ∧ a ≠ ∞ :=
  a.toReal_eq_zero_iff.not.trans not_or

set_option backward.isDefEq.respectTransparency false in
/-
**ENNReal.toNNReal_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toNNReal_eq_one_iff (x : Real>=0∞) : x.toNNReal = 1 ↔ x = 1
参数：x : Real>=0∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `WithTop.untopD_eq_iff`：∀ {α : Type u_1} {d y : α} {x : WithTop α}, WithT
op.untopD d x = y ↔ x = ↑y ∨ x = ⊤ ∧ y = d
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toNNReal_eq_one_iff (x : ℝ≥0∞) : x.toNNReal = 1 ↔ x = 1 :=
  WithTop.untopD_eq_iff.trans <| by simp
/-
**ENNReal.toReal_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toReal_eq_one_iff (x : Real>=0∞) : x.toReal = 1 ↔ x = 1
参数：x : Real>=0∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.toReal.eq_1`：∀ (a : ENNReal), a.toReal = ↑a.toNNReal
· 使用定理 `NNReal.coe_eq_one`：∀ {r : NNReal}, ↑r = 1 ↔ r = 1
· 使用定理 `ENNReal.toNNReal_eq_one_iff`：toNNReal_eq_one_iff (x : Real>=0∞) : x.toNN
Real = 1 ↔ x = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toReal_eq_one_iff (x : ℝ≥0∞) : x.toReal = 1 ↔ x = 1 := by
  rw [ENNReal.toReal, NNReal.coe_eq_one, ENNReal.toNNReal_eq_one_iff]
/-
**ENNReal.toNNReal_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toNNReal_ne_one : a.toNNReal != 1 ↔ a != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `ENNReal.toNNReal_eq_one_iff`：toNNReal_eq_one_iff (x : Real>=0∞) : x.toNN
Real = 1 ↔ x = 1
-/
theorem toNNReal_ne_one : a.toNNReal ≠ 1 ↔ a ≠ 1 :=
  a.toNNReal_eq_one_iff.not
/-
**ENNReal.toReal_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toReal_ne_one : a.toReal != 1 ↔ a != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `ENNReal.toReal_eq_one_iff`：toReal_eq_one_iff (x : Real>=0∞) : x.toReal =
 1 ↔ x = 1
-/
theorem toReal_ne_one : a.toReal ≠ 1 ↔ a ≠ 1 :=
  a.toReal_eq_one_iff.not

@[simp, aesop (rule_sets := [finiteness]) safe apply]
/-
**ENNReal.coe_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：coe_ne_top : (r : Real>=0∞) != ∞
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.coe_ne_top`：∀ {α : Type u_1} {a : α}, ↑a ≠ ⊤
-/
theorem coe_ne_top : (r : ℝ≥0∞) ≠ ∞ := WithTop.coe_ne_top
/-
**ENNReal.top_ne_coe** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {r : NNReal}, ⊤ ≠ ↑r
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.top_ne_coe`：∀ {α : Type u_1} {a : α}, ⊤ ≠ ↑a
-/
@[simp] theorem top_ne_coe : ∞ ≠ (r : ℝ≥0∞) := WithTop.top_ne_coe
/-
**ENNReal.coe_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {r : NNReal}, ↑r < ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.coe_lt_top`：∀ {α : Type u_1} [inst : LT α] (a : α), ↑a < ⊤
-/
@[simp] theorem coe_lt_top : (r : ℝ≥0∞) < ∞ := WithTop.coe_lt_top r

@[simp, aesop (rule_sets := [finiteness]) safe apply]
/-
**ENNReal.ofReal_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_ne_top {r : Real} : ENNReal.ofReal r != ∞
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
-/
theorem ofReal_ne_top {r : ℝ} : ENNReal.ofReal r ≠ ∞ := coe_ne_top
/-
**ENNReal.ofReal_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {r : ℝ}, ENNReal.ofReal r < ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
-/
@[simp] theorem ofReal_lt_top {r : ℝ} : ENNReal.ofReal r < ∞ := coe_lt_top
/-
**ENNReal.top_ne_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {r : ℝ}, ⊤ ≠ ENNReal.ofReal r
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.top_ne_coe`：∀ {r : NNReal}, ⊤ ≠ ↑r
-/
@[simp] theorem top_ne_ofReal {r : ℝ} : ∞ ≠ ENNReal.ofReal r := top_ne_coe

@[simp]
/-
**ENNReal.ofReal_toReal_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：ofReal_toReal_eq_iff : ENNReal.ofReal a.toReal = a ↔ a != ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofReal_ne_top`：ofReal_ne_top {r : Real} : ENNReal.ofReal r != ∞
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
-/
theorem ofReal_toReal_eq_iff : ENNReal.ofReal a.toReal = a ↔ a ≠ ⊤ :=
  ⟨fun h => by
    rw [← h]
    exact ofReal_ne_top, ofReal_toReal⟩

@[simp]
/-
**ENNReal.toReal_ofReal_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toReal_ofReal_eq_iff {a : Real} : (ENNReal.ofReal a).toReal = a ↔ 0 <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toReal_nonneg`：∀ {a : ENNReal}, 0 ≤ a.toReal
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
-/
theorem toReal_ofReal_eq_iff {a : ℝ} : (ENNReal.ofReal a).toReal = a ↔ 0 ≤ a :=
  ⟨fun h => by
    rw [← h]
    exact toReal_nonneg, toReal_ofReal⟩
/-
**ENNReal.zero_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：0 ≠ ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
-/
@[simp, aesop (rule_sets := [finiteness]) safe apply] theorem zero_ne_top : 0 ≠ ∞ := coe_ne_top
/-
**ENNReal.top_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：⊤ ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.top_ne_coe`：∀ {r : NNReal}, ⊤ ≠ ↑r
-/
@[simp] theorem top_ne_zero : ∞ ≠ 0 := top_ne_coe
/-
**ENNReal.one_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：1 ≠ ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
-/
@[simp, aesop (rule_sets := [finiteness]) safe apply] theorem one_ne_top : 1 ≠ ∞ := coe_ne_top
/-
**ENNReal.top_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：⊤ ≠ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.top_ne_coe`：∀ {r : NNReal}, ⊤ ≠ ↑r
-/
@[simp] theorem top_ne_one : ∞ ≠ 1 := top_ne_coe
/-
**ENNReal.zero_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：0 < ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
-/
@[simp] theorem zero_lt_top : 0 < ∞ := coe_lt_top
/-
**ENNReal.coe_le_coe** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.coe_le_coe`：∀ {α : Type u_1} {a b : α} [inst : LE α], ↑b ≤ ↑a ↔ 
b ≤ a
-/
@[simp, norm_cast, gcongr] theorem coe_le_coe : (↑r : ℝ≥0∞) ≤ ↑q ↔ r ≤ q := WithTop.coe_le_coe
/-
**ENNReal.coe_lt_coe** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {r q : NNReal}, ↑r < ↑q ↔ r < q
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.coe_lt_coe`：∀ {α : Type u_1} {a b : α} [inst : LT α], ↑b < ↑a ↔ 
b < a
-/
@[simp, norm_cast, gcongr] theorem coe_lt_coe : (↑r : ℝ≥0∞) < ↑q ↔ r < q := WithTop.coe_lt_coe

@[deprecated (since := "2026-08-04")] alias ⟨_, coe_le_coe_of_le⟩ := coe_le_coe

@[deprecated (since := "2026-08-04")] alias ⟨_, coe_lt_coe_of_lt⟩ := coe_lt_coe
/-
**ENNReal.coe_mono** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：coe_mono : Monotone ofNNReal
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
-/
theorem coe_mono : Monotone ofNNReal := fun _ _ => coe_le_coe.2
/-
**ENNReal.coe_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：coe_strictMono : StrictMono ofNNReal
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_lt_coe`：∀ {r q : NNReal}, ↑r < ↑q ↔ r < q
-/
theorem coe_strictMono : StrictMono ofNNReal := fun _ _ => coe_lt_coe.2
/-
**ENNReal.coe_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {r : NNReal}, ↑r = 0 ↔ r = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.coe_inj`：∀ {p q : NNReal}, ↑p = ↑q ↔ p = q
-/
@[simp, norm_cast] theorem coe_eq_zero : (↑r : ℝ≥0∞) = 0 ↔ r = 0 := coe_inj
/-
**ENNReal.zero_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {r : NNReal}, 0 = ↑r ↔ 0 = r
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.coe_inj`：∀ {p q : NNReal}, ↑p = ↑q ↔ p = q
-/
@[simp, norm_cast] theorem zero_eq_coe : 0 = (↑r : ℝ≥0∞) ↔ 0 = r := coe_inj
/-
**ENNReal.coe_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {r : NNReal}, ↑r = 1 ↔ r = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.coe_inj`：∀ {p q : NNReal}, ↑p = ↑q ↔ p = q
-/
@[simp, norm_cast] theorem coe_eq_one : (↑r : ℝ≥0∞) = 1 ↔ r = 1 := coe_inj
/-
**ENNReal.one_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {r : NNReal}, 1 = ↑r ↔ 1 = r
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.coe_inj`：∀ {p q : NNReal}, ↑p = ↑q ↔ p = q
-/
@[simp, norm_cast] theorem one_eq_coe : 1 = (↑r : ℝ≥0∞) ↔ 1 = r := coe_inj
/-
**ENNReal.coe_pos** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.coe_lt_coe`：∀ {r q : NNReal}, ↑r < ↑q ↔ r < q
-/
@[simp, norm_cast] theorem coe_pos : 0 < (r : ℝ≥0∞) ↔ 0 < r := coe_lt_coe
/-
**ENNReal.coe_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：coe_ne_zero : (r : Real>=0∞) != 0 ↔ r != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.coe_ne_zero`：∀ {α : Type u} [inst : Zero α] {a : α}, ↑a ≠ 0 ↔ a 
≠ 0
-/
theorem coe_ne_zero : (r : ℝ≥0∞) ≠ 0 ↔ r ≠ 0 := WithTop.coe_ne_zero
/-
**ENNReal.coe_ne_one** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：coe_ne_one : (r : Real>=0∞) != 1 ↔ r != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.coe_ne_one`：∀ {α : Type u} [inst : One α] {a : α}, ↑a ≠ 1 ↔ a ≠ 
1
-/
lemma coe_ne_one : (r : ℝ≥0∞) ≠ 1 ↔ r ≠ 1 := WithTop.coe_ne_one
/-
**ENNReal.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (x y : NNReal), ↑(x + y) = ↑x + ↑y
参数：x y : NNReal；x + y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_add (x y : ℝ≥0) : (↑(x + y) : ℝ≥0∞) = x + y := rfl
/-
**ENNReal.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (x y : NNReal), ↑(x * y) = ↑x * ↑y
参数：x y : NNReal；x * y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_mul (x y : ℝ≥0) : (↑(x * y) : ℝ≥0∞) = x * y := rfl
/-
**ENNReal.coe_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (n : ℕ) (x : NNReal), ↑(n • x) = n • ↑x
参数：n : ℕ；x : NNReal；n • x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[norm_cast] lemma coe_nsmul (n : ℕ) (x : ℝ≥0) : (↑(n • x) : ℝ≥0∞) = n • x := rfl
/-
**ENNReal.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (x : NNReal) (n : ℕ), ↑(x ^ n) = ↑x ^ n
参数：x : NNReal；n : ℕ；x ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_pow (x : ℝ≥0) (n : ℕ) : (↑(x ^ n) : ℝ≥0∞) = x ^ n := rfl

@[simp, norm_cast]
/-
**ENNReal.coe_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：coe_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Real>=0) : Real>=0∞) = o
fNat(n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ofNat (n : ℕ) [n.AtLeastTwo] : ((ofNat(n) : ℝ≥0) : ℝ≥0∞) = ofNat(n) := rfl

-- TODO: add lemmas about `OfNat.ofNat` and `<`/`≤`
/-
**ENNReal.coe_two** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：coe_two : ((2 : Real>=0) : Real>=0∞) = 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem coe_two : ((2 : ℝ≥0) : ℝ≥0∞) = 2 := rfl
/-
**ENNReal.toNNReal_eq_toNNReal_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toNNReal_eq_toNNReal_iff (x y : Real>=0∞) : x.toNNReal = y.toNNReal ↔ x = 
y ∨ x = 0 ∧ y = ⊤ ∨ x = ⊤ ∧ y = 0
参数：x y : Real>=0∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.untopD_eq_untopD_iff`：∀ {α : Type u_1} {d : α} {x y : WithTop α}
,   WithTop.untopD d x = WithTop.untopD d y ↔ x = y ∨ x = ↑d ∧ y = ⊤ ∨ x = ⊤ ∧ y
 = ↑d
-/
theorem toNNReal_eq_toNNReal_iff (x y : ℝ≥0∞) :
    x.toNNReal = y.toNNReal ↔ x = y ∨ x = 0 ∧ y = ⊤ ∨ x = ⊤ ∧ y = 0 :=
  WithTop.untopD_eq_untopD_iff
/-
**ENNReal.toReal_eq_toReal_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toReal_eq_toReal_iff (x y : Real>=0∞) : x.toReal = y.toReal ↔ x = y ∨ x = 
0 ∧ y = ⊤ ∨ x = ⊤ ∧ y = 0
参数：x y : Real>=0∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toReal_eq_toReal_iff (x y : ℝ≥0∞) :
    x.toReal = y.toReal ↔ x = y ∨ x = 0 ∧ y = ⊤ ∨ x = ⊤ ∧ y = 0 := by
  simp only [ENNReal.toReal, NNReal.coe_inj, toNNReal_eq_toNNReal_iff]
/-
**ENNReal.toNNReal_eq_toNNReal_iff'** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toNNReal_eq_toNNReal_iff' {x y : Real>=0∞} (hx : x != ⊤) (hy : y != ⊤) : x
.toNNReal = y.toNNReal ↔ x = y
参数：hx : x != ⊤；hy : y != ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.toNNReal_eq_toNNReal_iff`：toNNReal_eq_toNNReal_iff (x y : Real>=
0∞) : x.toNNReal = y.toNNReal ↔ x = y ∨ x = 0 ∧ y = ⊤ ∨ x = ⊤ ∧ y = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toNNReal_eq_toNNReal_iff' {x y : ℝ≥0∞} (hx : x ≠ ⊤) (hy : y ≠ ⊤) :
    x.toNNReal = y.toNNReal ↔ x = y := by
  simp only [ENNReal.toNNReal_eq_toNNReal_iff x y, hx, hy, and_false, false_and, or_false]
/-
**ENNReal.toReal_eq_toReal_iff'** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toReal_eq_toReal_iff' {x y : Real>=0∞} (hx : x != ⊤) (hy : y != ⊤) : x.toR
eal = y.toReal ↔ x = y
参数：hx : x != ⊤；hy : y != ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.toNNReal_eq_toNNReal_iff'`：toNNReal_eq_toNNReal_iff' {x y : Real
>=0∞} (hx : x != ⊤) (hy : y != ⊤) : x.toNNReal = y.toNNReal ↔ x = y
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toReal_eq_toReal_iff' {x y : ℝ≥0∞} (hx : x ≠ ⊤) (hy : y ≠ ⊤) :
    x.toReal = y.toReal ↔ x = y := by
  simp only [ENNReal.toReal, NNReal.coe_inj, toNNReal_eq_toNNReal_iff' hx hy]
/-
**ENNReal.one_lt_two** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：one_lt_two : (1 : Real>=0∞) < 2
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.one_lt_ofNat`：one_lt_ofNat : 1 < (ofNat(n) : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem one_lt_two : (1 : ℝ≥0∞) < 2 := Nat.one_lt_ofNat

/-- `(1 : ℝ≥0∞) ≤ 1`, recorded as a `Fact` for use with `Lp` spaces. -/
/-
**ENNReal._root_.fact_one_le_one_ennreal** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`(1 : ℝ≥0∞) ≤ 1`, recorded as a `Fact` for use with `Lp` spaces.
-/
instance _root_.fact_one_le_one_ennreal : Fact ((1 : ℝ≥0∞) ≤ 1) :=
  ⟨le_rfl⟩

/-- `(1 : ℝ≥0∞) ≤ 2`, recorded as a `Fact` for use with `Lp` spaces. -/
/-
**ENNReal._root_.fact_one_le_two_ennreal** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`(1 : ℝ≥0∞) ≤ 2`, recorded as a `Fact` for use with `Lp` spaces.
-/
instance _root_.fact_one_le_two_ennreal : Fact ((1 : ℝ≥0∞) ≤ 2) :=
  ⟨one_le_two⟩

/-- `(1 : ℝ≥0∞) ≤ ∞`, recorded as a `Fact` for use with `Lp` spaces. -/
/-
**ENNReal._root_.fact_one_le_top_ennreal** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`(1 : ℝ≥0∞) ≤ ∞`, recorded as a `Fact` for use with `Lp` spaces.
-/
instance _root_.fact_one_le_top_ennreal : Fact ((1 : ℝ≥0∞) ≤ ∞) :=
  ⟨le_top⟩

/-- The set of numbers in `ℝ≥0∞` that are not equal to `∞` is equivalent to `ℝ≥0`. -/
/-
**ENNReal.neTopEquivNNReal** 是 Mathlib 中的一个定义，位于命名空间 `ENNReal`。
形式化陈述：neTopEquivNNReal : { a | a != ∞ } ≃ Real>=0 where toFun x
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `ENNReal.toNNReal_coe`：∀ (r : NNReal), (↑r).toNNReal = r

--- 原说明 ---
The set of numbers in `ℝ≥0∞` that are not equal to `∞` is equivalent to `ℝ≥0`.
-/
def neTopEquivNNReal : { a | a ≠ ∞ } ≃ ℝ≥0 where
  toFun x := ENNReal.toNNReal x
  invFun x := ⟨x, coe_ne_top⟩
  left_inv := fun x => Subtype.ext <| coe_toNNReal x.2
  right_inv := toNNReal_coe
/-
**ENNReal.cinfi_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：cinfi_ne_top [InfSet α] (f : Real>=0∞ -> α) : ⨅ x : { x // x != ∞ }, f x =
 ⨅ x : Real>=0, f x
参数：f : Real>=0∞ -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Surjective.iInf_congr`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : So
rt u_5} [inst : InfSet α] {f : ι → α} {g : ι' → α} (h : ι → ι'),   Function.Surj
ective h → (∀ (x : ι…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
theorem cinfi_ne_top [InfSet α] (f : ℝ≥0∞ → α) : ⨅ x : { x // x ≠ ∞ }, f x = ⨅ x : ℝ≥0, f x :=
  Eq.symm <| neTopEquivNNReal.symm.surjective.iInf_congr _ fun _ => rfl
/-
**ENNReal.iInf_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：iInf_ne_top [CompleteLattice α] (f : Real>=0∞ -> α) : ⨅ (x) (_ : x != ∞), 
f x = ⨅ x : Real>=0, f x
参数：f : Real>=0∞ -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf_subtype'`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {p : ι → Prop} {f : (i : ι) → p i → α},   ⨅ i, ⨅ (h : p i), f i h = ⨅ x, f ↑x 
⋯
· 使用定理 `ENNReal.cinfi_ne_top`：cinfi_ne_top [InfSet α] (f : Real>=0∞ -> α) : ⨅ x 
: { x // x != ∞ }, f x = ⨅ x : Real>=0, f x
-/
theorem iInf_ne_top [CompleteLattice α] (f : ℝ≥0∞ → α) :
    ⨅ (x) (_ : x ≠ ∞), f x = ⨅ x : ℝ≥0, f x := by rw [iInf_subtype', cinfi_ne_top]
/-
**ENNReal.csupr_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：csupr_ne_top [SupSet α] (f : Real>=0∞ -> α) : ⨆ x : { x // x != ∞ }, f x =
 ⨆ x : Real>=0, f x
参数：f : Real>=0∞ -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.cinfi_ne_top`：cinfi_ne_top [InfSet α] (f : Real>=0∞ -> α) : ⨅ x 
: { x // x != ∞ }, f x = ⨅ x : Real>=0, f x
-/
theorem csupr_ne_top [SupSet α] (f : ℝ≥0∞ → α) : ⨆ x : { x // x ≠ ∞ }, f x = ⨆ x : ℝ≥0, f x :=
  @cinfi_ne_top αᵒᵈ _ _
/-
**ENNReal.iSup_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：iSup_ne_top [CompleteLattice α] (f : Real>=0∞ -> α) : ⨆ (x) (_ : x != ∞), 
f x = ⨆ x : Real>=0, f x
参数：f : Real>=0∞ -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.iInf_ne_top`：iInf_ne_top [CompleteLattice α] (f : Real>=0∞ -> α)
 : ⨅ (x) (_ : x != ∞), f x = ⨅ x : Real>=0, f x
-/
theorem iSup_ne_top [CompleteLattice α] (f : ℝ≥0∞ → α) :
    ⨆ (x) (_ : x ≠ ∞), f x = ⨆ x : ℝ≥0, f x :=
  @iInf_ne_top αᵒᵈ _ _
/-
**ENNReal.iInf_ennreal** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：iInf_ennreal {α : Type*} [CompleteLattice α] {f : Real>=0∞ -> α} : ⨅ n, f 
n = (⨅ n : Real>=0, f n) ⊓ f ∞
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iInf_option`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] 
(f : Option β → α), ⨅ o, f o = f none ⊓ ⨅ b, f (some b)
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
-/
theorem iInf_ennreal {α : Type*} [CompleteLattice α] {f : ℝ≥0∞ → α} :
    ⨅ n, f n = (⨅ n : ℝ≥0, f n) ⊓ f ∞ :=
  (iInf_option f).trans (inf_comm _ _)
/-
**ENNReal.iSup_ennreal** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：iSup_ennreal {α : Type*} [CompleteLattice α] {f : Real>=0∞ -> α} : ⨆ n, f 
n = (⨆ n : Real>=0, f n) ⊔ f ∞
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.iInf_ennreal`：iInf_ennreal {α : Type*} [CompleteLattice α] {f : 
Real>=0∞ -> α} : ⨅ n, f n = (⨅ n : Real>=0, f n) ⊓ f ∞
-/
theorem iSup_ennreal {α : Type*} [CompleteLattice α] {f : ℝ≥0∞ → α} :
    ⨆ n, f n = (⨆ n : ℝ≥0, f n) ⊔ f ∞ :=
  @iInf_ennreal αᵒᵈ _ _

/-- Coercion `ℝ≥0 → ℝ≥0∞` as a `RingHom`. -/
/-
**ENNReal.ofNNRealHom** 是 Mathlib 中的一个定义，位于命名空间 `ENNReal`。
形式化陈述：ofNNRealHom : Real>=0 ->+* Real>=0∞ where toFun
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.coe_one`：↑1 = 1
· 使用定理 `ENNReal.coe_mul`：∀ (x y : NNReal), ↑(x * y) = ↑x * ↑y
· 使用定理 `ENNReal.coe_zero`：↑0 = 0
· 使用定理 `ENNReal.coe_add`：∀ (x y : NNReal), ↑(x + y) = ↑x + ↑y

--- 原说明 ---
Coercion `ℝ≥0 → ℝ≥0∞` as a `RingHom`.
-/
noncomputable def ofNNRealHom : ℝ≥0 →+* ℝ≥0∞ where
  toFun := WithTop.some
  map_one' := coe_one
  map_mul' _ _ := coe_mul _ _
  map_zero' := coe_zero
  map_add' _ _ := coe_add _ _
/-
**ENNReal.coe_ofNNRealHom** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：⇑ENNReal.ofNNRealHom = WithTop.some
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_ofNNRealHom : ⇑ofNNRealHom = WithTop.some := rfl

section Order

/-
**ENNReal.bot_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：bot_eq_zero : (⊥ : Real>=0∞) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bot_eq_zero : (⊥ : ℝ≥0∞) = 0 := rfl

-- `coe_lt_top` moved up
/-
**ENNReal.not_top_le_coe** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：not_top_le_coe : ¬∞ <= ↑r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.not_top_le_coe`：∀ {α : Type u_1} [inst : LE α] (a : α), ¬⊤ ≤ ↑a
-/
theorem not_top_le_coe : ¬∞ ≤ ↑r := WithTop.not_top_le_coe r

@[simp, norm_cast]
/-
**ENNReal.one_le_coe_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：one_le_coe_iff : (1 : Real>=0∞) <= ↑r ↔ 1 <= r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
-/
theorem one_le_coe_iff : (1 : ℝ≥0∞) ≤ ↑r ↔ 1 ≤ r := coe_le_coe

@[simp, norm_cast]
/-
**ENNReal.coe_le_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：coe_le_one_iff : ↑r <= (1 : Real>=0∞) ↔ r <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
-/
theorem coe_le_one_iff : ↑r ≤ (1 : ℝ≥0∞) ↔ r ≤ 1 := coe_le_coe

@[simp, norm_cast]
/-
**ENNReal.coe_lt_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：coe_lt_one_iff : (↑p : Real>=0∞) < 1 ↔ p < 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.coe_lt_coe`：∀ {r q : NNReal}, ↑r < ↑q ↔ r < q
-/
theorem coe_lt_one_iff : (↑p : ℝ≥0∞) < 1 ↔ p < 1 := coe_lt_coe

@[simp, norm_cast]
/-
**ENNReal.one_lt_coe_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：one_lt_coe_iff : 1 < (↑p : Real>=0∞) ↔ 1 < p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.coe_lt_coe`：∀ {r q : NNReal}, ↑r < ↑q ↔ r < q
-/
theorem one_lt_coe_iff : 1 < (↑p : ℝ≥0∞) ↔ 1 < p := coe_lt_coe

@[simp, norm_cast]
/-
**ENNReal.coe_natCast** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：coe_natCast (n : Nat) : ((n : Real>=0) : Real>=0∞) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_natCast (n : ℕ) : ((n : ℝ≥0) : ℝ≥0∞) = n := rfl
/-
**ENNReal.ofReal_natCast** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (n : ℕ), ENNReal.ofReal ↑n = ↑n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.toNNReal_natCast`：∀ (n : ℕ), (↑n).toNNReal = ↑n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp, norm_cast] lemma ofReal_natCast (n : ℕ) : ENNReal.ofReal n = n := by simp [ENNReal.ofReal]
/-
**ENNReal.ofReal_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (n : ℕ) [inst : n.AtLeastTwo], ENNReal.ofReal (OfNat.ofNat n) = OfNat.of
Nat n
参数：n : ℕ；OfNat.ofNat n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.ofReal_natCast`：∀ (n : ℕ), ENNReal.ofReal ↑n = ↑n
-/
@[simp] theorem ofReal_ofNat (n : ℕ) [n.AtLeastTwo] : ENNReal.ofReal ofNat(n) = ofNat(n) :=
  ofReal_natCast n

@[simp, aesop (rule_sets := [finiteness]) safe apply]
/-
**ENNReal.natCast_ne_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：natCast_ne_top (n : Nat) : (n : Real>=0∞) != ∞
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.natCast_ne_top`：∀ {α : Type u} [inst : AddMonoidWithOne α] (n : 
ℕ), ↑n ≠ ⊤
-/
theorem natCast_ne_top (n : ℕ) : (n : ℝ≥0∞) ≠ ∞ := WithTop.natCast_ne_top n
/-
**ENNReal.natCast_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (n : ℕ), ↑n < ⊤
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.natCast_lt_top`：∀ {α : Type u} [inst : AddMonoidWithOne α] [inst
_1 : LT α] (n : ℕ), ↑n < ⊤
-/
@[simp] theorem natCast_lt_top (n : ℕ) : (n : ℝ≥0∞) < ∞ := WithTop.natCast_lt_top n

@[simp, aesop (rule_sets := [finiteness]) safe apply]
/-
**ENNReal.ofNat_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：ofNat_ne_top {n : Nat} [Nat.AtLeastTwo n] : ofNat(n) != ∞
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.natCast_ne_top`：natCast_ne_top (n : Nat) : (n : Real>=0∞) != ∞
-/
lemma ofNat_ne_top {n : ℕ} [Nat.AtLeastTwo n] : ofNat(n) ≠ ∞ := natCast_ne_top n

@[simp]
/-
**ENNReal.ofNat_lt_top** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：ofNat_lt_top {n : Nat} [Nat.AtLeastTwo n] : ofNat(n) < ∞
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.natCast_lt_top`：∀ (n : ℕ), ↑n < ⊤
-/
lemma ofNat_lt_top {n : ℕ} [Nat.AtLeastTwo n] : ofNat(n) < ∞ := natCast_lt_top n
/-
**ENNReal.top_ne_natCast** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (n : ℕ), ⊤ ≠ ↑n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.top_ne_natCast`：∀ {α : Type u} [inst : AddMonoidWithOne α] (n : 
ℕ), ⊤ ≠ ↑n
-/
@[simp] theorem top_ne_natCast (n : ℕ) : ∞ ≠ n := WithTop.top_ne_natCast n
/-
**ENNReal.top_ne_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {n : ℕ} [inst : n.AtLeastTwo], ⊤ ≠ OfNat.ofNat n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `ENNReal.ofNat_ne_top`：ofNat_ne_top {n : Nat} [Nat.AtLeastTwo n] : ofNat(
n) != ∞
-/
@[simp] theorem top_ne_ofNat {n : ℕ} [n.AtLeastTwo] : ∞ ≠ ofNat(n) :=
  ofNat_ne_top.symm
/-
**ENNReal.natCast_le_ofNNReal** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {r : NNReal} {n : ℕ}, ↑n ≤ ↑r ↔ ↑n ≤ r
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp, norm_cast] lemma natCast_le_ofNNReal : (n : ℝ≥0∞) ≤ r ↔ n ≤ r := by simp [← coe_le_coe]
/-
**ENNReal.ofNNReal_le_natCast** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {r : NNReal} {n : ℕ}, ↑r ≤ ↑n ↔ r ≤ ↑n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp, norm_cast] lemma ofNNReal_le_natCast : r ≤ (n : ℝ≥0∞) ↔ r ≤ n := by simp [← coe_le_coe]
/-
**ENNReal.ofNNReal_add_natCast** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (r : NNReal) (n : ℕ), ↑(r + ↑n) = ↑r + ↑n
参数：r : NNReal；n : ℕ；r + ↑n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma ofNNReal_add_natCast (r : ℝ≥0) (n : ℕ) : ofNNReal (r + n) = r + n := rfl
/-
**ENNReal.ofNNReal_natCast_add** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (n : ℕ) (r : NNReal), ↑(↑n + r) = ↑n + ↑r
参数：n : ℕ；r : NNReal；↑n + r。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma ofNNReal_natCast_add (n : ℕ) (r : ℝ≥0) : ofNNReal (n + r) = n + r := rfl
/-
**ENNReal.ofNNReal_sub_natCast** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (r : NNReal) (n : ℕ), ↑(r - ↑n) = ↑r - ↑n
参数：r : NNReal；n : ℕ；r - ↑n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma ofNNReal_sub_natCast (r : ℝ≥0) (n : ℕ) : ofNNReal (r - n) = r - n := rfl
/-
**ENNReal.ofNNReal_natCast_sub** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (n : ℕ) (r : NNReal), ↑(↑n - r) = ↑n - ↑r
参数：n : ℕ；r : NNReal；↑n - r。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma ofNNReal_natCast_sub (n : ℕ) (r : ℝ≥0) : ofNNReal (n - r) = n - r := rfl
/-
**ENNReal.one_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：1 < ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
-/
@[simp] theorem one_lt_top : 1 < ∞ := coe_lt_top

@[simp, norm_cast]
/-
**ENNReal.toNNReal_natCast** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toNNReal_natCast (n : Nat) : (n : Real>=0∞).toNNReal = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_natCast`：coe_natCast (n : Nat) : ((n : Real>=0) : Real>=0∞) 
= n
· 使用定理 `ENNReal.toNNReal_coe`：∀ (r : NNReal), (↑r).toNNReal = r
-/
theorem toNNReal_natCast (n : ℕ) : (n : ℝ≥0∞).toNNReal = n := by
  rw [← ENNReal.coe_natCast n, ENNReal.toNNReal_coe]
/-
**ENNReal.toNNReal_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toNNReal_ofNat (n : Nat) [n.AtLeastTwo] : ENNReal.toNNReal ofNat(n) = ofNa
t(n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.toNNReal_natCast`：toNNReal_natCast (n : Nat) : (n : Real>=0∞).to
NNReal = n
-/
theorem toNNReal_ofNat (n : ℕ) [n.AtLeastTwo] : ENNReal.toNNReal ofNat(n) = ofNat(n) :=
  toNNReal_natCast n

@[simp, norm_cast]
/-
**ENNReal.toReal_natCast** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toReal_natCast (n : Nat) : (n : Real>=0∞).toReal = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofReal_natCast`：∀ (n : ℕ), ENNReal.ofReal ↑n = ↑n
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
-/
theorem toReal_natCast (n : ℕ) : (n : ℝ≥0∞).toReal = n := by
  rw [← ENNReal.ofReal_natCast n, ENNReal.toReal_ofReal (Nat.cast_nonneg _)]
/-
**ENNReal.toReal_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ (n : ℕ) [inst : n.AtLeastTwo], (OfNat.ofNat n).toReal = OfNat.ofNat n
参数：n : ℕ；OfNat.ofNat n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.toReal_natCast`：toReal_natCast (n : Nat) : (n : Real>=0∞).toReal
 = n
-/
@[simp] theorem toReal_ofNat (n : ℕ) [n.AtLeastTwo] : ENNReal.toReal ofNat(n) = ofNat(n) :=
  toReal_natCast n
/-
**ENNReal.toNNReal_natCast_eq_toNNReal** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：toNNReal_natCast_eq_toNNReal (n : Nat) : (n : Real>=0∞).toNNReal = (n : Re
al).toNNReal
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.toNNReal_of_nonneg`：∀ {r : ℝ} (hr : 0 ≤ r), r.toNNReal = NNReal.mk 
r hr
· 使用定理 `ENNReal.toNNReal_natCast`：toNNReal_natCast (n : Nat) : (n : Real>=0∞).to
NNReal = n
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `NNReal.mk_natCast`：mk_natCast (n : Nat) : NNReal.mk (n : Real) (n.cast_n
onneg) = n
-/
lemma toNNReal_natCast_eq_toNNReal (n : ℕ) :
    (n : ℝ≥0∞).toNNReal = (n : ℝ).toNNReal := by
  rw [Real.toNNReal_of_nonneg (by positivity), ENNReal.toNNReal_natCast, mk_natCast]
/-
**ENNReal.le_coe_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：le_coe_iff : a <= ↑r ↔ exists p : Real>=0, a = p ∧ p <= r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.le_coe_iff`：∀ {α : Type u_1} {a : α} [inst : LE α] {x : WithTop 
α}, x ≤ ↑a ↔ ∃ b, x = ↑b ∧ b ≤ a
-/
theorem le_coe_iff : a ≤ ↑r ↔ ∃ p : ℝ≥0, a = p ∧ p ≤ r := WithTop.le_coe_iff
/-
**ENNReal.coe_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：coe_le_iff : ↑r <= a ↔ forall p : Real>=0, a = p -> r <= p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.coe_le_iff`：∀ {α : Type u_1} {b : α} [inst : LE α] {x : WithTop 
α}, ↑b ≤ x ↔ ∀ (a : α), x = ↑a → b ≤ a
-/
theorem coe_le_iff : ↑r ≤ a ↔ ∀ p : ℝ≥0, a = p → r ≤ p := WithTop.coe_le_iff
/-
**ENNReal.lt_iff_exists_coe** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：lt_iff_exists_coe : a < b ↔ exists p : Real>=0, a = p ∧ ↑p < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.lt_iff_exists_coe`：∀ {α : Type u_1} [inst : LT α] {x y : WithTop
 α}, y < x ↔ ∃ b, y = ↑b ∧ ↑b < x
-/
theorem lt_iff_exists_coe : a < b ↔ ∃ p : ℝ≥0, a = p ∧ ↑p < b :=
  WithTop.lt_iff_exists_coe
/-
**ENNReal.toReal_le_coe_of_le_coe** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：toReal_le_coe_of_le_coe {a : Real>=0∞} {b : Real>=0} (h : a <= b) : a.toRe
al <= b
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
-/
theorem toReal_le_coe_of_le_coe {a : ℝ≥0∞} {b : ℝ≥0} (h : a ≤ b) : a.toReal ≤ b := by
  lift a to ℝ≥0 using ne_top_of_le_ne_top coe_ne_top h
  simpa using h

@[deprecated max_eq_zero (since := "2026-05-07")]
/-
**ENNReal.max_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：max_eq_zero_iff : max a b = 0 ↔ a = 0 ∧ b = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `max_eq_bot`：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : OrderBot α
] {a b : α}, max a b = ⊥ ↔ a = ⊥ ∧ b = ⊥
-/
theorem max_eq_zero_iff : max a b = 0 ↔ a = 0 ∧ b = 0 := max_eq_bot

@[deprecated min_eq_zero (since := "2026-05-07")]
/-
**ENNReal.min_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：min_eq_zero_iff : min a b = 0 ↔ a = 0 ∨ b = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `min_eq_bot`：min_eq_bot {a b : α} : min a b = ⊥ ↔ a = ⊥ ∨ b = ⊥
-/
theorem min_eq_zero_iff : min a b = 0 ↔ a = 0 ∨ b = 0 := min_eq_bot

@[deprecated zero_max (since := "2026-05-07")]
/-
**ENNReal.max_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：max_zero_left : max 0 a = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
theorem max_zero_left : max 0 a = a :=
  max_eq_right zero_le

@[deprecated max_zero (since := "2026-05-07")]
/-
**ENNReal.max_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：max_zero_right : max a 0 = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
theorem max_zero_right : max a 0 = a :=
  max_eq_left zero_le
/-
**ENNReal.lt_iff_exists_rat_btwn** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：lt_iff_exists_rat_btwn : a < b ↔ exists q : Rat, 0 <= q ∧ a < Real.toNNRea
l q ∧ (Real.toNNReal q : Real>=0∞) < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.lt_iff_exists_coe`：lt_iff_exists_coe : a < b ↔ exists p : Real>=
0, a = p ∧ ↑p < b
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `ENNReal.instDenselyOrdered`：DenselyOrdered ENNReal
· 使用定理 `NNReal.lt_iff_exists_rat_btwn`：lt_iff_exists_rat_btwn (a b : Real>=0) : 
a < b ↔ exists q : Rat, 0 <= q ∧ a < Real.toNNReal q ∧ Real.toNNReal q < b
· 使用定理 `ENNReal.coe_lt_coe`：∀ {r q : NNReal}, ↑r < ↑q ↔ r < q
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem lt_iff_exists_rat_btwn :
    a < b ↔ ∃ q : ℚ, 0 ≤ q ∧ a < Real.toNNReal q ∧ (Real.toNNReal q : ℝ≥0∞) < b :=
  ⟨fun h => by
    rcases lt_iff_exists_coe.1 h with ⟨p, rfl, _⟩
    rcases exists_between h with ⟨c, pc, cb⟩
    rcases lt_iff_exists_coe.1 cb with ⟨r, rfl, _⟩
    rcases (NNReal.lt_iff_exists_rat_btwn _ _).1 (coe_lt_coe.1 pc) with ⟨q, hq0, pq, qr⟩
    exact ⟨q, hq0, coe_lt_coe.2 pq, lt_trans (coe_lt_coe.2 qr) cb⟩,
      fun ⟨_, _, qa, qb⟩ => lt_trans qa qb⟩
/-
**ENNReal.lt_iff_exists_real_btwn** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：lt_iff_exists_real_btwn : a < b ↔ exists r : Real, 0 <= r ∧ a < ENNReal.of
Real r ∧ (ENNReal.ofReal r : Real>=0∞) < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.lt_iff_exists_rat_btwn`：lt_iff_exists_rat_btwn : a < b ↔ exists 
q : Rat, 0 <= q ∧ a < Real.toNNReal q ∧ (Real.toNNReal q : Real>=0∞) < b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Rat.cast_nonneg`：∀ {q : ℚ} {K : Type u_5} [inst : Field K] [inst_1 : Lin
earOrder K] [IsStrictOrderedRing K], 0 ≤ ↑q ↔ 0 ≤ q
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
-/
theorem lt_iff_exists_real_btwn :
    a < b ↔ ∃ r : ℝ, 0 ≤ r ∧ a < ENNReal.ofReal r ∧ (ENNReal.ofReal r : ℝ≥0∞) < b :=
  ⟨fun h =>
    let ⟨q, q0, aq, qb⟩ := ENNReal.lt_iff_exists_rat_btwn.1 h
    ⟨q, Rat.cast_nonneg.2 q0, aq, qb⟩,
    fun ⟨_, _, qa, qb⟩ => lt_trans qa qb⟩
/-
**ENNReal.lt_iff_exists_nnreal_btwn** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：lt_iff_exists_nnreal_btwn : a < b ↔ exists r : Real>=0, a < r ∧ (r : Real>
=0∞) < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.lt_iff_exists_coe_btwn`：∀ {α : Type u_1} [inst : Preorder α] [De
nselyOrdered α] [NoMaxOrder α] {a b : WithTop α}, b < a ↔ ∃ x, b < ↑x ∧ ↑x < a
· 使用定理 `NNReal.instDenselyOrdered`：DenselyOrdered NNReal
· 使用定理 `IsStrictOrderedRing.toNoMaxOrder`：∀ {R : Type u} [inst : Semiring R] [in
st_1 : PartialOrder R] [IsStrictOrderedRing R], NoMaxOrder R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
-/
theorem lt_iff_exists_nnreal_btwn : a < b ↔ ∃ r : ℝ≥0, a < r ∧ (r : ℝ≥0∞) < b :=
  WithTop.lt_iff_exists_coe_btwn
/-
**ENNReal.lt_iff_exists_add_pos_lt** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：lt_iff_exists_add_pos_lt : a < b ↔ exists r : Real>=0, 0 < r ∧ a + r < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.lt_iff_exists_nnreal_btwn`：lt_iff_exists_nnreal_btwn : a < b ↔ e
xists r : Real>=0, a < r ∧ (r : Real>=0∞) < b
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LT.lt.ne_top`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderTop α] {
a b : α}, a < b → a ≠ ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tsub_pos_iff_lt`：tsub_pos_iff_lt : 0 < a - b ↔ b < a
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `NNReal.instOrderedSub`：OrderedSub NNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.coe_lt_coe`：∀ {r q : NNReal}, ↑r < ↑q ↔ r < q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_add`：∀ (x y : NNReal), ↑(x + y) = ↑x + ↑y
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
theorem lt_iff_exists_add_pos_lt : a < b ↔ ∃ r : ℝ≥0, 0 < r ∧ a + r < b := by
  refine ⟨fun hab => ?_, fun ⟨r, _, hr⟩ => lt_of_le_of_lt le_self_add hr⟩
  rcases lt_iff_exists_nnreal_btwn.1 hab with ⟨c, ac, cb⟩
  lift a to ℝ≥0 using ac.ne_top
  rw [coe_lt_coe] at ac
  refine ⟨c - a, tsub_pos_iff_lt.2 ac, ?_⟩
  rwa [← coe_add, add_tsub_cancel_of_le ac.le]
/-
**ENNReal.le_of_forall_pos_le_add** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：le_of_forall_pos_le_add (h : forall ε : Real>=0, 0 < ε -> b < ∞ -> a <= b 
+ ε) : a <= b
参数：h : forall ε : Real>=0, 0 < ε -> b < ∞ -> a <= b + ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.lt_iff_exists_add_pos_lt`：lt_iff_exists_add_pos_lt : a < b ↔ exi
sts r : Real>=0, 0 < r ∧ a + r < b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem le_of_forall_pos_le_add (h : ∀ ε : ℝ≥0, 0 < ε → b < ∞ → a ≤ b + ε) : a ≤ b := by
  contrapose! h
  rcases lt_iff_exists_add_pos_lt.1 h with ⟨r, hr0, hr⟩
  exact ⟨r, hr0, h.trans_le le_top, hr⟩
/-
**ENNReal.natCast_lt_coe** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：natCast_lt_coe {n : Nat} : n < (r : Real>=0∞) ↔ n < r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.coe_lt_coe`：∀ {r q : NNReal}, ↑r < ↑q ↔ r < q
· 使用定理 `ENNReal.coe_natCast`：coe_natCast (n : Nat) : ((n : Real>=0) : Real>=0∞) 
= n
-/
theorem natCast_lt_coe {n : ℕ} : n < (r : ℝ≥0∞) ↔ n < r := ENNReal.coe_natCast n ▸ coe_lt_coe
/-
**ENNReal.coe_lt_natCast** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：coe_lt_natCast {n : Nat} : (r : Real>=0∞) < n ↔ r < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.coe_lt_coe`：∀ {r q : NNReal}, ↑r < ↑q ↔ r < q
· 使用定理 `ENNReal.coe_natCast`：coe_natCast (n : Nat) : ((n : Real>=0) : Real>=0∞) 
= n
-/
theorem coe_lt_natCast {n : ℕ} : (r : ℝ≥0∞) < n ↔ r < n := ENNReal.coe_natCast n ▸ coe_lt_coe
/-
**ENNReal.exists_nat_gt** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：∀ {r : ENNReal}, r ≠ ⊤ → ∃ n, r < ↑n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `exists_nat_gt`：exists_nat_gt (x : R) : exists n : Nat, x < n
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `NNReal.instArchimedean`：Archimedean NNReal
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_lt_natCast`：coe_lt_natCast {n : Nat} : (r : Real>=0∞) < n ↔ 
r < n
-/
protected theorem exists_nat_gt {r : ℝ≥0∞} (h : r ≠ ∞) : ∃ n : ℕ, r < n := by
  lift r to ℝ≥0 using h
  rcases exists_nat_gt r with ⟨n, hn⟩
  exact ⟨n, coe_lt_natCast.2 hn⟩

@[simp]
/-
**ENNReal.iUnion_Iio_coe_nat** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：iUnion_Iio_coe_nat : ⋃ n : Nat, Iio (n : Real>=0∞) = {∞}ᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `ne_top_of_lt`：ne_top_of_lt (h : a < b) : a != ⊤
· 使用定理 `ENNReal.exists_nat_gt`：∀ {r : ENNReal}, r ≠ ⊤ → ∃ n, r < ↑n
-/
theorem iUnion_Iio_coe_nat : ⋃ n : ℕ, Iio (n : ℝ≥0∞) = {∞}ᶜ := by
  ext x
  rw [mem_iUnion]
  exact ⟨fun ⟨n, hn⟩ => ne_top_of_lt hn, ENNReal.exists_nat_gt⟩

@[simp]
/-
**ENNReal.iUnion_Iic_coe_nat** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：iUnion_Iic_coe_nat : ⋃ n : Nat, Iic (n : Real>=0∞) = {∞}ᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.iUnion_subset`：iUnion_subset {s : ι -> Set α} {t : Set α} (h : foral
l i, s i subseteq t) : ⋃ i, s i subseteq t
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `ENNReal.natCast_ne_top`：natCast_ne_top (n : Nat) : (n : Real>=0∞) != ∞
· 使用定理 `Set.iUnion_mono`：iUnion_mono {s t : ι -> Set α} (h : forall i, s i subse
teq t i) : ⋃ i, s i subseteq ⋃ i, t i
· 使用定理 `Set.Iio_subset_Iic_self`：Iio_subset_Iic_self : Iio a subseteq Iic a
· 使用定理 `ENNReal.iUnion_Iio_coe_nat`：iUnion_Iio_coe_nat : ⋃ n : Nat, Iio (n : Rea
l>=0∞) = {∞}ᶜ
-/
theorem iUnion_Iic_coe_nat : ⋃ n : ℕ, Iic (n : ℝ≥0∞) = {∞}ᶜ :=
  Subset.antisymm (iUnion_subset fun n _x hx => ne_top_of_le_ne_top (natCast_ne_top n) hx) <|
    iUnion_Iio_coe_nat ▸ iUnion_mono fun _ => Iio_subset_Iic_self

@[simp]
/-
**ENNReal.iUnion_Ioc_coe_nat** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：iUnion_Ioc_coe_nat : ⋃ n : Nat, Ioc a n = Ioi a \ {∞}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.iUnion_Iic_coe_nat`：iUnion_Iic_coe_nat : ⋃ n : Nat, Iic (n : Rea
l>=0∞) = {∞}ᶜ
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iUnion_Ioc_coe_nat : ⋃ n : ℕ, Ioc a n = Ioi a \ {∞} := by
  simp only [← Ioi_inter_Iic, ← inter_iUnion, iUnion_Iic_coe_nat, sdiff_eq]

@[simp]
/-
**ENNReal.iUnion_Ioo_coe_nat** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：iUnion_Ioo_coe_nat : ⋃ n : Nat, Ioo a n = Ioi a \ {∞}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.iUnion_Iio_coe_nat`：iUnion_Iio_coe_nat : ⋃ n : Nat, Iio (n : Rea
l>=0∞) = {∞}ᶜ
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iUnion_Ioo_coe_nat : ⋃ n : ℕ, Ioo a n = Ioi a \ {∞} := by
  simp only [← Ioi_inter_Iio, ← inter_iUnion, iUnion_Iio_coe_nat, sdiff_eq]

@[simp]
/-
**ENNReal.iUnion_Icc_coe_nat** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：iUnion_Icc_coe_nat : ⋃ n : Nat, Icc a n = Ici a \ {∞}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.iUnion_Iic_coe_nat`：iUnion_Iic_coe_nat : ⋃ n : Nat, Iic (n : Rea
l>=0∞) = {∞}ᶜ
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iUnion_Icc_coe_nat : ⋃ n : ℕ, Icc a n = Ici a \ {∞} := by
  simp only [← Ici_inter_Iic, ← inter_iUnion, iUnion_Iic_coe_nat, sdiff_eq]

@[simp]
/-
**ENNReal.iUnion_Ico_coe_nat** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：iUnion_Ico_coe_nat : ⋃ n : Nat, Ico a n = Ici a \ {∞}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.iUnion_Iio_coe_nat`：iUnion_Iio_coe_nat : ⋃ n : Nat, Iio (n : Rea
l>=0∞) = {∞}ᶜ
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iUnion_Ico_coe_nat : ⋃ n : ℕ, Ico a n = Ici a \ {∞} := by
  simp only [← Ici_inter_Iio, ← inter_iUnion, iUnion_Iio_coe_nat, sdiff_eq]

@[simp]
/-
**ENNReal.iInter_Ici_coe_nat** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：iInter_Ici_coe_nat : ⋂ n : Nat, Ici (n : Real>=0∞) = {∞}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.iUnion_Iio_coe_nat`：iUnion_Iio_coe_nat : ⋃ n : Nat, Iio (n : Rea
l>=0∞) = {∞}ᶜ
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iInter_Ici_coe_nat : ⋂ n : ℕ, Ici (n : ℝ≥0∞) = {∞} := by
  simp only [← compl_Iio, ← compl_iUnion, iUnion_Iio_coe_nat, compl_compl]

@[simp]
/-
**ENNReal.iInter_Ioi_coe_nat** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：iInter_Ioi_coe_nat : ⋂ n : Nat, Ioi (n : Real>=0∞) = {∞}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.iUnion_Iic_coe_nat`：iUnion_Iic_coe_nat : ⋃ n : Nat, Iic (n : Rea
l>=0∞) = {∞}ᶜ
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iInter_Ioi_coe_nat : ⋂ n : ℕ, Ioi (n : ℝ≥0∞) = {∞} := by
  simp only [← compl_Iic, ← compl_iUnion, iUnion_Iic_coe_nat, compl_compl]

@[simp, norm_cast]
/-
**ENNReal.coe_min** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：coe_min (r p : Real>=0) : ((min r p : Real>=0) : Real>=0∞) = min (r : Real
>=0∞) p
参数：r p : Real>=0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_min (r p : ℝ≥0) : ((min r p : ℝ≥0) : ℝ≥0∞) = min (r : ℝ≥0∞) p := rfl

@[simp, norm_cast]
/-
**ENNReal.coe_max** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：coe_max (r p : Real>=0) : ((max r p : Real>=0) : Real>=0∞) = max (r : Real
>=0∞) p
参数：r p : Real>=0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_max (r p : ℝ≥0) : ((max r p : ℝ≥0) : ℝ≥0∞) = max (r : ℝ≥0∞) p := rfl
/-
**ENNReal.le_of_top_imp_top_of_toNNReal_le** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：le_of_top_imp_top_of_toNNReal_le {a b : Real>=0∞} (h : a = ⊤ -> b = ⊤) (h_
nnreal : a != ⊤ -> b != ⊤ -> a.toNNReal <= b.toNNReal) : a <= b
参数：h : a = ⊤ -> b = ⊤；h_nnreal : a != ⊤ -> b != ⊤ -> a.toNNReal <= b.toNNReal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LT.lt.ne_top`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderTop α] {
a b : α}, a < b → a ≠ ⊤
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem le_of_top_imp_top_of_toNNReal_le {a b : ℝ≥0∞} (h : a = ⊤ → b = ⊤)
    (h_nnreal : a ≠ ⊤ → b ≠ ⊤ → a.toNNReal ≤ b.toNNReal) : a ≤ b := by
  by_contra! hlt
  lift b to ℝ≥0 using hlt.ne_top
  lift a to ℝ≥0 using mt h coe_ne_top
  refine hlt.not_ge ?_
  simpa using h_nnreal

@[simp]
/-
**ENNReal.abs_toReal** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：abs_toReal {x : Real>=0∞} : |x.toReal| = x.toReal
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.abs_eq`：abs_eq (x : Real>=0) : |(x : Real)| = x
-/
theorem abs_toReal {x : ℝ≥0∞} : |x.toReal| = x.toReal := by cases x <;> simp

end Order

section CompleteLattice
variable {ι : Sort*} {f : ι → ℝ≥0}

/-
**ENNReal.coe_sSup** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：coe_sSup {s : Set Real>=0} : BddAbove s -> (↑(sSup s) : Real>=0∞) = ⨆ a in
 s, ↑a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.coe_sSup`：coe_sSup {s : Set α} (hb : BddAbove s) : ↑(sSup s) = (
⨆ a in s, ↑a : WithTop α)
-/
theorem coe_sSup {s : Set ℝ≥0} : BddAbove s → (↑(sSup s) : ℝ≥0∞) = ⨆ a ∈ s, ↑a :=
  WithTop.coe_sSup
/-
**ENNReal.coe_sInf** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：coe_sInf {s : Set Real>=0} (hs : s.Nonempty) : (↑(sInf s) : Real>=0∞) = ⨅ 
a in s, ↑a
参数：hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.coe_sInf`：coe_sInf {s : Set α} (hs : s.Nonempty) (h's : BddBelow
 s) : ↑(sInf s) = (⨅ a in s, ↑a : WithTop α)
· 使用定理 `OrderBot.bddBelow`：∀ {α : Type u_1} [inst : Preorder α] [OrderBot α] (s 
: Set α), BddBelow s
-/
theorem coe_sInf {s : Set ℝ≥0} (hs : s.Nonempty) : (↑(sInf s) : ℝ≥0∞) = ⨅ a ∈ s, ↑a :=
  WithTop.coe_sInf hs (OrderBot.bddBelow s)
/-
**ENNReal.coe_iSup** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：coe_iSup {ι : Sort*} {f : ι -> Real>=0} (hf : BddAbove (range f)) : (↑(iSu
p f) : Real>=0∞) = ⨆ a, ↑(f a)
参数：hf : BddAbove (range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.coe_iSup`：WithTop.coe_iSup [SupSet α] (f : ι -> α) (h : BddAbove
 (Set.range f)) : ↑(⨆ i, f i) = (⨆ i, f i : WithTop α)
-/
theorem coe_iSup {ι : Sort*} {f : ι → ℝ≥0} (hf : BddAbove (range f)) :
    (↑(iSup f) : ℝ≥0∞) = ⨆ a, ↑(f a) :=
  WithTop.coe_iSup _ hf

@[norm_cast]
/-
**ENNReal.coe_iInf** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：coe_iInf {ι : Sort*} [Nonempty ι] (f : ι -> Real>=0) : (↑(iInf f) : Real>=
0∞) = ⨅ a, ↑(f a)
参数：f : ι -> Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.coe_iInf`：WithTop.coe_iInf [Nonempty ι] [InfSet α] {f : ι -> α} 
(hf : BddBelow (range f)) : ↑(⨅ i, f i) = (⨅ i, f i : WithTop α)
· 使用定理 `OrderBot.bddBelow`：∀ {α : Type u_1} [inst : Preorder α] [OrderBot α] (s 
: Set α), BddBelow s
-/
theorem coe_iInf {ι : Sort*} [Nonempty ι] (f : ι → ℝ≥0) : (↑(iInf f) : ℝ≥0∞) = ⨅ a, ↑(f a) :=
  WithTop.coe_iInf (OrderBot.bddBelow _)
/-
**ENNReal.coe_mem_upperBounds** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal`。
形式化陈述：coe_mem_upperBounds {s : Set Real>=0} : ↑r in upperBounds (ofNNReal '' s) 
↔ r in upperBounds s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coe_mem_upperBounds {s : Set ℝ≥0} :
    ↑r ∈ upperBounds (ofNNReal '' s) ↔ r ∈ upperBounds s := by
  simp +contextual [upperBounds, forall_mem_image, -mem_image, *]
/-
**ENNReal.iSup_coe_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：iSup_coe_eq_top : ⨆ i, (f i : Real>=0∞) = ⊤ ↔ ¬ BddAbove (range f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithTop.iSup_coe_eq_top`：iSup_coe_eq_top : ⨆ x, (f x : WithTop α) = ⊤ ↔ 
¬BddAbove (range f)
-/
lemma iSup_coe_eq_top : ⨆ i, (f i : ℝ≥0∞) = ⊤ ↔ ¬ BddAbove (range f) := WithTop.iSup_coe_eq_top
/-
**ENNReal.iSup_coe_lt_top** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：iSup_coe_lt_top : ⨆ i, (f i : Real>=0∞) < ⊤ ↔ BddAbove (range f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithTop.iSup_coe_lt_top`：iSup_coe_lt_top : ⨆ x, (f x : WithTop α) < ⊤ ↔ 
BddAbove (range f)
-/
lemma iSup_coe_lt_top : ⨆ i, (f i : ℝ≥0∞) < ⊤ ↔ BddAbove (range f) := WithTop.iSup_coe_lt_top
/-
**ENNReal.iInf_coe_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：iInf_coe_eq_top : ⨅ i, (f i : Real>=0∞) = ⊤ ↔ IsEmpty ι
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithTop.iInf_coe_eq_top`：iInf_coe_eq_top : ⨅ x, (f x : WithTop α) = ⊤ ↔ 
IsEmpty ι
-/
lemma iInf_coe_eq_top : ⨅ i, (f i : ℝ≥0∞) = ⊤ ↔ IsEmpty ι := WithTop.iInf_coe_eq_top
/-
**ENNReal.iInf_coe_lt_top** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：iInf_coe_lt_top : ⨅ i, (f i : Real>=0∞) < ⊤ ↔ Nonempty ι
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithTop.iInf_coe_lt_top`：iInf_coe_lt_top : ⨅ i, (f i : WithTop α) < ⊤ ↔ 
Nonempty ι
-/
lemma iInf_coe_lt_top : ⨅ i, (f i : ℝ≥0∞) < ⊤ ↔ Nonempty ι := WithTop.iInf_coe_lt_top

end CompleteLattice

-- TODO: add lemmas about `OfNat.ofNat`

end ENNReal

open ENNReal

namespace Set

namespace OrdConnected

variable {s : Set ℝ} {t : Set ℝ≥0} {u : Set ℝ≥0∞}

/-
**Set.OrdConnected.preimage_coe_nnreal_ennreal** 是 Mathlib 中的一个定理，位于命名空间 `Set.Or
dConnected`。
形式化陈述：preimage_coe_nnreal_ennreal (h : u.OrdConnected) : ((↑) ⁻¹' u : Set Real>=
0).OrdConnected
参数：h : u.OrdConnected。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.preimage_mono`：∀ {α : Type u_1} {β : Type u_2} [inst : 
Preorder α] [inst_1 : Preorder β] {s : Set α} {f : β → α},   s.OrdConnected → Mo
notone f → (f ⁻¹' s)…
· 使用定理 `ENNReal.coe_mono`：coe_mono : Monotone ofNNReal
-/
theorem preimage_coe_nnreal_ennreal (h : u.OrdConnected) : ((↑) ⁻¹' u : Set ℝ≥0).OrdConnected :=
  h.preimage_mono ENNReal.coe_mono

-- TODO: generalize to `WithTop`
/-
**Set.OrdConnected.image_coe_nnreal_ennreal** 是 Mathlib 中的一个定理，位于命名空间 `Set.OrdCo
nnected`。
形式化陈述：image_coe_nnreal_ennreal (h : t.OrdConnected) : ((↑) '' t : Set Real>=0∞).
OrdConnected
参数：h : t.OrdConnected。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_image`：forall_mem_image {f : α -> β} {s : Set α} {p : β -
> Prop} : (forall y in f '' s, p y) ↔ forall ⦃x⦄, x in s -> p (f x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.le_coe_iff`：le_coe_iff : a <= ↑r ↔ exists p : Real>=0, a = p ∧ p
 <= r
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem image_coe_nnreal_ennreal (h : t.OrdConnected) : ((↑) '' t : Set ℝ≥0∞).OrdConnected := by
  refine ⟨forall_mem_image.2 fun x hx => forall_mem_image.2 fun y hy z hz => ?_⟩
  rcases ENNReal.le_coe_iff.1 hz.2 with ⟨z, rfl, -⟩
  exact mem_image_of_mem _ (h.out hx hy ⟨ENNReal.coe_le_coe.1 hz.1, ENNReal.coe_le_coe.1 hz.2⟩)
/-
**Set.OrdConnected.preimage_ennreal_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `Set.OrdCon
nected`。
形式化陈述：preimage_ennreal_ofReal (h : u.OrdConnected) : (ENNReal.ofReal ⁻¹' u).OrdC
onnected
参数：h : u.OrdConnected。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.preimage_real_toNNReal`：preimage_real_toNNReal (h : t.O
rdConnected) : (Real.toNNReal ⁻¹' t).OrdConnected
· 使用定理 `Set.OrdConnected.preimage_coe_nnreal_ennreal`：preimage_coe_nnreal_ennrea
l (h : u.OrdConnected) : ((↑) ⁻¹' u : Set Real>=0).OrdConnected
-/
theorem preimage_ennreal_ofReal (h : u.OrdConnected) : (ENNReal.ofReal ⁻¹' u).OrdConnected :=
  h.preimage_coe_nnreal_ennreal.preimage_real_toNNReal
/-
**Set.OrdConnected.image_ennreal_ofReal** 是 Mathlib 中的一个定理，位于命名空间 `Set.OrdConnec
ted`。
形式化陈述：image_ennreal_ofReal (h : s.OrdConnected) : (ENNReal.ofReal '' s).OrdConne
cted
参数：h : s.OrdConnected。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.OrdConnected.image_coe_nnreal_ennreal`：image_coe_nnreal_ennreal (h :
 t.OrdConnected) : ((↑) '' t : Set Real>=0∞).OrdConnected
· 使用定理 `Set.OrdConnected.image_real_toNNReal`：image_real_toNNReal (h : s.OrdConn
ected) : (Real.toNNReal '' s).OrdConnected
-/
theorem image_ennreal_ofReal (h : s.OrdConnected) : (ENNReal.ofReal '' s).OrdConnected := by
  simpa only [image_image] using! h.image_real_toNNReal.image_coe_nnreal_ennreal

end OrdConnected

end Set

/-- While not very useful, this instance uses the same representation as `Real.instRepr`. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
While not very useful, this instance uses the same representation as `Real.instR
epr`.
-/
unsafe instance : Repr ℝ≥0∞ where
  reprPrec
  | (r : ℝ≥0), p => Repr.addAppParen f!"ENNReal.ofReal ({repr r.val})" p
  | ∞, _ => "∞"

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

/-- Extension for the `positivity` tactic: `ENNReal.toReal`. -/
@[positivity ENNReal.toReal _]
meta def evalENNRealtoReal : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(ENNReal.toReal $a) =>
    assertInstancesCommute
    pure (.nonnegative q(ENNReal.toReal_nonneg))
  | _, _, _ => throwError "not ENNReal.toReal"

/-- Extension for the `positivity` tactic: `ENNReal.ofNNReal`. -/
@[positivity ENNReal.ofNNReal _]
meta def evalENNRealOfNNReal : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ≥0∞), ~q(ENNReal.ofNNReal $a) =>
    assertInstancesCommute
    let ra ← core q(inferInstance) (some q(inferInstance)) a
    match ra with
    | .positive pa => pure <| .positive q(ENNReal.coe_pos.mpr $pa)
    | _ => pure .none
  | _, _, _ => throwError "not ENNReal.ofNNReal"

end Mathlib.Meta.Positivity

