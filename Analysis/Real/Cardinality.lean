/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Algebra.Order.Group.Pointwise.Interval
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.SetTheory.Cardinal.Continuum
public import Mathlib.SetTheory.Cardinal.Rat

/-!
# The cardinality of the reals

This file shows that the real numbers have cardinality continuum, i.e. `#ℝ = 𝔠`.

We show that `#ℝ ≤ 𝔠` by noting that every real number is determined by a Cauchy-sequence of the
form `ℕ → ℚ`, which has cardinality `𝔠`. To show that `#ℝ ≥ 𝔠` we define an injection from
`{0, 1} ^ ℕ` to `ℝ` with `f ↦ Σ n, f n * (1 / 3) ^ n`.

We conclude that all intervals with distinct endpoints have cardinality continuum.

## Main definitions

* `Cardinal.cantorFunction` is the function that sends `f` in `{0, 1} ^ ℕ` to `ℝ` by
  `f ↦ Σ' n, f n * (1 / 3) ^ n`

## Main statements

* `Cardinal.mk_real : #ℝ = 𝔠`: the reals have cardinality continuum.
* `Cardinal.not_countable_real`: the universal set of real numbers is not countable.
  We can use this same proof to show that all the other sets in this file are not countable.
* 8 lemmas of the form `mk_Ixy_real` for `x,y ∈ {i,o,c}` state that intervals on the reals
  have cardinality continuum.

## Notation

* `𝔠` : notation for `Cardinal.continuum` in scope `Cardinal`, defined in `SetTheory.Continuum`.

## Tags
continuum, cardinality, reals, cardinality of the reals
-/

@[expose] public section


open Nat Set

open Cardinal

noncomputable section

namespace Cardinal

variable {c : ℝ} {f g : ℕ → Bool} {n : ℕ}

/-- The body of the sum in `cantorFunction`.
`cantorFunctionAux c f n = c ^ n` if `f n = true`;
`cantorFunctionAux c f n = 0` if `f n = false`. -/
/-
**Cardinal.cantorFunctionAux** 是 Mathlib 中的一个定义，位于命名空间 `Cardinal`。
形式化陈述：cantorFunctionAux (c : Real) (f : Nat -> Bool) (n : Nat) : Real
参数：c : Real；f : Nat -> Bool；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The body of the sum in `cantorFunction`.
`cantorFunctionAux c f n = c ^ n` if `f n = true`;
`cantorFunctionAux c f n = 0` if `f n = false`.
-/
def cantorFunctionAux (c : ℝ) (f : ℕ → Bool) (n : ℕ) : ℝ :=
  cond (f n) (c ^ n) 0

@[simp]
/-
**Cardinal.cantorFunctionAux_true** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：cantorFunctionAux_true (h : f n = true) : cantorFunctionAux c f n = c ^ n
参数：h : f n = true。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cantorFunctionAux_true (h : f n = true) : cantorFunctionAux c f n = c ^ n := by
  simp [cantorFunctionAux, h]

@[simp]
/-
**Cardinal.cantorFunctionAux_false** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：cantorFunctionAux_false (h : f n = false) : cantorFunctionAux c f n = 0
参数：h : f n = false。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cantorFunctionAux_false (h : f n = false) : cantorFunctionAux c f n = 0 := by
  simp [cantorFunctionAux, h]
/-
**Cardinal.cantorFunctionAux_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：cantorFunctionAux_nonneg (h : 0 <= c) : 0 <= cantorFunctionAux c f n
参数：h : 0 <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.cantorFunctionAux_false`：cantorFunctionAux_false (h : f n = fal
se) : cantorFunctionAux c f n = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.cantorFunctionAux_true`：cantorFunctionAux_true (h : f n = true)
 : cantorFunctionAux c f n = c ^ n
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
theorem cantorFunctionAux_nonneg (h : 0 ≤ c) : 0 ≤ cantorFunctionAux c f n := by
  cases h' : f n
  · simp [h']
  · simpa [h'] using pow_nonneg h _
/-
**Cardinal.cantorFunctionAux_eq** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：cantorFunctionAux_eq (h : f n = g n) : cantorFunctionAux c f n = cantorFun
ctionAux c g n
参数：h : f n = g n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cantorFunctionAux_eq (h : f n = g n) :
    cantorFunctionAux c f n = cantorFunctionAux c g n := by simp [cantorFunctionAux, h]
/-
**Cardinal.cantorFunctionAux_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：cantorFunctionAux_zero (f : Nat -> Bool) : cantorFunctionAux c f 0 = cond 
(f 0) 1 0
参数：f : Nat -> Bool。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.cantorFunctionAux_false`：cantorFunctionAux_false (h : f n = fal
se) : cantorFunctionAux c f n = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.cantorFunctionAux_true`：cantorFunctionAux_true (h : f n = true)
 : cantorFunctionAux c f n = c ^ n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
-/
theorem cantorFunctionAux_zero (f : ℕ → Bool) : cantorFunctionAux c f 0 = cond (f 0) 1 0 := by
  cases h : f 0 <;> simp [h]
/-
**Cardinal.cantorFunctionAux_succ** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：cantorFunctionAux_succ (f : Nat -> Bool) : (fun n => cantorFunctionAux c f
 (n + 1)) = fun n => c * cantorFunctionAux c (fun n => f (n + 1)) n
参数：f : Nat -> Bool。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.cantorFunctionAux_false`：cantorFunctionAux_false (h : f n = fal
se) : cantorFunctionAux c f n = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.cantorFunctionAux_true`：cantorFunctionAux_true (h : f n = true)
 : cantorFunctionAux c f n = c ^ n
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
-/
theorem cantorFunctionAux_succ (f : ℕ → Bool) :
    (fun n => cantorFunctionAux c f (n + 1)) = fun n =>
      c * cantorFunctionAux c (fun n => f (n + 1)) n := by
  ext n
  cases h : f (n + 1) <;> simp [h, _root_.pow_succ']
/-
**Cardinal.summable_cantor_function** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：summable_cantor_function (f : Nat -> Bool) (h1 : 0 <= c) (h2 : c < 1) : Su
mmable (cantorFunctionAux c f)
参数：f : Nat -> Bool；h1 : 0 <= c；h2 : c < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.summable_of_eq_zero_or_self`：∀ {α : Type u_1} {β : Type u_2} [i
nst : UniformSpace α] [inst_1 : AddCommGroup α] [IsUniformAddGroup α] {f g : β →
 α}   [CompleteSpace α], S…
· 使用定理 `instIsUniformAddGroupReal`：IsUniformAddGroup ℝ
· 使用定理 `summable_geometric_of_lt_one`：summable_geometric_of_lt_one {r : Real} (h
₁ : 0 <= r) (h₂ : r < 1) : Summable fun n : Nat => r ^ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Cardinal.cantorFunctionAux_false`：cantorFunctionAux_false (h : f n = fal
se) : cantorFunctionAux c f n = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.cantorFunctionAux_true`：cantorFunctionAux_true (h : f n = true)
 : cantorFunctionAux c f n = c ^ n
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem summable_cantor_function (f : ℕ → Bool) (h1 : 0 ≤ c) (h2 : c < 1) :
    Summable (cantorFunctionAux c f) := by
  apply (summable_geometric_of_lt_one h1 h2).summable_of_eq_zero_or_self
  intro n; cases h : f n <;> simp [h]

/-- `cantorFunction c (f : ℕ → Bool)` is `Σ n, f n * c ^ n`, where `true` is interpreted as `1` and
`false` is interpreted as `0`. It is implemented using `cantorFunctionAux`. -/
/-
**Cardinal.cantorFunction** 是 Mathlib 中的一个定义，位于命名空间 `Cardinal`。
形式化陈述：cantorFunction (c : Real) (f : Nat -> Bool) : Real
参数：c : Real；f : Nat -> Bool。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`cantorFunction c (f : ℕ → Bool)` is `Σ n, f n * c ^ n`, where `true` is interpr
eted as `1` and
`false` is interpreted as `0`. It is implemented using `cantorFunctionAux`.
-/
def cantorFunction (c : ℝ) (f : ℕ → Bool) : ℝ :=
  ∑' n, cantorFunctionAux c f n
/-
**Cardinal.cantorFunction_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：cantorFunction_le (h1 : 0 <= c) (h2 : c < 1) (h3 : forall n, f n -> g n) :
 cantorFunction c f <= cantorFunction c g
参数：h1 : 0 <= c；h2 : c < 1；h3 : forall n, f n -> g n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.tsum_le_tsum`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFil
ter ι} [inst : AddCommMonoid α] [inst_1 : Preorder α]   [IsOrderedAddMonoid α] [
inst_3 : To…
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.cantorFunctionAux_false`：cantorFunctionAux_false (h : f n = fal
se) : cantorFunctionAux c f n = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Cardinal.cantorFunctionAux_nonneg`：cantorFunctionAux_nonneg (h : 0 <= c)
 : 0 <= cantorFunctionAux c f n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.cantorFunctionAux_true`：cantorFunctionAux_true (h : f n = true)
 : cantorFunctionAux c f n = c ^ n
· 使用定理 `Cardinal.summable_cantor_function`：summable_cantor_function (f : Nat -> 
Bool) (h1 : 0 <= c) (h2 : c < 1) : Summable (cantorFunctionAux c f)
-/
theorem cantorFunction_le (h1 : 0 ≤ c) (h2 : c < 1) (h3 : ∀ n, f n → g n) :
    cantorFunction c f ≤ cantorFunction c g := by
  apply (summable_cantor_function f h1 h2).tsum_le_tsum _ (summable_cantor_function g h1 h2)
  intro n; cases h : f n
  · simp [h, cantorFunctionAux_nonneg h1]
  replace h3 : g n = true := h3 n h; simp [h, h3]
/-
**Cardinal.cantorFunction_succ** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：cantorFunction_succ (f : Nat -> Bool) (h1 : 0 <= c) (h2 : c < 1) : cantorF
unction c f = cond (f 0) 1 0 + c * cantorFunction c fun n => f (n + 1)
参数：f : Nat -> Bool；h1 : 0 <= c；h2 : c < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.cantorFunction.eq_1`：∀ (c : ℝ) (f : ℕ → Bool), Cardinal.cantorF
unction c f = ∑' (n : ℕ), Cardinal.cantorFunctionAux c f n
· 使用定理 `Summable.tsum_eq_zero_add`：∀ {G : Type u_2} [inst : AddCommGroup G] [ins
t_1 : TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]   {f : ℕ → G}, S
ummable f → ∑' …
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Cardinal.summable_cantor_function`：summable_cantor_function (f : Nat -> 
Bool) (h1 : 0 <= c) (h2 : c < 1) : Summable (cantorFunctionAux c f)
· 使用定理 `Cardinal.cantorFunctionAux_succ`：cantorFunctionAux_succ (f : Nat -> Bool
) : (fun n => cantorFunctionAux c f (n + 1)) = fun n => c * cantorFunctionAux c 
(fun n => f (n + 1)) …
· 使用定理 `tsum_mul_left`：tsum_mul_left [T2Space α] : ∑'[L] x, a * f x = a * ∑'[L] 
x, f x
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Cardinal.cantorFunctionAux.eq_1`：∀ (c : ℝ) (f : ℕ → Bool) (n : ℕ), Cardi
nal.cantorFunctionAux c f n = bif f n then c ^ n else 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
-/
theorem cantorFunction_succ (f : ℕ → Bool) (h1 : 0 ≤ c) (h2 : c < 1) :
    cantorFunction c f = cond (f 0) 1 0 + c * cantorFunction c fun n => f (n + 1) := by
  rw [cantorFunction, (summable_cantor_function f h1 h2).tsum_eq_zero_add]
  rw [cantorFunctionAux_succ, tsum_mul_left, cantorFunctionAux, pow_zero, cantorFunction]

/-- `cantorFunction c` is strictly increasing with if `0 < c < 1/2`, if we endow `ℕ → Bool` with a
lexicographic order. The lexicographic order doesn't exist for these infinitary products, so we
explicitly write out what it means. -/
/-
**Cardinal.increasing_cantorFunction** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：increasing_cantorFunction (h1 : 0 < c) (h2 : c < 1 / 2) {n : Nat} {f g : N
at -> Bool} (hn : forall k < n, f k = g k) (fn : f n = false) (gn : g n = true) 
: cantorFunction c f < cantorFunction c g
参数：h1 : 0 < c；h2 : c < 1 / 2；hn : forall k < n, f k = g k；fn : f n = false；gn : 
g n = true。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_lt_true`：isNNRat_lt_true [Semiring α] [Line
arOrder α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Nat} -> {da db : Nat}
 -> IsNNRat a na da -> IsN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Cardinal.cantorFunction_le`：cantorFunction_le (h1 : 0 <= c) (h2 : c < 1)
 (h3 : forall n, f n -> g n) : cantorFunction c f <= cantorFunction c g
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `div_lt_one`：div_lt_one (hb : 0 < b) : a / b < 1 ↔ a < b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
（共 58 条，此处仅展示前 30 条）

--- 原说明 ---
`cantorFunction c` is strictly increasing with if `0 < c < 1/2`, if we endow `ℕ 
→ Bool` with a
lexicographic order. The lexicographic order doesn't exist for these infinitary 
products, so we
explicitly write out what it means.
-/
theorem increasing_cantorFunction (h1 : 0 < c) (h2 : c < 1 / 2) {n : ℕ} {f g : ℕ → Bool}
    (hn : ∀ k < n, f k = g k) (fn : f n = false) (gn : g n = true) :
    cantorFunction c f < cantorFunction c g := by
  have h3 : c < 1 := by
    apply h2.trans
    norm_num
  induction n generalizing f g with
  | zero =>
    let f_max : ℕ → Bool := fun n => Nat.rec false (fun _ _ => true) n
    have hf_max : ∀ n, f n → f_max n := by
      intro n hn
      cases n
      · rw [fn] at hn
        contradiction
      simp [f_max]
    let g_min : ℕ → Bool := fun n => Nat.rec true (fun _ _ => false) n
    have hg_min : ∀ n, g_min n → g n := by
      intro n hn
      cases n
      · rw [gn]
      simp at hn
    apply (cantorFunction_le (le_of_lt h1) h3 hf_max).trans_lt
    refine lt_of_lt_of_le ?_ (cantorFunction_le (le_of_lt h1) h3 hg_min)
    have : c / (1 - c) < 1 := by
      rw [div_lt_one, lt_sub_iff_add_lt]
      · convert! _root_.add_lt_add h2 h2
        norm_num
      rwa [sub_pos]
    convert! this
    · rw [cantorFunction_succ _ (le_of_lt h1) h3, div_eq_mul_inv, ←
        tsum_geometric_of_lt_one (le_of_lt h1) h3]
      apply zero_add
    · refine (tsum_eq_single 0 ?_).trans ?_
      · intro n hn
        cases n
        · contradiction
        simp [g_min]
      · exact cantorFunctionAux_zero _
  | succ n ih =>
  rw [cantorFunction_succ f h1.le h3, cantorFunction_succ g h1.le h3]
  rw [hn 0 <| zero_lt_succ n]
  gcongr
  exact ih (fun k hk => hn _ <| Nat.succ_lt_succ hk) fn gn

/-- `cantorFunction c` is injective if `0 < c < 1/2`. -/
/-
**Cardinal.cantorFunction_injective** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：cantorFunction_injective (h1 : 0 < c) (h2 : c < 1 / 2) : Function.Injectiv
e (cantorFunction c)
参数：h1 : 0 < c；h2 : c < 1 / 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.ne_iff`：ne_iff {β : α -> Sort*} {f₁ f₂ : forall a, β a} : f₁ !=
 f₂ ↔ exists a, f₁ a != f₂ a
· 使用定理 `of_not_not`：of_not_not {a : Prop} : ¬¬a -> a
· 使用定理 `Nat.find_min`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) {
m : ℕ}, m < Nat.find H → ¬p m
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `Cardinal.increasing_cantorFunction`：increasing_cantorFunction (h1 : 0 < 
c) (h2 : c < 1 / 2) {n : Nat} {f g : Nat -> Bool} (hn : forall k < n, f k = g k)
 (fn : f n = false) (gn …
· 使用定理 `Bool.eq_true_of_not_eq_false`：eq_true_of_not_eq_false {b : Bool} : ¬b = 
false -> b = true
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Bool.eq_false_of_not_eq_true`：eq_false_of_not_eq_true {b : Bool} : ¬b = 
true -> b = false

--- 原说明 ---
`cantorFunction c` is injective if `0 < c < 1/2`.
-/
theorem cantorFunction_injective (h1 : 0 < c) (h2 : c < 1 / 2) :
    Function.Injective (cantorFunction c) := by
  intro f g hfg
  classical
    contrapose hfg with h
    have : ∃ n, f n ≠ g n := Function.ne_iff.mp h
    let n := Nat.find this
    have hn : ∀ k : ℕ, k < n → f k = g k := by
      intro k hk
      apply of_not_not
      exact Nat.find_min this hk
    cases fn : f n
    · apply _root_.ne_of_lt
      refine increasing_cantorFunction h1 h2 hn fn ?_
      apply Bool.eq_true_of_not_eq_false
      rw [← fn]
      apply Ne.symm
      exact Nat.find_spec this
    · apply _root_.ne_of_gt
      refine increasing_cantorFunction h1 h2 (fun k hk => (hn k hk).symm) ?_ fn
      apply Bool.eq_false_of_not_eq_true
      rw [← fn]
      apply Ne.symm
      exact Nat.find_spec this

/-- The cardinality of the reals, as a type. -/
/-
**Cardinal.mk_real** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_real : #Real = 𝔠
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.cardinal_eq`：∀ {α β : Type u} (e : α ≃ β), Cardinal.mk α = Cardina
l.mk β
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Cardinal.mk_quotient_le`：mk_quotient_le {α : Type u} {s : Setoid α} : #(
Quotient s) <= #α
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Cardinal.mk_subtype_le`：mk_subtype_le {α : Type u} (p : α -> Prop) : #(S
ubtype p) <= #α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.power_def`：power_def (α β : Type u) : #α ^ #β = #(β -> α)
· 使用定理 `Cardinal.mk_nat`：mk_nat : #Nat = ℵ₀
· 使用定理 `Cardinal.mkRat`：Cardinal.mkRat : #Rat = ℵ₀
· 使用定理 `Cardinal.aleph0_power_aleph0`：aleph0_power_aleph0 : ℵ₀ ^ ℵ₀ = 𝔠
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Cardinal.mk_bool`：mk_bool : #Bool = 2
· 使用定理 `Cardinal.two_power_aleph0`：two_power_aleph0 : 2 ^ ℵ₀ = 𝔠
· 使用定理 `Cardinal.mk_le_of_injective`：mk_le_of_injective {α β : Type u} {f : α ->
 β} (hf : Injective f) : #α <= #β
· 使用定理 `Cardinal.cantorFunction_injective`：cantorFunction_injective (h1 : 0 < c)
 (h2 : c < 1 / 2) : Function.Injective (cantorFunction c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_lt_true`：isNNRat_lt_true [Semiring α] [Line
arOrder α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Nat} -> {da db : Nat}
 -> IsNNRat a na da -> IsN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
The cardinality of the reals, as a type.
-/
theorem mk_real : #ℝ = 𝔠 := by
  apply le_antisymm
  · rw [Real.equivCauchy.cardinal_eq]
    apply mk_quotient_le.trans
    apply (mk_subtype_le _).trans_eq
    rw [← power_def, mk_nat, mkRat, aleph0_power_aleph0]
  · convert! mk_le_of_injective (cantorFunction_injective _ _)
    · rw [← power_def, mk_bool, mk_nat, two_power_aleph0]
    · exact 1 / 3
    · simp
    · norm_num

/-- The cardinality of the reals, as a set. -/
/-
**Cardinal.mk_univ_real** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_univ_real : #(Set.univ : Set Real) = 𝔠
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_univ`：mk_univ {α : Type u} : #(@univ α) = #α
· 使用定理 `Cardinal.mk_real`：mk_real : #Real = 𝔠

--- 原说明 ---
The cardinality of the reals, as a set.
-/
theorem mk_univ_real : #(Set.univ : Set ℝ) = 𝔠 := by rw [mk_univ, mk_real]

/-- **Non-Denumerability of the Continuum**: The reals are not countable. -/
/-
**Cardinal.** 是 Mathlib 中的一个实例，位于命名空间 `Cardinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Non-Denumerability of the Continuum**: The reals are not countable.
-/
instance : Uncountable ℝ := by
  rw [← aleph0_lt_mk_iff, mk_real]
  exact aleph0_lt_continuum
/-
**Cardinal.not_countable_real** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：not_countable_real : ¬(Set.univ : Set Real).Countable
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.not_countable_univ`：not_countable_univ [Uncountable α] : ¬ (univ : S
et α).Countable
· 使用定理 `Cardinal.instUncountableReal`：Uncountable ℝ
-/
theorem not_countable_real : ¬(Set.univ : Set ℝ).Countable :=
  not_countable_univ

/-- The cardinality of the interval $(a, ∞)$. -/
/-
**Cardinal.mk_Ioi_real** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_Ioi_real (a : Real) : #(Ioi a) = 𝔠
参数：a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Cardinal.mk_set_le`：mk_set_le (s : Set α) : #s <= #α
· 使用定理 `Cardinal.mk_real`：mk_real : #Real = 𝔠
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Set.Iio_union_right`：Iio_union_right : Iio a union {a} = Iic a
· 使用定理 `Set.Iic_union_Ioi`：Iic_union_Ioi : Iic a union Ioi a = univ
· 使用定理 `lt_imp_lt_of_le_of_le`：lt_imp_lt_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a < b -> c < d
· 使用定理 `Cardinal.mk_union_le`：mk_union_le {α : Type u} (S T : Set α) : #(S union
 T : Set α) <= #S + #T
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_const_sub_Ioi`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_
1 : PartialOrder α] [IsOrderedAddMonoid α] (a b : α),   (fun x => a - x) '' Set.
Ioi b = Set.I…
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Cardinal.add_lt_of_lt`：add_lt_of_lt {a b c : Cardinal} (hc : ℵ₀ <= c) (h
1 : a < c) (h2 : b < c) : a + b < c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Cardinal.cantor`：cantor (a : Cardinal.{u}) : a < 2 ^ a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
The cardinality of the interval $(a, ∞)$.
-/
theorem mk_Ioi_real (a : ℝ) : #(Ioi a) = 𝔠 := by
  refine le_antisymm (mk_real ▸ mk_set_le _) ?_
  rw [← not_lt]
  intro h
  refine _root_.ne_of_lt ?_ mk_univ_real
  have hu : Iio a ∪ {a} ∪ Ioi a = Set.univ := by
    convert! @Iic_union_Ioi ℝ _ _
    exact Iio_union_right
  rw [← hu]
  grw [mk_union_le, mk_union_le]
  have h2 : (fun x => a + a - x) '' Ioi a = Iio a := by
    convert! @image_const_sub_Ioi ℝ _ _ _
    simp
  rw [← h2]
  refine add_lt_of_lt (cantor _).le ?_ h
  refine add_lt_of_lt (cantor _).le (mk_image_le.trans_lt h) ?_
  rw [mk_singleton]
  exact one_lt_aleph0.trans (cantor _)

/-- The cardinality of the interval $[a, ∞)$. -/
/-
**Cardinal.mk_Ici_real** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_Ici_real (a : Real) : #(Ici a) = 𝔠
参数：a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Cardinal.mk_set_le`：mk_set_le (s : Set α) : #s <= #α
· 使用定理 `Cardinal.mk_real`：mk_real : #Real = 𝔠
· 使用定理 `Cardinal.mk_le_mk_of_subset`：mk_le_mk_of_subset {α} {s t : Set α} (h : s
 subseteq t) : #s <= #t
· 使用定理 `Set.Ioi_subset_Ici_self`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, S
et.Ioi a ⊆ Set.Ici a
· 使用定理 `Cardinal.mk_Ioi_real`：mk_Ioi_real (a : Real) : #(Ioi a) = 𝔠

--- 原说明 ---
The cardinality of the interval $[a, ∞)$.
-/
theorem mk_Ici_real (a : ℝ) : #(Ici a) = 𝔠 :=
  le_antisymm (mk_real ▸ mk_set_le _) (mk_Ioi_real a ▸ mk_le_mk_of_subset Ioi_subset_Ici_self)

/-- The cardinality of the interval $(-∞, a)$. -/
/-
**Cardinal.mk_Iio_real** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_Iio_real (a : Real) : #(Iio a) = 𝔠
参数：a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Cardinal.mk_set_le`：mk_set_le (s : Set α) : #s <= #α
· 使用定理 `Cardinal.mk_real`：mk_real : #Real = 𝔠
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_const_sub_Iio`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_
1 : PartialOrder α] [IsOrderedAddMonoid α] (a b : α),   (fun x => a - x) '' Set.
Iio b = Set.I…
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Cardinal.mk_image_le`：mk_image_le {α β : Type u} {f : α -> β} {s : Set α
} : #(f '' s) <= #s
· 使用定理 `Cardinal.mk_Ioi_real`：mk_Ioi_real (a : Real) : #(Ioi a) = 𝔠

--- 原说明 ---
The cardinality of the interval $(-∞, a)$.
-/
theorem mk_Iio_real (a : ℝ) : #(Iio a) = 𝔠 := by
  refine le_antisymm (mk_real ▸ mk_set_le _) ?_
  have h2 : (fun x => a + a - x) '' Iio a = Ioi a := by
    simp only [image_const_sub_Iio, add_sub_cancel_right]
  exact mk_Ioi_real a ▸ h2 ▸ mk_image_le

/-- The cardinality of the interval $(-∞, a]$. -/
/-
**Cardinal.mk_Iic_real** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_Iic_real (a : Real) : #(Iic a) = 𝔠
参数：a : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Cardinal.mk_set_le`：mk_set_le (s : Set α) : #s <= #α
· 使用定理 `Cardinal.mk_real`：mk_real : #Real = 𝔠
· 使用定理 `Cardinal.mk_le_mk_of_subset`：mk_le_mk_of_subset {α} {s t : Set α} (h : s
 subseteq t) : #s <= #t
· 使用定理 `Set.Iio_subset_Iic_self`：Iio_subset_Iic_self : Iio a subseteq Iic a
· 使用定理 `Cardinal.mk_Iio_real`：mk_Iio_real (a : Real) : #(Iio a) = 𝔠

--- 原说明 ---
The cardinality of the interval $(-∞, a]$.
-/
theorem mk_Iic_real (a : ℝ) : #(Iic a) = 𝔠 :=
  le_antisymm (mk_real ▸ mk_set_le _) (mk_Iio_real a ▸ mk_le_mk_of_subset Iio_subset_Iic_self)

/-- The cardinality of the interval $(a, b)$. -/
/-
**Cardinal.mk_Ioo_real** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_Ioo_real {a b : Real} (h : a < b) : #(Ioo a b) = 𝔠
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Cardinal.mk_set_le`：mk_set_le (s : Set α) : #s <= #α
· 使用定理 `Cardinal.mk_real`：mk_real : #Real = 𝔠
· 使用定理 `Cardinal.mk_image_le`：mk_image_le {α β : Type u} {f : α -> β} {s : Set α
} : #(f '' s) <= #s
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_sub_const_Ioo`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_
1 : PartialOrder α] [IsOrderedAddMonoid α] (a b c : α),   (fun x => x - a) '' Se
t.Ioo b c = S…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `sub_pos_of_lt`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRi
ghtStrictMono α] {a b : α}, b < a → 0 < a - b
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
· 使用定理 `Set.image_inv_eq_inv`：image_inv_eq_inv : (·⁻¹) '' s = s⁻¹
· 使用定理 `Set.inv_Ioo_0_left`：inv_Ioo_0_left (ha : 0 < a) : (Ioo 0 a)⁻¹ = Ioi a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Cardinal.mk_Ioi_real`：mk_Ioi_real (a : Real) : #(Ioi a) = 𝔠
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
The cardinality of the interval $(a, b)$.
-/
theorem mk_Ioo_real {a b : ℝ} (h : a < b) : #(Ioo a b) = 𝔠 := by
  refine le_antisymm (mk_real ▸ mk_set_le _) ?_
  have h1 : #((fun x => x - a) '' Ioo a b) ≤ #(Ioo a b) := mk_image_le
  refine le_trans ?_ h1
  rw [image_sub_const_Ioo, sub_self]
  replace h := sub_pos_of_lt h
  have h2 : #(Inv.inv '' Ioo 0 (b - a)) ≤ #(Ioo 0 (b - a)) := mk_image_le
  refine le_trans ?_ h2
  rw [image_inv_eq_inv, inv_Ioo_0_left h, mk_Ioi_real]

/-- The cardinality of the interval $[a, b)$. -/
/-
**Cardinal.mk_Ico_real** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_Ico_real {a b : Real} (h : a < b) : #(Ico a b) = 𝔠
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Cardinal.mk_set_le`：mk_set_le (s : Set α) : #s <= #α
· 使用定理 `Cardinal.mk_real`：mk_real : #Real = 𝔠
· 使用定理 `Cardinal.mk_le_mk_of_subset`：mk_le_mk_of_subset {α} {s t : Set α} (h : s
 subseteq t) : #s <= #t
· 使用定理 `Set.Ioo_subset_Ico_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo a b ⊆ Set.Ico a b
· 使用定理 `Cardinal.mk_Ioo_real`：mk_Ioo_real {a b : Real} (h : a < b) : #(Ioo a b) 
= 𝔠

--- 原说明 ---
The cardinality of the interval $[a, b)$.
-/
theorem mk_Ico_real {a b : ℝ} (h : a < b) : #(Ico a b) = 𝔠 :=
  le_antisymm (mk_real ▸ mk_set_le _) (mk_Ioo_real h ▸ mk_le_mk_of_subset Ioo_subset_Ico_self)

/-- The cardinality of the interval $[a, b]$. -/
/-
**Cardinal.mk_Icc_real** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_Icc_real {a b : Real} (h : a < b) : #(Icc a b) = 𝔠
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Cardinal.mk_set_le`：mk_set_le (s : Set α) : #s <= #α
· 使用定理 `Cardinal.mk_real`：mk_real : #Real = 𝔠
· 使用定理 `Cardinal.mk_le_mk_of_subset`：mk_le_mk_of_subset {α} {s t : Set α} (h : s
 subseteq t) : #s <= #t
· 使用定理 `Set.Ioo_subset_Icc_self`：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b
· 使用定理 `Cardinal.mk_Ioo_real`：mk_Ioo_real {a b : Real} (h : a < b) : #(Ioo a b) 
= 𝔠

--- 原说明 ---
The cardinality of the interval $[a, b]$.
-/
theorem mk_Icc_real {a b : ℝ} (h : a < b) : #(Icc a b) = 𝔠 :=
  le_antisymm (mk_real ▸ mk_set_le _) (mk_Ioo_real h ▸ mk_le_mk_of_subset Ioo_subset_Icc_self)

/-- The cardinality of the interval $(a, b]$. -/
/-
**Cardinal.mk_Ioc_real** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_Ioc_real {a b : Real} (h : a < b) : #(Ioc a b) = 𝔠
参数：h : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Cardinal.mk_set_le`：mk_set_le (s : Set α) : #s <= #α
· 使用定理 `Cardinal.mk_real`：mk_real : #Real = 𝔠
· 使用定理 `Cardinal.mk_le_mk_of_subset`：mk_le_mk_of_subset {α} {s t : Set α} (h : s
 subseteq t) : #s <= #t
· 使用定理 `Set.Ioo_subset_Ioc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo b a ⊆ Set.Ioc b a
· 使用定理 `Cardinal.mk_Ioo_real`：mk_Ioo_real {a b : Real} (h : a < b) : #(Ioo a b) 
= 𝔠

--- 原说明 ---
The cardinality of the interval $(a, b]$.
-/
theorem mk_Ioc_real {a b : ℝ} (h : a < b) : #(Ioc a b) = 𝔠 :=
  le_antisymm (mk_real ▸ mk_set_le _) (mk_Ioo_real h ▸ mk_le_mk_of_subset Ioo_subset_Ioc_self)

@[simp]
/-
**Cardinal.Real.Ioo_countable_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal.Real`。
形式化陈述：∀ {x y : ℝ}, (Set.Ioo x y).Countable ↔ y ≤ x
参数：Set.Ioo x y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.le_aleph0_iff_set_countable`：le_aleph0_iff_set_countable {s : S
et α} : #s <= ℵ₀ ↔ s.Countable
· 使用定理 `Cardinal.mk_Ioo_real`：mk_Ioo_real {a b : Real} (h : a < b) : #(Ioo a b) 
= 𝔠
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Cardinal.aleph0_lt_continuum`：aleph0_lt_continuum : ℵ₀ < 𝔠
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.Ioo_eq_empty`：Ioo_eq_empty (h : ¬a < b) : Ioo a b = ∅
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma Real.Ioo_countable_iff {x y : ℝ} :
    (Ioo x y).Countable ↔ y ≤ x := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  contrapose! h
  rw [← Cardinal.le_aleph0_iff_set_countable, Cardinal.mk_Ioo_real h, not_le]
  exact Cardinal.aleph0_lt_continuum

@[simp]
/-
**Cardinal.Real.Ico_countable_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal.Real`。
形式化陈述：∀ {x y : ℝ}, (Set.Ico x y).Countable ↔ y ≤ x
参数：Set.Ico x y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.le_aleph0_iff_set_countable`：le_aleph0_iff_set_countable {s : S
et α} : #s <= ℵ₀ ↔ s.Countable
· 使用定理 `Cardinal.mk_Ico_real`：mk_Ico_real {a b : Real} (h : a < b) : #(Ico a b) 
= 𝔠
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Cardinal.aleph0_lt_continuum`：aleph0_lt_continuum : ℵ₀ < 𝔠
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.Ico_eq_empty`：Ico_eq_empty (h : ¬a < b) : Ico a b = ∅
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma Real.Ico_countable_iff {x y : ℝ} :
    (Ico x y).Countable ↔ y ≤ x := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  contrapose! h
  rw [← Cardinal.le_aleph0_iff_set_countable, Cardinal.mk_Ico_real h, not_le]
  exact Cardinal.aleph0_lt_continuum

@[simp]
/-
**Cardinal.Real.Ioc_countable_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal.Real`。
形式化陈述：∀ {x y : ℝ}, (Set.Ioc x y).Countable ↔ y ≤ x
参数：Set.Ioc x y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.le_aleph0_iff_set_countable`：le_aleph0_iff_set_countable {s : S
et α} : #s <= ℵ₀ ↔ s.Countable
· 使用定理 `Cardinal.mk_Ioc_real`：mk_Ioc_real {a b : Real} (h : a < b) : #(Ioc a b) 
= 𝔠
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Cardinal.aleph0_lt_continuum`：aleph0_lt_continuum : ℵ₀ < 𝔠
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.Ioc_eq_empty`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, ¬b < a
 → Set.Ioc b a = ∅
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma Real.Ioc_countable_iff {x y : ℝ} :
    (Ioc x y).Countable ↔ y ≤ x := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  contrapose! h
  rw [← Cardinal.le_aleph0_iff_set_countable, Cardinal.mk_Ioc_real h, not_le]
  exact Cardinal.aleph0_lt_continuum

@[simp]
/-
**Cardinal.Real.Icc_countable_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal.Real`。
形式化陈述：∀ {x y : ℝ}, (Set.Icc x y).Countable ↔ y ≤ x
参数：Set.Icc x y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.le_aleph0_iff_set_countable`：le_aleph0_iff_set_countable {s : S
et α} : #s <= ℵ₀ ↔ s.Countable
· 使用定理 `Cardinal.mk_Icc_real`：mk_Icc_real {a b : Real} (h : a < b) : #(Icc a b) 
= 𝔠
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Cardinal.aleph0_lt_continuum`：aleph0_lt_continuum : ℵ₀ < 𝔠
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_iff_eq_or_lt`：le_iff_eq_or_lt : a <= b ↔ a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `Set.Icc_eq_empty`：Icc_eq_empty (h : ¬a <= b) : Icc a b = ∅
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma Real.Icc_countable_iff {x y : ℝ} :
    (Icc x y).Countable ↔ y ≤ x := by
  refine ⟨fun h ↦ ?_, fun h ↦ by
    rcases le_iff_eq_or_lt.mp h with heq | hlt
    · simp [heq]
    · simp [hlt]⟩
  contrapose! h
  rw [← Cardinal.le_aleph0_iff_set_countable, Cardinal.mk_Icc_real h, not_le]
  exact Cardinal.aleph0_lt_continuum

end Cardinal

