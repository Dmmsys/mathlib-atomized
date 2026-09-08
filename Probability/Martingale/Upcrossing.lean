/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.Order.Interval.Set.Monotone
public import Mathlib.Probability.Notation
public import Mathlib.Probability.Process.HittingTime
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Tactic.AdaptationNote

/-!

# Doob's upcrossing estimate

Given a discrete real-valued submartingale $(f_n)_{n \in \mathbb{N}}$, denoting by $U_N(a, b)$ the
number of times $f_n$ crossed from below $a$ to above $b$ before time $N$, Doob's upcrossing
estimate (also known as Doob's inequality) states that
$$(b - a) \mathbb{E}[U_N(a, b)] \le \mathbb{E}[(f_N - a)^+].$$
Doob's upcrossing estimate is an important inequality and is central in proving the martingale
convergence theorems.

## Main definitions

* `MeasureTheory.upperCrossingTime a b f N n`: is the stopping time corresponding to `f`
  crossing above `b` the `n`-th time before time `N` (if this does not occur then the value is
  taken to be `N`).
* `MeasureTheory.lowerCrossingTime a b f N n`: is the stopping time corresponding to `f`
  crossing below `a` the `n`-th time before time `N` (if this does not occur then the value is
  taken to be `N`).
* `MeasureTheory.upcrossingStrat a b f N`: is the predictable process which is 1 if `n` is
  between a consecutive pair of lower and upper crossings and is 0 otherwise. Intuitively
  one might think of the `upcrossingStrat` as the strategy of buying 1 share whenever the process
  crosses below `a` for the first time after selling and selling 1 share whenever the process
  crosses above `b` for the first time after buying.
* `MeasureTheory.upcrossingsBefore a b f N`: is the number of times `f` crosses from below `a` to
  above `b` before time `N`.
* `MeasureTheory.upcrossings a b f`: is the number of times `f` crosses from below `a` to above
  `b`. This takes value in `ℝ≥0∞` and so is allowed to be `∞`.

## Main results

* `MeasureTheory.StronglyAdapted.isStoppingTime_upperCrossingTime`: `upperCrossingTime` is a
  stopping time whenever the process it is associated to is adapted.
* `MeasureTheory.StronglyAdapted.isStoppingTime_lowerCrossingTime`: `lowerCrossingTime` is a
  stopping time whenever the process it is associated to is adapted.
* `MeasureTheory.Submartingale.mul_integral_upcrossingsBefore_le_integral_pos_part`: Doob's
  upcrossing estimate.
* `MeasureTheory.Submartingale.mul_lintegral_upcrossings_le_lintegral_pos_part`: the inequality
  obtained by taking the supremum on both sides of Doob's upcrossing estimate.

### References

We mostly follow the proof from [Kallenberg, *Foundations of modern probability*][kallenberg2021]

-/

@[expose] public section


open TopologicalSpace Filter

open scoped NNReal ENNReal MeasureTheory ProbabilityTheory Topology

namespace MeasureTheory

variable {Ω ι : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-!

## Proof outline

In this section, we will denote by $U_N(a, b)$ the number of upcrossings of $(f_n)$ from below $a$
to above $b$ before time $N$.

To define $U_N(a, b)$, we will construct two stopping times corresponding to when $(f_n)$ crosses
below $a$ and above $b$. Namely, we define
$$
  \sigma_n := \inf \{n \ge \tau_n \mid f_n \le a\} \wedge N;
$$
$$
  \tau_{n + 1} := \inf \{n \ge \sigma_n \mid f_n \ge b\} \wedge N.
$$
These are `lowerCrossingTime` and `upperCrossingTime` in our formalization which are defined
using `MeasureTheory.hittingBtwn` allowing us to specify a starting and ending time.
Then, we may simply define $U_N(a, b) := \sup \{n \mid \tau_n < N\}$.

Fixing $a < b \in \mathbb{R}$, we will first prove the theorem in the special case that
$0 \le f_0$ and $a \le f_N$. In particular, we will show
$$
  (b - a) \mathbb{E}[U_N(a, b)] \le \mathbb{E}[f_N].
$$
This is `MeasureTheory.integral_mul_upcrossingsBefore_le_integral` in our formalization.

To prove this, we use the fact that given a non-negative, bounded, predictable process $(C_n)$
(i.e. $(C_{n + 1})$ is strongly adapted),
$(C \bullet f)_n := \sum_{k \le n} C_{k + 1}(f_{k + 1} - f_k)$ is a submartingale if $(f_n)$ is.

Define $C_n := \sum_{k \le n} \mathbf{1}_{[\sigma_k, \tau_{k + 1})}(n)$. It is easy to see that
$(1 - C_n)$ is non-negative, bounded and predictable, and hence, given a submartingale $(f_n)$,
$(1 - C) \bullet f$ is also a submartingale. Thus, by the submartingale property,
$0 \le \mathbb{E}[((1 - C) \bullet f)_0] \le \mathbb{E}[((1 - C) \bullet f)_N]$ implying
$$
  \mathbb{E}[(C \bullet f)_N] \le \mathbb{E}[(1 \bullet f)_N] = \mathbb{E}[f_N] - \mathbb{E}[f_0].
$$

Furthermore,
$$
\begin{align}
    (C \bullet f)_N & =
      \sum_{n \le N} \sum_{k \le N} \mathbf{1}_{[\sigma_k, \tau_{k + 1})}(n)(f_{n + 1} - f_n)\\
    & = \sum_{k \le N} \sum_{n \le N} \mathbf{1}_{[\sigma_k, \tau_{k + 1})}(n)(f_{n + 1} - f_n)\\
    & = \sum_{k \le N} (f_{\sigma_k + 1} - f_{\sigma_k} + f_{\sigma_k + 2} - f_{\sigma_k + 1}
      + \cdots + f_{\tau_{k + 1}} - f_{\tau_{k + 1} - 1})\\
    & = \sum_{k \le N} (f_{\tau_{k + 1}} - f_{\sigma_k})
      \ge \sum_{k < U_N(a, b)} (b - a) = (b - a) U_N(a, b)
\end{align}
$$
where the inequality follows since for all $k < U_N(a, b)$,
$f_{\tau_{k + 1}} - f_{\sigma_k} \ge b - a$ while for all $k > U_N(a, b)$,
$f_{\tau_{k + 1}} = f_{\sigma_k} = f_N$ and
$f_{\tau_{U_N(a, b) + 1}} - f_{\sigma_{U_N(a, b)}} = f_N - a \ge 0$. Hence, we have
$$
  (b - a) \mathbb{E}[U_N(a, b)] \le \mathbb{E}[(C \bullet f)_N]
  \le \mathbb{E}[f_N] - \mathbb{E}[f_0] \le \mathbb{E}[f_N],
$$
as required.

To obtain the general case, we simply apply the above to $((f_n - a)^+)_n$.

-/


/-- `lowerCrossingTimeAux a f c N` is the first time `f` reached below `a` after time `c` before
time `N`. -/
/-
**MeasureTheory.lowerCrossingTimeAux** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：lowerCrossingTimeAux [Preorder ι] [InfSet ι] (a : Real) (f : ι -> Ω -> Rea
l) (c N : ι) : Ω -> ι
参数：a : Real；f : ι -> Ω -> Real；c N : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`lowerCrossingTimeAux a f c N` is the first time `f` reached below `a` after tim
e `c` before
time `N`.
-/
noncomputable def lowerCrossingTimeAux [Preorder ι] [InfSet ι] (a : ℝ) (f : ι → Ω → ℝ) (c N : ι) :
    Ω → ι :=
  hittingBtwn f (Set.Iic a) c N

/-- `upperCrossingTime a b f N n` is the first time before time `N`, `f` reaches
above `b` after `f` reached below `a` for the `n - 1`-th time. -/
/-
**MeasureTheory.upperCrossingTime** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：{Ω : Type u_1} → {ι : Type u_2} → [inst : Preorder ι] → [OrderBot ι] → [In
fSet ι] → ℝ → ℝ → (ι → Ω → ℝ) → ι → ℕ → Ω → ι
参数：ι → Ω → ℝ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`upperCrossingTime a b f N n` is the first time before time `N`, `f` reaches
above `b` after `f` reached below `a` for the `n - 1`-th time.
-/
noncomputable def upperCrossingTime [Preorder ι] [OrderBot ι] [InfSet ι] (a b : ℝ) (f : ι → Ω → ℝ)
    (N : ι) : ℕ → Ω → ι
  | 0 => ⊥
  | n + 1 => fun ω =>
    hittingBtwn f (Set.Ici b) (lowerCrossingTimeAux a f (upperCrossingTime a b f N n ω) N ω) N ω

/-- `lowerCrossingTime a b f N n` is the first time before time `N`, `f` reaches
below `a` after `f` reached above `b` for the `n`-th time. -/
/-
**MeasureTheory.lowerCrossingTime** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：lowerCrossingTime [Preorder ι] [OrderBot ι] [InfSet ι] (a b : Real) (f : ι
 -> Ω -> Real) (N : ι) (n : Nat) : Ω -> ι
参数：a b : Real；f : ι -> Ω -> Real；N : ι；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`lowerCrossingTime a b f N n` is the first time before time `N`, `f` reaches
below `a` after `f` reached above `b` for the `n`-th time.
-/
noncomputable def lowerCrossingTime [Preorder ι] [OrderBot ι] [InfSet ι] (a b : ℝ) (f : ι → Ω → ℝ)
    (N : ι) (n : ℕ) : Ω → ι :=
    fun ω => hittingBtwn f (Set.Iic a) (upperCrossingTime a b f N n ω) N ω

section

variable [Preorder ι] [OrderBot ι] [InfSet ι]
variable {a b : ℝ} {f : ι → Ω → ℝ} {N : ι} {n : ℕ} {ω : Ω}

@[simp]
/-
**MeasureTheory.upperCrossingTime_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：upperCrossingTime_zero : upperCrossingTime a b f N 0 = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem upperCrossingTime_zero : upperCrossingTime a b f N 0 = ⊥ :=
  rfl

@[simp]
/-
**MeasureTheory.lowerCrossingTime_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：lowerCrossingTime_zero : lowerCrossingTime a b f N 0 = hittingBtwn f (Set.
Iic a) ⊥ N
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lowerCrossingTime_zero : lowerCrossingTime a b f N 0 = hittingBtwn f (Set.Iic a) ⊥ N :=
  rfl
/-
**MeasureTheory.upperCrossingTime_succ** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：upperCrossingTime_succ : upperCrossingTime a b f N (n + 1) ω = hittingBtwn
 f (Set.Ici b) (lowerCrossingTimeAux a f (upperCrossingTime a b f N n ω) N ω) N 
ω
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.upperCrossingTime.eq_2`：∀ {Ω : Type u_1} {ι : Type u_2} [i
nst : Preorder ι] [inst_1 : OrderBot ι] [inst_2 : InfSet ι] (a b : ℝ) (f : ι → Ω
 → ℝ)   (N : ι) (n : ℕ),  …
-/
theorem upperCrossingTime_succ : upperCrossingTime a b f N (n + 1) ω =
    hittingBtwn f (Set.Ici b)
      (lowerCrossingTimeAux a f (upperCrossingTime a b f N n ω) N ω) N ω := by
  rw [upperCrossingTime]
/-
**MeasureTheory.upperCrossingTime_succ_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：upperCrossingTime_succ_eq (ω : Ω) : upperCrossingTime a b f N (n + 1) ω = 
hittingBtwn f (Set.Ici b) (lowerCrossingTime a b f N n ω) N ω
参数：ω : Ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.upperCrossingTime_succ`：upperCrossingTime_succ : upperCros
singTime a b f N (n + 1) ω = hittingBtwn f (Set.Ici b) (lowerCrossingTimeAux a f
 (upperCrossingTime a b f …
-/
theorem upperCrossingTime_succ_eq (ω : Ω) : upperCrossingTime a b f N (n + 1) ω =
    hittingBtwn f (Set.Ici b) (lowerCrossingTime a b f N n ω) N ω := by
  simp only [upperCrossingTime_succ]
  rfl

end

section ConditionallyCompleteLinearOrderBot

variable [ConditionallyCompleteLinearOrderBot ι]
variable {a b : ℝ} {f : ι → Ω → ℝ} {N : ι} {n m : ℕ} {ω : Ω}

/-
**MeasureTheory.upperCrossingTime_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：upperCrossingTime_le : upperCrossingTime a b f N n ω <= N
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.upperCrossingTime_succ`：upperCrossingTime_succ : upperCros
singTime a b f N (n + 1) ω = hittingBtwn f (Set.Ici b) (lowerCrossingTimeAux a f
 (upperCrossingTime a b f …
-/
theorem upperCrossingTime_le : upperCrossingTime a b f N n ω ≤ N := by
  cases n
  · simp only [upperCrossingTime_zero, Pi.bot_apply, bot_le]
  · simp only [upperCrossingTime_succ, hittingBtwn_le]

@[simp]
/-
**MeasureTheory.upperCrossingTime_zero'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：upperCrossingTime_zero' : upperCrossingTime a b f ⊥ n ω = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `MeasureTheory.upperCrossingTime_le`：upperCrossingTime_le : upperCrossing
Time a b f N n ω <= N
-/
theorem upperCrossingTime_zero' : upperCrossingTime a b f ⊥ n ω = ⊥ :=
  eq_bot_iff.2 upperCrossingTime_le
/-
**MeasureTheory.lowerCrossingTime_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：lowerCrossingTime_le : lowerCrossingTime a b f N n ω <= N
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.hittingBtwn_le`：hittingBtwn_le {m : ι} (ω : Ω) : hittingBt
wn u s n m ω <= m
-/
theorem lowerCrossingTime_le : lowerCrossingTime a b f N n ω ≤ N := by
  simp only [lowerCrossingTime, hittingBtwn_le ω]
/-
**MeasureTheory.upperCrossingTime_le_lowerCrossingTime** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory`。
形式化陈述：upperCrossingTime_le_lowerCrossingTime : upperCrossingTime a b f N n ω <= 
lowerCrossingTime a b f N n ω
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.le_hittingBtwn`：le_hittingBtwn {m : ι} (hnm : n <= m) (ω :
 Ω) : n <= hittingBtwn u s n m ω
· 使用定理 `MeasureTheory.upperCrossingTime_le`：upperCrossingTime_le : upperCrossing
Time a b f N n ω <= N
-/
theorem upperCrossingTime_le_lowerCrossingTime :
    upperCrossingTime a b f N n ω ≤ lowerCrossingTime a b f N n ω := by
  simp only [lowerCrossingTime, le_hittingBtwn upperCrossingTime_le ω]
/-
**MeasureTheory.lowerCrossingTime_le_upperCrossingTime_succ** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory`。
形式化陈述：lowerCrossingTime_le_upperCrossingTime_succ : lowerCrossingTime a b f N n 
ω <= upperCrossingTime a b f N (n + 1) ω
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.upperCrossingTime_succ`：upperCrossingTime_succ : upperCros
singTime a b f N (n + 1) ω = hittingBtwn f (Set.Ici b) (lowerCrossingTimeAux a f
 (upperCrossingTime a b f …
· 使用定理 `MeasureTheory.le_hittingBtwn`：le_hittingBtwn {m : ι} (hnm : n <= m) (ω :
 Ω) : n <= hittingBtwn u s n m ω
· 使用定理 `MeasureTheory.lowerCrossingTime_le`：lowerCrossingTime_le : lowerCrossing
Time a b f N n ω <= N
-/
theorem lowerCrossingTime_le_upperCrossingTime_succ :
    lowerCrossingTime a b f N n ω ≤ upperCrossingTime a b f N (n + 1) ω := by
  rw [upperCrossingTime_succ]
  exact le_hittingBtwn lowerCrossingTime_le ω
/-
**MeasureTheory.lowerCrossingTime_mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：lowerCrossingTime_mono (hnm : n <= m) : lowerCrossingTime a b f N n ω <= l
owerCrossingTime a b f N m ω
参数：hnm : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `monotone_nat_of_le_succ`：monotone_nat_of_le_succ {f : Nat -> α} (hf : fo
rall n, f n <= f (n + 1)) : Monotone f
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `MeasureTheory.lowerCrossingTime_le_upperCrossingTime_succ`：lowerCrossing
Time_le_upperCrossingTime_succ : lowerCrossingTime a b f N n ω <= upperCrossingT
ime a b f N (n + 1) ω
· 使用定理 `MeasureTheory.upperCrossingTime_le_lowerCrossingTime`：upperCrossingTime_
le_lowerCrossingTime : upperCrossingTime a b f N n ω <= lowerCrossingTime a b f 
N n ω
-/
theorem lowerCrossingTime_mono (hnm : n ≤ m) :
    lowerCrossingTime a b f N n ω ≤ lowerCrossingTime a b f N m ω := by
  suffices Monotone fun n => lowerCrossingTime a b f N n ω by exact this hnm
  exact monotone_nat_of_le_succ fun n =>
    le_trans lowerCrossingTime_le_upperCrossingTime_succ upperCrossingTime_le_lowerCrossingTime
/-
**MeasureTheory.upperCrossingTime_mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：upperCrossingTime_mono (hnm : n <= m) : upperCrossingTime a b f N n ω <= u
pperCrossingTime a b f N m ω
参数：hnm : n <= m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `monotone_nat_of_le_succ`：monotone_nat_of_le_succ {f : Nat -> α} (hf : fo
rall n, f n <= f (n + 1)) : Monotone f
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `MeasureTheory.upperCrossingTime_le_lowerCrossingTime`：upperCrossingTime_
le_lowerCrossingTime : upperCrossingTime a b f N n ω <= lowerCrossingTime a b f 
N n ω
· 使用定理 `MeasureTheory.lowerCrossingTime_le_upperCrossingTime_succ`：lowerCrossing
Time_le_upperCrossingTime_succ : lowerCrossingTime a b f N n ω <= upperCrossingT
ime a b f N (n + 1) ω
-/
theorem upperCrossingTime_mono (hnm : n ≤ m) :
    upperCrossingTime a b f N n ω ≤ upperCrossingTime a b f N m ω := by
  suffices Monotone fun n => upperCrossingTime a b f N n ω by exact this hnm
  exact monotone_nat_of_le_succ fun n =>
    le_trans upperCrossingTime_le_lowerCrossingTime lowerCrossingTime_le_upperCrossingTime_succ

end ConditionallyCompleteLinearOrderBot

variable {a b : ℝ} {f : ℕ → Ω → ℝ} {N : ℕ} {n m : ℕ} {ω : Ω}

/-
**MeasureTheory.stoppedValue_lowerCrossingTime** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：stoppedValue_lowerCrossingTime (h : lowerCrossingTime a b f N n ω != N) : 
stoppedValue f (fun ω => (lowerCrossingTime a b f N n ω : Nat)) ω <= a
参数：h : lowerCrossingTime a b f N n ω != N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.hittingBtwn_le_iff_of_lt`：hittingBtwn_le_iff_of_lt [WellFo
undedLT ι] {m : ι} (i : ι) (hi : i < m) : hittingBtwn u s n m ω <= i ↔ exists j 
in Set.Icc n i, u j ω in s
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `MeasureTheory.lowerCrossingTime_le`：lowerCrossingTime_le : lowerCrossing
Time a b f N n ω <= N
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.stoppedValue_hittingBtwn_mem`：stoppedValue_hittingBtwn_mem
 [ConditionallyCompleteLinearOrder ι] [WellFoundedLT ι] {u : ι -> Ω -> β} {s : S
et β} {n m : ι} {ω : Ω} (h : exi…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem stoppedValue_lowerCrossingTime (h : lowerCrossingTime a b f N n ω ≠ N) :
    stoppedValue f (fun ω ↦ (lowerCrossingTime a b f N n ω : ℕ)) ω ≤ a := by
  obtain ⟨j, hj₁, hj₂⟩ :=
    (hittingBtwn_le_iff_of_lt _ (lt_of_le_of_ne lowerCrossingTime_le h)).1 le_rfl
  exact stoppedValue_hittingBtwn_mem ⟨j, ⟨hj₁.1, le_trans hj₁.2 lowerCrossingTime_le⟩, hj₂⟩
/-
**MeasureTheory.stoppedValue_upperCrossingTime** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：stoppedValue_upperCrossingTime (h : upperCrossingTime a b f N (n + 1) ω !=
 N) : b <= stoppedValue f (fun ω => (upperCrossingTime a b f N (n + 1) ω : Nat))
 ω
参数：h : upperCrossingTime a b f N (n + 1) ω != N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.hittingBtwn_le_iff_of_lt`：hittingBtwn_le_iff_of_lt [WellFo
undedLT ι] {m : ι} (i : ι) (hi : i < m) : hittingBtwn u s n m ω <= i ↔ exists j 
in Set.Icc n i, u j ω in s
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `MeasureTheory.upperCrossingTime_le`：upperCrossingTime_le : upperCrossing
Time a b f N n ω <= N
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.stoppedValue_hittingBtwn_mem`：stoppedValue_hittingBtwn_mem
 [ConditionallyCompleteLinearOrder ι] [WellFoundedLT ι] {u : ι -> Ω -> β} {s : S
et β} {n m : ι} {ω : Ω} (h : exi…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.hittingBtwn_le`：hittingBtwn_le {m : ι} (ω : Ω) : hittingBt
wn u s n m ω <= m
-/
theorem stoppedValue_upperCrossingTime (h : upperCrossingTime a b f N (n + 1) ω ≠ N) :
    b ≤ stoppedValue f (fun ω ↦ (upperCrossingTime a b f N (n + 1) ω : ℕ)) ω := by
  obtain ⟨j, hj₁, hj₂⟩ :=
    (hittingBtwn_le_iff_of_lt _ (lt_of_le_of_ne upperCrossingTime_le h)).1 le_rfl
  exact stoppedValue_hittingBtwn_mem ⟨j, ⟨hj₁.1, le_trans hj₁.2 (hittingBtwn_le _)⟩, hj₂⟩
/-
**MeasureTheory.upperCrossingTime_lt_lowerCrossingTime** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory`。
形式化陈述：upperCrossingTime_lt_lowerCrossingTime (hab : a < b) (hn : lowerCrossingTi
me a b f N (n + 1) ω != N) : upperCrossingTime a b f N (n + 1) ω < lowerCrossing
Time a b f N (n + 1) ω
参数：hab : a < b；hn : lowerCrossingTime a b f N (n + 1) ω != N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `MeasureTheory.upperCrossingTime_le_lowerCrossingTime`：upperCrossingTime_
le_lowerCrossingTime : upperCrossingTime a b f N n ω <= lowerCrossingTime a b f 
N n ω
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.stoppedValue_upperCrossingTime`：stoppedValue_upperCrossing
Time (h : upperCrossingTime a b f N (n + 1) ω != N) : b <= stoppedValue f (fun ω
 => (upperCrossingTime a b f N (n …
· 使用定理 `MeasureTheory.stoppedValue_lowerCrossingTime`：stoppedValue_lowerCrossing
Time (h : lowerCrossingTime a b f N n ω != N) : stoppedValue f (fun ω => (lowerC
rossingTime a b f N n ω : Nat)) ω …
-/
theorem upperCrossingTime_lt_lowerCrossingTime (hab : a < b)
    (hn : lowerCrossingTime a b f N (n + 1) ω ≠ N) :
    upperCrossingTime a b f N (n + 1) ω < lowerCrossingTime a b f N (n + 1) ω := by
  refine lt_of_le_of_ne upperCrossingTime_le_lowerCrossingTime fun h =>
    not_le.2 hab <| le_trans ?_ (stoppedValue_lowerCrossingTime hn)
  simp only [stoppedValue]
  rw [← h]
  exact stoppedValue_upperCrossingTime (h.symm ▸ hn)
/-
**MeasureTheory.lowerCrossingTime_lt_upperCrossingTime** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory`。
形式化陈述：lowerCrossingTime_lt_upperCrossingTime (hab : a < b) (hn : upperCrossingTi
me a b f N (n + 1) ω != N) : lowerCrossingTime a b f N n ω < upperCrossingTime a
 b f N (n + 1) ω
参数：hab : a < b；hn : upperCrossingTime a b f N (n + 1) ω != N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `MeasureTheory.lowerCrossingTime_le_upperCrossingTime_succ`：lowerCrossing
Time_le_upperCrossingTime_succ : lowerCrossingTime a b f N n ω <= upperCrossingT
ime a b f N (n + 1) ω
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MeasureTheory.stoppedValue_upperCrossingTime`：stoppedValue_upperCrossing
Time (h : upperCrossingTime a b f N (n + 1) ω != N) : b <= stoppedValue f (fun ω
 => (upperCrossingTime a b f N (n …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.stoppedValue_lowerCrossingTime`：stoppedValue_lowerCrossing
Time (h : lowerCrossingTime a b f N n ω != N) : stoppedValue f (fun ω => (lowerC
rossingTime a b f N n ω : Nat)) ω …
-/
theorem lowerCrossingTime_lt_upperCrossingTime (hab : a < b)
    (hn : upperCrossingTime a b f N (n + 1) ω ≠ N) :
    lowerCrossingTime a b f N n ω < upperCrossingTime a b f N (n + 1) ω := by
  refine lt_of_le_of_ne lowerCrossingTime_le_upperCrossingTime_succ fun h =>
    not_le.2 hab <| le_trans (stoppedValue_upperCrossingTime hn) ?_
  simp only [stoppedValue]
  rw [← h]
  exact stoppedValue_lowerCrossingTime (h.symm ▸ hn)
/-
**MeasureTheory.upperCrossingTime_lt_succ** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：upperCrossingTime_lt_succ (hab : a < b) (hn : upperCrossingTime a b f N (n
 + 1) ω != N) : upperCrossingTime a b f N n ω < upperCrossingTime a b f N (n + 1
) ω
参数：hab : a < b；hn : upperCrossingTime a b f N (n + 1) ω != N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `MeasureTheory.upperCrossingTime_le_lowerCrossingTime`：upperCrossingTime_
le_lowerCrossingTime : upperCrossingTime a b f N n ω <= lowerCrossingTime a b f 
N n ω
· 使用定理 `MeasureTheory.lowerCrossingTime_lt_upperCrossingTime`：lowerCrossingTime_
lt_upperCrossingTime (hab : a < b) (hn : upperCrossingTime a b f N (n + 1) ω != 
N) : lowerCrossingTime a b f N n ω < upper…
-/
theorem upperCrossingTime_lt_succ (hab : a < b) (hn : upperCrossingTime a b f N (n + 1) ω ≠ N) :
    upperCrossingTime a b f N n ω < upperCrossingTime a b f N (n + 1) ω :=
  lt_of_le_of_lt upperCrossingTime_le_lowerCrossingTime
    (lowerCrossingTime_lt_upperCrossingTime hab hn)
/-
**MeasureTheory.lowerCrossingTime_stabilize** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：lowerCrossingTime_stabilize (hnm : n <= m) (hn : lowerCrossingTime a b f N
 n ω = N) : lowerCrossingTime a b f N m ω = N
参数：hnm : n <= m；hn : lowerCrossingTime a b f N n ω = N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasureTheory.lowerCrossingTime_le`：lowerCrossingTime_le : lowerCrossing
Time a b f N n ω <= N
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.lowerCrossingTime_mono`：lowerCrossingTime_mono (hnm : n <=
 m) : lowerCrossingTime a b f N n ω <= lowerCrossingTime a b f N m ω
-/
theorem lowerCrossingTime_stabilize (hnm : n ≤ m) (hn : lowerCrossingTime a b f N n ω = N) :
    lowerCrossingTime a b f N m ω = N :=
  le_antisymm lowerCrossingTime_le (le_trans (le_of_eq hn.symm) (lowerCrossingTime_mono hnm))
/-
**MeasureTheory.upperCrossingTime_stabilize** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：upperCrossingTime_stabilize (hnm : n <= m) (hn : upperCrossingTime a b f N
 n ω = N) : upperCrossingTime a b f N m ω = N
参数：hnm : n <= m；hn : upperCrossingTime a b f N n ω = N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasureTheory.upperCrossingTime_le`：upperCrossingTime_le : upperCrossing
Time a b f N n ω <= N
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.upperCrossingTime_mono`：upperCrossingTime_mono (hnm : n <=
 m) : upperCrossingTime a b f N n ω <= upperCrossingTime a b f N m ω
-/
theorem upperCrossingTime_stabilize (hnm : n ≤ m) (hn : upperCrossingTime a b f N n ω = N) :
    upperCrossingTime a b f N m ω = N :=
  le_antisymm upperCrossingTime_le (le_trans (le_of_eq hn.symm) (upperCrossingTime_mono hnm))
/-
**MeasureTheory.lowerCrossingTime_stabilize'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：lowerCrossingTime_stabilize' (hnm : n <= m) (hn : N <= lowerCrossingTime a
 b f N n ω) : lowerCrossingTime a b f N m ω = N
参数：hnm : n <= m；hn : N <= lowerCrossingTime a b f N n ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.lowerCrossingTime_stabilize`：lowerCrossingTime_stabilize (
hnm : n <= m) (hn : lowerCrossingTime a b f N n ω = N) : lowerCrossingTime a b f
 N m ω = N
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasureTheory.lowerCrossingTime_le`：lowerCrossingTime_le : lowerCrossing
Time a b f N n ω <= N
-/
theorem lowerCrossingTime_stabilize' (hnm : n ≤ m) (hn : N ≤ lowerCrossingTime a b f N n ω) :
    lowerCrossingTime a b f N m ω = N :=
  lowerCrossingTime_stabilize hnm (le_antisymm lowerCrossingTime_le hn)
/-
**MeasureTheory.upperCrossingTime_stabilize'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：upperCrossingTime_stabilize' (hnm : n <= m) (hn : N <= upperCrossingTime a
 b f N n ω) : upperCrossingTime a b f N m ω = N
参数：hnm : n <= m；hn : N <= upperCrossingTime a b f N n ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.upperCrossingTime_stabilize`：upperCrossingTime_stabilize (
hnm : n <= m) (hn : upperCrossingTime a b f N n ω = N) : upperCrossingTime a b f
 N m ω = N
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasureTheory.upperCrossingTime_le`：upperCrossingTime_le : upperCrossing
Time a b f N n ω <= N
-/
theorem upperCrossingTime_stabilize' (hnm : n ≤ m) (hn : N ≤ upperCrossingTime a b f N n ω) :
    upperCrossingTime a b f N m ω = N :=
  upperCrossingTime_stabilize hnm (le_antisymm upperCrossingTime_le hn)

-- `upperCrossingTime_bound_eq` provides an explicit bound
/-
**MeasureTheory.exists_upperCrossingTime_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：exists_upperCrossingTime_eq (f : Nat -> Ω -> Real) (N : Nat) (ω : Ω) (hab 
: a < b) : exists n, upperCrossingTime a b f N n ω = N
参数：f : Nat -> Ω -> Real；N : Nat；ω : Ω；hab : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `strictMono_nat_of_lt_succ`：strictMono_nat_of_lt_succ {f : Nat -> α} (hf 
: forall n, f n < f (n + 1)) : StrictMono f
· 使用定理 `MeasureTheory.upperCrossingTime_lt_succ`：upperCrossingTime_lt_succ (hab 
: a < b) (hn : upperCrossingTime a b f N (n + 1) ω != N) : upperCrossingTime a b
 f N n ω < upperCrossingTime …
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `StrictMono.id_le`：StrictMono.id_le [WellFoundedLT β] {f : β -> β} (hf : 
StrictMono f) : id <= f
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `MeasureTheory.upperCrossingTime_le`：upperCrossingTime_le : upperCrossing
Time a b f N n ω <= N
-/
theorem exists_upperCrossingTime_eq (f : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) (hab : a < b) :
    ∃ n, upperCrossingTime a b f N n ω = N := by
  by_contra! h
  have : StrictMono fun n => upperCrossingTime a b f N n ω :=
    strictMono_nat_of_lt_succ fun n => upperCrossingTime_lt_succ hab (h _)
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ :
      ∃ (m : _) (_ : m ∈ Set.range fun n => upperCrossingTime a b f N n ω), N < m :=
    ⟨upperCrossingTime a b f N (N + 1) ω, ⟨N + 1, rfl⟩,
      lt_of_lt_of_le N.lt_succ_self (StrictMono.id_le this (N + 1))⟩
  exact not_le.2 hk upperCrossingTime_le
/-
**MeasureTheory.upperCrossingTime_lt_bddAbove** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：upperCrossingTime_lt_bddAbove (hab : a < b) : BddAbove {n | upperCrossingT
ime a b f N n ω < N}
参数：hab : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.exists_upperCrossingTime_eq`：exists_upperCrossingTime_eq (
f : Nat -> Ω -> Real) (N : Nat) (ω : Ω) (hab : a < b) : exists n, upperCrossingT
ime a b f N n ω = N
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.upperCrossingTime_stabilize`：upperCrossingTime_stabilize (
hnm : n <= m) (hn : upperCrossingTime a b f N n ω = N) : upperCrossingTime a b f
 N m ω = N
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
-/
theorem upperCrossingTime_lt_bddAbove (hab : a < b) :
    BddAbove {n | upperCrossingTime a b f N n ω < N} := by
  obtain ⟨k, hk⟩ := exists_upperCrossingTime_eq f N ω hab
  refine ⟨k, fun n (hn : upperCrossingTime a b f N n ω < N) => ?_⟩
  by_contra hn'
  exact hn.ne (upperCrossingTime_stabilize (not_le.1 hn').le hk)
/-
**MeasureTheory.upperCrossingTime_lt_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：upperCrossingTime_lt_nonempty (hN : 0 < N) : {n | upperCrossingTime a b f 
N n ω < N}.Nonempty
参数：hN : 0 < N。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem upperCrossingTime_lt_nonempty (hN : 0 < N) :
    {n | upperCrossingTime a b f N n ω < N}.Nonempty :=
  ⟨0, hN⟩
/-
**MeasureTheory.upperCrossingTime_bound_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：upperCrossingTime_bound_eq (f : Nat -> Ω -> Real) (N : Nat) (ω : Ω) (hab :
 a < b) : upperCrossingTime a b f N N ω = N
参数：f : Nat -> Ω -> Real；N : Nat；ω : Ω；hab : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.exists_upperCrossingTime_eq`：exists_upperCrossingTime_eq (
f : Nat -> Ω -> Real) (N : Nat) (ω : Ω) (hab : a < b) : exists n, upperCrossingT
ime a b f N n ω = N
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasureTheory.upperCrossingTime_le`：upperCrossingTime_le : upperCrossing
Time a b f N n ω <= N
· 使用定理 `strictMonoOn_Iic_of_lt_succ`：strictMonoOn_Iic_of_lt_succ [SuccOrder α] [
IsSuccArchimedean α] {n : α} (hψ : forall m, m < n -> ψ m < ψ (succ m)) : Strict
MonoOn ψ (Set.Iic…
· 使用定理 `Nat.instIsSuccArchimedean`：IsSuccArchimedean ℕ
· 使用定理 `MeasureTheory.upperCrossingTime_lt_succ`：upperCrossingTime_lt_succ (hab 
: a < b) (hn : upperCrossingTime a b f N (n + 1) ω != N) : upperCrossingTime a b
 f N n ω < upperCrossingTime …
· 使用定理 `Nat.find_min`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) {
m : ℕ}, m < Nat.find H → ¬p m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.lt_pred_iff`：∀ {n : ℕ} {m : ℕ}, n < m.pred ↔ n.succ < m
· 使用定理 `StrictMonoOn.Iic_id_le`：StrictMonoOn.Iic_id_le [SuccOrder α] [IsSuccArch
imedean α] [OrderBot α] {n : α} {φ : α -> α} (hφ : StrictMonoOn φ (Set.Iic n)) :
 forall m <=…
· 使用定理 `Nat.le_sub_one_of_lt`：∀ {a b : ℕ}, a < b → a ≤ b - 1
· 使用定理 `MeasureTheory.upperCrossingTime_stabilize`：upperCrossingTime_stabilize (
hnm : n <= m) (hn : upperCrossingTime a b f N n ω = N) : upperCrossingTime a b f
 N m ω = N
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
-/
theorem upperCrossingTime_bound_eq (f : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) (hab : a < b) :
    upperCrossingTime a b f N N ω = N := by
  by_cases hN' : N < Nat.find (exists_upperCrossingTime_eq f N ω hab)
  · refine le_antisymm upperCrossingTime_le ?_
    have hmono : StrictMonoOn (fun n => upperCrossingTime a b f N n ω)
        (Set.Iic (Nat.find (exists_upperCrossingTime_eq f N ω hab)).pred) := by
      refine strictMonoOn_Iic_of_lt_succ fun m hm => upperCrossingTime_lt_succ hab ?_
      rw [Nat.lt_pred_iff] at hm
      convert! Nat.find_min _ hm
    convert! StrictMonoOn.Iic_id_le hmono N (Nat.le_sub_one_of_lt hN')
  · rw [not_lt] at hN'
    exact upperCrossingTime_stabilize hN' (Nat.find_spec (exists_upperCrossingTime_eq f N ω hab))
/-
**MeasureTheory.upperCrossingTime_eq_of_bound_le** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：upperCrossingTime_eq_of_bound_le (hab : a < b) (hn : N <= n) : upperCrossi
ngTime a b f N n ω = N
参数：hab : a < b；hn : N <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasureTheory.upperCrossingTime_le`：upperCrossingTime_le : upperCrossing
Time a b f N n ω <= N
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.upperCrossingTime_bound_eq`：upperCrossingTime_bound_eq (f 
: Nat -> Ω -> Real) (N : Nat) (ω : Ω) (hab : a < b) : upperCrossingTime a b f N 
N ω = N
· 使用定理 `MeasureTheory.upperCrossingTime_mono`：upperCrossingTime_mono (hnm : n <=
 m) : upperCrossingTime a b f N n ω <= upperCrossingTime a b f N m ω
-/
theorem upperCrossingTime_eq_of_bound_le (hab : a < b) (hn : N ≤ n) :
    upperCrossingTime a b f N n ω = N :=
  le_antisymm upperCrossingTime_le
    (le_trans (upperCrossingTime_bound_eq f N ω hab).symm.le (upperCrossingTime_mono hn))

variable {ℱ : Filtration ℕ m0}
/-
**MeasureTheory.StronglyAdapted.isStoppingTime_crossing** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.StronglyAdapted`。
形式化陈述：∀ {Ω : Type u_1} {m0 : MeasurableSpace Ω} {a b : ℝ} {f : ℕ → Ω → ℝ} {N n :
 ℕ} {ℱ : MeasureTheory.Filtration ℕ m0},   MeasureTheory.StronglyAdapted ℱ f →  
   (MeasureTheory.IsStoppingTime ℱ fun ω => ↑(MeasureTheory.upperCrossingTime a 
b f N n ω)) ∧       MeasureTheory.IsStoppingTime ℱ fun ω => ↑(MeasureTheory.lowe
rCrossingTime a b f N n ω)
参数：MeasureTheory.IsStoppingTime ℱ fun ω => ↑(MeasureTheory.upperCrossingTime a b
 f N n ω)；MeasureTheory.lowerCrossingTime a b f N n ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.isStoppingTime_const`：isStoppingTime_const [Preorder ι] (f
 : Filtration ι m) (i : ι) : IsStoppingTime f fun _ => i
· 使用定理 `MeasureTheory.Adapted.isStoppingTime_hittingBtwn`：∀ {Ω : Type u_1} {β : 
Type u_2} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : ConditionallyCompleteLi
nearOrder ι]   [WellFoundedLT ι] [Coun…
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasureTheory.StronglyAdapted.adapted`：∀ {Ω : Type u_1} {ι : Type u_2} {
m : MeasurableSpace Ω} [inst : Preorder ι] {f : MeasureTheory.Filtration ι m}   
{β : ι → Type u_3} [inst_1 …
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `measurableSet_Iic`：measurableSet_Iic [ClosedIicTopology α] : MeasurableS
et (Iic a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.upperCrossingTime_succ_eq`：upperCrossingTime_succ_eq (ω : 
Ω) : upperCrossingTime a b f N (n + 1) ω = hittingBtwn f (Set.Ici b) (lowerCross
ingTime a b f N n ω) N ω
· 使用定理 `MeasureTheory.Adapted.isStoppingTime_hittingBtwn_isStoppingTime`：∀ {Ω : 
Type u_1} {β : Type u_2} {ι : Type u_3} {m : MeasurableSpace Ω} [inst : Conditio
nallyCompleteLinearOrder ι]   [WellFoundedLT ι] [Coun…
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `measurableSet_Ici`：measurableSet_Ici [ClosedIciTopology α] : MeasurableS
et (Ici a)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
-/
theorem StronglyAdapted.isStoppingTime_crossing (hf : StronglyAdapted ℱ f) :
    IsStoppingTime ℱ (fun ω ↦ (upperCrossingTime a b f N n ω : ℕ)) ∧
      IsStoppingTime ℱ (fun ω ↦ (lowerCrossingTime a b f N n ω : ℕ)) := by
  induction n with
  | zero =>
    refine ⟨isStoppingTime_const _ 0, ?_⟩
    simp only [lowerCrossingTime_zero, Nat.bot_eq_zero]
    exact hf.adapted.isStoppingTime_hittingBtwn measurableSet_Iic
  | succ k ih =>
    have : IsStoppingTime ℱ (fun ω ↦ (upperCrossingTime a b f N (k + 1) ω : ℕ)) := by
      intro n
      simp_rw [upperCrossingTime_succ_eq]
      refine hf.adapted.isStoppingTime_hittingBtwn_isStoppingTime ih.2 ?_ measurableSet_Ici _
      simp [lowerCrossingTime_le]
    refine ⟨this, fun n ↦ ?_⟩
    refine hf.adapted.isStoppingTime_hittingBtwn_isStoppingTime this ?_ measurableSet_Iic _
    simp [upperCrossingTime_le]
/-
**MeasureTheory.StronglyAdapted.isStoppingTime_upperCrossingTime** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory.StronglyAdapted`。
形式化陈述：∀ {Ω : Type u_1} {m0 : MeasurableSpace Ω} {a b : ℝ} {f : ℕ → Ω → ℝ} {N n :
 ℕ} {ℱ : MeasureTheory.Filtration ℕ m0},   MeasureTheory.StronglyAdapted ℱ f →  
   MeasureTheory.IsStoppingTime ℱ fun ω => ↑(MeasureTheory.upperCrossingTime a b
 f N n ω)
参数：MeasureTheory.upperCrossingTime a b f N n ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.StronglyAdapted.isStoppingTime_crossing`：∀ {Ω : Type u_1} 
{m0 : MeasurableSpace Ω} {a b : ℝ} {f : ℕ → Ω → ℝ} {N n : ℕ} {ℱ : MeasureTheory.
Filtration ℕ m0},   MeasureTheory.StronglyA…
-/
theorem StronglyAdapted.isStoppingTime_upperCrossingTime (hf : StronglyAdapted ℱ f) :
    IsStoppingTime ℱ (fun ω ↦ (upperCrossingTime a b f N n ω : ℕ)) :=
  hf.isStoppingTime_crossing.1
/-
**MeasureTheory.StronglyAdapted.isStoppingTime_lowerCrossingTime** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory.StronglyAdapted`。
形式化陈述：∀ {Ω : Type u_1} {m0 : MeasurableSpace Ω} {a b : ℝ} {f : ℕ → Ω → ℝ} {N n :
 ℕ} {ℱ : MeasureTheory.Filtration ℕ m0},   MeasureTheory.StronglyAdapted ℱ f →  
   MeasureTheory.IsStoppingTime ℱ fun ω => ↑(MeasureTheory.lowerCrossingTime a b
 f N n ω)
参数：MeasureTheory.lowerCrossingTime a b f N n ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.StronglyAdapted.isStoppingTime_crossing`：∀ {Ω : Type u_1} 
{m0 : MeasurableSpace Ω} {a b : ℝ} {f : ℕ → Ω → ℝ} {N n : ℕ} {ℱ : MeasureTheory.
Filtration ℕ m0},   MeasureTheory.StronglyA…
-/
theorem StronglyAdapted.isStoppingTime_lowerCrossingTime (hf : StronglyAdapted ℱ f) :
    IsStoppingTime ℱ (fun ω ↦ (lowerCrossingTime a b f N n ω : ℕ)) :=
  hf.isStoppingTime_crossing.2

/-- `upcrossingStrat a b f N n` is 1 if `n` is between a consecutive pair of lower and upper
crossings and is 0 otherwise. `upcrossingStrat` is shifted by one index so that it is adapted
rather than predictable. -/
/-
**MeasureTheory.upcrossingStrat** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：upcrossingStrat (a b : Real) (f : Nat -> Ω -> Real) (N n : Nat) (ω : Ω) : 
Real
参数：a b : Real；f : Nat -> Ω -> Real；N n : Nat；ω : Ω。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`upcrossingStrat a b f N n` is 1 if `n` is between a consecutive pair of lower a
nd upper
crossings and is 0 otherwise. `upcrossingStrat` is shifted by one index so that 
it is adapted
rather than predictable.
-/
noncomputable def upcrossingStrat (a b : ℝ) (f : ℕ → Ω → ℝ) (N n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range N,
    (Set.Ico (lowerCrossingTime a b f N k ω) (upperCrossingTime a b f N (k + 1) ω)).indicator 1 n
/-
**MeasureTheory.upcrossingStrat_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：upcrossingStrat_nonneg : 0 <= upcrossingStrat a b f N n ω
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Set.indicator_nonneg`：∀ {α : Type u_2} {M : Type u_3} [inst : Preorder M
] [inst_1 : Zero M] {s : Set α} {f : α → M},   (∀ a ∈ s, 0 ≤ f a) → ∀ (a : α), 0
 ≤ s.indic…
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
-/
theorem upcrossingStrat_nonneg : 0 ≤ upcrossingStrat a b f N n ω :=
  Finset.sum_nonneg fun _ _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _
/-
**MeasureTheory.upcrossingStrat_le_one** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：upcrossingStrat_le_one : upcrossingStrat a b f N n ω <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.upcrossingStrat.eq_1`：∀ {Ω : Type u_1} (a b : ℝ) (f : ℕ → 
Ω → ℝ) (N n : ℕ) (ω : Ω),   MeasureTheory.upcrossingStrat a b f N n ω =     ∑ k 
∈ Finset.range N,       …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.indicator_biUnion_apply`：∀ {ι : Type u_1} {κ : Type u_2} {β : Typ
e u_4} [inst : AddCommMonoid β] (s : Finset ι) (t : ι → Set κ) {f : κ → β},   (↑
s).PairwiseDisjoint …
· 使用引理 `lt_or_gt_of_ne`：lt_or_gt_of_ne (h : a != b) : a < b ∨ b < a
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `MeasureTheory.upperCrossingTime_mono`：upperCrossingTime_mono (hnm : n <=
 m) : upperCrossingTime a b f N n ω <= upperCrossingTime a b f N m ω
· 使用定理 `Nat.succ_le_succ`：∀ {n m : ℕ}, n ≤ m → n.succ ≤ m.succ
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用定理 `MeasureTheory.lowerCrossingTime_mono`：lowerCrossingTime_mono (hnm : n <=
 m) : lowerCrossingTime a b f N n ω <= lowerCrossingTime a b f N m ω
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `MeasureTheory.upperCrossingTime_le_lowerCrossingTime`：upperCrossingTime_
le_lowerCrossingTime : upperCrossingTime a b f N n ω <= lowerCrossingTime a b f 
N n ω
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用引理 `min_eq_right`：min_eq_right (h : b <= a) : min a b = b
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用定理 `Set.indicator_le_self'`：∀ {α : Type u_2} {M : Type u_3} [inst : Preorder
 M] [inst_1 : Zero M] {s : Set α} {f : α → M},   (∀ x ∉ s, 0 ≤ f x) → s.indicato
r f ≤ f
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
-/
theorem upcrossingStrat_le_one : upcrossingStrat a b f N n ω ≤ 1 := by
  rw [upcrossingStrat, ← Finset.indicator_biUnion_apply]
  · exact Set.indicator_le_self' (fun _ _ => zero_le_one) _
  intro i _ j _ hij
  simp only [Set.Ico_disjoint_Ico]
  obtain hij' | hij' := lt_or_gt_of_ne hij
  · rw [min_eq_left (upperCrossingTime_mono (Nat.succ_le_succ hij'.le) :
      upperCrossingTime a b f N _ ω ≤ upperCrossingTime a b f N _ ω),
      max_eq_right (lowerCrossingTime_mono hij'.le :
        lowerCrossingTime a b f N _ _ ≤ lowerCrossingTime _ _ _ _ _ _)]
    refine le_trans upperCrossingTime_le_lowerCrossingTime
      (lowerCrossingTime_mono (Nat.succ_le_of_lt hij'))
  · rw [min_eq_right (upperCrossingTime_mono (Nat.succ_le_succ hij'.le) :
      upperCrossingTime a b f N _ ω ≤ upperCrossingTime a b f N _ ω),
      max_eq_left (lowerCrossingTime_mono hij'.le :
        lowerCrossingTime a b f N _ _ ≤ lowerCrossingTime _ _ _ _ _ _)]
    refine le_trans upperCrossingTime_le_lowerCrossingTime
      (lowerCrossingTime_mono (Nat.succ_le_of_lt hij'))
/-
**MeasureTheory.StronglyAdapted.upcrossingStrat** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.StronglyAdapted`。
形式化陈述：∀ {Ω : Type u_1} {m0 : MeasurableSpace Ω} {a b : ℝ} {f : ℕ → Ω → ℝ} {N : ℕ
} {ℱ : MeasureTheory.Filtration ℕ m0},   MeasureTheory.StronglyAdapted ℱ f → Mea
sureTheory.StronglyAdapted ℱ (MeasureTheory.upcrossingStrat a b f N)
参数：MeasureTheory.upcrossingStrat a b f N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.stronglyMeasurable_fun_sum`：∀ {α : Type u_1} {M : Type u_5} [inst
 : AddCommMonoid M] [inst_1 : TopologicalSpace M] [ContinuousAdd M]   {m : Measu
rableSpace α} {ι : Type…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.StronglyMeasurable.indicator`：∀ {α : Type u_1} {β : Type u
_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Ze
ro β],   MeasureTheory.StronglyM…
· 使用定理 `MeasureTheory.stronglyMeasurable_const`：stronglyMeasurable_const {b : β}
 : StronglyMeasurable fun _ : α => b
· 使用定理 `MeasureTheory.StronglyAdapted.isStoppingTime_lowerCrossingTime`：∀ {Ω : T
ype u_1} {m0 : MeasurableSpace Ω} {a b : ℝ} {f : ℕ → Ω → ℝ} {N n : ℕ} {ℱ : Measu
reTheory.Filtration ℕ m0},   MeasureTheory.StronglyA…
· 使用定理 `MeasureTheory.StronglyAdapted.isStoppingTime_upperCrossingTime`：∀ {Ω : T
ype u_1} {m0 : MeasurableSpace Ω} {a b : ℝ} {f : ℕ → Ω → ℝ} {N n : ℕ} {ℱ : Measu
reTheory.Filtration ℕ m0},   MeasureTheory.StronglyA…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
-/
theorem StronglyAdapted.upcrossingStrat (hf : StronglyAdapted ℱ f) :
    StronglyAdapted ℱ (upcrossingStrat a b f N) := by
  intro n
  change StronglyMeasurable[ℱ n] fun ω =>
    ∑ k ∈ Finset.range N, ({n | lowerCrossingTime a b f N k ω ≤ n} ∩
      {n | n < upperCrossingTime a b f N (k + 1) ω}).indicator 1 n
  refine Finset.stronglyMeasurable_fun_sum _ fun i _ =>
    stronglyMeasurable_const.indicator ?_
  have hl := hf.isStoppingTime_lowerCrossingTime (a := a) (b := b) (N := N) (n := i) n
  have hu := hf.isStoppingTime_upperCrossingTime (a := a) (b := b) (N := N) (n := i + 1) n
  simp only [ENat.some_eq_natCast, Nat.cast_le] at hl hu
  simp_rw [← not_le]
  exact hl.inter hu.compl
/-
**MeasureTheory.Submartingale.sum_upcrossingStrat_mul** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.Submartingale`。
形式化陈述：∀ {Ω : Type u_1} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {f
 : ℕ → Ω → ℝ}   {ℱ : MeasureTheory.Filtration ℕ m0} [MeasureTheory.IsFiniteMeasu
re μ],   MeasureTheory.Submartingale f ℱ μ →     ∀ (a b : ℝ) (N : ℕ),       Meas
ureTheory.Submartingale         (fun n => ∑ k ∈ Finset.range n, MeasureTheory.up
crossingStrat a b f N k * (f (k + 1) - f k)) ℱ μ
参数：a b : ℝ；N : ℕ；fun n => ∑ k ∈ Finset.range n, MeasureTheory.upcrossingStrat a 
b f N k * (f (k + 1) - f k)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Submartingale.sum_mul_sub`：∀ {Ω : Type u_1} {m0 : Measurab
leSpace Ω} {μ : MeasureTheory.Measure Ω} {𝒢 : MeasureTheory.Filtration ℕ m0}   [
MeasureTheory.IsFiniteMeasure…
· 使用定理 `MeasureTheory.StronglyAdapted.upcrossingStrat`：∀ {Ω : Type u_1} {m0 : Me
asurableSpace Ω} {a b : ℝ} {f : ℕ → Ω → ℝ} {N : ℕ} {ℱ : MeasureTheory.Filtration
 ℕ m0},   MeasureTheory.StronglyAda…
· 使用定理 `MeasureTheory.Submartingale.stronglyAdapted`：∀ {Ω : Type u_1} {E : Type 
u_2} {ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureT
heory.Measure Ω} [inst_1 : Normed…
· 使用定理 `MeasureTheory.upcrossingStrat_le_one`：upcrossingStrat_le_one : upcrossin
gStrat a b f N n ω <= 1
· 使用定理 `MeasureTheory.upcrossingStrat_nonneg`：upcrossingStrat_nonneg : 0 <= upcr
ossingStrat a b f N n ω
-/
theorem Submartingale.sum_upcrossingStrat_mul [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (a b : ℝ) (N : ℕ) : Submartingale (fun n : ℕ =>
      ∑ k ∈ Finset.range n, upcrossingStrat a b f N k * (f (k + 1) - f k)) ℱ μ :=
  hf.sum_mul_sub hf.stronglyAdapted.upcrossingStrat (fun _ _ => upcrossingStrat_le_one) fun _ _ =>
    upcrossingStrat_nonneg
/-
**MeasureTheory.Submartingale.sum_sub_upcrossingStrat_mul** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.Submartingale`。
形式化陈述：∀ {Ω : Type u_1} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {f
 : ℕ → Ω → ℝ}   {ℱ : MeasureTheory.Filtration ℕ m0} [MeasureTheory.IsFiniteMeasu
re μ],   MeasureTheory.Submartingale f ℱ μ →     ∀ (a b : ℝ) (N : ℕ),       Meas
ureTheory.Submartingale         (fun n => ∑ k ∈ Finset.range n, (1 - MeasureTheo
ry.upcrossingStrat a b f N k) * (f (k + 1) - f k)) ℱ μ
参数：a b : ℝ；N : ℕ；fun n => ∑ k ∈ Finset.range n, (1 - MeasureTheory.upcrossingStr
at a b f N k) * (f (k + 1) - f k)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Submartingale.sum_mul_sub`：∀ {Ω : Type u_1} {m0 : Measurab
leSpace Ω} {μ : MeasureTheory.Measure Ω} {𝒢 : MeasureTheory.Filtration ℕ m0}   [
MeasureTheory.IsFiniteMeasure…
· 使用定理 `MeasureTheory.StronglyMeasurable.sub`：∀ {α : Type u_1} {β : Type u_2} {f
 g : α → β} {mα : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Sub β
]   [ContinuousSub β],   M…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `MeasureTheory.stronglyAdapted_const`：stronglyAdapted_const {β : Type*} [
TopologicalSpace β] (f : Filtration ι m) (x : β) : StronglyAdapted f fun _ _ => 
x
· 使用定理 `MeasureTheory.StronglyAdapted.upcrossingStrat`：∀ {Ω : Type u_1} {m0 : Me
asurableSpace Ω} {a b : ℝ} {f : ℕ → Ω → ℝ} {N : ℕ} {ℱ : MeasureTheory.Filtration
 ℕ m0},   MeasureTheory.StronglyAda…
· 使用定理 `MeasureTheory.Submartingale.stronglyAdapted`：∀ {Ω : Type u_1} {E : Type 
u_2} {ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureT
heory.Measure Ω} [inst_1 : Normed…
· 使用定理 `sub_le_self`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeft
Mono α] (a : α) {b : α}, 0 ≤ b → a - b ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.upcrossingStrat_nonneg`：upcrossingStrat_nonneg : 0 <= upcr
ossingStrat a b f N n ω
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem Submartingale.sum_sub_upcrossingStrat_mul [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (a b : ℝ) (N : ℕ) : Submartingale (fun n : ℕ =>
      ∑ k ∈ Finset.range n, (1 - upcrossingStrat a b f N k) * (f (k + 1) - f k)) ℱ μ := by
  refine hf.sum_mul_sub
    (fun n => (stronglyAdapted_const ℱ 1 n).sub (hf.stronglyAdapted.upcrossingStrat n))
    (?_ : ∀ n ω, (1 - upcrossingStrat a b f N n) ω ≤ 1) ?_
  · exact fun n ω => sub_le_self _ upcrossingStrat_nonneg
  · intro n ω
    simp [upcrossingStrat_le_one]
/-
**MeasureTheory.Submartingale.sum_mul_upcrossingStrat_le** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.Submartingale`。
形式化陈述：∀ {Ω : Type u_1} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {a
 b : ℝ} {f : ℕ → Ω → ℝ} {N n : ℕ}   {ℱ : MeasureTheory.Filtration ℕ m0} [Measure
Theory.IsFiniteMeasure μ],   MeasureTheory.Submartingale f ℱ μ →     ∫ (x : Ω), 
(∑ k ∈ Finset.range n, MeasureTheory.upcrossingStrat a b f N k * (f (k + 1) - f 
k)) x ∂μ ≤       ∫ (x : Ω), f n x ∂μ - ∫ (x : Ω), f 0 x ∂μ
参数：x : Ω；∑ k ∈ Finset.range n, MeasureTheory.upcrossingStrat a b f N k * (f (k +
 1) - f k)；x : Ω；x : Ω。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Submartingale.setIntegral_le`：setIntegral_le [PartialOrder
 E] [IsOrderedAddMonoid E] [IsOrderedModule Real E] [ClosedIciTopology E] [Sigma
FiniteFiltration μ ℱ] {f : ι -> …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `MeasureTheory.IsFiniteMeasure.sigmaFiniteFiltration`：∀ {Ω : Type u_1} {ι
 : Type u_2} {m : MeasurableSpace Ω} [inst : Preorder ι] (μ : MeasureTheory.Meas
ure Ω)   (f : MeasureTheory.Filtration ι …
· 使用定理 `MeasureTheory.Submartingale.sum_sub_upcrossingStrat_mul`：∀ {Ω : Type u_1
} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {f : ℕ → Ω → ℝ}   {ℱ : 
MeasureTheory.Filtration ℕ m0} [MeasureTheory…
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_zero'`：integral_zero' : integral μ (0 : α -> G) =
 0
· 使用定理 `MeasureTheory.setIntegral_univ`：setIntegral_univ : ∫ x in univ, f x ∂μ =
 ∫ x, f x ∂μ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `MeasureTheory.integral_sub`：integral_sub {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.Integrable.sub`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f g
 : α → β}, Measure…
· 使用定理 `MeasureTheory.integrable_finsetSum`：integrable_finsetSum {ι} (s : Finset
 ι) {f : ι -> α -> ε'} (hf : forall i in s, Integrable (f i) μ) : Integrable (fu
n a => ∑ i in s, f i a) …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
（共 43 条，此处仅展示前 30 条）
-/
theorem Submartingale.sum_mul_upcrossingStrat_le [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ) :
    μ[∑ k ∈ Finset.range n, upcrossingStrat a b f N k * (f (k + 1) - f k)] ≤ μ[f n] - μ[f 0] := by
  have h₁ : (0 : ℝ) ≤
      μ[∑ k ∈ Finset.range n, (1 - upcrossingStrat a b f N k) * (f (k + 1) - f k)] := by
    have := (hf.sum_sub_upcrossingStrat_mul a b N).setIntegral_le (zero_le (a := n)) .univ
    rw [setIntegral_univ, setIntegral_univ] at this
    refine le_trans ?_ this
    simp only [Finset.range_zero, Finset.sum_empty, integral_zero', le_refl]
  have h₂ : μ[∑ k ∈ Finset.range n, (1 - upcrossingStrat a b f N k) * (f (k + 1) - f k)] =
    μ[∑ k ∈ Finset.range n, (f (k + 1) - f k)] -
      μ[∑ k ∈ Finset.range n, upcrossingStrat a b f N k * (f (k + 1) - f k)] := by
    simp only [sub_mul, one_mul, Finset.sum_sub_distrib, Pi.sub_apply, Finset.sum_apply,
      Pi.mul_apply]
    refine integral_sub (Integrable.sub (integrable_finsetSum _ fun i _ => hf.integrable _)
      (integrable_finsetSum _ fun i _ => hf.integrable _)) ?_
    convert! (hf.sum_upcrossingStrat_mul a b N).integrable n using 1
    ext; simp
  rw [h₂, sub_nonneg] at h₁
  refine le_trans h₁ ?_
  simp_rw [Finset.sum_range_sub, integral_sub' (hf.integrable _) (hf.integrable _), le_refl]

/-- The number of upcrossings (strictly) before time `N`. -/
/-
**MeasureTheory.upcrossingsBefore** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：upcrossingsBefore [Preorder ι] [OrderBot ι] [InfSet ι] (a b : Real) (f : ι
 -> Ω -> Real) (N : ι) (ω : Ω) : Nat
参数：a b : Real；f : ι -> Ω -> Real；N : ι；ω : Ω。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The number of upcrossings (strictly) before time `N`.
-/
noncomputable def upcrossingsBefore [Preorder ι] [OrderBot ι] [InfSet ι] (a b : ℝ) (f : ι → Ω → ℝ)
    (N : ι) (ω : Ω) : ℕ :=
  sSup {n | upperCrossingTime a b f N n ω < N}

@[simp]
/-
**MeasureTheory.upcrossingsBefore_bot** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：upcrossingsBefore_bot [Preorder ι] [OrderBot ι] [InfSet ι] {a b : Real} {f
 : ι -> Ω -> Real} {ω : Ω} : upcrossingsBefore a b f ⊥ ω = ⊥
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
· 使用定理 `csSup_empty`：csSup_empty : (sSup ∅ : α) = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem upcrossingsBefore_bot [Preorder ι] [OrderBot ι] [InfSet ι] {a b : ℝ} {f : ι → Ω → ℝ}
    {ω : Ω} : upcrossingsBefore a b f ⊥ ω = ⊥ := by simp [upcrossingsBefore]
/-
**MeasureTheory.upcrossingsBefore_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：upcrossingsBefore_zero : upcrossingsBefore a b f 0 ω = 0
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
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `csSup_empty`：csSup_empty : (sSup ∅ : α) = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem upcrossingsBefore_zero : upcrossingsBefore a b f 0 ω = 0 := by simp [upcrossingsBefore]

@[simp]
/-
**MeasureTheory.upcrossingsBefore_zero'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：upcrossingsBefore_zero' : upcrossingsBefore a b f 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.upcrossingsBefore_zero`：upcrossingsBefore_zero : upcrossin
gsBefore a b f 0 ω = 0
-/
theorem upcrossingsBefore_zero' : upcrossingsBefore a b f 0 = 0 := by
  ext ω; exact upcrossingsBefore_zero
/-
**MeasureTheory.upperCrossingTime_lt_of_le_upcrossingsBefore** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory`。
形式化陈述：upperCrossingTime_lt_of_le_upcrossingsBefore (hN : 0 < N) (hab : a < b) (h
n : n <= upcrossingsBefore a b f N ω) : upperCrossingTime a b f N n ω < N
参数：hN : 0 < N；hab : a < b；hn : n <= upcrossingsBefore a b f N ω。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `MeasureTheory.upperCrossingTime_mono`：upperCrossingTime_mono (hnm : n <=
 m) : upperCrossingTime a b f N n ω <= upperCrossingTime a b f N m ω
· 使用定理 `Set.Nonempty.csSup_mem`：Set.Nonempty.csSup_mem (h : s.Nonempty) (hs : s.
Finite) : sSup s in s
· 使用定理 `MeasureTheory.upperCrossingTime_lt_nonempty`：upperCrossingTime_lt_nonemp
ty (hN : 0 < N) : {n | upperCrossingTime a b f N n ω < N}.Nonempty
· 使用定理 `BddBelow.finite_of_bddAbove`：BddBelow.finite_of_bddAbove [Preorder α] [L
ocallyFiniteOrder α] {s : Set α} (h₀ : BddBelow s) (h₁ : BddAbove s) : s.Finite
· 使用定理 `OrderBot.bddBelow`：∀ {α : Type u_1} [inst : Preorder α] [OrderBot α] (s 
: Set α), BddBelow s
· 使用定理 `MeasureTheory.upperCrossingTime_lt_bddAbove`：upperCrossingTime_lt_bddAbo
ve (hab : a < b) : BddAbove {n | upperCrossingTime a b f N n ω < N}
-/
theorem upperCrossingTime_lt_of_le_upcrossingsBefore (hN : 0 < N) (hab : a < b)
    (hn : n ≤ upcrossingsBefore a b f N ω) : upperCrossingTime a b f N n ω < N :=
  haveI : upperCrossingTime a b f N (upcrossingsBefore a b f N ω) ω < N :=
    (upperCrossingTime_lt_nonempty hN).csSup_mem
      ((OrderBot.bddBelow _).finite_of_bddAbove (upperCrossingTime_lt_bddAbove hab))
  lt_of_le_of_lt (upperCrossingTime_mono hn) this
/-
**MeasureTheory.upperCrossingTime_eq_of_upcrossingsBefore_lt** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory`。
形式化陈述：upperCrossingTime_eq_of_upcrossingsBefore_lt (hab : a < b) (hn : upcrossin
gsBefore a b f N ω < n) : upperCrossingTime a b f N n ω = N
参数：hab : a < b；hn : upcrossingsBefore a b f N ω < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasureTheory.upperCrossingTime_le`：upperCrossingTime_le : upperCrossing
Time a b f N n ω <= N
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `notMem_of_csSup_lt`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattic
e α] {x : α} {s : Set α}, sSup s < x → BddAbove s → x ∉ s
· 使用定理 `MeasureTheory.upperCrossingTime_lt_bddAbove`：upperCrossingTime_lt_bddAbo
ve (hab : a < b) : BddAbove {n | upperCrossingTime a b f N n ω < N}
-/
theorem upperCrossingTime_eq_of_upcrossingsBefore_lt (hab : a < b)
    (hn : upcrossingsBefore a b f N ω < n) : upperCrossingTime a b f N n ω = N := by
  refine le_antisymm upperCrossingTime_le (not_lt.1 ?_)
  convert! notMem_of_csSup_lt hn (upperCrossingTime_lt_bddAbove hab) using 1
/-
**MeasureTheory.upcrossingsBefore_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：upcrossingsBefore_le (f : Nat -> Ω -> Real) (ω : Ω) (hab : a < b) : upcros
singsBefore a b f N ω <= N
参数：f : Nat -> Ω -> Real；ω : Ω；hab : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.upcrossingsBefore_zero`：upcrossingsBefore_zero : upcrossin
gsBefore a b f 0 ω = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `csSup_le`：csSup_le (h₁ : s.Nonempty) (h₂ : forall b in s, b <= a) : sSup
 s <= a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `zero_lt_iff`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : 
Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.upperCrossingTime_eq_of_bound_le`：upperCrossingTime_eq_of_
bound_le (hab : a < b) (hn : N <= n) : upperCrossingTime a b f N n ω = N
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
-/
theorem upcrossingsBefore_le (f : ℕ → Ω → ℝ) (ω : Ω) (hab : a < b) :
    upcrossingsBefore a b f N ω ≤ N := by
  by_cases hN : N = 0
  · subst hN
    rw [upcrossingsBefore_zero]
  · refine csSup_le ⟨0, zero_lt_iff.2 hN⟩ fun n (hn : _ < N) => ?_
    by_contra hnN
    exact hn.ne (upperCrossingTime_eq_of_bound_le hab (not_le.1 hnN).le)
/-
**MeasureTheory.crossing_eq_crossing_of_lowerCrossingTime_lt** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory`。
形式化陈述：crossing_eq_crossing_of_lowerCrossingTime_lt {M : Nat} (hNM : N <= M) (h :
 lowerCrossingTime a b f N n ω < N) : upperCrossingTime a b f M n ω = upperCross
ingTime a b f N n ω ∧ lowerCrossingTime a b f M n ω = lowerCrossingTime a b f N 
n ω
参数：hNM : N <= M；h : lowerCrossingTime a b f N n ω < N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `MeasureTheory.upperCrossingTime_le_lowerCrossingTime`：upperCrossingTime_
le_lowerCrossingTime : upperCrossingTime a b f N n ω <= lowerCrossingTime a b f 
N n ω
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `MeasureTheory.hittingBtwn_eq_hittingBtwn_of_exists`：hittingBtwn_eq_hitti
ngBtwn_of_exists {m₁ m₂ : ι} (h : m₁ <= m₂) (h' : exists j in Set.Icc n m₁, u j 
ω in s) : hittingBtwn u s n m₁ ω = hitti…
· 使用定理 `MeasureTheory.hittingBtwn_lt_iff`：hittingBtwn_lt_iff {m : ι} (i : ι) (hi
 : i <= m) : hittingBtwn u s n m ω < i ↔ exists j in Set.Ico n i, u j ω in s
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.lowerCrossingTime.eq_1`：∀ {Ω : Type u_1} {ι : Type u_2} [i
nst : Preorder ι] [inst_1 : OrderBot ι] [inst_2 : InfSet ι] (a b : ℝ) (f : ι → Ω
 → ℝ)   (N : ι) (n : ℕ) (ω…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.upperCrossingTime_succ_eq`：upperCrossingTime_succ_eq (ω : 
Ω) : upperCrossingTime a b f N (n + 1) ω = hittingBtwn f (Set.Ici b) (lowerCross
ingTime a b f N n ω) N ω
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `MeasureTheory.lowerCrossingTime_mono`：lowerCrossingTime_mono (hnm : n <=
 m) : lowerCrossingTime a b f N n ω <= lowerCrossingTime a b f N m ω
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `MeasureTheory.upperCrossingTime_mono`：upperCrossingTime_mono (hnm : n <=
 m) : upperCrossingTime a b f N n ω <= upperCrossingTime a b f N m ω
-/
theorem crossing_eq_crossing_of_lowerCrossingTime_lt {M : ℕ} (hNM : N ≤ M)
    (h : lowerCrossingTime a b f N n ω < N) :
    upperCrossingTime a b f M n ω = upperCrossingTime a b f N n ω ∧
      lowerCrossingTime a b f M n ω = lowerCrossingTime a b f N n ω := by
  have h' : upperCrossingTime a b f N n ω < N :=
    lt_of_le_of_lt upperCrossingTime_le_lowerCrossingTime h
  induction n with
  | zero =>
    simp only [upperCrossingTime_zero, bot_eq_zero',
      lowerCrossingTime_zero, true_and, eq_comm]
    refine hittingBtwn_eq_hittingBtwn_of_exists hNM ?_
    rw [lowerCrossingTime, hittingBtwn_lt_iff] at h
    · obtain ⟨j, hj₁, hj₂⟩ := h
      exact ⟨j, ⟨hj₁.1, hj₁.2.le⟩, hj₂⟩
    · exact le_rfl
  | succ k ih =>
    specialize ih (lt_of_le_of_lt (lowerCrossingTime_mono (Nat.le_succ _)) h)
      (lt_of_le_of_lt (upperCrossingTime_mono (Nat.le_succ _)) h')
    have : upperCrossingTime a b f M k.succ ω = upperCrossingTime a b f N k.succ ω := by
      rw [upperCrossingTime_succ_eq, hittingBtwn_lt_iff] at h'
      · simp only [upperCrossingTime_succ_eq]
        obtain ⟨j, hj₁, hj₂⟩ := h'
        rw [eq_comm, ih.2]
        exact hittingBtwn_eq_hittingBtwn_of_exists hNM ⟨j, ⟨hj₁.1, hj₁.2.le⟩, hj₂⟩
      · exact le_rfl
    refine ⟨this, ?_⟩
    simp only [lowerCrossingTime, eq_comm, this, Nat.succ_eq_add_one]
    refine hittingBtwn_eq_hittingBtwn_of_exists hNM ?_
    rw [lowerCrossingTime, hittingBtwn_lt_iff _ le_rfl] at h
    obtain ⟨j, hj₁, hj₂⟩ := h
    exact ⟨j, ⟨hj₁.1, hj₁.2.le⟩, hj₂⟩
/-
**MeasureTheory.crossing_eq_crossing_of_upperCrossingTime_lt** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory`。
形式化陈述：crossing_eq_crossing_of_upperCrossingTime_lt {M : Nat} (hNM : N <= M) (h :
 upperCrossingTime a b f N (n + 1) ω < N) : upperCrossingTime a b f M (n + 1) ω 
= upperCrossingTime a b f N (n + 1) ω ∧ lowerCrossingTime a b f M n ω = lowerCro
ssingTime a b f N n ω
参数：hNM : N <= M；h : upperCrossingTime a b f N (n + 1) ω < N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.crossing_eq_crossing_of_lowerCrossingTime_lt`：crossing_eq_
crossing_of_lowerCrossingTime_lt {M : Nat} (hNM : N <= M) (h : lowerCrossingTime
 a b f N n ω < N) : upperCrossingTime a b f M n …
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `MeasureTheory.lowerCrossingTime_le_upperCrossingTime_succ`：lowerCrossing
Time_le_upperCrossingTime_succ : lowerCrossingTime a b f N n ω <= upperCrossingT
ime a b f N (n + 1) ω
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.upperCrossingTime_succ_eq`：upperCrossingTime_succ_eq (ω : 
Ω) : upperCrossingTime a b f N (n + 1) ω = hittingBtwn f (Set.Ici b) (lowerCross
ingTime a b f N n ω) N ω
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `MeasureTheory.hittingBtwn_eq_hittingBtwn_of_exists`：hittingBtwn_eq_hitti
ngBtwn_of_exists {m₁ m₂ : ι} (h : m₁ <= m₂) (h' : exists j in Set.Icc n m₁, u j 
ω in s) : hittingBtwn u s n m₁ ω = hitti…
· 使用定理 `MeasureTheory.hittingBtwn_lt_iff`：hittingBtwn_lt_iff {m : ι} (i : ι) (hi
 : i <= m) : hittingBtwn u s n m ω < i ↔ exists j in Set.Ico n i, u j ω in s
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem crossing_eq_crossing_of_upperCrossingTime_lt {M : ℕ} (hNM : N ≤ M)
    (h : upperCrossingTime a b f N (n + 1) ω < N) :
    upperCrossingTime a b f M (n + 1) ω = upperCrossingTime a b f N (n + 1) ω ∧
      lowerCrossingTime a b f M n ω = lowerCrossingTime a b f N n ω := by
  have := (crossing_eq_crossing_of_lowerCrossingTime_lt hNM
    (lt_of_le_of_lt lowerCrossingTime_le_upperCrossingTime_succ h)).2
  refine ⟨?_, this⟩
  rw [upperCrossingTime_succ_eq, upperCrossingTime_succ_eq, eq_comm, this]
  refine hittingBtwn_eq_hittingBtwn_of_exists hNM ?_
  rw [upperCrossingTime_succ_eq, hittingBtwn_lt_iff] at h
  · obtain ⟨j, hj₁, hj₂⟩ := h
    exact ⟨j, ⟨hj₁.1, hj₁.2.le⟩, hj₂⟩
  · exact le_rfl
/-
**MeasureTheory.upperCrossingTime_eq_upperCrossingTime_of_lt** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory`。
形式化陈述：upperCrossingTime_eq_upperCrossingTime_of_lt {M : Nat} (hNM : N <= M) (h :
 upperCrossingTime a b f N n ω < N) : upperCrossingTime a b f M n ω = upperCross
ingTime a b f N n ω
参数：hNM : N <= M；h : upperCrossingTime a b f N n ω < N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.crossing_eq_crossing_of_upperCrossingTime_lt`：crossing_eq_
crossing_of_upperCrossingTime_lt {M : Nat} (hNM : N <= M) (h : upperCrossingTime
 a b f N (n + 1) ω < N) : upperCrossingTime a b …
-/
theorem upperCrossingTime_eq_upperCrossingTime_of_lt {M : ℕ} (hNM : N ≤ M)
    (h : upperCrossingTime a b f N n ω < N) :
    upperCrossingTime a b f M n ω = upperCrossingTime a b f N n ω := by
  cases n
  · simp
  · exact (crossing_eq_crossing_of_upperCrossingTime_lt hNM h).1
/-
**MeasureTheory.upcrossingsBefore_mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：upcrossingsBefore_mono (hab : a < b) : Monotone fun N ω => upcrossingsBefo
re a b f N ω
参数：hab : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csSup_le_csSup'`：csSup_le_csSup' {s t : Set α} (h₁ : BddAbove t) (h₂ : s
 subseteq t) : sSup s <= sSup t
· 使用定理 `MeasureTheory.upperCrossingTime_lt_bddAbove`：upperCrossingTime_lt_bddAbo
ve (hab : a < b) : BddAbove {n | upperCrossingTime a b f N n ω < N}
· 使用定理 `Set.ofPred_subset_ofPred_of_imp`：∀ {α : Type u} {p q : α → Prop}, (∀ (a 
: α), p a → q a) → {a | p a} ⊆ {a | q a}
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.upperCrossingTime_eq_upperCrossingTime_of_lt`：upperCrossin
gTime_eq_upperCrossingTime_of_lt {M : Nat} (hNM : N <= M) (h : upperCrossingTime
 a b f N n ω < N) : upperCrossingTime a b f M n …
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
-/
theorem upcrossingsBefore_mono (hab : a < b) : Monotone fun N ω => upcrossingsBefore a b f N ω := by
  intro N M hNM ω
  simp only [upcrossingsBefore]
  gcongr sSup {n | ?_} with n
  · exact upperCrossingTime_lt_bddAbove hab
  intro hn
  rw [upperCrossingTime_eq_upperCrossingTime_of_lt hNM hn]
  exact lt_of_lt_of_le hn hNM
/-
**MeasureTheory.upcrossingsBefore_lt_of_exists_upcrossing** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory`。
形式化陈述：upcrossingsBefore_lt_of_exists_upcrossing (hab : a < b) {N₁ N₂ : Nat} (hN₁
 : N <= N₁) (hN₁' : f N₁ ω < a) (hN₂ : N₁ <= N₂) (hN₂' : b < f N₂ ω) : upcrossin
gsBefore a b f N ω < upcrossingsBefore a b f (N₂ + 1) ω
参数：hab : a < b；hN₁ : N <= N₁；hN₁' : f N₁ ω < a；hN₂ : N₁ <= N₂；hN₂' : b < f N₂ ω。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `le_csSup`：le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s
· 使用定理 `MeasureTheory.upperCrossingTime_lt_bddAbove`：upperCrossingTime_lt_bddAbo
ve (hab : a < b) : BddAbove {n | upperCrossingTime a b f N n ω < N}
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `MeasureTheory.upperCrossingTime_succ_eq`：upperCrossingTime_succ_eq (ω : 
Ω) : upperCrossingTime a b f N (n + 1) ω = hittingBtwn f (Set.Ici b) (lowerCross
ingTime a b f N n ω) N ω
· 使用定理 `MeasureTheory.hittingBtwn_lt_iff`：hittingBtwn_lt_iff {m : ι} (i : ι) (hi
 : i <= m) : hittingBtwn u s n m ω < i ↔ exists j in Set.Ico n i, u j ω in s
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.lowerCrossingTime.eq_1`：∀ {Ω : Type u_1} {ι : Type u_2} [i
nst : Preorder ι] [inst_1 : OrderBot ι] [inst_2 : InfSet ι] (a b : ℝ) (f : ι → Ω
 → ℝ)   (N : ι) (n : ℕ) (ω…
· 使用定理 `MeasureTheory.hittingBtwn_le_iff_of_lt`：hittingBtwn_le_iff_of_lt [WellFo
undedLT ι] {m : ι} (i : ι) (hi : i < m) : hittingBtwn u s n m ω <= i ↔ exists j 
in Set.Icc n i, u j ω in s
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.sSup_mem`：sSup_mem {s : Set Nat} (h₁ : s.Nonempty) (h₂ : BddAbove s)
 : sSup s in s
· 使用定理 `MeasureTheory.upperCrossingTime_lt_nonempty`：upperCrossingTime_lt_nonemp
ty (hN : 0 < N) : {n | upperCrossingTime a b f N n ω < N}.Nonempty
· 使用定理 `MeasureTheory.upperCrossingTime_eq_upperCrossingTime_of_lt`：upperCrossin
gTime_eq_upperCrossingTime_of_lt {M : Nat} (hNM : N <= M) (h : upperCrossingTime
 a b f N n ω < N) : upperCrossingTime a b f M n …
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.le_zero`：∀ {i : ℕ}, i ≤ 0 ↔ i = 0
· 使用定理 `MeasureTheory.upcrossingsBefore_zero`：upcrossingsBefore_zero : upcrossin
gsBefore a b f 0 ω = 0
· 使用定理 `MeasureTheory.upperCrossingTime_zero`：upperCrossingTime_zero : upperCros
singTime a b f N 0 = ⊥
· 使用定理 `Pi.bot_apply`：bot_apply [forall i, Bot (α' i)] (i : ι) : (⊥ : forall i, 
α' i) i = ⊥
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem upcrossingsBefore_lt_of_exists_upcrossing (hab : a < b) {N₁ N₂ : ℕ} (hN₁ : N ≤ N₁)
    (hN₁' : f N₁ ω < a) (hN₂ : N₁ ≤ N₂) (hN₂' : b < f N₂ ω) :
    upcrossingsBefore a b f N ω < upcrossingsBefore a b f (N₂ + 1) ω := by
  refine lt_of_lt_of_le (Nat.lt_succ_self _) (le_csSup (upperCrossingTime_lt_bddAbove hab) ?_)
  rw [Set.mem_ofPred_eq, upperCrossingTime_succ_eq, hittingBtwn_lt_iff _ le_rfl]
  refine ⟨N₂, ⟨?_, Nat.lt_succ_self _⟩, hN₂'.le⟩
  rw [lowerCrossingTime, hittingBtwn_le_iff_of_lt _ (Nat.lt_succ_self _)]
  refine ⟨N₁, ⟨le_trans ?_ hN₁, hN₂⟩, hN₁'.le⟩
  by_cases! hN : 0 < N
  · have : upperCrossingTime a b f N (upcrossingsBefore a b f N ω) ω < N :=
      Nat.sSup_mem (upperCrossingTime_lt_nonempty hN) (upperCrossingTime_lt_bddAbove hab)
    rw [upperCrossingTime_eq_upperCrossingTime_of_lt (hN₁.trans (hN₂.trans <| Nat.le_succ _))
      this]
    exact this.le
  · rw [Nat.le_zero] at hN
    rw [hN, upcrossingsBefore_zero, upperCrossingTime_zero, Pi.bot_apply, bot_eq_zero']
/-
**MeasureTheory.lowerCrossingTime_lt_of_lt_upcrossingsBefore** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory`。
形式化陈述：lowerCrossingTime_lt_of_lt_upcrossingsBefore (hN : 0 < N) (hab : a < b) (h
n : n < upcrossingsBefore a b f N ω) : lowerCrossingTime a b f N n ω < N
参数：hN : 0 < N；hab : a < b；hn : n < upcrossingsBefore a b f N ω。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `MeasureTheory.lowerCrossingTime_le_upperCrossingTime_succ`：lowerCrossing
Time_le_upperCrossingTime_succ : lowerCrossingTime a b f N n ω <= upperCrossingT
ime a b f N (n + 1) ω
· 使用定理 `MeasureTheory.upperCrossingTime_lt_of_le_upcrossingsBefore`：upperCrossin
gTime_lt_of_le_upcrossingsBefore (hN : 0 < N) (hab : a < b) (hn : n <= upcrossin
gsBefore a b f N ω) : upperCrossingTime a b f N …
-/
theorem lowerCrossingTime_lt_of_lt_upcrossingsBefore (hN : 0 < N) (hab : a < b)
    (hn : n < upcrossingsBefore a b f N ω) : lowerCrossingTime a b f N n ω < N :=
  lt_of_le_of_lt lowerCrossingTime_le_upperCrossingTime_succ
    (upperCrossingTime_lt_of_le_upcrossingsBefore hN hab hn)
/-
**MeasureTheory.le_sub_of_le_upcrossingsBefore** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：le_sub_of_le_upcrossingsBefore (hN : 0 < N) (hab : a < b) (hn : n < upcros
singsBefore a b f N ω) : b - a <= stoppedValue f (fun ω => (upperCrossingTime a 
b f N (n + 1) ω : Nat)) ω - stoppedValue f (fun ω => (lowerCrossingTime a b f N 
n ω : Nat)) ω
参数：hN : 0 < N；hab : a < b；hn : n < upcrossingsBefore a b f N ω。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sub_le_sub`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : Preorder α]
 [AddLeftMono α] {a b c d : α},   a ≤ b → c ≤ d → a - d ≤ b - c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MeasureTheory.stoppedValue_upperCrossingTime`：stoppedValue_upperCrossing
Time (h : upperCrossingTime a b f N (n + 1) ω != N) : b <= stoppedValue f (fun ω
 => (upperCrossingTime a b f N (n …
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `MeasureTheory.upperCrossingTime_lt_of_le_upcrossingsBefore`：upperCrossin
gTime_lt_of_le_upcrossingsBefore (hN : 0 < N) (hab : a < b) (hn : n <= upcrossin
gsBefore a b f N ω) : upperCrossingTime a b f N …
· 使用定理 `MeasureTheory.stoppedValue_lowerCrossingTime`：stoppedValue_lowerCrossing
Time (h : lowerCrossingTime a b f N n ω != N) : stoppedValue f (fun ω => (lowerC
rossingTime a b f N n ω : Nat)) ω …
· 使用定理 `MeasureTheory.lowerCrossingTime_lt_of_lt_upcrossingsBefore`：lowerCrossin
gTime_lt_of_lt_upcrossingsBefore (hN : 0 < N) (hab : a < b) (hn : n < upcrossing
sBefore a b f N ω) : lowerCrossingTime a b f N n…
-/
theorem le_sub_of_le_upcrossingsBefore (hN : 0 < N) (hab : a < b)
    (hn : n < upcrossingsBefore a b f N ω) :
    b - a ≤ stoppedValue f (fun ω ↦ (upperCrossingTime a b f N (n + 1) ω : ℕ)) ω -
      stoppedValue f (fun ω ↦ (lowerCrossingTime a b f N n ω : ℕ)) ω :=
  sub_le_sub
    (stoppedValue_upperCrossingTime (upperCrossingTime_lt_of_le_upcrossingsBefore hN hab hn).ne)
    (stoppedValue_lowerCrossingTime (lowerCrossingTime_lt_of_lt_upcrossingsBefore hN hab hn).ne)
/-
**MeasureTheory.sub_eq_zero_of_upcrossingsBefore_lt** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
形式化陈述：sub_eq_zero_of_upcrossingsBefore_lt (hab : a < b) (hn : upcrossingsBefore 
a b f N ω < n) : stoppedValue f (fun ω => (upperCrossingTime a b f N (n + 1) ω :
 Nat)) ω - stoppedValue f (fun ω => (lowerCrossingTime a b f N n ω : Nat)) ω = 0
参数：hab : a < b；hn : upcrossingsBefore a b f N ω < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `MeasureTheory.upcrossingsBefore.eq_1`：∀ {Ω : Type u_1} {ι : Type u_2} [i
nst : Preorder ι] [inst_1 : OrderBot ι] [inst_2 : InfSet ι] (a b : ℝ) (f : ι → Ω
 → ℝ)   (N : ι) (ω : Ω),  …
· 使用定理 `le_csSup`：le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s
· 使用定理 `MeasureTheory.upperCrossingTime_lt_bddAbove`：upperCrossingTime_lt_bddAbo
ve (hab : a < b) : BddAbove {n | upperCrossingTime a b f N n ω < N}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `WithTop.untopA.congr_simp`：∀ {α : Type u_1} [inst : Nonempty α] (a a_1 :
 WithTop α), a = a_1 → a.untopA = a_1.untopA
· 使用定理 `MeasureTheory.upperCrossingTime_stabilize'`：upperCrossingTime_stabilize'
 (hnm : n <= m) (hn : N <= upperCrossingTime a b f N n ω) : upperCrossingTime a 
b f N m ω = N
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `MeasureTheory.lowerCrossingTime_stabilize'`：lowerCrossingTime_stabilize'
 (hnm : n <= m) (hn : N <= lowerCrossingTime a b f N n ω) : lowerCrossingTime a 
b f N m ω = N
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `MeasureTheory.upperCrossingTime_le_lowerCrossingTime`：upperCrossingTime_
le_lowerCrossingTime : upperCrossingTime a b f N n ω <= lowerCrossingTime a b f 
N n ω
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sub_eq_zero_of_upcrossingsBefore_lt (hab : a < b) (hn : upcrossingsBefore a b f N ω < n) :
    stoppedValue f (fun ω ↦ (upperCrossingTime a b f N (n + 1) ω : ℕ)) ω -
      stoppedValue f (fun ω ↦ (lowerCrossingTime a b f N n ω : ℕ)) ω = 0 := by
  have : N ≤ upperCrossingTime a b f N n ω := by
    rw [upcrossingsBefore] at hn
    rw [← not_lt]
    exact fun h => not_le.2 hn (le_csSup (upperCrossingTime_lt_bddAbove hab) h)
  simp [stoppedValue, upperCrossingTime_stabilize' (Nat.le_succ n) this,
    lowerCrossingTime_stabilize' le_rfl (le_trans this upperCrossingTime_le_lowerCrossingTime)]
/-
**MeasureTheory.mul_upcrossingsBefore_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：mul_upcrossingsBefore_le (hf : a <= f N ω) (hab : a < b) : (b - a) * upcro
ssingsBefore a b f N ω <= ∑ k in Finset.range N, upcrossingStrat a b f N k ω * (
f (k + 1) - f k) ω
参数：hf : a <= f N ω；hab : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.upcrossingsBefore_zero'`：upcrossingsBefore_zero' : upcross
ingsBefore a b f 0 = 0
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.indicator_mul_left`：indicator_mul_left (s : Set ι) (f g : ι -> M₀) :
 indicator s (fun j => f j * g j) i = indicator s f i * g i
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Finset.sum_indicator_eq_sum_filter`：∀ {ι : Type u_1} {κ : Type u_2} {β :
 Type u_4} [inst : AddCommMonoid β] (s : Finset ι) (f : ι → κ → β) (t : ι → Set 
κ)   (g : ι → κ) [inst_1…
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `MeasureTheory.upperCrossingTime_le`：upperCrossingTime_le : upperCrossing
Time a b f N n ω <= N
· 使用定理 `Finset.sum_Ico_eq_add_neg`：∀ {δ : Type u_4} [inst : AddCommGroup δ] (f :
 ℕ → δ) {m n : ℕ},   m ≤ n → ∑ k ∈ Finset.Ico m n, f k = ∑ k ∈ Finset.range n, f
 k + -∑ k ∈ Fin…
· 使用定理 `MeasureTheory.lowerCrossingTime_le_upperCrossingTime_succ`：lowerCrossing
Time_le_upperCrossingTime_succ : lowerCrossingTime a b f N n ω <= upperCrossingT
ime a b f N (n + 1) ω
· 使用定理 `Finset.sum_range_sub`：∀ {G : Type u_3} [inst : AddCommGroup G] (f : ℕ → 
G) (n : ℕ), ∑ i ∈ Finset.range n, (f (i + 1) - f i) = f n - f 0
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `sub_add_sub_cancel`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : G), a 
- b + (b - c) = a - c
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
（共 55 条，此处仅展示前 30 条）
-/
theorem mul_upcrossingsBefore_le (hf : a ≤ f N ω) (hab : a < b) :
    (b - a) * upcrossingsBefore a b f N ω ≤
    ∑ k ∈ Finset.range N, upcrossingStrat a b f N k ω * (f (k + 1) - f k) ω := by
  by_cases hN : N = 0
  · simp [hN]
  simp_rw [upcrossingStrat, Finset.sum_mul, ←
    Set.indicator_mul_left _ _ (fun x ↦ (f (x + 1) - f x) ω), Pi.one_apply, Pi.sub_apply, one_mul]
  rw [Finset.sum_comm]
  have h₁ : ∀ k, ∑ n ∈ Finset.range N, (Set.Ico (lowerCrossingTime a b f N k ω)
      (upperCrossingTime a b f N (k + 1) ω)).indicator (fun m => f (m + 1) ω - f m ω) n =
      stoppedValue f (fun ω ↦ (upperCrossingTime a b f N (k + 1) ω : ℕ)) ω -
        stoppedValue f (fun ω ↦ (lowerCrossingTime a b f N k ω : ℕ)) ω := by
    intro k
    rw [Finset.sum_indicator_eq_sum_filter, (_ : Finset.filter (fun i => i ∈ Set.Ico
      (lowerCrossingTime a b f N k ω) (upperCrossingTime a b f N (k + 1) ω)) (Finset.range N) =
      Finset.Ico (lowerCrossingTime a b f N k ω) (upperCrossingTime a b f N (k + 1) ω)),
      Finset.sum_Ico_eq_add_neg _ lowerCrossingTime_le_upperCrossingTime_succ,
      Finset.sum_range_sub fun n => f n ω, Finset.sum_range_sub fun n => f n ω, neg_sub,
      sub_add_sub_cancel]
    · rfl
    · ext i
      simp only [Set.mem_Ico, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico,
        and_iff_right_iff_imp, and_imp]
      exact fun _ h => lt_of_lt_of_le h upperCrossingTime_le
  simp_rw [h₁]
  have h₂ : ∑ _k ∈ Finset.range (upcrossingsBefore a b f N ω), (b - a) ≤
      ∑ k ∈ Finset.range N, (stoppedValue f (fun ω ↦ (upperCrossingTime a b f N (k + 1) ω : ℕ)) ω -
        stoppedValue f (fun ω ↦ (lowerCrossingTime a b f N k ω : ℕ)) ω) := by
    calc
      ∑ _k ∈ Finset.range (upcrossingsBefore a b f N ω), (b - a) ≤
          ∑ k ∈ Finset.range (upcrossingsBefore a b f N ω),
            (stoppedValue f (fun ω ↦ (upperCrossingTime a b f N (k + 1) ω : ℕ)) ω -
              stoppedValue f (fun ω ↦ (lowerCrossingTime a b f N k ω : ℕ)) ω) := by
        gcongr ∑ k ∈ _, ?_ with i hi
        refine le_sub_of_le_upcrossingsBefore (zero_lt_iff.2 hN) hab ?_
        rwa [Finset.mem_range] at hi
      _ ≤ ∑ k ∈ Finset.range N,
          (stoppedValue f (fun ω ↦ (upperCrossingTime a b f N (k + 1) ω : ℕ)) ω -
          stoppedValue f (fun ω ↦ (lowerCrossingTime a b f N k ω : ℕ)) ω) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.2 (upcrossingsBefore_le f ω hab)) fun i _ hi => ?_
        by_cases hi' : i = upcrossingsBefore a b f N ω
        · subst hi'
          simp only [stoppedValue]
          rw [upperCrossingTime_eq_of_upcrossingsBefore_lt hab (Nat.lt_succ_self _)]
          by_cases heq : lowerCrossingTime a b f N (upcrossingsBefore a b f N ω) ω = N
          · rw [heq, sub_self]
          · rw [sub_nonneg]
            exact le_trans (stoppedValue_lowerCrossingTime heq) hf
        · rw [sub_eq_zero_of_upcrossingsBefore_lt hab]
          rw [Finset.mem_range, not_lt] at hi
          exact lt_of_le_of_ne hi (Ne.symm hi')
  refine le_trans ?_ h₂
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
/-
**MeasureTheory.integral_mul_upcrossingsBefore_le_integral** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory`。
形式化陈述：integral_mul_upcrossingsBefore_le_integral [IsFiniteMeasure μ] (hf : Subma
rtingale f ℱ μ) (hfN : forall ω, a <= f N ω) (hfzero : 0 <= f 0) (hab : a < b) :
 (b - a) * μ[upcrossingsBefore a b f N] <= μ[f N]
参数：hf : Submartingale f ℱ μ；hfN : forall ω, a <= f N ω；hfzero : 0 <= f 0；hab : a
 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_const_mul`：integral_const_mul {L : Type*} [RCLike
 L] (r : L) (f : α -> L) : ∫ a, r * f a ∂μ = r * ∫ a, f a ∂μ
· 使用引理 `MeasureTheory.integral_mono_of_nonneg`：integral_mono_of_nonneg {f g : α 
-> E} (hf : 0 <=ᵐ[μ] f) (hgi : Integrable g μ) (h : f <=ᵐ[μ] g) : ∫ a, f a ∂μ <=
 ∫ a, g a ∂μ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `MeasureTheory.Submartingale.integrable`：∀ {Ω : Type u_1} {E : Type u_2} 
{ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureTheory
.Measure Ω} [inst_1 : Normed…
· 使用定理 `MeasureTheory.Submartingale.sum_upcrossingStrat_mul`：∀ {Ω : Type u_1} {m
0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {f : ℕ → Ω → ℝ}   {ℱ : Meas
ureTheory.Filtration ℕ m0} [MeasureTheory…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MeasureTheory.mul_upcrossingsBefore_le`：mul_upcrossingsBefore_le (hf : a
 <= f N ω) (hab : a < b) : (b - a) * upcrossingsBefore a b f N ω <= ∑ k in Finse
t.range N, upcrossingStrat a…
· 使用定理 `MeasureTheory.Submartingale.sum_mul_upcrossingStrat_le`：∀ {Ω : Type u_1}
 {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {a b : ℝ} {f : ℕ → Ω → ℝ
} {N n : ℕ}   {ℱ : MeasureTheory.Filtration …
· 使用定理 `sub_le_self_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Add
LeftMono α] (a : α) {b : α}, a - b ≤ a ↔ 0 ≤ b
· 使用引理 `MeasureTheory.integral_nonneg`：integral_nonneg {f : α -> E} (hf : 0 <= f
) : 0 <= ∫ x, f x ∂μ
-/
theorem integral_mul_upcrossingsBefore_le_integral [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hfN : ∀ ω, a ≤ f N ω) (hfzero : 0 ≤ f 0) (hab : a < b) :
    (b - a) * μ[upcrossingsBefore a b f N] ≤ μ[f N] :=
  calc
    (b - a) * μ[upcrossingsBefore a b f N] ≤
        μ[∑ k ∈ Finset.range N, upcrossingStrat a b f N k * (f (k + 1) - f k)] := by
      rw [← integral_const_mul]
      refine integral_mono_of_nonneg ?_ ((hf.sum_upcrossingStrat_mul a b N).integrable N) ?_
      · exact Eventually.of_forall fun ω => mul_nonneg (sub_nonneg.2 hab.le) (Nat.cast_nonneg _)
      · filter_upwards with ω
        simpa using mul_upcrossingsBefore_le (hfN ω) hab
    _ ≤ μ[f N] - μ[f 0] := hf.sum_mul_upcrossingStrat_le
    _ ≤ μ[f N] := (sub_le_self_iff _).2 (integral_nonneg hfzero)
/-
**MeasureTheory.crossing_pos_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：crossing_pos_eq (hab : a < b) : upperCrossingTime 0 (b - a) (fun n ω => (f
 n ω - a)⁺) N n = upperCrossingTime a b f N n ∧ lowerCrossingTime 0 (b - a) (fun
 n ω => (f n ω - a)⁺) N n = lowerCrossingTime a b f N n
参数：hab : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_le_sub_iff_right`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α]
 [AddRightMono α] {a b : α} (c : α), a - c ≤ b - c ↔ a ≤ b
· 使用定理 `posPart_eq_of_posPart_pos`：∀ {α : Type u_1} [inst : LinearOrder α] [inst
_1 : AddGroup α] {a : α}, 0 < a⁺ → a⁺ = a
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `posPart_eq_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : SubNegMon
oid α] {a : α}, a⁺ = a ↔ 0 ≤ a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `posPart_nonpos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : SubNegMono
id α] {a : α}, a⁺ ≤ 0 ↔ a ≤ 0
· 使用定理 `sub_nonpos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, a - b ≤ 0 ↔ a ≤ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.upperCrossingTime_succ_eq`：upperCrossingTime_succ_eq (ω : 
Ω) : upperCrossingTime a b f N (n + 1) ω = hittingBtwn f (Set.Ici b) (lowerCross
ingTime a b f N n ω) N ω
（共 38 条，此处仅展示前 30 条）
-/
theorem crossing_pos_eq (hab : a < b) :
    upperCrossingTime 0 (b - a) (fun n ω => (f n ω - a)⁺) N n = upperCrossingTime a b f N n ∧
      lowerCrossingTime 0 (b - a) (fun n ω => (f n ω - a)⁺) N n = lowerCrossingTime a b f N n := by
  have hab' : 0 < b - a := sub_pos.2 hab
  have hf : ∀ ω i, b - a ≤ (f i ω - a)⁺ ↔ b ≤ f i ω := by
    intro i ω
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rwa [← sub_le_sub_iff_right a, ←
        posPart_eq_of_posPart_pos (lt_of_lt_of_le hab' h)]
    · rw [← sub_le_sub_iff_right a] at h
      rwa [posPart_eq_self.2 (le_trans hab'.le h)]
  have hf' (ω i) : (f i ω - a)⁺ ≤ 0 ↔ f i ω ≤ a := by rw [posPart_nonpos, sub_nonpos]
  induction n with
  | zero =>
    refine ⟨rfl, ?_⟩
    simp +unfoldPartialApp only [lowerCrossingTime_zero, hittingBtwn,
      Set.mem_Icc, Set.mem_Iic]
    simp_all
  | succ k ih =>
    have : upperCrossingTime 0 (b - a) (fun n ω => (f n ω - a)⁺) N (k + 1) =
        upperCrossingTime a b f N (k + 1) := by
      ext ω
      simp only [upperCrossingTime_succ_eq, ← ih.2, hittingBtwn, Set.mem_Ici, tsub_le_iff_right]
      split_ifs with h₁ h₂ h₂
      · simp_rw [← sub_le_iff_le_add, hf ω]
      · refine False.elim (h₂ ?_)
        simp_all only [Set.mem_Ici, not_true_eq_false]
      · refine False.elim (h₁ ?_)
        simp_all only [Set.mem_Ici]
      · rfl
    refine ⟨this, ?_⟩
    ext ω
    simp only [lowerCrossingTime, this, hittingBtwn, Set.mem_Iic]
    split_ifs with h₁ h₂ h₂
    · simp_rw [hf' ω]
    · refine False.elim (h₂ ?_)
      simp_all only [Set.mem_Iic, not_true_eq_false]
    · refine False.elim (h₁ ?_)
      simp_all only [Set.mem_Iic]
    · rfl
/-
**MeasureTheory.upcrossingsBefore_pos_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：upcrossingsBefore_pos_eq (hab : a < b) : upcrossingsBefore 0 (b - a) (fun 
n ω => (f n ω - a)⁺) N ω = upcrossingsBefore a b f N ω
参数：hab : a < b。
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
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.crossing_pos_eq`：crossing_pos_eq (hab : a < b) : upperCros
singTime 0 (b - a) (fun n ω => (f n ω - a)⁺) N n = upperCrossingTime a b f N n ∧
 lowerCrossingTime …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem upcrossingsBefore_pos_eq (hab : a < b) :
    upcrossingsBefore 0 (b - a) (fun n ω => (f n ω - a)⁺) N ω = upcrossingsBefore a b f N ω := by
  simp_rw [upcrossingsBefore, (crossing_pos_eq hab).1]
/-
**MeasureTheory.mul_integral_upcrossingsBefore_le_integral_pos_part_aux** 是 Math
lib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：mul_integral_upcrossingsBefore_le_integral_pos_part_aux [IsFiniteMeasure μ
] (hf : Submartingale f ℱ μ) (hab : a < b) : (b - a) * μ[upcrossingsBefore a b f
 N] <= μ[fun ω => (f N ω - a)⁺]
参数：hf : Submartingale f ℱ μ；hab : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.upcrossingsBefore_pos_eq`：upcrossingsBefore_pos_eq (hab : 
a < b) : upcrossingsBefore 0 (b - a) (fun n ω => (f n ω - a)⁺) N ω = upcrossings
Before a b f N ω
· 使用定理 `MeasureTheory.integral_mul_upcrossingsBefore_le_integral`：integral_mul_u
pcrossingsBefore_le_integral [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ) (hfN
 : forall ω, a <= f N ω) (hfzero : 0 <= f 0) (…
· 使用定理 `MeasureTheory.Submartingale.pos`：∀ {Ω : Type u_1} {E : Type u_2} {ι : Ty
pe u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureTheory.Measur
e Ω} [inst_1 : Normed…
· 使用定理 `TopologicalLattice.toContinuousSup`：∀ {L : Type u_1} {inst : Topological
Space L} {inst_1 : Lattice L} [self : TopologicalLattice L], ContinuousSup L
· 使用定理 `HasSolidNorm.toTopologicalLattice`：∀ {α : Type u_1} [inst : NormedAddCom
mGroup α] [inst_1 : Lattice α] [HasSolidNorm α] [IsOrderedAddMonoid α],   Topolo
gicalLattice α
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `MeasureTheory.Submartingale.sub_martingale`：sub_martingale [Preorder E] 
[AddLeftMono E] (hf : Submartingale f ℱ μ) (hg : Martingale g ℱ μ) : Submartinga
le (f - g) ℱ μ
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.martingale_const`：martingale_const (ℱ : Filtration ι m0) (
μ : Measure Ω) [IsFiniteMeasure μ] (x : E) : Martingale (fun _ _ => x) ℱ μ
· 使用定理 `posPart_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : SubNegMono
id α] (a : α), 0 ≤ a⁺
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
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
theorem mul_integral_upcrossingsBefore_le_integral_pos_part_aux [IsFiniteMeasure μ]
    (hf : Submartingale f ℱ μ) (hab : a < b) :
    (b - a) * μ[upcrossingsBefore a b f N] ≤ μ[fun ω => (f N ω - a)⁺] := by
  refine le_trans (le_of_eq ?_)
    (integral_mul_upcrossingsBefore_le_integral (hf.sub_martingale (martingale_const _ _ _)).pos
      (fun ω => posPart_nonneg _)
      (fun ω => posPart_nonneg _) (sub_pos.2 hab))
  simp_rw [sub_zero, ← upcrossingsBefore_pos_eq hab]
  rfl

/-- **Doob's upcrossing estimate**: given a real-valued discrete submartingale `f` and real
values `a` and `b`, we have `(b - a) * 𝔼[upcrossingsBefore a b f N] ≤ 𝔼[(f N - a)⁺]` where
`upcrossingsBefore a b f N` is the number of times the process `f` crossed from below `a` to above
`b` before the time `N`. -/
/-
**MeasureTheory.Submartingale.mul_integral_upcrossingsBefore_le_integral_pos_par
t** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Submartingale`。
形式化陈述：∀ {Ω : Type u_1} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {f
 : ℕ → Ω → ℝ}   {ℱ : MeasureTheory.Filtration ℕ m0} [MeasureTheory.IsFiniteMeasu
re μ] (a b : ℝ),   MeasureTheory.Submartingale f ℱ μ →     ∀ (N : ℕ),       (b -
 a) * ∫ (x : Ω), ↑(MeasureTheory.upcrossingsBefore a b f N x) ∂μ ≤ ∫ (x : Ω), (f
un ω => (f N ω - a)⁺) x ∂μ
参数：a b : ℝ；N : ℕ；b - a；x : Ω；MeasureTheory.upcrossingsBefore a b f N x；x : Ω；fun
 ω => (f N ω - a)⁺。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.mul_integral_upcrossingsBefore_le_integral_pos_part_aux`：m
ul_integral_upcrossingsBefore_le_integral_pos_part_aux [IsFiniteMeasure μ] (hf :
 Submartingale f ℱ μ) (hab : a < b) : (b - a) * μ[upcrossin…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `mul_nonpos_of_nonpos_of_nonneg`：mul_nonpos_of_nonpos_of_nonneg [MulPosMo
no α] (ha : a <= 0) (hb : 0 <= b) : a * b <= 0
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_nonpos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, a - b ≤ 0 ↔ a ≤ b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `MeasureTheory.integral_nonneg`：integral_nonneg {f : α -> E} (hf : 0 <= f
) : 0 <= ∫ x, f x ∂μ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `posPart_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : SubNegMono
id α] (a : α), 0 ≤ a⁺

--- 原说明 ---
**Doob's upcrossing estimate**: given a real-valued discrete submartingale `f` a
nd real
values `a` and `b`, we have `(b - a) * 𝔼[upcrossingsBefore a b f N] ≤ 𝔼[(f N - a
)⁺]` where
`upcrossingsBefore a b f N` is the number of times the process `f` crossed from 
below `a` to above
`b` before the time `N`.
-/
theorem Submartingale.mul_integral_upcrossingsBefore_le_integral_pos_part [IsFiniteMeasure μ]
    (a b : ℝ) (hf : Submartingale f ℱ μ) (N : ℕ) :
    (b - a) * μ[upcrossingsBefore a b f N] ≤ μ[fun ω => (f N ω - a)⁺] := by
  by_cases! hab : a < b
  · exact mul_integral_upcrossingsBefore_le_integral_pos_part_aux hf hab
  · rw [← sub_nonpos] at hab
    exact le_trans (mul_nonpos_of_nonpos_of_nonneg hab (by positivity))
      (integral_nonneg fun ω => posPart_nonneg _)

/-!

### Variant of the upcrossing estimate

Now, we would like to prove a variant of the upcrossing estimate obtained by taking the supremum
over $N$ of the original upcrossing estimate. Namely, we want the inequality
$$
  (b - a) \sup_N \mathbb{E}[U_N(a, b)] \le \sup_N \mathbb{E}[f_N].
$$
This inequality is central for the martingale convergence theorem as it provides a uniform bound
for the upcrossings.

We note that on top of taking the supremum on both sides of the inequality, we had also used
the monotone convergence theorem on the left-hand side to take the supremum outside of the
integral. To do this, we need to make sure $U_N(a, b)$ is measurable and integrable. Integrability
is easy to check as $U_N(a, b) ≤ N$ and so it suffices to show measurability. Indeed, by
noting that
$$
  U_N(a, b) = \sum_{i = 1}^N \mathbf{1}_{\{U_N(a, b) < N\}}
$$
$U_N(a, b)$ is measurable as $\{U_N(a, b) < N\}$ is a measurable set since $U_N(a, b)$ is a
stopping time.

-/


/-
**MeasureTheory.upcrossingsBefore_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：upcrossingsBefore_eq_sum (hab : a < b) : upcrossingsBefore a b f N ω = ∑ i
 in Finset.Ico 1 (N + 1), {n | upperCrossingTime a b f N n ω < N}.indicator 1 i
参数：hab : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MeasureTheory.upcrossingsBefore_zero'`：upcrossingsBefore_zero' : upcross
ingsBefore a b f 0 = 0
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Finset.Ico_eq_empty_of_le`：Ico_eq_empty_of_le (h : b <= a) : Ico a b = ∅
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_Ico_consecutive`：∀ {M : Type u_3} [inst : AddCommMonoid M] (f
 : ℕ → M) {m n k : ℕ},   m ≤ n → n ≤ k → ∑ i ∈ Finset.Ico m n, f i + ∑ i ∈ Finse
t.Ico n k, f i =…
· 使用定理 `Nat.succ_le_succ`：∀ {n m : ℕ}, n ≤ m → n.succ ≤ m.succ
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `MeasureTheory.upcrossingsBefore_le`：upcrossingsBefore_le (f : Nat -> Ω -
> Real) (ω : Ω) (hab : a < b) : upcrossingsBefore a b f N ω <= N
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `MeasureTheory.upperCrossingTime_lt_of_le_upcrossingsBefore`：upperCrossin
gTime_lt_of_le_upcrossingsBefore (hN : 0 < N) (hab : a < b) (hn : n <= upcrossin
gsBefore a b f N ω) : upperCrossingTime a b f N …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `zero_lt_iff`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : 
Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.mem_Ico`：mem_Ico : x in Ico a b ↔ a <= x ∧ x < b
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
### Variant of the upcrossing estimate

Now, we would like to prove a variant of the upcrossing estimate obtained by tak
ing the supremum
over $N$ of the original upcrossing estimate. Namely, we want the inequality
$$
  (b - a) \sup_N \mathbb{E}[U_N(a, b)] \le \sup_N \mathbb{E}[f_N].
$$
This inequality is central for the martingale convergence theorem as it provides
 a uniform bound
for the upcrossings.

We note that on top of taking the supremum on both sides of the inequality, we h
ad also used
the monotone convergence theorem on the left-hand side to take the supremum outs
ide of the
integral. To do this, we need to make sure $U_N(a, b)$ is measurable and integra
ble. Integrability
is easy to check as $U_N(a, b) ≤ N$ and so it suffices to show measurability. In
deed, by
noting that
$$
  U_N(a, b) = \sum_{i = 1}^N \mathbf{1}_{\{U_N(a, b) < N\}}
$$
$U_N(a, b)$ is measurable as $\{U_N(a, b) < N\}$ is a measurable set since $U_N(
a, b)$ is a
stopping time.
-/
theorem upcrossingsBefore_eq_sum (hab : a < b) : upcrossingsBefore a b f N ω =
    ∑ i ∈ Finset.Ico 1 (N + 1), {n | upperCrossingTime a b f N n ω < N}.indicator 1 i := by
  by_cases hN : N = 0
  · simp [hN]
  rw [← Finset.sum_Ico_consecutive _ (Nat.succ_le_succ zero_le)
    (Nat.succ_le_succ (upcrossingsBefore_le f ω hab))]
  have h₁ : ∀ k ∈ Finset.Ico 1 (upcrossingsBefore a b f N ω + 1),
      {n : ℕ | upperCrossingTime a b f N n ω < N}.indicator 1 k = 1 := by
    rintro k hk
    rw [Finset.mem_Ico] at hk
    rw [Set.indicator_of_mem]
    · rfl
    · exact upperCrossingTime_lt_of_le_upcrossingsBefore (zero_lt_iff.2 hN) hab
        (Nat.lt_succ_iff.1 hk.2)
  have h₂ : ∀ k ∈ Finset.Ico (upcrossingsBefore a b f N ω + 1) (N + 1),
      {n : ℕ | upperCrossingTime a b f N n ω < N}.indicator 1 k = 0 := by
    rintro k hk
    rw [Finset.mem_Ico, Nat.succ_le_iff] at hk
    rw [Set.indicator_of_notMem]
    simp only [Set.mem_ofPred_eq, not_lt]
    exact (upperCrossingTime_eq_of_upcrossingsBefore_lt hab hk.1).symm.le
  rw [Finset.sum_congr rfl h₁, Finset.sum_congr rfl h₂, Finset.sum_const, Finset.sum_const,
    smul_eq_mul, mul_one, smul_eq_mul, mul_zero, Nat.card_Ico, Nat.add_succ_sub_one,
    add_zero, add_zero]
/-
**MeasureTheory.StronglyAdapted.measurable_upcrossingsBefore** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.StronglyAdapted`。
形式化陈述：∀ {Ω : Type u_1} {m0 : MeasurableSpace Ω} {a b : ℝ} {f : ℕ → Ω → ℝ} {N : ℕ
} {ℱ : MeasureTheory.Filtration ℕ m0},   MeasureTheory.StronglyAdapted ℱ f → a <
 b → Measurable (MeasureTheory.upcrossingsBefore a b f N)
参数：MeasureTheory.upcrossingsBefore a b f N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.upcrossingsBefore_eq_sum`：upcrossingsBefore_eq_sum (hab : 
a < b) : upcrossingsBefore a b f N ω = ∑ i in Finset.Ico 1 (N + 1), {n | upperCr
ossingTime a b f N n ω < N}.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.measurable_fun_sum`：∀ {M : Type u_2} {ι : Type u_3} {α : Type u_4
} [inst : AddCommMonoid M] [inst_1 : MeasurableSpace M] [MeasurableAdd₂ M]   {m 
: MeasurableSpa…
· 使用定理 `ContinuousAdd.measurableMul₂`：∀ {γ : Type u_3} [inst : TopologicalSpace 
γ] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [SecondCountableTopology γ]   [in
st_4 : Add γ] [Con…
· 使用定理 `PolishSpace.toSecondCountableTopology`：∀ {α : Type u_3} {h : Topological
Space α} [self : PolishSpace α], SecondCountableTopology α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.Countable.to_separableSpace`：∀ {α : Type u} [t : Topolo
gicalSpace α] [Countable α], TopologicalSpace.SeparableSpace α
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `DiscreteUniformity.instCompleteSpace`：∀ {α : Type u} [uniformSpace : Uni
formSpace α] [DiscreteUniformity α], CompleteSpace α
· 使用定理 `DiscreteUniformity.inst`：∀ (X : Type u_1), DiscreteUniformity X
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `DiscreteTopology.topologicalSemiring`：∀ {R : Type u_1} [inst : Topologic
alSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [DiscreteTopology R],   IsTopo
logicalSemiring R
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `Measurable.indicator`：Measurable.indicator [Zero β] (hf : Measurable f) 
(hs : MeasurableSet s) : Measurable (s.indicator f)
· 使用定理 `measurable_const`：measurable_const {_ : MeasurableSpace α} {_ : Measurab
leSpace β} {a : α} : Measurable fun _ : β => a
· 使用定理 `MeasureTheory.Filtration.le`：∀ {Ω : Type u_1} {ι : Type u_2} {m : Measur
ableSpace Ω} [inst : Preorder ι] (f : MeasureTheory.Filtration ι m) (i : ι),   ↑
f i ≤ m
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.IsStoppingTime.measurableSet_lt_of_pred`：∀ {Ω : Type u_1} 
{ι : Type u_3} {m : MeasurableSpace Ω} [inst : Preorder ι] {f : MeasureTheory.Fi
ltration ι m}   {τ : Ω → WithTop ι} [PredOr…
· 使用定理 `MeasureTheory.StronglyAdapted.isStoppingTime_upperCrossingTime`：∀ {Ω : T
ype u_1} {m0 : MeasurableSpace Ω} {a b : ℝ} {f : ℕ → Ω → ℝ} {N n : ℕ} {ℱ : Measu
reTheory.Filtration ℕ m0},   MeasureTheory.StronglyA…
-/
theorem StronglyAdapted.measurable_upcrossingsBefore (hf : StronglyAdapted ℱ f) (hab : a < b) :
    Measurable (upcrossingsBefore a b f N) := by
  have : upcrossingsBefore a b f N = fun ω =>
      ∑ i ∈ Finset.Ico 1 (N + 1), {n | upperCrossingTime a b f N n ω < N}.indicator 1 i := by
    ext ω
    exact upcrossingsBefore_eq_sum hab
  rw [this]
  refine Finset.measurable_fun_sum _ fun i _ => Measurable.indicator measurable_const <|
    ℱ.le N _ ?_
  simpa only [ENat.some_eq_natCast, Nat.cast_lt] using!
    hf.isStoppingTime_upperCrossingTime.measurableSet_lt_of_pred N
/-
**MeasureTheory.StronglyAdapted.integrable_upcrossingsBefore** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.StronglyAdapted`。
形式化陈述：∀ {Ω : Type u_1} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {a
 b : ℝ} {f : ℕ → Ω → ℝ} {N : ℕ}   {ℱ : MeasureTheory.Filtration ℕ m0} [MeasureTh
eory.IsFiniteMeasure μ],   MeasureTheory.StronglyAdapted ℱ f →     a < b → Measu
reTheory.Integrable (fun ω => ↑(MeasureTheory.upcrossingsBefore a b f N ω)) μ
参数：fun ω => ↑(MeasureTheory.upcrossingsBefore a b f N ω)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 :…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_from_top`：measurable_from_top [MeasurableSpace β] {f : α -> β
} : Measurable[⊤] f
· 使用定理 `MeasureTheory.StronglyAdapted.measurable_upcrossingsBefore`：∀ {Ω : Type 
u_1} {m0 : MeasurableSpace Ω} {a b : ℝ} {f : ℕ → Ω → ℝ} {N : ℕ} {ℱ : MeasureTheo
ry.Filtration ℕ m0},   MeasureTheory.StronglyAda…
· 使用定理 `MeasureTheory.HasFiniteIntegral.of_bounded`：∀ {α : Type u_1} {β : Type u
_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommG
roup β]   [MeasureTheory.IsFinit…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用定理 `Nat.abs_cast`：abs_cast (n : Nat) : |(n : R)| = n
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `MeasureTheory.upcrossingsBefore_le`：upcrossingsBefore_le (f : Nat -> Ω -
> Real) (ω : Ω) (hab : a < b) : upcrossingsBefore a b f N ω <= N
-/
theorem StronglyAdapted.integrable_upcrossingsBefore [IsFiniteMeasure μ]
    (hf : StronglyAdapted ℱ f) (hab : a < b) :
    Integrable (fun ω => (upcrossingsBefore a b f N ω : ℝ)) μ :=
  haveI : ∀ᵐ ω ∂μ, ‖(upcrossingsBefore a b f N ω : ℝ)‖ ≤ N := by
    filter_upwards with ω
    rw [Real.norm_eq_abs, Nat.abs_cast, Nat.cast_le]
    exact upcrossingsBefore_le _ _ hab
  ⟨Measurable.aestronglyMeasurable (measurable_from_top.comp (hf.measurable_upcrossingsBefore hab)),
    .of_bounded this⟩

/-- The number of upcrossings of a realization of a stochastic process (`upcrossings` takes value
in `ℝ≥0∞` and so is allowed to be `∞`). -/
/-
**MeasureTheory.upcrossings** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：upcrossings [Preorder ι] [OrderBot ι] [InfSet ι] (a b : Real) (f : ι -> Ω 
-> Real) (ω : Ω) : Real>=0∞
参数：a b : Real；f : ι -> Ω -> Real；ω : Ω。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The number of upcrossings of a realization of a stochastic process (`upcrossings
` takes value
in `ℝ≥0∞` and so is allowed to be `∞`).
-/
noncomputable def upcrossings [Preorder ι] [OrderBot ι] [InfSet ι] (a b : ℝ) (f : ι → Ω → ℝ)
    (ω : Ω) : ℝ≥0∞ :=
  ⨆ N, (upcrossingsBefore a b f N ω : ℝ≥0∞)
/-
**MeasureTheory.StronglyAdapted.measurable_upcrossings** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.StronglyAdapted`。
形式化陈述：∀ {Ω : Type u_1} {m0 : MeasurableSpace Ω} {a b : ℝ} {f : ℕ → Ω → ℝ} {ℱ : M
easureTheory.Filtration ℕ m0},   MeasureTheory.StronglyAdapted ℱ f → a < b → Mea
surable (MeasureTheory.upcrossings a b f)
参数：MeasureTheory.upcrossings a b f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.iSup`：∀ {α : Type u_1} {δ : Type u_4} [inst : TopologicalSpac
e α] {mα : MeasurableSpace α} [BorelSpace α]   {mδ : MeasurableSpace δ} [inst_2 
: Con…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.instSecondCountableTopology`：SecondCountableTopology ENNReal
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_from_top`：measurable_from_top [MeasurableSpace β] {f : α -> β
} : Measurable[⊤] f
· 使用定理 `MeasureTheory.StronglyAdapted.measurable_upcrossingsBefore`：∀ {Ω : Type 
u_1} {m0 : MeasurableSpace Ω} {a b : ℝ} {f : ℕ → Ω → ℝ} {N : ℕ} {ℱ : MeasureTheo
ry.Filtration ℕ m0},   MeasureTheory.StronglyAda…
-/
theorem StronglyAdapted.measurable_upcrossings (hf : StronglyAdapted ℱ f) (hab : a < b) :
    Measurable (upcrossings a b f) :=
  .iSup fun _ => measurable_from_top.comp (hf.measurable_upcrossingsBefore hab)
/-
**MeasureTheory.upcrossings_lt_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：upcrossings_lt_top_iff : upcrossings a b f ω < ∞ ↔ exists k, forall N, upc
rossingsBefore a b f N ω <= k
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
· 使用定理 `exists_nat_ge`：exists_nat_ge (x : R) : exists n : Nat, x <= n
· 使用定理 `NNReal.instIsOrderedRing_1`：IsOrderedRing NNReal
· 使用定理 `NNReal.instArchimedean`：Archimedean NNReal
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `ENNReal.coe_natCast`：coe_natCast (n : Nat) : ((n : Real>=0) : Real>=0∞) 
= n
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem upcrossings_lt_top_iff :
    upcrossings a b f ω < ∞ ↔ ∃ k, ∀ N, upcrossingsBefore a b f N ω ≤ k := by
  have : upcrossings a b f ω < ∞ ↔ ∃ k : ℝ≥0, upcrossings a b f ω ≤ k := by
    constructor
    · intro h
      lift upcrossings a b f ω to ℝ≥0 using h.ne with r hr
      exact ⟨r, le_rfl⟩
    · rintro ⟨k, hk⟩
      exact lt_of_le_of_lt hk ENNReal.coe_lt_top
  simp_rw [this, upcrossings, iSup_le_iff]
  constructor <;> rintro ⟨k, hk⟩
  · obtain ⟨m, hm⟩ := exists_nat_ge k
    refine ⟨m, fun N => Nat.cast_le.1 ((hk N).trans ?_)⟩
    rwa [← ENNReal.coe_natCast, ENNReal.coe_le_coe]
  · refine ⟨k, fun N => ?_⟩
    simp only [ENNReal.coe_natCast, Nat.cast_le, hk N]

/-- A variant of Doob's upcrossing estimate obtained by taking the supremum on both sides. -/
/-
**MeasureTheory.Submartingale.mul_lintegral_upcrossings_le_lintegral_pos_part** 
是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Submartingale`。
形式化陈述：∀ {Ω : Type u_1} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} {f
 : ℕ → Ω → ℝ}   {ℱ : MeasureTheory.Filtration ℕ m0} [MeasureTheory.IsFiniteMeasu
re μ] (a b : ℝ),   MeasureTheory.Submartingale f ℱ μ →     ENNReal.ofReal (b - a
) * ∫⁻ (ω : Ω), MeasureTheory.upcrossings a b f ω ∂μ ≤       ⨆ N, ∫⁻ (ω : Ω), EN
NReal.ofReal (f N ω - a)⁺ ∂μ
参数：a b : ℝ；b - a；ω : Ω；ω : Ω；f N ω - a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ofReal_integral_eq_lintegral_ofReal`：ofReal_integral_eq_li
ntegral_ofReal {f : α -> Real} (hfi : Integrable f μ) (f_nn : 0 <=ᵐ[μ] f) : ENNR
eal.ofReal (∫ x, f x ∂μ) = ∫⁻ x, ENNRea…
· 使用定理 `MeasureTheory.Submartingale.integrable`：∀ {Ω : Type u_1} {E : Type u_2} 
{ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureTheory
.Measure Ω} [inst_1 : Normed…
· 使用定理 `MeasureTheory.Submartingale.pos`：∀ {Ω : Type u_1} {E : Type u_2} {ι : Ty
pe u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureTheory.Measur
e Ω} [inst_1 : Normed…
· 使用定理 `TopologicalLattice.toContinuousSup`：∀ {L : Type u_1} {inst : Topological
Space L} {inst_1 : Lattice L} [self : TopologicalLattice L], ContinuousSup L
· 使用定理 `HasSolidNorm.toTopologicalLattice`：∀ {α : Type u_1} [inst : NormedAddCom
mGroup α] [inst_1 : Lattice α] [HasSolidNorm α] [IsOrderedAddMonoid α],   Topolo
gicalLattice α
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `MeasureTheory.Submartingale.sub_martingale`：sub_martingale [Preorder E] 
[AddLeftMono E] (hf : Submartingale f ℱ μ) (hg : Martingale g ℱ μ) : Submartinga
le (f - g) ℱ μ
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.martingale_const`：martingale_const (ℱ : Filtration ι m0) (
μ : Measure Ω) [IsFiniteMeasure μ] (x : E) : Martingale (fun _ _ => x) ℱ μ
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `posPart_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : SubNegMono
id α] (a : α), 0 ≤ a⁺
· 使用定理 `MeasureTheory.lintegral_iSup'`：lintegral_iSup' {f : Nat -> α -> Real>=0∞
} (hf : forall n, AEMeasurable (f n) μ) (h_mono : forallᵐ x ∂μ, Monotone fun n =
> f n x) : ∫⁻ a, ⨆ …
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `measurable_from_top`：measurable_from_top [MeasurableSpace β] {f : α -> β
} : Measurable[⊤] f
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.StronglyAdapted.measurable_upcrossingsBefore`：∀ {Ω : Type 
u_1} {m0 : MeasurableSpace Ω} {a b : ℝ} {f : ℕ → Ω → ℝ} {N : ℕ} {ℱ : MeasureTheo
ry.Filtration ℕ m0},   MeasureTheory.StronglyAda…
· 使用定理 `MeasureTheory.Submartingale.stronglyAdapted`：∀ {Ω : Type u_1} {E : Type 
u_2} {ι : Type u_3} [inst : Preorder ι] {m0 : MeasurableSpace Ω}   {μ : MeasureT
heory.Measure Ω} [inst_1 : Normed…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `MeasureTheory.upcrossingsBefore_mono`：upcrossingsBefore_mono (hab : a < 
b) : Monotone fun N ω => upcrossingsBefore a b f N ω
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 59 条，此处仅展示前 30 条）

--- 原说明 ---
A variant of Doob's upcrossing estimate obtained by taking the supremum on both 
sides.
-/
theorem Submartingale.mul_lintegral_upcrossings_le_lintegral_pos_part [IsFiniteMeasure μ] (a b : ℝ)
    (hf : Submartingale f ℱ μ) : ENNReal.ofReal (b - a) * ∫⁻ ω, upcrossings a b f ω ∂μ ≤
      ⨆ N, ∫⁻ ω, ENNReal.ofReal ((f N ω - a)⁺) ∂μ := by
  by_cases! hab : a < b
  · simp_rw [upcrossings]
    have : ∀ N, ∫⁻ ω, ENNReal.ofReal ((f N ω - a)⁺) ∂μ = ENNReal.ofReal (∫ ω, (f N ω - a)⁺ ∂μ) := by
      intro N
      rw [ofReal_integral_eq_lintegral_ofReal]
      · exact (hf.sub_martingale (martingale_const _ _ _)).pos.integrable _
      · exact Eventually.of_forall fun ω => posPart_nonneg _
    rw [lintegral_iSup']
    · simp_rw [this, ENNReal.mul_iSup, iSup_le_iff]
      intro N
      rw [(by simp :
          ∫⁻ ω, upcrossingsBefore a b f N ω ∂μ = ∫⁻ ω, ↑(upcrossingsBefore a b f N ω : ℝ≥0) ∂μ),
        lintegral_coe_eq_integral, ← ENNReal.ofReal_mul (sub_pos.2 hab).le]
      · simp_rw [NNReal.coe_natCast]
        exact (ENNReal.ofReal_le_ofReal
          (hf.mul_integral_upcrossingsBefore_le_integral_pos_part a b N)).trans
            (le_iSup (α := ℝ≥0∞) _ N)
      · simp only [NNReal.coe_natCast, hf.stronglyAdapted.integrable_upcrossingsBefore hab]
    · exact fun n => measurable_from_top.comp_aemeasurable
        (hf.stronglyAdapted.measurable_upcrossingsBefore hab).aemeasurable
    · filter_upwards with ω N M hNM
      rw [Nat.cast_le]
      exact upcrossingsBefore_mono hab hNM ω
  · rw [← sub_nonpos] at hab
    rw [ENNReal.ofReal_of_nonpos hab, zero_mul]
    exact zero_le

end MeasureTheory

