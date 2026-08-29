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


/--
Definition of `lowerCrossingTimeAux` / `lowerCrossingTimeAux` 的定义

English:
definition lowerCrossingTimeAux
  signature: [Preorder ι] [InfSet ι] (a : Real) (f : ι -> Ω -> Real) (c N : ι)
  body: hittingBtwn f (Set.Iic a) c N

中文:
定义 lowerCrossingTimeAux
  签名: [Preorder ι] [InfSet ι] (a : 实数) (f : ι -> Ω -> 实数) (c N : ι)
  定义体: hittingBtwn f (Set.Iic a) c N

Depends on / 依赖: Set.Iic, hittingBtwn
-/
noncomputable def lowerCrossingTimeAux [Preorder ι] [InfSet ι] (a : Real) (f : ι -> Ω -> Real) (c N : ι) :
    Ω -> ι :=
  hittingBtwn f (Set.Iic a) c N

/--
Definition of `upperCrossingTime` / `upperCrossingTime` 的定义

English:
definition upperCrossingTime
  signature: [Preorder ι] [OrderBot ι] [InfSet ι] (a b : Real) (f : ι -> Ω -> Real)

中文:
定义 upperCrossingTime
  签名: [Preorder ι] [OrderBot ι] [InfSet ι] (a b : 实数) (f : ι -> Ω -> 实数)
-/
noncomputable def upperCrossingTime [Preorder ι] [OrderBot ι] [InfSet ι] (a b : Real) (f : ι -> Ω -> Real)
    (N : ι) : Nat -> Ω -> ι
  | 0 => ⊥
  | n + 1 => fun ω =>
    hittingBtwn f (Set.Ici b) (lowerCrossingTimeAux a f (upperCrossingTime a b f N n ω) N ω) N ω

/--
Definition of `lowerCrossingTime` / `lowerCrossingTime` 的定义

English:
definition lowerCrossingTime
  signature: [Preorder ι] [OrderBot ι] [InfSet ι] (a b : Real) (f : ι -> Ω -> Real)
  body: fun ω => hittingBtwn f (Set.Iic a) (upperCrossingTime a b f N n ω) N ω

中文:
定义 lowerCrossingTime
  签名: [Preorder ι] [OrderBot ι] [InfSet ι] (a b : 实数) (f : ι -> Ω -> 实数)
  定义体: fun ω => hittingBtwn f (Set.Iic a) (upperCrossingTime a b f N n ω) N ω

Depends on / 依赖: Set.Iic, hittingBtwn, upperCrossingTime
-/
noncomputable def lowerCrossingTime [Preorder ι] [OrderBot ι] [InfSet ι] (a b : Real) (f : ι -> Ω -> Real)
    (N : ι) (n : Nat) : Ω -> ι :=
    fun ω => hittingBtwn f (Set.Iic a) (upperCrossingTime a b f N n ω) N ω

section

variable [Preorder ι] [OrderBot ι] [InfSet ι]
variable {a b : Real} {f : ι -> Ω -> Real} {N : ι} {n : Nat} {ω : Ω}

@[simp]
/--
theorem `upperCrossingTime_zero` / 定理 `upperCrossingTime_zero`

English:
theorem upperCrossingTime_zero
  statement: upperCrossingTime a b f N 0 = ⊥
  proof: rfl

@[simp]

中文:
定理 upperCrossingTime_zero
  结论: upperCrossingTime a b f N 0 = ⊥
  证明: rfl

@[simp]

Depends on / 依赖: Finite, IsNoetherian, Module, Module.Finite
-/
theorem upperCrossingTime_zero : upperCrossingTime a b f N 0 = ⊥ :=
  rfl

@[simp]
/--
theorem `lowerCrossingTime_zero` / 定理 `lowerCrossingTime_zero`

English:
theorem lowerCrossingTime_zero
  statement: lowerCrossingTime a b f N 0 = hittingBtwn f (Set.Iic a) ⊥ N
  proof: rfl

中文:
定理 lowerCrossingTime_zero
  结论: lowerCrossingTime a b f N 0 = hittingBtwn f (Set.Iic a) ⊥ N
  证明: rfl
-/
theorem lowerCrossingTime_zero : lowerCrossingTime a b f N 0 = hittingBtwn f (Set.Iic a) ⊥ N :=
  rfl

/--
theorem `upperCrossingTime_succ` / 定理 `upperCrossingTime_succ`

English:
theorem upperCrossingTime_succ
  statement: upperCrossingTime a b f N (n + 1) ω =
  proof: by
  rw [upperCrossingTime]

中文:
定理 upperCrossingTime_succ
  结论: upperCrossingTime a b f N (n + 1) ω =
  证明: by
  rw [upperCrossingTime]

Depends on / 依赖: upperCrossingTime
-/
theorem upperCrossingTime_succ : upperCrossingTime a b f N (n + 1) ω =
    hittingBtwn f (Set.Ici b)
      (lowerCrossingTimeAux a f (upperCrossingTime a b f N n ω) N ω) N ω := by
  rw [upperCrossingTime]

/--
theorem `upperCrossingTime_succ_eq` / 定理 `upperCrossingTime_succ_eq`

English:
theorem upperCrossingTime_succ_eq
  given: (ω : Ω)
  statement: upperCrossingTime a b f N (n + 1) ω =
  proof: by
  simp only [upperCrossingTime_succ]
  rfl

中文:
定理 upperCrossingTime_succ_eq
  条件: (ω : Ω)
  结论: upperCrossingTime a b f N (n + 1) ω =
  证明: by
  simp only [upperCrossingTime_succ]
  rfl

Depends on / 依赖: upperCrossingTime_succ
-/
theorem upperCrossingTime_succ_eq (ω : Ω) : upperCrossingTime a b f N (n + 1) ω =
    hittingBtwn f (Set.Ici b) (lowerCrossingTime a b f N n ω) N ω := by
  simp only [upperCrossingTime_succ]
  rfl

end

section ConditionallyCompleteLinearOrderBot

variable [ConditionallyCompleteLinearOrderBot ι]
variable {a b : Real} {f : ι -> Ω -> Real} {N : ι} {n m : Nat} {ω : Ω}

/--
theorem `upperCrossingTime_le` / 定理 `upperCrossingTime_le`

English:
theorem upperCrossingTime_le
  statement: upperCrossingTime a b f N n ω <= N
  proof: by
  cases n
  · simp only [upperCrossingTime_zero, Pi.bot_apply, bot_le]
  · simp only [upperCrossingTime_succ, hittingBtwn_le]

@[simp]

中文:
定理 upperCrossingTime_le
  结论: upperCrossingTime a b f N n ω <= N
  证明: by
  cases n
  · simp only [upperCrossingTime_zero, Pi.bot_apply, bot_le]
  · simp only [upperCrossingTime_succ, hittingBtwn_le]

@[simp]

Depends on / 依赖: Pi.bot_apply, bot_apply, bot_le, hittingBtwn_le, upperCrossingTime_succ, upperCrossingTime_zero
-/
theorem upperCrossingTime_le : upperCrossingTime a b f N n ω <= N := by
  cases n
  · simp only [upperCrossingTime_zero, Pi.bot_apply, bot_le]
  · simp only [upperCrossingTime_succ, hittingBtwn_le]

@[simp]
/--
theorem `upperCrossingTime_zero'` / 定理 `upperCrossingTime_zero'`

English:
theorem upperCrossingTime_zero'
  statement: upperCrossingTime a b f ⊥ n ω = ⊥
  proof: eq_bot_iff.2 upperCrossingTime_le

中文:
定理 upperCrossingTime_zero'
  结论: upperCrossingTime a b f ⊥ n ω = ⊥
  证明: eq_bot_iff.2 upperCrossingTime_le

Depends on / 依赖: eq_bot_iff, upperCrossingTime_le
-/
theorem upperCrossingTime_zero' : upperCrossingTime a b f ⊥ n ω = ⊥ :=
  eq_bot_iff.2 upperCrossingTime_le

/--
theorem `lowerCrossingTime_le` / 定理 `lowerCrossingTime_le`

English:
theorem lowerCrossingTime_le
  statement: lowerCrossingTime a b f N n ω <= N
  proof: by
  simp only [lowerCrossingTime, hittingBtwn_le ω]

中文:
定理 lowerCrossingTime_le
  结论: lowerCrossingTime a b f N n ω <= N
  证明: by
  simp only [lowerCrossingTime, hittingBtwn_le ω]

Depends on / 依赖: hittingBtwn_le, lowerCrossingTime
-/
theorem lowerCrossingTime_le : lowerCrossingTime a b f N n ω <= N := by
  simp only [lowerCrossingTime, hittingBtwn_le ω]

/--
theorem `upperCrossingTime_le_lowerCrossingTime` / 定理 `upperCrossingTime_le_lowerCrossingTime`

English:
theorem upperCrossingTime_le_lowerCrossingTime
  proof: by
  simp only [lowerCrossingTime, le_hittingBtwn upperCrossingTime_le ω]

中文:
定理 upperCrossingTime_le_lowerCrossingTime
  证明: by
  simp only [lowerCrossingTime, le_hittingBtwn upperCrossingTime_le ω]

Depends on / 依赖: le_hittingBtwn, lowerCrossingTime, upperCrossingTime_le
-/
theorem upperCrossingTime_le_lowerCrossingTime :
    upperCrossingTime a b f N n ω <= lowerCrossingTime a b f N n ω := by
  simp only [lowerCrossingTime, le_hittingBtwn upperCrossingTime_le ω]

/--
theorem `lowerCrossingTime_le_upperCrossingTime_succ` / 定理 `lowerCrossingTime_le_upperCrossingTime_succ`

English:
theorem lowerCrossingTime_le_upperCrossingTime_succ
  proof: by
  rw [upperCrossingTime_succ]
  exact le_hittingBtwn lowerCrossingTime_le ω

中文:
定理 lowerCrossingTime_le_upperCrossingTime_succ
  证明: by
  rw [upperCrossingTime_succ]
  exact le_hittingBtwn lowerCrossingTime_le ω

Depends on / 依赖: DFinsupp, DFinsupp.iSup_range_lsingle, classical, iSup_range_lsingle, isSemisimpleModule_of_isSemisimpleModule_submodule, le_hittingBtwn, lowerCrossingTime_le, upperCrossingTime_succ
-/
theorem lowerCrossingTime_le_upperCrossingTime_succ :
    lowerCrossingTime a b f N n ω <= upperCrossingTime a b f N (n + 1) ω := by
  rw [upperCrossingTime_succ]
  exact le_hittingBtwn lowerCrossingTime_le ω

/--
theorem `lowerCrossingTime_mono` / 定理 `lowerCrossingTime_mono`

English:
theorem lowerCrossingTime_mono
  given: (hnm : n <= m)
  proof: by
  suffices Monotone fun n => lowerCrossingTime a b f N n ω by exact this hnm
  exact monotone_nat_of_le_succ fun n =>
    le_trans lowerCrossingTime_le_upperCrossingTime_succ upperCrossingTime_le_lowerCrossingTime

中文:
定理 lowerCrossingTime_mono
  条件: (hnm : n <= m)
  证明: by
  suffices Monotone fun n => lowerCrossingTime a b f N n ω by exact this hnm
  exact monotone_nat_of_le_succ fun n =>
    le_trans lowerCrossingTime_le_upperCrossingTime_succ upperCrossingTime_le_lowerCrossingTime

Depends on / 依赖: Monotone, le_trans, lowerCrossingTime, lowerCrossingTime_le_upperCrossingTime_succ, monotone_nat_of_le_succ, upperCrossingTime_le_lowerCrossingTime
-/
theorem lowerCrossingTime_mono (hnm : n <= m) :
    lowerCrossingTime a b f N n ω <= lowerCrossingTime a b f N m ω := by
  suffices Monotone fun n => lowerCrossingTime a b f N n ω by exact this hnm
  exact monotone_nat_of_le_succ fun n =>
    le_trans lowerCrossingTime_le_upperCrossingTime_succ upperCrossingTime_le_lowerCrossingTime

/--
theorem `upperCrossingTime_mono` / 定理 `upperCrossingTime_mono`

English:
theorem upperCrossingTime_mono
  given: (hnm : n <= m)
  proof: by
  suffices Monotone fun n => upperCrossingTime a b f N n ω by exact this hnm
  exact monotone_nat_of_le_succ fun n =>
    le_trans upperCrossingTime_le_lowerCrossingTime lowerCrossingTime_le_upperCrossingTime_succ

中文:
定理 upperCrossingTime_mono
  条件: (hnm : n <= m)
  证明: by
  suffices Monotone fun n => upperCrossingTime a b f N n ω by exact this hnm
  exact monotone_nat_of_le_succ fun n =>
    le_trans upperCrossingTime_le_lowerCrossingTime lowerCrossingTime_le_upperCrossingTime_succ

Depends on / 依赖: Monotone, le_trans, lowerCrossingTime_le_upperCrossingTime_succ, monotone_nat_of_le_succ, upperCrossingTime, upperCrossingTime_le_lowerCrossingTime
-/
theorem upperCrossingTime_mono (hnm : n <= m) :
    upperCrossingTime a b f N n ω <= upperCrossingTime a b f N m ω := by
  suffices Monotone fun n => upperCrossingTime a b f N n ω by exact this hnm
  exact monotone_nat_of_le_succ fun n =>
    le_trans upperCrossingTime_le_lowerCrossingTime lowerCrossingTime_le_upperCrossingTime_succ

end ConditionallyCompleteLinearOrderBot

variable {a b : Real} {f : Nat -> Ω -> Real} {N : Nat} {n m : Nat} {ω : Ω}

/--
theorem `stoppedValue_lowerCrossingTime` / 定理 `stoppedValue_lowerCrossingTime`

English:
theorem stoppedValue_lowerCrossingTime
  given: (h : lowerCrossingTime a b f N n ω != N)
  proof: by
  obtain ⟨j, hj₁, hj₂⟩ :=
    (hittingBtwn_le_iff_of_lt _ (lt_of_le_of_ne lowerCrossingTime_le h)).1 le_rfl
  exact stoppedValue_hittingBtwn_mem ⟨j, ⟨hj₁.1, le_trans hj₁.2 lowerCrossingTime_le⟩, hj₂⟩

中文:
定理 stoppedValue_lowerCrossingTime
  条件: (h : lowerCrossingTime a b f N n ω != N)
  证明: by
  obtain ⟨j, hj₁, hj₂⟩ :=
    (hittingBtwn_le_iff_of_lt _ (lt_of_le_of_ne lowerCrossingTime_le h)).1 le_rfl
  exact stoppedValue_hittingBtwn_mem ⟨j, ⟨hj₁.1, le_trans hj₁.2 lowerCrossingTime_le⟩, hj₂⟩

Depends on / 依赖: hittingBtwn_le_iff_of_lt, le_rfl, le_trans, lowerCrossingTime_le, lt_of_le_of_ne, stoppedValue_hittingBtwn_mem
-/
theorem stoppedValue_lowerCrossingTime (h : lowerCrossingTime a b f N n ω != N) :
    stoppedValue f (fun ω => (lowerCrossingTime a b f N n ω : Nat)) ω <= a := by
  obtain ⟨j, hj₁, hj₂⟩ :=
    (hittingBtwn_le_iff_of_lt _ (lt_of_le_of_ne lowerCrossingTime_le h)).1 le_rfl
  exact stoppedValue_hittingBtwn_mem ⟨j, ⟨hj₁.1, le_trans hj₁.2 lowerCrossingTime_le⟩, hj₂⟩

/--
theorem `stoppedValue_upperCrossingTime` / 定理 `stoppedValue_upperCrossingTime`

English:
theorem stoppedValue_upperCrossingTime
  given: (h : upperCrossingTime a b f N (n + 1) ω != N)
  proof: by
  obtain ⟨j, hj₁, hj₂⟩ :=
    (hittingBtwn_le_iff_of_lt _ (lt_of_le_of_ne upperCrossingTime_le h)).1 le_rfl
  exact stoppedValue_hittingBtwn_mem ⟨j, ⟨hj₁.1, le_trans hj₁.2 (hittingBtwn_le _)⟩, hj₂⟩

中文:
定理 stoppedValue_upperCrossingTime
  条件: (h : upperCrossingTime a b f N (n + 1) ω != N)
  证明: by
  obtain ⟨j, hj₁, hj₂⟩ :=
    (hittingBtwn_le_iff_of_lt _ (lt_of_le_of_ne upperCrossingTime_le h)).1 le_rfl
  exact stoppedValue_hittingBtwn_mem ⟨j, ⟨hj₁.1, le_trans hj₁.2 (hittingBtwn_le _)⟩, hj₂⟩

Depends on / 依赖: Submodule, Submodule.iSup_map_single, Submodule.pi_top, classical, hittingBtwn_le, hittingBtwn_le_iff_of_lt, iSup_map_single, isSemisimpleModule_of_isSemisimpleModule_submodule, le_rfl, le_trans, lt_of_le_of_ne, pi_top, range_eq_map, simp_rw, single, stoppedValue_hittingBtwn_mem, upperCrossingTime_le
-/
theorem stoppedValue_upperCrossingTime (h : upperCrossingTime a b f N (n + 1) ω != N) :
    b <= stoppedValue f (fun ω => (upperCrossingTime a b f N (n + 1) ω : Nat)) ω := by
  obtain ⟨j, hj₁, hj₂⟩ :=
    (hittingBtwn_le_iff_of_lt _ (lt_of_le_of_ne upperCrossingTime_le h)).1 le_rfl
  exact stoppedValue_hittingBtwn_mem ⟨j, ⟨hj₁.1, le_trans hj₁.2 (hittingBtwn_le _)⟩, hj₂⟩

/--
theorem `upperCrossingTime_lt_lowerCrossingTime` / 定理 `upperCrossingTime_lt_lowerCrossingTime`

English:
theorem upperCrossingTime_lt_lowerCrossingTime
  statement: (hab : a < b)
  proof: by
  refine lt_of_le_of_ne upperCrossingTime_le_lowerCrossingTime fun h =>
not_le.2 hab le_trans ?_ (stoppedValue_lowerCrossingTime hn)
  simp only [stoppedValue]
  rw [← h]
  exact stoppedValue_upperCrossingTime (h.symm ▸ hn)

中文:
定理 upperCrossingTime_lt_lowerCrossingTime
  结论: (hab : a < b)
  证明: by
  refine lt_of_le_of_ne upperCrossingTime_le_lowerCrossingTime fun h =>
not_le.2 hab le_trans ?_ (stoppedValue_lowerCrossingTime hn)
  simp only [stoppedValue]
  rw [← h]
  exact stoppedValue_upperCrossingTime (h.symm ▸ hn)

Depends on / 依赖: h.symm, le_trans, lt_of_le_of_ne, not_le, stoppedValue, stoppedValue_lowerCrossingTime, stoppedValue_upperCrossingTime, upperCrossingTime_le_lowerCrossingTime
-/
theorem upperCrossingTime_lt_lowerCrossingTime (hab : a < b)
    (hn : lowerCrossingTime a b f N (n + 1) ω != N) :
    upperCrossingTime a b f N (n + 1) ω < lowerCrossingTime a b f N (n + 1) ω := by
  refine lt_of_le_of_ne upperCrossingTime_le_lowerCrossingTime fun h =>
not_le.2 hab le_trans ?_ (stoppedValue_lowerCrossingTime hn)
  simp only [stoppedValue]
  rw [← h]
  exact stoppedValue_upperCrossingTime (h.symm ▸ hn)

/--
theorem `lowerCrossingTime_lt_upperCrossingTime` / 定理 `lowerCrossingTime_lt_upperCrossingTime`

English:
theorem lowerCrossingTime_lt_upperCrossingTime
  statement: (hab : a < b)
  proof: by
  refine lt_of_le_of_ne lowerCrossingTime_le_upperCrossingTime_succ fun h =>
not_le.2 hab le_trans (stoppedValue_upperCrossingTime hn) ?_
  simp only [stoppedValue]
  rw [← h]
  exact stoppedValue_lowerCrossingTime (h.symm ▸ hn)

中文:
定理 lowerCrossingTime_lt_upperCrossingTime
  结论: (hab : a < b)
  证明: by
  refine lt_of_le_of_ne lowerCrossingTime_le_upperCrossingTime_succ fun h =>
not_le.2 hab le_trans (stoppedValue_upperCrossingTime hn) ?_
  simp only [stoppedValue]
  rw [← h]
  exact stoppedValue_lowerCrossingTime (h.symm ▸ hn)

Depends on / 依赖: h.symm, le_trans, lowerCrossingTime_le_upperCrossingTime_succ, lt_of_le_of_ne, not_le, stoppedValue, stoppedValue_lowerCrossingTime, stoppedValue_upperCrossingTime
-/
theorem lowerCrossingTime_lt_upperCrossingTime (hab : a < b)
    (hn : upperCrossingTime a b f N (n + 1) ω != N) :
    lowerCrossingTime a b f N n ω < upperCrossingTime a b f N (n + 1) ω := by
  refine lt_of_le_of_ne lowerCrossingTime_le_upperCrossingTime_succ fun h =>
not_le.2 hab le_trans (stoppedValue_upperCrossingTime hn) ?_
  simp only [stoppedValue]
  rw [← h]
  exact stoppedValue_lowerCrossingTime (h.symm ▸ hn)

/--
theorem `upperCrossingTime_lt_succ` / 定理 `upperCrossingTime_lt_succ`

English:
theorem upperCrossingTime_lt_succ
  given: (hab : a < b) (hn : upperCrossingTime a b f N (n + 1) ω != N)
  proof: lt_of_le_of_lt upperCrossingTime_le_lowerCrossingTime
    (lowerCrossingTime_lt_upperCrossingTime hab hn)

中文:
定理 upperCrossingTime_lt_succ
  条件: (hab : a < b) (hn : upperCrossingTime a b f N (n + 1) ω != N)
  证明: lt_of_le_of_lt upperCrossingTime_le_lowerCrossingTime
    (lowerCrossingTime_lt_upperCrossingTime hab hn)

Depends on / 依赖: Finsupp, Finsupp.iSup_lsingle_range, LinearMap, LinearMap.quotKerEquivRange, iSup_lsingle_range, isSemisimpleModule_of_isSemisimpleModule_submodule, lowerCrossingTime_lt_upperCrossingTime, lt_of_le_of_lt, quotKerEquivRange, upperCrossingTime_le_lowerCrossingTime
-/
theorem upperCrossingTime_lt_succ (hab : a < b) (hn : upperCrossingTime a b f N (n + 1) ω != N) :
    upperCrossingTime a b f N n ω < upperCrossingTime a b f N (n + 1) ω :=
  lt_of_le_of_lt upperCrossingTime_le_lowerCrossingTime
    (lowerCrossingTime_lt_upperCrossingTime hab hn)

/--
theorem `lowerCrossingTime_stabilize` / 定理 `lowerCrossingTime_stabilize`

English:
theorem lowerCrossingTime_stabilize
  given: (hnm : n <= m) (hn : lowerCrossingTime a b f N n ω = N)
  proof: le_antisymm lowerCrossingTime_le (le_trans (le_of_eq hn.symm) (lowerCrossingTime_mono hnm))

中文:
定理 lowerCrossingTime_stabilize
  条件: (hnm : n <= m) (hn : lowerCrossingTime a b f N n ω = N)
  证明: le_antisymm lowerCrossingTime_le (le_trans (le_of_eq hn.symm) (lowerCrossingTime_mono hnm))

Depends on / 依赖: hn.symm, le_antisymm, le_of_eq, le_trans, lowerCrossingTime_le, lowerCrossingTime_mono
-/
theorem lowerCrossingTime_stabilize (hnm : n <= m) (hn : lowerCrossingTime a b f N n ω = N) :
    lowerCrossingTime a b f N m ω = N :=
  le_antisymm lowerCrossingTime_le (le_trans (le_of_eq hn.symm) (lowerCrossingTime_mono hnm))

/--
theorem `upperCrossingTime_stabilize` / 定理 `upperCrossingTime_stabilize`

English:
theorem upperCrossingTime_stabilize
  given: (hnm : n <= m) (hn : upperCrossingTime a b f N n ω = N)
  proof: le_antisymm upperCrossingTime_le (le_trans (le_of_eq hn.symm) (upperCrossingTime_mono hnm))

中文:
定理 upperCrossingTime_stabilize
  条件: (hnm : n <= m) (hn : upperCrossingTime a b f N n ω = N)
  证明: le_antisymm upperCrossingTime_le (le_trans (le_of_eq hn.symm) (upperCrossingTime_mono hnm))

Depends on / 依赖: hn.symm, le_antisymm, le_of_eq, le_trans, upperCrossingTime_le, upperCrossingTime_mono
-/
theorem upperCrossingTime_stabilize (hnm : n <= m) (hn : upperCrossingTime a b f N n ω = N) :
    upperCrossingTime a b f N m ω = N :=
  le_antisymm upperCrossingTime_le (le_trans (le_of_eq hn.symm) (upperCrossingTime_mono hnm))

/--
theorem `lowerCrossingTime_stabilize'` / 定理 `lowerCrossingTime_stabilize'`

English:
theorem lowerCrossingTime_stabilize'
  given: (hnm : n <= m) (hn : N <= lowerCrossingTime a b f N n ω)
  proof: lowerCrossingTime_stabilize hnm (le_antisymm lowerCrossingTime_le hn)

中文:
定理 lowerCrossingTime_stabilize'
  条件: (hnm : n <= m) (hn : N <= lowerCrossingTime a b f N n ω)
  证明: lowerCrossingTime_stabilize hnm (le_antisymm lowerCrossingTime_le hn)

Depends on / 依赖: AddMonoidHom, AddMonoidHom.id, Function, Function.bijective_id, IsSemisimpleModule, Module, Module.compHom, Pi.evalRingHom, bijective_id, compHom, evalRingHom, infer_instance, isSemisimpleModule_iff_of_bijective, le_antisymm, lowerCrossingTime_le, lowerCrossingTime_stabilize, map_smul
-/
theorem lowerCrossingTime_stabilize' (hnm : n <= m) (hn : N <= lowerCrossingTime a b f N n ω) :
    lowerCrossingTime a b f N m ω = N :=
  lowerCrossingTime_stabilize hnm (le_antisymm lowerCrossingTime_le hn)

/--
theorem `upperCrossingTime_stabilize'` / 定理 `upperCrossingTime_stabilize'`

English:
theorem upperCrossingTime_stabilize'
  given: (hnm : n <= m) (hn : N <= upperCrossingTime a b f N n ω)
  proof: upperCrossingTime_stabilize hnm (le_antisymm upperCrossingTime_le hn)

中文:
定理 upperCrossingTime_stabilize'
  条件: (hnm : n <= m) (hn : N <= upperCrossingTime a b f N n ω)
  证明: upperCrossingTime_stabilize hnm (le_antisymm upperCrossingTime_le hn)

Depends on / 依赖: le_antisymm, upperCrossingTime_le, upperCrossingTime_stabilize
-/
theorem upperCrossingTime_stabilize' (hnm : n <= m) (hn : N <= upperCrossingTime a b f N n ω) :
    upperCrossingTime a b f N m ω = N :=
  upperCrossingTime_stabilize hnm (le_antisymm upperCrossingTime_le hn)

-- `upperCrossingTime_bound_eq` provides an explicit bound
/--
theorem `exists_upperCrossingTime_eq` / 定理 `exists_upperCrossingTime_eq`

English:
theorem exists_upperCrossingTime_eq
  given: (f : Nat -> Ω -> Real) (N : Nat) (ω : Ω) (hab : a < b)
  proof: by
  by_contra! h
  have : StrictMono fun n => upperCrossingTime a b f N n ω :=
    strictMono_nat_of_lt_succ fun n => upperCrossingTime_lt_succ hab (h _)
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ :
      exists (m : _) (_ : m in Set.range fun n => upperCrossingTime a b f N n ω), N < m :=
    ⟨upperCrossingTime a 

中文:
定理 exists_upperCrossingTime_eq
  条件: (f : 自然数 -> Ω -> 实数) (N : 自然数) (ω : Ω) (hab : a < b)
  证明: by
  by_contra! h
  have : StrictMono fun n => upperCrossingTime a b f N n ω :=
    strictMono_nat_of_lt_succ fun n => upperCrossingTime_lt_succ hab (h _)
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ :
      exists (m : _) (_ : m in Set.range fun n => upperCrossingTime a b f N n ω), N < m :=
    ⟨upperCrossingTime a 

Depends on / 依赖: N.lt_succ_self, Set.range, StrictMono, StrictMono.id_le, id_le, lt_of_lt_of_le, lt_succ_self, not_le, strictMono_nat_of_lt_succ, upperCrossingTime, upperCrossingTime_le, upperCrossingTime_lt_succ
-/
theorem exists_upperCrossingTime_eq (f : Nat -> Ω -> Real) (N : Nat) (ω : Ω) (hab : a < b) :
    exists n, upperCrossingTime a b f N n ω = N := by
  by_contra! h
  have : StrictMono fun n => upperCrossingTime a b f N n ω :=
    strictMono_nat_of_lt_succ fun n => upperCrossingTime_lt_succ hab (h _)
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ :
      exists (m : _) (_ : m in Set.range fun n => upperCrossingTime a b f N n ω), N < m :=
    ⟨upperCrossingTime a b f N (N + 1) ω, ⟨N + 1, rfl⟩,
      lt_of_lt_of_le N.lt_succ_self (StrictMono.id_le this (N + 1))⟩
  exact not_le.2 hk upperCrossingTime_le

/--
theorem `upperCrossingTime_lt_bddAbove` / 定理 `upperCrossingTime_lt_bddAbove`

English:
theorem upperCrossingTime_lt_bddAbove
  given: (hab : a < b)
  proof: by
  obtain ⟨k, hk⟩ := exists_upperCrossingTime_eq f N ω hab
  refine ⟨k, fun n (hn : upperCrossingTime a b f N n ω < N) => ?_⟩
  by_contra hn'
  exact hn.ne (upperCrossingTime_stabilize (not_le.1 hn').le hk)

中文:
定理 upperCrossingTime_lt_bddAbove
  条件: (hab : a < b)
  证明: by
  obtain ⟨k, hk⟩ := exists_upperCrossingTime_eq f N ω hab
  refine ⟨k, fun n (hn : upperCrossingTime a b f N n ω < N) => ?_⟩
  by_contra hn'
  exact hn.ne (upperCrossingTime_stabilize (not_le.1 hn').le hk)

Depends on / 依赖: exists_upperCrossingTime_eq, hn.ne, not_le, upperCrossingTime, upperCrossingTime_stabilize
-/
theorem upperCrossingTime_lt_bddAbove (hab : a < b) :
    BddAbove {n | upperCrossingTime a b f N n ω < N} := by
  obtain ⟨k, hk⟩ := exists_upperCrossingTime_eq f N ω hab
  refine ⟨k, fun n (hn : upperCrossingTime a b f N n ω < N) => ?_⟩
  by_contra hn'
  exact hn.ne (upperCrossingTime_stabilize (not_le.1 hn').le hk)

/--
theorem `upperCrossingTime_lt_nonempty` / 定理 `upperCrossingTime_lt_nonempty`

English:
theorem upperCrossingTime_lt_nonempty
  given: (hN : 0 < N)
  proof: ⟨0, hN⟩

中文:
定理 upperCrossingTime_lt_nonempty
  条件: (hN : 0 < N)
  证明: ⟨0, hN⟩
-/
theorem upperCrossingTime_lt_nonempty (hN : 0 < N) :
    {n | upperCrossingTime a b f N n ω < N}.Nonempty :=
  ⟨0, hN⟩

/--
theorem `upperCrossingTime_bound_eq` / 定理 `upperCrossingTime_bound_eq`

English:
theorem upperCrossingTime_bound_eq
  given: (f : Nat -> Ω -> Real) (N : Nat) (ω : Ω) (hab : a < b)
  proof: by
  by_cases hN' : N < Nat.find (exists_upperCrossingTime_eq f N ω hab)
  · refine le_antisymm upperCrossingTime_le ?_
    have hmono : StrictMonoOn (fun n => upperCrossingTime a b f N n ω)
        (Set.Iic (Nat.find (exists_upperCrossingTime_eq f N ω hab)).pred) := by
      refine strictMonoOn_Iic

中文:
定理 upperCrossingTime_bound_eq
  条件: (f : 自然数 -> Ω -> 实数) (N : 自然数) (ω : Ω) (hab : a < b)
  证明: by
  by_cases hN' : N < Nat.find (exists_upperCrossingTime_eq f N ω hab)
  · refine le_antisymm upperCrossingTime_le ?_
    have hmono : StrictMonoOn (fun n => upperCrossingTime a b f N n ω)
        (Set.Iic (Nat.find (exists_upperCrossingTime_eq f N ω hab)).pred) := by
      refine strictMonoOn_Iic

Depends on / 依赖: Iic_id_le, Nat.find, Nat.find_min, Nat.le_sub_one_of_lt, Nat.lt_pred_iff, Set.Iic, StrictMonoOn, StrictMonoOn.Iic_id_le, convert, exists_upperCrossingTime_eq, find_min, le_antisymm, le_sub_one_of_lt, lt_pred_iff, not_lt, strictMonoOn_Iic_of_lt_succ, upperCrossingTime, upperCrossingTime_le, upperCrossingTime_lt_succ
-/
theorem upperCrossingTime_bound_eq (f : Nat -> Ω -> Real) (N : Nat) (ω : Ω) (hab : a < b) :
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

/--
theorem `upperCrossingTime_eq_of_bound_le` / 定理 `upperCrossingTime_eq_of_bound_le`

English:
theorem upperCrossingTime_eq_of_bound_le
  given: (hab : a < b) (hn : N <= n)
  proof: le_antisymm upperCrossingTime_le
    (le_trans (upperCrossingTime_bound_eq f N ω hab).symm.le (upperCrossingTime_mono hn))

中文:
定理 upperCrossingTime_eq_of_bound_le
  条件: (hab : a < b) (hn : N <= n)
  证明: le_antisymm upperCrossingTime_le
    (le_trans (upperCrossingTime_bound_eq f N ω hab).symm.le (upperCrossingTime_mono hn))

Depends on / 依赖: le_antisymm, le_trans, symm.le, upperCrossingTime_bound_eq, upperCrossingTime_le, upperCrossingTime_mono
-/
theorem upperCrossingTime_eq_of_bound_le (hab : a < b) (hn : N <= n) :
    upperCrossingTime a b f N n ω = N :=
  le_antisymm upperCrossingTime_le
    (le_trans (upperCrossingTime_bound_eq f N ω hab).symm.le (upperCrossingTime_mono hn))

variable {ℱ : Filtration Nat m0}

/--
theorem `StronglyAdapted.isStoppingTime_crossing` / 定理 `StronglyAdapted.isStoppingTime_crossing`

English:
theorem StronglyAdapted.isStoppingTime_crossing
  given: (hf : StronglyAdapted ℱ f)
  proof: by
  induction n with
  | zero =>
    refine ⟨isStoppingTime_const _ 0, ?_⟩
    simp only [lowerCrossingTime_zero, Nat.bot_eq_zero]
    exact hf.adapted.isStoppingTime_hittingBtwn measurableSet_Iic
  | succ k ih =>
    have : IsStoppingTime ℱ (fun ω => (upperCrossingTime a b f N (k + 1) ω : Nat)) :=

中文:
定理 StronglyAdapted.isStoppingTime_crossing
  条件: (hf : StronglyAdapted ℱ f)
  证明: by
  induction n with
  | zero =>
    refine ⟨isStoppingTime_const _ 0, ?_⟩
    simp only [lowerCrossingTime_zero, Nat.bot_eq_zero]
    exact hf.adapted.isStoppingTime_hittingBtwn measurableSet_Iic
  | succ k ih =>
    have : IsStoppingTime ℱ (fun ω => (upperCrossingTime a b f N (k + 1) ω : Nat)) :=

Depends on / 依赖: IsStoppingTime, Nat.bot_eq_zero, adapted, bot_eq_zero, hf.adapted.isStoppingTim, hf.adapted.isStoppingTime_hittingBtwn, hf.adapted.isStoppingTime_hittingBtwn_isStoppingTime, isStoppingTim, isStoppingTime_const, isStoppingTime_hittingBtwn, isStoppingTime_hittingBtwn_isStoppingTime, lowerCrossingTime_le, lowerCrossingTime_zero, measurableSet_Ici, measurableSet_Iic, simp_rw, upperCrossingTime, upperCrossingTime_succ_eq
-/
theorem StronglyAdapted.isStoppingTime_crossing (hf : StronglyAdapted ℱ f) :
    IsStoppingTime ℱ (fun ω => (upperCrossingTime a b f N n ω : Nat)) ∧
      IsStoppingTime ℱ (fun ω => (lowerCrossingTime a b f N n ω : Nat)) := by
  induction n with
  | zero =>
    refine ⟨isStoppingTime_const _ 0, ?_⟩
    simp only [lowerCrossingTime_zero, Nat.bot_eq_zero]
    exact hf.adapted.isStoppingTime_hittingBtwn measurableSet_Iic
  | succ k ih =>
    have : IsStoppingTime ℱ (fun ω => (upperCrossingTime a b f N (k + 1) ω : Nat)) := by
      intro n
      simp_rw [upperCrossingTime_succ_eq]
      refine hf.adapted.isStoppingTime_hittingBtwn_isStoppingTime ih.2 ?_ measurableSet_Ici _
      simp [lowerCrossingTime_le]
    refine ⟨this, fun n => ?_⟩
    refine hf.adapted.isStoppingTime_hittingBtwn_isStoppingTime this ?_ measurableSet_Iic _
    simp [upperCrossingTime_le]

/--
theorem `StronglyAdapted.isStoppingTime_upperCrossingTime` / 定理 `StronglyAdapted.isStoppingTime_upperCrossingTime`

English:
theorem StronglyAdapted.isStoppingTime_upperCrossingTime
  given: (hf : StronglyAdapted ℱ f)
  proof: hf.isStoppingTime_crossing.1

中文:
定理 StronglyAdapted.isStoppingTime_upperCrossingTime
  条件: (hf : StronglyAdapted ℱ f)
  证明: hf.isStoppingTime_crossing.1

Depends on / 依赖: hf.isStoppingTime_crossing, isStoppingTime_crossing
-/
theorem StronglyAdapted.isStoppingTime_upperCrossingTime (hf : StronglyAdapted ℱ f) :
    IsStoppingTime ℱ (fun ω => (upperCrossingTime a b f N n ω : Nat)) :=
  hf.isStoppingTime_crossing.1

/--
theorem `StronglyAdapted.isStoppingTime_lowerCrossingTime` / 定理 `StronglyAdapted.isStoppingTime_lowerCrossingTime`

English:
theorem StronglyAdapted.isStoppingTime_lowerCrossingTime
  given: (hf : StronglyAdapted ℱ f)
  proof: hf.isStoppingTime_crossing.2

中文:
定理 StronglyAdapted.isStoppingTime_lowerCrossingTime
  条件: (hf : StronglyAdapted ℱ f)
  证明: hf.isStoppingTime_crossing.2

Depends on / 依赖: hf.isStoppingTime_crossing, isStoppingTime_crossing
-/
theorem StronglyAdapted.isStoppingTime_lowerCrossingTime (hf : StronglyAdapted ℱ f) :
    IsStoppingTime ℱ (fun ω => (lowerCrossingTime a b f N n ω : Nat)) :=
  hf.isStoppingTime_crossing.2

/--
Definition of `upcrossingStrat` / `upcrossingStrat` 的定义

English:
definition upcrossingStrat
  signature: (a b : Real) (f : Nat -> Ω -> Real) (N n : Nat) (ω : Ω)
  body: ∑ k in Finset.range N,
    (Set.Ico (lowerCrossingTime a b f N k ω) (upperCrossingTime a b f N (k + 1) ω)).indicator 1 n

中文:
定义 upcrossingStrat
  签名: (a b : 实数) (f : 自然数 -> Ω -> 实数) (N n : 自然数) (ω : Ω)
  定义体: ∑ k in Finset.range N,
    (Set.Ico (lowerCrossingTime a b f N k ω) (upperCrossingTime a b f N (k + 1) ω)).indicator 1 n

Depends on / 依赖: Finset, Finset.range, Set.Ico, indicator, lowerCrossingTime, upperCrossingTime
-/
noncomputable def upcrossingStrat (a b : Real) (f : Nat -> Ω -> Real) (N n : Nat) (ω : Ω) : Real :=
  ∑ k in Finset.range N,
    (Set.Ico (lowerCrossingTime a b f N k ω) (upperCrossingTime a b f N (k + 1) ω)).indicator 1 n

/--
theorem `upcrossingStrat_nonneg` / 定理 `upcrossingStrat_nonneg`

English:
theorem upcrossingStrat_nonneg
  statement: 0 <= upcrossingStrat a b f N n ω
  proof: Finset.sum_nonneg fun _ _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _

中文:
定理 upcrossingStrat_nonneg
  结论: 0 <= upcrossingStrat a b f N n ω
  证明: Finset.sum_nonneg fun _ _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _

Depends on / 依赖: Finset, Finset.sum_nonneg, Set.indicator_nonneg, indicator_nonneg, sum_nonneg, zero_le_one
-/
theorem upcrossingStrat_nonneg : 0 <= upcrossingStrat a b f N n ω :=
  Finset.sum_nonneg fun _ _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _

/--
theorem `upcrossingStrat_le_one` / 定理 `upcrossingStrat_le_one`

English:
theorem upcrossingStrat_le_one
  statement: upcrossingStrat a b f N n ω <= 1
  proof: by
  rw [upcrossingStrat]; rw [← Finset.indicator_biUnion_apply]
  · exact Set.indicator_le_self' (fun _ _ => zero_le_one) _
  intro i _ j _ hij
  simp only [Set.Ico_disjoint_Ico]
  obtain hij' | hij' := lt_or_gt_of_ne hij
  · rw [min_eq_left (upperCrossingTime_mono (Nat.succ_le_succ hij'.le) :
    

中文:
定理 upcrossingStrat_le_one
  结论: upcrossingStrat a b f N n ω <= 1
  证明: by
  rw [upcrossingStrat]; rw [← Finset.indicator_biUnion_apply]
  · exact Set.indicator_le_self' (fun _ _ => zero_le_one) _
  intro i _ j _ hij
  simp only [Set.Ico_disjoint_Ico]
  obtain hij' | hij' := lt_or_gt_of_ne hij
  · rw [min_eq_left (upperCrossingTime_mono (Nat.succ_le_succ hij'.le) :
    

Depends on / 依赖: Finset, Finset.indicator_biUnion_apply, Ico_disjoint_Ico, Nat.succ_le_succ, Set.Ico_disjoint_Ico, Set.indicator_le_self, indicator_biUnion_apply, indicator_le_self, le_trans, lowerCrossingTime, lowerCrossingTime_mono, lt_or_gt_of_ne, max_eq_right, min_eq_left, succ_le_succ, upcrossingStrat, upperCrossingTime, upperCrossingTime_le_lo, upperCrossingTime_mono, zero_le_one
-/
theorem upcrossingStrat_le_one : upcrossingStrat a b f N n ω <= 1 := by
  rw [upcrossingStrat]; rw [← Finset.indicator_biUnion_apply]
  · exact Set.indicator_le_self' (fun _ _ => zero_le_one) _
  intro i _ j _ hij
  simp only [Set.Ico_disjoint_Ico]
  obtain hij' | hij' := lt_or_gt_of_ne hij
  · rw [min_eq_left (upperCrossingTime_mono (Nat.succ_le_succ hij'.le) :
      upperCrossingTime a b f N _ ω <= upperCrossingTime a b f N _ ω),
      max_eq_right (lowerCrossingTime_mono hij'.le :
        lowerCrossingTime a b f N _ _ <= lowerCrossingTime _ _ _ _ _ _)]
    refine le_trans upperCrossingTime_le_lowerCrossingTime
      (lowerCrossingTime_mono (Nat.succ_le_of_lt hij'))
  · rw [min_eq_right (upperCrossingTime_mono (Nat.succ_le_succ hij'.le) :
      upperCrossingTime a b f N _ ω <= upperCrossingTime a b f N _ ω),
      max_eq_left (lowerCrossingTime_mono hij'.le :
        lowerCrossingTime a b f N _ _ <= lowerCrossingTime _ _ _ _ _ _)]
    refine le_trans upperCrossingTime_le_lowerCrossingTime
      (lowerCrossingTime_mono (Nat.succ_le_of_lt hij'))

/--
theorem `StronglyAdapted.upcrossingStrat` / 定理 `StronglyAdapted.upcrossingStrat`

English:
theorem StronglyAdapted.upcrossingStrat
  given: (hf : StronglyAdapted ℱ f)
  proof: by
  intro n
  change StronglyMeasurable[ℱ n] fun ω =>
    ∑ k in Finset.range N, ({n | lowerCrossingTime a b f N k ω <= n} inter
      {n | n < upperCrossingTime a b f N (k + 1) ω}).indicator 1 n
  refine Finset.stronglyMeasurable_fun_sum _ fun i _ =>
    stronglyMeasurable_const.indicator ?_
  hav

中文:
定理 StronglyAdapted.upcrossingStrat
  条件: (hf : StronglyAdapted ℱ f)
  证明: by
  intro n
  change StronglyMeasurable[ℱ n] fun ω =>
    ∑ k in Finset.range N, ({n | lowerCrossingTime a b f N k ω <= n} inter
      {n | n < upperCrossingTime a b f N (k + 1) ω}).indicator 1 n
  refine Finset.stronglyMeasurable_fun_sum _ fun i _ =>
    stronglyMeasurable_const.indicator ?_
  hav

Depends on / 依赖: ENat.some_eq_natCast, Finset, Finset.range, Finset.stronglyMeasurable_fun_sum, Nat.cast_le, StronglyMeasurable, cast_le, hf.isStoppingTime_lowerCrossingTime, hf.isStoppingTime_upperCrossingTime, indicator, isStoppingTime_lowerCrossingTime, isStoppingTime_upperCrossingTime, lowerCrossingTime, some_eq_natCast, stronglyMeasurable_const, stronglyMeasurable_const.indicator, stronglyMeasurable_fun_sum, upperCrossingTime
-/
theorem StronglyAdapted.upcrossingStrat (hf : StronglyAdapted ℱ f) :
    StronglyAdapted ℱ (upcrossingStrat a b f N) := by
  intro n
  change StronglyMeasurable[ℱ n] fun ω =>
    ∑ k in Finset.range N, ({n | lowerCrossingTime a b f N k ω <= n} inter
      {n | n < upperCrossingTime a b f N (k + 1) ω}).indicator 1 n
  refine Finset.stronglyMeasurable_fun_sum _ fun i _ =>
    stronglyMeasurable_const.indicator ?_
  have hl := hf.isStoppingTime_lowerCrossingTime (a := a) (b := b) (N := N) (n := i) n
  have hu := hf.isStoppingTime_upperCrossingTime (a := a) (b := b) (N := N) (n := i + 1) n
  simp only [ENat.some_eq_natCast, Nat.cast_le] at hl hu
  simp_rw [← not_le]
  exact hl.inter hu.compl

/--
theorem `Submartingale.sum_upcrossingStrat_mul` / 定理 `Submartingale.sum_upcrossingStrat_mul`

English:
theorem Submartingale.sum_upcrossingStrat_mul
  statement: [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
  proof: hf.sum_mul_sub hf.stronglyAdapted.upcrossingStrat (fun _ _ => upcrossingStrat_le_one) fun _ _ =>
    upcrossingStrat_nonneg

中文:
定理 Submartingale.sum_upcrossingStrat_mul
  结论: [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
  证明: hf.sum_mul_sub hf.stronglyAdapted.upcrossingStrat (fun _ _ => upcrossingStrat_le_one) fun _ _ =>
    upcrossingStrat_nonneg

Depends on / 依赖: IsSemisimpleModule, IsSemisimpleModule.extension_property, extension_property, hf.stronglyAdapted.upcrossingStrat, hf.sum_mul_sub, isSimpleModule_iff_toSpanSingleton_surjective, isSimpleModule_iff_toSpanSingleton_surjective.mpr, ker_eq_bot, ker_eq_bot.mp, ker_toSpanSingleton, stronglyAdapted, sum_mul_sub, toSpanSingleton, upcrossingStrat, upcrossingStrat_le_one, upcrossingStrat_nonneg
-/
theorem Submartingale.sum_upcrossingStrat_mul [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (a b : Real) (N : Nat) : Submartingale (fun n : Nat =>
      ∑ k in Finset.range n, upcrossingStrat a b f N k * (f (k + 1) - f k)) ℱ μ :=
  hf.sum_mul_sub hf.stronglyAdapted.upcrossingStrat (fun _ _ => upcrossingStrat_le_one) fun _ _ =>
    upcrossingStrat_nonneg

/--
theorem `Submartingale.sum_sub_upcrossingStrat_mul` / 定理 `Submartingale.sum_sub_upcrossingStrat_mul`

English:
theorem Submartingale.sum_sub_upcrossingStrat_mul
  statement: [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
  proof: by
  refine hf.sum_mul_sub
    (fun n => (stronglyAdapted_const ℱ 1 n).sub (hf.stronglyAdapted.upcrossingStrat n))
    (?_ : forall n ω, (1 - upcrossingStrat a b f N n) ω <= 1) ?_
  · exact fun n ω => sub_le_self _ upcrossingStrat_nonneg
  · intro n ω
    simp [upcrossingStrat_le_one]

中文:
定理 Submartingale.sum_sub_upcrossingStrat_mul
  结论: [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
  证明: by
  refine hf.sum_mul_sub
    (fun n => (stronglyAdapted_const ℱ 1 n).sub (hf.stronglyAdapted.upcrossingStrat n))
    (?_ : forall n ω, (1 - upcrossingStrat a b f N n) ω <= 1) ?_
  · exact fun n ω => sub_le_self _ upcrossingStrat_nonneg
  · intro n ω
    simp [upcrossingStrat_le_one]

Depends on / 依赖: hf.stronglyAdapted.upcrossingStrat, hf.sum_mul_sub, stronglyAdapted, stronglyAdapted_const, sub_le_self, sum_mul_sub, upcrossingStrat, upcrossingStrat_le_one, upcrossingStrat_nonneg
-/
theorem Submartingale.sum_sub_upcrossingStrat_mul [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (a b : Real) (N : Nat) : Submartingale (fun n : Nat =>
      ∑ k in Finset.range n, (1 - upcrossingStrat a b f N k) * (f (k + 1) - f k)) ℱ μ := by
  refine hf.sum_mul_sub
    (fun n => (stronglyAdapted_const ℱ 1 n).sub (hf.stronglyAdapted.upcrossingStrat n))
    (?_ : forall n ω, (1 - upcrossingStrat a b f N n) ω <= 1) ?_
  · exact fun n ω => sub_le_self _ upcrossingStrat_nonneg
  · intro n ω
    simp [upcrossingStrat_le_one]

/--
theorem `Submartingale.sum_mul_upcrossingStrat_le` / 定理 `Submartingale.sum_mul_upcrossingStrat_le`

English:
theorem Submartingale.sum_mul_upcrossingStrat_le
  given: [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
  proof: by
  have h₁ : (0 : Real) <=
      μ[∑ k in Finset.range n, (1 - upcrossingStrat a b f N k) * (f (k + 1) - f k)] := by
    have := (hf.sum_sub_upcrossingStrat_mul a b N).setIntegral_le (zero_le (a := n)) .univ
    rw [setIntegral_univ]; rw [setIntegral_univ] at this
    refine le_trans ?_ this
    s

中文:
定理 Submartingale.sum_mul_upcrossingStrat_le
  条件: [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
  证明: by
  have h₁ : (0 : Real) <=
      μ[∑ k in Finset.range n, (1 - upcrossingStrat a b f N k) * (f (k + 1) - f k)] := by
    have := (hf.sum_sub_upcrossingStrat_mul a b N).setIntegral_le (zero_le (a := n)) .univ
    rw [setIntegral_univ]; rw [setIntegral_univ] at this
    refine le_trans ?_ this
    s

Depends on / 依赖: Finset, Finset.range, Finset.range_zero, Finset.sum_empty, hf.sum_sub_upcrossingStrat_mul, integral_zero, le_refl, le_trans, range_zero, setIntegral_le, setIntegral_univ, sum_empty, sum_sub_upcrossingStrat_mul, upcrossingStrat, zero_le
-/
theorem Submartingale.sum_mul_upcrossingStrat_le [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ) :
    μ[∑ k in Finset.range n, upcrossingStrat a b f N k * (f (k + 1) - f k)] <= μ[f n] - μ[f 0] := by
  have h₁ : (0 : Real) <=
      μ[∑ k in Finset.range n, (1 - upcrossingStrat a b f N k) * (f (k + 1) - f k)] := by
    have := (hf.sum_sub_upcrossingStrat_mul a b N).setIntegral_le (zero_le (a := n)) .univ
    rw [setIntegral_univ]; rw [setIntegral_univ] at this
    refine le_trans ?_ this
    simp only [Finset.range_zero, Finset.sum_empty, integral_zero', le_refl]
  have h₂ : μ[∑ k in Finset.range n, (1 - upcrossingStrat a b f N k) * (f (k + 1) - f k)] =
    μ[∑ k in Finset.range n, (f (k + 1) - f k)] -
      μ[∑ k in Finset.range n, upcrossingStrat a b f N k * (f (k + 1) - f k)] := by
    simp only [sub_mul, one_mul, Finset.sum_sub_distrib, Pi.sub_apply, Finset.sum_apply,
      Pi.mul_apply]
    refine integral_sub (Integrable.sub (integrable_finsetSum _ fun i _ => hf.integrable _)
      (integrable_finsetSum _ fun i _ => hf.integrable _)) ?_
    convert! (hf.sum_upcrossingStrat_mul a b N).integrable n using 1
    ext; simp
  rw [h₂]; rw [sub_nonneg] at h₁
  refine le_trans h₁ ?_
  simp_rw [Finset.sum_range_sub, integral_sub' (hf.integrable _) (hf.integrable _), le_refl]

/--
Definition of `upcrossingsBefore` / `upcrossingsBefore` 的定义

English:
definition upcrossingsBefore
  signature: [Preorder ι] [OrderBot ι] [InfSet ι] (a b : Real) (f : ι -> Ω -> Real)
  body: sSup {n | upperCrossingTime a b f N n ω < N}

@[simp]

中文:
定义 upcrossingsBefore
  签名: [Preorder ι] [OrderBot ι] [InfSet ι] (a b : 实数) (f : ι -> Ω -> 实数)
  定义体: sSup {n | upperCrossingTime a b f N n ω < N}

@[simp]

Depends on / 依赖: upperCrossingTime
-/
noncomputable def upcrossingsBefore [Preorder ι] [OrderBot ι] [InfSet ι] (a b : Real) (f : ι -> Ω -> Real)
    (N : ι) (ω : Ω) : Nat :=
  sSup {n | upperCrossingTime a b f N n ω < N}

@[simp]
/--
theorem `upcrossingsBefore_bot` / 定理 `upcrossingsBefore_bot`

English:
theorem upcrossingsBefore_bot
  statement: [Preorder ι] [OrderBot ι] [InfSet ι] {a b : Real} {f : ι -> Ω -> Real}
  proof: by simp [upcrossingsBefore]

中文:
定理 upcrossingsBefore_bot
  结论: [Preorder ι] [OrderBot ι] [InfSet ι] {a b : 实数} {f : ι -> Ω -> 实数}
  证明: by simp [upcrossingsBefore]

Depends on / 依赖: upcrossingsBefore
-/
theorem upcrossingsBefore_bot [Preorder ι] [OrderBot ι] [InfSet ι] {a b : Real} {f : ι -> Ω -> Real}
    {ω : Ω} : upcrossingsBefore a b f ⊥ ω = ⊥ := by simp [upcrossingsBefore]

/--
theorem `upcrossingsBefore_zero` / 定理 `upcrossingsBefore_zero`

English:
theorem upcrossingsBefore_zero
  statement: upcrossingsBefore a b f 0 ω = 0
  proof: by simp [upcrossingsBefore]

@[simp]

中文:
定理 upcrossingsBefore_zero
  结论: upcrossingsBefore a b f 0 ω = 0
  证明: by simp [upcrossingsBefore]

@[simp]

Depends on / 依赖: upcrossingsBefore
-/
theorem upcrossingsBefore_zero : upcrossingsBefore a b f 0 ω = 0 := by simp [upcrossingsBefore]

@[simp]
/--
theorem `upcrossingsBefore_zero'` / 定理 `upcrossingsBefore_zero'`

English:
theorem upcrossingsBefore_zero'
  statement: upcrossingsBefore a b f 0 = 0
  proof: by
  ext ω; exact upcrossingsBefore_zero

中文:
定理 upcrossingsBefore_zero'
  结论: upcrossingsBefore a b f 0 = 0
  证明: by
  ext ω; exact upcrossingsBefore_zero

Depends on / 依赖: upcrossingsBefore_zero
-/
theorem upcrossingsBefore_zero' : upcrossingsBefore a b f 0 = 0 := by
  ext ω; exact upcrossingsBefore_zero

/--
theorem `upperCrossingTime_lt_of_le_upcrossingsBefore` / 定理 `upperCrossingTime_lt_of_le_upcrossingsBefore`

English:
theorem upperCrossingTime_lt_of_le_upcrossingsBefore
  statement: (hN : 0 < N) (hab : a < b)
  proof: haveI : upperCrossingTime a b f N (upcrossingsBefore a b f N ω) ω < N :=
    (upperCrossingTime_lt_nonempty hN).csSup_mem
      ((OrderBot.bddBelow _).finite_of_bddAbove (upperCrossingTime_lt_bddAbove hab))
  lt_of_le_of_lt (upperCrossingTime_mono hn) this

中文:
定理 upperCrossingTime_lt_of_le_upcrossingsBefore
  结论: (hN : 0 < N) (hab : a < b)
  证明: haveI : upperCrossingTime a b f N (upcrossingsBefore a b f N ω) ω < N :=
    (upperCrossingTime_lt_nonempty hN).csSup_mem
      ((OrderBot.bddBelow _).finite_of_bddAbove (upperCrossingTime_lt_bddAbove hab))
  lt_of_le_of_lt (upperCrossingTime_mono hn) this

Depends on / 依赖: OrderBot, OrderBot.bddBelow, bddBelow, csSup_mem, finite_of_bddAbove, lt_of_le_of_lt, upcrossingsBefore, upperCrossingTime, upperCrossingTime_lt_bddAbove, upperCrossingTime_lt_nonempty, upperCrossingTime_mono
-/
theorem upperCrossingTime_lt_of_le_upcrossingsBefore (hN : 0 < N) (hab : a < b)
    (hn : n <= upcrossingsBefore a b f N ω) : upperCrossingTime a b f N n ω < N :=
  haveI : upperCrossingTime a b f N (upcrossingsBefore a b f N ω) ω < N :=
    (upperCrossingTime_lt_nonempty hN).csSup_mem
      ((OrderBot.bddBelow _).finite_of_bddAbove (upperCrossingTime_lt_bddAbove hab))
  lt_of_le_of_lt (upperCrossingTime_mono hn) this

/--
theorem `upperCrossingTime_eq_of_upcrossingsBefore_lt` / 定理 `upperCrossingTime_eq_of_upcrossingsBefore_lt`

English:
theorem upperCrossingTime_eq_of_upcrossingsBefore_lt
  statement: (hab : a < b)
  proof: by
  refine le_antisymm upperCrossingTime_le (not_lt.1 ?_)
  convert! notMem_of_csSup_lt hn (upperCrossingTime_lt_bddAbove hab) using 1

中文:
定理 upperCrossingTime_eq_of_upcrossingsBefore_lt
  结论: (hab : a < b)
  证明: by
  refine le_antisymm upperCrossingTime_le (not_lt.1 ?_)
  convert! notMem_of_csSup_lt hn (upperCrossingTime_lt_bddAbove hab) using 1

Depends on / 依赖: convert, le_antisymm, notMem_of_csSup_lt, not_lt, upperCrossingTime_le, upperCrossingTime_lt_bddAbove
-/
theorem upperCrossingTime_eq_of_upcrossingsBefore_lt (hab : a < b)
    (hn : upcrossingsBefore a b f N ω < n) : upperCrossingTime a b f N n ω = N := by
  refine le_antisymm upperCrossingTime_le (not_lt.1 ?_)
  convert! notMem_of_csSup_lt hn (upperCrossingTime_lt_bddAbove hab) using 1

/--
theorem `upcrossingsBefore_le` / 定理 `upcrossingsBefore_le`

English:
theorem upcrossingsBefore_le
  given: (f : Nat -> Ω -> Real) (ω : Ω) (hab : a < b)
  proof: by
  by_cases hN : N = 0
  · subst hN
    rw [upcrossingsBefore_zero]
  · refine csSup_le ⟨0, zero_lt_iff.2 hN⟩ fun n (hn : _ < N) => ?_
    by_contra hnN
    exact hn.ne (upperCrossingTime_eq_of_bound_le hab (not_le.1 hnN).le)

中文:
定理 upcrossingsBefore_le
  条件: (f : 自然数 -> Ω -> 实数) (ω : Ω) (hab : a < b)
  证明: by
  by_cases hN : N = 0
  · subst hN
    rw [upcrossingsBefore_zero]
  · refine csSup_le ⟨0, zero_lt_iff.2 hN⟩ fun n (hn : _ < N) => ?_
    by_contra hnN
    exact hn.ne (upperCrossingTime_eq_of_bound_le hab (not_le.1 hnN).le)

Depends on / 依赖: csSup_le, hn.ne, not_le, upcrossingsBefore_zero, upperCrossingTime_eq_of_bound_le, zero_lt_iff
-/
theorem upcrossingsBefore_le (f : Nat -> Ω -> Real) (ω : Ω) (hab : a < b) :
    upcrossingsBefore a b f N ω <= N := by
  by_cases hN : N = 0
  · subst hN
    rw [upcrossingsBefore_zero]
  · refine csSup_le ⟨0, zero_lt_iff.2 hN⟩ fun n (hn : _ < N) => ?_
    by_contra hnN
    exact hn.ne (upperCrossingTime_eq_of_bound_le hab (not_le.1 hnN).le)

/--
theorem `crossing_eq_crossing_of_lowerCrossingTime_lt` / 定理 `crossing_eq_crossing_of_lowerCrossingTime_lt`

English:
theorem crossing_eq_crossing_of_lowerCrossingTime_lt
  statement: {M : Nat} (hNM : N <= M)
  proof: by
  have h' : upperCrossingTime a b f N n ω < N :=
    lt_of_le_of_lt upperCrossingTime_le_lowerCrossingTime h
  induction n with
  | zero =>
    simp only [upperCrossingTime_zero, bot_eq_zero',
      lowerCrossingTime_zero, true_and, eq_comm]
    refine hittingBtwn_eq_hittingBtwn_of_exists hNM ?_


中文:
定理 crossing_eq_crossing_of_lowerCrossingTime_lt
  结论: {M : 自然数} (hNM : N <= M)
  证明: by
  have h' : upperCrossingTime a b f N n ω < N :=
    lt_of_le_of_lt upperCrossingTime_le_lowerCrossingTime h
  induction n with
  | zero =>
    simp only [upperCrossingTime_zero, bot_eq_zero',
      lowerCrossingTime_zero, true_and, eq_comm]
    refine hittingBtwn_eq_hittingBtwn_of_exists hNM ?_


Depends on / 依赖: Nat.le_succ, bot_eq_zero, eq_comm, hittingBtwn_eq_hittingBtwn_of_exists, hittingBtwn_lt_iff, le_rfl, le_succ, lowerCrossingTime, lowerCrossingTime_mono, lowerCrossingTime_zero, lt_o, lt_of_le_of_lt, specialize, true_and, upperCrossingTime, upperCrossingTime_le_lowerCrossingTime, upperCrossingTime_zero
-/
theorem crossing_eq_crossing_of_lowerCrossingTime_lt {M : Nat} (hNM : N <= M)
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
    rw [lowerCrossingTime]; rw [hittingBtwn_lt_iff] at h
    · obtain ⟨j, hj₁, hj₂⟩ := h
      exact ⟨j, ⟨hj₁.1, hj₁.2.le⟩, hj₂⟩
    · exact le_rfl
  | succ k ih =>
    specialize ih (lt_of_le_of_lt (lowerCrossingTime_mono (Nat.le_succ _)) h)
      (lt_of_le_of_lt (upperCrossingTime_mono (Nat.le_succ _)) h')
    have : upperCrossingTime a b f M k.succ ω = upperCrossingTime a b f N k.succ ω := by
      rw [upperCrossingTime_succ_eq]; rw [hittingBtwn_lt_iff] at h'
      · simp only [upperCrossingTime_succ_eq]
        obtain ⟨j, hj₁, hj₂⟩ := h'
        rw [eq_comm]; rw [ih.2]
        exact hittingBtwn_eq_hittingBtwn_of_exists hNM ⟨j, ⟨hj₁.1, hj₁.2.le⟩, hj₂⟩
      · exact le_rfl
    refine ⟨this, ?_⟩
    simp only [lowerCrossingTime, eq_comm, this, Nat.succ_eq_add_one]
    refine hittingBtwn_eq_hittingBtwn_of_exists hNM ?_
    rw [lowerCrossingTime]; rw [hittingBtwn_lt_iff _ le_rfl] at h
    obtain ⟨j, hj₁, hj₂⟩ := h
    exact ⟨j, ⟨hj₁.1, hj₁.2.le⟩, hj₂⟩

/--
theorem `crossing_eq_crossing_of_upperCrossingTime_lt` / 定理 `crossing_eq_crossing_of_upperCrossingTime_lt`

English:
theorem crossing_eq_crossing_of_upperCrossingTime_lt
  statement: {M : Nat} (hNM : N <= M)
  proof: by
  have := (crossing_eq_crossing_of_lowerCrossingTime_lt hNM
    (lt_of_le_of_lt lowerCrossingTime_le_upperCrossingTime_succ h)).2
  refine ⟨?_, this⟩
  rw [upperCrossingTime_succ_eq]; rw [upperCrossingTime_succ_eq]; rw [eq_comm]; rw [this]
  refine hittingBtwn_eq_hittingBtwn_of_exists hNM ?_
  rw

中文:
定理 crossing_eq_crossing_of_upperCrossingTime_lt
  结论: {M : 自然数} (hNM : N <= M)
  证明: by
  have := (crossing_eq_crossing_of_lowerCrossingTime_lt hNM
    (lt_of_le_of_lt lowerCrossingTime_le_upperCrossingTime_succ h)).2
  refine ⟨?_, this⟩
  rw [upperCrossingTime_succ_eq]; rw [upperCrossingTime_succ_eq]; rw [eq_comm]; rw [this]
  refine hittingBtwn_eq_hittingBtwn_of_exists hNM ?_
  rw

Depends on / 依赖: crossing_eq_crossing_of_lowerCrossingTime_lt, eq_comm, hittingBtwn_eq_hittingBtwn_of_exists, hittingBtwn_lt_iff, le_rfl, lowerCrossingTime_le_upperCrossingTime_succ, lt_of_le_of_lt, upperCrossingTime_succ_eq
-/
theorem crossing_eq_crossing_of_upperCrossingTime_lt {M : Nat} (hNM : N <= M)
    (h : upperCrossingTime a b f N (n + 1) ω < N) :
    upperCrossingTime a b f M (n + 1) ω = upperCrossingTime a b f N (n + 1) ω ∧
      lowerCrossingTime a b f M n ω = lowerCrossingTime a b f N n ω := by
  have := (crossing_eq_crossing_of_lowerCrossingTime_lt hNM
    (lt_of_le_of_lt lowerCrossingTime_le_upperCrossingTime_succ h)).2
  refine ⟨?_, this⟩
  rw [upperCrossingTime_succ_eq]; rw [upperCrossingTime_succ_eq]; rw [eq_comm]; rw [this]
  refine hittingBtwn_eq_hittingBtwn_of_exists hNM ?_
  rw [upperCrossingTime_succ_eq]; rw [hittingBtwn_lt_iff] at h
  · obtain ⟨j, hj₁, hj₂⟩ := h
    exact ⟨j, ⟨hj₁.1, hj₁.2.le⟩, hj₂⟩
  · exact le_rfl

/--
theorem `upperCrossingTime_eq_upperCrossingTime_of_lt` / 定理 `upperCrossingTime_eq_upperCrossingTime_of_lt`

English:
theorem upperCrossingTime_eq_upperCrossingTime_of_lt
  statement: {M : Nat} (hNM : N <= M)
  proof: by
  cases n
  · simp
  · exact (crossing_eq_crossing_of_upperCrossingTime_lt hNM h).1

中文:
定理 upperCrossingTime_eq_upperCrossingTime_of_lt
  结论: {M : 自然数} (hNM : N <= M)
  证明: by
  cases n
  · simp
  · exact (crossing_eq_crossing_of_upperCrossingTime_lt hNM h).1

Depends on / 依赖: crossing_eq_crossing_of_upperCrossingTime_lt
-/
theorem upperCrossingTime_eq_upperCrossingTime_of_lt {M : Nat} (hNM : N <= M)
    (h : upperCrossingTime a b f N n ω < N) :
    upperCrossingTime a b f M n ω = upperCrossingTime a b f N n ω := by
  cases n
  · simp
  · exact (crossing_eq_crossing_of_upperCrossingTime_lt hNM h).1

/--
theorem `upcrossingsBefore_mono` / 定理 `upcrossingsBefore_mono`

English:
theorem upcrossingsBefore_mono
  given: (hab : a < b)
  statement: Monotone fun N ω => upcrossingsBefore a b f N ω
  proof: by
  intro N M hNM ω
  simp only [upcrossingsBefore]
  gcongr sSup {n | ?_} with n
  · exact upperCrossingTime_lt_bddAbove hab
  intro hn
  rw [upperCrossingTime_eq_upperCrossingTime_of_lt hNM hn]
  exact lt_of_lt_of_le hn hNM

中文:
定理 upcrossingsBefore_mono
  条件: (hab : a < b)
  结论: Monotone fun N ω => upcrossingsBefore a b f N ω
  证明: by
  intro N M hNM ω
  simp only [upcrossingsBefore]
  gcongr sSup {n | ?_} with n
  · exact upperCrossingTime_lt_bddAbove hab
  intro hn
  rw [upperCrossingTime_eq_upperCrossingTime_of_lt hNM hn]
  exact lt_of_lt_of_le hn hNM

Depends on / 依赖: lt_of_lt_of_le, upcrossingsBefore, upperCrossingTime_eq_upperCrossingTime_of_lt, upperCrossingTime_lt_bddAbove
-/
theorem upcrossingsBefore_mono (hab : a < b) : Monotone fun N ω => upcrossingsBefore a b f N ω := by
  intro N M hNM ω
  simp only [upcrossingsBefore]
  gcongr sSup {n | ?_} with n
  · exact upperCrossingTime_lt_bddAbove hab
  intro hn
  rw [upperCrossingTime_eq_upperCrossingTime_of_lt hNM hn]
  exact lt_of_lt_of_le hn hNM

/--
theorem `upcrossingsBefore_lt_of_exists_upcrossing` / 定理 `upcrossingsBefore_lt_of_exists_upcrossing`

English:
theorem upcrossingsBefore_lt_of_exists_upcrossing
  statement: (hab : a < b) {N₁ N₂ : Nat} (hN₁ : N <= N₁)
  proof: by
  refine lt_of_lt_of_le (Nat.lt_succ_self _) (le_csSup (upperCrossingTime_lt_bddAbove hab) ?_)
  rw [Set.mem_ofPred_eq]; rw [upperCrossingTime_succ_eq]; rw [hittingBtwn_lt_iff _ le_rfl]
  refine ⟨N₂, ⟨?_, Nat.lt_succ_self _⟩, hN₂'.le⟩
  rw [lowerCrossingTime]; rw [hittingBtwn_le_iff_of_lt _ (Nat.

中文:
定理 upcrossingsBefore_lt_of_exists_upcrossing
  结论: (hab : a < b) {N₁ N₂ : 自然数} (hN₁ : N <= N₁)
  证明: by
  refine lt_of_lt_of_le (Nat.lt_succ_self _) (le_csSup (upperCrossingTime_lt_bddAbove hab) ?_)
  rw [Set.mem_ofPred_eq]; rw [upperCrossingTime_succ_eq]; rw [hittingBtwn_lt_iff _ le_rfl]
  refine ⟨N₂, ⟨?_, Nat.lt_succ_self _⟩, hN₂'.le⟩
  rw [lowerCrossingTime]; rw [hittingBtwn_le_iff_of_lt _ (Nat.

Depends on / 依赖: Nat.lt_succ_self, Nat.sSup_mem, Set.mem_ofPred_eq, hittingBtwn_le_iff_of_lt, hittingBtwn_lt_iff, le_csSup, le_rfl, le_trans, lowerCrossingTime, lt_of_lt_of_le, lt_succ_self, mem_ofPred_eq, sSup_mem, upcrossingsBefore, upperCrossingTime, upperCrossingTime_lt_bddAbove, upperCrossingTime_lt_nonempty, upperCrossingTime_succ_eq
-/
theorem upcrossingsBefore_lt_of_exists_upcrossing (hab : a < b) {N₁ N₂ : Nat} (hN₁ : N <= N₁)
    (hN₁' : f N₁ ω < a) (hN₂ : N₁ <= N₂) (hN₂' : b < f N₂ ω) :
    upcrossingsBefore a b f N ω < upcrossingsBefore a b f (N₂ + 1) ω := by
  refine lt_of_lt_of_le (Nat.lt_succ_self _) (le_csSup (upperCrossingTime_lt_bddAbove hab) ?_)
  rw [Set.mem_ofPred_eq]; rw [upperCrossingTime_succ_eq]; rw [hittingBtwn_lt_iff _ le_rfl]
  refine ⟨N₂, ⟨?_, Nat.lt_succ_self _⟩, hN₂'.le⟩
  rw [lowerCrossingTime]; rw [hittingBtwn_le_iff_of_lt _ (Nat.lt_succ_self _)]
  refine ⟨N₁, ⟨le_trans ?_ hN₁, hN₂⟩, hN₁'.le⟩
  by_cases! hN : 0 < N
  · have : upperCrossingTime a b f N (upcrossingsBefore a b f N ω) ω < N :=
      Nat.sSup_mem (upperCrossingTime_lt_nonempty hN) (upperCrossingTime_lt_bddAbove hab)
    rw [upperCrossingTime_eq_upperCrossingTime_of_lt (hN₁.trans (hN₂.trans <| Nat.le_succ _))
      this]
    exact this.le
  · rw [Nat.le_zero] at hN
    rw [hN]; rw [upcrossingsBefore_zero]; rw [upperCrossingTime_zero]; rw [Pi.bot_apply]; rw [bot_eq_zero']

/--
theorem `lowerCrossingTime_lt_of_lt_upcrossingsBefore` / 定理 `lowerCrossingTime_lt_of_lt_upcrossingsBefore`

English:
theorem lowerCrossingTime_lt_of_lt_upcrossingsBefore
  statement: (hN : 0 < N) (hab : a < b)
  proof: lt_of_le_of_lt lowerCrossingTime_le_upperCrossingTime_succ
    (upperCrossingTime_lt_of_le_upcrossingsBefore hN hab hn)

中文:
定理 lowerCrossingTime_lt_of_lt_upcrossingsBefore
  结论: (hN : 0 < N) (hab : a < b)
  证明: lt_of_le_of_lt lowerCrossingTime_le_upperCrossingTime_succ
    (upperCrossingTime_lt_of_le_upcrossingsBefore hN hab hn)

Depends on / 依赖: lowerCrossingTime_le_upperCrossingTime_succ, lt_of_le_of_lt, upperCrossingTime_lt_of_le_upcrossingsBefore
-/
theorem lowerCrossingTime_lt_of_lt_upcrossingsBefore (hN : 0 < N) (hab : a < b)
    (hn : n < upcrossingsBefore a b f N ω) : lowerCrossingTime a b f N n ω < N :=
  lt_of_le_of_lt lowerCrossingTime_le_upperCrossingTime_succ
    (upperCrossingTime_lt_of_le_upcrossingsBefore hN hab hn)

/--
theorem `le_sub_of_le_upcrossingsBefore` / 定理 `le_sub_of_le_upcrossingsBefore`

English:
theorem le_sub_of_le_upcrossingsBefore
  statement: (hN : 0 < N) (hab : a < b)
  proof: sub_le_sub
    (stoppedValue_upperCrossingTime (upperCrossingTime_lt_of_le_upcrossingsBefore hN hab hn).ne)
    (stoppedValue_lowerCrossingTime (lowerCrossingTime_lt_of_lt_upcrossingsBefore hN hab hn).ne)

中文:
定理 le_sub_of_le_upcrossingsBefore
  结论: (hN : 0 < N) (hab : a < b)
  证明: sub_le_sub
    (stoppedValue_upperCrossingTime (upperCrossingTime_lt_of_le_upcrossingsBefore hN hab hn).ne)
    (stoppedValue_lowerCrossingTime (lowerCrossingTime_lt_of_lt_upcrossingsBefore hN hab hn).ne)

Depends on / 依赖: lowerCrossingTime_lt_of_lt_upcrossingsBefore, stoppedValue_lowerCrossingTime, stoppedValue_upperCrossingTime, sub_le_sub, upperCrossingTime_lt_of_le_upcrossingsBefore
-/
theorem le_sub_of_le_upcrossingsBefore (hN : 0 < N) (hab : a < b)
    (hn : n < upcrossingsBefore a b f N ω) :
    b - a <= stoppedValue f (fun ω => (upperCrossingTime a b f N (n + 1) ω : Nat)) ω -
      stoppedValue f (fun ω => (lowerCrossingTime a b f N n ω : Nat)) ω :=
  sub_le_sub
    (stoppedValue_upperCrossingTime (upperCrossingTime_lt_of_le_upcrossingsBefore hN hab hn).ne)
    (stoppedValue_lowerCrossingTime (lowerCrossingTime_lt_of_lt_upcrossingsBefore hN hab hn).ne)

/--
theorem `sub_eq_zero_of_upcrossingsBefore_lt` / 定理 `sub_eq_zero_of_upcrossingsBefore_lt`

English:
theorem sub_eq_zero_of_upcrossingsBefore_lt
  given: (hab : a < b) (hn : upcrossingsBefore a b f N ω < n)
  proof: by
  have : N <= upperCrossingTime a b f N n ω := by
    rw [upcrossingsBefore] at hn
    rw [← not_lt]
    exact fun h => not_le.2 hn (le_csSup (upperCrossingTime_lt_bddAbove hab) h)
  simp [stoppedValue, upperCrossingTime_stabilize' (Nat.le_succ n) this,
    lowerCrossingTime_stabilize' le_rfl (le

中文:
定理 sub_eq_zero_of_upcrossingsBefore_lt
  条件: (hab : a < b) (hn : upcrossingsBefore a b f N ω < n)
  证明: by
  have : N <= upperCrossingTime a b f N n ω := by
    rw [upcrossingsBefore] at hn
    rw [← not_lt]
    exact fun h => not_le.2 hn (le_csSup (upperCrossingTime_lt_bddAbove hab) h)
  simp [stoppedValue, upperCrossingTime_stabilize' (Nat.le_succ n) this,
    lowerCrossingTime_stabilize' le_rfl (le

Depends on / 依赖: Nat.le_succ, le_csSup, le_rfl, le_succ, le_trans, lowerCrossingTime_stabilize, not_le, not_lt, stoppedValue, upcrossingsBefore, upperCrossingTime, upperCrossingTime_le_lowerCrossingTime, upperCrossingTime_lt_bddAbove, upperCrossingTime_stabilize
-/
theorem sub_eq_zero_of_upcrossingsBefore_lt (hab : a < b) (hn : upcrossingsBefore a b f N ω < n) :
    stoppedValue f (fun ω => (upperCrossingTime a b f N (n + 1) ω : Nat)) ω -
      stoppedValue f (fun ω => (lowerCrossingTime a b f N n ω : Nat)) ω = 0 := by
  have : N <= upperCrossingTime a b f N n ω := by
    rw [upcrossingsBefore] at hn
    rw [← not_lt]
    exact fun h => not_le.2 hn (le_csSup (upperCrossingTime_lt_bddAbove hab) h)
  simp [stoppedValue, upperCrossingTime_stabilize' (Nat.le_succ n) this,
    lowerCrossingTime_stabilize' le_rfl (le_trans this upperCrossingTime_le_lowerCrossingTime)]

/--
theorem `mul_upcrossingsBefore_le` / 定理 `mul_upcrossingsBefore_le`

English:
theorem mul_upcrossingsBefore_le
  given: (hf : a <= f N ω) (hab : a < b)
  proof: by
  by_cases hN : N = 0
  · simp [hN]
  simp_rw [upcrossingStrat, Finset.sum_mul, ←
    Set.indicator_mul_left _ _ (fun x => (f (x + 1) - f x) ω), Pi.one_apply, Pi.sub_apply, one_mul]
  rw [Finset.sum_comm]
  have h₁ : forall k, ∑ n in Finset.range N, (Set.Ico (lowerCrossingTime a b f N k ω)
      

中文:
定理 mul_upcrossingsBefore_le
  条件: (hf : a <= f N ω) (hab : a < b)
  证明: by
  by_cases hN : N = 0
  · simp [hN]
  simp_rw [upcrossingStrat, Finset.sum_mul, ←
    Set.indicator_mul_left _ _ (fun x => (f (x + 1) - f x) ω), Pi.one_apply, Pi.sub_apply, one_mul]
  rw [Finset.sum_comm]
  have h₁ : forall k, ∑ n in Finset.range N, (Set.Ico (lowerCrossingTime a b f N k ω)
      

Depends on / 依赖: Finset, Finset.range, Finset.sum_comm, Finset.sum_mul, Pi.one_apply, Pi.sub_apply, Set.Ico, Set.indicator_mul_left, indicator, indicator_mul_left, lowerCrossingTime, one_apply, one_mul, simp_rw, stoppedValue, sub_apply, sum_comm, sum_mul, upcrossingStrat, upperCrossingTime
-/
theorem mul_upcrossingsBefore_le (hf : a <= f N ω) (hab : a < b) :
    (b - a) * upcrossingsBefore a b f N ω <=
    ∑ k in Finset.range N, upcrossingStrat a b f N k ω * (f (k + 1) - f k) ω := by
  by_cases hN : N = 0
  · simp [hN]
  simp_rw [upcrossingStrat, Finset.sum_mul, ←
    Set.indicator_mul_left _ _ (fun x => (f (x + 1) - f x) ω), Pi.one_apply, Pi.sub_apply, one_mul]
  rw [Finset.sum_comm]
  have h₁ : forall k, ∑ n in Finset.range N, (Set.Ico (lowerCrossingTime a b f N k ω)
      (upperCrossingTime a b f N (k + 1) ω)).indicator (fun m => f (m + 1) ω - f m ω) n =
      stoppedValue f (fun ω => (upperCrossingTime a b f N (k + 1) ω : Nat)) ω -
        stoppedValue f (fun ω => (lowerCrossingTime a b f N k ω : Nat)) ω := by
    intro k
    rw [Finset.sum_indicator_eq_sum_filter]; rw [(_ : Finset.filter (fun i => i in Set.Ico
      (lowerCrossingTime a b f N k ω) (upperCrossingTime a b f N (k + 1) ω)) (Finset.range N) =
      Finset.Ico (lowerCrossingTime a b f N k ω) (upperCrossingTime a b f N (k + 1) ω))]; rw [Finset.sum_Ico_eq_add_neg _ lowerCrossingTime_le_upperCrossingTime_succ]; rw [Finset.sum_range_sub fun n => f n ω]; rw [Finset.sum_range_sub fun n => f n ω]; rw [neg_sub]; rw [sub_add_sub_cancel]
    · rfl
    · ext i
      simp only [Set.mem_Ico, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico,
        and_iff_right_iff_imp, and_imp]
      exact fun _ h => lt_of_lt_of_le h upperCrossingTime_le
  simp_rw [h₁]
  have h₂ : ∑ _k in Finset.range (upcrossingsBefore a b f N ω), (b - a) <=
      ∑ k in Finset.range N, (stoppedValue f (fun ω => (upperCrossingTime a b f N (k + 1) ω : Nat)) ω -
        stoppedValue f (fun ω => (lowerCrossingTime a b f N k ω : Nat)) ω) := by
    calc
      ∑ _k in Finset.range (upcrossingsBefore a b f N ω), (b - a) <=
          ∑ k in Finset.range (upcrossingsBefore a b f N ω),
            (stoppedValue f (fun ω => (upperCrossingTime a b f N (k + 1) ω : Nat)) ω -
              stoppedValue f (fun ω => (lowerCrossingTime a b f N k ω : Nat)) ω) := by
        gcongr ∑ k in _, ?_ with i hi
        refine le_sub_of_le_upcrossingsBefore (zero_lt_iff.2 hN) hab ?_
        rwa [Finset.mem_range] at hi
      _ <= ∑ k in Finset.range N,
          (stoppedValue f (fun ω => (upperCrossingTime a b f N (k + 1) ω : Nat)) ω -
          stoppedValue f (fun ω => (lowerCrossingTime a b f N k ω : Nat)) ω) := by
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
          rw [Finset.mem_range]; rw [not_lt] at hi
          exact lt_of_le_of_ne hi (Ne.symm hi')
  refine le_trans ?_ h₂
  rw [Finset.sum_const]; rw [Finset.card_range]; rw [nsmul_eq_mul]; rw [mul_comm]

/--
theorem `integral_mul_upcrossingsBefore_le_integral` / 定理 `integral_mul_upcrossingsBefore_le_integral`

English:
theorem integral_mul_upcrossingsBefore_le_integral
  statement: [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
  proof: calc
    (b - a) * μ[upcrossingsBefore a b f N] <=
        μ[∑ k in Finset.range N, upcrossingStrat a b f N k * (f (k + 1) - f k)] := by
      rw [← integral_const_mul]
      refine integral_mono_of_nonneg ?_ ((hf.sum_upcrossingStrat_mul a b N).integrable N) ?_
      · exact Eventually.of_forall fun

中文:
定理 integral_mul_upcrossingsBefore_le_integral
  结论: [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
  证明: calc
    (b - a) * μ[upcrossingsBefore a b f N] <=
        μ[∑ k in Finset.range N, upcrossingStrat a b f N k * (f (k + 1) - f k)] := by
      rw [← integral_const_mul]
      refine integral_mono_of_nonneg ?_ ((hf.sum_upcrossingStrat_mul a b N).integrable N) ?_
      · exact Eventually.of_forall fun

Depends on / 依赖: Eventually, Eventually.of_forall, Finset, Finset.range, Nat.cast_nonneg, cast_nonneg, filter_upwards, hab.le, hf.sum_mul_upcrossingStrat_le, hf.sum_upcrossingStrat_mul, integr, integrable, integral_const_mul, integral_mono_of_nonneg, mul_nonneg, mul_upcrossingsBefore_le, of_forall, sub_le_self_iff, sub_nonneg, sum_mul_upcrossingStrat_le
-/
theorem integral_mul_upcrossingsBefore_le_integral [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hfN : forall ω, a <= f N ω) (hfzero : 0 <= f 0) (hab : a < b) :
    (b - a) * μ[upcrossingsBefore a b f N] <= μ[f N] :=
  calc
    (b - a) * μ[upcrossingsBefore a b f N] <=
        μ[∑ k in Finset.range N, upcrossingStrat a b f N k * (f (k + 1) - f k)] := by
      rw [← integral_const_mul]
      refine integral_mono_of_nonneg ?_ ((hf.sum_upcrossingStrat_mul a b N).integrable N) ?_
      · exact Eventually.of_forall fun ω => mul_nonneg (sub_nonneg.2 hab.le) (Nat.cast_nonneg _)
      · filter_upwards with ω
        simpa using mul_upcrossingsBefore_le (hfN ω) hab
    _ <= μ[f N] - μ[f 0] := hf.sum_mul_upcrossingStrat_le
    _ <= μ[f N] := (sub_le_self_iff _).2 (integral_nonneg hfzero)

/--
theorem `crossing_pos_eq` / 定理 `crossing_pos_eq`

English:
theorem crossing_pos_eq
  given: (hab : a < b)
  proof: by
  have hab' : 0 < b - a := sub_pos.2 hab
  have hf : forall ω i, b - a <= (f i ω - a)⁺ ↔ b <= f i ω := by
    intro i ω
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rwa [← sub_le_sub_iff_right a, ←
        posPart_eq_of_posPart_pos (lt_of_lt_of_le hab' h)]
    · rw [← sub_le_sub_iff_right a] at h


中文:
定理 crossing_pos_eq
  条件: (hab : a < b)
  证明: by
  have hab' : 0 < b - a := sub_pos.2 hab
  have hf : forall ω i, b - a <= (f i ω - a)⁺ ↔ b <= f i ω := by
    intro i ω
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rwa [← sub_le_sub_iff_right a, ←
        posPart_eq_of_posPart_pos (lt_of_lt_of_le hab' h)]
    · rw [← sub_le_sub_iff_right a] at h


Depends on / 依赖: le_trans, lowerCrossingTime_zero, lt_of_lt_of_le, posPart_eq_of_posPart_pos, posPart_eq_self, posPart_nonpos, sub_le_sub_iff_right, sub_nonpos, sub_pos, unfoldPartialApp
-/
theorem crossing_pos_eq (hab : a < b) :
    upperCrossingTime 0 (b - a) (fun n ω => (f n ω - a)⁺) N n = upperCrossingTime a b f N n ∧
      lowerCrossingTime 0 (b - a) (fun n ω => (f n ω - a)⁺) N n = lowerCrossingTime a b f N n := by
  have hab' : 0 < b - a := sub_pos.2 hab
  have hf : forall ω i, b - a <= (f i ω - a)⁺ ↔ b <= f i ω := by
    intro i ω
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rwa [← sub_le_sub_iff_right a, ←
        posPart_eq_of_posPart_pos (lt_of_lt_of_le hab' h)]
    · rw [← sub_le_sub_iff_right a] at h
      rwa [posPart_eq_self.2 (le_trans hab'.le h)]
  have hf' (ω i) : (f i ω - a)⁺ <= 0 ↔ f i ω <= a := by rw [posPart_nonpos, sub_nonpos]
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

/--
theorem `upcrossingsBefore_pos_eq` / 定理 `upcrossingsBefore_pos_eq`

English:
theorem upcrossingsBefore_pos_eq
  given: (hab : a < b)
  proof: by
  simp_rw [upcrossingsBefore, (crossing_pos_eq hab).1]

中文:
定理 upcrossingsBefore_pos_eq
  条件: (hab : a < b)
  证明: by
  simp_rw [upcrossingsBefore, (crossing_pos_eq hab).1]

Depends on / 依赖: crossing_pos_eq, simp_rw, upcrossingsBefore
-/
theorem upcrossingsBefore_pos_eq (hab : a < b) :
    upcrossingsBefore 0 (b - a) (fun n ω => (f n ω - a)⁺) N ω = upcrossingsBefore a b f N ω := by
  simp_rw [upcrossingsBefore, (crossing_pos_eq hab).1]

/--
theorem `mul_integral_upcrossingsBefore_le_integral_pos_part_aux` / 定理 `mul_integral_upcrossingsBefore_le_integral_pos_part_aux`

English:
theorem mul_integral_upcrossingsBefore_le_integral_pos_part_aux
  statement: [IsFiniteMeasure μ]
  proof: by
  refine le_trans (le_of_eq ?_)
    (integral_mul_upcrossingsBefore_le_integral (hf.sub_martingale (martingale_const _ _ _)).pos
      (fun ω => posPart_nonneg _)
      (fun ω => posPart_nonneg _) (sub_pos.2 hab))
  simp_rw [sub_zero, ← upcrossingsBefore_pos_eq hab]
  rfl

中文:
定理 mul_integral_upcrossingsBefore_le_integral_pos_part_aux
  结论: [IsFiniteMeasure μ]
  证明: by
  refine le_trans (le_of_eq ?_)
    (integral_mul_upcrossingsBefore_le_integral (hf.sub_martingale (martingale_const _ _ _)).pos
      (fun ω => posPart_nonneg _)
      (fun ω => posPart_nonneg _) (sub_pos.2 hab))
  simp_rw [sub_zero, ← upcrossingsBefore_pos_eq hab]
  rfl

Depends on / 依赖: hf.sub_martingale, integral_mul_upcrossingsBefore_le_integral, le_of_eq, le_trans, martingale_const, posPart_nonneg, simp_rw, sub_martingale, sub_pos, sub_zero, upcrossingsBefore_pos_eq
-/
theorem mul_integral_upcrossingsBefore_le_integral_pos_part_aux [IsFiniteMeasure μ]
    (hf : Submartingale f ℱ μ) (hab : a < b) :
    (b - a) * μ[upcrossingsBefore a b f N] <= μ[fun ω => (f N ω - a)⁺] := by
  refine le_trans (le_of_eq ?_)
    (integral_mul_upcrossingsBefore_le_integral (hf.sub_martingale (martingale_const _ _ _)).pos
      (fun ω => posPart_nonneg _)
      (fun ω => posPart_nonneg _) (sub_pos.2 hab))
  simp_rw [sub_zero, ← upcrossingsBefore_pos_eq hab]
  rfl

/--
theorem `Submartingale.mul_integral_upcrossingsBefore_le_integral_pos_part` / 定理 `Submartingale.mul_integral_upcrossingsBefore_le_integral_pos_part`

English:
theorem Submartingale.mul_integral_upcrossingsBefore_le_integral_pos_part
  statement: [IsFiniteMeasure μ]
  proof: by
  by_cases! hab : a < b
  · exact mul_integral_upcrossingsBefore_le_integral_pos_part_aux hf hab
  · rw [← sub_nonpos] at hab
    exact le_trans (mul_nonpos_of_nonpos_of_nonneg hab (by positivity))
      (integral_nonneg fun ω => posPart_nonneg _)

中文:
定理 Submartingale.mul_integral_upcrossingsBefore_le_integral_pos_part
  结论: [IsFiniteMeasure μ]
  证明: by
  by_cases! hab : a < b
  · exact mul_integral_upcrossingsBefore_le_integral_pos_part_aux hf hab
  · rw [← sub_nonpos] at hab
    exact le_trans (mul_nonpos_of_nonpos_of_nonneg hab (by positivity))
      (integral_nonneg fun ω => posPart_nonneg _)

Depends on / 依赖: integral_nonneg, le_trans, mul_integral_upcrossingsBefore_le_integral_pos_part_aux, mul_nonpos_of_nonpos_of_nonneg, posPart_nonneg, sub_nonpos
-/
theorem Submartingale.mul_integral_upcrossingsBefore_le_integral_pos_part [IsFiniteMeasure μ]
    (a b : Real) (hf : Submartingale f ℱ μ) (N : Nat) :
    (b - a) * μ[upcrossingsBefore a b f N] <= μ[fun ω => (f N ω - a)⁺] := by
  by_cases! hab : a < b
  · exact mul_integral_upcrossingsBefore_le_integral_pos_part_aux hf hab
  · rw [← sub_nonpos] at hab
    exact le_trans (mul_nonpos_of_nonpos_of_nonneg hab (by positivity))
      (integral_nonneg fun ω => posPart_nonneg _)



/--
theorem `upcrossingsBefore_eq_sum` / 定理 `upcrossingsBefore_eq_sum`

English:
theorem upcrossingsBefore_eq_sum
  given: (hab : a < b)
  statement: upcrossingsBefore a b f N ω =
  proof: by
  by_cases hN : N = 0
  · simp [hN]
  rw [← Finset.sum_Ico_consecutive _ (Nat.succ_le_succ zero_le)
    (Nat.succ_le_succ (upcrossingsBefore_le f ω hab))]
  have h₁ : forall k in Finset.Ico 1 (upcrossingsBefore a b f N ω + 1),
      {n : Nat | upperCrossingTime a b f N n ω < N}.indicator 1 k = 1 

中文:
定理 upcrossingsBefore_eq_sum
  条件: (hab : a < b)
  结论: upcrossingsBefore a b f N ω =
  证明: by
  by_cases hN : N = 0
  · simp [hN]
  rw [← Finset.sum_Ico_consecutive _ (Nat.succ_le_succ zero_le)
    (Nat.succ_le_succ (upcrossingsBefore_le f ω hab))]
  have h₁ : forall k in Finset.Ico 1 (upcrossingsBefore a b f N ω + 1),
      {n : Nat | upperCrossingTime a b f N n ω < N}.indicator 1 k = 1 

Depends on / 依赖: Finset, Finset.Ico, Finset.mem_Ico, Finset.sum_Ico_consecutive, Nat.lt_succ_iff, Nat.succ_le_succ, Set.indicator_of_mem, indicator, indicator_of_mem, lt_succ_iff, mem_Ico, succ_le_succ, sum_Ico_consecutive, upcross, upcrossingsBefore, upcrossingsBefore_le, upperCrossingTime, upperCrossingTime_lt_of_le_upcrossingsBefore, zero_le, zero_lt_iff
-/
theorem upcrossingsBefore_eq_sum (hab : a < b) : upcrossingsBefore a b f N ω =
    ∑ i in Finset.Ico 1 (N + 1), {n | upperCrossingTime a b f N n ω < N}.indicator 1 i := by
  by_cases hN : N = 0
  · simp [hN]
  rw [← Finset.sum_Ico_consecutive _ (Nat.succ_le_succ zero_le)
    (Nat.succ_le_succ (upcrossingsBefore_le f ω hab))]
  have h₁ : forall k in Finset.Ico 1 (upcrossingsBefore a b f N ω + 1),
      {n : Nat | upperCrossingTime a b f N n ω < N}.indicator 1 k = 1 := by
    rintro k hk
    rw [Finset.mem_Ico] at hk
    rw [Set.indicator_of_mem]
    · rfl
    · exact upperCrossingTime_lt_of_le_upcrossingsBefore (zero_lt_iff.2 hN) hab
        (Nat.lt_succ_iff.1 hk.2)
  have h₂ : forall k in Finset.Ico (upcrossingsBefore a b f N ω + 1) (N + 1),
      {n : Nat | upperCrossingTime a b f N n ω < N}.indicator 1 k = 0 := by
    rintro k hk
    rw [Finset.mem_Ico]; rw [Nat.succ_le_iff] at hk
    rw [Set.indicator_of_notMem]
    simp only [Set.mem_ofPred_eq, not_lt]
    exact (upperCrossingTime_eq_of_upcrossingsBefore_lt hab hk.1).symm.le
  rw [Finset.sum_congr rfl h₁]; rw [Finset.sum_congr rfl h₂]; rw [Finset.sum_const]; rw [Finset.sum_const]; rw [smul_eq_mul]; rw [mul_one]; rw [smul_eq_mul]; rw [mul_zero]; rw [Nat.card_Ico]; rw [Nat.add_succ_sub_one]; rw [add_zero]; rw [add_zero]

/--
theorem `StronglyAdapted.measurable_upcrossingsBefore` / 定理 `StronglyAdapted.measurable_upcrossingsBefore`

English:
theorem StronglyAdapted.measurable_upcrossingsBefore
  given: (hf : StronglyAdapted ℱ f) (hab : a < b)
  proof: by
  have : upcrossingsBefore a b f N = fun ω =>
      ∑ i in Finset.Ico 1 (N + 1), {n | upperCrossingTime a b f N n ω < N}.indicator 1 i := by
    ext ω
    exact upcrossingsBefore_eq_sum hab
  rw [this]
refine Finset.measurable_fun_sum _ fun i _ => Measurable.indicator measurable_const
    ℱ.le N 

中文:
定理 StronglyAdapted.measurable_upcrossingsBefore
  条件: (hf : StronglyAdapted ℱ f) (hab : a < b)
  证明: by
  have : upcrossingsBefore a b f N = fun ω =>
      ∑ i in Finset.Ico 1 (N + 1), {n | upperCrossingTime a b f N n ω < N}.indicator 1 i := by
    ext ω
    exact upcrossingsBefore_eq_sum hab
  rw [this]
refine Finset.measurable_fun_sum _ fun i _ => Measurable.indicator measurable_const
    ℱ.le N 

Depends on / 依赖: ENat.some_eq_natCast, Finset, Finset.Ico, Finset.measurable_fun_sum, Measurable, Measurable.indicator, Nat.cast_lt, cast_lt, hf.isStoppingTime_upperCrossingTime.measurableSet_lt_of_pred, indicator, isStoppingTime_upperCrossingTime, measurableSet_lt_of_pred, measurable_const, measurable_fun_sum, some_eq_natCast, upcrossingsBefore, upcrossingsBefore_eq_sum, upperCrossingTime
-/
theorem StronglyAdapted.measurable_upcrossingsBefore (hf : StronglyAdapted ℱ f) (hab : a < b) :
    Measurable (upcrossingsBefore a b f N) := by
  have : upcrossingsBefore a b f N = fun ω =>
      ∑ i in Finset.Ico 1 (N + 1), {n | upperCrossingTime a b f N n ω < N}.indicator 1 i := by
    ext ω
    exact upcrossingsBefore_eq_sum hab
  rw [this]
refine Finset.measurable_fun_sum _ fun i _ => Measurable.indicator measurable_const
    ℱ.le N _ ?_
  simpa only [ENat.some_eq_natCast, Nat.cast_lt] using!
    hf.isStoppingTime_upperCrossingTime.measurableSet_lt_of_pred N

/--
theorem `StronglyAdapted.integrable_upcrossingsBefore` / 定理 `StronglyAdapted.integrable_upcrossingsBefore`

English:
theorem StronglyAdapted.integrable_upcrossingsBefore
  statement: [IsFiniteMeasure μ]
  proof: haveI : forallᵐ ω ∂μ, ‖(upcrossingsBefore a b f N ω : Real)‖ <= N := by
    filter_upwards with ω
    rw [Real.norm_eq_abs]; rw [Nat.abs_cast]; rw [Nat.cast_le]
    exact upcrossingsBefore_le _ _ hab
  ⟨Measurable.aestronglyMeasurable (measurable_from_top.comp (hf.measurable_upcrossingsBefore hab)),

中文:
定理 StronglyAdapted.integrable_upcrossingsBefore
  结论: [IsFiniteMeasure μ]
  证明: haveI : forallᵐ ω ∂μ, ‖(upcrossingsBefore a b f N ω : Real)‖ <= N := by
    filter_upwards with ω
    rw [Real.norm_eq_abs]; rw [Nat.abs_cast]; rw [Nat.cast_le]
    exact upcrossingsBefore_le _ _ hab
  ⟨Measurable.aestronglyMeasurable (measurable_from_top.comp (hf.measurable_upcrossingsBefore hab)),

Depends on / 依赖: Measurable, Measurable.aestronglyMeasurable, Nat.abs_cast, Nat.cast_le, Real.norm_eq_abs, abs_cast, aestronglyMeasurable, cast_le, filter_upwards, hf.measurable_upcrossingsBefore, measurable_from_top, measurable_from_top.comp, measurable_upcrossingsBefore, norm_eq_abs, of_bounded, upcrossingsBefore, upcrossingsBefore_le
-/
theorem StronglyAdapted.integrable_upcrossingsBefore [IsFiniteMeasure μ]
    (hf : StronglyAdapted ℱ f) (hab : a < b) :
    Integrable (fun ω => (upcrossingsBefore a b f N ω : Real)) μ :=
  haveI : forallᵐ ω ∂μ, ‖(upcrossingsBefore a b f N ω : Real)‖ <= N := by
    filter_upwards with ω
    rw [Real.norm_eq_abs]; rw [Nat.abs_cast]; rw [Nat.cast_le]
    exact upcrossingsBefore_le _ _ hab
  ⟨Measurable.aestronglyMeasurable (measurable_from_top.comp (hf.measurable_upcrossingsBefore hab)),
    .of_bounded this⟩

/--
Definition of `upcrossings` / `upcrossings` 的定义

English:
definition upcrossings
  signature: [Preorder ι] [OrderBot ι] [InfSet ι] (a b : Real) (f : ι -> Ω -> Real)
  body: ⨆ N, (upcrossingsBefore a b f N ω : Real>=0∞)

中文:
定义 upcrossings
  签名: [Preorder ι] [OrderBot ι] [InfSet ι] (a b : 实数) (f : ι -> Ω -> 实数)
  定义体: ⨆ N, (upcrossingsBefore a b f N ω : Real>=0∞)

Depends on / 依赖: upcrossingsBefore
-/
noncomputable def upcrossings [Preorder ι] [OrderBot ι] [InfSet ι] (a b : Real) (f : ι -> Ω -> Real)
    (ω : Ω) : Real>=0∞ :=
  ⨆ N, (upcrossingsBefore a b f N ω : Real>=0∞)

/--
theorem `StronglyAdapted.measurable_upcrossings` / 定理 `StronglyAdapted.measurable_upcrossings`

English:
theorem StronglyAdapted.measurable_upcrossings
  given: (hf : StronglyAdapted ℱ f) (hab : a < b)
  proof: .iSup fun _ => measurable_from_top.comp (hf.measurable_upcrossingsBefore hab)

中文:
定理 StronglyAdapted.measurable_upcrossings
  条件: (hf : StronglyAdapted ℱ f) (hab : a < b)
  证明: .iSup fun _ => measurable_from_top.comp (hf.measurable_upcrossingsBefore hab)

Depends on / 依赖: hf.measurable_upcrossingsBefore, measurable_from_top, measurable_from_top.comp, measurable_upcrossingsBefore
-/
theorem StronglyAdapted.measurable_upcrossings (hf : StronglyAdapted ℱ f) (hab : a < b) :
    Measurable (upcrossings a b f) :=
  .iSup fun _ => measurable_from_top.comp (hf.measurable_upcrossingsBefore hab)

/--
theorem `upcrossings_lt_top_iff` / 定理 `upcrossings_lt_top_iff`

English:
theorem upcrossings_lt_top_iff
  proof: by
  have : upcrossings a b f ω < ∞ ↔ exists k : Real>=0, upcrossings a b f ω <= k := by
    constructor
    · intro h
      lift upcrossings a b f ω to Real>=0 using h.ne with r hr
      exact ⟨r, le_rfl⟩
    · rintro ⟨k, hk⟩
      exact lt_of_le_of_lt hk ENNReal.coe_lt_top
  simp_rw [this, upcross

中文:
定理 upcrossings_lt_top_iff
  证明: by
  have : upcrossings a b f ω < ∞ ↔ exists k : Real>=0, upcrossings a b f ω <= k := by
    constructor
    · intro h
      lift upcrossings a b f ω to Real>=0 using h.ne with r hr
      exact ⟨r, le_rfl⟩
    · rintro ⟨k, hk⟩
      exact lt_of_le_of_lt hk ENNReal.coe_lt_top
  simp_rw [this, upcross

Depends on / 依赖: ENNReal, ENNReal.co, ENNReal.coe_le_coe, ENNReal.coe_lt_top, ENNReal.coe_natCast, Nat.cast_le, cast_le, coe_le_coe, coe_lt_top, coe_natCast, exists_nat_ge, h.ne, iSup_le_iff, le_rfl, lt_of_le_of_lt, simp_rw, upcrossings
-/
theorem upcrossings_lt_top_iff :
    upcrossings a b f ω < ∞ ↔ exists k, forall N, upcrossingsBefore a b f N ω <= k := by
  have : upcrossings a b f ω < ∞ ↔ exists k : Real>=0, upcrossings a b f ω <= k := by
    constructor
    · intro h
      lift upcrossings a b f ω to Real>=0 using h.ne with r hr
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

/--
theorem `Submartingale.mul_lintegral_upcrossings_le_lintegral_pos_part` / 定理 `Submartingale.mul_lintegral_upcrossings_le_lintegral_pos_part`

English:
theorem Submartingale.mul_lintegral_upcrossings_le_lintegral_pos_part
  statement: [IsFiniteMeasure μ] (a b : Real)
  proof: by
  by_cases! hab : a < b
  · simp_rw [upcrossings]
    have : forall N, ∫⁻ ω, ENNReal.ofReal ((f N ω - a)⁺) ∂μ = ENNReal.ofReal (∫ ω, (f N ω - a)⁺ ∂μ) := by
      intro N
      rw [ofReal_integral_eq_lintegral_ofReal]
      · exact (hf.sub_martingale (martingale_const _ _ _)).pos.integrable _
    

中文:
定理 Submartingale.mul_lintegral_upcrossings_le_lintegral_pos_part
  结论: [IsFiniteMeasure μ] (a b : 实数)
  证明: by
  by_cases! hab : a < b
  · simp_rw [upcrossings]
    have : forall N, ∫⁻ ω, ENNReal.ofReal ((f N ω - a)⁺) ∂μ = ENNReal.ofReal (∫ ω, (f N ω - a)⁺ ∂μ) := by
      intro N
      rw [ofReal_integral_eq_lintegral_ofReal]
      · exact (hf.sub_martingale (martingale_const _ _ _)).pos.integrable _
    

Depends on / 依赖: ENNReal, ENNReal.mul_iSup, ENNReal.ofReal, Eventually, Eventually.of_forall, hf.sub_martingale, iSup_le_iff, integrable, lintegral_iSup, martingale_const, mul_iSup, ofReal, ofReal_integral_eq_lintegral_ofReal, of_forall, pos.integrable, posPart_nonneg, simp_rw, sub_martingale, upcrossings, upcrossingsBefore
-/
theorem Submartingale.mul_lintegral_upcrossings_le_lintegral_pos_part [IsFiniteMeasure μ] (a b : Real)
    (hf : Submartingale f ℱ μ) : ENNReal.ofReal (b - a) * ∫⁻ ω, upcrossings a b f ω ∂μ <=
      ⨆ N, ∫⁻ ω, ENNReal.ofReal ((f N ω - a)⁺) ∂μ := by
  by_cases! hab : a < b
  · simp_rw [upcrossings]
    have : forall N, ∫⁻ ω, ENNReal.ofReal ((f N ω - a)⁺) ∂μ = ENNReal.ofReal (∫ ω, (f N ω - a)⁺ ∂μ) := by
      intro N
      rw [ofReal_integral_eq_lintegral_ofReal]
      · exact (hf.sub_martingale (martingale_const _ _ _)).pos.integrable _
      · exact Eventually.of_forall fun ω => posPart_nonneg _
    rw [lintegral_iSup']
    · simp_rw [this, ENNReal.mul_iSup, iSup_le_iff]
      intro N
      rw [(by simp :
          ∫⁻ ω]; rw [upcrossingsBefore a b f N ω ∂μ = ∫⁻ ω]; rw [↑(upcrossingsBefore a b f N ω : Real>=0) ∂μ)]; rw [lintegral_coe_eq_integral]; rw [← ENNReal.ofReal_mul (sub_pos.2 hab).le]
      · simp_rw [NNReal.coe_natCast]
        exact (ENNReal.ofReal_le_ofReal
          (hf.mul_integral_upcrossingsBefore_le_integral_pos_part a b N)).trans
            (le_iSup (α := Real>=0∞) _ N)
      · simp only [NNReal.coe_natCast, hf.stronglyAdapted.integrable_upcrossingsBefore hab]
    · exact fun n => measurable_from_top.comp_aemeasurable
        (hf.stronglyAdapted.measurable_upcrossingsBefore hab).aemeasurable
    · filter_upwards with ω N M hNM
      rw [Nat.cast_le]
      exact upcrossingsBefore_mono hab hNM ω
  · rw [← sub_nonpos] at hab
    rw [ENNReal.ofReal_of_nonpos hab]; rw [zero_mul]
    exact zero_le

end MeasureTheory
