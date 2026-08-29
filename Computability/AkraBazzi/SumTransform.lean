/-
Copyright (c) 2023 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Computability.AkraBazzi.GrowsPolynomially
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

import Mathlib.Analysis.SpecialFunctions.Log.InvLog
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Tactic.Positivity

/-!
# Akra-Bazzi theorem: the sum transform

We develop further preliminaries required for the theorem, up to the sum transform.

## Main definitions and results

* `AkraBazziRecurrence T g a b r`: the predicate stating that `T : ℕ → ℝ` satisfies an Akra-Bazzi
  recurrence with parameters `g`, `a`, `b` and `r` as above, together with basic bounds on `r i n`
  and positivity of `T`.
* `AkraBazziRecurrence.smoothingFn`: the smoothing function $\varepsilon(x) = 1 / \log x$ used in
  the inductive estimates, along with monotonicity, differentiability, and asymptotic properties.
* `AkraBazziRecurrence.p`: the unique Akra–Bazzi exponent characterized by $\sum_i a_i\,(b_i)^p = 1$
  and supporting analytical lemmas such as continuity and injectivity of the defining sum.
* `AkraBazziRecurrence.sumTransform`: the transformation that turns a function `g` into
  `n^p * ∑ u ∈ Finset.Ico n₀ n, g u / u^(p+1)` and its eventual comparison with multiples of `g n`.
* `AkraBazziRecurrence.asympBound`: the asymptotic bound satisfied by an Akra-Bazzi recurrence,
  namely `n^p (1 + ∑ g(u) / u^(p+1))`, together with positivity statements along the branches
  `r i n`.


## References

* Mohamad Akra and Louay Bazzi, On the solution of linear recurrence equations
* Tom Leighton, Notes on better master theorems for divide-and-conquer recurrences
* Manuel Eberl, Asymptotic reasoning in a proof assistant

-/

@[expose] public section

open Finset Real Filter Asymptotics
open scoped Topology

/-!
### Definition of Akra-Bazzi recurrences

This section defines the predicate `AkraBazziRecurrence T g a b r` which states that `T`
satisfies the recurrence relation
`T(n) = ∑_{i=0}^{k-1} a_i T(r_i(n)) + g(n)`
with appropriate conditions on the various parameters.
-/

/--
Definition of `AkraBazziRecurrence` / `AkraBazziRecurrence` 的定义

English:
structure AkraBazziRecurrence
  parameters: {α : Type*} [Fintype α] [Nonempty α]
  axioms and operations (11):
    - n₀ : Nat
    - n₀_gt_zero : 0 < n₀
    - a_pos : forall i, 0 < a i
    - b_pos : forall i, 0 < b i
    - b_lt_one : forall i, b i < 1
    - g_nonneg : forall x >= 0, 0 <= g x
    - g_grows_poly : AkraBazziRecurrence.GrowsPolynomially g
    - h_rec((n : Nat) (hn₀ : n₀ <= n)) : T n = (∑ i, a i * T (r i n)) + g n
    - T_gt_zero'((n : Nat) (hn : n < n₀)) : 0 < T n
    - r_lt_n : forall i n, n₀ <= n -> r i n < n
    - dist_r_b : forall i, (fun n => (r i n : Real) - b i * n) =o[atTop] fun n => n / (log n) ^ 2

中文:
结构 AkraBazziRecurrence
  参数: {α : 类型} [Fintype α] [Nonempty α]
  公理与运算 (11 个):
    - n₀ : 自然数
    - n₀_gt_zero : 0 < n₀
    - a_pos : 对任意 i, 0 < a i
    - b_pos : 对任意 i, 0 < b i
    - b_lt_one : 对任意 i, b i < 1
    - g_nonneg : 对任意 x >= 0, 0 <= g x
    - g_grows_poly : AkraBazziRecurrence.GrowsPolynomially g
    - h_rec((n : 自然数) (hn₀ : n₀ <= n)) : T n = (∑ i, a i * T (r i n)) + g n
    - T_gt_zero'((n : 自然数) (hn : n < n₀)) : 0 < T n
    - r_lt_n : 对任意 i n, n₀ <= n -> r i n < n
    - dist_r_b : 对任意 i, (fun n => (r i n : 实数) - b i * n) =o[atTop] fun n => n / (log n) ^ 2
-/
structure AkraBazziRecurrence {α : Type*} [Fintype α] [Nonempty α]
    (T : Nat -> Real) (g : Real -> Real) (a : α -> Real) (b : α -> Real) (r : α -> Nat -> Nat) where
  /-- Point below which the recurrence is in the base case -/
  n₀ : Nat
  /-- `n₀` is always positive -/
  n₀_gt_zero : 0 < n₀
  /-- The coefficients `a i` are positive. -/
  a_pos : forall i, 0 < a i
  /-- The coefficients `b i` are positive. -/
  b_pos : forall i, 0 < b i
  /-- The coefficients `b i` are less than 1. -/
  b_lt_one : forall i, b i < 1
  /-- `g` is nonnegative -/
  g_nonneg : forall x >= 0, 0 <= g x
  /-- `g` grows polynomially -/
  g_grows_poly : AkraBazziRecurrence.GrowsPolynomially g
  /-- The actual recurrence -/
  h_rec (n : Nat) (hn₀ : n₀ <= n) : T n = (∑ i, a i * T (r i n)) + g n
  /-- Base case: `T(n) > 0` whenever `n < n₀` -/
  T_gt_zero' (n : Nat) (hn : n < n₀) : 0 < T n
  /-- The functions `r i` always reduce `n`. -/
  r_lt_n : forall i n, n₀ <= n -> r i n < n
  /-- The functions `r i` approximate the values `b i * n`. -/
  dist_r_b : forall i, (fun n => (r i n : Real) - b i * n) =o[atTop] fun n => n / (log n) ^ 2

namespace AkraBazziRecurrence

section min_max

variable {α : Type*} [Finite α] [Nonempty α]

/--
Definition of `min_bi` / `min_bi` 的定义

English:
definition min_bi
  signature: (b : α -> Real)
  body: Classical.choose Finite.exists_min b

中文:
定义 min_bi
  签名: (b : α -> 实数)
  定义体: Classical.choose Finite.exists_min b

Depends on / 依赖: Classical, Classical.choose, Finite, Finite.exists_min, exists_min
-/
noncomputable def min_bi (b : α -> Real) : α :=
Classical.choose Finite.exists_min b

/--
Definition of `max_bi` / `max_bi` 的定义

English:
definition max_bi
  signature: (b : α -> Real)
  body: Classical.choose Finite.exists_max b

@[aesop safe apply]

中文:
定义 max_bi
  签名: (b : α -> 实数)
  定义体: Classical.choose Finite.exists_max b

@[aesop safe apply]

Depends on / 依赖: Classical, Classical.choose, Finite, Finite.exists_max, exists_max
-/
noncomputable def max_bi (b : α -> Real) : α :=
Classical.choose Finite.exists_max b

@[aesop safe apply]
/--
lemma `min_bi_le` / 引理 `min_bi_le`

English:
lemma min_bi_le
  given: {b : α -> Real} (i : α)
  statement: b (min_bi b) <= b i
  proof: Classical.choose_spec (Finite.exists_min b) i

@[aesop safe apply]

中文:
引理 min_bi_le
  条件: {b : α -> 实数} (i : α)
  结论: b (min_bi b) <= b i
  证明: Classical.choose_spec (Finite.exists_min b) i

@[aesop safe apply]

Depends on / 依赖: Classical, Classical.choose_spec, Finite, Finite.exists_min, choose_spec, exists_min
-/
lemma min_bi_le {b : α -> Real} (i : α) : b (min_bi b) <= b i :=
  Classical.choose_spec (Finite.exists_min b) i

@[aesop safe apply]
/--
lemma `max_bi_le` / 引理 `max_bi_le`

English:
lemma max_bi_le
  given: {b : α -> Real} (i : α)
  statement: b i <= b (max_bi b)
  proof: Classical.choose_spec (Finite.exists_max b) i

中文:
引理 max_bi_le
  条件: {b : α -> 实数} (i : α)
  结论: b i <= b (max_bi b)
  证明: Classical.choose_spec (Finite.exists_max b) i

Depends on / 依赖: Classical, Classical.choose_spec, Finite, Finite.exists_max, choose_spec, exists_max
-/
lemma max_bi_le {b : α -> Real} (i : α) : b i <= b (max_bi b) :=
  Classical.choose_spec (Finite.exists_max b) i

end min_max

/--
lemma `isLittleO_self_div_log_id` / 引理 `isLittleO_self_div_log_id`

English:
lemma isLittleO_self_div_log_id
  proof: by
  calc (fun (n : Nat) => (n : Real) / log n ^ 2)
    _ = fun (n : Nat) => (n : Real) * ((log n) ^ 2)⁻¹ := by simp_rw [div_eq_mul_inv]
    _ =o[atTop] fun (n : Nat) => (n : Real) * 1⁻¹ := by
      refine IsBigO.mul_isLittleO (isBigO_refl _ _) ?_
      refine IsLittleO.inv_rev ?_ (by simp)
      ca

中文:
引理 isLittleO_self_div_log_id
  证明: by
  calc (fun (n : Nat) => (n : Real) / log n ^ 2)
    _ = fun (n : Nat) => (n : Real) * ((log n) ^ 2)⁻¹ := by simp_rw [div_eq_mul_inv]
    _ =o[atTop] fun (n : Nat) => (n : Real) * 1⁻¹ := by
      refine IsBigO.mul_isLittleO (isBigO_refl _ _) ?_
      refine IsLittleO.inv_rev ?_ (by simp)
      ca

Depends on / 依赖: IsBigO, IsBigO.mul_isLittleO, IsLittleO, IsLittleO.inv_rev, IsLittleO.natCast_atTop, IsLittleO.pow, div_eq_mul_inv, inv_rev, isBigO_refl, isLittleO_const_log_atTop, mul_isLittleO, natCast_atTop, simp_rw
-/
lemma isLittleO_self_div_log_id :
    (fun (n : Nat) => n / log n ^ 2) =o[atTop] (fun (n : Nat) => (n : Real)) := by
  calc (fun (n : Nat) => (n : Real) / log n ^ 2)
    _ = fun (n : Nat) => (n : Real) * ((log n) ^ 2)⁻¹ := by simp_rw [div_eq_mul_inv]
    _ =o[atTop] fun (n : Nat) => (n : Real) * 1⁻¹ := by
      refine IsBigO.mul_isLittleO (isBigO_refl _ _) ?_
      refine IsLittleO.inv_rev ?_ (by simp)
      calc
        _ = (fun (_ : Nat) => ((1 : Real) ^ 2)) := by simp
        _ =o[atTop] (fun (n : Nat) => (log n) ^ 2) :=
          IsLittleO.pow (IsLittleO.natCast_atTop <| isLittleO_const_log_atTop) (by norm_num)
    _ = (fun (n : Nat) => (n : Real)) := by ext; simp

variable {α : Type*} [Fintype α] {T : Nat -> Real} {g : Real -> Real} {a b : α -> Real} {r : α -> Nat -> Nat}
variable [Nonempty α] (R : AkraBazziRecurrence T g a b r)
section
include R

/--
lemma `dist_r_b'` / 引理 `dist_r_b'`

English:
lemma dist_r_b'
  statement: forallᶠ n in atTop, forall i, ‖(r i n : Real) - b i * n‖ <= n / log n ^ 2
  proof: by
  rw [Filter.eventually_all]
  intro i
  simpa using IsLittleO.eventuallyLE (R.dist_r_b i)

中文:
引理 dist_r_b'
  结论: 对任意ᶠ n in atTop, 对任意 i, ‖(r i n : 实数) - b i * n‖ <= n / log n ^ 2
  证明: by
  rw [Filter.eventually_all]
  intro i
  simpa using IsLittleO.eventuallyLE (R.dist_r_b i)

Depends on / 依赖: Filter, Filter.eventually_all, IsLittleO, IsLittleO.eventuallyLE, R.dist_r_b, dist_r_b, eventuallyLE, eventually_all
-/
lemma dist_r_b' : forallᶠ n in atTop, forall i, ‖(r i n : Real) - b i * n‖ <= n / log n ^ 2 := by
  rw [Filter.eventually_all]
  intro i
  simpa using IsLittleO.eventuallyLE (R.dist_r_b i)

/--
lemma `eventually_b_le_r` / 引理 `eventually_b_le_r`

English:
lemma eventually_b_le_r
  statement: forallᶠ (n : Nat) in atTop, forall i, (b i : Real) * n - (n / log n ^ 2) <= r i n
  proof: by
  filter_upwards [R.dist_r_b'] with n hn i
have h₁ : 0 <= b i := le_of_lt R.b_pos _
  rw [sub_le_iff_le_add]; rw [add_comm]; rw [← sub_le_iff_le_add]
  calc (b i : Real) * n - r i n
    _ = ‖b i * n‖ - ‖(r i n : Real)‖ := by
      simp only [norm_mul, RCLike.norm_natCast, Real.norm_of_nonneg h₁]


中文:
引理 eventually_b_le_r
  结论: 对任意ᶠ (n : 自然数) in atTop, 对任意 i, (b i : 实数) * n - (n / log n ^ 2) <= r i n
  证明: by
  filter_upwards [R.dist_r_b'] with n hn i
have h₁ : 0 <= b i := le_of_lt R.b_pos _
  rw [sub_le_iff_le_add]; rw [add_comm]; rw [← sub_le_iff_le_add]
  calc (b i : Real) * n - r i n
    _ = ‖b i * n‖ - ‖(r i n : Real)‖ := by
      simp only [norm_mul, RCLike.norm_natCast, Real.norm_of_nonneg h₁]


Depends on / 依赖: R.b_pos, R.dist_r_b, RCLike, RCLike.norm_natCast, Real.norm_of_nonneg, add_comm, b_pos, dist_r_b, filter_upwards, le_of_lt, norm_mul, norm_natCast, norm_of_nonneg, norm_sub_norm_le, norm_sub_rev, sub_le_iff_le_add
-/
lemma eventually_b_le_r : forallᶠ (n : Nat) in atTop, forall i, (b i : Real) * n - (n / log n ^ 2) <= r i n := by
  filter_upwards [R.dist_r_b'] with n hn i
have h₁ : 0 <= b i := le_of_lt R.b_pos _
  rw [sub_le_iff_le_add]; rw [add_comm]; rw [← sub_le_iff_le_add]
  calc (b i : Real) * n - r i n
    _ = ‖b i * n‖ - ‖(r i n : Real)‖ := by
      simp only [norm_mul, RCLike.norm_natCast, Real.norm_of_nonneg h₁]
    _ <= ‖(b i * n : Real) - r i n‖ := norm_sub_norm_le _ _
    _ = ‖(r i n : Real) - b i * n‖ := norm_sub_rev _ _
    _ <= n / log n ^ 2 := hn i

/--
lemma `eventually_r_le_b` / 引理 `eventually_r_le_b`

English:
lemma eventually_r_le_b
  statement: forallᶠ (n : Nat) in atTop, forall i, r i n <= (b i : Real) * n + (n / log n ^ 2)
  proof: by
  filter_upwards [R.dist_r_b'] with n hn i
  calc r i n = b i * n + (r i n - b i * n) := by ring
             _ <= b i * n + ‖r i n - b i * n‖ := by gcongr; exact Real.le_norm_self _
             _ <= b i * n + n / log n ^ 2 := by gcongr; exact hn i

中文:
引理 eventually_r_le_b
  结论: 对任意ᶠ (n : 自然数) in atTop, 对任意 i, r i n <= (b i : 实数) * n + (n / log n ^ 2)
  证明: by
  filter_upwards [R.dist_r_b'] with n hn i
  calc r i n = b i * n + (r i n - b i * n) := by ring
             _ <= b i * n + ‖r i n - b i * n‖ := by gcongr; exact Real.le_norm_self _
             _ <= b i * n + n / log n ^ 2 := by gcongr; exact hn i

Depends on / 依赖: R.dist_r_b, Real.le_norm_self, dist_r_b, filter_upwards, le_norm_self
-/
lemma eventually_r_le_b : forallᶠ (n : Nat) in atTop, forall i, r i n <= (b i : Real) * n + (n / log n ^ 2) := by
  filter_upwards [R.dist_r_b'] with n hn i
  calc r i n = b i * n + (r i n - b i * n) := by ring
             _ <= b i * n + ‖r i n - b i * n‖ := by gcongr; exact Real.le_norm_self _
             _ <= b i * n + n / log n ^ 2 := by gcongr; exact hn i

/--
lemma `eventually_r_lt_n` / 引理 `eventually_r_lt_n`

English:
lemma eventually_r_lt_n
  statement: forallᶠ (n : Nat) in atTop, forall i, r i n < n
  proof: by
  filter_upwards [eventually_ge_atTop R.n₀] with n hn i using R.r_lt_n i n hn

中文:
引理 eventually_r_lt_n
  结论: 对任意ᶠ (n : 自然数) in atTop, 对任意 i, r i n < n
  证明: by
  filter_upwards [eventually_ge_atTop R.n₀] with n hn i using R.r_lt_n i n hn

Depends on / 依赖: R.r_lt_n, eventually_ge_atTop, filter_upwards, r_lt_n
-/
lemma eventually_r_lt_n : forallᶠ (n : Nat) in atTop, forall i, r i n < n := by
  filter_upwards [eventually_ge_atTop R.n₀] with n hn i using R.r_lt_n i n hn

/--
lemma `eventually_bi_mul_le_r` / 引理 `eventually_bi_mul_le_r`

English:
lemma eventually_bi_mul_le_r
  statement: forallᶠ (n : Nat) in atTop, forall i, (b (min_bi b) / 2) * n <= r i n
  proof: by
  have gt_zero : 0 < b (min_bi b) := R.b_pos (min_bi b)
  have hlo := isLittleO_self_div_log_id
  rw [Asymptotics.isLittleO_iff] at hlo
  have hlo' := hlo (by positivity : 0 < b (min_bi b) / 2)
  filter_upwards [hlo', R.eventually_b_le_r] with n hn hn' i
  simp only [Real.norm_of_nonneg (by posit

中文:
引理 eventually_bi_mul_le_r
  结论: 对任意ᶠ (n : 自然数) in atTop, 对任意 i, (b (min_bi b) / 2) * n <= r i n
  证明: by
  have gt_zero : 0 < b (min_bi b) := R.b_pos (min_bi b)
  have hlo := isLittleO_self_div_log_id
  rw [Asymptotics.isLittleO_iff] at hlo
  have hlo' := hlo (by positivity : 0 < b (min_bi b) / 2)
  filter_upwards [hlo', R.eventually_b_le_r] with n hn hn' i
  simp only [Real.norm_of_nonneg (by posit

Depends on / 依赖: Asymptotics, Asymptotics.isLittleO_iff, R.b_pos, R.eventually_b_le_r, Real.norm_of_nonneg, b_pos, eventually_b_le_r, filter_upwards, gt_zero, isLittleO_iff, isLittleO_self_div_log_id, min_bi, norm_of_nonneg
-/
lemma eventually_bi_mul_le_r : forallᶠ (n : Nat) in atTop, forall i, (b (min_bi b) / 2) * n <= r i n := by
  have gt_zero : 0 < b (min_bi b) := R.b_pos (min_bi b)
  have hlo := isLittleO_self_div_log_id
  rw [Asymptotics.isLittleO_iff] at hlo
  have hlo' := hlo (by positivity : 0 < b (min_bi b) / 2)
  filter_upwards [hlo', R.eventually_b_le_r] with n hn hn' i
  simp only [Real.norm_of_nonneg (by positivity : 0 <= (n : Real))] at hn
  calc b (min_bi b) / 2 * n
    _ = b (min_bi b) * n - b (min_bi b) / 2 * n := by ring
    _ <= b (min_bi b) * n - ‖n / log n ^ 2‖ := by gcongr
    _ <= b i * n - ‖n / log n ^ 2‖ := by gcongr; aesop
    _ = b i * n - n / log n ^ 2 := by
      congr
exact Real.norm_of_nonneg by positivity
    _ <= r i n := hn' i

/--
lemma `bi_min_div_two_lt_one` / 引理 `bi_min_div_two_lt_one`

English:
lemma bi_min_div_two_lt_one
  statement: b (min_bi b) / 2 < 1
  proof: by
  have gt_zero : 0 < b (min_bi b) := R.b_pos (min_bi b)
  calc b (min_bi b) / 2
    _ < b (min_bi b) := by aesop (add safe apply div_two_lt_of_pos)
    _ < 1 := R.b_lt_one _

中文:
引理 bi_min_div_two_lt_one
  结论: b (min_bi b) / 2 < 1
  证明: by
  have gt_zero : 0 < b (min_bi b) := R.b_pos (min_bi b)
  calc b (min_bi b) / 2
    _ < b (min_bi b) := by aesop (add safe apply div_two_lt_of_pos)
    _ < 1 := R.b_lt_one _

Depends on / 依赖: R.b_lt_one, R.b_pos, b_lt_one, b_pos, div_two_lt_of_pos, gt_zero, min_bi
-/
lemma bi_min_div_two_lt_one : b (min_bi b) / 2 < 1 := by
  have gt_zero : 0 < b (min_bi b) := R.b_pos (min_bi b)
  calc b (min_bi b) / 2
    _ < b (min_bi b) := by aesop (add safe apply div_two_lt_of_pos)
    _ < 1 := R.b_lt_one _

/--
lemma `bi_min_div_two_pos` / 引理 `bi_min_div_two_pos`

English:
lemma bi_min_div_two_pos
  statement: 0 < b (min_bi b) / 2
  proof: div_pos (R.b_pos _) (by simp)

中文:
引理 bi_min_div_two_pos
  结论: 0 < b (min_bi b) / 2
  证明: div_pos (R.b_pos _) (by simp)

Depends on / 依赖: R.b_pos, b_pos, div_pos
-/
lemma bi_min_div_two_pos : 0 < b (min_bi b) / 2 := div_pos (R.b_pos _) (by simp)

/--
lemma `exists_eventually_const_mul_le_r` / 引理 `exists_eventually_const_mul_le_r`

English:
lemma exists_eventually_const_mul_le_r
  proof: by
  have gt_zero : 0 < b (min_bi b) := R.b_pos (min_bi b)
  exact ⟨b (min_bi b) / 2, ⟨⟨by positivity, R.bi_min_div_two_lt_one⟩, R.eventually_bi_mul_le_r⟩⟩

中文:
引理 exists_eventually_const_mul_le_r
  证明: by
  have gt_zero : 0 < b (min_bi b) := R.b_pos (min_bi b)
  exact ⟨b (min_bi b) / 2, ⟨⟨by positivity, R.bi_min_div_two_lt_one⟩, R.eventually_bi_mul_le_r⟩⟩

Depends on / 依赖: R.b_pos, R.bi_min_div_two_lt_one, R.eventually_bi_mul_le_r, b_pos, bi_min_div_two_lt_one, eventually_bi_mul_le_r, gt_zero, min_bi
-/
lemma exists_eventually_const_mul_le_r :
    exists c in Set.Ioo (0 : Real) 1, forallᶠ (n : Nat) in atTop, forall i, c * n <= r i n := by
  have gt_zero : 0 < b (min_bi b) := R.b_pos (min_bi b)
  exact ⟨b (min_bi b) / 2, ⟨⟨by positivity, R.bi_min_div_two_lt_one⟩, R.eventually_bi_mul_le_r⟩⟩

/--
lemma `eventually_r_ge` / 引理 `eventually_r_ge`

English:
lemma eventually_r_ge
  given: (C : Real)
  statement: forallᶠ (n : Nat) in atTop, forall i, C <= r i n
  proof: by
  obtain ⟨c, hc_mem, hc⟩ := R.exists_eventually_const_mul_le_r
  filter_upwards [eventually_ge_atTop ⌈C / c⌉₊, hc] with n hn₁ hn₂ i
  have h₁ := hc_mem.1
  calc C
    _ = c * (C / c) := by
      rw [← mul_div_assoc]
      exact (mul_div_cancel_left₀ _ (by positivity)).symm
    _ <= c * ⌈C / c⌉₊ :

中文:
引理 eventually_r_ge
  条件: (C : 实数)
  结论: 对任意ᶠ (n : 自然数) in atTop, 对任意 i, C <= r i n
  证明: by
  obtain ⟨c, hc_mem, hc⟩ := R.exists_eventually_const_mul_le_r
  filter_upwards [eventually_ge_atTop ⌈C / c⌉₊, hc] with n hn₁ hn₂ i
  have h₁ := hc_mem.1
  calc C
    _ = c * (C / c) := by
      rw [← mul_div_assoc]
      exact (mul_div_cancel_left₀ _ (by positivity)).symm
    _ <= c * ⌈C / c⌉₊ :

Depends on / 依赖: Nat.le_ceil, R.exists_eventually_const_mul_le_r, eventually_ge_atTop, exists_eventually_const_mul_le_r, filter_upwards, hc_mem, le_ceil, mul_div_assoc
-/
lemma eventually_r_ge (C : Real) : forallᶠ (n : Nat) in atTop, forall i, C <= r i n := by
  obtain ⟨c, hc_mem, hc⟩ := R.exists_eventually_const_mul_le_r
  filter_upwards [eventually_ge_atTop ⌈C / c⌉₊, hc] with n hn₁ hn₂ i
  have h₁ := hc_mem.1
  calc C
    _ = c * (C / c) := by
      rw [← mul_div_assoc]
      exact (mul_div_cancel_left₀ _ (by positivity)).symm
    _ <= c * ⌈C / c⌉₊ := by gcongr; simp [Nat.le_ceil]
    _ <= c * n := by gcongr
    _ <= r i n := hn₂ i

/--
lemma `tendsto_atTop_r` / 引理 `tendsto_atTop_r`

English:
lemma tendsto_atTop_r
  given: (i : α)
  statement: Tendsto (r i) atTop atTop
  proof: by
  rw [tendsto_atTop]
  intro b
  have := R.eventually_r_ge b
  rw [Filter.eventually_all] at this
  exact_mod_cast this i

中文:
引理 tendsto_atTop_r
  条件: (i : α)
  结论: Tendsto (r i) atTop atTop
  证明: by
  rw [tendsto_atTop]
  intro b
  have := R.eventually_r_ge b
  rw [Filter.eventually_all] at this
  exact_mod_cast this i

Depends on / 依赖: Filter, Filter.eventually_all, R.eventually_r_ge, eventually_all, eventually_r_ge, tendsto_atTop
-/
lemma tendsto_atTop_r (i : α) : Tendsto (r i) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  have := R.eventually_r_ge b
  rw [Filter.eventually_all] at this
  exact_mod_cast this i

/--
lemma `tendsto_atTop_r_real` / 引理 `tendsto_atTop_r_real`

English:
lemma tendsto_atTop_r_real
  given: (i : α)
  statement: Tendsto (fun n => (r i n : Real)) atTop atTop
  proof: Tendsto.comp tendsto_natCast_atTop_atTop (R.tendsto_atTop_r i)

中文:
引理 tendsto_atTop_r_real
  条件: (i : α)
  结论: Tendsto (fun n => (r i n : 实数)) atTop atTop
  证明: Tendsto.comp tendsto_natCast_atTop_atTop (R.tendsto_atTop_r i)

Depends on / 依赖: R.tendsto_atTop_r, Tendsto, Tendsto.comp, tendsto_atTop_r, tendsto_natCast_atTop_atTop
-/
lemma tendsto_atTop_r_real (i : α) : Tendsto (fun n => (r i n : Real)) atTop atTop :=
  Tendsto.comp tendsto_natCast_atTop_atTop (R.tendsto_atTop_r i)

/--
lemma `exists_eventually_r_le_const_mul` / 引理 `exists_eventually_r_le_const_mul`

English:
lemma exists_eventually_r_le_const_mul
  proof: by
  let c := b (max_bi b) + (1 - b (max_bi b)) / 2
  have h_max_bi_pos : 0 < b (max_bi b) := R.b_pos _
  have h_max_bi_lt_one : 0 < 1 - b (max_bi b) := by
    have : b (max_bi b) < 1 := R.b_lt_one _
    linarith
  have hc_pos : 0 < c := by positivity
  have h₁ : 0 < (1 - b (max_bi b)) / 2 := by pos

中文:
引理 exists_eventually_r_le_const_mul
  证明: by
  let c := b (max_bi b) + (1 - b (max_bi b)) / 2
  have h_max_bi_pos : 0 < b (max_bi b) := R.b_pos _
  have h_max_bi_lt_one : 0 < 1 - b (max_bi b) := by
    have : b (max_bi b) < 1 := R.b_lt_one _
    linarith
  have hc_pos : 0 < c := by positivity
  have h₁ : 0 < (1 - b (max_bi b)) / 2 := by pos

Depends on / 依赖: R.b_lt_one, R.b_pos, b_lt_one, b_pos, h_max_bi_lt_one, h_max_bi_pos, hc_lt_one, hc_po, hc_pos, max_bi
-/
lemma exists_eventually_r_le_const_mul :
    exists c in Set.Ioo (0 : Real) 1, forallᶠ (n : Nat) in atTop, forall i, r i n <= c * n := by
  let c := b (max_bi b) + (1 - b (max_bi b)) / 2
  have h_max_bi_pos : 0 < b (max_bi b) := R.b_pos _
  have h_max_bi_lt_one : 0 < 1 - b (max_bi b) := by
    have : b (max_bi b) < 1 := R.b_lt_one _
    linarith
  have hc_pos : 0 < c := by positivity
  have h₁ : 0 < (1 - b (max_bi b)) / 2 := by positivity
  have hc_lt_one : c < 1 :=
    calc b (max_bi b) + (1 - b (max_bi b)) / 2
      _ = b (max_bi b) * (1 / 2) + 1 / 2 := by ring
      _ < 1 * (1 / 2) + 1 / 2 := by gcongr; exact R.b_lt_one _
      _ = 1 := by norm_num
  refine ⟨c, ⟨hc_pos, hc_lt_one⟩, ?_⟩
  have hlo := isLittleO_self_div_log_id
  rw [Asymptotics.isLittleO_iff] at hlo
  have hlo' := hlo h₁
  filter_upwards [hlo', R.eventually_r_le_b] with n hn hn'
  intro i
  rw [Real.norm_of_nonneg (by positivity)] at hn
  simp only [Real.norm_of_nonneg (by positivity : 0 <= (n : Real))] at hn
  calc r i n <= b i * n + n / log n ^ 2 := by exact hn' i
             _ <= b i * n + (1 - b (max_bi b)) / 2 * n := by gcongr
             _ = (b i + (1 - b (max_bi b)) / 2) * n := by ring
             _ <= (b (max_bi b) + (1 - b (max_bi b)) / 2) * n := by gcongr; exact max_bi_le _

/--
lemma `eventually_r_pos` / 引理 `eventually_r_pos`

English:
lemma eventually_r_pos
  statement: forallᶠ (n : Nat) in atTop, forall i, 0 < r i n
  proof: by
  rw [Filter.eventually_all]
  exact fun i => (R.tendsto_atTop_r i).eventually_gt_atTop 0

中文:
引理 eventually_r_pos
  结论: 对任意ᶠ (n : 自然数) in atTop, 对任意 i, 0 < r i n
  证明: by
  rw [Filter.eventually_all]
  exact fun i => (R.tendsto_atTop_r i).eventually_gt_atTop 0

Depends on / 依赖: Filter, Filter.eventually_all, R.tendsto_atTop_r, eventually_all, eventually_gt_atTop, tendsto_atTop_r
-/
lemma eventually_r_pos : forallᶠ (n : Nat) in atTop, forall i, 0 < r i n := by
  rw [Filter.eventually_all]
  exact fun i => (R.tendsto_atTop_r i).eventually_gt_atTop 0

/--
lemma `eventually_log_b_mul_pos` / 引理 `eventually_log_b_mul_pos`

English:
lemma eventually_log_b_mul_pos
  statement: forallᶠ (n : Nat) in atTop, forall i, 0 < log (b i * n)
  proof: by
  rw [Filter.eventually_all]
  intro i
  have h : Tendsto (fun (n : Nat) => log (b i * n)) atTop atTop :=
    Tendsto.comp tendsto_log_atTop
 Tendsto.const_mul_atTop (b_pos R i) tendsto_natCast_atTop_atTop
  exact h.eventually_gt_atTop 0

中文:
引理 eventually_log_b_mul_pos
  结论: 对任意ᶠ (n : 自然数) in atTop, 对任意 i, 0 < log (b i * n)
  证明: by
  rw [Filter.eventually_all]
  intro i
  have h : Tendsto (fun (n : Nat) => log (b i * n)) atTop atTop :=
    Tendsto.comp tendsto_log_atTop
 Tendsto.const_mul_atTop (b_pos R i) tendsto_natCast_atTop_atTop
  exact h.eventually_gt_atTop 0

Depends on / 依赖: Filter, Filter.eventually_all, Tendsto, Tendsto.comp, Tendsto.const_mul_atTop, b_pos, const_mul_atTop, eventually_all, eventually_gt_atTop, h.eventually_gt_atTop, tendsto_log_atTop, tendsto_natCast_atTop_atTop
-/
lemma eventually_log_b_mul_pos : forallᶠ (n : Nat) in atTop, forall i, 0 < log (b i * n) := by
  rw [Filter.eventually_all]
  intro i
  have h : Tendsto (fun (n : Nat) => log (b i * n)) atTop atTop :=
    Tendsto.comp tendsto_log_atTop
 Tendsto.const_mul_atTop (b_pos R i) tendsto_natCast_atTop_atTop
  exact h.eventually_gt_atTop 0

/--
lemma `T_pos` / 引理 `T_pos`

English:
lemma T_pos
  given: (n : Nat)
  statement: 0 < T n
  proof: by
  induction n using Nat.strongRecOn with
  | ind n h_ind =>
    cases lt_or_ge n R.n₀ with
    | inl hn => exact R.T_gt_zero' n hn -- n < R.n₀
    | inr hn => -- R.n₀ ≤ n
      rw [R.h_rec n hn]
      have := R.g_nonneg
      refine add_pos_of_pos_of_nonneg (Finset.sum_pos ?sum_elems univ_nonempt

中文:
引理 T_pos
  条件: (n : 自然数)
  结论: 0 < T n
  证明: by
  induction n using Nat.strongRecOn with
  | ind n h_ind =>
    cases lt_or_ge n R.n₀ with
    | inl hn => exact R.T_gt_zero' n hn -- n < R.n₀
    | inr hn => -- R.n₀ ≤ n
      rw [R.h_rec n hn]
      have := R.g_nonneg
      refine add_pos_of_pos_of_nonneg (Finset.sum_pos ?sum_elems univ_nonempt
-/
@[aesop safe apply] lemma T_pos (n : Nat) : 0 < T n := by
  induction n using Nat.strongRecOn with
  | ind n h_ind =>
    cases lt_or_ge n R.n₀ with
    | inl hn => exact R.T_gt_zero' n hn -- n < R.n₀
    | inr hn => -- R.n₀ ≤ n
      rw [R.h_rec n hn]
      have := R.g_nonneg
      refine add_pos_of_pos_of_nonneg (Finset.sum_pos ?sum_elems univ_nonempty) (by simp_all)
exact fun i _ => mul_pos (R.a_pos i) h_ind _ (R.r_lt_n i _ hn)

@[aesop safe apply]
/--
lemma `T_nonneg` / 引理 `T_nonneg`

English:
lemma T_nonneg
  given: (n : Nat)
  statement: 0 <= T n
  proof: le_of_lt R.T_pos n

中文:
引理 T_nonneg
  条件: (n : 自然数)
  结论: 0 <= T n
  证明: le_of_lt R.T_pos n

Depends on / 依赖: R.T_pos, T_pos, le_of_lt
-/
lemma T_nonneg (n : Nat) : 0 <= T n := le_of_lt R.T_pos n

end

/-!
### Smoothing function

We define `ε` as the "smoothing function" `fun n => 1 / log n`, which will be used in the form of a
factor of `1 ± ε n` needed to make the induction step go through.

This is its own definition to make it easier to switch to a different smoothing function.
For example, choosing `1 / log n ^ δ` for a suitable choice of `δ` leads to a slightly tighter
theorem at the price of a more complicated proof.

This part of the file then proves several properties of this function that will be needed later in
the proof.
-/

/--
Definition of `smoothingFn` / `smoothingFn` 的定义

English:
definition smoothingFn
  signature: (n : Real)
  body: 1 / log n

local notation "ε" => smoothingFn

中文:
定义 smoothingFn
  签名: (n : 实数)
  定义体: 1 / log n

local notation "ε" => smoothingFn
-/
noncomputable def smoothingFn (n : Real) : Real := 1 / log n

local notation "ε" => smoothingFn

/--
lemma `one_add_smoothingFn_le_two` / 引理 `one_add_smoothingFn_le_two`

English:
lemma one_add_smoothingFn_le_two
  given: {x : Real} (hx : exp 1 <= x)
  statement: 1 + ε x <= 2
  proof: by
  simp only [smoothingFn, ← one_add_one_eq_two]
  gcongr
  have : 1 < x := by
    calc 1 = exp 0 := by simp
         _ < exp 1 := by simp
         _ <= x := hx
  rw [div_le_one (log_pos this)]
  calc 1 = log (exp 1) := by simp
       _ <= log x := log_le_log (exp_pos _) hx

中文:
引理 one_add_smoothingFn_le_two
  条件: {x : 实数} (hx : exp 1 <= x)
  结论: 1 + ε x <= 2
  证明: by
  simp only [smoothingFn, ← one_add_one_eq_two]
  gcongr
  have : 1 < x := by
    calc 1 = exp 0 := by simp
         _ < exp 1 := by simp
         _ <= x := hx
  rw [div_le_one (log_pos this)]
  calc 1 = log (exp 1) := by simp
       _ <= log x := log_le_log (exp_pos _) hx

Depends on / 依赖: div_le_one, exp_pos, log_le_log, log_pos, one_add_one_eq_two, smoothingFn
-/
lemma one_add_smoothingFn_le_two {x : Real} (hx : exp 1 <= x) : 1 + ε x <= 2 := by
  simp only [smoothingFn, ← one_add_one_eq_two]
  gcongr
  have : 1 < x := by
    calc 1 = exp 0 := by simp
         _ < exp 1 := by simp
         _ <= x := hx
  rw [div_le_one (log_pos this)]
  calc 1 = log (exp 1) := by simp
       _ <= log x := log_le_log (exp_pos _) hx

/--
lemma `isLittleO_smoothingFn_one` / 引理 `isLittleO_smoothingFn_one`

English:
lemma isLittleO_smoothingFn_one
  statement: ε =o[atTop] (fun _ => (1 : Real))
  proof: by
  unfold smoothingFn
  refine isLittleO_of_tendsto (fun _ h => False.elim <| one_ne_zero h) ?_
  simp only [one_div, div_one]
  exact Tendsto.inv_tendsto_atTop Real.tendsto_log_atTop

中文:
引理 isLittleO_smoothingFn_one
  结论: ε =o[atTop] (fun _ => (1 : 实数))
  证明: by
  unfold smoothingFn
  refine isLittleO_of_tendsto (fun _ h => False.elim <| one_ne_zero h) ?_
  simp only [one_div, div_one]
  exact Tendsto.inv_tendsto_atTop Real.tendsto_log_atTop

Depends on / 依赖: False.elim, Real.tendsto_log_atTop, Tendsto, Tendsto.inv_tendsto_atTop, div_one, inv_tendsto_atTop, isLittleO_of_tendsto, one_div, one_ne_zero, smoothingFn, tendsto_log_atTop
-/
lemma isLittleO_smoothingFn_one : ε =o[atTop] (fun _ => (1 : Real)) := by
  unfold smoothingFn
  refine isLittleO_of_tendsto (fun _ h => False.elim <| one_ne_zero h) ?_
  simp only [one_div, div_one]
  exact Tendsto.inv_tendsto_atTop Real.tendsto_log_atTop

/--
lemma `isEquivalent_one_add_smoothingFn_one` / 引理 `isEquivalent_one_add_smoothingFn_one`

English:
lemma isEquivalent_one_add_smoothingFn_one
  statement: (fun x => 1 + ε x) ~[atTop] (fun _ => (1 : Real))
  proof: IsEquivalent.add_isLittleO IsEquivalent.refl isLittleO_smoothingFn_one

中文:
引理 isEquivalent_one_add_smoothingFn_one
  结论: (fun x => 1 + ε x) ~[atTop] (fun _ => (1 : 实数))
  证明: IsEquivalent.add_isLittleO IsEquivalent.refl isLittleO_smoothingFn_one

Depends on / 依赖: IsEquivalent, IsEquivalent.add_isLittleO, IsEquivalent.refl, add_isLittleO, isLittleO_smoothingFn_one
-/
lemma isEquivalent_one_add_smoothingFn_one : (fun x => 1 + ε x) ~[atTop] (fun _ => (1 : Real)) :=
  IsEquivalent.add_isLittleO IsEquivalent.refl isLittleO_smoothingFn_one

/--
lemma `isEquivalent_one_sub_smoothingFn_one` / 引理 `isEquivalent_one_sub_smoothingFn_one`

English:
lemma isEquivalent_one_sub_smoothingFn_one
  statement: (fun x => 1 - ε x) ~[atTop] (fun _ => (1 : Real))
  proof: IsEquivalent.sub_isLittleO IsEquivalent.refl isLittleO_smoothingFn_one

中文:
引理 isEquivalent_one_sub_smoothingFn_one
  结论: (fun x => 1 - ε x) ~[atTop] (fun _ => (1 : 实数))
  证明: IsEquivalent.sub_isLittleO IsEquivalent.refl isLittleO_smoothingFn_one

Depends on / 依赖: IsEquivalent, IsEquivalent.refl, IsEquivalent.sub_isLittleO, isLittleO_smoothingFn_one, sub_isLittleO
-/
lemma isEquivalent_one_sub_smoothingFn_one : (fun x => 1 - ε x) ~[atTop] (fun _ => (1 : Real)) :=
  IsEquivalent.sub_isLittleO IsEquivalent.refl isLittleO_smoothingFn_one

/--
lemma `growsPolynomially_one_sub_smoothingFn` / 引理 `growsPolynomially_one_sub_smoothingFn`

English:
lemma growsPolynomially_one_sub_smoothingFn
  statement: GrowsPolynomially fun x => 1 - ε x
  proof: GrowsPolynomially.of_isEquivalent_const isEquivalent_one_sub_smoothingFn_one

中文:
引理 growsPolynomially_one_sub_smoothingFn
  结论: GrowsPolynomially fun x => 1 - ε x
  证明: GrowsPolynomially.of_isEquivalent_const isEquivalent_one_sub_smoothingFn_one

Depends on / 依赖: GrowsPolynomially, GrowsPolynomially.of_isEquivalent_const, isEquivalent_one_sub_smoothingFn_one, of_isEquivalent_const
-/
lemma growsPolynomially_one_sub_smoothingFn : GrowsPolynomially fun x => 1 - ε x :=
  GrowsPolynomially.of_isEquivalent_const isEquivalent_one_sub_smoothingFn_one

/--
lemma `growsPolynomially_one_add_smoothingFn` / 引理 `growsPolynomially_one_add_smoothingFn`

English:
lemma growsPolynomially_one_add_smoothingFn
  statement: GrowsPolynomially fun x => 1 + ε x
  proof: GrowsPolynomially.of_isEquivalent_const isEquivalent_one_add_smoothingFn_one

中文:
引理 growsPolynomially_one_add_smoothingFn
  结论: GrowsPolynomially fun x => 1 + ε x
  证明: GrowsPolynomially.of_isEquivalent_const isEquivalent_one_add_smoothingFn_one

Depends on / 依赖: GrowsPolynomially, GrowsPolynomially.of_isEquivalent_const, isEquivalent_one_add_smoothingFn_one, of_isEquivalent_const
-/
lemma growsPolynomially_one_add_smoothingFn : GrowsPolynomially fun x => 1 + ε x :=
  GrowsPolynomially.of_isEquivalent_const isEquivalent_one_add_smoothingFn_one

/--
lemma `eventually_one_sub_smoothingFn_gt_const_real` / 引理 `eventually_one_sub_smoothingFn_gt_const_real`

English:
lemma eventually_one_sub_smoothingFn_gt_const_real
  given: (c : Real) (hc : c < 1)
  proof: by
  have h₁ : Tendsto (fun x => 1 - ε x) atTop (𝓝 1) := by
    rw [← isEquivalent_const_iff_tendsto one_ne_zero]
    exact isEquivalent_one_sub_smoothingFn_one
  rw [tendsto_order] at h₁
  exact h₁.1 c hc

中文:
引理 eventually_one_sub_smoothingFn_gt_const_real
  条件: (c : 实数) (hc : c < 1)
  证明: by
  have h₁ : Tendsto (fun x => 1 - ε x) atTop (𝓝 1) := by
    rw [← isEquivalent_const_iff_tendsto one_ne_zero]
    exact isEquivalent_one_sub_smoothingFn_one
  rw [tendsto_order] at h₁
  exact h₁.1 c hc

Depends on / 依赖: Tendsto, isEquivalent_const_iff_tendsto, isEquivalent_one_sub_smoothingFn_one, one_ne_zero, tendsto_order
-/
lemma eventually_one_sub_smoothingFn_gt_const_real (c : Real) (hc : c < 1) :
    forallᶠ (x : Real) in atTop, c < 1 - ε x := by
  have h₁ : Tendsto (fun x => 1 - ε x) atTop (𝓝 1) := by
    rw [← isEquivalent_const_iff_tendsto one_ne_zero]
    exact isEquivalent_one_sub_smoothingFn_one
  rw [tendsto_order] at h₁
  exact h₁.1 c hc

/--
lemma `eventually_one_sub_smoothingFn_gt_const` / 引理 `eventually_one_sub_smoothingFn_gt_const`

English:
lemma eventually_one_sub_smoothingFn_gt_const
  given: (c : Real) (hc : c < 1)
  proof: Eventually.natCast_atTop (p := fun n => c < 1 - ε n)
 eventually_one_sub_smoothingFn_gt_const_real c hc

中文:
引理 eventually_one_sub_smoothingFn_gt_const
  条件: (c : 实数) (hc : c < 1)
  证明: Eventually.natCast_atTop (p := fun n => c < 1 - ε n)
 eventually_one_sub_smoothingFn_gt_const_real c hc

Depends on / 依赖: Eventually, Eventually.natCast_atTop, eventually_one_sub_smoothingFn_gt_const_real, natCast_atTop
-/
lemma eventually_one_sub_smoothingFn_gt_const (c : Real) (hc : c < 1) :
    forallᶠ (n : Nat) in atTop, c < 1 - ε n :=
  Eventually.natCast_atTop (p := fun n => c < 1 - ε n)
 eventually_one_sub_smoothingFn_gt_const_real c hc

/--
lemma `eventually_one_sub_smoothingFn_pos_real` / 引理 `eventually_one_sub_smoothingFn_pos_real`

English:
lemma eventually_one_sub_smoothingFn_pos_real
  statement: forallᶠ (x : Real) in atTop, 0 < 1 - ε x
  proof: eventually_one_sub_smoothingFn_gt_const_real 0 zero_lt_one

中文:
引理 eventually_one_sub_smoothingFn_pos_real
  结论: 对任意ᶠ (x : 实数) in atTop, 0 < 1 - ε x
  证明: eventually_one_sub_smoothingFn_gt_const_real 0 zero_lt_one

Depends on / 依赖: eventually_one_sub_smoothingFn_gt_const_real, zero_lt_one
-/
lemma eventually_one_sub_smoothingFn_pos_real : forallᶠ (x : Real) in atTop, 0 < 1 - ε x :=
  eventually_one_sub_smoothingFn_gt_const_real 0 zero_lt_one

/--
lemma `eventually_one_sub_smoothingFn_pos` / 引理 `eventually_one_sub_smoothingFn_pos`

English:
lemma eventually_one_sub_smoothingFn_pos
  statement: forallᶠ (n : Nat) in atTop, 0 < 1 - ε n
  proof: eventually_one_sub_smoothingFn_pos_real.natCast_atTop

中文:
引理 eventually_one_sub_smoothingFn_pos
  结论: 对任意ᶠ (n : 自然数) in atTop, 0 < 1 - ε n
  证明: eventually_one_sub_smoothingFn_pos_real.natCast_atTop

Depends on / 依赖: eventually_one_sub_smoothingFn_pos_real, eventually_one_sub_smoothingFn_pos_real.natCast_atTop, natCast_atTop
-/
lemma eventually_one_sub_smoothingFn_pos : forallᶠ (n : Nat) in atTop, 0 < 1 - ε n :=
  eventually_one_sub_smoothingFn_pos_real.natCast_atTop

/--
lemma `eventually_one_sub_smoothingFn_nonneg` / 引理 `eventually_one_sub_smoothingFn_nonneg`

English:
lemma eventually_one_sub_smoothingFn_nonneg
  statement: forallᶠ (n : Nat) in atTop, 0 <= 1 - ε n
  proof: by
  filter_upwards [eventually_one_sub_smoothingFn_pos] with n hn; exact le_of_lt hn

include R in

中文:
引理 eventually_one_sub_smoothingFn_nonneg
  结论: 对任意ᶠ (n : 自然数) in atTop, 0 <= 1 - ε n
  证明: by
  filter_upwards [eventually_one_sub_smoothingFn_pos] with n hn; exact le_of_lt hn

include R in

Depends on / 依赖: eventually_one_sub_smoothingFn_pos, filter_upwards, le_of_lt
-/
lemma eventually_one_sub_smoothingFn_nonneg : forallᶠ (n : Nat) in atTop, 0 <= 1 - ε n := by
  filter_upwards [eventually_one_sub_smoothingFn_pos] with n hn; exact le_of_lt hn

include R in
/--
lemma `eventually_one_sub_smoothingFn_r_pos` / 引理 `eventually_one_sub_smoothingFn_r_pos`

English:
lemma eventually_one_sub_smoothingFn_r_pos
  statement: forallᶠ (n : Nat) in atTop, forall i, 0 < 1 - ε (r i n)
  proof: by
  rw [Filter.eventually_all]
  exact fun i => (R.tendsto_atTop_r_real i).eventually eventually_one_sub_smoothingFn_pos_real

@[aesop safe apply]

中文:
引理 eventually_one_sub_smoothingFn_r_pos
  结论: 对任意ᶠ (n : 自然数) in atTop, 对任意 i, 0 < 1 - ε (r i n)
  证明: by
  rw [Filter.eventually_all]
  exact fun i => (R.tendsto_atTop_r_real i).eventually eventually_one_sub_smoothingFn_pos_real

@[aesop safe apply]

Depends on / 依赖: Filter, Filter.eventually_all, R.tendsto_atTop_r_real, eventually, eventually_all, eventually_one_sub_smoothingFn_pos_real, tendsto_atTop_r_real
-/
lemma eventually_one_sub_smoothingFn_r_pos : forallᶠ (n : Nat) in atTop, forall i, 0 < 1 - ε (r i n) := by
  rw [Filter.eventually_all]
  exact fun i => (R.tendsto_atTop_r_real i).eventually eventually_one_sub_smoothingFn_pos_real

@[aesop safe apply]
/--
lemma `differentiableAt_smoothingFn` / 引理 `differentiableAt_smoothingFn`

English:
lemma differentiableAt_smoothingFn
  given: {x : Real} (hx : 1 < x)
  statement: DifferentiableAt Real ε x
  proof: by
  have : log x != 0 := Real.log_ne_zero_of_pos_of_ne_one (by positivity) (ne_of_gt hx)
  change DifferentiableAt Real (fun z => 1 / log z) x
  simp_rw [one_div]
  exact DifferentiableAt.inv (differentiableAt_log (by positivity)) this

@[aesop safe apply]

中文:
引理 differentiableAt_smoothingFn
  条件: {x : 实数} (hx : 1 < x)
  结论: DifferentiableAt 实数 ε x
  证明: by
  have : log x != 0 := Real.log_ne_zero_of_pos_of_ne_one (by positivity) (ne_of_gt hx)
  change DifferentiableAt Real (fun z => 1 / log z) x
  simp_rw [one_div]
  exact DifferentiableAt.inv (differentiableAt_log (by positivity)) this

@[aesop safe apply]

Depends on / 依赖: DifferentiableAt, DifferentiableAt.inv, Real.log_ne_zero_of_pos_of_ne_one, differentiableAt_log, log_ne_zero_of_pos_of_ne_one, ne_of_gt, one_div, simp_rw
-/
lemma differentiableAt_smoothingFn {x : Real} (hx : 1 < x) : DifferentiableAt Real ε x := by
  have : log x != 0 := Real.log_ne_zero_of_pos_of_ne_one (by positivity) (ne_of_gt hx)
  change DifferentiableAt Real (fun z => 1 / log z) x
  simp_rw [one_div]
  exact DifferentiableAt.inv (differentiableAt_log (by positivity)) this

@[aesop safe apply]
/--
lemma `differentiableAt_one_sub_smoothingFn` / 引理 `differentiableAt_one_sub_smoothingFn`

English:
lemma differentiableAt_one_sub_smoothingFn
  given: {x : Real} (hx : 1 < x)
  proof: DifferentiableAt.sub (differentiableAt_const _) differentiableAt_smoothingFn hx

中文:
引理 differentiableAt_one_sub_smoothingFn
  条件: {x : 实数} (hx : 1 < x)
  证明: DifferentiableAt.sub (differentiableAt_const _) differentiableAt_smoothingFn hx

Depends on / 依赖: DifferentiableAt, DifferentiableAt.sub, differentiableAt_const, differentiableAt_smoothingFn
-/
lemma differentiableAt_one_sub_smoothingFn {x : Real} (hx : 1 < x) :
    DifferentiableAt Real (fun z => 1 - ε z) x :=
DifferentiableAt.sub (differentiableAt_const _) differentiableAt_smoothingFn hx

/--
lemma `differentiableOn_one_sub_smoothingFn` / 引理 `differentiableOn_one_sub_smoothingFn`

English:
lemma differentiableOn_one_sub_smoothingFn
  statement: DifferentiableOn Real (fun z => 1 - ε z) (Set.Ioi 1)
  proof: fun _ hx => (differentiableAt_one_sub_smoothingFn hx).differentiableWithinAt

@[aesop safe apply]

中文:
引理 differentiableOn_one_sub_smoothingFn
  结论: DifferentiableOn 实数 (fun z => 1 - ε z) (Set.Ioi 1)
  证明: fun _ hx => (differentiableAt_one_sub_smoothingFn hx).differentiableWithinAt

@[aesop safe apply]

Depends on / 依赖: differentiableAt_one_sub_smoothingFn, differentiableWithinAt
-/
lemma differentiableOn_one_sub_smoothingFn : DifferentiableOn Real (fun z => 1 - ε z) (Set.Ioi 1) :=
  fun _ hx => (differentiableAt_one_sub_smoothingFn hx).differentiableWithinAt

@[aesop safe apply]
/--
lemma `differentiableAt_one_add_smoothingFn` / 引理 `differentiableAt_one_add_smoothingFn`

English:
lemma differentiableAt_one_add_smoothingFn
  given: {x : Real} (hx : 1 < x)
  proof: DifferentiableAt.add (differentiableAt_const _) differentiableAt_smoothingFn hx

中文:
引理 differentiableAt_one_add_smoothingFn
  条件: {x : 实数} (hx : 1 < x)
  证明: DifferentiableAt.add (differentiableAt_const _) differentiableAt_smoothingFn hx

Depends on / 依赖: DifferentiableAt, DifferentiableAt.add, differentiableAt_const, differentiableAt_smoothingFn
-/
lemma differentiableAt_one_add_smoothingFn {x : Real} (hx : 1 < x) :
    DifferentiableAt Real (fun z => 1 + ε z) x :=
DifferentiableAt.add (differentiableAt_const _) differentiableAt_smoothingFn hx

/--
lemma `differentiableOn_one_add_smoothingFn` / 引理 `differentiableOn_one_add_smoothingFn`

English:
lemma differentiableOn_one_add_smoothingFn
  statement: DifferentiableOn Real (fun z => 1 + ε z) (Set.Ioi 1)
  proof: fun _ hx => (differentiableAt_one_add_smoothingFn hx).differentiableWithinAt

中文:
引理 differentiableOn_one_add_smoothingFn
  结论: DifferentiableOn 实数 (fun z => 1 + ε z) (Set.Ioi 1)
  证明: fun _ hx => (differentiableAt_one_add_smoothingFn hx).differentiableWithinAt

Depends on / 依赖: differentiableAt_one_add_smoothingFn, differentiableWithinAt
-/
lemma differentiableOn_one_add_smoothingFn : DifferentiableOn Real (fun z => 1 + ε z) (Set.Ioi 1) :=
  fun _ hx => (differentiableAt_one_add_smoothingFn hx).differentiableWithinAt

/--
lemma `deriv_smoothingFn` / 引理 `deriv_smoothingFn`

English:
lemma deriv_smoothingFn
  given: {x : Real}
  statement: deriv ε x = -x⁻¹ / (log x ^ 2)
  proof: by
  unfold smoothingFn
  simp

中文:
引理 deriv_smoothingFn
  条件: {x : 实数}
  结论: deriv ε x = -x⁻¹ / (log x ^ 2)
  证明: by
  unfold smoothingFn
  simp

Depends on / 依赖: smoothingFn
-/
lemma deriv_smoothingFn {x : Real} : deriv ε x = -x⁻¹ / (log x ^ 2) := by
  unfold smoothingFn
  simp

/--
lemma `isLittleO_deriv_smoothingFn` / 引理 `isLittleO_deriv_smoothingFn`

English:
lemma isLittleO_deriv_smoothingFn
  statement: deriv ε =o[atTop] fun x => x⁻¹
  proof: calc deriv ε
    _ =ᶠ[atTop] fun x => -x⁻¹ / (log x ^ 2) := by
      filter_upwards with x
      rw [deriv_smoothingFn]
    _ = fun x => (-x * log x ^ 2)⁻¹ := by
      simp_rw [neg_div, div_eq_mul_inv, ← mul_inv, neg_inv, neg_mul]
    _ =o[atTop] fun x => (x * 1)⁻¹ := by
      refine IsLittleO.inv_r

中文:
引理 isLittleO_deriv_smoothingFn
  结论: deriv ε =o[atTop] fun x => x⁻¹
  证明: calc deriv ε
    _ =ᶠ[atTop] fun x => -x⁻¹ / (log x ^ 2) := by
      filter_upwards with x
      rw [deriv_smoothingFn]
    _ = fun x => (-x * log x ^ 2)⁻¹ := by
      simp_rw [neg_div, div_eq_mul_inv, ← mul_inv, neg_inv, neg_mul]
    _ =o[atTop] fun x => (x * 1)⁻¹ := by
      refine IsLittleO.inv_r

Depends on / 依赖: IsBigO, IsBigO.mul_isLittleO, IsLittleO, IsLittleO.inv_rev, Tendsto, Tendsto.comp, deriv_smoothingFn, div_eq_mul_inv, filter_upwards, inv_rev, isBigO_neg_right, isBigO_refl, isLittleO_one_left_iff, mul_inv, mul_isLittleO, neg_div, neg_inv, neg_mul, simp_rw, tendsto_log_atTop
-/
lemma isLittleO_deriv_smoothingFn : deriv ε =o[atTop] fun x => x⁻¹ :=
  calc deriv ε
    _ =ᶠ[atTop] fun x => -x⁻¹ / (log x ^ 2) := by
      filter_upwards with x
      rw [deriv_smoothingFn]
    _ = fun x => (-x * log x ^ 2)⁻¹ := by
      simp_rw [neg_div, div_eq_mul_inv, ← mul_inv, neg_inv, neg_mul]
    _ =o[atTop] fun x => (x * 1)⁻¹ := by
      refine IsLittleO.inv_rev ?_ ?_
      · refine IsBigO.mul_isLittleO
          (by rw [isBigO_neg_right]; aesop (add safe isBigO_refl)) ?_
        rw [isLittleO_one_left_iff]
        exact Tendsto.comp tendsto_norm_atTop_atTop
 Tendsto.comp (tendsto_pow_atTop (by norm_num)) tendsto_log_atTop
      · exact Filter.Eventually.of_forall (fun x hx => by rw [mul_one] at hx; simp [hx])
    _ = fun x => x⁻¹ := by simp

/--
lemma `eventually_deriv_one_sub_smoothingFn` / 引理 `eventually_deriv_one_sub_smoothingFn`

English:
lemma eventually_deriv_one_sub_smoothingFn
  proof: calc deriv (fun x => 1 - ε x)
    _ =ᶠ[atTop] -(deriv ε) := by
      filter_upwards [eventually_gt_atTop 1] with x hx; rw [deriv_fun_sub] <;> aesop
    _ =ᶠ[atTop] fun x => x⁻¹ / (log x ^ 2) := by
      filter_upwards with x
      simp [deriv_smoothingFn, neg_div]

中文:
引理 eventually_deriv_one_sub_smoothingFn
  证明: calc deriv (fun x => 1 - ε x)
    _ =ᶠ[atTop] -(deriv ε) := by
      filter_upwards [eventually_gt_atTop 1] with x hx; rw [deriv_fun_sub] <;> aesop
    _ =ᶠ[atTop] fun x => x⁻¹ / (log x ^ 2) := by
      filter_upwards with x
      simp [deriv_smoothingFn, neg_div]

Depends on / 依赖: deriv_fun_sub, deriv_smoothingFn, eventually_gt_atTop, filter_upwards, neg_div
-/
lemma eventually_deriv_one_sub_smoothingFn :
    deriv (fun x => 1 - ε x) =ᶠ[atTop] fun x => x⁻¹ / (log x ^ 2) :=
  calc deriv (fun x => 1 - ε x)
    _ =ᶠ[atTop] -(deriv ε) := by
      filter_upwards [eventually_gt_atTop 1] with x hx; rw [deriv_fun_sub] <;> aesop
    _ =ᶠ[atTop] fun x => x⁻¹ / (log x ^ 2) := by
      filter_upwards with x
      simp [deriv_smoothingFn, neg_div]

/--
lemma `eventually_deriv_one_add_smoothingFn` / 引理 `eventually_deriv_one_add_smoothingFn`

English:
lemma eventually_deriv_one_add_smoothingFn
  proof: calc deriv (fun x => 1 + ε x)
    _ =ᶠ[atTop] deriv ε := by
      filter_upwards [eventually_gt_atTop 1] with x hx; rw [deriv_fun_add] <;> aesop
    _ =ᶠ[atTop] fun x => -x⁻¹ / (log x ^ 2) := by
      filter_upwards with x
      simp [deriv_smoothingFn]

中文:
引理 eventually_deriv_one_add_smoothingFn
  证明: calc deriv (fun x => 1 + ε x)
    _ =ᶠ[atTop] deriv ε := by
      filter_upwards [eventually_gt_atTop 1] with x hx; rw [deriv_fun_add] <;> aesop
    _ =ᶠ[atTop] fun x => -x⁻¹ / (log x ^ 2) := by
      filter_upwards with x
      simp [deriv_smoothingFn]

Depends on / 依赖: deriv_fun_add, deriv_smoothingFn, eventually_gt_atTop, filter_upwards
-/
lemma eventually_deriv_one_add_smoothingFn :
    deriv (fun x => 1 + ε x) =ᶠ[atTop] fun x => -x⁻¹ / (log x ^ 2) :=
  calc deriv (fun x => 1 + ε x)
    _ =ᶠ[atTop] deriv ε := by
      filter_upwards [eventually_gt_atTop 1] with x hx; rw [deriv_fun_add] <;> aesop
    _ =ᶠ[atTop] fun x => -x⁻¹ / (log x ^ 2) := by
      filter_upwards with x
      simp [deriv_smoothingFn]

/--
lemma `isLittleO_deriv_one_sub_smoothingFn` / 引理 `isLittleO_deriv_one_sub_smoothingFn`

English:
lemma isLittleO_deriv_one_sub_smoothingFn
  proof: calc deriv (fun x => 1 - ε x)
    _ =ᶠ[atTop] fun z => -(deriv ε z) := by
      filter_upwards [eventually_gt_atTop 1] with x hx; rw [deriv_fun_sub] <;> aesop
    _ =o[atTop] fun x => x⁻¹ := by rw [isLittleO_neg_left]; exact isLittleO_deriv_smoothingFn

中文:
引理 isLittleO_deriv_one_sub_smoothingFn
  证明: calc deriv (fun x => 1 - ε x)
    _ =ᶠ[atTop] fun z => -(deriv ε z) := by
      filter_upwards [eventually_gt_atTop 1] with x hx; rw [deriv_fun_sub] <;> aesop
    _ =o[atTop] fun x => x⁻¹ := by rw [isLittleO_neg_left]; exact isLittleO_deriv_smoothingFn

Depends on / 依赖: deriv_fun_sub, eventually_gt_atTop, filter_upwards, isLittleO_deriv_smoothingFn, isLittleO_neg_left
-/
lemma isLittleO_deriv_one_sub_smoothingFn :
    deriv (fun x => 1 - ε x) =o[atTop] fun (x : Real) => x⁻¹ :=
  calc deriv (fun x => 1 - ε x)
    _ =ᶠ[atTop] fun z => -(deriv ε z) := by
      filter_upwards [eventually_gt_atTop 1] with x hx; rw [deriv_fun_sub] <;> aesop
    _ =o[atTop] fun x => x⁻¹ := by rw [isLittleO_neg_left]; exact isLittleO_deriv_smoothingFn

/--
lemma `isLittleO_deriv_one_add_smoothingFn` / 引理 `isLittleO_deriv_one_add_smoothingFn`

English:
lemma isLittleO_deriv_one_add_smoothingFn
  proof: calc deriv (fun x => 1 + ε x)
    _ =ᶠ[atTop] fun z => deriv ε z := by
      filter_upwards [eventually_gt_atTop 1] with x hx; rw [deriv_fun_add] <;> aesop
    _ =o[atTop] fun x => x⁻¹ := isLittleO_deriv_smoothingFn

中文:
引理 isLittleO_deriv_one_add_smoothingFn
  证明: calc deriv (fun x => 1 + ε x)
    _ =ᶠ[atTop] fun z => deriv ε z := by
      filter_upwards [eventually_gt_atTop 1] with x hx; rw [deriv_fun_add] <;> aesop
    _ =o[atTop] fun x => x⁻¹ := isLittleO_deriv_smoothingFn

Depends on / 依赖: deriv_fun_add, eventually_gt_atTop, filter_upwards, isLittleO_deriv_smoothingFn
-/
lemma isLittleO_deriv_one_add_smoothingFn :
    deriv (fun x => 1 + ε x) =o[atTop] fun (x : Real) => x⁻¹ :=
  calc deriv (fun x => 1 + ε x)
    _ =ᶠ[atTop] fun z => deriv ε z := by
      filter_upwards [eventually_gt_atTop 1] with x hx; rw [deriv_fun_add] <;> aesop
    _ =o[atTop] fun x => x⁻¹ := isLittleO_deriv_smoothingFn

/--
lemma `eventually_one_add_smoothingFn_pos` / 引理 `eventually_one_add_smoothingFn_pos`

English:
lemma eventually_one_add_smoothingFn_pos
  statement: forallᶠ (n : Nat) in atTop, 0 < 1 + ε n
  proof: by
  have h₁ := isLittleO_smoothingFn_one
  rw [isLittleO_iff] at h₁
  refine Eventually.natCast_atTop (p := fun n => 0 < 1 + ε n) ?_
  filter_upwards [h₁ (by simp : (0 : Real) < 1 / 2), eventually_gt_atTop 1] with x _ hx'
  have : 0 < log x := Real.log_pos hx'
  change 0 < 1 + 1 / log x
  positivit

中文:
引理 eventually_one_add_smoothingFn_pos
  结论: 对任意ᶠ (n : 自然数) in atTop, 0 < 1 + ε n
  证明: by
  have h₁ := isLittleO_smoothingFn_one
  rw [isLittleO_iff] at h₁
  refine Eventually.natCast_atTop (p := fun n => 0 < 1 + ε n) ?_
  filter_upwards [h₁ (by simp : (0 : Real) < 1 / 2), eventually_gt_atTop 1] with x _ hx'
  have : 0 < log x := Real.log_pos hx'
  change 0 < 1 + 1 / log x
  positivit

Depends on / 依赖: Eventually, Eventually.natCast_atTop, Real.log_pos, eventually_gt_atTop, filter_upwards, isLittleO_iff, isLittleO_smoothingFn_one, log_pos, natCast_atTop
-/
lemma eventually_one_add_smoothingFn_pos : forallᶠ (n : Nat) in atTop, 0 < 1 + ε n := by
  have h₁ := isLittleO_smoothingFn_one
  rw [isLittleO_iff] at h₁
  refine Eventually.natCast_atTop (p := fun n => 0 < 1 + ε n) ?_
  filter_upwards [h₁ (by simp : (0 : Real) < 1 / 2), eventually_gt_atTop 1] with x _ hx'
  have : 0 < log x := Real.log_pos hx'
  change 0 < 1 + 1 / log x
  positivity

include R in
/--
lemma `eventually_one_add_smoothingFn_r_pos` / 引理 `eventually_one_add_smoothingFn_r_pos`

English:
lemma eventually_one_add_smoothingFn_r_pos
  statement: forallᶠ (n : Nat) in atTop, forall i, 0 < 1 + ε (r i n)
  proof: by
  rw [Filter.eventually_all]
  exact fun i => (R.tendsto_atTop_r i).eventually (f := r i) eventually_one_add_smoothingFn_pos

中文:
引理 eventually_one_add_smoothingFn_r_pos
  结论: 对任意ᶠ (n : 自然数) in atTop, 对任意 i, 0 < 1 + ε (r i n)
  证明: by
  rw [Filter.eventually_all]
  exact fun i => (R.tendsto_atTop_r i).eventually (f := r i) eventually_one_add_smoothingFn_pos

Depends on / 依赖: Filter, Filter.eventually_all, R.tendsto_atTop_r, eventually, eventually_all, eventually_one_add_smoothingFn_pos, tendsto_atTop_r
-/
lemma eventually_one_add_smoothingFn_r_pos : forallᶠ (n : Nat) in atTop, forall i, 0 < 1 + ε (r i n) := by
  rw [Filter.eventually_all]
  exact fun i => (R.tendsto_atTop_r i).eventually (f := r i) eventually_one_add_smoothingFn_pos

/--
lemma `eventually_one_add_smoothingFn_nonneg` / 引理 `eventually_one_add_smoothingFn_nonneg`

English:
lemma eventually_one_add_smoothingFn_nonneg
  statement: forallᶠ (n : Nat) in atTop, 0 <= 1 + ε n
  proof: by
  filter_upwards [eventually_one_add_smoothingFn_pos] with n hn; exact le_of_lt hn

中文:
引理 eventually_one_add_smoothingFn_nonneg
  结论: 对任意ᶠ (n : 自然数) in atTop, 0 <= 1 + ε n
  证明: by
  filter_upwards [eventually_one_add_smoothingFn_pos] with n hn; exact le_of_lt hn

Depends on / 依赖: eventually_one_add_smoothingFn_pos, filter_upwards, le_of_lt
-/
lemma eventually_one_add_smoothingFn_nonneg : forallᶠ (n : Nat) in atTop, 0 <= 1 + ε n := by
  filter_upwards [eventually_one_add_smoothingFn_pos] with n hn; exact le_of_lt hn

/--
lemma `strictAntiOn_smoothingFn` / 引理 `strictAntiOn_smoothingFn`

English:
lemma strictAntiOn_smoothingFn
  statement: StrictAntiOn ε (Set.Ioi 1)
  proof: by
  change StrictAntiOn (fun x => 1 / log x) (Set.Ioi 1)
  simp_rw [one_div]
  refine StrictAntiOn.comp_strictMonoOn inv_strictAntiOn ?log fun _ hx => log_pos hx
  refine StrictMonoOn.mono strictMonoOn_log (fun x hx => ?_)
  exact Set.Ioi_subset_Ioi zero_le_one hx

中文:
引理 strictAntiOn_smoothingFn
  结论: StrictAntiOn ε (Set.Ioi 1)
  证明: by
  change StrictAntiOn (fun x => 1 / log x) (Set.Ioi 1)
  simp_rw [one_div]
  refine StrictAntiOn.comp_strictMonoOn inv_strictAntiOn ?log fun _ hx => log_pos hx
  refine StrictMonoOn.mono strictMonoOn_log (fun x hx => ?_)
  exact Set.Ioi_subset_Ioi zero_le_one hx

Depends on / 依赖: Ioi_subset_Ioi, Set.Ioi, Set.Ioi_subset_Ioi, StrictAntiOn, StrictAntiOn.comp_strictMonoOn, StrictMonoOn, StrictMonoOn.mono, comp_strictMonoOn, inv_strictAntiOn, log_pos, one_div, simp_rw, strictMonoOn_log, zero_le_one
-/
lemma strictAntiOn_smoothingFn : StrictAntiOn ε (Set.Ioi 1) := by
  change StrictAntiOn (fun x => 1 / log x) (Set.Ioi 1)
  simp_rw [one_div]
  refine StrictAntiOn.comp_strictMonoOn inv_strictAntiOn ?log fun _ hx => log_pos hx
  refine StrictMonoOn.mono strictMonoOn_log (fun x hx => ?_)
  exact Set.Ioi_subset_Ioi zero_le_one hx

/--
lemma `strictMonoOn_one_sub_smoothingFn` / 引理 `strictMonoOn_one_sub_smoothingFn`

English:
lemma strictMonoOn_one_sub_smoothingFn
  proof: by
  simp_rw [sub_eq_add_neg]
  exact StrictMonoOn.const_add (StrictAntiOn.neg <| strictAntiOn_smoothingFn) 1

中文:
引理 strictMonoOn_one_sub_smoothingFn
  证明: by
  simp_rw [sub_eq_add_neg]
  exact StrictMonoOn.const_add (StrictAntiOn.neg <| strictAntiOn_smoothingFn) 1

Depends on / 依赖: StrictAntiOn, StrictAntiOn.neg, StrictMonoOn, StrictMonoOn.const_add, const_add, simp_rw, strictAntiOn_smoothingFn, sub_eq_add_neg
-/
lemma strictMonoOn_one_sub_smoothingFn :
    StrictMonoOn (fun (x : Real) => (1 : Real) - ε x) (Set.Ioi 1) := by
  simp_rw [sub_eq_add_neg]
  exact StrictMonoOn.const_add (StrictAntiOn.neg <| strictAntiOn_smoothingFn) 1

/--
lemma `strictAntiOn_one_add_smoothingFn` / 引理 `strictAntiOn_one_add_smoothingFn`

English:
lemma strictAntiOn_one_add_smoothingFn
  statement: StrictAntiOn (fun (x : Real) => (1 : Real) + ε x) (Set.Ioi 1)
  proof: StrictAntiOn.const_add strictAntiOn_smoothingFn 1

中文:
引理 strictAntiOn_one_add_smoothingFn
  结论: StrictAntiOn (fun (x : 实数) => (1 : 实数) + ε x) (Set.Ioi 1)
  证明: StrictAntiOn.const_add strictAntiOn_smoothingFn 1

Depends on / 依赖: StrictAntiOn, StrictAntiOn.const_add, const_add, strictAntiOn_smoothingFn
-/
lemma strictAntiOn_one_add_smoothingFn : StrictAntiOn (fun (x : Real) => (1 : Real) + ε x) (Set.Ioi 1) :=
  StrictAntiOn.const_add strictAntiOn_smoothingFn 1

section
include R

/--
lemma `isEquivalent_smoothingFn_sub_self` / 引理 `isEquivalent_smoothingFn_sub_self`

English:
lemma isEquivalent_smoothingFn_sub_self
  given: (i : α)
  proof: by
  calc (fun (n : Nat) => 1 / log (b i * n) - 1 / log n)
    _ =ᶠ[atTop] fun (n : Nat) => (log n - log (b i * n)) / (log (b i * n) * log n) := by
      filter_upwards [eventually_gt_atTop 1, R.eventually_log_b_mul_pos] with n hn hn'
have h_log_pos : 0 < log n := Real.log_pos by simp_all
      simp

中文:
引理 isEquivalent_smoothingFn_sub_self
  条件: (i : α)
  证明: by
  calc (fun (n : Nat) => 1 / log (b i * n) - 1 / log n)
    _ =ᶠ[atTop] fun (n : Nat) => (log n - log (b i * n)) / (log (b i * n) * log n) := by
      filter_upwards [eventually_gt_atTop 1, R.eventually_log_b_mul_pos] with n hn hn'
have h_log_pos : 0 < log n := Real.log_pos by simp_all
      simp

Depends on / 依赖: R.eventually_log_b_mul_pos, Real.log_pos, eventually_gt_atTop, eventually_log_b_mul_pos, eventually_ne_atTop, filter_upwards, h_log_pos, inv_sub_inv, log_pos, one_div
-/
lemma isEquivalent_smoothingFn_sub_self (i : α) :
    (fun (n : Nat) => ε (b i * n) - ε n) ~[atTop] fun n => -log (b i) / (log n) ^ 2 := by
  calc (fun (n : Nat) => 1 / log (b i * n) - 1 / log n)
    _ =ᶠ[atTop] fun (n : Nat) => (log n - log (b i * n)) / (log (b i * n) * log n) := by
      filter_upwards [eventually_gt_atTop 1, R.eventually_log_b_mul_pos] with n hn hn'
have h_log_pos : 0 < log n := Real.log_pos by simp_all
      simp only [one_div]
      rw [inv_sub_inv (by have := hn' i; positivity) (by aesop)]
    _ =ᶠ[atTop] (fun (n : Nat) => (log n - log (b i) - log n) / ((log (b i) + log n) * log n)) := by
      filter_upwards [eventually_ne_atTop 0] with n hn
      have : 0 < b i := R.b_pos i
      rw [log_mul (by positivity) (by simp_all)]; rw [sub_add_eq_sub_sub]
    _ = (fun (n : Nat) => -log (b i) / ((log (b i) + log n) * log n)) := by ext; congr; ring
    _ ~[atTop] (fun (n : Nat) => -log (b i) / (log n * log n)) := by
refine IsEquivalent.div (IsEquivalent.refl) IsEquivalent.mul ?_ (IsEquivalent.refl)
      have : (fun (n : Nat) => log (b i) + log n) = fun (n : Nat) => log n + log (b i) := by
        ext; simp [add_comm]
      rw [this]
      exact IsEquivalent.add_isLittleO IsEquivalent.refl
 IsLittleO.natCast_atTop (f := fun (_ : Real) => log (b i))
          isLittleO_const_log_atTop
    _ = (fun (n : Nat) => -log (b i) / (log n) ^ 2) := by ext; congr 1; rw [← pow_two]

/--
lemma `isTheta_smoothingFn_sub_self` / 引理 `isTheta_smoothingFn_sub_self`

English:
lemma isTheta_smoothingFn_sub_self
  given: (i : α)
  proof: by
  calc (fun (n : Nat) => ε (b i * n) - ε n)
    _ =Θ[atTop] fun n => (-log (b i)) / (log n) ^ 2 :=
      (R.isEquivalent_smoothingFn_sub_self i).isTheta
    _ = fun (n : Nat) => (-log (b i)) * 1 / (log n) ^ 2 := by simp only [mul_one]
    _ = fun (n : Nat) => -log (b i) * (1 / (log n) ^ 2) := by 

中文:
引理 isTheta_smoothingFn_sub_self
  条件: (i : α)
  证明: by
  calc (fun (n : Nat) => ε (b i * n) - ε n)
    _ =Θ[atTop] fun n => (-log (b i)) / (log n) ^ 2 :=
      (R.isEquivalent_smoothingFn_sub_self i).isTheta
    _ = fun (n : Nat) => (-log (b i)) * 1 / (log n) ^ 2 := by simp only [mul_one]
    _ = fun (n : Nat) => -log (b i) * (1 / (log n) ^ 2) := by 

Depends on / 依赖: R.b_lt_one, R.b_pos, R.isEquivalent_smoothingFn_sub_self, Real.log_ne_zero_of_pos_of_ne_one, b_lt_one, b_pos, isEquivalent_smoothingFn_sub_self, isTheta, isTheta_cons, log_ne_zero_of_pos_of_ne_one, mul_div_assoc, mul_one, ne_of_lt, neg_ne_zero, simp_rw
-/
lemma isTheta_smoothingFn_sub_self (i : α) :
    (fun (n : Nat) => ε (b i * n) - ε n) =Θ[atTop] fun n => 1 / (log n) ^ 2 := by
  calc (fun (n : Nat) => ε (b i * n) - ε n)
    _ =Θ[atTop] fun n => (-log (b i)) / (log n) ^ 2 :=
      (R.isEquivalent_smoothingFn_sub_self i).isTheta
    _ = fun (n : Nat) => (-log (b i)) * 1 / (log n) ^ 2 := by simp only [mul_one]
    _ = fun (n : Nat) => -log (b i) * (1 / (log n) ^ 2) := by simp_rw [← mul_div_assoc]
    _ =Θ[atTop] fun (n : Nat) => 1 / (log n) ^ 2 := by
      have : -log (b i) != 0 := by
        rw [neg_ne_zero]
        exact Real.log_ne_zero_of_pos_of_ne_one (R.b_pos i) (ne_of_lt <| R.b_lt_one i)
      rw [← isTheta_const_mul_right this]

/-!
### Akra-Bazzi exponent `p`

Every Akra-Bazzi recurrence has an associated exponent, denoted by `p : ℝ`, such that
`∑ a_i b_i^p = 1`. This section shows the existence and uniqueness of this exponent `p` for any
`R : AkraBazziRecurrence`. These results are used in the next section to define the asymptotic
bound expression. -/

@[continuity, fun_prop]
/--
lemma `continuous_sumCoeffsExp` / 引理 `continuous_sumCoeffsExp`

English:
lemma continuous_sumCoeffsExp
  statement: Continuous (fun (p : Real) => ∑ i, a i * (b i) ^ p)
  proof: by
  refine continuous_finsetSum Finset.univ fun i _ => Continuous.mul (by fun_prop) ?_
  exact Continuous.rpow continuous_const continuous_id (fun x => Or.inl (ne_of_gt (R.b_pos i)))

中文:
引理 continuous_sumCoeffsExp
  结论: Continuous (fun (p : 实数) => ∑ i, a i * (b i) ^ p)
  证明: by
  refine continuous_finsetSum Finset.univ fun i _ => Continuous.mul (by fun_prop) ?_
  exact Continuous.rpow continuous_const continuous_id (fun x => Or.inl (ne_of_gt (R.b_pos i)))

Depends on / 依赖: Continuous, Continuous.mul, Continuous.rpow, Finset, Finset.univ, Or.inl, R.b_pos, b_pos, continuous_const, continuous_finsetSum, continuous_id, fun_prop, ne_of_gt
-/
lemma continuous_sumCoeffsExp : Continuous (fun (p : Real) => ∑ i, a i * (b i) ^ p) := by
  refine continuous_finsetSum Finset.univ fun i _ => Continuous.mul (by fun_prop) ?_
  exact Continuous.rpow continuous_const continuous_id (fun x => Or.inl (ne_of_gt (R.b_pos i)))

/--
lemma `strictAnti_sumCoeffsExp` / 引理 `strictAnti_sumCoeffsExp`

English:
lemma strictAnti_sumCoeffsExp
  statement: StrictAnti (fun (p : Real) => ∑ i, a i * (b i) ^ p)
  proof: by
  rw [← Finset.sum_fn]
  refine Finset.sum_induction_nonempty _ _ (fun _ _ => StrictAnti.add) univ_nonempty ?terms
  refine fun i _ => StrictAnti.const_mul ?_ (R.a_pos i)
  exact Real.strictAnti_rpow_of_base_lt_one (R.b_pos i) (R.b_lt_one i)

中文:
引理 strictAnti_sumCoeffsExp
  结论: StrictAnti (fun (p : 实数) => ∑ i, a i * (b i) ^ p)
  证明: by
  rw [← Finset.sum_fn]
  refine Finset.sum_induction_nonempty _ _ (fun _ _ => StrictAnti.add) univ_nonempty ?terms
  refine fun i _ => StrictAnti.const_mul ?_ (R.a_pos i)
  exact Real.strictAnti_rpow_of_base_lt_one (R.b_pos i) (R.b_lt_one i)

Depends on / 依赖: Finset, Finset.sum_fn, Finset.sum_induction_nonempty, R.a_pos, R.b_lt_one, R.b_pos, Real.strictAnti_rpow_of_base_lt_one, StrictAnti, StrictAnti.add, StrictAnti.const_mul, a_pos, b_lt_one, b_pos, const_mul, strictAnti_rpow_of_base_lt_one, sum_fn, sum_induction_nonempty, univ_nonempty
-/
lemma strictAnti_sumCoeffsExp : StrictAnti (fun (p : Real) => ∑ i, a i * (b i) ^ p) := by
  rw [← Finset.sum_fn]
  refine Finset.sum_induction_nonempty _ _ (fun _ _ => StrictAnti.add) univ_nonempty ?terms
  refine fun i _ => StrictAnti.const_mul ?_ (R.a_pos i)
  exact Real.strictAnti_rpow_of_base_lt_one (R.b_pos i) (R.b_lt_one i)

/--
lemma `tendsto_zero_sumCoeffsExp` / 引理 `tendsto_zero_sumCoeffsExp`

English:
lemma tendsto_zero_sumCoeffsExp
  statement: Tendsto (fun (p : Real) => ∑ i, a i * (b i) ^ p) atTop (𝓝 0)
  proof: by
  have h₁ : Finset.univ.sum (fun _ : α => (0 : Real)) = 0 := by simp
  rw [← h₁]
  refine tendsto_finsetSum (univ : Finset α) (fun i _ => ?_)
  rw [← mul_zero (a i)]
refine Tendsto.mul (by simp) tendsto_rpow_atTop_of_base_lt_one _ ?_ (R.b_lt_one i)
  have := R.b_pos i
  linarith

中文:
引理 tendsto_zero_sumCoeffsExp
  结论: Tendsto (fun (p : 实数) => ∑ i, a i * (b i) ^ p) atTop (𝓝 0)
  证明: by
  have h₁ : Finset.univ.sum (fun _ : α => (0 : Real)) = 0 := by simp
  rw [← h₁]
  refine tendsto_finsetSum (univ : Finset α) (fun i _ => ?_)
  rw [← mul_zero (a i)]
refine Tendsto.mul (by simp) tendsto_rpow_atTop_of_base_lt_one _ ?_ (R.b_lt_one i)
  have := R.b_pos i
  linarith

Depends on / 依赖: Finset, Finset.univ.sum, R.b_lt_one, R.b_pos, Tendsto, Tendsto.mul, b_lt_one, b_pos, mul_zero, tendsto_finsetSum, tendsto_rpow_atTop_of_base_lt_one
-/
lemma tendsto_zero_sumCoeffsExp : Tendsto (fun (p : Real) => ∑ i, a i * (b i) ^ p) atTop (𝓝 0) := by
  have h₁ : Finset.univ.sum (fun _ : α => (0 : Real)) = 0 := by simp
  rw [← h₁]
  refine tendsto_finsetSum (univ : Finset α) (fun i _ => ?_)
  rw [← mul_zero (a i)]
refine Tendsto.mul (by simp) tendsto_rpow_atTop_of_base_lt_one _ ?_ (R.b_lt_one i)
  have := R.b_pos i
  linarith

/--
lemma `tendsto_atTop_sumCoeffsExp` / 引理 `tendsto_atTop_sumCoeffsExp`

English:
lemma tendsto_atTop_sumCoeffsExp
  statement: Tendsto (fun (p : Real) => ∑ i, a i * (b i) ^ p) atBot atTop
  proof: by
  have h₁ : Tendsto (fun p : Real => (a (max_bi b) : Real) * b (max_bi b) ^ p) atBot atTop :=
Tendsto.const_mul_atTop (R.a_pos (max_bi b)) tendsto_rpow_atBot_of_base_lt_one _
      (by have := R.b_pos (max_bi b); linarith) (R.b_lt_one _)
  refine tendsto_atTop_mono (fun p => ?_) h₁
  refine Finse

中文:
引理 tendsto_atTop_sumCoeffsExp
  结论: Tendsto (fun (p : 实数) => ∑ i, a i * (b i) ^ p) atBot atTop
  证明: by
  have h₁ : Tendsto (fun p : Real => (a (max_bi b) : Real) * b (max_bi b) ^ p) atBot atTop :=
Tendsto.const_mul_atTop (R.a_pos (max_bi b)) tendsto_rpow_atBot_of_base_lt_one _
      (by have := R.b_pos (max_bi b); linarith) (R.b_lt_one _)
  refine tendsto_atTop_mono (fun p => ?_) h₁
  refine Finse

Depends on / 依赖: Finset, Finset.single_le_sum, R.a_pos, R.b_lt_one, R.b_pos, Tendsto, Tendsto.const_mul_atTop, a_pos, b_lt_one, b_pos, const_mul_atTop, max_bi, mem_univ, single_le_sum, tendsto_atTop_mono, tendsto_rpow_atBot_of_base_lt_one
-/
lemma tendsto_atTop_sumCoeffsExp : Tendsto (fun (p : Real) => ∑ i, a i * (b i) ^ p) atBot atTop := by
  have h₁ : Tendsto (fun p : Real => (a (max_bi b) : Real) * b (max_bi b) ^ p) atBot atTop :=
Tendsto.const_mul_atTop (R.a_pos (max_bi b)) tendsto_rpow_atBot_of_base_lt_one _
      (by have := R.b_pos (max_bi b); linarith) (R.b_lt_one _)
  refine tendsto_atTop_mono (fun p => ?_) h₁
  refine Finset.single_le_sum (f := fun i => (a i : Real) * b i ^ p) (fun i _ => ?_) (mem_univ _)
  positivity [R.a_pos i, R.b_pos i]

/--
lemma `one_mem_range_sumCoeffsExp` / 引理 `one_mem_range_sumCoeffsExp`

English:
lemma one_mem_range_sumCoeffsExp
  statement: 1 in Set.range (fun (p : Real) => ∑ i, a i * (b i) ^ p)
  proof: by
  refine mem_range_of_exists_le_of_exists_ge R.continuous_sumCoeffsExp ?le_one ?ge_one
  case le_one =>
.exists exact R.tendsto_zero_sumCoeffsExp.eventually_le_const zero_lt_one
  case ge_one =>
.exists exact R.tendsto_atTop_sumCoeffsExp.eventually_ge_atTop _

中文:
引理 one_mem_range_sumCoeffsExp
  结论: 1 in Set.range (fun (p : 实数) => ∑ i, a i * (b i) ^ p)
  证明: by
  refine mem_range_of_exists_le_of_exists_ge R.continuous_sumCoeffsExp ?le_one ?ge_one
  case le_one =>
.exists exact R.tendsto_zero_sumCoeffsExp.eventually_le_const zero_lt_one
  case ge_one =>
.exists exact R.tendsto_atTop_sumCoeffsExp.eventually_ge_atTop _

Depends on / 依赖: R.continuous_sumCoeffsExp, R.tendsto_atTop_sumCoeffsExp.eventually_ge_atTop, R.tendsto_zero_sumCoeffsExp.eventually_le_const, continuous_sumCoeffsExp, eventually_ge_atTop, eventually_le_const, ge_one, le_one, mem_range_of_exists_le_of_exists_ge, tendsto_atTop_sumCoeffsExp, tendsto_zero_sumCoeffsExp, zero_lt_one
-/
lemma one_mem_range_sumCoeffsExp : 1 in Set.range (fun (p : Real) => ∑ i, a i * (b i) ^ p) := by
  refine mem_range_of_exists_le_of_exists_ge R.continuous_sumCoeffsExp ?le_one ?ge_one
  case le_one =>
.exists exact R.tendsto_zero_sumCoeffsExp.eventually_le_const zero_lt_one
  case ge_one =>
.exists exact R.tendsto_atTop_sumCoeffsExp.eventually_ge_atTop _

/--
lemma `injective_sumCoeffsExp` / 引理 `injective_sumCoeffsExp`

English:
lemma injective_sumCoeffsExp
  statement: Function.Injective (fun (p : Real) => ∑ i, a i * (b i) ^ p)
  proof: R.strictAnti_sumCoeffsExp.injective

中文:
引理 injective_sumCoeffsExp
  结论: Function.Injective (fun (p : 实数) => ∑ i, a i * (b i) ^ p)
  证明: R.strictAnti_sumCoeffsExp.injective

Depends on / 依赖: R.strictAnti_sumCoeffsExp.injective, injective, strictAnti_sumCoeffsExp
-/
lemma injective_sumCoeffsExp : Function.Injective (fun (p : Real) => ∑ i, a i * (b i) ^ p) :=
    R.strictAnti_sumCoeffsExp.injective

end

variable (a b) in
/-- The exponent `p` associated with a particular Akra-Bazzi recurrence. -/
noncomputable irreducible_def p : Real := Function.invFun (fun (p : Real) => ∑ i, a i * (b i) ^ p) 1

include R in
-- Cannot be @[simp] because `T`, `g`, `r`, and `R` cannot be inferred by `simp`.
/--
lemma `sumCoeffsExp_p_eq_one` / 引理 `sumCoeffsExp_p_eq_one`

English:
lemma sumCoeffsExp_p_eq_one
  statement: ∑ i, a i * (b i) ^ p a b = 1
  proof: by
  simp only [p]
  exact Function.invFun_eq (by rw [← Set.mem_range]; exact R.one_mem_range_sumCoeffsExp)

中文:
引理 sumCoeffsExp_p_eq_one
  结论: ∑ i, a i * (b i) ^ p a b = 1
  证明: by
  simp only [p]
  exact Function.invFun_eq (by rw [← Set.mem_range]; exact R.one_mem_range_sumCoeffsExp)

Depends on / 依赖: Function, Function.invFun_eq, R.one_mem_range_sumCoeffsExp, Set.mem_range, invFun_eq, mem_range, one_mem_range_sumCoeffsExp
-/
lemma sumCoeffsExp_p_eq_one : ∑ i, a i * (b i) ^ p a b = 1 := by
  simp only [p]
  exact Function.invFun_eq (by rw [← Set.mem_range]; exact R.one_mem_range_sumCoeffsExp)

/-!
### The sum transform

This section defines the "sum transform" of a function `g` as
`∑ u ∈ Finset.Ico n₀ n, g u / u ^ (p + 1)`, and uses it to define `asympBound` as the bound
satisfied by an Akra-Bazzi recurrence, namely `n^p (1 + ∑_{u < n} g(u) / u^(p+1))`. Here, the
exponent `p` refers to the one established in the previous section.

Several properties of the sum transform are then proven.
-/

/--
Definition of `sumTransform` / `sumTransform` 的定义

English:
definition sumTransform
  signature: (p : Real) (g : Real -> Real) (n₀ n : Nat)
  body: n ^ p * ∑ u in Finset.Ico n₀ n, g u / u ^ (p + 1)

中文:
定义 sumTransform
  签名: (p : 实数) (g : 实数 -> 实数) (n₀ n : 自然数)
  定义体: n ^ p * ∑ u in Finset.Ico n₀ n, g u / u ^ (p + 1)

Depends on / 依赖: Finset, Finset.Ico
-/
noncomputable def sumTransform (p : Real) (g : Real -> Real) (n₀ n : Nat) :=
  n ^ p * ∑ u in Finset.Ico n₀ n, g u / u ^ (p + 1)

/--
lemma `sumTransform_def` / 引理 `sumTransform_def`

English:
lemma sumTransform_def
  given: {p : Real} {g : Real -> Real} {n₀ n : Nat}
  proof: rfl

中文:
引理 sumTransform_def
  条件: {p : 实数} {g : 实数 -> 实数} {n₀ n : 自然数}
  证明: rfl
-/
lemma sumTransform_def {p : Real} {g : Real -> Real} {n₀ n : Nat} :
    sumTransform p g n₀ n = n ^ p * ∑ u in Finset.Ico n₀ n, g u / u ^ (p + 1) := rfl


variable (g) (a) (b)
/--
Definition of `asympBound` / `asympBound` 的定义

English:
definition asympBound
  signature: (n : Nat)
  body: n ^ p a b + sumTransform (p a b) g 0 n

中文:
定义 asympBound
  签名: (n : 自然数)
  定义体: n ^ p a b + sumTransform (p a b) g 0 n

Depends on / 依赖: sumTransform
-/
noncomputable def asympBound (n : Nat) : Real := n ^ p a b + sumTransform (p a b) g 0 n

/--
lemma `asympBound_def` / 引理 `asympBound_def`

English:
lemma asympBound_def
  given: {α} [Fintype α] (a b : α -> Real) {n : Nat}
  proof: rfl

中文:
引理 asympBound_def
  条件: {α} [Fintype α] (a b : α -> 实数) {n : 自然数}
  证明: rfl
-/
lemma asympBound_def {α} [Fintype α] (a b : α -> Real) {n : Nat} :
    asympBound g a b n = n ^ p a b + sumTransform (p a b) g 0 n := rfl

variable {g} {a} {b}

/--
lemma `asympBound_def'` / 引理 `asympBound_def'`

English:
lemma asympBound_def'
  given: {α} [Fintype α] (a b : α -> Real) {n : Nat}
  proof: by
  simp [asympBound_def, sumTransform, mul_add, mul_one]

中文:
引理 asympBound_def'
  条件: {α} [Fintype α] (a b : α -> 实数) {n : 自然数}
  证明: by
  simp [asympBound_def, sumTransform, mul_add, mul_one]

Depends on / 依赖: asympBound_def, mul_add, mul_one, sumTransform
-/
lemma asympBound_def' {α} [Fintype α] (a b : α -> Real) {n : Nat} :
    asympBound g a b n = n ^ p a b * (1 + (∑ u in range n, g u / u ^ (p a b + 1))) := by
  simp [asympBound_def, sumTransform, mul_add, mul_one]

section
include R

/--
lemma `asympBound_pos` / 引理 `asympBound_pos`

English:
lemma asympBound_pos
  given: (n : Nat) (hn : 0 < n)
  statement: 0 < asympBound g a b n
  proof: by
  calc 0 < (n : Real) ^ p a b * (1 + 0) := by aesop (add safe Real.rpow_pos_of_pos)
       _ <= asympBound g a b n := by
        simp only [asympBound_def']
        gcongr n ^ p a b * (1 + ?_)
        have := R.g_nonneg
        aesop (add safe Real.rpow_nonneg, safe div_nonneg, safe Finset.sum_no

中文:
引理 asympBound_pos
  条件: (n : 自然数) (hn : 0 < n)
  结论: 0 < asympBound g a b n
  证明: by
  calc 0 < (n : Real) ^ p a b * (1 + 0) := by aesop (add safe Real.rpow_pos_of_pos)
       _ <= asympBound g a b n := by
        simp only [asympBound_def']
        gcongr n ^ p a b * (1 + ?_)
        have := R.g_nonneg
        aesop (add safe Real.rpow_nonneg, safe div_nonneg, safe Finset.sum_no

Depends on / 依赖: Finset, Finset.sum_nonneg, R.g_nonneg, Real.rpow_nonneg, Real.rpow_pos_of_pos, asympBound, asympBound_def, div_nonneg, g_nonneg, rpow_nonneg, rpow_pos_of_pos, sum_nonneg
-/
lemma asympBound_pos (n : Nat) (hn : 0 < n) : 0 < asympBound g a b n := by
  calc 0 < (n : Real) ^ p a b * (1 + 0) := by aesop (add safe Real.rpow_pos_of_pos)
       _ <= asympBound g a b n := by
        simp only [asympBound_def']
        gcongr n ^ p a b * (1 + ?_)
        have := R.g_nonneg
        aesop (add safe Real.rpow_nonneg, safe div_nonneg, safe Finset.sum_nonneg)

/--
lemma `eventually_asympBound_pos` / 引理 `eventually_asympBound_pos`

English:
lemma eventually_asympBound_pos
  statement: forallᶠ (n : Nat) in atTop, 0 < asympBound g a b n
  proof: by
  filter_upwards [eventually_gt_atTop 0] with n hn using R.asympBound_pos n hn

中文:
引理 eventually_asympBound_pos
  结论: 对任意ᶠ (n : 自然数) in atTop, 0 < asympBound g a b n
  证明: by
  filter_upwards [eventually_gt_atTop 0] with n hn using R.asympBound_pos n hn

Depends on / 依赖: R.asympBound_pos, asympBound_pos, eventually_gt_atTop, filter_upwards
-/
lemma eventually_asympBound_pos : forallᶠ (n : Nat) in atTop, 0 < asympBound g a b n := by
  filter_upwards [eventually_gt_atTop 0] with n hn using R.asympBound_pos n hn

/--
lemma `eventually_asympBound_r_pos` / 引理 `eventually_asympBound_r_pos`

English:
lemma eventually_asympBound_r_pos
  statement: forallᶠ (n : Nat) in atTop, forall i, 0 < asympBound g a b (r i n)
  proof: by
  rw [Filter.eventually_all]
  exact fun i => (R.tendsto_atTop_r i).eventually R.eventually_asympBound_pos

中文:
引理 eventually_asympBound_r_pos
  结论: 对任意ᶠ (n : 自然数) in atTop, 对任意 i, 0 < asympBound g a b (r i n)
  证明: by
  rw [Filter.eventually_all]
  exact fun i => (R.tendsto_atTop_r i).eventually R.eventually_asympBound_pos

Depends on / 依赖: Filter, Filter.eventually_all, R.eventually_asympBound_pos, R.tendsto_atTop_r, eventually, eventually_all, eventually_asympBound_pos, tendsto_atTop_r
-/
lemma eventually_asympBound_r_pos : forallᶠ (n : Nat) in atTop, forall i, 0 < asympBound g a b (r i n) := by
  rw [Filter.eventually_all]
  exact fun i => (R.tendsto_atTop_r i).eventually R.eventually_asympBound_pos

/--
lemma `eventually_atTop_sumTransform_le` / 引理 `eventually_atTop_sumTransform_le`

English:
lemma eventually_atTop_sumTransform_le
  proof: by
  obtain ⟨c₁, hc₁_mem, hc₁⟩ := R.exists_eventually_const_mul_le_r
  obtain ⟨c₂, hc₂_mem, hc₂⟩ := R.g_grows_poly.eventually_atTop_le_nat hc₁_mem
  have hc₁_pos : 0 < c₁ := hc₁_mem.1
  refine ⟨max c₂ (c₂ / c₁ ^ (p a b + 1)), by positivity, ?_⟩
  filter_upwards [hc₁, hc₂, R.eventually_r_pos, R.event

中文:
引理 eventually_atTop_sumTransform_le
  证明: by
  obtain ⟨c₁, hc₁_mem, hc₁⟩ := R.exists_eventually_const_mul_le_r
  obtain ⟨c₂, hc₂_mem, hc₂⟩ := R.g_grows_poly.eventually_atTop_le_nat hc₁_mem
  have hc₁_pos : 0 < c₁ := hc₁_mem.1
  refine ⟨max c₂ (c₂ / c₁ ^ (p a b + 1)), by positivity, ?_⟩
  filter_upwards [hc₁, hc₂, R.eventually_r_pos, R.event

Depends on / 依赖: R.eventually_r_lt_n, R.eventually_r_pos, R.exists_eventually_const_mul_le_r, R.g_grows_poly.eventually_atTop_le_nat, R.g_nonneg, eventually_atTop_le_nat, eventually_gt_atTop, eventually_r_lt_n, eventually_r_pos, exists_eventually_const_mul_le_r, filter_upwards, g_grows_poly, g_nonneg, hn_pos, hr_lt_n, hrpos_i, le_or_gt
-/
lemma eventually_atTop_sumTransform_le :
    exists c > 0, forallᶠ (n : Nat) in atTop, forall i, sumTransform (p a b) g (r i n) n <= c * g n := by
  obtain ⟨c₁, hc₁_mem, hc₁⟩ := R.exists_eventually_const_mul_le_r
  obtain ⟨c₂, hc₂_mem, hc₂⟩ := R.g_grows_poly.eventually_atTop_le_nat hc₁_mem
  have hc₁_pos : 0 < c₁ := hc₁_mem.1
  refine ⟨max c₂ (c₂ / c₁ ^ (p a b + 1)), by positivity, ?_⟩
  filter_upwards [hc₁, hc₂, R.eventually_r_pos, R.eventually_r_lt_n, eventually_gt_atTop 0]
    with n hn₁ hn₂ hrpos hr_lt_n hn_pos i
  have hrpos_i := hrpos i
  have g_nonneg : 0 <= g n := R.g_nonneg n (by positivity)
  cases le_or_gt 0 (p a b + 1) with
  | inl hp => -- 0 ≤ p a b + 1
    calc sumTransform (p a b) g (r i n) n
           = n ^ (p a b) * (∑ u in Finset.Ico (r i n) n, g u / u ^ ((p a b) + 1)) := by rfl
         _ <= n ^ (p a b) * (∑ u in Finset.Ico (r i n) n, c₂ * g n / u ^ ((p a b) + 1)) := by
          gcongr with u hu
          rw [Finset.mem_Ico] at hu
          have hu' : u in Set.Icc (r i n) n := ⟨hu.1, by lia⟩
          refine hn₂ u ?_
          rw [Set.mem_Icc]
          refine ⟨?_, by norm_cast; lia⟩
          calc c₁ * n <= r i n := by exact hn₁ i
                    _ <= u := by exact_mod_cast hu'.1
         _ <= n ^ (p a b) * (∑ _u in Finset.Ico (r i n) n, c₂ * g n / (r i n) ^ ((p a b) + 1)) := by
          gcongr with u hu; rw [Finset.mem_Ico] at hu; exact hu.1
         _ <= n ^ p a b * #(Ico (r i n) n) • (c₂ * g n / r i n ^ (p a b + 1)) := by
          gcongr; exact Finset.sum_le_card_nsmul _ _ _ (fun x _ => by rfl)
         _ = n ^ p a b * #(Ico (r i n) n) * (c₂ * g n / r i n ^ (p a b + 1)) := by
          rw [nsmul_eq_mul]; rw [mul_assoc]
         _ = n ^ (p a b) * (n - r i n) * (c₂ * g n / (r i n) ^ ((p a b) + 1)) := by
          congr; rw [Nat.card_Ico, Nat.cast_sub (le_of_lt <| hr_lt_n i)]
         _ <= n ^ (p a b) * n * (c₂ * g n / (r i n) ^ ((p a b) + 1)) := by
          gcongr; simp only [tsub_le_iff_right, le_add_iff_nonneg_right, Nat.cast_nonneg]
         _ <= n ^ (p a b) * n * (c₂ * g n / (c₁ * n) ^ ((p a b) + 1)) := by
          gcongr; exact hn₁ i
         _ = c₂ * g n * n ^ ((p a b) + 1) / (c₁ * n) ^ ((p a b) + 1) := by
          rw [← Real.rpow_add_one (by positivity) (p a b)]; ring
         _ = c₂ * g n * n ^ ((p a b) + 1) / (n ^ ((p a b) + 1) * c₁ ^ ((p a b) + 1)) := by
          rw [mul_comm c₁]; rw [Real.mul_rpow (by positivity) (by positivity)]
         _ = c₂ * g n * (n ^ ((p a b) + 1) / (n ^ ((p a b) + 1))) / c₁ ^ ((p a b) + 1) := by ring
         _ = c₂ * g n / c₁ ^ ((p a b) + 1) := by rw [div_self (by positivity), mul_one]
         _ = (c₂ / c₁ ^ ((p a b) + 1)) * g n := by ring
         _ <= max c₂ (c₂ / c₁ ^ ((p a b) + 1)) * g n := by gcongr; exact le_max_right _ _
  | inr hp => -- p a b + 1 < 0
    calc sumTransform (p a b) g (r i n) n
      _ = n ^ (p a b) * (∑ u in Finset.Ico (r i n) n, g u / u ^ ((p a b) + 1)) := by rfl
      _ <= n ^ (p a b) * (∑ u in Finset.Ico (r i n) n, c₂ * g n / u ^ ((p a b) + 1)) := by
        gcongr with u hu
        rw [Finset.mem_Ico] at hu
        have hu' : u in Set.Icc (r i n) n := ⟨hu.1, by lia⟩
        refine hn₂ u ?_
        rw [Set.mem_Icc]
        refine ⟨?_, by norm_cast; lia⟩
        calc c₁ * n <= r i n := by exact hn₁ i
                  _ <= u := by exact_mod_cast hu'.1
      _ <= n ^ (p a b) * (∑ _u in Finset.Ico (r i n) n, c₂ * g n / n ^ ((p a b) + 1)) := by
        gcongr n ^ (p a b) * (Finset.Ico (r i n) n).sum (fun _ => c₂ * g n / ?_) with u hu
        rw [Finset.mem_Ico] at hu
        have : 0 < u := calc
          0 < r i n := by exact hrpos_i
          _ <= u := by exact hu.1
        exact rpow_le_rpow_of_nonpos (by positivity)
          (by exact_mod_cast (le_of_lt hu.2)) (le_of_lt hp)
      _ <= n ^ p a b * #(Ico (r i n) n) • (c₂ * g n / n ^ (p a b + 1)) := by
        gcongr; exact Finset.sum_le_card_nsmul _ _ _ (fun x _ => by rfl)
      _ = n ^ p a b * #(Ico (r i n) n) * (c₂ * g n / n ^ (p a b + 1)) := by
        rw [nsmul_eq_mul]; rw [mul_assoc]
      _ = n ^ (p a b) * (n - r i n) * (c₂ * g n / n ^ ((p a b) + 1)) := by
        congr; rw [Nat.card_Ico, Nat.cast_sub (le_of_lt <| hr_lt_n i)]
      _ <= n ^ (p a b) * n * (c₂ * g n / n ^ ((p a b) + 1)) := by
        gcongr; simp only [tsub_le_iff_right, le_add_iff_nonneg_right, Nat.cast_nonneg]
      _ = c₂ * (n ^ ((p a b) + 1) / n ^ ((p a b) + 1)) * g n := by
        rw [← Real.rpow_add_one (by positivity) (p a b)]; ring
      _ = c₂ * g n := by rw [div_self (by positivity), mul_one]
      _ <= max c₂ (c₂ / c₁ ^ ((p a b) + 1)) * g n := by gcongr; exact le_max_left _ _

/--
lemma `eventually_atTop_sumTransform_ge` / 引理 `eventually_atTop_sumTransform_ge`

English:
lemma eventually_atTop_sumTransform_ge
  proof: by
  obtain ⟨c₁, hc₁_mem, hc₁⟩ := R.exists_eventually_const_mul_le_r
  obtain ⟨c₂, hc₂_mem, hc₂⟩ := R.g_grows_poly.eventually_atTop_ge_nat hc₁_mem
  obtain ⟨c₃, hc₃_mem, hc₃⟩ := R.exists_eventually_r_le_const_mul
  have hc₁_pos : 0 < c₁ := hc₁_mem.1
  have hc₃' : 0 < (1 - c₃) := by have := hc₃_mem.2

中文:
引理 eventually_atTop_sumTransform_ge
  证明: by
  obtain ⟨c₁, hc₁_mem, hc₁⟩ := R.exists_eventually_const_mul_le_r
  obtain ⟨c₂, hc₂_mem, hc₂⟩ := R.g_grows_poly.eventually_atTop_ge_nat hc₁_mem
  obtain ⟨c₃, hc₃_mem, hc₃⟩ := R.exists_eventually_r_le_const_mul
  have hc₁_pos : 0 < c₁ := hc₁_mem.1
  have hc₃' : 0 < (1 - c₃) := by have := hc₃_mem.2

Depends on / 依赖: R.eventually_r_lt_n, R.eventually_r_pos, R.exists_eventually_const_mul_le_r, R.exists_eventually_r_le_const_mul, R.g_grows_poly.eventually_atTop_ge_nat, eventually_atTop_ge_nat, eventually_gt_atTop, eventually_r_lt_n, eventually_r_pos, exists_eventually_const_mul_le_r, exists_eventually_r_le_const_mul, filter_upwards, g_grows_poly
-/
lemma eventually_atTop_sumTransform_ge :
    exists c > 0, forallᶠ (n : Nat) in atTop, forall i, c * g n <= sumTransform (p a b) g (r i n) n := by
  obtain ⟨c₁, hc₁_mem, hc₁⟩ := R.exists_eventually_const_mul_le_r
  obtain ⟨c₂, hc₂_mem, hc₂⟩ := R.g_grows_poly.eventually_atTop_ge_nat hc₁_mem
  obtain ⟨c₃, hc₃_mem, hc₃⟩ := R.exists_eventually_r_le_const_mul
  have hc₁_pos : 0 < c₁ := hc₁_mem.1
  have hc₃' : 0 < (1 - c₃) := by have := hc₃_mem.2; linarith
  refine ⟨min (c₂ * (1 - c₃)) ((1 - c₃) * c₂ / c₁^((p a b) + 1)), by positivity, ?_⟩
  filter_upwards [hc₁, hc₂, hc₃, R.eventually_r_pos, R.eventually_r_lt_n, eventually_gt_atTop 0]
    with n hn₁ hn₂ hn₃ hrpos hr_lt_n hn_pos
  intro i
  have hrpos_i := hrpos i
  have g_nonneg : 0 <= g n := R.g_nonneg n (by positivity)
  cases le_or_gt 0 (p a b + 1) with
  | inl hp => -- 0 ≤ (p a b) + 1
    calc sumTransform (p a b) g (r i n) n
      _ = n ^ (p a b) * (∑ u in Finset.Ico (r i n) n, g u / u ^ ((p a b) + 1)) := rfl
      _ >= n ^ (p a b) * (∑ u in Finset.Ico (r i n) n, c₂ * g n / u ^ ((p a b) + 1)) := by
        gcongr with u hu
        rw [Finset.mem_Ico] at hu
        have hu' : u in Set.Icc (r i n) n := ⟨hu.1, by lia⟩
        refine hn₂ u ?_
        rw [Set.mem_Icc]
        refine ⟨?_, by norm_cast; lia⟩
        calc c₁ * n <= r i n := by exact hn₁ i
                  _ <= u := by exact_mod_cast hu'.1
      _ >= n ^ (p a b) * (∑ _u in Finset.Ico (r i n) n, c₂ * g n / n ^ ((p a b) + 1)) := by
        gcongr with u hu
        · rw [Finset.mem_Ico] at hu
          have := calc 0 < r i n := hrpos_i
                      _ <= u := hu.1
          positivity
        · rw [Finset.mem_Ico] at hu
          exact le_of_lt hu.2
      _ >= n ^ p a b * #(Ico (r i n) n) • (c₂ * g n / n ^ (p a b + 1)) := by
        gcongr; exact Finset.card_nsmul_le_sum _ _ _ (fun x _ => by rfl)
      _ = n ^ p a b * #(Ico (r i n) n) * (c₂ * g n / n ^ (p a b + 1)) := by
        rw [nsmul_eq_mul]; rw [mul_assoc]
      _ = n ^ (p a b) * (n - r i n) * (c₂ * g n / n ^ ((p a b) + 1)) := by
        congr; rw [Nat.card_Ico, Nat.cast_sub (le_of_lt <| hr_lt_n i)]
      _ >= n ^ (p a b) * (n - c₃ * n) * (c₂ * g n / n ^ ((p a b) + 1)) := by
        gcongr; exact hn₃ i
      _ = n ^ (p a b) * n * (1 - c₃) * (c₂ * g n / n ^ ((p a b) + 1)) := by ring
      _ = c₂ * (1 - c₃) * g n * (n ^ ((p a b) + 1) / n ^ ((p a b) + 1)) := by
        rw [← Real.rpow_add_one (by positivity) (p a b)]; ring
      _ = c₂ * (1 - c₃) * g n := by rw [div_self (by positivity), mul_one]
      _ >= min (c₂ * (1 - c₃)) ((1 - c₃) * c₂ / c₁ ^ ((p a b) + 1)) * g n := by
        gcongr; exact min_le_left _ _
  | inr hp => -- (p a b) + 1 < 0
    calc sumTransform (p a b) g (r i n) n
        = n ^ (p a b) * (∑ u in Finset.Ico (r i n) n, g u / u ^ ((p a b) + 1)) := by rfl
      _ >= n ^ (p a b) * (∑ u in Finset.Ico (r i n) n, c₂ * g n / u ^ ((p a b) + 1)) := by
        gcongr with u hu
        rw [Finset.mem_Ico] at hu
        have hu' : u in Set.Icc (r i n) n := ⟨hu.1, by lia⟩
        refine hn₂ u ?_
        rw [Set.mem_Icc]
        refine ⟨?_, by norm_cast; lia⟩
        calc c₁ * n <= r i n := by exact hn₁ i
                  _ <= u := by exact_mod_cast hu'.1
      _ >= n ^ (p a b) * (∑ _u in Finset.Ico (r i n) n, c₂ * g n / (r i n) ^ ((p a b) + 1)) := by
        gcongr n ^ (p a b) * (Finset.Ico (r i n) n).sum (fun _ => c₂ * g n / ?_) with u hu
        · rw [Finset.mem_Ico] at hu
          have := calc 0 < r i n := hrpos_i
                      _ <= u := hu.1
          positivity
        · rw [Finset.mem_Ico] at hu
          exact rpow_le_rpow_of_nonpos (by positivity)
            (by exact_mod_cast hu.1) (le_of_lt hp)
      _ >= n ^ p a b * #(Ico (r i n) n) • (c₂ * g n / r i n ^ (p a b + 1)) := by
          gcongr; exact Finset.card_nsmul_le_sum _ _ _ (fun x _ => by rfl)
      _ = n ^ p a b * #(Ico (r i n) n) * (c₂ * g n / r i n ^ (p a b + 1)) := by
          rw [nsmul_eq_mul]; rw [mul_assoc]
      _ >= n ^ p a b * #(Ico (r i n) n) * (c₂ * g n / (c₁ * n) ^ (p a b + 1)) := by
          gcongr n ^ p a b * #(Ico (r i n) n) * (c₂ * g n / ?_)
          exact rpow_le_rpow_of_nonpos (by positivity) (hn₁ i) (le_of_lt hp)
      _ = n ^ (p a b) * (n - r i n) * (c₂ * g n / (c₁ * n) ^ ((p a b) + 1)) := by
          congr; rw [Nat.card_Ico, Nat.cast_sub (le_of_lt <| hr_lt_n i)]
      _ >= n ^ (p a b) * (n - c₃ * n) * (c₂ * g n / (c₁ * n) ^ ((p a b) + 1)) := by
          gcongr; exact hn₃ i
      _ = n ^ (p a b) * n * (1 - c₃) * (c₂ * g n / (c₁ * n) ^ ((p a b) + 1)) := by ring
      _ = n ^ (p a b) * n * (1 - c₃) * (c₂ * g n / (c₁ ^ ((p a b) + 1) * n ^ ((p a b) + 1))) := by
          rw [Real.mul_rpow (by positivity) (by positivity)]
      _ = (n ^ ((p a b) + 1) / n ^ ((p a b) + 1)) * (1 - c₃) * c₂ * g n / c₁ ^ ((p a b) + 1) := by
          rw [← Real.rpow_add_one (by positivity) (p a b)]; ring
      _ = (1 - c₃) * c₂ / c₁ ^ ((p a b) + 1) * g n := by
          rw [div_self (by positivity)]; rw [one_mul]; ring
      _ >= min (c₂ * (1 - c₃)) ((1 - c₃) * c₂ / c₁ ^ ((p a b) + 1)) * g n := by
          gcongr; exact min_le_right _ _

end

end AkraBazziRecurrence
