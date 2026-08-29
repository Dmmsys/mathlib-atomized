/-
Copyright (c) 2025 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuval Filmus
-/
module

public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Tactic.Positivity

/-!
# Chebyshev polynomials over the reals: some extremal properties

* Chebyshev polynomials have largest leading coefficient,
following proof in https://math.stackexchange.com/a/978145/1277
* Chebyshev polynomials maximize iterated derivatives at 1 and beyond

## Main statements

* leadingCoeff_le_of_forall_abs_le_one: If `P` is a real polynomial of degree at most `n` and
  `|P (x)| ≤ 1` for all `x ∈ [-1, 1]` then the leading coefficient of `P` is at most `2 ^ (n - 1)`
* leadingCoeff_eq_iff_of_forall_abs_le_one: When `n ≥ 2`, equality holds iff `P = T_n`
* eval_iterate_derivative_le_of_forall_abs_le_one: If `P` is a real polynomial of degree at most `n`
  and `|P (x)| ≤ 1` for all `x ∈ [-1, 1]` then for all `x ≥ 1`, `P ^ (k) (x) ≤ T_n ^ (k)(x)`
* eval_iterate_derivative_eq_iff_of_forall_abs_le_one: If `0 < k ≤ n` then equality holds iff
  `P = T_n`

## Implementation

We describe the proof for the leading coefficient; the proof for iterated derivatives uses a
similar approach.

By monotonicity of `2 ^ (n - 1)`, we can assume that `P` has degree exactly `n`.
Using Lagrange interpolation, we can give a formula for the leading coefficient of `P`
as a linear combination of the values of `P` on the Chebyshev nodes (sumNodes_eq_coeff).
The Chebyshev polynomial `T_n` has value `±1` on the nodes, with the same signs as the
coefficients of the linear combination (negOnePow_mul_leadingCoeffC_pos).
Since `|P (x)| ≤ 1` on the nodes, this implies that the leading coefficient of `P` is bounded
by that of `T_n`, which is known to equal `2 ^ (n - 1)`.
Moreover, equality holds iff `P` and `T_n` agree on the nodes, which implies that they coincide.
-/
@[expose] public section
namespace Polynomial.Chebyshev

open Polynomial Real

/--
Definition of `node` / `node` 的定义

English:
definition node
  signature: (n i : Nat)
  body: cos (i * π / n)

中文:
定义 node
  签名: (n i : 自然数)
  定义体: cos (i * π / n)
-/
noncomputable def node (n i : Nat) : Real := cos (i * π / n)

/--
lemma `node_eq_one` / 引理 `node_eq_one`

English:
lemma node_eq_one
  given: {n : Nat}
  statement: node n 0 = 1
  proof: by simp [node]

中文:
引理 node_eq_one
  条件: {n : 自然数}
  结论: node n 0 = 1
  证明: by simp [node]
-/
lemma node_eq_one {n : Nat} : node n 0 = 1 := by simp [node]

/--
lemma `node_eq_neg_one` / 引理 `node_eq_neg_one`

English:
lemma node_eq_neg_one
  given: {n : Nat} (hn : n != 0)
  statement: node n n = -1
  proof: by
  have : n * π / n = π := by aesop
  simp [node, this]

中文:
引理 node_eq_neg_one
  条件: {n : 自然数} (hn : n != 0)
  结论: node n n = -1
  证明: by
  have : n * π / n = π := by aesop
  simp [node, this]
-/
lemma node_eq_neg_one {n : Nat} (hn : n != 0) : node n n = -1 := by
  have : n * π / n = π := by aesop
  simp [node, this]

/--
lemma `node_mem_Icc` / 引理 `node_mem_Icc`

English:
lemma node_mem_Icc
  given: {n i : Nat}
  statement: node n i in Set.Icc (-1) 1
  proof: Set.mem_Icc.mpr ⟨neg_one_le_cos _, cos_le_one _⟩

中文:
引理 node_mem_Icc
  条件: {n i : 自然数}
  结论: node n i in 集合.闭区间 (-1) 1
  证明: Set.mem_Icc.mpr ⟨neg_one_le_cos _, cos_le_one _⟩

Depends on / 依赖: Set.mem_Icc.mpr, cos_le_one, mem_Icc, neg_one_le_cos
-/
lemma node_mem_Icc {n i : Nat} : node n i in Set.Icc (-1) 1 :=
  Set.mem_Icc.mpr ⟨neg_one_le_cos _, cos_le_one _⟩

/--
lemma `eval_T_real_node` / 引理 `eval_T_real_node`

English:
lemma eval_T_real_node
  given: {n i : Nat} (hi : i in Finset.Iic n)
  proof: by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [show i = 0 by grind]
  have : (n : Int) * (i * π / n) = i * π := by norm_cast; field
  rw [node]; rw [T_real_cos]; rw [this]; rw [cos_nat_mul_pi]

中文:
引理 eval_T_real_node
  条件: {n i : 自然数} (hi : i in 有限集.左无界右闭区间 n)
  证明: by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [show i = 0 by grind]
  have : (n : Int) * (i * π / n) = i * π := by norm_cast; field
  rw [node]; rw [T_real_cos]; rw [this]; rw [cos_nat_mul_pi]

Depends on / 依赖: T_real_cos, cos_nat_mul_pi, eq_or_ne
-/
lemma eval_T_real_node {n i : Nat} (hi : i in Finset.Iic n) :
    (T Real n).eval (node n i) = (-1) ^ i := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [show i = 0 by grind]
  have : (n : Int) * (i * π / n) = i * π := by norm_cast; field
  rw [node]; rw [T_real_cos]; rw [this]; rw [cos_nat_mul_pi]

/--
lemma `strictAntiOn_node` / 引理 `strictAntiOn_node`

English:
lemma strictAntiOn_node
  given: (n : Nat)
  proof: by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  refine strictAntiOn_cos.comp_strictMonoOn ?_ (fun x hx => Set.mem_Icc.mpr ⟨by positivity, ?_⟩)
  · apply StrictMono.strictMonoOn
    exact StrictMono.mul_const
      (StrictMono.mul_const Nat.strictMono_cast (by positivity)) (by positivity)
  rw [Finset.mem_coe]; rw [Finset.mem_range_succ_iff] at hx
  rw [mul_div_assoc]
  nth_rewrite 2 [← mul_div_cancel₀ π (Nat.cast_ne_zero.mpr hn)]
  gcongr

中文:
引理 strictAntiOn_node
  条件: (n : 自然数)
  证明: by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  refine strictAntiOn_cos.comp_strictMonoOn ?_ (fun x hx => Set.mem_Icc.mpr ⟨by positivity, ?_⟩)
  · apply StrictMono.strictMonoOn
    exact StrictMono.mul_const
      (StrictMono.mul_const Nat.strictMono_cast (by positivity)) (by positivity)
  rw [Finset.mem_coe]; rw [Finset.mem_range_succ_iff] at hx
  rw [mul_div_assoc]
  nth_rewrite 2 [← mul_div_cancel₀ π (Nat.cast_ne_zero.mpr hn)]
  gcongr

Depends on / 依赖: Finset, Finset.mem_coe, Finset.mem_range_succ_iff, Nat.cast_ne_zero.mpr, Nat.strictMono_cast, Set.mem_Icc.mpr, StrictMono, StrictMono.mul_const, StrictMono.strictMonoOn, cast_ne_zero, comp_strictMonoOn, eq_or_ne, mem_Icc, mem_coe, mem_range_succ_iff, mul_const, mul_div_assoc, nth_rewrite, strictAntiOn_cos, strictAntiOn_cos.comp_strictMonoOn
-/
lemma strictAntiOn_node (n : Nat) :
    StrictAntiOn (node n ·) (Finset.range (n + 1)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  refine strictAntiOn_cos.comp_strictMonoOn ?_ (fun x hx => Set.mem_Icc.mpr ⟨by positivity, ?_⟩)
  · apply StrictMono.strictMonoOn
    exact StrictMono.mul_const
      (StrictMono.mul_const Nat.strictMono_cast (by positivity)) (by positivity)
  rw [Finset.mem_coe]; rw [Finset.mem_range_succ_iff] at hx
  rw [mul_div_assoc]
  nth_rewrite 2 [← mul_div_cancel₀ π (Nat.cast_ne_zero.mpr hn)]
  gcongr

/--
lemma `node_lt` / 引理 `node_lt`

English:
lemma node_lt
  given: {n i j : Nat} (hj : j <= n) (hij : i < j)
  proof: strictAntiOn_node n (Finset.mem_coe.mpr (Finset.mem_range_succ_iff.mpr (by grind)))
    (Finset.mem_coe.mpr (Finset.mem_range_succ_iff.mpr hj)) hij

中文:
引理 node_lt
  条件: {n i j : 自然数} (hj : j <= n) (hij : i < j)
  证明: strictAntiOn_node n (Finset.mem_coe.mpr (Finset.mem_range_succ_iff.mpr (by grind)))
    (Finset.mem_coe.mpr (Finset.mem_range_succ_iff.mpr hj)) hij

Depends on / 依赖: Finset, Finset.mem_coe.mpr, Finset.mem_range_succ_iff.mpr, mem_coe, mem_range_succ_iff, strictAntiOn_node
-/
lemma node_lt {n i j : Nat} (hj : j <= n) (hij : i < j) :
    node n j < node n i :=
  strictAntiOn_node n (Finset.mem_coe.mpr (Finset.mem_range_succ_iff.mpr (by grind)))
    (Finset.mem_coe.mpr (Finset.mem_range_succ_iff.mpr hj)) hij

/--
lemma `zero_lt_prod_node_sub_node` / 引理 `zero_lt_prod_node_sub_node`

English:
lemma zero_lt_prod_node_sub_node
  given: {n i : Nat} (hi : i <= n)
  proof: by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Nat.le_zero.mp hi]
  have h₁ : 0 < ∏ j in Finset.range i, ((-1) * (node n i - node n j)) :=
    Finset.prod_pos (fun j hj => mul_pos_of_neg_of_neg neg_one_lt_zero <| sub_neg.mpr <|
    node_lt hi (Finset.mem_range.mp hj))
  rw [Finset.prod_mul_distrib]; rw [Finset.prod_const]; rw [Finset.card_range] at h₁
  have h₂ : 0 < ∏ j in Finset.Ioc i n, (node n i - node n j) :=
    Finset.prod_pos (fun j hj => sub_pos.mpr <|
      node_lt (Finset.mem_Ioc.mp hj).2 (Finset.mem_Ioc.mp hj).1)
  have union : (Finset.range (n + 1)).erase i = (Finset.range i) union Finset.Ioc i n := by grind
  have disjoint : Disjoint (Finset.range i) (Finset.Ioc i n) := by grind [Finset.disjoint_iff_ne]
  rw [union]; rw [Finset.prod_union disjoint]; rw [← mul_assoc]
  exact mul_pos h₁ h₂

中文:
引理 zero_lt_prod_node_sub_node
  条件: {n i : 自然数} (hi : i <= n)
  证明: by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Nat.le_zero.mp hi]
  have h₁ : 0 < ∏ j in Finset.range i, ((-1) * (node n i - node n j)) :=
    Finset.prod_pos (fun j hj => mul_pos_of_neg_of_neg neg_one_lt_zero <| sub_neg.mpr <|
    node_lt hi (Finset.mem_range.mp hj))
  rw [Finset.prod_mul_distrib]; rw [Finset.prod_const]; rw [Finset.card_range] at h₁
  have h₂ : 0 < ∏ j in Finset.Ioc i n, (node n i - node n j) :=
    Finset.prod_pos (fun j hj => sub_pos.mpr <|
      node_lt (Finset.mem_Ioc.mp hj).2 (Finset.mem_Ioc.mp hj).1)
  have union : (Finset.range (n + 1)).erase i = (Finset.range i) union Finset.Ioc i n := by grind
  have disjoint : Disjoint (Finset.range i) (Finset.Ioc i n) := by grind [Finset.disjoint_iff_ne]
  rw [union]; rw [Finset.prod_union disjoint]; rw [← mul_assoc]
  exact mul_pos h₁ h₂

Depends on / 依赖: Finset, Finset.Ioc, Finset.card_range, Finset.mem_Ioc.mp, Finset.mem_range.mp, Finset.prod_const, Finset.prod_mul_distrib, Finset.prod_pos, Finset.range, Nat.le_zero.mp, card_range, eq_or_ne, le_zero, mem_Ioc, mem_range, mul_pos_of_neg_of_neg, neg_one_lt_zero, node_lt, prod_const, prod_mul_distrib
-/
lemma zero_lt_prod_node_sub_node {n i : Nat} (hi : i <= n) :
    0 < (-1) ^ i * ∏ j in (Finset.range (n + 1)).erase i, (node n i - node n j) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Nat.le_zero.mp hi]
  have h₁ : 0 < ∏ j in Finset.range i, ((-1) * (node n i - node n j)) :=
    Finset.prod_pos (fun j hj => mul_pos_of_neg_of_neg neg_one_lt_zero <| sub_neg.mpr <|
    node_lt hi (Finset.mem_range.mp hj))
  rw [Finset.prod_mul_distrib]; rw [Finset.prod_const]; rw [Finset.card_range] at h₁
  have h₂ : 0 < ∏ j in Finset.Ioc i n, (node n i - node n j) :=
    Finset.prod_pos (fun j hj => sub_pos.mpr <|
      node_lt (Finset.mem_Ioc.mp hj).2 (Finset.mem_Ioc.mp hj).1)
  have union : (Finset.range (n + 1)).erase i = (Finset.range i) union Finset.Ioc i n := by grind
  have disjoint : Disjoint (Finset.range i) (Finset.Ioc i n) := by grind [Finset.disjoint_iff_ne]
  rw [union]; rw [Finset.prod_union disjoint]; rw [← mul_assoc]
  exact mul_pos h₁ h₂

/--
lemma `negOnePow_mul_le` / 引理 `negOnePow_mul_le`

English:
lemma negOnePow_mul_le
  given: {α : Real} {i : Nat} (hα : |α| <= 1)
  statement: (-1) ^ i * α <= 1
  proof: by
  apply le_of_abs_le
  rwa [abs_mul, abs_neg_one_pow, one_mul]

中文:
引理 negOnePow_mul_le
  条件: {α : 实数} {i : 自然数} (hα : |α| <= 1)
  结论: (-1) ^ i * α <= 1
  证明: by
  apply le_of_abs_le
  rwa [abs_mul, abs_neg_one_pow, one_mul]
-/
private lemma negOnePow_mul_le {α : Real} {i : Nat} (hα : |α| <= 1) : (-1) ^ i * α <= 1 := by
  apply le_of_abs_le
  rwa [abs_mul, abs_neg_one_pow, one_mul]

/--
lemma `negOnePow_mul_negOnePow_mul_cancel` / 引理 `negOnePow_mul_negOnePow_mul_cancel`

English:
lemma negOnePow_mul_negOnePow_mul_cancel
  given: {α β : Real} {i : Nat}
  proof: calc
  _ = ((-1) ^ i * (-1) ^ i) * α * β := by ring
  _ = α * β := by simp [← mul_pow]

中文:
引理 negOnePow_mul_negOnePow_mul_cancel
  条件: {α β : 实数} {i : 自然数}
  证明: calc
  _ = ((-1) ^ i * (-1) ^ i) * α * β := by ring
  _ = α * β := by simp [← mul_pow]
-/
private lemma negOnePow_mul_negOnePow_mul_cancel {α β : Real} {i : Nat} :
    ((-1) ^ i * α) * ((-1) ^ i * β) = α * β := calc
  _ = ((-1) ^ i * (-1) ^ i) * α * β := by ring
  _ = α * β := by simp [← mul_pow]

/--
Definition of `sumNodes` / `sumNodes` 的定义

English:
definition sumNodes
  signature: (n : Nat) (c : Nat -> Real) (P : Real[X])
  body: ∑ i <= n, P.eval (node n i) * (c i)

中文:
定义 sumNodes
  签名: (n : 自然数) (c : 自然数 -> 实数) (P : 实数[X])
  定义体: ∑ i <= n, P.eval (node n i) * (c i)

Depends on / 依赖: P.eval
-/
noncomputable def sumNodes (n : Nat) (c : Nat -> Real) (P : Real[X]) := ∑ i <= n, P.eval (node n i) * (c i)

/--
theorem `sumNodes_le_sumNodes_T` / 定理 `sumNodes_le_sumNodes_T`

English:
theorem sumNodes_le_sumNodes_T
  statement: {n : Nat} {c : Nat -> Real}
  proof: by
  rw [sumNodes]; rw [sumNodes]
  refine Finset.sum_le_sum (fun i hi => ?_)
  calc
    P.eval (node n i) * (c i) =
      ((-1) ^ i * P.eval (node n i)) * ((-1) ^ i * (c i)) :=
      negOnePow_mul_negOnePow_mul_cancel.symm
    _ <= 1 * ((-1) ^ i * (c i)) := by
      gcongr
      · exact (hcnonneg i (Finset.mem_Iic.mp hi))
      · exact (negOnePow_mul_le (hPbnd _ node_mem_Icc))
    _ = (T Real n).eval (node n i) * (c i) := by
      rw [eval_T_real_node hi]; rw [one_mul]

中文:
定理 sumNodes_le_sumNodes_T
  结论: {n : 自然数} {c : 自然数 -> 实数}
  证明: by
  rw [sumNodes]; rw [sumNodes]
  refine Finset.sum_le_sum (fun i hi => ?_)
  calc
    P.eval (node n i) * (c i) =
      ((-1) ^ i * P.eval (node n i)) * ((-1) ^ i * (c i)) :=
      negOnePow_mul_negOnePow_mul_cancel.symm
    _ <= 1 * ((-1) ^ i * (c i)) := by
      gcongr
      · exact (hcnonneg i (Finset.mem_Iic.mp hi))
      · exact (negOnePow_mul_le (hPbnd _ node_mem_Icc))
    _ = (T Real n).eval (node n i) * (c i) := by
      rw [eval_T_real_node hi]; rw [one_mul]

Depends on / 依赖: Finset, Finset.mem_Iic.mp, Finset.sum_le_sum, P.eval, eval_T_real_node, hcnonneg, mem_Iic, negOnePow_mul_le, negOnePow_mul_negOnePow_mul_cancel, negOnePow_mul_negOnePow_mul_cancel.symm, node_mem_Icc, one_mul, sumNodes, sum_le_sum
-/
theorem sumNodes_le_sumNodes_T {n : Nat} {c : Nat -> Real}
    (hcnonneg : forall i <= n, 0 <= (-1) ^ i * (c i))
    {P : Real[X]} (hPbnd : forall x in Set.Icc (-1) 1, |P.eval x| <= 1) :
    sumNodes n c P <= sumNodes n c (T Real n) := by
  rw [sumNodes]; rw [sumNodes]
  refine Finset.sum_le_sum (fun i hi => ?_)
  calc
    P.eval (node n i) * (c i) =
      ((-1) ^ i * P.eval (node n i)) * ((-1) ^ i * (c i)) :=
      negOnePow_mul_negOnePow_mul_cancel.symm
    _ <= 1 * ((-1) ^ i * (c i)) := by
      gcongr
      · exact (hcnonneg i (Finset.mem_Iic.mp hi))
      · exact (negOnePow_mul_le (hPbnd _ node_mem_Icc))
    _ = (T Real n).eval (node n i) * (c i) := by
      rw [eval_T_real_node hi]; rw [one_mul]

/--
theorem `sumNodes_eq_sumNodes_T_iff` / 定理 `sumNodes_eq_sumNodes_T_iff`

English:
theorem sumNodes_eq_sumNodes_T_iff
  statement: {n : Nat} {c : Nat -> Real}
  proof: by
  refine ⟨fun h => ?_, by intro h; rw [h]⟩
  rw [sumNodes]; rw [sumNodes] at h
  apply eq_of_degrees_lt_of_eval_finset_eq ((Finset.range (n + 1)).image (node n ·))
  · apply lt_of_le_of_lt hPdeg
    rw [Nat.cast_lt]; rw [Finset.card_image_of_injOn (strictAntiOn_node n).injOn]; rw [Finset.card_range]; rw [Nat.lt_succ_iff]
  · rw [degree_T, Int.natAbs_natCast, Nat.cast_lt,
      Finset.card_image_of_injOn (strictAntiOn_node n).injOn,
      Finset.card_range, Nat.lt_succ_iff]
  replace h := ge_of_eq h
  contrapose! h
  obtain ⟨x, hx, hPx⟩ := h
  obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx
  replace hi := Finset.mem_Iic.mpr (Finset.mem_range_succ_iff.mp hi)
  suffices ∑ i <= n, ((-1) ^ i * P.eval (node n i)) * ((-1) ^ i * c i) <
      ∑ i <= n, ((-1) ^ i * (T Real n).eval (node n i)) * ((-1) ^ i * c i) by
    simpa [negOnePow_mul_negOnePow_mul_cancel]
  have h_le {i : Nat} (hi : i in Finset.Iic n) :
    (-1) ^ i * P.eval (node n i) * ((-1) ^ i * c i) <=
    (-1) ^ i * (T Real n).eval (node n i) * ((-1) ^ i * c i) := by
    refine mul_le_mul_of_nonneg_right ?_ (le_of_lt (hcpos i (Finset.mem_Iic.mp hi)))
    rw [eval_T_real_node hi]; rw [← neg_pow']; rw [neg_neg]; rw [one_pow]
    exact negOnePow_mul_le (hPbnd _ node_mem_Icc)
  refine Finset.sum_lt_sum (fun i hi => h_le hi) ⟨i, hi, lt_of_le_of_ne (h_le hi) ?_⟩
  have := ne_of_lt (hcpos i (Finset.mem_Iic.mp hi))
  grind => ring

中文:
定理 sumNodes_eq_sumNodes_T_iff
  结论: {n : 自然数} {c : 自然数 -> 实数}
  证明: by
  refine ⟨fun h => ?_, by intro h; rw [h]⟩
  rw [sumNodes]; rw [sumNodes] at h
  apply eq_of_degrees_lt_of_eval_finset_eq ((Finset.range (n + 1)).image (node n ·))
  · apply lt_of_le_of_lt hPdeg
    rw [Nat.cast_lt]; rw [Finset.card_image_of_injOn (strictAntiOn_node n).injOn]; rw [Finset.card_range]; rw [Nat.lt_succ_iff]
  · rw [degree_T, Int.natAbs_natCast, Nat.cast_lt,
      Finset.card_image_of_injOn (strictAntiOn_node n).injOn,
      Finset.card_range, Nat.lt_succ_iff]
  replace h := ge_of_eq h
  contrapose! h
  obtain ⟨x, hx, hPx⟩ := h
  obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx
  replace hi := Finset.mem_Iic.mpr (Finset.mem_range_succ_iff.mp hi)
  suffices ∑ i <= n, ((-1) ^ i * P.eval (node n i)) * ((-1) ^ i * c i) <
      ∑ i <= n, ((-1) ^ i * (T Real n).eval (node n i)) * ((-1) ^ i * c i) by
    simpa [negOnePow_mul_negOnePow_mul_cancel]
  have h_le {i : Nat} (hi : i in Finset.Iic n) :
    (-1) ^ i * P.eval (node n i) * ((-1) ^ i * c i) <=
    (-1) ^ i * (T Real n).eval (node n i) * ((-1) ^ i * c i) := by
    refine mul_le_mul_of_nonneg_right ?_ (le_of_lt (hcpos i (Finset.mem_Iic.mp hi)))
    rw [eval_T_real_node hi]; rw [← neg_pow']; rw [neg_neg]; rw [one_pow]
    exact negOnePow_mul_le (hPbnd _ node_mem_Icc)
  refine Finset.sum_lt_sum (fun i hi => h_le hi) ⟨i, hi, lt_of_le_of_ne (h_le hi) ?_⟩
  have := ne_of_lt (hcpos i (Finset.mem_Iic.mp hi))
  grind => ring

Depends on / 依赖: Finset, Finset.card_image_of_injOn, Finset.card_range, Finset.range, Int.natAbs_natCast, Nat.cast_lt, Nat.lt_succ_iff, card_image_of_injOn, card_range, cast_lt, contrapose, degree_T, eq_of_degrees_lt_of_eval_finset_eq, ge_of_eq, lt_of_le_of_lt, lt_succ_iff, natAbs_natCast, replace, strictAntiOn_node, sumNodes
-/
theorem sumNodes_eq_sumNodes_T_iff {n : Nat} {c : Nat -> Real}
    (hcpos : forall i <= n, 0 < (-1) ^ i * (c i))
    {P : Real[X]} (hPdeg : P.degree <= n) (hPbnd : forall x in Set.Icc (-1) 1, |P.eval x| <= 1) :
    (sumNodes n c P = sumNodes n c (T Real n)) ↔ P = T Real n := by
  refine ⟨fun h => ?_, by intro h; rw [h]⟩
  rw [sumNodes]; rw [sumNodes] at h
  apply eq_of_degrees_lt_of_eval_finset_eq ((Finset.range (n + 1)).image (node n ·))
  · apply lt_of_le_of_lt hPdeg
    rw [Nat.cast_lt]; rw [Finset.card_image_of_injOn (strictAntiOn_node n).injOn]; rw [Finset.card_range]; rw [Nat.lt_succ_iff]
  · rw [degree_T, Int.natAbs_natCast, Nat.cast_lt,
      Finset.card_image_of_injOn (strictAntiOn_node n).injOn,
      Finset.card_range, Nat.lt_succ_iff]
  replace h := ge_of_eq h
  contrapose! h
  obtain ⟨x, hx, hPx⟩ := h
  obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx
  replace hi := Finset.mem_Iic.mpr (Finset.mem_range_succ_iff.mp hi)
  suffices ∑ i <= n, ((-1) ^ i * P.eval (node n i)) * ((-1) ^ i * c i) <
      ∑ i <= n, ((-1) ^ i * (T Real n).eval (node n i)) * ((-1) ^ i * c i) by
    simpa [negOnePow_mul_negOnePow_mul_cancel]
  have h_le {i : Nat} (hi : i in Finset.Iic n) :
    (-1) ^ i * P.eval (node n i) * ((-1) ^ i * c i) <=
    (-1) ^ i * (T Real n).eval (node n i) * ((-1) ^ i * c i) := by
    refine mul_le_mul_of_nonneg_right ?_ (le_of_lt (hcpos i (Finset.mem_Iic.mp hi)))
    rw [eval_T_real_node hi]; rw [← neg_pow']; rw [neg_neg]; rw [one_pow]
    exact negOnePow_mul_le (hPbnd _ node_mem_Icc)
  refine Finset.sum_lt_sum (fun i hi => h_le hi) ⟨i, hi, lt_of_le_of_ne (h_le hi) ?_⟩
  have := ne_of_lt (hcpos i (Finset.mem_Iic.mp hi))
  grind => ring

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def leadingCoeffC (n i : Nat)
  body: (∏ j in (Finset.range (n + 1)).erase i, (node n i - node n j))⁻¹

中文:
定义 noncomputable
  签名: def leadingCoeffC (n i : 自然数)
  定义体: (∏ j in (Finset.range (n + 1)).erase i, (node n i - node n j))⁻¹
-/
private noncomputable def leadingCoeffC (n i : Nat) :=
  (∏ j in (Finset.range (n + 1)).erase i, (node n i - node n j))⁻¹

/--
theorem `sumNodes_eq_coeff` / 定理 `sumNodes_eq_coeff`

English:
theorem sumNodes_eq_coeff
  given: {n : Nat} {P : Real[X]} (hP : P.degree <= n)
  proof: by
  simp_rw [sumNodes, leadingCoeffC]
  have : P.degree < (Finset.range (n + 1)).card := by
    rw [Finset.card_range]
    grw [hP]
    norm_cast
    simp
  convert! (Lagrange.coeff_eq_sum (strictAntiOn_node n).injOn this).symm using 2
  · exact Eq.symm (Nat.range_succ_eq_Iic n)
  · simp

中文:
定理 sumNodes_eq_coeff
  条件: {n : 自然数} {P : 实数[X]} (hP : P.degree <= n)
  证明: by
  simp_rw [sumNodes, leadingCoeffC]
  have : P.degree < (Finset.range (n + 1)).card := by
    rw [Finset.card_range]
    grw [hP]
    norm_cast
    simp
  convert! (Lagrange.coeff_eq_sum (strictAntiOn_node n).injOn this).symm using 2
  · exact Eq.symm (Nat.range_succ_eq_Iic n)
  · simp
-/
private theorem sumNodes_eq_coeff {n : Nat} {P : Real[X]} (hP : P.degree <= n) :
    sumNodes n (leadingCoeffC n) P = P.coeff n := by
  simp_rw [sumNodes, leadingCoeffC]
  have : P.degree < (Finset.range (n + 1)).card := by
    rw [Finset.card_range]
    grw [hP]
    norm_cast
    simp
  convert! (Lagrange.coeff_eq_sum (strictAntiOn_node n).injOn this).symm using 2
  · exact Eq.symm (Nat.range_succ_eq_Iic n)
  · simp

/--
theorem `sumNodes_T_eq` / 定理 `sumNodes_T_eq`

English:
theorem sumNodes_T_eq
  given: (n : Nat)
  proof: by
  rw [sumNodes_eq_coeff (by simp)]
  trans (T Real n).leadingCoeff
  · simp [leadingCoeff]
  · simp

中文:
定理 sumNodes_T_eq
  条件: (n : 自然数)
  证明: by
  rw [sumNodes_eq_coeff (by simp)]
  trans (T Real n).leadingCoeff
  · simp [leadingCoeff]
  · simp
-/
private theorem sumNodes_T_eq (n : Nat) :
    sumNodes n (leadingCoeffC n) (T Real n) = 2 ^ (n - 1) := by
  rw [sumNodes_eq_coeff (by simp)]
  trans (T Real n).leadingCoeff
  · simp [leadingCoeff]
  · simp

/--
theorem `negOnePow_mul_leadingCoeffC_pos` / 定理 `negOnePow_mul_leadingCoeffC_pos`

English:
theorem negOnePow_mul_leadingCoeffC_pos
  given: {n i : Nat} (hi : i <= n)
  proof: by
have := inv_pos_of_pos zero_lt_prod_node_sub_node hi
  rwa [mul_inv, ← inv_pow, inv_neg_one] at this

中文:
定理 negOnePow_mul_leadingCoeffC_pos
  条件: {n i : 自然数} (hi : i <= n)
  证明: by
have := inv_pos_of_pos zero_lt_prod_node_sub_node hi
  rwa [mul_inv, ← inv_pow, inv_neg_one] at this
-/
private theorem negOnePow_mul_leadingCoeffC_pos {n i : Nat} (hi : i <= n) :
    0 < (-1) ^ i * leadingCoeffC n i := by
have := inv_pos_of_pos zero_lt_prod_node_sub_node hi
  rwa [mul_inv, ← inv_pow, inv_neg_one] at this

/--
theorem `coeff_le_of_forall_abs_le_one` / 定理 `coeff_le_of_forall_abs_le_one`

English:
theorem coeff_le_of_forall_abs_le_one
  statement: {n : Nat} {P : Real[X]}
  proof: by
  convert! sumNodes_le_sumNodes_T (fun i hi => le_of_lt <| negOnePow_mul_leadingCoeffC_pos hi) hPbnd
  · rw [sumNodes_eq_coeff hPdeg]
  · rw [sumNodes_T_eq]

中文:
定理 coeff_le_of_对任意_abs_le_one
  结论: {n : 自然数} {P : 实数[X]}
  证明: by
  convert! sumNodes_le_sumNodes_T (fun i hi => le_of_lt <| negOnePow_mul_leadingCoeffC_pos hi) hPbnd
  · rw [sumNodes_eq_coeff hPdeg]
  · rw [sumNodes_T_eq]

Depends on / 依赖: convert, le_of_lt, negOnePow_mul_leadingCoeffC_pos, sumNodes_T_eq, sumNodes_eq_coeff, sumNodes_le_sumNodes_T
-/
theorem coeff_le_of_forall_abs_le_one {n : Nat} {P : Real[X]}
    (hPdeg : P.degree <= n) (hPbnd : forall x in Set.Icc (-1) 1, |P.eval x| <= 1) :
    P.coeff n <= 2 ^ (n - 1) := by
  convert! sumNodes_le_sumNodes_T (fun i hi => le_of_lt <| negOnePow_mul_leadingCoeffC_pos hi) hPbnd
  · rw [sumNodes_eq_coeff hPdeg]
  · rw [sumNodes_T_eq]

/--
theorem `leadingCoeff_le_of_forall_abs_le_one` / 定理 `leadingCoeff_le_of_forall_abs_le_one`

English:
theorem leadingCoeff_le_of_forall_abs_le_one
  statement: {n : Nat} {P : Real[X]}
  proof: by
  by_cases P = 0
  case pos hP => simp [hP]
  case neg hP =>
    lift P.degree to Nat using degree_ne_bot.mpr hP with d hd
    replace hPdeg : d <= n := (WithBot.coe_le rfl).mp hPdeg
    rw [leadingCoeff]; rw [natDegree_eq_of_degree_eq_some hd.symm]
    grw [coeff_le_of_forall_abs_le_one (le_of_eq hd.symm) hPbnd, hPdeg]
    norm_num

中文:
定理 leadingCoeff_le_of_对任意_abs_le_one
  结论: {n : 自然数} {P : 实数[X]}
  证明: by
  by_cases P = 0
  case pos hP => simp [hP]
  case neg hP =>
    lift P.degree to Nat using degree_ne_bot.mpr hP with d hd
    replace hPdeg : d <= n := (WithBot.coe_le rfl).mp hPdeg
    rw [leadingCoeff]; rw [natDegree_eq_of_degree_eq_some hd.symm]
    grw [coeff_le_of_forall_abs_le_one (le_of_eq hd.symm) hPbnd, hPdeg]
    norm_num

Depends on / 依赖: P.degree, WithBot, WithBot.coe_le, coe_le, coeff_le_of_forall_abs_le_one, degree, degree_ne_bot, degree_ne_bot.mpr, hd.symm, le_of_eq, leadingCoeff, natDegree_eq_of_degree_eq_some, replace
-/
theorem leadingCoeff_le_of_forall_abs_le_one {n : Nat} {P : Real[X]}
    (hPdeg : P.degree <= n) (hPbnd : forall x in Set.Icc (-1) 1, |P.eval x| <= 1) :
    P.leadingCoeff <= 2 ^ (n - 1) := by
  by_cases P = 0
  case pos hP => simp [hP]
  case neg hP =>
    lift P.degree to Nat using degree_ne_bot.mpr hP with d hd
    replace hPdeg : d <= n := (WithBot.coe_le rfl).mp hPdeg
    rw [leadingCoeff]; rw [natDegree_eq_of_degree_eq_some hd.symm]
    grw [coeff_le_of_forall_abs_le_one (le_of_eq hd.symm) hPbnd, hPdeg]
    norm_num

/--
theorem `coeff_eq_iff_of_forall_abs_le_one` / 定理 `coeff_eq_iff_of_forall_abs_le_one`

English:
theorem coeff_eq_iff_of_forall_abs_le_one
  statement: {n : Nat} {P : Real[X]}
  proof: by
  convert! sumNodes_eq_sumNodes_T_iff (fun i hi => negOnePow_mul_leadingCoeffC_pos hi) hPdeg hPbnd
  · rw [sumNodes_eq_coeff hPdeg]
  · rw [sumNodes_T_eq]

中文:
定理 coeff_eq_iff_of_对任意_abs_le_one
  结论: {n : 自然数} {P : 实数[X]}
  证明: by
  convert! sumNodes_eq_sumNodes_T_iff (fun i hi => negOnePow_mul_leadingCoeffC_pos hi) hPdeg hPbnd
  · rw [sumNodes_eq_coeff hPdeg]
  · rw [sumNodes_T_eq]

Depends on / 依赖: convert, negOnePow_mul_leadingCoeffC_pos, sumNodes_T_eq, sumNodes_eq_coeff, sumNodes_eq_sumNodes_T_iff
-/
theorem coeff_eq_iff_of_forall_abs_le_one {n : Nat} {P : Real[X]}
    (hPdeg : P.degree <= n) (hPbnd : forall x in Set.Icc (-1) 1, |P.eval x| <= 1) :
    P.coeff n = 2 ^ (n - 1) ↔ P = T Real n := by
  convert! sumNodes_eq_sumNodes_T_iff (fun i hi => negOnePow_mul_leadingCoeffC_pos hi) hPdeg hPbnd
  · rw [sumNodes_eq_coeff hPdeg]
  · rw [sumNodes_T_eq]

/--
theorem `leadingCoeff_eq_iff_of_forall_abs_le_one` / 定理 `leadingCoeff_eq_iff_of_forall_abs_le_one`

English:
theorem leadingCoeff_eq_iff_of_forall_abs_le_one
  statement: {n : Nat} {P : Real[X]} (hn : 2 <= n)
  proof: by
  refine ⟨fun hP => ?_, fun hP => by simp [hP]⟩
  apply (coeff_eq_iff_of_forall_abs_le_one hPdeg hPbnd).mp
  suffices hPdeg' : n <= P.degree by
    replace hPdeg' : P.degree = n := eq_of_le_of_ge hPdeg hPdeg'
    rwa [leadingCoeff, natDegree_eq_of_degree_eq_some hPdeg'] at hP
  lift P.degree to Nat with d hd
  · contrapose! hP
    rw [degree_eq_bot.mp hP]; rw [leadingCoeff_zero]
    positivity
  replace hP := ge_of_eq hP
  contrapose! hP
  have : d - 1 < n - 1 := by grind [Nat.cast_withBot, WithBot.coe_le_coe, WithBot.coe_lt_coe]
  calc P.leadingCoeff <= 2 ^ (d - 1) := leadingCoeff_le_of_forall_abs_le_one (le_of_eq hd.symm) hPbnd
  _ < 2 ^ (n - 1) := by gcongr; norm_num

中文:
定理 leadingCoeff_eq_iff_of_对任意_abs_le_one
  结论: {n : 自然数} {P : 实数[X]} (hn : 2 <= n)
  证明: by
  refine ⟨fun hP => ?_, fun hP => by simp [hP]⟩
  apply (coeff_eq_iff_of_forall_abs_le_one hPdeg hPbnd).mp
  suffices hPdeg' : n <= P.degree by
    replace hPdeg' : P.degree = n := eq_of_le_of_ge hPdeg hPdeg'
    rwa [leadingCoeff, natDegree_eq_of_degree_eq_some hPdeg'] at hP
  lift P.degree to Nat with d hd
  · contrapose! hP
    rw [degree_eq_bot.mp hP]; rw [leadingCoeff_zero]
    positivity
  replace hP := ge_of_eq hP
  contrapose! hP
  have : d - 1 < n - 1 := by grind [Nat.cast_withBot, WithBot.coe_le_coe, WithBot.coe_lt_coe]
  calc P.leadingCoeff <= 2 ^ (d - 1) := leadingCoeff_le_of_forall_abs_le_one (le_of_eq hd.symm) hPbnd
  _ < 2 ^ (n - 1) := by gcongr; norm_num

Depends on / 依赖: Nat.cast_withBot, P.degree, WithBot, WithBot.coe_l, WithBot.coe_le_coe, cast_withBot, coe_l, coe_le_coe, coeff_eq_iff_of_forall_abs_le_one, contrapose, degree, degree_eq_bot, degree_eq_bot.mp, eq_of_le_of_ge, ge_of_eq, leadingCoeff, leadingCoeff_zero, natDegree_eq_of_degree_eq_some, replace
-/
theorem leadingCoeff_eq_iff_of_forall_abs_le_one {n : Nat} {P : Real[X]} (hn : 2 <= n)
    (hPdeg : P.degree <= n) (hPbnd : forall x in Set.Icc (-1) 1, |P.eval x| <= 1) :
    P.leadingCoeff = 2 ^ (n - 1) ↔ P = T Real n := by
  refine ⟨fun hP => ?_, fun hP => by simp [hP]⟩
  apply (coeff_eq_iff_of_forall_abs_le_one hPdeg hPbnd).mp
  suffices hPdeg' : n <= P.degree by
    replace hPdeg' : P.degree = n := eq_of_le_of_ge hPdeg hPdeg'
    rwa [leadingCoeff, natDegree_eq_of_degree_eq_some hPdeg'] at hP
  lift P.degree to Nat with d hd
  · contrapose! hP
    rw [degree_eq_bot.mp hP]; rw [leadingCoeff_zero]
    positivity
  replace hP := ge_of_eq hP
  contrapose! hP
  have : d - 1 < n - 1 := by grind [Nat.cast_withBot, WithBot.coe_le_coe, WithBot.coe_lt_coe]
  calc P.leadingCoeff <= 2 ^ (d - 1) := leadingCoeff_le_of_forall_abs_le_one (le_of_eq hd.symm) hPbnd
  _ < 2 ^ (n - 1) := by gcongr; norm_num

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def iterateDerivativeC (n k : Nat) (x : Real) (i : Nat)
  body: k.factorial * (∏ j in (Finset.range (n + 1)).erase i, ((node n i) - (node n j)))⁻¹ *
    ∑ t in ((Finset.range (n + 1)).erase i).powersetCard (n - k), ∏ a in t, (x - node n a)

中文:
定义 noncomputable
  签名: def iterateDerivativeC (n k : 自然数) (x : 实数) (i : 自然数)
  定义体: k.factorial * (∏ j in (Finset.range (n + 1)).erase i, ((node n i) - (node n j)))⁻¹ *
    ∑ t in ((Finset.range (n + 1)).erase i).powersetCard (n - k), ∏ a in t, (x - node n a)
-/
private noncomputable def iterateDerivativeC (n k : Nat) (x : Real) (i : Nat) :=
    k.factorial * (∏ j in (Finset.range (n + 1)).erase i, ((node n i) - (node n j)))⁻¹ *
    ∑ t in ((Finset.range (n + 1)).erase i).powersetCard (n - k), ∏ a in t, (x - node n a)

/--
theorem `sumNodes_eq_eval_iterate_derivative` / 定理 `sumNodes_eq_eval_iterate_derivative`

English:
theorem sumNodes_eq_eval_iterate_derivative
  statement: {n k : Nat} (hk : k <= n) (x : Real)
  proof: by
  simp_rw [sumNodes, iterateDerivativeC]
  have h₁ : P.degree < (Finset.range (n + 1)).card := by
    rw [Finset.card_range]; grw [hP]; norm_cast; simp
  convert!
    (Lagrange.eval_iterate_derivative_eq_sum (strictAntiOn_node n).injOn h₁
        (show k < _ by simp [hk]) x).symm
  rw [Finset.mul_sum]
  grind [Nat.range_succ_eq_Iic, Nat.card_Iic]

中文:
定理 sumNodes_eq_eval_iterate_derivative
  结论: {n k : 自然数} (hk : k <= n) (x : 实数)
  证明: by
  simp_rw [sumNodes, iterateDerivativeC]
  have h₁ : P.degree < (Finset.range (n + 1)).card := by
    rw [Finset.card_range]; grw [hP]; norm_cast; simp
  convert!
    (Lagrange.eval_iterate_derivative_eq_sum (strictAntiOn_node n).injOn h₁
        (show k < _ by simp [hk]) x).symm
  rw [Finset.mul_sum]
  grind [Nat.range_succ_eq_Iic, Nat.card_Iic]
-/
private theorem sumNodes_eq_eval_iterate_derivative {n k : Nat} (hk : k <= n) (x : Real)
    {P : Real[X]} (hP : P.degree <= n) :
    sumNodes n (iterateDerivativeC n k x) P = (derivative^[k] P).eval x := by
  simp_rw [sumNodes, iterateDerivativeC]
  have h₁ : P.degree < (Finset.range (n + 1)).card := by
    rw [Finset.card_range]; grw [hP]; norm_cast; simp
  convert!
    (Lagrange.eval_iterate_derivative_eq_sum (strictAntiOn_node n).injOn h₁
        (show k < _ by simp [hk]) x).symm
  rw [Finset.mul_sum]
  grind [Nat.range_succ_eq_Iic, Nat.card_Iic]

/--
theorem `negOnePow_mul_iterateDerivativeC_nonneg` / 定理 `negOnePow_mul_iterateDerivativeC_nonneg`

English:
theorem negOnePow_mul_iterateDerivativeC_nonneg
  proof: by
  rw [iterateDerivativeC]; rw [← mul_assoc]
  refine mul_nonneg ?_ (Finset.sum_nonneg' ?_)
  · rw [← mul_assoc, mul_comm (a := (-1) ^ i), mul_assoc]
exact le_of_lt mul_pos (Nat.cast_pos.mpr <| Nat.factorial_pos k)
      (negOnePow_mul_leadingCoeffC_pos hi)
  · exact fun t => Finset.prod_nonneg (fun a _ => by grind [show node n a <= 1 from cos_le_one _])

中文:
定理 negOnePow_mul_iterateDerivativeC_nonneg
  证明: by
  rw [iterateDerivativeC]; rw [← mul_assoc]
  refine mul_nonneg ?_ (Finset.sum_nonneg' ?_)
  · rw [← mul_assoc, mul_comm (a := (-1) ^ i), mul_assoc]
exact le_of_lt mul_pos (Nat.cast_pos.mpr <| Nat.factorial_pos k)
      (negOnePow_mul_leadingCoeffC_pos hi)
  · exact fun t => Finset.prod_nonneg (fun a _ => by grind [show node n a <= 1 from cos_le_one _])
-/
private theorem negOnePow_mul_iterateDerivativeC_nonneg
    {n k i : Nat} (hi : i <= n) {x : Real} (hx : 1 <= x) :
    0 <= (-1) ^ i * iterateDerivativeC n k x i := by
  rw [iterateDerivativeC]; rw [← mul_assoc]
  refine mul_nonneg ?_ (Finset.sum_nonneg' ?_)
  · rw [← mul_assoc, mul_comm (a := (-1) ^ i), mul_assoc]
exact le_of_lt mul_pos (Nat.cast_pos.mpr <| Nat.factorial_pos k)
      (negOnePow_mul_leadingCoeffC_pos hi)
  · exact fun t => Finset.prod_nonneg (fun a _ => by grind [show node n a <= 1 from cos_le_one _])

/--
theorem `negOnePow_mul_iterateDerivativeC_pos` / 定理 `negOnePow_mul_iterateDerivativeC_pos`

English:
theorem negOnePow_mul_iterateDerivativeC_pos
  proof: by
  rw [iterateDerivativeC]; rw [← mul_assoc]
  refine mul_pos ?_ (Finset.sum_pos' ?_ ?_)
  · rw [← mul_assoc, mul_comm (a := (-1) ^ i), mul_assoc]
    exact mul_pos (Nat.cast_pos.mpr <| Nat.factorial_pos k) (negOnePow_mul_leadingCoeffC_pos hi)
  · exact fun t _ => Finset.prod_nonneg (fun a _ => by grind [show node n a <= 1 from cos_le_one _])
  · have : exists s subseteq (Finset.range (n + 1)).erase i, s.card = n - k ∧ 0 ∉ s := by
      by_cases 1 <= i ∧ i <= n - k
      case neg => exact ⟨Finset.Icc 1 (n - k), by grind, by grind [Nat.card_Icc], by simp⟩
      case pos => exact ⟨(Finset.Icc 1 (n - k + 1)).erase i, by grind, by grind [Nat.card_Icc],
        by simp⟩
    obtain ⟨s, hs, hscard, hsn⟩ := this
    refine ⟨s, by simp [hs, hscard], Finset.prod_pos (fun a ha => ?_)⟩
    grind [show node n a < 1 by rw [← node_eq_one (n := n)]; exact node_lt (by grind) (by grind)]

中文:
定理 negOnePow_mul_iterateDerivativeC_pos
  证明: by
  rw [iterateDerivativeC]; rw [← mul_assoc]
  refine mul_pos ?_ (Finset.sum_pos' ?_ ?_)
  · rw [← mul_assoc, mul_comm (a := (-1) ^ i), mul_assoc]
    exact mul_pos (Nat.cast_pos.mpr <| Nat.factorial_pos k) (negOnePow_mul_leadingCoeffC_pos hi)
  · exact fun t _ => Finset.prod_nonneg (fun a _ => by grind [show node n a <= 1 from cos_le_one _])
  · have : exists s subseteq (Finset.range (n + 1)).erase i, s.card = n - k ∧ 0 ∉ s := by
      by_cases 1 <= i ∧ i <= n - k
      case neg => exact ⟨Finset.Icc 1 (n - k), by grind, by grind [Nat.card_Icc], by simp⟩
      case pos => exact ⟨(Finset.Icc 1 (n - k + 1)).erase i, by grind, by grind [Nat.card_Icc],
        by simp⟩
    obtain ⟨s, hs, hscard, hsn⟩ := this
    refine ⟨s, by simp [hs, hscard], Finset.prod_pos (fun a ha => ?_)⟩
    grind [show node n a < 1 by rw [← node_eq_one (n := n)]; exact node_lt (by grind) (by grind)]
-/
private theorem negOnePow_mul_iterateDerivativeC_pos
    {n k i : Nat} (hk₁ : 0 < k) (hk₂ : k <= n) (hi : i <= n) {x : Real} (hx : 1 <= x) :
    0 < (-1) ^ i * iterateDerivativeC n k x i := by
  rw [iterateDerivativeC]; rw [← mul_assoc]
  refine mul_pos ?_ (Finset.sum_pos' ?_ ?_)
  · rw [← mul_assoc, mul_comm (a := (-1) ^ i), mul_assoc]
    exact mul_pos (Nat.cast_pos.mpr <| Nat.factorial_pos k) (negOnePow_mul_leadingCoeffC_pos hi)
  · exact fun t _ => Finset.prod_nonneg (fun a _ => by grind [show node n a <= 1 from cos_le_one _])
  · have : exists s subseteq (Finset.range (n + 1)).erase i, s.card = n - k ∧ 0 ∉ s := by
      by_cases 1 <= i ∧ i <= n - k
      case neg => exact ⟨Finset.Icc 1 (n - k), by grind, by grind [Nat.card_Icc], by simp⟩
      case pos => exact ⟨(Finset.Icc 1 (n - k + 1)).erase i, by grind, by grind [Nat.card_Icc],
        by simp⟩
    obtain ⟨s, hs, hscard, hsn⟩ := this
    refine ⟨s, by simp [hs, hscard], Finset.prod_pos (fun a ha => ?_)⟩
    grind [show node n a < 1 by rw [← node_eq_one (n := n)]; exact node_lt (by grind) (by grind)]

/--
theorem `eval_iterate_derivative_le_of_forall_abs_le_one` / 定理 `eval_iterate_derivative_le_of_forall_abs_le_one`

English:
theorem eval_iterate_derivative_le_of_forall_abs_le_one
  statement: {n : Nat} {P : Real[X]}
  proof: by
  by_cases! hk : n < k
  · rw [iterate_derivative_eq_zero_of_degree_lt (by grw [hPdeg]; simpa),
      iterate_derivative_eq_zero_of_degree_lt (by simp [hk])]
  convert!
    sumNodes_le_sumNodes_T (fun i hi => negOnePow_mul_iterateDerivativeC_nonneg hi hx) hPbnd using 1
  · rw [sumNodes_eq_eval_iterate_derivative hk x hPdeg]
  · rw [sumNodes_eq_eval_iterate_derivative hk x (le_of_eq (degree_T Real n))]

中文:
定理 eval_iterate_derivative_le_of_对任意_abs_le_one
  结论: {n : 自然数} {P : 实数[X]}
  证明: by
  by_cases! hk : n < k
  · rw [iterate_derivative_eq_zero_of_degree_lt (by grw [hPdeg]; simpa),
      iterate_derivative_eq_zero_of_degree_lt (by simp [hk])]
  convert!
    sumNodes_le_sumNodes_T (fun i hi => negOnePow_mul_iterateDerivativeC_nonneg hi hx) hPbnd using 1
  · rw [sumNodes_eq_eval_iterate_derivative hk x hPdeg]
  · rw [sumNodes_eq_eval_iterate_derivative hk x (le_of_eq (degree_T Real n))]

Depends on / 依赖: convert, degree_T, iterate_derivative_eq_zero_of_degree_lt, le_of_eq, negOnePow_mul_iterateDerivativeC_nonneg, sumNodes_eq_eval_iterate_derivative, sumNodes_le_sumNodes_T
-/
theorem eval_iterate_derivative_le_of_forall_abs_le_one {n : Nat} {P : Real[X]}
    {k : Nat} {x : Real} (hx : 1 <= x)
    (hPdeg : P.degree <= n) (hPbnd : forall x in Set.Icc (-1) 1, |P.eval x| <= 1) :
    (derivative^[k] P).eval x <= (derivative^[k] (T Real n)).eval x := by
  by_cases! hk : n < k
  · rw [iterate_derivative_eq_zero_of_degree_lt (by grw [hPdeg]; simpa),
      iterate_derivative_eq_zero_of_degree_lt (by simp [hk])]
  convert!
    sumNodes_le_sumNodes_T (fun i hi => negOnePow_mul_iterateDerivativeC_nonneg hi hx) hPbnd using 1
  · rw [sumNodes_eq_eval_iterate_derivative hk x hPdeg]
  · rw [sumNodes_eq_eval_iterate_derivative hk x (le_of_eq (degree_T Real n))]

/--
theorem `eval_iterate_derivative_eq_iff_of_bounded` / 定理 `eval_iterate_derivative_eq_iff_of_bounded`

English:
theorem eval_iterate_derivative_eq_iff_of_bounded
  statement: {n : Nat} {P : Real[X]}
  proof: by
  convert!
    sumNodes_eq_sumNodes_T_iff (fun i hi => negOnePow_mul_iterateDerivativeC_pos hk₁ hk₂ hi hx)
      hPdeg hPbnd using 2
  · rw [sumNodes_eq_eval_iterate_derivative hk₂ x hPdeg]
  · rw [sumNodes_eq_eval_iterate_derivative hk₂ x (le_of_eq (degree_T Real n))]

中文:
定理 eval_iterate_derivative_eq_iff_of_bounded
  结论: {n : 自然数} {P : 实数[X]}
  证明: by
  convert!
    sumNodes_eq_sumNodes_T_iff (fun i hi => negOnePow_mul_iterateDerivativeC_pos hk₁ hk₂ hi hx)
      hPdeg hPbnd using 2
  · rw [sumNodes_eq_eval_iterate_derivative hk₂ x hPdeg]
  · rw [sumNodes_eq_eval_iterate_derivative hk₂ x (le_of_eq (degree_T Real n))]

Depends on / 依赖: convert, degree_T, le_of_eq, negOnePow_mul_iterateDerivativeC_pos, sumNodes_eq_eval_iterate_derivative, sumNodes_eq_sumNodes_T_iff
-/
theorem eval_iterate_derivative_eq_iff_of_bounded {n : Nat} {P : Real[X]}
    {k : Nat} (hk₁ : 0 < k) (hk₂ : k <= n) {x : Real} (hx : 1 <= x)
    (hPdeg : P.degree <= n) (hPbnd : forall x in Set.Icc (-1) 1, |P.eval x| <= 1) :
    (derivative^[k] P).eval x = (derivative^[k] (T Real n)).eval x ↔ P = T Real n := by
  convert!
    sumNodes_eq_sumNodes_T_iff (fun i hi => negOnePow_mul_iterateDerivativeC_pos hk₁ hk₂ hi hx)
      hPdeg hPbnd using 2
  · rw [sumNodes_eq_eval_iterate_derivative hk₂ x hPdeg]
  · rw [sumNodes_eq_eval_iterate_derivative hk₂ x (le_of_eq (degree_T Real n))]

end Polynomial.Chebyshev
