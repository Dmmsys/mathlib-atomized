/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Arithmetic-geometric sequences

An arithmetic-geometric sequence is a sequence defined by the recurrence relation
`u (n + 1) = a * u n + b`.

## Main definitions

* `arithGeom a b u₀`: arithmetic-geometric sequence with starting value `u₀` and recurrence relation
  `u (n + 1) = a * u n + b`.

## Main statements

* `arithGeom_eq`: for `a ≠ 1`, `arithGeom a b u₀ n = a ^ n * (u₀ - (b / (1 - a))) + b / (1 - a)`
* `tendsto_arithGeom_atTop_of_one_lt`: if `1 < a` and `b / (1 - a) < u₀`, then `arithGeom a b u₀ n`
  tends to `+∞` as `n` tends to `+∞`.
  `tendsto_arithGeom_nhds_of_lt_one`: if `0 ≤ a < 1`, then `arithGeom a b u₀ n` tends to
  `b / (1 - a)` as `n` tends to `+∞`.
* `arithGeom_strictMono`: if `1 < a` and `b / (1 - a) < u₀`, then `arithGeom a b u₀` is strictly
  monotone.

-/

@[expose] public section

open Filter Topology

variable {R : Type*} {a b u₀ : R}

/--
Definition of `arithGeom` / `arithGeom` 的定义

English:
definition arithGeom
  signature: [Mul R] [Add R] (a b u₀ : R)

中文:
定义 arithGeom
  签名: [乘法 R] [加法 R] (a b u₀ : R)
-/
def arithGeom [Mul R] [Add R] (a b u₀ : R) : Nat -> R
| 0 => u₀
| n + 1 => a * arithGeom a b u₀ n + b

/--
lemma `arithGeom_zero` / 引理 `arithGeom_zero`

English:
lemma arithGeom_zero
  given: [Mul R] [Add R]
  statement: arithGeom a b u₀ 0 = u₀
  proof: rfl

中文:
引理 arithGeom_zero
  条件: [乘法 R] [加法 R]
  结论: arithGeom a b u₀ 0 = u₀
  证明: rfl
-/
@[simp] lemma arithGeom_zero [Mul R] [Add R] : arithGeom a b u₀ 0 = u₀ := rfl

/--
lemma `arithGeom_succ` / 引理 `arithGeom_succ`

English:
lemma arithGeom_succ
  given: [Mul R] [Add R] (n : Nat)
  proof: rfl

中文:
引理 arithGeom_succ
  条件: [乘法 R] [加法 R] (n : 自然数)
  证明: rfl
-/
lemma arithGeom_succ [Mul R] [Add R] (n : Nat) :
    arithGeom a b u₀ (n + 1) = a * arithGeom a b u₀ n + b := rfl

/--
lemma `arithGeom_eq_add_sum` / 引理 `arithGeom_eq_add_sum`

English:
lemma arithGeom_eq_add_sum
  given: [CommSemiring R] (n : Nat)
  proof: by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [arithGeom_succ]; rw [hn]; rw [mul_add]; rw [← mul_assoc]; rw [add_comm n]; rw [pow_add]; rw [pow_one]; rw [add_assoc]
    congr
    rw [add_comm _ n]; rw [Finset.sum_range_succ']; rw [Finset.mul_sum]; rw [pow_zero]; rw [mul_add]; rw [mu

中文:
引理 arithGeom_eq_add_sum
  条件: [交换半环 R] (n : 自然数)
  证明: by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [arithGeom_succ]; rw [hn]; rw [mul_add]; rw [← mul_assoc]; rw [add_comm n]; rw [pow_add]; rw [pow_one]; rw [add_assoc]
    congr
    rw [add_comm _ n]; rw [Finset.sum_range_succ']; rw [Finset.mul_sum]; rw [pow_zero]; rw [mul_add]; rw [mu

Depends on / 依赖: Finset, Finset.mul_sum, Finset.sum_range_succ, add_assoc, add_comm, arithGeom_succ, category, mul_add, mul_assoc, mul_one, mul_sum, pow_add, pow_one, pow_zero, sum_range_succ
-/
lemma arithGeom_eq_add_sum [CommSemiring R] (n : Nat) :
    arithGeom a b u₀ n = a ^ n * u₀ + b * ∑ k in Finset.range n, a ^ k := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [arithGeom_succ]; rw [hn]; rw [mul_add]; rw [← mul_assoc]; rw [add_comm n]; rw [pow_add]; rw [pow_one]; rw [add_assoc]
    congr
    rw [add_comm _ n]; rw [Finset.sum_range_succ']; rw [Finset.mul_sum]; rw [pow_zero]; rw [mul_add]; rw [mul_one]; rw [Finset.mul_sum]; rw [Finset.mul_sum]
    congr with k
    ring

/--
lemma `arithGeom_same_eq_sum` / 引理 `arithGeom_same_eq_sum`

English:
lemma arithGeom_same_eq_sum
  given: [CommSemiring R] (n : Nat)
  proof: by
  rw [arithGeom_eq_add_sum]; rw [Finset.sum_range_succ]; rw [mul_add]; rw [add_comm]; rw [mul_comm _ b]

中文:
引理 arithGeom_same_eq_sum
  条件: [交换半环 R] (n : 自然数)
  证明: by
  rw [arithGeom_eq_add_sum]; rw [Finset.sum_range_succ]; rw [mul_add]; rw [add_comm]; rw [mul_comm _ b]

Depends on / 依赖: Finset, Finset.sum_range_succ, add_comm, arithGeom_eq_add_sum, mul_add, mul_comm, sum_range_succ
-/
lemma arithGeom_same_eq_sum [CommSemiring R] (n : Nat) :
    arithGeom a b b n = b * ∑ k in Finset.range (n + 1), a ^ k := by
  rw [arithGeom_eq_add_sum]; rw [Finset.sum_range_succ]; rw [mul_add]; rw [add_comm]; rw [mul_comm _ b]

/--
lemma `arithGeom_zero_eq_sum` / 引理 `arithGeom_zero_eq_sum`

English:
lemma arithGeom_zero_eq_sum
  given: [CommSemiring R] (n : Nat)
  proof: by
  simp [arithGeom_eq_add_sum]

中文:
引理 arithGeom_zero_eq_sum
  条件: [交换半环 R] (n : 自然数)
  证明: by
  simp [arithGeom_eq_add_sum]

Depends on / 依赖: arithGeom_eq_add_sum
-/
lemma arithGeom_zero_eq_sum [CommSemiring R] (n : Nat) :
    arithGeom a b 0 n = b * ∑ k in Finset.range n, a ^ k := by
  simp [arithGeom_eq_add_sum]

variable [Field R]

/--
lemma `arithGeom_eq` / 引理 `arithGeom_eq`

English:
lemma arithGeom_eq
  given: (ha : a != 1) (n : Nat)
  proof: by
  induction n with
  | zero => simp
  | succ n hn => unfold arithGeom; grind

中文:
引理 arithGeom_eq
  条件: (ha : a != 1) (n : 自然数)
  证明: by
  induction n with
  | zero => simp
  | succ n hn => unfold arithGeom; grind

Depends on / 依赖: arithGeom
-/
lemma arithGeom_eq (ha : a != 1) (n : Nat) :
    arithGeom a b u₀ n = a ^ n * (u₀ - (b / (1 - a))) + b / (1 - a) := by
  induction n with
  | zero => simp
  | succ n hn => unfold arithGeom; grind

/--
lemma `arithGeom_eq'` / 引理 `arithGeom_eq'`

English:
lemma arithGeom_eq'
  given: (ha : a != 1)
  proof: by
  ext
  exact arithGeom_eq ha _

中文:
引理 arithGeom_eq'
  条件: (ha : a != 1)
  证明: by
  ext
  exact arithGeom_eq ha _

Depends on / 依赖: arithGeom_eq
-/
lemma arithGeom_eq' (ha : a != 1) :
    arithGeom a b u₀ = fun n => a ^ n * (u₀ - (b / (1 - a))) + b / (1 - a) := by
  ext
  exact arithGeom_eq ha _

/--
lemma `arithGeom_same_eq_mul_div'` / 引理 `arithGeom_same_eq_mul_div'`

English:
lemma arithGeom_same_eq_mul_div'
  given: (ha : a != 1) (n : Nat)
  proof: by
  rw [arithGeom_eq ha n]
  field [sub_ne_zero.mpr ha.symm]

中文:
引理 arithGeom_same_eq_mul_div'
  条件: (ha : a != 1) (n : 自然数)
  证明: by
  rw [arithGeom_eq ha n]
  field [sub_ne_zero.mpr ha.symm]

Depends on / 依赖: arithGeom_eq, ha.symm, sub_ne_zero, sub_ne_zero.mpr
-/
lemma arithGeom_same_eq_mul_div' (ha : a != 1) (n : Nat) :
    arithGeom a b b n = b * (1 - a ^ (n + 1)) / (1 - a) := by
  rw [arithGeom_eq ha n]
  field [sub_ne_zero.mpr ha.symm]

/--
lemma `arithGeom_same_eq_mul_div` / 引理 `arithGeom_same_eq_mul_div`

English:
lemma arithGeom_same_eq_mul_div
  given: (ha : a != 1) (n : Nat)
  proof: by
  rw [arithGeom_same_eq_mul_div' ha n]; rw [← neg_sub _ a]; rw [div_neg]; rw [← neg_sub _ (a ^ (n + 1))]; rw [mul_neg]; rw [neg_div]; rw [neg_neg]

中文:
引理 arithGeom_same_eq_mul_div
  条件: (ha : a != 1) (n : 自然数)
  证明: by
  rw [arithGeom_same_eq_mul_div' ha n]; rw [← neg_sub _ a]; rw [div_neg]; rw [← neg_sub _ (a ^ (n + 1))]; rw [mul_neg]; rw [neg_div]; rw [neg_neg]

Depends on / 依赖: arithGeom_same_eq_mul_div, div_neg, mul_neg, neg_div, neg_neg, neg_sub
-/
lemma arithGeom_same_eq_mul_div (ha : a != 1) (n : Nat) :
    arithGeom a b b n = b * (a ^ (n + 1) - 1) / (a - 1) := by
  rw [arithGeom_same_eq_mul_div' ha n]; rw [← neg_sub _ a]; rw [div_neg]; rw [← neg_sub _ (a ^ (n + 1))]; rw [mul_neg]; rw [neg_div]; rw [neg_neg]

/--
lemma `arithGeom_zero_eq_mul_div'` / 引理 `arithGeom_zero_eq_mul_div'`

English:
lemma arithGeom_zero_eq_mul_div'
  given: (ha : a != 1) (n : Nat)
  proof: by
  rw [arithGeom_eq ha n]
  ring

中文:
引理 arithGeom_zero_eq_mul_div'
  条件: (ha : a != 1) (n : 自然数)
  证明: by
  rw [arithGeom_eq ha n]
  ring

Depends on / 依赖: arithGeom_eq
-/
lemma arithGeom_zero_eq_mul_div' (ha : a != 1) (n : Nat) :
    arithGeom a b 0 n = b * (1 - a ^ n) / (1 - a) := by
  rw [arithGeom_eq ha n]
  ring

/--
lemma `arithGeom_zero_eq_mul_div` / 引理 `arithGeom_zero_eq_mul_div`

English:
lemma arithGeom_zero_eq_mul_div
  given: (ha : a != 1) (n : Nat)
  proof: by
  rw [arithGeom_zero_eq_mul_div' ha n]; rw [← neg_sub _ a]; rw [div_neg]; rw [← neg_sub _ (a ^ n)]; rw [mul_neg]; rw [neg_div]; rw [neg_neg]

中文:
引理 arithGeom_zero_eq_mul_div
  条件: (ha : a != 1) (n : 自然数)
  证明: by
  rw [arithGeom_zero_eq_mul_div' ha n]; rw [← neg_sub _ a]; rw [div_neg]; rw [← neg_sub _ (a ^ n)]; rw [mul_neg]; rw [neg_div]; rw [neg_neg]

Depends on / 依赖: arithGeom_zero_eq_mul_div, div_neg, mul_neg, neg_div, neg_neg, neg_sub
-/
lemma arithGeom_zero_eq_mul_div (ha : a != 1) (n : Nat) :
    arithGeom a b 0 n = b * (a ^ n - 1) / (a - 1) := by
  rw [arithGeom_zero_eq_mul_div' ha n]; rw [← neg_sub _ a]; rw [div_neg]; rw [← neg_sub _ (a ^ n)]; rw [mul_neg]; rw [neg_div]; rw [neg_neg]

variable [LinearOrder R] [IsStrictOrderedRing R]

/--
lemma `div_lt_arithGeom` / 引理 `div_lt_arithGeom`

English:
lemma div_lt_arithGeom
  given: (ha_pos : 0 < a) (ha_ne : a != 1) (h0 : b / (1 - a) < u₀) (n : Nat)
  proof: by
  induction n with
  | zero => exact h0
  | succ n hn =>
    calc b / (1 - a)
    _ = a * (b / (1 - a)) + b := by grind
    _ < a * arithGeom a b u₀ n + b := by gcongr

中文:
引理 div_lt_arithGeom
  条件: (ha_pos : 0 < a) (ha_ne : a != 1) (h0 : b / (1 - a) < u₀) (n : 自然数)
  证明: by
  induction n with
  | zero => exact h0
  | succ n hn =>
    calc b / (1 - a)
    _ = a * (b / (1 - a)) + b := by grind
    _ < a * arithGeom a b u₀ n + b := by gcongr

Depends on / 依赖: IsHomLift, IsHomLift.id, arithGeom, w_obj
-/
lemma div_lt_arithGeom (ha_pos : 0 < a) (ha_ne : a != 1) (h0 : b / (1 - a) < u₀) (n : Nat) :
    b / (1 - a) < arithGeom a b u₀ n := by
  induction n with
  | zero => exact h0
  | succ n hn =>
    calc b / (1 - a)
    _ = a * (b / (1 - a)) + b := by grind
    _ < a * arithGeom a b u₀ n + b := by gcongr

/--
lemma `arithGeom_strictMono` / 引理 `arithGeom_strictMono`

English:
lemma arithGeom_strictMono
  given: (ha : 1 < a) (h0 : b / (1 - a) < u₀)
  proof: by
  refine strictMono_nat_of_lt_succ fun n => ?_
  have h_lt : b / (1 - a) < arithGeom a b u₀ n := div_lt_arithGeom (by positivity) ha.ne' h0 n
  rw [div_lt_iff_of_neg (sub_neg.mpr ha)] at h_lt
  rw [arithGeom_succ]
  linarith

中文:
引理 arithGeom_strictMono
  条件: (ha : 1 < a) (h0 : b / (1 - a) < u₀)
  证明: by
  refine strictMono_nat_of_lt_succ fun n => ?_
  have h_lt : b / (1 - a) < arithGeom a b u₀ n := div_lt_arithGeom (by positivity) ha.ne' h0 n
  rw [div_lt_iff_of_neg (sub_neg.mpr ha)] at h_lt
  rw [arithGeom_succ]
  linarith

Depends on / 依赖: arithGeom, arithGeom_succ, div_lt_arithGeom, div_lt_iff_of_neg, h_lt, ha.ne, strictMono_nat_of_lt_succ, sub_neg, sub_neg.mpr
-/
lemma arithGeom_strictMono (ha : 1 < a) (h0 : b / (1 - a) < u₀) :
    StrictMono (arithGeom a b u₀) := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  have h_lt : b / (1 - a) < arithGeom a b u₀ n := div_lt_arithGeom (by positivity) ha.ne' h0 n
  rw [div_lt_iff_of_neg (sub_neg.mpr ha)] at h_lt
  rw [arithGeom_succ]
  linarith

/--
lemma `tendsto_arithGeom_atTop_of_one_lt` / 引理 `tendsto_arithGeom_atTop_of_one_lt`

English:
lemma tendsto_arithGeom_atTop_of_one_lt
  given: [Archimedean R] (ha : 1 < a) (h0 : b / (1 - a) < u₀)
  proof: by
  rw [arithGeom_eq' ha.ne']
  refine tendsto_atTop_add_const_right _ _ ?_
  refine Tendsto.atTop_mul_const (sub_pos.mpr h0) ?_
  exact tendsto_pow_atTop_atTop_of_one_lt ha

中文:
引理 tendsto_arithGeom_atTop_of_one_lt
  条件: [阿基米德 R] (ha : 1 < a) (h0 : b / (1 - a) < u₀)
  证明: by
  rw [arithGeom_eq' ha.ne']
  refine tendsto_atTop_add_const_right _ _ ?_
  refine Tendsto.atTop_mul_const (sub_pos.mpr h0) ?_
  exact tendsto_pow_atTop_atTop_of_one_lt ha

Depends on / 依赖: Tendsto, Tendsto.atTop_mul_const, arithGeom_eq, atTop_mul_const, ha.ne, sub_pos, sub_pos.mpr, tendsto_atTop_add_const_right, tendsto_pow_atTop_atTop_of_one_lt
-/
lemma tendsto_arithGeom_atTop_of_one_lt [Archimedean R] (ha : 1 < a) (h0 : b / (1 - a) < u₀) :
    Tendsto (arithGeom a b u₀) atTop atTop := by
  rw [arithGeom_eq' ha.ne']
  refine tendsto_atTop_add_const_right _ _ ?_
  refine Tendsto.atTop_mul_const (sub_pos.mpr h0) ?_
  exact tendsto_pow_atTop_atTop_of_one_lt ha

/--
lemma `tendsto_arithGeom_nhds_of_lt_one` / 引理 `tendsto_arithGeom_nhds_of_lt_one`

English:
lemma tendsto_arithGeom_nhds_of_lt_one
  statement: [Archimedean R] [TopologicalSpace R] [OrderTopology R]
  proof: by
  rw [arithGeom_eq' ha.ne]
  conv_rhs => rw [← zero_add (b / (1 - a))]
  refine Tendsto.add ?_ tendsto_const_nhds
  conv_rhs => rw [← zero_mul (u₀ - (b / (1 - a)))]
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one ha_pos ha).mul_const _

中文:
引理 tendsto_arithGeom_nhds_of_lt_one
  结论: [阿基米德 R] [拓扑空间 R] [Order拓扑 R]
  证明: by
  rw [arithGeom_eq' ha.ne]
  conv_rhs => rw [← zero_add (b / (1 - a))]
  refine Tendsto.add ?_ tendsto_const_nhds
  conv_rhs => rw [← zero_mul (u₀ - (b / (1 - a)))]
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one ha_pos ha).mul_const _

Depends on / 依赖: Tendsto, Tendsto.add, arithGeom_eq, conv_rhs, ha.ne, ha_pos, mul_const, tendsto_const_nhds, tendsto_pow_atTop_nhds_zero_of_lt_one, zero_add, zero_mul
-/
lemma tendsto_arithGeom_nhds_of_lt_one [Archimedean R] [TopologicalSpace R] [OrderTopology R]
    (ha_pos : 0 <= a) (ha : a < 1) :
    Tendsto (arithGeom a b u₀) atTop (𝓝 (b / (1 - a))) := by
  rw [arithGeom_eq' ha.ne]
  conv_rhs => rw [← zero_add (b / (1 - a))]
  refine Tendsto.add ?_ tendsto_const_nhds
  conv_rhs => rw [← zero_mul (u₀ - (b / (1 - a)))]
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one ha_pos ha).mul_const _
