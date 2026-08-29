/-
Copyright (c) 2023 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.ToIntervalMod
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Interval.Set.Group

/-!
# Akra-Bazzi theorem: the polynomial growth condition

This file defines and develops an API for the polynomial growth condition that appears in the
statement of the Akra-Bazzi theorem: for the theorem to hold, the function `g` must
satisfy the condition that `c₁ g(n) ≤ g(u) ≤ c₂ g(n)`, for `u` between `b*n` and `n` for any
constant `b ∈ (0,1)`.

## Implementation notes

Our definition requires that the condition hold for any `b ∈ (0,1)`. This is equivalent to requiring
it only for `b = 1 / 2` (or any other particular value in `(0, 1)`). While this could, in principle,
make it harder to prove that a particular function grows polynomially, this issue does not seem to
arise in practice.

-/

@[expose] public section

open Finset Real Filter Asymptotics
open scoped Topology

namespace AkraBazziRecurrence

/--
Definition of `GrowsPolynomially` / `GrowsPolynomially` 的定义

English:
definition GrowsPolynomially
  signature: (f : Real -> Real)
  body: forall b in Set.Ioo 0 1, exists c₁ > 0, exists c₂ > 0,
    forallᶠ x in atTop, forall u in Set.Icc (b * x) x, f u in Set.Icc (c₁ * (f x)) (c₂ * f x)

中文:
定义 GrowsPolynomially
  签名: (f : 实数 -> 实数)
  定义体: forall b in Set.Ioo 0 1, exists c₁ > 0, exists c₂ > 0,
    forallᶠ x in atTop, forall u in Set.Icc (b * x) x, f u in Set.Icc (c₁ * (f x)) (c₂ * f x)

Depends on / 依赖: Set.Icc, Set.Ioo
-/
def GrowsPolynomially (f : Real -> Real) : Prop :=
  forall b in Set.Ioo 0 1, exists c₁ > 0, exists c₂ > 0,
    forallᶠ x in atTop, forall u in Set.Icc (b * x) x, f u in Set.Icc (c₁ * (f x)) (c₂ * f x)

namespace GrowsPolynomially

/--
lemma `congr_of_eventuallyEq` / 引理 `congr_of_eventuallyEq`

English:
lemma congr_of_eventuallyEq
  given: {f g : Real -> Real} (hfg : f =ᶠ[atTop] g) (hg : GrowsPolynomially g)
  proof: by
  intro b hb
  have hg' := hg b hb
  obtain ⟨c₁, hc₁_mem, c₂, hc₂_mem, hg'⟩ := hg'
  refine ⟨c₁, hc₁_mem, c₂, hc₂_mem, ?_⟩
  filter_upwards [hg', (tendsto_id.const_mul_atTop hb.1).eventually_forall_ge_atTop hfg, hfg]
    with x hx₁ hx₂ hx₃
  intro u hu
  rw [hx₂ u hu.1]; rw [hx₃]
  exact hx₁ u hu

中文:
引理 congr_of_eventuallyEq
  条件: {f g : 实数 -> 实数} (hfg : f =ᶠ[atTop] g) (hg : GrowsPolynomially g)
  证明: by
  intro b hb
  have hg' := hg b hb
  obtain ⟨c₁, hc₁_mem, c₂, hc₂_mem, hg'⟩ := hg'
  refine ⟨c₁, hc₁_mem, c₂, hc₂_mem, ?_⟩
  filter_upwards [hg', (tendsto_id.const_mul_atTop hb.1).eventually_forall_ge_atTop hfg, hfg]
    with x hx₁ hx₂ hx₃
  intro u hu
  rw [hx₂ u hu.1]; rw [hx₃]
  exact hx₁ u hu

Depends on / 依赖: const_mul_atTop, eventually_forall_ge_atTop, filter_upwards, tendsto_id, tendsto_id.const_mul_atTop
-/
lemma congr_of_eventuallyEq {f g : Real -> Real} (hfg : f =ᶠ[atTop] g) (hg : GrowsPolynomially g) :
    GrowsPolynomially f := by
  intro b hb
  have hg' := hg b hb
  obtain ⟨c₁, hc₁_mem, c₂, hc₂_mem, hg'⟩ := hg'
  refine ⟨c₁, hc₁_mem, c₂, hc₂_mem, ?_⟩
  filter_upwards [hg', (tendsto_id.const_mul_atTop hb.1).eventually_forall_ge_atTop hfg, hfg]
    with x hx₁ hx₂ hx₃
  intro u hu
  rw [hx₂ u hu.1]; rw [hx₃]
  exact hx₁ u hu

/--
lemma `iff_eventuallyEq` / 引理 `iff_eventuallyEq`

English:
lemma iff_eventuallyEq
  given: {f g : Real -> Real} (h : f =ᶠ[atTop] g)
  proof: ⟨fun hf => congr_of_eventuallyEq h.symm hf, fun hg => congr_of_eventuallyEq h hg⟩

中文:
引理 iff_eventuallyEq
  条件: {f g : 实数 -> 实数} (h : f =ᶠ[atTop] g)
  证明: ⟨fun hf => congr_of_eventuallyEq h.symm hf, fun hg => congr_of_eventuallyEq h hg⟩

Depends on / 依赖: congr_of_eventuallyEq, h.symm
-/
lemma iff_eventuallyEq {f g : Real -> Real} (h : f =ᶠ[atTop] g) :
    GrowsPolynomially f ↔ GrowsPolynomially g :=
  ⟨fun hf => congr_of_eventuallyEq h.symm hf, fun hg => congr_of_eventuallyEq h hg⟩

variable {f : Real -> Real}

/--
lemma `eventually_atTop_le` / 引理 `eventually_atTop_le`

English:
lemma eventually_atTop_le
  given: {b : Real} (hb : b in Set.Ioo 0 1) (hf : GrowsPolynomially f)
  proof: by
  obtain ⟨c₁, _, c₂, hc₂, h⟩ := hf b hb
  refine ⟨c₂, hc₂, ?_⟩
  filter_upwards [h]
  exact fun _ H u hu => (H u hu).2

中文:
引理 eventually_atTop_le
  条件: {b : 实数} (hb : b in 集合.开区间 0 1) (hf : GrowsPolynomially f)
  证明: by
  obtain ⟨c₁, _, c₂, hc₂, h⟩ := hf b hb
  refine ⟨c₂, hc₂, ?_⟩
  filter_upwards [h]
  exact fun _ H u hu => (H u hu).2

Depends on / 依赖: filter_upwards
-/
lemma eventually_atTop_le {b : Real} (hb : b in Set.Ioo 0 1) (hf : GrowsPolynomially f) :
    exists c > 0, forallᶠ x in atTop, forall u in Set.Icc (b * x) x, f u <= c * f x := by
  obtain ⟨c₁, _, c₂, hc₂, h⟩ := hf b hb
  refine ⟨c₂, hc₂, ?_⟩
  filter_upwards [h]
  exact fun _ H u hu => (H u hu).2

/--
lemma `eventually_atTop_le_nat` / 引理 `eventually_atTop_le_nat`

English:
lemma eventually_atTop_le_nat
  given: {b : Real} (hb : b in Set.Ioo 0 1) (hf : GrowsPolynomially f)
  proof: by
  obtain ⟨c, hc_mem, hc⟩ := hf.eventually_atTop_le hb
  exact ⟨c, hc_mem, hc.natCast_atTop⟩

中文:
引理 eventually_atTop_le_nat
  条件: {b : 实数} (hb : b in 集合.开区间 0 1) (hf : GrowsPolynomially f)
  证明: by
  obtain ⟨c, hc_mem, hc⟩ := hf.eventually_atTop_le hb
  exact ⟨c, hc_mem, hc.natCast_atTop⟩

Depends on / 依赖: eventually_atTop_le, hc.natCast_atTop, hc_mem, hf.eventually_atTop_le, natCast_atTop
-/
lemma eventually_atTop_le_nat {b : Real} (hb : b in Set.Ioo 0 1) (hf : GrowsPolynomially f) :
    exists c > 0, forallᶠ (n : Nat) in atTop, forall u in Set.Icc (b * n) n, f u <= c * f n := by
  obtain ⟨c, hc_mem, hc⟩ := hf.eventually_atTop_le hb
  exact ⟨c, hc_mem, hc.natCast_atTop⟩

/--
lemma `eventually_atTop_ge` / 引理 `eventually_atTop_ge`

English:
lemma eventually_atTop_ge
  given: {b : Real} (hb : b in Set.Ioo 0 1) (hf : GrowsPolynomially f)
  proof: by
  obtain ⟨c₁, hc₁, c₂, _, h⟩ := hf b hb
  refine ⟨c₁, hc₁, ?_⟩
  filter_upwards [h]
  exact fun _ H u hu => (H u hu).1

中文:
引理 eventually_atTop_ge
  条件: {b : 实数} (hb : b in 集合.开区间 0 1) (hf : GrowsPolynomially f)
  证明: by
  obtain ⟨c₁, hc₁, c₂, _, h⟩ := hf b hb
  refine ⟨c₁, hc₁, ?_⟩
  filter_upwards [h]
  exact fun _ H u hu => (H u hu).1

Depends on / 依赖: filter_upwards
-/
lemma eventually_atTop_ge {b : Real} (hb : b in Set.Ioo 0 1) (hf : GrowsPolynomially f) :
    exists c > 0, forallᶠ x in atTop, forall u in Set.Icc (b * x) x, c * f x <= f u := by
  obtain ⟨c₁, hc₁, c₂, _, h⟩ := hf b hb
  refine ⟨c₁, hc₁, ?_⟩
  filter_upwards [h]
  exact fun _ H u hu => (H u hu).1

/--
lemma `eventually_atTop_ge_nat` / 引理 `eventually_atTop_ge_nat`

English:
lemma eventually_atTop_ge_nat
  given: {b : Real} (hb : b in Set.Ioo 0 1) (hf : GrowsPolynomially f)
  proof: by
  obtain ⟨c, hc_mem, hc⟩ := hf.eventually_atTop_ge hb
  exact ⟨c, hc_mem, hc.natCast_atTop⟩

中文:
引理 eventually_atTop_ge_nat
  条件: {b : 实数} (hb : b in 集合.开区间 0 1) (hf : GrowsPolynomially f)
  证明: by
  obtain ⟨c, hc_mem, hc⟩ := hf.eventually_atTop_ge hb
  exact ⟨c, hc_mem, hc.natCast_atTop⟩

Depends on / 依赖: eventually_atTop_ge, hc.natCast_atTop, hc_mem, hf.eventually_atTop_ge, natCast_atTop
-/
lemma eventually_atTop_ge_nat {b : Real} (hb : b in Set.Ioo 0 1) (hf : GrowsPolynomially f) :
    exists c > 0, forallᶠ (n : Nat) in atTop, forall u in Set.Icc (b * n) n, c * f n <= f u := by
  obtain ⟨c, hc_mem, hc⟩ := hf.eventually_atTop_ge hb
  exact ⟨c, hc_mem, hc.natCast_atTop⟩

/--
lemma `eventually_zero_of_frequently_zero` / 引理 `eventually_zero_of_frequently_zero`

English:
lemma eventually_zero_of_frequently_zero
  given: (hf : GrowsPolynomially f) (hf' : existsᶠ x in atTop, f x = 0)
  proof: by
  obtain ⟨c₁, hc₁_mem, c₂, hc₂_mem, hf⟩ := hf (1 / 2) (by norm_num)
  rw [frequently_atTop] at hf'
  filter_upwards [eventually_forall_ge_atTop.mpr hf, eventually_gt_atTop 0] with x hx hx_pos
  obtain ⟨x₀, hx₀_ge, hx₀⟩ := hf' (max x 1)
  have x₀_pos := calc
    0 < 1 := by norm_num
    _ <= x₀ :=

中文:
引理 eventually_zero_of_frequently_zero
  条件: (hf : GrowsPolynomially f) (hf' : 存在ᶠ x in atTop, f x = 0)
  证明: by
  obtain ⟨c₁, hc₁_mem, c₂, hc₂_mem, hf⟩ := hf (1 / 2) (by norm_num)
  rw [frequently_atTop] at hf'
  filter_upwards [eventually_forall_ge_atTop.mpr hf, eventually_gt_atTop 0] with x hx hx_pos
  obtain ⟨x₀, hx₀_ge, hx₀⟩ := hf' (max x 1)
  have x₀_pos := calc
    0 < 1 := by norm_num
    _ <= x₀ :=

Depends on / 依赖: Set.Icc, eventually_forall_ge_atTop, eventually_forall_ge_atTop.mpr, eventually_gt_atTop, filter_upwards, frequently_atTop, hx_pos, le_of_max_le_right
-/
lemma eventually_zero_of_frequently_zero (hf : GrowsPolynomially f) (hf' : existsᶠ x in atTop, f x = 0) :
    forallᶠ x in atTop, f x = 0 := by
  obtain ⟨c₁, hc₁_mem, c₂, hc₂_mem, hf⟩ := hf (1 / 2) (by norm_num)
  rw [frequently_atTop] at hf'
  filter_upwards [eventually_forall_ge_atTop.mpr hf, eventually_gt_atTop 0] with x hx hx_pos
  obtain ⟨x₀, hx₀_ge, hx₀⟩ := hf' (max x 1)
  have x₀_pos := calc
    0 < 1 := by norm_num
    _ <= x₀ := le_of_max_le_right hx₀_ge
  have hmain : forall (m : Nat) (z : Real), x <= z ->
      z in Set.Icc ((2 : Real) ^ (-(m : Int) - 1) * x₀) ((2 : Real) ^ (-(m : Int)) * x₀) -> f z = 0 := by
    intro m
    induction m with
    | zero =>
      simp only [CharP.cast_eq_zero, neg_zero, zero_sub, zpow_zero, one_mul] at *
      specialize hx x₀ (le_of_max_le_left hx₀_ge)
      simp only [hx₀, mul_zero, Set.Icc_self, Set.mem_singleton_iff] at hx
      refine fun z _ hz => hx _ ?_
      simp only [zpow_neg, zpow_one] at hz
      simp only [one_div, hz]
    | succ k ih =>
      intro z hxz hz
      simp only [Nat.cast_add, Nat.cast_one] at *
      have hx' : x <= (2 : Real) ^ (-(k : Int) - 1) * x₀ := by
        calc x <= z := hxz
          _ <= _ := by simp only [neg_add, ← sub_eq_add_neg] at hz; exact hz.2
      specialize hx ((2 : Real) ^ (-(k : Int) - 1) * x₀) hx' z
      specialize ih ((2 : Real) ^ (-(k : Int) - 1) * x₀) hx' ?ineq
      case ineq =>
        rw [Set.left_mem_Icc]
        gcongr
        · norm_num
        · lia
      simp only [ih, mul_zero, Set.Icc_self, Set.mem_singleton_iff] at hx
      refine hx ⟨?lb₁, ?ub₁⟩
      case lb₁ =>
        rw [one_div]; rw [← zpow_neg_one]; rw [← mul_assoc]; rw [← zpow_add₀ (by norm_num)]
        have h₁ : (-1 : Int) + (-k - 1) = -k - 2 := by ring
        have h₂ : -(k + (1 : Int)) - 1 = -k - 2 := by ring
        rw [h₁]
        rw [h₂] at hz
        exact hz.1
      case ub₁ =>
        have := hz.2
        simp only [neg_add, ← sub_eq_add_neg] at this
        exact this
  refine hmain ⌊-logb 2 (x / x₀)⌋₊ x le_rfl ⟨?lb, ?ub⟩
  case lb =>
    rw [← le_div_iff₀ x₀_pos]
    refine (logb_le_logb (b := 2) (by norm_num) (zpow_pos (by norm_num) _)
      (by positivity)).mp ?_
    rw [← rpow_intCast]; rw [logb_rpow (by norm_num) (by norm_num)]; rw [← neg_le_neg_iff]
    simp only [Int.cast_sub, Int.cast_neg, Int.cast_natCast, Int.cast_one, neg_sub, sub_neg_eq_add]
    calc -logb 2 (x / x₀) <= ⌈-logb 2 (x / x₀)⌉₊ := Nat.le_ceil (-logb 2 (x / x₀))
         _ <= _ := by rw [add_comm]; exact_mod_cast Nat.ceil_le_floor_add_one _
  case ub =>
    rw [← div_le_iff₀ x₀_pos]
    refine (logb_le_logb (b := 2) (by norm_num) (by positivity)
      (zpow_pos (by norm_num) _)).mp ?_
    rw [← rpow_intCast]; rw [logb_rpow (by norm_num) (by norm_num)]; rw [← neg_le_neg_iff]
    simp only [Int.cast_neg, Int.cast_natCast, neg_neg]
    have : 0 <= -logb 2 (x / x₀) := by
      rw [neg_nonneg]
      refine logb_nonpos (by norm_num) (by positivity) ?_
      rw [div_le_one x₀_pos]
      exact le_of_max_le_left hx₀_ge
    exact_mod_cast Nat.floor_le this

/--
lemma `eventually_atTop_nonneg_or_nonpos` / 引理 `eventually_atTop_nonneg_or_nonpos`

English:
lemma eventually_atTop_nonneg_or_nonpos
  given: (hf : GrowsPolynomially f)
  proof: by
  obtain ⟨c₁, _, c₂, _, h⟩ := hf (1 / 2) (by norm_num)
  match lt_trichotomy c₁ c₂ with
  | .inl hlt => -- c₁ < c₂
    left
    filter_upwards [h, eventually_ge_atTop 0] with x hx hx_nonneg
    have h' : 3 / 4 * x in Set.Icc (1 / 2 * x) x := by
      rw [Set.mem_Icc]
      exact ⟨by gcongr ?_ * x

中文:
引理 eventually_atTop_nonneg_or_nonpos
  条件: (hf : GrowsPolynomially f)
  证明: by
  obtain ⟨c₁, _, c₂, _, h⟩ := hf (1 / 2) (by norm_num)
  match lt_trichotomy c₁ c₂ with
  | .inl hlt => -- c₁ < c₂
    left
    filter_upwards [h, eventually_ge_atTop 0] with x hx hx_nonneg
    have h' : 3 / 4 * x in Set.Icc (1 / 2 * x) x := by
      rw [Set.mem_Icc]
      exact ⟨by gcongr ?_ * x

Depends on / 依赖: Set.Icc, Set.mem_Icc, Set.nonempty_Icc, Set.nonempty_of_mem, eventually_ge_atTop, filter_upwards, hx_nonneg, lt_trichotomy, mem_Icc, nonempty_Icc, nonempty_of_mem, nonneg_of_mul_nonneg_right
-/
lemma eventually_atTop_nonneg_or_nonpos (hf : GrowsPolynomially f) :
    (forallᶠ x in atTop, 0 <= f x) ∨ (forallᶠ x in atTop, f x <= 0) := by
  obtain ⟨c₁, _, c₂, _, h⟩ := hf (1 / 2) (by norm_num)
  match lt_trichotomy c₁ c₂ with
  | .inl hlt => -- c₁ < c₂
    left
    filter_upwards [h, eventually_ge_atTop 0] with x hx hx_nonneg
    have h' : 3 / 4 * x in Set.Icc (1 / 2 * x) x := by
      rw [Set.mem_Icc]
      exact ⟨by gcongr ?_ * x; norm_num, by linarith⟩
    have hu := hx (3 / 4 * x) h'
    have hu := Set.nonempty_of_mem hu
    rw [Set.nonempty_Icc] at hu
    have hu' : 0 <= (c₂ - c₁) * f x := by linarith
    exact nonneg_of_mul_nonneg_right hu' (by linarith)
  | .inr (.inr hgt) => -- c₂ < c₁
    right
    filter_upwards [h, eventually_ge_atTop 0] with x hx hx_nonneg
    have h' : 3 / 4 * x in Set.Icc (1 / 2 * x) x := by
      rw [Set.mem_Icc]
      exact ⟨by gcongr ?_ * x; norm_num, by linarith⟩
    have hu := hx (3 / 4 * x) h'
    have hu := Set.nonempty_of_mem hu
    rw [Set.nonempty_Icc] at hu
    have hu' : (c₁ - c₂) * f x <= 0 := by linarith
    exact nonpos_of_mul_nonpos_right hu' (by linarith)
  | .inr (.inl heq) => -- c₁ = c₂
    have hmain : exists c, forallᶠ x in atTop, f x = c := by
      simp only [heq, Set.Icc_self, Set.mem_singleton_iff] at h
      rw [eventually_atTop] at h
      obtain ⟨n₀, hn₀⟩ := h
      refine ⟨f (max n₀ 2), ?_⟩
      rw [eventually_atTop]
      refine ⟨max n₀ 2, ?_⟩
      refine Real.induction_Ico_mul _ 2 (by norm_num) (by positivity) ?base ?step
      case base => grind
      case step =>
        intro n _ _ z _
        have le_2n : max n₀ 2 <= (2 : Real) ^ n * max n₀ 2 := by
          simp [one_le_pow₀ (show (1 : Real) <= 2 by norm_num1)]
        have half_z_to_base : f (1 / 2 * z) = f (max n₀ 2) := by
          grind [mul_assoc]
        grind
    obtain ⟨c, hc⟩ := hmain
    cases le_or_gt 0 c with
    | inl hpos =>
exact Or.inl by filter_upwards [hc] with _ hc; simpa only [hc]
    | inr hneg =>
      right
      filter_upwards [hc] with x hc
exact le_of_lt by simpa only [hc]

/--
lemma `eventually_atTop_zero_or_pos_or_neg` / 引理 `eventually_atTop_zero_or_pos_or_neg`

English:
lemma eventually_atTop_zero_or_pos_or_neg
  given: (hf : GrowsPolynomially f)
  proof: by
  by_cases! h : existsᶠ x in atTop, f x = 0
· exact Or.inl eventually_zero_of_frequently_zero hf h
  · cases eventually_atTop_nonneg_or_nonpos hf with
    | inl h' =>
      refine Or.inr (Or.inl ?_)
      simp only [lt_iff_le_and_ne]
      rw [eventually_and]
      exact ⟨h', by filter_upwards [h

中文:
引理 eventually_atTop_zero_or_pos_or_neg
  条件: (hf : GrowsPolynomially f)
  证明: by
  by_cases! h : existsᶠ x in atTop, f x = 0
· exact Or.inl eventually_zero_of_frequently_zero hf h
  · cases eventually_atTop_nonneg_or_nonpos hf with
    | inl h' =>
      refine Or.inr (Or.inl ?_)
      simp only [lt_iff_le_and_ne]
      rw [eventually_and]
      exact ⟨h', by filter_upwards [h

Depends on / 依赖: Or.inl, Or.inr, eventually_and, eventually_atTop_nonneg_or_nonpos, eventually_zero_of_frequently_zero, filter_upwards, hx.symm, lt_iff_le_and_ne
-/
lemma eventually_atTop_zero_or_pos_or_neg (hf : GrowsPolynomially f) :
    (forallᶠ x in atTop, f x = 0) ∨ (forallᶠ x in atTop, 0 < f x) ∨ (forallᶠ x in atTop, f x < 0) := by
  by_cases! h : existsᶠ x in atTop, f x = 0
· exact Or.inl eventually_zero_of_frequently_zero hf h
  · cases eventually_atTop_nonneg_or_nonpos hf with
    | inl h' =>
      refine Or.inr (Or.inl ?_)
      simp only [lt_iff_le_and_ne]
      rw [eventually_and]
      exact ⟨h', by filter_upwards [h] with x hx; exact hx.symm⟩
    | inr h' =>
      refine Or.inr (Or.inr ?_)
      simp only [lt_iff_le_and_ne]
      rw [eventually_and]
      exact ⟨h', h⟩

/--
lemma `neg` / 引理 `neg`

English:
lemma neg
  given: {f : Real -> Real} (hf : GrowsPolynomially f)
  statement: GrowsPolynomially (-f)
  proof: by
  intro b hb
  obtain ⟨c₁, hc₁_mem, c₂, hc₂_mem, hf⟩ := hf b hb
  refine ⟨c₂, hc₂_mem, c₁, hc₁_mem, ?_⟩
  filter_upwards [hf] with x hx
  intro u hu
  simp only [Pi.neg_apply, Set.neg_mem_Icc_iff, neg_mul_eq_mul_neg, neg_neg]
  exact hx u hu

中文:
引理 neg
  条件: {f : 实数 -> 实数} (hf : GrowsPolynomially f)
  结论: GrowsPolynomially (-f)
  证明: by
  intro b hb
  obtain ⟨c₁, hc₁_mem, c₂, hc₂_mem, hf⟩ := hf b hb
  refine ⟨c₂, hc₂_mem, c₁, hc₁_mem, ?_⟩
  filter_upwards [hf] with x hx
  intro u hu
  simp only [Pi.neg_apply, Set.neg_mem_Icc_iff, neg_mul_eq_mul_neg, neg_neg]
  exact hx u hu
-/
protected lemma neg {f : Real -> Real} (hf : GrowsPolynomially f) : GrowsPolynomially (-f) := by
  intro b hb
  obtain ⟨c₁, hc₁_mem, c₂, hc₂_mem, hf⟩ := hf b hb
  refine ⟨c₂, hc₂_mem, c₁, hc₁_mem, ?_⟩
  filter_upwards [hf] with x hx
  intro u hu
  simp only [Pi.neg_apply, Set.neg_mem_Icc_iff, neg_mul_eq_mul_neg, neg_neg]
  exact hx u hu

/--
lemma `neg_iff` / 引理 `neg_iff`

English:
lemma neg_iff
  given: {f : Real -> Real}
  statement: GrowsPolynomially f ↔ GrowsPolynomially (-f)
  proof: ⟨fun hf => hf.neg, fun hf => by rw [← neg_neg f]; exact hf.neg⟩

中文:
引理 neg_iff
  条件: {f : 实数 -> 实数}
  结论: GrowsPolynomially f ↔ GrowsPolynomially (-f)
  证明: ⟨fun hf => hf.neg, fun hf => by rw [← neg_neg f]; exact hf.neg⟩
-/
protected lemma neg_iff {f : Real -> Real} : GrowsPolynomially f ↔ GrowsPolynomially (-f) :=
  ⟨fun hf => hf.neg, fun hf => by rw [← neg_neg f]; exact hf.neg⟩

/--
lemma `abs` / 引理 `abs`

English:
lemma abs
  given: (hf : GrowsPolynomially f)
  statement: GrowsPolynomially (fun x => |f x|)
  proof: by
  cases eventually_atTop_nonneg_or_nonpos hf with
  | inl hf' =>
    have hmain : f =ᶠ[atTop] fun x => |f x| := by
      filter_upwards [hf'] with x hx
      rw [abs_of_nonneg hx]
    rw [← iff_eventuallyEq hmain]
    exact hf
  | inr hf' =>
    have hmain : -f =ᶠ[atTop] fun x => |f x| := by
    

中文:
引理 abs
  条件: (hf : GrowsPolynomially f)
  结论: GrowsPolynomially (fun x => |f x|)
  证明: by
  cases eventually_atTop_nonneg_or_nonpos hf with
  | inl hf' =>
    have hmain : f =ᶠ[atTop] fun x => |f x| := by
      filter_upwards [hf'] with x hx
      rw [abs_of_nonneg hx]
    rw [← iff_eventuallyEq hmain]
    exact hf
  | inr hf' =>
    have hmain : -f =ᶠ[atTop] fun x => |f x| := by
    
-/
protected lemma abs (hf : GrowsPolynomially f) : GrowsPolynomially (fun x => |f x|) := by
  cases eventually_atTop_nonneg_or_nonpos hf with
  | inl hf' =>
    have hmain : f =ᶠ[atTop] fun x => |f x| := by
      filter_upwards [hf'] with x hx
      rw [abs_of_nonneg hx]
    rw [← iff_eventuallyEq hmain]
    exact hf
  | inr hf' =>
    have hmain : -f =ᶠ[atTop] fun x => |f x| := by
      filter_upwards [hf'] with x hx
      simp only [Pi.neg_apply, abs_of_nonpos hx]
    rw [← iff_eventuallyEq hmain]
    exact hf.neg

/--
lemma `norm` / 引理 `norm`

English:
lemma norm
  given: (hf : GrowsPolynomially f)
  statement: GrowsPolynomially (fun x => ‖f x‖)
  proof: by
  simp only [norm_eq_abs]
  exact hf.abs

中文:
引理 norm
  条件: (hf : GrowsPolynomially f)
  结论: GrowsPolynomially (fun x => ‖f x‖)
  证明: by
  simp only [norm_eq_abs]
  exact hf.abs
-/
protected lemma norm (hf : GrowsPolynomially f) : GrowsPolynomially (fun x => ‖f x‖) := by
  simp only [norm_eq_abs]
  exact hf.abs

end GrowsPolynomially

variable {f : Real -> Real}

/--
lemma `growsPolynomially_const` / 引理 `growsPolynomially_const`

English:
lemma growsPolynomially_const
  given: {c : Real}
  statement: GrowsPolynomially (fun _ => c)
  proof: by
  refine fun _ _ => ⟨1, by norm_num, 1, by norm_num, ?_⟩
  filter_upwards [] with x
  simp

中文:
引理 growsPolynomially_const
  条件: {c : 实数}
  结论: GrowsPolynomially (fun _ => c)
  证明: by
  refine fun _ _ => ⟨1, by norm_num, 1, by norm_num, ?_⟩
  filter_upwards [] with x
  simp

Depends on / 依赖: filter_upwards
-/
lemma growsPolynomially_const {c : Real} : GrowsPolynomially (fun _ => c) := by
  refine fun _ _ => ⟨1, by norm_num, 1, by norm_num, ?_⟩
  filter_upwards [] with x
  simp

/--
lemma `growsPolynomially_id` / 引理 `growsPolynomially_id`

English:
lemma growsPolynomially_id
  statement: GrowsPolynomially (fun x => x)
  proof: by
  intro b hb
  refine ⟨b, hb.1, ?_⟩
  refine ⟨1, by norm_num, ?_⟩
  filter_upwards with x u hu
  simp only [one_mul, Set.mem_Icc]
  exact ⟨hu.1, hu.2⟩

中文:
引理 growsPolynomially_id
  结论: GrowsPolynomially (fun x => x)
  证明: by
  intro b hb
  refine ⟨b, hb.1, ?_⟩
  refine ⟨1, by norm_num, ?_⟩
  filter_upwards with x u hu
  simp only [one_mul, Set.mem_Icc]
  exact ⟨hu.1, hu.2⟩

Depends on / 依赖: Set.mem_Icc, filter_upwards, mem_Icc, one_mul
-/
lemma growsPolynomially_id : GrowsPolynomially (fun x => x) := by
  intro b hb
  refine ⟨b, hb.1, ?_⟩
  refine ⟨1, by norm_num, ?_⟩
  filter_upwards with x u hu
  simp only [one_mul, Set.mem_Icc]
  exact ⟨hu.1, hu.2⟩

/--
lemma `GrowsPolynomially.mul` / 引理 `GrowsPolynomially.mul`

English:
lemma GrowsPolynomially.mul
  statement: {f g : Real -> Real} (hf : GrowsPolynomially f)
  proof: by
  suffices GrowsPolynomially fun x => |f x| * |g x| by
    cases eventually_atTop_nonneg_or_nonpos hf with
    | inl hf' =>
      cases eventually_atTop_nonneg_or_nonpos hg with
      | inl hg' =>
        have hmain : (fun x => f x * g x) =ᶠ[atTop] fun x => |f x| * |g x| := by
          filter_up

中文:
引理 GrowsPolynomially.mul
  结论: {f g : 实数 -> 实数} (hf : GrowsPolynomially f)
  证明: by
  suffices GrowsPolynomially fun x => |f x| * |g x| by
    cases eventually_atTop_nonneg_or_nonpos hf with
    | inl hf' =>
      cases eventually_atTop_nonneg_or_nonpos hg with
      | inl hg' =>
        have hmain : (fun x => f x * g x) =ᶠ[atTop] fun x => |f x| * |g x| := by
          filter_up
-/
protected lemma GrowsPolynomially.mul {f g : Real -> Real} (hf : GrowsPolynomially f)
    (hg : GrowsPolynomially g) : GrowsPolynomially fun x => f x * g x := by
  suffices GrowsPolynomially fun x => |f x| * |g x| by
    cases eventually_atTop_nonneg_or_nonpos hf with
    | inl hf' =>
      cases eventually_atTop_nonneg_or_nonpos hg with
      | inl hg' =>
        have hmain : (fun x => f x * g x) =ᶠ[atTop] fun x => |f x| * |g x| := by
          filter_upwards [hf', hg'] with x hx₁ hx₂
          rw [abs_of_nonneg hx₁]; rw [abs_of_nonneg hx₂]
        rwa [iff_eventuallyEq hmain]
      | inr hg' =>
        have hmain : (fun x => f x * g x) =ᶠ[atTop] fun x => -|f x| * |g x| := by
          filter_upwards [hf', hg'] with x hx₁ hx₂
          simp [abs_of_nonneg hx₁, abs_of_nonpos hx₂]
        simp only [iff_eventuallyEq hmain, neg_mul]
        exact this.neg
    | inr hf' =>
      cases eventually_atTop_nonneg_or_nonpos hg with
      | inl hg' =>
        have hmain : (fun x => f x * g x) =ᶠ[atTop] fun x => -|f x| * |g x| := by
          filter_upwards [hf', hg'] with x hx₁ hx₂
          rw [abs_of_nonpos hx₁]; rw [abs_of_nonneg hx₂]; rw [neg_neg]
        simp only [iff_eventuallyEq hmain, neg_mul]
        exact this.neg
      | inr hg' =>
        have hmain : (fun x => f x * g x) =ᶠ[atTop] fun x => |f x| * |g x| := by
          filter_upwards [hf', hg'] with x hx₁ hx₂
          simp [abs_of_nonpos hx₁, abs_of_nonpos hx₂]
        simp only [iff_eventuallyEq hmain]
        exact this
  intro b hb
  have hf := hf.abs b hb
  have hg := hg.abs b hb
  obtain ⟨c₁, hc₁_mem, c₂, hc₂_mem, hf⟩ := hf
  obtain ⟨c₃, hc₃_mem, c₄, hc₄_mem, hg⟩ := hg
  refine ⟨c₁ * c₃, by change 0 < c₁ * c₃; positivity, ?_⟩
  refine ⟨c₂ * c₄, by change 0 < c₂ * c₄; positivity, ?_⟩
  filter_upwards [hf, hg] with x hf hg
  intro u hu
  refine ⟨?lb, ?ub⟩
  case lb => calc
    c₁ * c₃ * (|f x| * |g x|) = (c₁ * |f x|) * (c₃ * |g x|) := by ring
    _ <= |f u| * |g u| := by
           gcongr
           · exact (hf u hu).1
           · exact (hg u hu).1
  case ub => calc
    |f u| * |g u| <= (c₂ * |f x|) * (c₄ * |g x|) := by
           gcongr
           · exact (hf u hu).2
           · exact (hg u hu).2
    _ = c₂ * c₄ * (|f x| * |g x|) := by ring

/--
lemma `GrowsPolynomially.const_mul` / 引理 `GrowsPolynomially.const_mul`

English:
lemma GrowsPolynomially.const_mul
  given: {f : Real -> Real} {c : Real} (hf : GrowsPolynomially f)
  proof: GrowsPolynomially.mul growsPolynomially_const hf

中文:
引理 GrowsPolynomially.const_mul
  条件: {f : 实数 -> 实数} {c : 实数} (hf : GrowsPolynomially f)
  证明: GrowsPolynomially.mul growsPolynomially_const hf

Depends on / 依赖: GrowsPolynomially, GrowsPolynomially.mul, growsPolynomially_const
-/
lemma GrowsPolynomially.const_mul {f : Real -> Real} {c : Real} (hf : GrowsPolynomially f) :
    GrowsPolynomially fun x => c * f x :=
  GrowsPolynomially.mul growsPolynomially_const hf

/--
lemma `GrowsPolynomially.add` / 引理 `GrowsPolynomially.add`

English:
lemma GrowsPolynomially.add
  statement: {f g : Real -> Real} (hf : GrowsPolynomially f)
  proof: by
  intro b hb
  have hf := hf b hb
  have hg := hg b hb
  obtain ⟨c₁, hc₁_mem, c₂, hc₂_mem, hf⟩ := hf
  obtain ⟨c₃, hc₃_mem, c₄, _, hg⟩ := hg
  refine ⟨min c₁ c₃, by change 0 < min c₁ c₃; positivity, ?_⟩
  refine ⟨max c₂ c₄, by change 0 < max c₂ c₄; positivity, ?_⟩
  filter_upwards [hf, hg,
      

中文:
引理 GrowsPolynomially.add
  结论: {f g : 实数 -> 实数} (hf : GrowsPolynomially f)
  证明: by
  intro b hb
  have hf := hf b hb
  have hg := hg b hb
  obtain ⟨c₁, hc₁_mem, c₂, hc₂_mem, hf⟩ := hf
  obtain ⟨c₃, hc₃_mem, c₄, _, hg⟩ := hg
  refine ⟨min c₁ c₃, by change 0 < min c₁ c₃; positivity, ?_⟩
  refine ⟨max c₂ c₄, by change 0 < max c₂ c₄; positivity, ?_⟩
  filter_upwards [hf, hg,
      
-/
protected lemma GrowsPolynomially.add {f g : Real -> Real} (hf : GrowsPolynomially f)
    (hg : GrowsPolynomially g) (hf' : 0 <=ᶠ[atTop] f) (hg' : 0 <=ᶠ[atTop] g) :
    GrowsPolynomially fun x => f x + g x := by
  intro b hb
  have hf := hf b hb
  have hg := hg b hb
  obtain ⟨c₁, hc₁_mem, c₂, hc₂_mem, hf⟩ := hf
  obtain ⟨c₃, hc₃_mem, c₄, _, hg⟩ := hg
  refine ⟨min c₁ c₃, by change 0 < min c₁ c₃; positivity, ?_⟩
  refine ⟨max c₂ c₄, by change 0 < max c₂ c₄; positivity, ?_⟩
  filter_upwards [hf, hg,
                  (tendsto_id.const_mul_atTop hb.1).eventually_forall_ge_atTop hf',
                  (tendsto_id.const_mul_atTop hb.1).eventually_forall_ge_atTop hg',
                  eventually_ge_atTop 0] with x hf hg hf' hg' hx_pos
  intro u hu
  have hbx : b * x <= x := calc
    b * x <= 1 * x := by gcongr; exact le_of_lt hb.2
        _ = x := by ring
  have fx_nonneg : 0 <= f x := hf' x hbx
  have gx_nonneg : 0 <= g x := hg' x hbx
  refine ⟨?lb, ?ub⟩
  case lb => calc
    min c₁ c₃ * (f x + g x) = min c₁ c₃ * f x + min c₁ c₃ * g x := by simp only [mul_add]
      _ <= c₁ * f x + c₃ * g x := by
              gcongr
              · exact min_le_left _ _
              · exact min_le_right _ _
      _ <= f u + g u := by
              gcongr
              · exact (hf u hu).1
              · exact (hg u hu).1
  case ub => calc
    max c₂ c₄ * (f x + g x) = max c₂ c₄ * f x + max c₂ c₄ * g x := by simp only [mul_add]
      _ >= c₂ * f x + c₄ * g x := by gcongr
                                    · exact le_max_left _ _
                                    · exact le_max_right _ _
      _ >= f u + g u := by gcongr
                          · exact (hf u hu).2
                          · exact (hg u hu).2

/--
lemma `GrowsPolynomially.add_isLittleO` / 引理 `GrowsPolynomially.add_isLittleO`

English:
lemma GrowsPolynomially.add_isLittleO
  statement: {f g : Real -> Real} (hf : GrowsPolynomially f)
  proof: by
  intro b hb
  have hb_ub := hb.2
  rw [isLittleO_iff] at hfg
  cases hf.eventually_atTop_nonneg_or_nonpos with
  | inl hf' => -- f is eventually non-negative
    have hf := hf b hb
    obtain ⟨c₁, hc₁_mem : 0 < c₁, c₂, hc₂_mem : 0 < c₂, hf⟩ := hf
    specialize hfg (c := 1 / 2) (by norm_num)
   

中文:
引理 GrowsPolynomially.add_isLittleO
  结论: {f g : 实数 -> 实数} (hf : GrowsPolynomially f)
  证明: by
  intro b hb
  have hb_ub := hb.2
  rw [isLittleO_iff] at hfg
  cases hf.eventually_atTop_nonneg_or_nonpos with
  | inl hf' => -- f is eventually non-negative
    have hf := hf b hb
    obtain ⟨c₁, hc₁_mem : 0 < c₁, c₂, hc₂_mem : 0 < c₂, hf⟩ := hf
    specialize hfg (c := 1 / 2) (by norm_num)
   

Depends on / 依赖: const_mul_atTop, eventually, eventually_atTop_nonneg_or_nonpos, eventually_forall_ge_atTop, eventually_ge_atT, filter_upwards, hb_ub, hf.eventually_atTop_nonneg_or_nonpos, isLittleO_iff, negative, specialize, tendsto_id, tendsto_id.const_mul_atTop
-/
lemma GrowsPolynomially.add_isLittleO {f g : Real -> Real} (hf : GrowsPolynomially f)
    (hfg : g =o[atTop] f) : GrowsPolynomially fun x => f x + g x := by
  intro b hb
  have hb_ub := hb.2
  rw [isLittleO_iff] at hfg
  cases hf.eventually_atTop_nonneg_or_nonpos with
  | inl hf' => -- f is eventually non-negative
    have hf := hf b hb
    obtain ⟨c₁, hc₁_mem : 0 < c₁, c₂, hc₂_mem : 0 < c₂, hf⟩ := hf
    specialize hfg (c := 1 / 2) (by norm_num)
    refine ⟨c₁ / 3, by positivity, 3*c₂, by positivity, ?_⟩
    filter_upwards [hf,
                    (tendsto_id.const_mul_atTop hb.1).eventually_forall_ge_atTop hfg,
                    (tendsto_id.const_mul_atTop hb.1).eventually_forall_ge_atTop hf',
                    eventually_ge_atTop 0] with x hf₁ hfg' hf₂ hx_nonneg
    have hbx : b * x <= x := by nth_rewrite 2 [← one_mul x]; gcongr
    have hfg₂ : ‖g x‖ <= 1 / 2 * f x := by
      calc ‖g x‖ <= 1 / 2 * ‖f x‖ := hfg' x hbx
           _ = 1 / 2 * f x := by congr; exact norm_of_nonneg (hf₂ _ hbx)
    have hx_ub : f x + g x <= 3 / 2 * f x := by
      calc _ <= f x + ‖g x‖ := by gcongr; exact le_norm_self (g x)
           _ <= f x + 1 / 2 * f x := by gcongr
           _ = 3 / 2 * f x := by ring
    have hx_lb : 1 / 2 * f x <= f x + g x := by
      calc f x + g x >= f x - ‖g x‖ := by
                rw [sub_eq_add_neg]; rw [norm_eq_abs]; gcongr; exact neg_abs_le (g x)
           _ >= f x - 1 / 2 * f x := by gcongr
           _ = 1 / 2 * f x := by ring
    intro u ⟨hu_lb, hu_ub⟩
    have hfu_nonneg : 0 <= f u := hf₂ _ hu_lb
    have hfg₃ : ‖g u‖ <= 1 / 2 * f u := by
      calc ‖g u‖ <= 1 / 2 * ‖f u‖ := hfg' _ hu_lb
           _ = 1 / 2 * f u := by congr; simp only [norm_eq_abs, abs_eq_self, hfu_nonneg]
    refine ⟨?lb, ?ub⟩
    case lb =>
      calc f u + g u >= f u - ‖g u‖ := by
                  rw [sub_eq_add_neg]; rw [norm_eq_abs]; gcongr; exact neg_abs_le _
           _ >= f u - 1 / 2 * f u := by gcongr
           _ = 1 / 2 * f u := by ring
           _ >= 1 / 2 * (c₁ * f x) := by gcongr; exact (hf₁ u ⟨hu_lb, hu_ub⟩).1
           _ = c₁ / 3 * (3 / 2 * f x) := by ring
           _ >= c₁ / 3 * (f x + g x) := by gcongr
    case ub =>
      calc _ <= f u + ‖g u‖ := by gcongr; exact le_norm_self (g u)
           _ <= f u + 1 / 2 * f u := by gcongr
           _ = 3 / 2 * f u := by ring
           _ <= 3 / 2 * (c₂ * f x) := by gcongr; exact (hf₁ u ⟨hu_lb, hu_ub⟩).2
           _ = 3 * c₂ * (1 / 2 * f x) := by ring
           _ <= 3 * c₂ * (f x + g x) := by gcongr
  | inr hf' => -- f is eventually nonpos
    have hf := hf b hb
    obtain ⟨c₁, hc₁_mem : 0 < c₁, c₂, hc₂_mem : 0 < c₂, hf⟩ := hf
    specialize hfg (c := 1 / 2) (by norm_num)
    refine ⟨3*c₁, by positivity, c₂/3, by positivity, ?_⟩
    filter_upwards [hf,
                    (tendsto_id.const_mul_atTop hb.1).eventually_forall_ge_atTop hfg,
                    (tendsto_id.const_mul_atTop hb.1).eventually_forall_ge_atTop hf',
                    eventually_ge_atTop 0] with x hf₁ hfg' hf₂ hx_nonneg
    have hbx : b * x <= x := by nth_rewrite 2 [← one_mul x]; gcongr
    have hfg₂ : ‖g x‖ <= -1 / 2 * f x := by
      calc ‖g x‖ <= 1 / 2 * ‖f x‖ := hfg' x hbx
           _ = 1 / 2 * (-f x) := by congr; exact norm_of_nonpos (hf₂ x hbx)
           _ = _ := by ring
    have hx_ub : f x + g x <= 1 / 2 * f x := by
      calc _ <= f x + ‖g x‖ := by gcongr; exact le_norm_self (g x)
           _ <= f x + (-1 / 2 * f x) := by gcongr
           _ = 1 / 2 * f x := by ring
    have hx_lb : 3 / 2 * f x <= f x + g x := by
      calc f x + g x >= f x - ‖g x‖ := by
                rw [sub_eq_add_neg]; rw [norm_eq_abs]; gcongr; exact neg_abs_le (g x)
           _ >= f x + 1 / 2 * f x := by
                  rw [sub_eq_add_neg]
                  gcongr
                  refine le_of_neg_le_neg ?bc.a
                  rwa [neg_neg, ← neg_mul, ← neg_div]
           _ = 3 / 2 * f x := by ring
    intro u ⟨hu_lb, hu_ub⟩
    have hfu_nonpos : f u <= 0 := hf₂ _ hu_lb
    have hfg₃ : ‖g u‖ <= -1 / 2 * f u := by
      calc ‖g u‖ <= 1 / 2 * ‖f u‖ := hfg' _ hu_lb
           _ = 1 / 2 * (-f u) := by congr; exact norm_of_nonpos hfu_nonpos
           _ = -1 / 2 * f u := by ring
    refine ⟨?lb, ?ub⟩
    case lb =>
      calc f u + g u >= f u - ‖g u‖ := by
                  rw [sub_eq_add_neg]; rw [norm_eq_abs]; gcongr; exact neg_abs_le _
           _ >= f u + 1 / 2 * f u := by
                  rw [sub_eq_add_neg]
                  gcongr
                  refine le_of_neg_le_neg ?_
                  rwa [neg_neg, ← neg_mul, ← neg_div]
           _ = 3 / 2 * f u := by ring
           _ >= 3 / 2 * (c₁ * f x) := by gcongr; exact (hf₁ u ⟨hu_lb, hu_ub⟩).1
           _ = 3 * c₁ * (1 / 2 * f x) := by ring
           _ >= 3 * c₁ * (f x + g x) := by gcongr
    case ub =>
      calc _ <= f u + ‖g u‖ := by gcongr; exact le_norm_self (g u)
           _ <= f u - 1 / 2 * f u := by
                rw [sub_eq_add_neg]
                gcongr
                rwa [← neg_mul, ← neg_div]
           _ = 1 / 2 * f u := by ring
           _ <= 1 / 2 * (c₂ * f x) := by gcongr; exact (hf₁ u ⟨hu_lb, hu_ub⟩).2
           _ = c₂ / 3 * (3 / 2 * f x) := by ring
           _ <= c₂ / 3 * (f x + g x) := by gcongr

/--
lemma `GrowsPolynomially.inv` / 引理 `GrowsPolynomially.inv`

English:
lemma GrowsPolynomially.inv
  given: {f : Real -> Real} (hf : GrowsPolynomially f)
  proof: by
  cases hf.eventually_atTop_zero_or_pos_or_neg with
  | inl hf' =>
    refine fun b hb => ⟨1, by simp, 1, by simp, ?_⟩
    have hb_pos := hb.1
    filter_upwards [hf', (tendsto_id.const_mul_atTop hb_pos).eventually_forall_ge_atTop hf']
      with x hx hx'
    intro u hu
    simp only [hx, inv_zer

中文:
引理 GrowsPolynomially.inv
  条件: {f : 实数 -> 实数} (hf : GrowsPolynomially f)
  证明: by
  cases hf.eventually_atTop_zero_or_pos_or_neg with
  | inl hf' =>
    refine fun b hb => ⟨1, by simp, 1, by simp, ?_⟩
    have hb_pos := hb.1
    filter_upwards [hf', (tendsto_id.const_mul_atTop hb_pos).eventually_forall_ge_atTop hf']
      with x hx hx'
    intro u hu
    simp only [hx, inv_zer
-/
protected lemma GrowsPolynomially.inv {f : Real -> Real} (hf : GrowsPolynomially f) :
    GrowsPolynomially fun x => (f x)⁻¹ := by
  cases hf.eventually_atTop_zero_or_pos_or_neg with
  | inl hf' =>
    refine fun b hb => ⟨1, by simp, 1, by simp, ?_⟩
    have hb_pos := hb.1
    filter_upwards [hf', (tendsto_id.const_mul_atTop hb_pos).eventually_forall_ge_atTop hf']
      with x hx hx'
    intro u hu
    simp only [hx, inv_zero, mul_zero, Set.Icc_self, Set.mem_singleton_iff, hx' u hu.1]
  | inr hf_pos_or_neg =>
    suffices GrowsPolynomially fun x => |(f x)⁻¹| by
      cases hf_pos_or_neg with
      | inl hf' =>
        have hmain : (fun x => (f x)⁻¹) =ᶠ[atTop] fun x => |(f x)⁻¹| := by
          filter_upwards [hf'] with x hx₁
          rw [abs_of_nonneg (inv_nonneg_of_nonneg (le_of_lt hx₁))]
        rwa [iff_eventuallyEq hmain]
      | inr hf' =>
        have hmain : (fun x => (f x)⁻¹) =ᶠ[atTop] fun x => -|(f x)⁻¹| := by
          filter_upwards [hf'] with x hx₁
          simp [abs_of_nonpos (inv_nonpos.mpr (le_of_lt hx₁))]
        rw [iff_eventuallyEq hmain]
        exact this.neg
    have hf' : forallᶠ x in atTop, f x != 0 := by
      cases hf_pos_or_neg with
      | inl H => filter_upwards [H] with _ hx; exact (ne_of_lt hx).symm
      | inr H => filter_upwards [H] with _ hx; exact (ne_of_gt hx).symm
    simp only [abs_inv]
    have hf := hf.abs
    intro b hb
    have hb_pos := hb.1
    obtain ⟨c₁, hc₁_mem, c₂, hc₂_mem, hf⟩ := hf b hb
    refine ⟨c₂⁻¹, by change 0 < c₂⁻¹; positivity, ?_⟩
    refine ⟨c₁⁻¹, by change 0 < c₁⁻¹; positivity, ?_⟩
    filter_upwards [hf, hf', (tendsto_id.const_mul_atTop hb_pos).eventually_forall_ge_atTop hf']
      with x hx hx' hx''
    intro u hu
    have h₁ : 0 < |f u| := by rw [abs_pos]; exact hx'' u hu.1
    refine ⟨?lb, ?ub⟩
    case lb =>
      rw [← mul_inv]
      gcongr
      exact (hx u hu).2
    case ub =>
      rw [← mul_inv]
      gcongr
      exact (hx u hu).1

/--
lemma `GrowsPolynomially.div` / 引理 `GrowsPolynomially.div`

English:
lemma GrowsPolynomially.div
  statement: {f g : Real -> Real} (hf : GrowsPolynomially f)
  proof: by
  have : (fun x => f x / g x) = fun x => f x * (g x)⁻¹ := by ext; rw [div_eq_mul_inv]
  rw [this]
  exact GrowsPolynomially.mul hf (GrowsPolynomially.inv hg)

中文:
引理 GrowsPolynomially.div
  结论: {f g : 实数 -> 实数} (hf : GrowsPolynomially f)
  证明: by
  have : (fun x => f x / g x) = fun x => f x * (g x)⁻¹ := by ext; rw [div_eq_mul_inv]
  rw [this]
  exact GrowsPolynomially.mul hf (GrowsPolynomially.inv hg)
-/
protected lemma GrowsPolynomially.div {f g : Real -> Real} (hf : GrowsPolynomially f)
    (hg : GrowsPolynomially g) : GrowsPolynomially fun x => f x / g x := by
  have : (fun x => f x / g x) = fun x => f x * (g x)⁻¹ := by ext; rw [div_eq_mul_inv]
  rw [this]
  exact GrowsPolynomially.mul hf (GrowsPolynomially.inv hg)

/--
lemma `GrowsPolynomially.rpow` / 引理 `GrowsPolynomially.rpow`

English:
lemma GrowsPolynomially.rpow
  statement: (p : Real) (hf : GrowsPolynomially f)
  proof: by
  intro b hb
  obtain ⟨c₁, (hc₁_mem : 0 < c₁), c₂, hc₂_mem, hfnew⟩ := hf b hb
  have hc₁p : 0 < c₁ ^ p := Real.rpow_pos_of_pos hc₁_mem _
  have hc₂p : 0 < c₂ ^ p := Real.rpow_pos_of_pos hc₂_mem _
  cases le_or_gt 0 p with
  | inl => -- 0 ≤ p
    refine ⟨c₁^p, hc₁p, ?_⟩
    refine ⟨c₂^p, hc₂p, ?_⟩

中文:
引理 GrowsPolynomially.rpow
  结论: (p : 实数) (hf : GrowsPolynomially f)
  证明: by
  intro b hb
  obtain ⟨c₁, (hc₁_mem : 0 < c₁), c₂, hc₂_mem, hfnew⟩ := hf b hb
  have hc₁p : 0 < c₁ ^ p := Real.rpow_pos_of_pos hc₁_mem _
  have hc₂p : 0 < c₂ ^ p := Real.rpow_pos_of_pos hc₂_mem _
  cases le_or_gt 0 p with
  | inl => -- 0 ≤ p
    refine ⟨c₁^p, hc₁p, ?_⟩
    refine ⟨c₂^p, hc₂p, ?_⟩
-/
protected lemma GrowsPolynomially.rpow (p : Real) (hf : GrowsPolynomially f)
    (hf_nonneg : forallᶠ x in atTop, 0 <= f x) : GrowsPolynomially fun x => (f x) ^ p := by
  intro b hb
  obtain ⟨c₁, (hc₁_mem : 0 < c₁), c₂, hc₂_mem, hfnew⟩ := hf b hb
  have hc₁p : 0 < c₁ ^ p := Real.rpow_pos_of_pos hc₁_mem _
  have hc₂p : 0 < c₂ ^ p := Real.rpow_pos_of_pos hc₂_mem _
  cases le_or_gt 0 p with
  | inl => -- 0 ≤ p
    refine ⟨c₁^p, hc₁p, ?_⟩
    refine ⟨c₂^p, hc₂p, ?_⟩
    filter_upwards [eventually_gt_atTop 0, hfnew, hf_nonneg,
        (tendsto_id.const_mul_atTop hb.1).eventually_forall_ge_atTop hf_nonneg]
        with x _ hf₁ hf_nonneg hf_nonneg₂
    intro u hu
    have fu_nonneg : 0 <= f u := hf_nonneg₂ u hu.1
    refine ⟨?lb, ?ub⟩
    case lb => calc
      c₁ ^ p * (f x) ^ p = (c₁ * f x) ^ p := by rw [mul_rpow (le_of_lt hc₁_mem) hf_nonneg]
        _ <= _ := by gcongr; exact (hf₁ u hu).1
    case ub => calc
      (f u) ^ p <= (c₂ * f x) ^ p := by gcongr; exact (hf₁ u hu).2
        _ = _ := by rw [← mul_rpow (le_of_lt hc₂_mem) hf_nonneg]
  | inr hp => -- p < 0
    match hf.eventually_atTop_zero_or_pos_or_neg with
    | .inl hzero => -- eventually zero
      refine ⟨1, by norm_num, 1, by norm_num, ?_⟩
      filter_upwards [hzero, hfnew] with x hx hx'
      intro u hu
      simp only [hx, zero_rpow (ne_of_lt hp), mul_zero,
        Set.Icc_self, Set.mem_singleton_iff]
      simp only [hx, mul_zero, Set.Icc_self, Set.mem_singleton_iff] at hx'
      rw [hx' u hu]; rw [zero_rpow (ne_of_lt hp)]
    | .inr (.inl hpos) => -- eventually positive
      refine ⟨c₂^p, hc₂p, ?_⟩
      refine ⟨c₁^p, hc₁p, ?_⟩
      filter_upwards [eventually_gt_atTop 0, hfnew, hpos,
          (tendsto_id.const_mul_atTop hb.1).eventually_forall_ge_atTop hpos]
          with x _ hf₁ hf_pos hf_pos₂
      intro u hu
      refine ⟨?lb, ?ub⟩
      case lb => calc
        c₂ ^ p * (f x) ^ p = (c₂ * f x) ^ p := by rw [mul_rpow (le_of_lt hc₂_mem) (le_of_lt hf_pos)]
          _ <= _ := rpow_le_rpow_of_nonpos (hf_pos₂ u hu.1) (hf₁ u hu).2 (le_of_lt hp)
      case ub => calc
        (f u) ^ p <= (c₁ * f x) ^ p := by
              exact rpow_le_rpow_of_nonpos (by positivity) (hf₁ u hu).1 (le_of_lt hp)
          _ = _ := by rw [← mul_rpow (le_of_lt hc₁_mem) (le_of_lt hf_pos)]
    | .inr (.inr hneg) => -- eventually negative (which is impossible)
      have : forallᶠ (_ : Real) in atTop, False := by
        filter_upwards [hf_nonneg, hneg] with x hx hx'; linarith
      rw [Filter.eventually_false_iff_eq_bot] at this
exact False.elim atTop_neBot.ne this

/--
lemma `GrowsPolynomially.pow` / 引理 `GrowsPolynomially.pow`

English:
lemma GrowsPolynomially.pow
  statement: (p : Nat) (hf : GrowsPolynomially f)
  proof: by
  simp_rw [← rpow_natCast]
  exact hf.rpow p hf_nonneg

中文:
引理 GrowsPolynomially.pow
  结论: (p : 自然数) (hf : GrowsPolynomially f)
  证明: by
  simp_rw [← rpow_natCast]
  exact hf.rpow p hf_nonneg
-/
protected lemma GrowsPolynomially.pow (p : Nat) (hf : GrowsPolynomially f)
    (hf_nonneg : forallᶠ x in atTop, 0 <= f x) : GrowsPolynomially fun x => (f x) ^ p := by
  simp_rw [← rpow_natCast]
  exact hf.rpow p hf_nonneg

/--
lemma `GrowsPolynomially.zpow` / 引理 `GrowsPolynomially.zpow`

English:
lemma GrowsPolynomially.zpow
  statement: (p : Int) (hf : GrowsPolynomially f)
  proof: by
  simp_rw [← rpow_intCast]
  exact hf.rpow p hf_nonneg

中文:
引理 GrowsPolynomially.zpow
  结论: (p : 整数) (hf : GrowsPolynomially f)
  证明: by
  simp_rw [← rpow_intCast]
  exact hf.rpow p hf_nonneg
-/
protected lemma GrowsPolynomially.zpow (p : Int) (hf : GrowsPolynomially f)
    (hf_nonneg : forallᶠ x in atTop, 0 <= f x) : GrowsPolynomially fun x => (f x) ^ p := by
  simp_rw [← rpow_intCast]
  exact hf.rpow p hf_nonneg

/--
lemma `growsPolynomially_rpow` / 引理 `growsPolynomially_rpow`

English:
lemma growsPolynomially_rpow
  given: (p : Real)
  statement: GrowsPolynomially fun x => x ^ p
  proof: growsPolynomially_id.rpow p (eventually_ge_atTop 0)

中文:
引理 growsPolynomially_rpow
  条件: (p : 实数)
  结论: GrowsPolynomially fun x => x ^ p
  证明: growsPolynomially_id.rpow p (eventually_ge_atTop 0)

Depends on / 依赖: eventually_ge_atTop, growsPolynomially_id, growsPolynomially_id.rpow
-/
lemma growsPolynomially_rpow (p : Real) : GrowsPolynomially fun x => x ^ p :=
  growsPolynomially_id.rpow p (eventually_ge_atTop 0)

/--
lemma `growsPolynomially_pow` / 引理 `growsPolynomially_pow`

English:
lemma growsPolynomially_pow
  given: (p : Nat)
  statement: GrowsPolynomially fun x => x ^ p
  proof: growsPolynomially_id.pow p (eventually_ge_atTop 0)

中文:
引理 growsPolynomially_pow
  条件: (p : 自然数)
  结论: GrowsPolynomially fun x => x ^ p
  证明: growsPolynomially_id.pow p (eventually_ge_atTop 0)

Depends on / 依赖: eventually_ge_atTop, growsPolynomially_id, growsPolynomially_id.pow
-/
lemma growsPolynomially_pow (p : Nat) : GrowsPolynomially fun x => x ^ p :=
  growsPolynomially_id.pow p (eventually_ge_atTop 0)

/--
lemma `growsPolynomially_zpow` / 引理 `growsPolynomially_zpow`

English:
lemma growsPolynomially_zpow
  given: (p : Int)
  statement: GrowsPolynomially fun x => x ^ p
  proof: growsPolynomially_id.zpow p (eventually_ge_atTop 0)

中文:
引理 growsPolynomially_zpow
  条件: (p : 整数)
  结论: GrowsPolynomially fun x => x ^ p
  证明: growsPolynomially_id.zpow p (eventually_ge_atTop 0)

Depends on / 依赖: eventually_ge_atTop, growsPolynomially_id, growsPolynomially_id.zpow
-/
lemma growsPolynomially_zpow (p : Int) : GrowsPolynomially fun x => x ^ p :=
  growsPolynomially_id.zpow p (eventually_ge_atTop 0)

/--
lemma `growsPolynomially_log` / 引理 `growsPolynomially_log`

English:
lemma growsPolynomially_log
  statement: GrowsPolynomially Real.log
  proof: by
  intro b hb
  have hb₀ : 0 < b := hb.1
  refine ⟨1 / 2, by norm_num, ?_⟩
  refine ⟨1, by norm_num, ?_⟩
  have h_tendsto : Tendsto (fun x => 1 / 2 * Real.log x) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) Real.tendsto_log_atTop
  filter_upwards [eventually_gt_atTop 1,
               

中文:
引理 growsPolynomially_log
  结论: GrowsPolynomially 实数.log
  证明: by
  intro b hb
  have hb₀ : 0 < b := hb.1
  refine ⟨1 / 2, by norm_num, ?_⟩
  refine ⟨1, by norm_num, ?_⟩
  have h_tendsto : Tendsto (fun x => 1 / 2 * Real.log x) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) Real.tendsto_log_atTop
  filter_upwards [eventually_gt_atTop 1,
               

Depends on / 依赖: Real.log, Real.tendsto_log_atTop, Tendsto, Tendsto.const_mul_atTop, const_mul_atTop, eventually, eventually_forall_ge_atTop, eventually_gt_atTop, filter_upwards, h_tendsto, h_tendsto.eventually, hx_pos, tendsto_id, tendsto_id.const_mul_atTop, tendsto_log_atTop
-/
lemma growsPolynomially_log : GrowsPolynomially Real.log := by
  intro b hb
  have hb₀ : 0 < b := hb.1
  refine ⟨1 / 2, by norm_num, ?_⟩
  refine ⟨1, by norm_num, ?_⟩
  have h_tendsto : Tendsto (fun x => 1 / 2 * Real.log x) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) Real.tendsto_log_atTop
  filter_upwards [eventually_gt_atTop 1,
                  (tendsto_id.const_mul_atTop hb.1).eventually_forall_ge_atTop
 h_tendsto.eventually (eventually_gt_atTop (-Real.log b))] with x hx_pos hx
  intro u hu
  refine ⟨?lb, ?ub⟩
  case lb => calc
    1 / 2 * Real.log x = Real.log x + (-1 / 2) * Real.log x := by ring
      _ <= Real.log x + Real.log b := by grind
      _ = Real.log (b * x) := by rw [← Real.log_mul (by positivity) (by positivity), mul_comm]
      _ <= Real.log u := by gcongr; exact hu.1
  case ub =>
    rw [one_mul]
    gcongr
    · calc 0 < b * x := by positivity
         _ <= u := by exact hu.1
    · exact hu.2

/--
lemma `GrowsPolynomially.of_isTheta` / 引理 `GrowsPolynomially.of_isTheta`

English:
lemma GrowsPolynomially.of_isTheta
  statement: {f g : Real -> Real} (hg : GrowsPolynomially g) (hf : f =Θ[atTop] g)
  proof: by
  intro b hb
  have hb_pos := hb.1
  have hf_lb := isBigO_iff''.mp hf.isBigO_symm
  have hf_ub := isBigO_iff'.mp hf.isBigO
  obtain ⟨c₁, hc₁_pos : 0 < c₁, hf_lb⟩ := hf_lb
  obtain ⟨c₂, hc₂_pos : 0 < c₂, hf_ub⟩ := hf_ub
  have hg := hg.norm b hb
  obtain ⟨c₃, hc₃_pos : 0 < c₃, hg⟩ := hg
  obtain ⟨

中文:
引理 GrowsPolynomially.of_isTheta
  结论: {f g : 实数 -> 实数} (hg : GrowsPolynomially g) (hf : f =Θ[atTop] g)
  证明: by
  intro b hb
  have hb_pos := hb.1
  have hf_lb := isBigO_iff''.mp hf.isBigO_symm
  have hf_ub := isBigO_iff'.mp hf.isBigO
  obtain ⟨c₁, hc₁_pos : 0 < c₁, hf_lb⟩ := hf_lb
  obtain ⟨c₂, hc₂_pos : 0 < c₂, hf_ub⟩ := hf_ub
  have hg := hg.norm b hb
  obtain ⟨c₃, hc₃_pos : 0 < c₃, hg⟩ := hg
  obtain ⟨

Depends on / 依赖: h_lb_pos, h_ub_pos, hb_pos, hf.isBigO, hf.isBigO_symm, hf_lb, hf_ub, hg.norm, isBigO, isBigO_iff, isBigO_symm
-/
lemma GrowsPolynomially.of_isTheta {f g : Real -> Real} (hg : GrowsPolynomially g) (hf : f =Θ[atTop] g)
    (hf' : forallᶠ x in atTop, 0 <= f x) : GrowsPolynomially f := by
  intro b hb
  have hb_pos := hb.1
  have hf_lb := isBigO_iff''.mp hf.isBigO_symm
  have hf_ub := isBigO_iff'.mp hf.isBigO
  obtain ⟨c₁, hc₁_pos : 0 < c₁, hf_lb⟩ := hf_lb
  obtain ⟨c₂, hc₂_pos : 0 < c₂, hf_ub⟩ := hf_ub
  have hg := hg.norm b hb
  obtain ⟨c₃, hc₃_pos : 0 < c₃, hg⟩ := hg
  obtain ⟨c₄, hc₄_pos : 0 < c₄, hg⟩ := hg
  have h_lb_pos : 0 < c₁ * c₂⁻¹ * c₃ := by positivity
  have h_ub_pos : 0 < c₂ * c₄ * c₁⁻¹ := by positivity
  refine ⟨c₁ * c₂⁻¹ * c₃, h_lb_pos, ?_⟩
  refine ⟨c₂ * c₄ * c₁⁻¹, h_ub_pos, ?_⟩
  have c₂_cancel : c₂⁻¹ * c₂ = 1 := inv_mul_cancel₀ (by positivity)
  have c₁_cancel : c₁⁻¹ * c₁ = 1 := inv_mul_cancel₀ (by positivity)
  filter_upwards [(tendsto_id.const_mul_atTop hb_pos).eventually_forall_ge_atTop hf',
                  (tendsto_id.const_mul_atTop hb_pos).eventually_forall_ge_atTop hf_lb,
                  (tendsto_id.const_mul_atTop hb_pos).eventually_forall_ge_atTop hf_ub,
                  (tendsto_id.const_mul_atTop hb_pos).eventually_forall_ge_atTop hg,
                  eventually_ge_atTop 0]
    with x hf_pos h_lb h_ub hg_bound hx_pos
  intro u hu
  have hbx : b * x <= x :=
    calc b * x <= 1 * x := by gcongr; exact le_of_lt hb.2
             _ = x := by rw [one_mul]
  have hg_bound := hg_bound x hbx
  refine ⟨?lb, ?ub⟩
  case lb => calc
    c₁ * c₂⁻¹ * c₃ * f x <= c₁ * c₂⁻¹ * c₃ * (c₂ * ‖g x‖) := by
          rw [← Real.norm_of_nonneg (hf_pos x hbx)]; gcongr; exact h_ub x hbx
      _ = (c₂⁻¹ * c₂) * c₁ * (c₃ * ‖g x‖) := by ring
      _ = c₁ * (c₃ * ‖g x‖) := by simp [c₂_cancel]
      _ <= c₁ * ‖g u‖ := by gcongr; exact (hg_bound u hu).1
      _ <= f u := by
          rw [← Real.norm_of_nonneg (hf_pos u hu.1)]
          exact h_lb u hu.1
  case ub => calc
    f u <= c₂ * ‖g u‖ := by rw [← Real.norm_of_nonneg (hf_pos u hu.1)]; exact h_ub u hu.1
      _ <= c₂ * (c₄ * ‖g x‖) := by gcongr; exact (hg_bound u hu).2
      _ = c₂ * c₄ * (c₁⁻¹ * c₁) * ‖g x‖ := by simp [c₁_cancel]; ring
      _ = c₂ * c₄ * c₁⁻¹ * (c₁ * ‖g x‖) := by ring
      _ <= c₂ * c₄ * c₁⁻¹ * f x := by
                gcongr
                rw [← Real.norm_of_nonneg (hf_pos x hbx)]
                exact h_lb x hbx

/--
lemma `GrowsPolynomially.of_isEquivalent` / 引理 `GrowsPolynomially.of_isEquivalent`

English:
lemma GrowsPolynomially.of_isEquivalent
  statement: {f g : Real -> Real} (hg : GrowsPolynomially g)
  proof: by
  have : f = g + (f - g) := by ext; simp
  rw [this]
  exact add_isLittleO hg hf

中文:
引理 GrowsPolynomially.of_isEquivalent
  结论: {f g : 实数 -> 实数} (hg : GrowsPolynomially g)
  证明: by
  have : f = g + (f - g) := by ext; simp
  rw [this]
  exact add_isLittleO hg hf

Depends on / 依赖: add_isLittleO
-/
lemma GrowsPolynomially.of_isEquivalent {f g : Real -> Real} (hg : GrowsPolynomially g)
    (hf : f ~[atTop] g) : GrowsPolynomially f := by
  have : f = g + (f - g) := by ext; simp
  rw [this]
  exact add_isLittleO hg hf

/--
lemma `GrowsPolynomially.of_isEquivalent_const` / 引理 `GrowsPolynomially.of_isEquivalent_const`

English:
lemma GrowsPolynomially.of_isEquivalent_const
  given: {f : Real -> Real} {c : Real} (hf : f ~[atTop] fun _ => c)
  proof: of_isEquivalent growsPolynomially_const hf

中文:
引理 GrowsPolynomially.of_isEquivalent_const
  条件: {f : 实数 -> 实数} {c : 实数} (hf : f ~[atTop] fun _ => c)
  证明: of_isEquivalent growsPolynomially_const hf

Depends on / 依赖: growsPolynomially_const, of_isEquivalent
-/
lemma GrowsPolynomially.of_isEquivalent_const {f : Real -> Real} {c : Real} (hf : f ~[atTop] fun _ => c) :
    GrowsPolynomially f :=
  of_isEquivalent growsPolynomially_const hf

end AkraBazziRecurrence
