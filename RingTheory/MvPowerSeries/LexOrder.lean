/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Data.Finsupp.WellFounded

/-! # LexOrder of multivariate power series

Given an ordering of `σ` such that `WellFoundedGT σ`,
the lexicographic order on `σ →₀ ℕ` is a well ordering,
which can be used to define a natural valuation `lexOrder` on the ring `MvPowerSeries σ R`:
the smallest exponent in the support.

-/

@[expose] public section

namespace MvPowerSeries

variable {σ R : Type*}
variable [Semiring R]

section LexOrder

open Finsupp
variable [LinearOrder σ] [WellFoundedGT σ]

/--
Definition of `lexOrder` / `lexOrder` 的定义

English:
definition lexOrder
  signature: (φ : MvPowerSeries σ R)
  body: by
  classical
  exact if h : φ = 0 then ⊤ else by
    have ne : Set.Nonempty (toLex '' φ.support) := (Function.support_nonempty_iff.mpr h).image _
    apply WithTop.some
    apply WellFounded.min _ (toLex '' φ.support) ne
    · exact Finsupp.instLTLex.lt
    · exact wellFounded_lt

中文:
定义 lexOrder
  签名: (φ : MvPowerSeries σ R)
  定义体: by
  classical
  exact if h : φ = 0 then ⊤ else by
    have ne : Set.Nonempty (toLex '' φ.support) := (Function.support_nonempty_iff.mpr h).image _
    apply WithTop.some
    apply WellFounded.min _ (toLex '' φ.support) ne
    · exact Finsupp.instLTLex.lt
    · exact wellFounded_lt

Depends on / 依赖: Finsupp, Finsupp.instLTLex.lt, Function, Function.support_nonempty_iff.mpr, Nonempty, Set.Nonempty, WellFounded, WellFounded.min, WithTop, WithTop.some, classical, instLTLex, support, support_nonempty_iff, wellFounded_lt
-/
noncomputable def lexOrder (φ : MvPowerSeries σ R) : (WithTop (Lex (σ ->₀ Nat))) := by
  classical
  exact if h : φ = 0 then ⊤ else by
    have ne : Set.Nonempty (toLex '' φ.support) := (Function.support_nonempty_iff.mpr h).image _
    apply WithTop.some
    apply WellFounded.min _ (toLex '' φ.support) ne
    · exact Finsupp.instLTLex.lt
    · exact wellFounded_lt

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lexOrder_def_of_ne_zero` / 定理 `lexOrder_def_of_ne_zero`

English:
theorem lexOrder_def_of_ne_zero
  given: {φ : MvPowerSeries σ R} (hφ : φ != 0)
  proof: by
  suffices ne : Set.Nonempty (toLex '' φ.support) by
    use ne
    unfold lexOrder
    simp only [dif_neg hφ]
  exact (Function.support_nonempty_iff.mpr hφ).image _

@[simp]

中文:
定理 lexOrder_def_of_ne_zero
  条件: {φ : MvPowerSeries σ R} (hφ : φ != 0)
  证明: by
  suffices ne : Set.Nonempty (toLex '' φ.support) by
    use ne
    unfold lexOrder
    simp only [dif_neg hφ]
  exact (Function.support_nonempty_iff.mpr hφ).image _

@[simp]

Depends on / 依赖: Function, Function.support_nonempty_iff.mpr, Nonempty, Set.Nonempty, dif_neg, lexOrder, support, support_nonempty_iff
-/
theorem lexOrder_def_of_ne_zero {φ : MvPowerSeries σ R} (hφ : φ != 0) :
    exists (ne : Set.Nonempty (toLex '' φ.support)),
      lexOrder φ = WithTop.some ((@wellFounded_lt (Lex (σ ->₀ Nat))
        (instLTLex) (Lex.wellFoundedLT)).min (toLex '' φ.support) ne) := by
  suffices ne : Set.Nonempty (toLex '' φ.support) by
    use ne
    unfold lexOrder
    simp only [dif_neg hφ]
  exact (Function.support_nonempty_iff.mpr hφ).image _

@[simp]
/--
theorem `lexOrder_eq_top_iff_eq_zero` / 定理 `lexOrder_eq_top_iff_eq_zero`

English:
theorem lexOrder_eq_top_iff_eq_zero
  given: (φ : MvPowerSeries σ R)
  proof: by
  unfold lexOrder
  split_ifs with h
  · simp only [h]
  · simp only [h, WithTop.coe_ne_top]

中文:
定理 lexOrder_eq_top_iff_eq_zero
  条件: (φ : MvPowerSeries σ R)
  证明: by
  unfold lexOrder
  split_ifs with h
  · simp only [h]
  · simp only [h, WithTop.coe_ne_top]

Depends on / 依赖: WithTop, WithTop.coe_ne_top, coe_ne_top, lexOrder, split_ifs
-/
theorem lexOrder_eq_top_iff_eq_zero (φ : MvPowerSeries σ R) :
    lexOrder φ = ⊤ ↔ φ = 0 := by
  unfold lexOrder
  split_ifs with h
  · simp only [h]
  · simp only [h, WithTop.coe_ne_top]

/--
theorem `lexOrder_zero` / 定理 `lexOrder_zero`

English:
theorem lexOrder_zero
  statement: lexOrder (0 : MvPowerSeries σ R) = ⊤
  proof: by
  unfold lexOrder
  rw [dif_pos rfl]

中文:
定理 lexOrder_zero
  结论: lexOrder (0 : MvPowerSeries σ R) = ⊤
  证明: by
  unfold lexOrder
  rw [dif_pos rfl]
-/
@[simp] theorem lexOrder_zero : lexOrder (0 : MvPowerSeries σ R) = ⊤ := by
  unfold lexOrder
  rw [dif_pos rfl]

/--
theorem `exists_finsupp_eq_lexOrder_of_ne_zero` / 定理 `exists_finsupp_eq_lexOrder_of_ne_zero`

English:
theorem exists_finsupp_eq_lexOrder_of_ne_zero
  given: {φ : MvPowerSeries σ R} (hφ : φ != 0)
  proof: by
  simp only [ne_eq, ← lexOrder_eq_top_iff_eq_zero, WithTop.ne_top_iff_exists] at hφ
  obtain ⟨p, hp⟩ := hφ
  exact ⟨ofLex p, by simp only [toLex_ofLex, hp]⟩

中文:
定理 存在_finsupp_eq_lexOrder_of_ne_zero
  条件: {φ : MvPowerSeries σ R} (hφ : φ != 0)
  证明: by
  simp only [ne_eq, ← lexOrder_eq_top_iff_eq_zero, WithTop.ne_top_iff_exists] at hφ
  obtain ⟨p, hp⟩ := hφ
  exact ⟨ofLex p, by simp only [toLex_ofLex, hp]⟩

Depends on / 依赖: WithTop, WithTop.ne_top_iff_exists, lexOrder_eq_top_iff_eq_zero, ne_eq, ne_top_iff_exists, toLex_ofLex
-/
theorem exists_finsupp_eq_lexOrder_of_ne_zero {φ : MvPowerSeries σ R} (hφ : φ != 0) :
    exists (d : σ ->₀ Nat), lexOrder φ = toLex d := by
  simp only [ne_eq, ← lexOrder_eq_top_iff_eq_zero, WithTop.ne_top_iff_exists] at hφ
  obtain ⟨p, hp⟩ := hφ
  exact ⟨ofLex p, by simp only [toLex_ofLex, hp]⟩

/--
theorem `coeff_ne_zero_of_lexOrder` / 定理 `coeff_ne_zero_of_lexOrder`

English:
theorem coeff_ne_zero_of_lexOrder
  statement: {φ : MvPowerSeries σ R} {d : σ ->₀ Nat}
  proof: by
  have hφ : φ != 0 := by
    simp only [ne_eq, ← lexOrder_eq_top_iff_eq_zero, ← h, WithTop.coe_ne_top, not_false_eq_true]
  have hφ' := lexOrder_def_of_ne_zero hφ
  rcases hφ' with ⟨ne, hφ'⟩
  simp only [← h, WithTop.coe_eq_coe] at hφ'
  suffices toLex d in toLex '' φ.support by
    simp only [Set.mem_image_equiv, toLex_symm_eq, ofLex_toLex] at this
    apply this
  rw [hφ']
  apply WellFounded.min_mem

中文:
定理 coeff_ne_zero_of_lexOrder
  结论: {φ : MvPowerSeries σ R} {d : σ ->₀ 自然数}
  证明: by
  have hφ : φ != 0 := by
    simp only [ne_eq, ← lexOrder_eq_top_iff_eq_zero, ← h, WithTop.coe_ne_top, not_false_eq_true]
  have hφ' := lexOrder_def_of_ne_zero hφ
  rcases hφ' with ⟨ne, hφ'⟩
  simp only [← h, WithTop.coe_eq_coe] at hφ'
  suffices toLex d in toLex '' φ.support by
    simp only [Set.mem_image_equiv, toLex_symm_eq, ofLex_toLex] at this
    apply this
  rw [hφ']
  apply WellFounded.min_mem

Depends on / 依赖: Set.mem_image_equiv, WellFounded, WellFounded.min_mem, WithTop, WithTop.coe_eq_coe, WithTop.coe_ne_top, coe_eq_coe, coe_ne_top, lexOrder_def_of_ne_zero, lexOrder_eq_top_iff_eq_zero, mem_image_equiv, min_mem, ne_eq, not_false_eq_true, ofLex_toLex, support, toLex_symm_eq
-/
theorem coeff_ne_zero_of_lexOrder {φ : MvPowerSeries σ R} {d : σ ->₀ Nat}
    (h : toLex d = lexOrder φ) : coeff d φ != 0 := by
  have hφ : φ != 0 := by
    simp only [ne_eq, ← lexOrder_eq_top_iff_eq_zero, ← h, WithTop.coe_ne_top, not_false_eq_true]
  have hφ' := lexOrder_def_of_ne_zero hφ
  rcases hφ' with ⟨ne, hφ'⟩
  simp only [← h, WithTop.coe_eq_coe] at hφ'
  suffices toLex d in toLex '' φ.support by
    simp only [Set.mem_image_equiv, toLex_symm_eq, ofLex_toLex] at this
    apply this
  rw [hφ']
  apply WellFounded.min_mem

/--
theorem `coeff_eq_zero_of_lt_lexOrder` / 定理 `coeff_eq_zero_of_lt_lexOrder`

English:
theorem coeff_eq_zero_of_lt_lexOrder
  statement: {φ : MvPowerSeries σ R} {d : σ ->₀ Nat}
  proof: by
  by_cases hφ : φ = 0
  · simp only [hφ, map_zero]
  · rcases lexOrder_def_of_ne_zero hφ with ⟨ne, hφ'⟩
    rw [hφ']; rw [WithTop.coe_lt_coe] at h
    by_contra h'
    exact WellFounded.not_lt_min _ (toLex '' φ.support) (Set.mem_image_equiv.mpr h') h

中文:
定理 coeff_eq_zero_of_lt_lexOrder
  结论: {φ : MvPowerSeries σ R} {d : σ ->₀ 自然数}
  证明: by
  by_cases hφ : φ = 0
  · simp only [hφ, map_zero]
  · rcases lexOrder_def_of_ne_zero hφ with ⟨ne, hφ'⟩
    rw [hφ']; rw [WithTop.coe_lt_coe] at h
    by_contra h'
    exact WellFounded.not_lt_min _ (toLex '' φ.support) (Set.mem_image_equiv.mpr h') h

Depends on / 依赖: Set.mem_image_equiv.mpr, WellFounded, WellFounded.not_lt_min, WithTop, WithTop.coe_lt_coe, coe_lt_coe, lexOrder_def_of_ne_zero, map_zero, mem_image_equiv, not_lt_min, support
-/
theorem coeff_eq_zero_of_lt_lexOrder {φ : MvPowerSeries σ R} {d : σ ->₀ Nat}
    (h : toLex d < lexOrder φ) : coeff d φ = 0 := by
  by_cases hφ : φ = 0
  · simp only [hφ, map_zero]
  · rcases lexOrder_def_of_ne_zero hφ with ⟨ne, hφ'⟩
    rw [hφ']; rw [WithTop.coe_lt_coe] at h
    by_contra h'
    exact WellFounded.not_lt_min _ (toLex '' φ.support) (Set.mem_image_equiv.mpr h') h

/--
theorem `lexOrder_le_of_coeff_ne_zero` / 定理 `lexOrder_le_of_coeff_ne_zero`

English:
theorem lexOrder_le_of_coeff_ne_zero
  statement: {φ : MvPowerSeries σ R} {d : σ ->₀ Nat}
  proof: by
  rw [← not_lt]
  intro h'
  exact h (coeff_eq_zero_of_lt_lexOrder h')

中文:
定理 lexOrder_le_of_coeff_ne_zero
  结论: {φ : MvPowerSeries σ R} {d : σ ->₀ 自然数}
  证明: by
  rw [← not_lt]
  intro h'
  exact h (coeff_eq_zero_of_lt_lexOrder h')

Depends on / 依赖: coeff_eq_zero_of_lt_lexOrder, not_lt
-/
theorem lexOrder_le_of_coeff_ne_zero {φ : MvPowerSeries σ R} {d : σ ->₀ Nat}
    (h : coeff d φ != 0) : lexOrder φ <= toLex d := by
  rw [← not_lt]
  intro h'
  exact h (coeff_eq_zero_of_lt_lexOrder h')

/--
theorem `le_lexOrder_iff` / 定理 `le_lexOrder_iff`

English:
theorem le_lexOrder_iff
  given: {φ : MvPowerSeries σ R} {w : WithTop (Lex (σ ->₀ Nat))}
  proof: by
  constructor
  · intro h d hd
    apply coeff_eq_zero_of_lt_lexOrder
    exact lt_of_lt_of_le hd h
  · intro h
    rw [← not_lt]
    intro h'
    have hφ : φ != 0 := by
      rw [ne_eq]; rw [← lexOrder_eq_top_iff_eq_zero]
      exact ne_top_of_lt h'
    obtain ⟨d, hd⟩ := exists_finsupp_eq_lexOrder_of_ne_zero hφ
    refine coeff_ne_zero_of_lexOrder hd.symm (h d ?_)
    rwa [← hd]

中文:
定理 le_lexOrder_iff
  条件: {φ : MvPowerSeries σ R} {w : WithTop (Lex (σ ->₀ 自然数))}
  证明: by
  constructor
  · intro h d hd
    apply coeff_eq_zero_of_lt_lexOrder
    exact lt_of_lt_of_le hd h
  · intro h
    rw [← not_lt]
    intro h'
    have hφ : φ != 0 := by
      rw [ne_eq]; rw [← lexOrder_eq_top_iff_eq_zero]
      exact ne_top_of_lt h'
    obtain ⟨d, hd⟩ := exists_finsupp_eq_lexOrder_of_ne_zero hφ
    refine coeff_ne_zero_of_lexOrder hd.symm (h d ?_)
    rwa [← hd]

Depends on / 依赖: coeff_eq_zero_of_lt_lexOrder, coeff_ne_zero_of_lexOrder, exists_finsupp_eq_lexOrder_of_ne_zero, hd.symm, lexOrder_eq_top_iff_eq_zero, lt_of_lt_of_le, ne_eq, ne_top_of_lt, not_lt
-/
theorem le_lexOrder_iff {φ : MvPowerSeries σ R} {w : WithTop (Lex (σ ->₀ Nat))} :
    w <= lexOrder φ ↔ (forall (d : σ ->₀ Nat) (_ : toLex d < w), coeff d φ = 0) := by
  constructor
  · intro h d hd
    apply coeff_eq_zero_of_lt_lexOrder
    exact lt_of_lt_of_le hd h
  · intro h
    rw [← not_lt]
    intro h'
    have hφ : φ != 0 := by
      rw [ne_eq]; rw [← lexOrder_eq_top_iff_eq_zero]
      exact ne_top_of_lt h'
    obtain ⟨d, hd⟩ := exists_finsupp_eq_lexOrder_of_ne_zero hφ
    refine coeff_ne_zero_of_lexOrder hd.symm (h d ?_)
    rwa [← hd]

/--
theorem `min_lexOrder_le` / 定理 `min_lexOrder_le`

English:
theorem min_lexOrder_le
  given: {φ ψ : MvPowerSeries σ R}
  proof: by
  rw [le_lexOrder_iff]
  intro d hd
  simp only [lt_min_iff] at hd
  rw [map_add]; rw [coeff_eq_zero_of_lt_lexOrder hd.1]; rw [coeff_eq_zero_of_lt_lexOrder hd.2]; rw [add_zero]

中文:
定理 min_lexOrder_le
  条件: {φ ψ : MvPowerSeries σ R}
  证明: by
  rw [le_lexOrder_iff]
  intro d hd
  simp only [lt_min_iff] at hd
  rw [map_add]; rw [coeff_eq_zero_of_lt_lexOrder hd.1]; rw [coeff_eq_zero_of_lt_lexOrder hd.2]; rw [add_zero]

Depends on / 依赖: add_zero, coeff_eq_zero_of_lt_lexOrder, le_lexOrder_iff, lt_min_iff, map_add
-/
theorem min_lexOrder_le {φ ψ : MvPowerSeries σ R} :
    min (lexOrder φ) (lexOrder ψ) <= lexOrder (φ + ψ) := by
  rw [le_lexOrder_iff]
  intro d hd
  simp only [lt_min_iff] at hd
  rw [map_add]; rw [coeff_eq_zero_of_lt_lexOrder hd.1]; rw [coeff_eq_zero_of_lt_lexOrder hd.2]; rw [add_zero]

/--
theorem `coeff_mul_of_add_lexOrder` / 定理 `coeff_mul_of_add_lexOrder`

English:
theorem coeff_mul_of_add_lexOrder
  statement: {φ ψ : MvPowerSeries σ R}
  proof: by
  rw [coeff_mul]; rw [Finset.sum_eq_single_of_mem ⟨p]; rw [q⟩ (by simp)]
  rintro ⟨u, v⟩ h h'
  simp only [Finset.mem_antidiagonal] at h
  rcases trichotomy_of_add_eq_add (congrArg toLex h) with h'' | h'' | h''
  · exact False.elim (h' (by simp [h''.1, h''.2]))
  · rw [coeff_eq_zero_of_lt_lexOrder (d := u), zero_mul]
    rw [hp]
    norm_cast
  · rw [coeff_eq_zero_of_lt_lexOrder (d := v), mul_zero]
    rw [hq]
    norm_cast

中文:
定理 coeff_mul_of_add_lexOrder
  结论: {φ ψ : MvPowerSeries σ R}
  证明: by
  rw [coeff_mul]; rw [Finset.sum_eq_single_of_mem ⟨p]; rw [q⟩ (by simp)]
  rintro ⟨u, v⟩ h h'
  simp only [Finset.mem_antidiagonal] at h
  rcases trichotomy_of_add_eq_add (congrArg toLex h) with h'' | h'' | h''
  · exact False.elim (h' (by simp [h''.1, h''.2]))
  · rw [coeff_eq_zero_of_lt_lexOrder (d := u), zero_mul]
    rw [hp]
    norm_cast
  · rw [coeff_eq_zero_of_lt_lexOrder (d := v), mul_zero]
    rw [hq]
    norm_cast

Depends on / 依赖: False.elim, Finset, Finset.mem_antidiagonal, Finset.sum_eq_single_of_mem, coeff_eq_zero_of_lt_lexOrder, coeff_mul, mem_antidiagonal, mul_zero, sum_eq_single_of_mem, trichotomy_of_add_eq_add, zero_mul
-/
theorem coeff_mul_of_add_lexOrder {φ ψ : MvPowerSeries σ R}
    {p q : σ ->₀ Nat} (hp : lexOrder φ = toLex p) (hq : lexOrder ψ = toLex q) :
    coeff (p + q) (φ * ψ) = coeff p φ * coeff q ψ := by
  rw [coeff_mul]; rw [Finset.sum_eq_single_of_mem ⟨p]; rw [q⟩ (by simp)]
  rintro ⟨u, v⟩ h h'
  simp only [Finset.mem_antidiagonal] at h
  rcases trichotomy_of_add_eq_add (congrArg toLex h) with h'' | h'' | h''
  · exact False.elim (h' (by simp [h''.1, h''.2]))
  · rw [coeff_eq_zero_of_lt_lexOrder (d := u), zero_mul]
    rw [hp]
    norm_cast
  · rw [coeff_eq_zero_of_lt_lexOrder (d := v), mul_zero]
    rw [hq]
    norm_cast

/--
theorem `le_lexOrder_mul` / 定理 `le_lexOrder_mul`

English:
theorem le_lexOrder_mul
  given: (φ ψ : MvPowerSeries σ R)
  proof: by
  rw [le_lexOrder_iff]
  intro d hd
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨u, v⟩ h
  simp only [Finset.mem_antidiagonal] at h
  simp only
  suffices toLex u < lexOrder φ ∨ toLex v < lexOrder ψ by
    rcases this with (hu | hv)
    · rw [coeff_eq_zero_of_lt_lexOrder hu, zero_mul]
    · rw [coeff_eq_zero_of_lt_lexOrder hv, mul_zero]
  rw [or_iff_not_imp_left]; rw [not_lt]; rw [← not_le]
  intro hu hv
  rw [← not_le] at hd
  apply hd
  simp only [← h, toLex_add, WithTop.coe_add, add_le_add hu hv]

alias lexOrder_mul_ge := le_lexOrder_mul

中文:
定理 le_lexOrder_mul
  条件: (φ ψ : MvPowerSeries σ R)
  证明: by
  rw [le_lexOrder_iff]
  intro d hd
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨u, v⟩ h
  simp only [Finset.mem_antidiagonal] at h
  simp only
  suffices toLex u < lexOrder φ ∨ toLex v < lexOrder ψ by
    rcases this with (hu | hv)
    · rw [coeff_eq_zero_of_lt_lexOrder hu, zero_mul]
    · rw [coeff_eq_zero_of_lt_lexOrder hv, mul_zero]
  rw [or_iff_not_imp_left]; rw [not_lt]; rw [← not_le]
  intro hu hv
  rw [← not_le] at hd
  apply hd
  simp only [← h, toLex_add, WithTop.coe_add, add_le_add hu hv]

alias lexOrder_mul_ge := le_lexOrder_mul

Depends on / 依赖: Finset, Finset.mem_antidiagonal, Finset.sum_eq_zero, WithTop, WithTop.coe_add, add_le_add, coe_add, coeff_eq_zero_of_lt_lexOrder, coeff_mul, le_lexOrder_iff, lexOrder, mem_antidiagonal, mul_zero, not_le, not_lt, or_iff_not_imp_left, sum_eq_zero, toLex_add, zero_mul
-/
theorem le_lexOrder_mul (φ ψ : MvPowerSeries σ R) :
    lexOrder φ + lexOrder ψ <= lexOrder (φ * ψ) := by
  rw [le_lexOrder_iff]
  intro d hd
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨u, v⟩ h
  simp only [Finset.mem_antidiagonal] at h
  simp only
  suffices toLex u < lexOrder φ ∨ toLex v < lexOrder ψ by
    rcases this with (hu | hv)
    · rw [coeff_eq_zero_of_lt_lexOrder hu, zero_mul]
    · rw [coeff_eq_zero_of_lt_lexOrder hv, mul_zero]
  rw [or_iff_not_imp_left]; rw [not_lt]; rw [← not_le]
  intro hu hv
  rw [← not_le] at hd
  apply hd
  simp only [← h, toLex_add, WithTop.coe_add, add_le_add hu hv]

alias lexOrder_mul_ge := le_lexOrder_mul

/--
theorem `lexOrder_mul` / 定理 `lexOrder_mul`

English:
theorem lexOrder_mul
  given: [NoZeroDivisors R] (φ ψ : MvPowerSeries σ R)
  proof: by
  obtain rfl | hφ := eq_or_ne φ 0
  · simp
  obtain rfl | hψ := eq_or_ne ψ 0
  · simp
  rcases exists_finsupp_eq_lexOrder_of_ne_zero hφ with ⟨p, hp⟩
  rcases exists_finsupp_eq_lexOrder_of_ne_zero hψ with ⟨q, hq⟩
  apply le_antisymm _ (lexOrder_mul_ge φ ψ)
  rw [hp]; rw [hq]
  apply lexOrder_le_of_coeff_ne_zero (d := p + q)
  rw [coeff_mul_of_add_lexOrder hp hq]; rw [mul_ne_zero_iff]
  exact ⟨coeff_ne_zero_of_lexOrder hp.symm, coeff_ne_zero_of_lexOrder hq.symm⟩

中文:
定理 lexOrder_mul
  条件: [无零因子 R] (φ ψ : MvPowerSeries σ R)
  证明: by
  obtain rfl | hφ := eq_or_ne φ 0
  · simp
  obtain rfl | hψ := eq_or_ne ψ 0
  · simp
  rcases exists_finsupp_eq_lexOrder_of_ne_zero hφ with ⟨p, hp⟩
  rcases exists_finsupp_eq_lexOrder_of_ne_zero hψ with ⟨q, hq⟩
  apply le_antisymm _ (lexOrder_mul_ge φ ψ)
  rw [hp]; rw [hq]
  apply lexOrder_le_of_coeff_ne_zero (d := p + q)
  rw [coeff_mul_of_add_lexOrder hp hq]; rw [mul_ne_zero_iff]
  exact ⟨coeff_ne_zero_of_lexOrder hp.symm, coeff_ne_zero_of_lexOrder hq.symm⟩

Depends on / 依赖: coeff_mul_of_add_lexOrder, coeff_ne_zero_of_lexOrder, eq_or_ne, exists_finsupp_eq_lexOrder_of_ne_zero, hp.symm, hq.symm, le_antisymm, lexOrder_le_of_coeff_ne_zero, lexOrder_mul_ge, mul_ne_zero_iff
-/
theorem lexOrder_mul [NoZeroDivisors R] (φ ψ : MvPowerSeries σ R) :
    lexOrder (φ * ψ) = lexOrder φ + lexOrder ψ := by
  obtain rfl | hφ := eq_or_ne φ 0
  · simp
  obtain rfl | hψ := eq_or_ne ψ 0
  · simp
  rcases exists_finsupp_eq_lexOrder_of_ne_zero hφ with ⟨p, hp⟩
  rcases exists_finsupp_eq_lexOrder_of_ne_zero hψ with ⟨q, hq⟩
  apply le_antisymm _ (lexOrder_mul_ge φ ψ)
  rw [hp]; rw [hq]
  apply lexOrder_le_of_coeff_ne_zero (d := p + q)
  rw [coeff_mul_of_add_lexOrder hp hq]; rw [mul_ne_zero_iff]
  exact ⟨coeff_ne_zero_of_lexOrder hp.symm, coeff_ne_zero_of_lexOrder hq.symm⟩

end LexOrder

end MvPowerSeries
