/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Order.Group.Indicator
public import Mathlib.Analysis.Normed.Group.Basic

/-!
# Indicator function and (e)norm

This file contains a few simple lemmas about `Set.indicator`, `norm` and `enorm`.

## Tags
indicator, norm
-/

public section

open Set

section ESeminormedAddMonoid

variable {α ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε]
  {s t : Set α} (f : α -> ε) (a : α)

/--
lemma `enorm_indicator_eq_indicator_enorm` / 引理 `enorm_indicator_eq_indicator_enorm`

English:
lemma enorm_indicator_eq_indicator_enorm
  proof: flip congr_fun a (indicator_comp_of_zero (enorm_zero (E := ε))).symm

中文:
引理 enorm_indicator_eq_indicator_enorm
  证明: flip congr_fun a (indicator_comp_of_zero (enorm_zero (E := ε))).symm

Depends on / 依赖: congr_fun, enorm_zero, indicator_comp_of_zero
-/
lemma enorm_indicator_eq_indicator_enorm :
    ‖indicator s f a‖ₑ = indicator s (fun a => ‖f a‖ₑ) a :=
  flip congr_fun a (indicator_comp_of_zero (enorm_zero (E := ε))).symm

/--
theorem `enorm_indicator_le_of_subset` / 定理 `enorm_indicator_le_of_subset`

English:
theorem enorm_indicator_le_of_subset
  given: (h : s subseteq t) (f : α -> ε) (a : α)
  proof: by
  simp only [enorm_indicator_eq_indicator_enorm]
  grw [h]

中文:
定理 enorm_indicator_le_of_subset
  条件: (h : s subseteq t) (f : α -> ε) (a : α)
  证明: by
  simp only [enorm_indicator_eq_indicator_enorm]
  grw [h]

Depends on / 依赖: enorm_indicator_eq_indicator_enorm
-/
theorem enorm_indicator_le_of_subset (h : s subseteq t) (f : α -> ε) (a : α) :
    ‖indicator s f a‖ₑ <= ‖indicator t f a‖ₑ := by
  simp only [enorm_indicator_eq_indicator_enorm]
  grw [h]

/--
theorem `indicator_enorm_le_enorm_self` / 定理 `indicator_enorm_le_enorm_self`

English:
theorem indicator_enorm_le_enorm_self
  statement: indicator s (fun a => ‖f a‖ₑ) a <= ‖f a‖ₑ
  proof: indicator_le_self' (fun _ _ => zero_le) a

中文:
定理 indicator_enorm_le_enorm_self
  结论: indicator s (fun a => ‖f a‖ₑ) a <= ‖f a‖ₑ
  证明: indicator_le_self' (fun _ _ => zero_le) a

Depends on / 依赖: indicator_le_self, zero_le
-/
theorem indicator_enorm_le_enorm_self : indicator s (fun a => ‖f a‖ₑ) a <= ‖f a‖ₑ :=
  indicator_le_self' (fun _ _ => zero_le) a

/--
theorem `enorm_indicator_le_enorm_self` / 定理 `enorm_indicator_le_enorm_self`

English:
theorem enorm_indicator_le_enorm_self
  statement: ‖indicator s f a‖ₑ <= ‖f a‖ₑ
  proof: by
  rw [enorm_indicator_eq_indicator_enorm]
  apply indicator_enorm_le_enorm_self

中文:
定理 enorm_indicator_le_enorm_self
  结论: ‖indicator s f a‖ₑ <= ‖f a‖ₑ
  证明: by
  rw [enorm_indicator_eq_indicator_enorm]
  apply indicator_enorm_le_enorm_self

Depends on / 依赖: enorm_indicator_eq_indicator_enorm, indicator_enorm_le_enorm_self
-/
theorem enorm_indicator_le_enorm_self : ‖indicator s f a‖ₑ <= ‖f a‖ₑ := by
  rw [enorm_indicator_eq_indicator_enorm]
  apply indicator_enorm_le_enorm_self

end ESeminormedAddMonoid

section SeminormedAddGroup

variable {α E : Type*} [SeminormedAddGroup E] {s t : Set α} (f : α -> E) (a : α)

/--
theorem `norm_indicator_eq_indicator_norm` / 定理 `norm_indicator_eq_indicator_norm`

English:
theorem norm_indicator_eq_indicator_norm
  statement: ‖indicator s f a‖ = indicator s (fun a => ‖f a‖) a
  proof: flip congr_fun a (indicator_comp_of_zero norm_zero).symm

中文:
定理 norm_indicator_eq_indicator_norm
  结论: ‖indicator s f a‖ = indicator s (fun a => ‖f a‖) a
  证明: flip congr_fun a (indicator_comp_of_zero norm_zero).symm

Depends on / 依赖: congr_fun, indicator_comp_of_zero, norm_zero
-/
theorem norm_indicator_eq_indicator_norm : ‖indicator s f a‖ = indicator s (fun a => ‖f a‖) a :=
  flip congr_fun a (indicator_comp_of_zero norm_zero).symm

/--
theorem `nnnorm_indicator_eq_indicator_nnnorm` / 定理 `nnnorm_indicator_eq_indicator_nnnorm`

English:
theorem nnnorm_indicator_eq_indicator_nnnorm
  proof: flip congr_fun a (indicator_comp_of_zero nnnorm_zero).symm

中文:
定理 nnnorm_indicator_eq_indicator_nnnorm
  证明: flip congr_fun a (indicator_comp_of_zero nnnorm_zero).symm

Depends on / 依赖: congr_fun, indicator_comp_of_zero, nnnorm_zero
-/
theorem nnnorm_indicator_eq_indicator_nnnorm :
    ‖indicator s f a‖₊ = indicator s (fun a => ‖f a‖₊) a :=
  flip congr_fun a (indicator_comp_of_zero nnnorm_zero).symm

/--
theorem `norm_indicator_le_of_subset` / 定理 `norm_indicator_le_of_subset`

English:
theorem norm_indicator_le_of_subset
  given: (h : s subseteq t) (f : α -> E) (a : α)
  proof: by
  simp only [norm_indicator_eq_indicator_norm]
  grw [h]

中文:
定理 norm_indicator_le_of_subset
  条件: (h : s subseteq t) (f : α -> E) (a : α)
  证明: by
  simp only [norm_indicator_eq_indicator_norm]
  grw [h]

Depends on / 依赖: norm_indicator_eq_indicator_norm
-/
theorem norm_indicator_le_of_subset (h : s subseteq t) (f : α -> E) (a : α) :
    ‖indicator s f a‖ <= ‖indicator t f a‖ := by
  simp only [norm_indicator_eq_indicator_norm]
  grw [h]

/--
theorem `indicator_norm_le_norm_self` / 定理 `indicator_norm_le_norm_self`

English:
theorem indicator_norm_le_norm_self
  statement: indicator s (fun a => ‖f a‖) a <= ‖f a‖
  proof: indicator_le_self' (fun _ _ => norm_nonneg _) a

中文:
定理 indicator_norm_le_norm_self
  结论: indicator s (fun a => ‖f a‖) a <= ‖f a‖
  证明: indicator_le_self' (fun _ _ => norm_nonneg _) a

Depends on / 依赖: indicator_le_self, norm_nonneg
-/
theorem indicator_norm_le_norm_self : indicator s (fun a => ‖f a‖) a <= ‖f a‖ :=
  indicator_le_self' (fun _ _ => norm_nonneg _) a

/--
theorem `norm_indicator_le_norm_self` / 定理 `norm_indicator_le_norm_self`

English:
theorem norm_indicator_le_norm_self
  statement: ‖indicator s f a‖ <= ‖f a‖
  proof: by
  rw [norm_indicator_eq_indicator_norm]
  apply indicator_norm_le_norm_self

中文:
定理 norm_indicator_le_norm_self
  结论: ‖indicator s f a‖ <= ‖f a‖
  证明: by
  rw [norm_indicator_eq_indicator_norm]
  apply indicator_norm_le_norm_self

Depends on / 依赖: indicator_norm_le_norm_self, norm_indicator_eq_indicator_norm
-/
theorem norm_indicator_le_norm_self : ‖indicator s f a‖ <= ‖f a‖ := by
  rw [norm_indicator_eq_indicator_norm]
  apply indicator_norm_le_norm_self

end SeminormedAddGroup
