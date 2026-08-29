/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.EReal.Basic
public import Mathlib.NumberTheory.LSeries.Basic

/-!
# Convergence of L-series

We define `LSeries.abscissaOfAbsConv f` (as an `EReal`) to be the infimum
of all real numbers `x` such that the L-series of `f` converges for complex arguments with
real part `x` and provide some results about it.

## Tags

L-series, abscissa of convergence
-/

@[expose] public section

open Complex

/--
Definition of `LSeries.abscissaOfAbsConv` / `LSeries.abscissaOfAbsConv` 的定义

English:
definition LSeries.abscissaOfAbsConv
  signature: (f : Nat -> Complex)
  body: sInf Real.toEReal '' {x : Real | LSeriesSummable f x}

中文:
定义 LSeries.abscissaOfAbsConv
  签名: (f : 自然数 -> 复形)
  定义体: sInf Real.toEReal '' {x : Real | LSeriesSummable f x}

Depends on / 依赖: LSeriesSummable, Real.toEReal, toEReal
-/
noncomputable def LSeries.abscissaOfAbsConv (f : Nat -> Complex) : EReal :=
sInf Real.toEReal '' {x : Real | LSeriesSummable f x}

/--
lemma `LSeries.abscissaOfAbsConv_congr` / 引理 `LSeries.abscissaOfAbsConv_congr`

English:
lemma LSeries.abscissaOfAbsConv_congr
  given: {f g : Nat -> Complex} (h : forall {n}, n != 0 -> f n = g n)
  proof: congr_arg sInf congr_arg _ Set.ext fun x => LSeriesSummable_congr x h

中文:
引理 LSeries.abscissaOfAbsConv_congr
  条件: {f g : 自然数 -> 复形} (h : 对任意 {n}, n != 0 -> f n = g n)
  证明: congr_arg sInf congr_arg _ Set.ext fun x => LSeriesSummable_congr x h

Depends on / 依赖: LSeriesSummable_congr, Set.ext, congr_arg
-/
lemma LSeries.abscissaOfAbsConv_congr {f g : Nat -> Complex} (h : forall {n}, n != 0 -> f n = g n) :
    abscissaOfAbsConv f = abscissaOfAbsConv g :=
congr_arg sInf congr_arg _ Set.ext fun x => LSeriesSummable_congr x h

open Filter in
/--
lemma `LSeries.abscissaOfAbsConv_congr'` / 引理 `LSeries.abscissaOfAbsConv_congr'`

English:
lemma LSeries.abscissaOfAbsConv_congr'
  given: {f g : Nat -> Complex} (h : f =ᶠ[atTop] g)
  proof: congr_arg sInf congr_arg _ Set.ext fun x => LSeriesSummable_congr' x h

中文:
引理 LSeries.abscissaOfAbsConv_congr'
  条件: {f g : 自然数 -> 复形} (h : f =ᶠ[atTop] g)
  证明: congr_arg sInf congr_arg _ Set.ext fun x => LSeriesSummable_congr' x h

Depends on / 依赖: LSeriesSummable_congr, Set.ext, congr_arg
-/
lemma LSeries.abscissaOfAbsConv_congr' {f g : Nat -> Complex} (h : f =ᶠ[atTop] g) :
    abscissaOfAbsConv f = abscissaOfAbsConv g :=
congr_arg sInf congr_arg _ Set.ext fun x => LSeriesSummable_congr' x h

open LSeries

/--
lemma `LSeriesSummable_of_abscissaOfAbsConv_lt_re` / 引理 `LSeriesSummable_of_abscissaOfAbsConv_lt_re`

English:
lemma LSeriesSummable_of_abscissaOfAbsConv_lt_re
  statement: {f : Nat -> Complex} {s : Complex}
  proof: by
  obtain ⟨y, hy, hys⟩ : exists a : Real, LSeriesSummable f a ∧ a < s.re := by
    simpa [abscissaOfAbsConv, sInf_lt_iff] using hs
exact hy.of_re_le_re ofReal_re y ▸ hys.le

中文:
引理 LSeriesSummable_of_abscissaOfAbsConv_lt_re
  结论: {f : 自然数 -> 复形} {s : 复形}
  证明: by
  obtain ⟨y, hy, hys⟩ : exists a : Real, LSeriesSummable f a ∧ a < s.re := by
    simpa [abscissaOfAbsConv, sInf_lt_iff] using hs
exact hy.of_re_le_re ofReal_re y ▸ hys.le

Depends on / 依赖: LSeriesSummable, abscissaOfAbsConv, hy.of_re_le_re, hys.le, ofReal_re, of_re_le_re, s.re, sInf_lt_iff
-/
lemma LSeriesSummable_of_abscissaOfAbsConv_lt_re {f : Nat -> Complex} {s : Complex}
    (hs : abscissaOfAbsConv f < s.re) : LSeriesSummable f s := by
  obtain ⟨y, hy, hys⟩ : exists a : Real, LSeriesSummable f a ∧ a < s.re := by
    simpa [abscissaOfAbsConv, sInf_lt_iff] using hs
exact hy.of_re_le_re ofReal_re y ▸ hys.le

/--
lemma `LSeriesSummable_lt_re_of_abscissaOfAbsConv_lt_re` / 引理 `LSeriesSummable_lt_re_of_abscissaOfAbsConv_lt_re`

English:
lemma LSeriesSummable_lt_re_of_abscissaOfAbsConv_lt_re
  statement: {f : Nat -> Complex} {s : Complex}
  proof: by
  obtain ⟨x, hx₁, hx₂⟩ := EReal.exists_between_coe_real hs
  exact ⟨x, by simpa using hx₂, LSeriesSummable_of_abscissaOfAbsConv_lt_re hx₁⟩

中文:
引理 LSeriesSummable_lt_re_of_abscissaOfAbsConv_lt_re
  结论: {f : 自然数 -> 复形} {s : 复形}
  证明: by
  obtain ⟨x, hx₁, hx₂⟩ := EReal.exists_between_coe_real hs
  exact ⟨x, by simpa using hx₂, LSeriesSummable_of_abscissaOfAbsConv_lt_re hx₁⟩

Depends on / 依赖: EReal.exists_between_coe_real, LSeriesSummable_of_abscissaOfAbsConv_lt_re, exists_between_coe_real
-/
lemma LSeriesSummable_lt_re_of_abscissaOfAbsConv_lt_re {f : Nat -> Complex} {s : Complex}
    (hs : abscissaOfAbsConv f < s.re) :
    exists x : Real, x < s.re ∧ LSeriesSummable f x := by
  obtain ⟨x, hx₁, hx₂⟩ := EReal.exists_between_coe_real hs
  exact ⟨x, by simpa using hx₂, LSeriesSummable_of_abscissaOfAbsConv_lt_re hx₁⟩

/--
lemma `LSeriesSummable.abscissaOfAbsConv_le` / 引理 `LSeriesSummable.abscissaOfAbsConv_le`

English:
lemma LSeriesSummable.abscissaOfAbsConv_le
  given: {f : Nat -> Complex} {s : Complex} (h : LSeriesSummable f s)
  proof: sInf_le by simpa using h.of_re_le_re (by simp)

中文:
引理 LSeriesSummable.abscissaOfAbsConv_le
  条件: {f : 自然数 -> 复形} {s : 复形} (h : LSeriesSummable f s)
  证明: sInf_le by simpa using h.of_re_le_re (by simp)

Depends on / 依赖: h.of_re_le_re, of_re_le_re, sInf_le
-/
lemma LSeriesSummable.abscissaOfAbsConv_le {f : Nat -> Complex} {s : Complex} (h : LSeriesSummable f s) :
    abscissaOfAbsConv f <= s.re :=
sInf_le by simpa using h.of_re_le_re (by simp)

/--
lemma `LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable` / 引理 `LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable`

English:
lemma LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
  statement: {f : Nat -> Complex} {x : Real}
  proof: by
  refine sInf_le_iff.mpr fun y hy => le_of_forall_gt_imp_ge_of_dense fun a => ?_
  replace hy : forall (a : Real), LSeriesSummable f a -> y <= a := by simpa [mem_lowerBounds] using hy
  cases a with
  | coe a₀ => exact_mod_cast fun ha => hy a₀ (h a₀ ha)
  | bot => simp
  | top => simp

中文:
引理 LSeries.abscissaOfAbsConv_le_of_对任意_lt_LSeriesSummable
  结论: {f : 自然数 -> 复形} {x : 实数}
  证明: by
  refine sInf_le_iff.mpr fun y hy => le_of_forall_gt_imp_ge_of_dense fun a => ?_
  replace hy : forall (a : Real), LSeriesSummable f a -> y <= a := by simpa [mem_lowerBounds] using hy
  cases a with
  | coe a₀ => exact_mod_cast fun ha => hy a₀ (h a₀ ha)
  | bot => simp
  | top => simp

Depends on / 依赖: LSeriesSummable, le_of_forall_gt_imp_ge_of_dense, mem_lowerBounds, replace, sInf_le_iff, sInf_le_iff.mpr
-/
lemma LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable {f : Nat -> Complex} {x : Real}
    (h : forall y : Real, x < y -> LSeriesSummable f y) :
    abscissaOfAbsConv f <= x := by
  refine sInf_le_iff.mpr fun y hy => le_of_forall_gt_imp_ge_of_dense fun a => ?_
  replace hy : forall (a : Real), LSeriesSummable f a -> y <= a := by simpa [mem_lowerBounds] using hy
  cases a with
  | coe a₀ => exact_mod_cast fun ha => hy a₀ (h a₀ ha)
  | bot => simp
  | top => simp

/--
lemma `LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable'` / 引理 `LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable'`

English:
lemma LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable'
  statement: {f : Nat -> Complex} {x : EReal}
  proof: by
  cases x with
| coe => exact abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable mod_cast h
  | top => exact le_top
  | bot =>
refine le_of_eq sInf_eq_bot.mpr fun y hy => ?_
    cases y with
    | bot => simp at hy
| coe y => exact ⟨_, ⟨_, h _ EReal.bot_lt_coe _, rfl⟩, mod_cast sub_one_lt y⟩
| top => exact ⟨_, ⟨_, h _ EReal.bot_lt_coe 0, rfl⟩, EReal.zero_lt_top⟩

中文:
引理 LSeries.abscissaOfAbsConv_le_of_对任意_lt_LSeriesSummable'
  结论: {f : 自然数 -> 复形} {x : E实数}
  证明: by
  cases x with
| coe => exact abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable mod_cast h
  | top => exact le_top
  | bot =>
refine le_of_eq sInf_eq_bot.mpr fun y hy => ?_
    cases y with
    | bot => simp at hy
| coe y => exact ⟨_, ⟨_, h _ EReal.bot_lt_coe _, rfl⟩, mod_cast sub_one_lt y⟩
| top => exact ⟨_, ⟨_, h _ EReal.bot_lt_coe 0, rfl⟩, EReal.zero_lt_top⟩

Depends on / 依赖: EReal.bot_lt_coe, EReal.zero_lt_top, abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable, bot_lt_coe, le_of_eq, le_top, mod_cast, sInf_eq_bot, sInf_eq_bot.mpr, sub_one_lt, zero_lt_top
-/
lemma LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable' {f : Nat -> Complex} {x : EReal}
    (h : forall y : Real, x < y -> LSeriesSummable f y) :
    abscissaOfAbsConv f <= x := by
  cases x with
| coe => exact abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable mod_cast h
  | top => exact le_top
  | bot =>
refine le_of_eq sInf_eq_bot.mpr fun y hy => ?_
    cases y with
    | bot => simp at hy
| coe y => exact ⟨_, ⟨_, h _ EReal.bot_lt_coe _, rfl⟩, mod_cast sub_one_lt y⟩
| top => exact ⟨_, ⟨_, h _ EReal.bot_lt_coe 0, rfl⟩, EReal.zero_lt_top⟩

/--
lemma `LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow` / 引理 `LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow`

English:
lemma LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow
  statement: {f : Nat -> Complex} {x : Real}
  proof: by
  rw [show x = x + 1 - 1 by ring] at h
  by_contra! H
  obtain ⟨y, hy₁, hy₂⟩ := EReal.exists_between_coe_real H
  exact (LSeriesSummable_of_le_const_mul_rpow (s := y) (EReal.coe_lt_coe_iff.mp hy₁) h
.abscissaOfAbsConv_le.trans_lt hy₂).false

中文:
引理 LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow
  结论: {f : 自然数 -> 复形} {x : 实数}
  证明: by
  rw [show x = x + 1 - 1 by ring] at h
  by_contra! H
  obtain ⟨y, hy₁, hy₂⟩ := EReal.exists_between_coe_real H
  exact (LSeriesSummable_of_le_const_mul_rpow (s := y) (EReal.coe_lt_coe_iff.mp hy₁) h
.abscissaOfAbsConv_le.trans_lt hy₂).false

Depends on / 依赖: EReal.coe_lt_coe_iff.mp, EReal.exists_between_coe_real, LSeriesSummable_of_le_const_mul_rpow, abscissaOfAbsConv_le, abscissaOfAbsConv_le.trans_lt, coe_lt_coe_iff, exists_between_coe_real, trans_lt
-/
lemma LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow {f : Nat -> Complex} {x : Real}
    (h : exists C, forall n != 0, ‖f n‖ <= C * n ^ x) : abscissaOfAbsConv f <= x + 1 := by
  rw [show x = x + 1 - 1 by ring] at h
  by_contra! H
  obtain ⟨y, hy₁, hy₂⟩ := EReal.exists_between_coe_real H
  exact (LSeriesSummable_of_le_const_mul_rpow (s := y) (EReal.coe_lt_coe_iff.mp hy₁) h
.abscissaOfAbsConv_le.trans_lt hy₂).false

open Filter in
/--
lemma `LSeries.abscissaOfAbsConv_le_of_isBigO_rpow` / 引理 `LSeries.abscissaOfAbsConv_le_of_isBigO_rpow`

English:
lemma LSeries.abscissaOfAbsConv_le_of_isBigO_rpow
  statement: {f : Nat -> Complex} {x : Real}
  proof: by
  rw [show x = x + 1 - 1 by ring] at h
  by_contra! H
  obtain ⟨y, hy₁, hy₂⟩ := EReal.exists_between_coe_real H
  exact (LSeriesSummable_of_isBigO_rpow (s := y) (EReal.coe_lt_coe_iff.mp hy₁) h
.abscissaOfAbsConv_le.trans_lt hy₂).false

中文:
引理 LSeries.abscissaOfAbsConv_le_of_isBigO_rpow
  结论: {f : 自然数 -> 复形} {x : 实数}
  证明: by
  rw [show x = x + 1 - 1 by ring] at h
  by_contra! H
  obtain ⟨y, hy₁, hy₂⟩ := EReal.exists_between_coe_real H
  exact (LSeriesSummable_of_isBigO_rpow (s := y) (EReal.coe_lt_coe_iff.mp hy₁) h
.abscissaOfAbsConv_le.trans_lt hy₂).false

Depends on / 依赖: EReal.coe_lt_coe_iff.mp, EReal.exists_between_coe_real, LSeriesSummable_of_isBigO_rpow, abscissaOfAbsConv_le, abscissaOfAbsConv_le.trans_lt, coe_lt_coe_iff, exists_between_coe_real, trans_lt
-/
lemma LSeries.abscissaOfAbsConv_le_of_isBigO_rpow {f : Nat -> Complex} {x : Real}
    (h : f =O[atTop] fun n => (n : Real) ^ x) :
    abscissaOfAbsConv f <= x + 1 := by
  rw [show x = x + 1 - 1 by ring] at h
  by_contra! H
  obtain ⟨y, hy₁, hy₂⟩ := EReal.exists_between_coe_real H
  exact (LSeriesSummable_of_isBigO_rpow (s := y) (EReal.coe_lt_coe_iff.mp hy₁) h
.abscissaOfAbsConv_le.trans_lt hy₂).false

/--
lemma `LSeries.abscissaOfAbsConv_le_of_le_const` / 引理 `LSeries.abscissaOfAbsConv_le_of_le_const`

English:
lemma LSeries.abscissaOfAbsConv_le_of_le_const
  given: {f : Nat -> Complex} (h : exists C, forall n != 0, ‖f n‖ <= C)
  proof: by
  simpa using abscissaOfAbsConv_le_of_le_const_mul_rpow (x := 0) (by simpa using h)

中文:
引理 LSeries.abscissaOfAbsConv_le_of_le_const
  条件: {f : 自然数 -> 复形} (h : 存在 C, 对任意 n != 0, ‖f n‖ <= C)
  证明: by
  simpa using abscissaOfAbsConv_le_of_le_const_mul_rpow (x := 0) (by simpa using h)

Depends on / 依赖: abscissaOfAbsConv_le_of_le_const_mul_rpow
-/
lemma LSeries.abscissaOfAbsConv_le_of_le_const {f : Nat -> Complex} (h : exists C, forall n != 0, ‖f n‖ <= C) :
    abscissaOfAbsConv f <= 1 := by
  simpa using abscissaOfAbsConv_le_of_le_const_mul_rpow (x := 0) (by simpa using h)

open Filter in
/--
lemma `LSeries.abscissaOfAbsConv_le_one_of_isBigO_one` / 引理 `LSeries.abscissaOfAbsConv_le_one_of_isBigO_one`

English:
lemma LSeries.abscissaOfAbsConv_le_one_of_isBigO_one
  given: {f : Nat -> Complex} (h : f =O[atTop] fun _ => (1 : Real))
  proof: by
  simpa using abscissaOfAbsConv_le_of_isBigO_rpow (x := 0) (by simpa using h)

中文:
引理 LSeries.abscissaOfAbsConv_le_one_of_isBigO_one
  条件: {f : 自然数 -> 复形} (h : f =O[atTop] fun _ => (1 : 实数))
  证明: by
  simpa using abscissaOfAbsConv_le_of_isBigO_rpow (x := 0) (by simpa using h)

Depends on / 依赖: abscissaOfAbsConv_le_of_isBigO_rpow
-/
lemma LSeries.abscissaOfAbsConv_le_one_of_isBigO_one {f : Nat -> Complex} (h : f =O[atTop] fun _ => (1 : Real)) :
    abscissaOfAbsConv f <= 1 := by
  simpa using abscissaOfAbsConv_le_of_isBigO_rpow (x := 0) (by simpa using h)

/--
lemma `LSeries.summable_real_of_abscissaOfAbsConv_lt` / 引理 `LSeries.summable_real_of_abscissaOfAbsConv_lt`

English:
lemma LSeries.summable_real_of_abscissaOfAbsConv_lt
  statement: {f : Nat -> Real} {x : Real}
  proof: by
  have aux : term (f ·) x = fun n => ↑(if n = 0 then 0 else f n / (n : Real) ^ x) := by
    ext n
    simp [term_def, apply_ite ((↑) : Real -> Complex), ofReal_cpow n.cast_nonneg]
  have := LSeriesSummable_of_abscissaOfAbsConv_lt_re (ofReal_re x ▸ h)
  simp only [LSeriesSummable, aux, summable_ofReal] at this
  refine this.congr_cofinite ?_
  filter_upwards [(Set.finite_singleton 0).compl_mem_cofinite] with n hn
    using if_neg (by simpa using hn)

中文:
引理 LSeries.summable_real_of_abscissaOfAbsConv_lt
  结论: {f : 自然数 -> 实数} {x : 实数}
  证明: by
  have aux : term (f ·) x = fun n => ↑(if n = 0 then 0 else f n / (n : Real) ^ x) := by
    ext n
    simp [term_def, apply_ite ((↑) : Real -> Complex), ofReal_cpow n.cast_nonneg]
  have := LSeriesSummable_of_abscissaOfAbsConv_lt_re (ofReal_re x ▸ h)
  simp only [LSeriesSummable, aux, summable_ofReal] at this
  refine this.congr_cofinite ?_
  filter_upwards [(Set.finite_singleton 0).compl_mem_cofinite] with n hn
    using if_neg (by simpa using hn)

Depends on / 依赖: LSeriesSummable, LSeriesSummable_of_abscissaOfAbsConv_lt_re, Set.finite_singleton, apply_ite, cast_nonneg, compl_mem_cofinite, congr_cofinite, filter_upwards, finite_singleton, if_neg, n.cast_nonneg, ofReal_cpow, ofReal_re, summable_ofReal, term_def, this.congr_cofinite
-/
lemma LSeries.summable_real_of_abscissaOfAbsConv_lt {f : Nat -> Real} {x : Real}
    (h : abscissaOfAbsConv (f ·) < x) :
    Summable fun n : Nat => f n / (n : Real) ^ x := by
  have aux : term (f ·) x = fun n => ↑(if n = 0 then 0 else f n / (n : Real) ^ x) := by
    ext n
    simp [term_def, apply_ite ((↑) : Real -> Complex), ofReal_cpow n.cast_nonneg]
  have := LSeriesSummable_of_abscissaOfAbsConv_lt_re (ofReal_re x ▸ h)
  simp only [LSeriesSummable, aux, summable_ofReal] at this
  refine this.congr_cofinite ?_
  filter_upwards [(Set.finite_singleton 0).compl_mem_cofinite] with n hn
    using if_neg (by simpa using hn)

/--
lemma `LSeries.abscissaOfAbsConv_binop_le` / 引理 `LSeries.abscissaOfAbsConv_binop_le`

English:
lemma LSeries.abscissaOfAbsConv_binop_le
  statement: {F : (Nat -> Complex) -> (Nat -> Complex) -> (Nat -> Complex)}
  proof: by
  refine abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable' fun x hx => hF ?_ ?_
· exact LSeriesSummable_of_abscissaOfAbsConv_lt_re
      (ofReal_re x).symm ▸ (le_max_left ..).trans_lt hx
· exact LSeriesSummable_of_abscissaOfAbsConv_lt_re
      (ofReal_re x).symm ▸ (le_max_right ..).trans_lt hx

中文:
引理 LSeries.abscissaOfAbsConv_binop_le
  结论: {F : (自然数 -> 复形) -> (自然数 -> 复形) -> (自然数 -> 复形)}
  证明: by
  refine abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable' fun x hx => hF ?_ ?_
· exact LSeriesSummable_of_abscissaOfAbsConv_lt_re
      (ofReal_re x).symm ▸ (le_max_left ..).trans_lt hx
· exact LSeriesSummable_of_abscissaOfAbsConv_lt_re
      (ofReal_re x).symm ▸ (le_max_right ..).trans_lt hx

Depends on / 依赖: LSeriesSummable_of_abscissaOfAbsConv_lt_re, abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable, le_max_left, le_max_right, ofReal_re, trans_lt
-/
lemma LSeries.abscissaOfAbsConv_binop_le {F : (Nat -> Complex) -> (Nat -> Complex) -> (Nat -> Complex)}
    (hF : forall {f g s}, LSeriesSummable f s -> LSeriesSummable g s -> LSeriesSummable (F f g) s)
    (f g : Nat -> Complex) :
    abscissaOfAbsConv (F f g) <= max (abscissaOfAbsConv f) (abscissaOfAbsConv g) := by
  refine abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable' fun x hx => hF ?_ ?_
· exact LSeriesSummable_of_abscissaOfAbsConv_lt_re
      (ofReal_re x).symm ▸ (le_max_left ..).trans_lt hx
· exact LSeriesSummable_of_abscissaOfAbsConv_lt_re
      (ofReal_re x).symm ▸ (le_max_right ..).trans_lt hx
