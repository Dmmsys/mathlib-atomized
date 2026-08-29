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

variable {c : Real} {f g : Nat -> Bool} {n : Nat}

/--
Definition of `cantorFunctionAux` / `cantorFunctionAux` 的定义

English:
definition cantorFunctionAux
  signature: (c : Real) (f : Nat -> Bool) (n : Nat)
  body: cond (f n) (c ^ n) 0

@[simp]

中文:
定义 cantorFunctionAux
  签名: (c : 实数) (f : 自然数 -> 布尔值) (n : 自然数)
  定义体: cond (f n) (c ^ n) 0

@[simp]
-/
def cantorFunctionAux (c : Real) (f : Nat -> Bool) (n : Nat) : Real :=
  cond (f n) (c ^ n) 0

@[simp]
/--
theorem `cantorFunctionAux_true` / 定理 `cantorFunctionAux_true`

English:
theorem cantorFunctionAux_true
  given: (h : f n = true)
  statement: cantorFunctionAux c f n = c ^ n
  proof: by
  simp [cantorFunctionAux, h]

@[simp]

中文:
定理 cantorFunctionAux_true
  条件: (h : f n = true)
  结论: cantorFunctionAux c f n = c ^ n
  证明: by
  simp [cantorFunctionAux, h]

@[simp]

Depends on / 依赖: cantorFunctionAux
-/
theorem cantorFunctionAux_true (h : f n = true) : cantorFunctionAux c f n = c ^ n := by
  simp [cantorFunctionAux, h]

@[simp]
/--
theorem `cantorFunctionAux_false` / 定理 `cantorFunctionAux_false`

English:
theorem cantorFunctionAux_false
  given: (h : f n = false)
  statement: cantorFunctionAux c f n = 0
  proof: by
  simp [cantorFunctionAux, h]

中文:
定理 cantorFunctionAux_false
  条件: (h : f n = false)
  结论: cantorFunctionAux c f n = 0
  证明: by
  simp [cantorFunctionAux, h]

Depends on / 依赖: cantorFunctionAux
-/
theorem cantorFunctionAux_false (h : f n = false) : cantorFunctionAux c f n = 0 := by
  simp [cantorFunctionAux, h]

/--
theorem `cantorFunctionAux_nonneg` / 定理 `cantorFunctionAux_nonneg`

English:
theorem cantorFunctionAux_nonneg
  given: (h : 0 <= c)
  statement: 0 <= cantorFunctionAux c f n
  proof: by
  cases h' : f n
  · simp [h']
  · simpa [h'] using pow_nonneg h _

中文:
定理 cantorFunctionAux_nonneg
  条件: (h : 0 <= c)
  结论: 0 <= cantorFunctionAux c f n
  证明: by
  cases h' : f n
  · simp [h']
  · simpa [h'] using pow_nonneg h _

Depends on / 依赖: pow_nonneg
-/
theorem cantorFunctionAux_nonneg (h : 0 <= c) : 0 <= cantorFunctionAux c f n := by
  cases h' : f n
  · simp [h']
  · simpa [h'] using pow_nonneg h _

/--
theorem `cantorFunctionAux_eq` / 定理 `cantorFunctionAux_eq`

English:
theorem cantorFunctionAux_eq
  given: (h : f n = g n)
  proof: by simp [cantorFunctionAux, h]

中文:
定理 cantorFunctionAux_eq
  条件: (h : f n = g n)
  证明: by simp [cantorFunctionAux, h]

Depends on / 依赖: cantorFunctionAux
-/
theorem cantorFunctionAux_eq (h : f n = g n) :
    cantorFunctionAux c f n = cantorFunctionAux c g n := by simp [cantorFunctionAux, h]

/--
theorem `cantorFunctionAux_zero` / 定理 `cantorFunctionAux_zero`

English:
theorem cantorFunctionAux_zero
  given: (f : Nat -> Bool)
  statement: cantorFunctionAux c f 0 = cond (f 0) 1 0
  proof: by
  cases h : f 0 <;> simp [h]

中文:
定理 cantorFunctionAux_zero
  条件: (f : 自然数 -> 布尔值)
  结论: cantorFunctionAux c f 0 = cond (f 0) 1 0
  证明: by
  cases h : f 0 <;> simp [h]
-/
theorem cantorFunctionAux_zero (f : Nat -> Bool) : cantorFunctionAux c f 0 = cond (f 0) 1 0 := by
  cases h : f 0 <;> simp [h]

/--
theorem `cantorFunctionAux_succ` / 定理 `cantorFunctionAux_succ`

English:
theorem cantorFunctionAux_succ
  given: (f : Nat -> Bool)
  proof: by
  ext n
  cases h : f (n + 1) <;> simp [h, _root_.pow_succ']

中文:
定理 cantorFunctionAux_succ
  条件: (f : 自然数 -> 布尔值)
  证明: by
  ext n
  cases h : f (n + 1) <;> simp [h, _root_.pow_succ']

Depends on / 依赖: _root_, _root_.pow_succ, pow_succ
-/
theorem cantorFunctionAux_succ (f : Nat -> Bool) :
    (fun n => cantorFunctionAux c f (n + 1)) = fun n =>
      c * cantorFunctionAux c (fun n => f (n + 1)) n := by
  ext n
  cases h : f (n + 1) <;> simp [h, _root_.pow_succ']

/--
theorem `summable_cantor_function` / 定理 `summable_cantor_function`

English:
theorem summable_cantor_function
  given: (f : Nat -> Bool) (h1 : 0 <= c) (h2 : c < 1)
  proof: by
  apply (summable_geometric_of_lt_one h1 h2).summable_of_eq_zero_or_self
  intro n; cases h : f n <;> simp [h]

中文:
定理 summable_cantor_function
  条件: (f : 自然数 -> 布尔值) (h1 : 0 <= c) (h2 : c < 1)
  证明: by
  apply (summable_geometric_of_lt_one h1 h2).summable_of_eq_zero_or_self
  intro n; cases h : f n <;> simp [h]

Depends on / 依赖: summable_geometric_of_lt_one, summable_of_eq_zero_or_self
-/
theorem summable_cantor_function (f : Nat -> Bool) (h1 : 0 <= c) (h2 : c < 1) :
    Summable (cantorFunctionAux c f) := by
  apply (summable_geometric_of_lt_one h1 h2).summable_of_eq_zero_or_self
  intro n; cases h : f n <;> simp [h]

/--
Definition of `cantorFunction` / `cantorFunction` 的定义

English:
definition cantorFunction
  signature: (c : Real) (f : Nat -> Bool)
  body: ∑' n, cantorFunctionAux c f n

中文:
定义 cantorFunction
  签名: (c : 实数) (f : 自然数 -> 布尔值)
  定义体: ∑' n, cantorFunctionAux c f n

Depends on / 依赖: cantorFunctionAux
-/
def cantorFunction (c : Real) (f : Nat -> Bool) : Real :=
  ∑' n, cantorFunctionAux c f n

/--
theorem `cantorFunction_le` / 定理 `cantorFunction_le`

English:
theorem cantorFunction_le
  given: (h1 : 0 <= c) (h2 : c < 1) (h3 : forall n, f n -> g n)
  proof: by
  apply (summable_cantor_function f h1 h2).tsum_le_tsum _ (summable_cantor_function g h1 h2)
  intro n; cases h : f n
  · simp [h, cantorFunctionAux_nonneg h1]
  replace h3 : g n = true := h3 n h; simp [h, h3]

中文:
定理 cantorFunction_le
  条件: (h1 : 0 <= c) (h2 : c < 1) (h3 : 对任意 n, f n -> g n)
  证明: by
  apply (summable_cantor_function f h1 h2).tsum_le_tsum _ (summable_cantor_function g h1 h2)
  intro n; cases h : f n
  · simp [h, cantorFunctionAux_nonneg h1]
  replace h3 : g n = true := h3 n h; simp [h, h3]

Depends on / 依赖: cantorFunctionAux_nonneg, replace, summable_cantor_function, tsum_le_tsum
-/
theorem cantorFunction_le (h1 : 0 <= c) (h2 : c < 1) (h3 : forall n, f n -> g n) :
    cantorFunction c f <= cantorFunction c g := by
  apply (summable_cantor_function f h1 h2).tsum_le_tsum _ (summable_cantor_function g h1 h2)
  intro n; cases h : f n
  · simp [h, cantorFunctionAux_nonneg h1]
  replace h3 : g n = true := h3 n h; simp [h, h3]

/--
theorem `cantorFunction_succ` / 定理 `cantorFunction_succ`

English:
theorem cantorFunction_succ
  given: (f : Nat -> Bool) (h1 : 0 <= c) (h2 : c < 1)
  proof: by
  rw [cantorFunction]; rw [(summable_cantor_function f h1 h2).tsum_eq_zero_add]
  rw [cantorFunctionAux_succ]; rw [tsum_mul_left]; rw [cantorFunctionAux]; rw [pow_zero]; rw [cantorFunction]

中文:
定理 cantorFunction_succ
  条件: (f : 自然数 -> 布尔值) (h1 : 0 <= c) (h2 : c < 1)
  证明: by
  rw [cantorFunction]; rw [(summable_cantor_function f h1 h2).tsum_eq_zero_add]
  rw [cantorFunctionAux_succ]; rw [tsum_mul_left]; rw [cantorFunctionAux]; rw [pow_zero]; rw [cantorFunction]

Depends on / 依赖: cantorFunction, cantorFunctionAux, cantorFunctionAux_succ, pow_zero, summable_cantor_function, tsum_eq_zero_add, tsum_mul_left
-/
theorem cantorFunction_succ (f : Nat -> Bool) (h1 : 0 <= c) (h2 : c < 1) :
    cantorFunction c f = cond (f 0) 1 0 + c * cantorFunction c fun n => f (n + 1) := by
  rw [cantorFunction]; rw [(summable_cantor_function f h1 h2).tsum_eq_zero_add]
  rw [cantorFunctionAux_succ]; rw [tsum_mul_left]; rw [cantorFunctionAux]; rw [pow_zero]; rw [cantorFunction]

/--
theorem `increasing_cantorFunction` / 定理 `increasing_cantorFunction`

English:
theorem increasing_cantorFunction
  statement: (h1 : 0 < c) (h2 : c < 1 / 2) {n : Nat} {f g : Nat -> Bool}
  proof: by
  have h3 : c < 1 := by
    apply h2.trans
    norm_num
  induction n generalizing f g with
  | zero =>
    let f_max : Nat -> Bool := fun n => Nat.rec false (fun _ _ => true) n
    have hf_max : forall n, f n -> f_max n := by
      intro n hn
      cases n
      · rw [fn] at hn
        contradic

中文:
定理 increasing_cantorFunction
  结论: (h1 : 0 < c) (h2 : c < 1 / 2) {n : 自然数} {f g : 自然数 -> 布尔值}
  证明: by
  have h3 : c < 1 := by
    apply h2.trans
    norm_num
  induction n generalizing f g with
  | zero =>
    let f_max : Nat -> Bool := fun n => Nat.rec false (fun _ _ => true) n
    have hf_max : forall n, f n -> f_max n := by
      intro n hn
      cases n
      · rw [fn] at hn
        contradic

Depends on / 依赖: Nat.rec, cantorFunction_le, f_max, g_min, generalizing, h2.trans, hf_max, hg_min, le_of_lt, lt_of_lt_, trans_lt
-/
theorem increasing_cantorFunction (h1 : 0 < c) (h2 : c < 1 / 2) {n : Nat} {f g : Nat -> Bool}
    (hn : forall k < n, f k = g k) (fn : f n = false) (gn : g n = true) :
    cantorFunction c f < cantorFunction c g := by
  have h3 : c < 1 := by
    apply h2.trans
    norm_num
  induction n generalizing f g with
  | zero =>
    let f_max : Nat -> Bool := fun n => Nat.rec false (fun _ _ => true) n
    have hf_max : forall n, f n -> f_max n := by
      intro n hn
      cases n
      · rw [fn] at hn
        contradiction
      simp [f_max]
    let g_min : Nat -> Bool := fun n => Nat.rec true (fun _ _ => false) n
    have hg_min : forall n, g_min n -> g n := by
      intro n hn
      cases n
      · rw [gn]
      simp at hn
    apply (cantorFunction_le (le_of_lt h1) h3 hf_max).trans_lt
    refine lt_of_lt_of_le ?_ (cantorFunction_le (le_of_lt h1) h3 hg_min)
    have : c / (1 - c) < 1 := by
      rw [div_lt_one]; rw [lt_sub_iff_add_lt]
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
  rw [cantorFunction_succ f h1.le h3]; rw [cantorFunction_succ g h1.le h3]
  rw [hn 0 <| zero_lt_succ n]
  gcongr
  exact ih (fun k hk => hn _ <| Nat.succ_lt_succ hk) fn gn

/--
theorem `cantorFunction_injective` / 定理 `cantorFunction_injective`

English:
theorem cantorFunction_injective
  given: (h1 : 0 < c) (h2 : c < 1 / 2)
  proof: by
  intro f g hfg
  classical
    contrapose hfg with h
    have : exists n, f n != g n := Function.ne_iff.mp h
    let n := Nat.find this
    have hn : forall k : Nat, k < n -> f k = g k := by
      intro k hk
      apply of_not_not
      exact Nat.find_min this hk
    cases fn : f n
    · apply _

中文:
定理 cantorFunction_injective
  条件: (h1 : 0 < c) (h2 : c < 1 / 2)
  证明: by
  intro f g hfg
  classical
    contrapose hfg with h
    have : exists n, f n != g n := Function.ne_iff.mp h
    let n := Nat.find this
    have hn : forall k : Nat, k < n -> f k = g k := by
      intro k hk
      apply of_not_not
      exact Nat.find_min this hk
    cases fn : f n
    · apply _

Depends on / 依赖: Bool.eq_true_of_not_eq_false, Function, Function.ne_iff.mp, Nat.find, Nat.find_min, Nat.find_spec, Ne.symm, _root_, _root_.ne_of_gt, _root_.ne_of_lt, classical, contrapose, eq_true_of_not_eq_false, find_min, find_spec, increasing_cantorFunction, ne_iff, ne_of_gt, ne_of_lt, of_not_not
-/
theorem cantorFunction_injective (h1 : 0 < c) (h2 : c < 1 / 2) :
    Function.Injective (cantorFunction c) := by
  intro f g hfg
  classical
    contrapose hfg with h
    have : exists n, f n != g n := Function.ne_iff.mp h
    let n := Nat.find this
    have hn : forall k : Nat, k < n -> f k = g k := by
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

/--
theorem `mk_real` / 定理 `mk_real`

English:
theorem mk_real
  statement: #Real = 𝔠
  proof: by
  apply le_antisymm
  · rw [Real.equivCauchy.cardinal_eq]
    apply mk_quotient_le.trans
    apply (mk_subtype_le _).trans_eq
    rw [← power_def]; rw [mk_nat]; rw [mkRat]; rw [aleph0_power_aleph0]
  · convert! mk_le_of_injective (cantorFunction_injective _ _)
    · rw [← power_def, mk_bool, mk_n

中文:
定理 mk_real
  结论: #实数 = 𝔠
  证明: by
  apply le_antisymm
  · rw [Real.equivCauchy.cardinal_eq]
    apply mk_quotient_le.trans
    apply (mk_subtype_le _).trans_eq
    rw [← power_def]; rw [mk_nat]; rw [mkRat]; rw [aleph0_power_aleph0]
  · convert! mk_le_of_injective (cantorFunction_injective _ _)
    · rw [← power_def, mk_bool, mk_n

Depends on / 依赖: Real.equivCauchy.cardinal_eq, aleph0_power_aleph0, cantorFunction_injective, cardinal_eq, convert, equivCauchy, le_antisymm, mk_bool, mk_le_of_injective, mk_nat, mk_quotient_le, mk_quotient_le.trans, mk_subtype_le, power_def, trans_eq, two_power_aleph0
-/
theorem mk_real : #Real = 𝔠 := by
  apply le_antisymm
  · rw [Real.equivCauchy.cardinal_eq]
    apply mk_quotient_le.trans
    apply (mk_subtype_le _).trans_eq
    rw [← power_def]; rw [mk_nat]; rw [mkRat]; rw [aleph0_power_aleph0]
  · convert! mk_le_of_injective (cantorFunction_injective _ _)
    · rw [← power_def, mk_bool, mk_nat, two_power_aleph0]
    · exact 1 / 3
    · simp
    · norm_num

/--
theorem `mk_univ_real` / 定理 `mk_univ_real`

English:
theorem mk_univ_real
  statement: #(Set.univ : Set Real) = 𝔠
  proof: by rw [mk_univ, mk_real]

中文:
定理 mk_univ_real
  结论: #(集合.univ : 集合 实数) = 𝔠
  证明: by rw [mk_univ, mk_real]

Depends on / 依赖: mk_real, mk_univ
-/
theorem mk_univ_real : #(Set.univ : Set Real) = 𝔠 := by rw [mk_univ, mk_real]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Uncountable Real
  body: by
  rw [← aleph0_lt_mk_iff]; rw [mk_real]
  exact aleph0_lt_continuum

中文:
实例 :
  签名: 不可数 实数
  定义体: by
  rw [← aleph0_lt_mk_iff]; rw [mk_real]
  exact aleph0_lt_continuum

Depends on / 依赖: aleph0_lt_continuum, aleph0_lt_mk_iff, mk_real
-/
instance : Uncountable Real := by
  rw [← aleph0_lt_mk_iff]; rw [mk_real]
  exact aleph0_lt_continuum

/--
theorem `not_countable_real` / 定理 `not_countable_real`

English:
theorem not_countable_real
  statement: ¬(Set.univ : Set Real).Countable
  proof: not_countable_univ

中文:
定理 not_countable_real
  结论: ¬(集合.univ : 集合 实数).可数
  证明: not_countable_univ

Depends on / 依赖: not_countable_univ
-/
theorem not_countable_real : ¬(Set.univ : Set Real).Countable :=
  not_countable_univ

/--
theorem `mk_Ioi_real` / 定理 `mk_Ioi_real`

English:
theorem mk_Ioi_real
  given: (a : Real)
  statement: #(Ioi a) = 𝔠
  proof: by
  refine le_antisymm (mk_real ▸ mk_set_le _) ?_
  rw [← not_lt]
  intro h
  refine _root_.ne_of_lt ?_ mk_univ_real
  have hu : Iio a union {a} union Ioi a = Set.univ := by
    convert! @Iic_union_Ioi Real _ _
    exact Iio_union_right
  rw [← hu]
  grw [mk_union_le, mk_union_le]
  have h2 : (fun 

中文:
定理 mk_Ioi_real
  条件: (a : 实数)
  结论: #(左开右无界区间 a) = 𝔠
  证明: by
  refine le_antisymm (mk_real ▸ mk_set_le _) ?_
  rw [← not_lt]
  intro h
  refine _root_.ne_of_lt ?_ mk_univ_real
  have hu : Iio a union {a} union Ioi a = Set.univ := by
    convert! @Iic_union_Ioi Real _ _
    exact Iio_union_right
  rw [← hu]
  grw [mk_union_le, mk_union_le]
  have h2 : (fun 

Depends on / 依赖: Iic_union_Ioi, Iio_union_right, Set.univ, _root_, _root_.ne_of_lt, add_lt_of_lt, cantor, convert, image_const_sub_Ioi, le_antisymm, mk_image_le, mk_image_le.trans_lt, mk_real, mk_set_le, mk_singleton, mk_union_le, mk_univ_real, ne_of_lt, not_lt, one_
-/
theorem mk_Ioi_real (a : Real) : #(Ioi a) = 𝔠 := by
  refine le_antisymm (mk_real ▸ mk_set_le _) ?_
  rw [← not_lt]
  intro h
  refine _root_.ne_of_lt ?_ mk_univ_real
  have hu : Iio a union {a} union Ioi a = Set.univ := by
    convert! @Iic_union_Ioi Real _ _
    exact Iio_union_right
  rw [← hu]
  grw [mk_union_le, mk_union_le]
  have h2 : (fun x => a + a - x) '' Ioi a = Iio a := by
    convert! @image_const_sub_Ioi Real _ _ _
    simp
  rw [← h2]
  refine add_lt_of_lt (cantor _).le ?_ h
  refine add_lt_of_lt (cantor _).le (mk_image_le.trans_lt h) ?_
  rw [mk_singleton]
  exact one_lt_aleph0.trans (cantor _)

/--
theorem `mk_Ici_real` / 定理 `mk_Ici_real`

English:
theorem mk_Ici_real
  given: (a : Real)
  statement: #(Ici a) = 𝔠
  proof: le_antisymm (mk_real ▸ mk_set_le _) (mk_Ioi_real a ▸ mk_le_mk_of_subset Ioi_subset_Ici_self)

中文:
定理 mk_Ici_real
  条件: (a : 实数)
  结论: #(左闭右无界区间 a) = 𝔠
  证明: le_antisymm (mk_real ▸ mk_set_le _) (mk_Ioi_real a ▸ mk_le_mk_of_subset Ioi_subset_Ici_self)

Depends on / 依赖: Ioi_subset_Ici_self, le_antisymm, mk_Ioi_real, mk_le_mk_of_subset, mk_real, mk_set_le
-/
theorem mk_Ici_real (a : Real) : #(Ici a) = 𝔠 :=
  le_antisymm (mk_real ▸ mk_set_le _) (mk_Ioi_real a ▸ mk_le_mk_of_subset Ioi_subset_Ici_self)

/--
theorem `mk_Iio_real` / 定理 `mk_Iio_real`

English:
theorem mk_Iio_real
  given: (a : Real)
  statement: #(Iio a) = 𝔠
  proof: by
  refine le_antisymm (mk_real ▸ mk_set_le _) ?_
  have h2 : (fun x => a + a - x) '' Iio a = Ioi a := by
    simp only [image_const_sub_Iio, add_sub_cancel_right]
  exact mk_Ioi_real a ▸ h2 ▸ mk_image_le

中文:
定理 mk_Iio_real
  条件: (a : 实数)
  结论: #(左无界右开区间 a) = 𝔠
  证明: by
  refine le_antisymm (mk_real ▸ mk_set_le _) ?_
  have h2 : (fun x => a + a - x) '' Iio a = Ioi a := by
    simp only [image_const_sub_Iio, add_sub_cancel_right]
  exact mk_Ioi_real a ▸ h2 ▸ mk_image_le

Depends on / 依赖: add_sub_cancel_right, image_const_sub_Iio, le_antisymm, mk_Ioi_real, mk_image_le, mk_real, mk_set_le
-/
theorem mk_Iio_real (a : Real) : #(Iio a) = 𝔠 := by
  refine le_antisymm (mk_real ▸ mk_set_le _) ?_
  have h2 : (fun x => a + a - x) '' Iio a = Ioi a := by
    simp only [image_const_sub_Iio, add_sub_cancel_right]
  exact mk_Ioi_real a ▸ h2 ▸ mk_image_le

/--
theorem `mk_Iic_real` / 定理 `mk_Iic_real`

English:
theorem mk_Iic_real
  given: (a : Real)
  statement: #(Iic a) = 𝔠
  proof: le_antisymm (mk_real ▸ mk_set_le _) (mk_Iio_real a ▸ mk_le_mk_of_subset Iio_subset_Iic_self)

中文:
定理 mk_Iic_real
  条件: (a : 实数)
  结论: #(左无界右闭区间 a) = 𝔠
  证明: le_antisymm (mk_real ▸ mk_set_le _) (mk_Iio_real a ▸ mk_le_mk_of_subset Iio_subset_Iic_self)

Depends on / 依赖: Iio_subset_Iic_self, le_antisymm, mk_Iio_real, mk_le_mk_of_subset, mk_real, mk_set_le
-/
theorem mk_Iic_real (a : Real) : #(Iic a) = 𝔠 :=
  le_antisymm (mk_real ▸ mk_set_le _) (mk_Iio_real a ▸ mk_le_mk_of_subset Iio_subset_Iic_self)

/--
theorem `mk_Ioo_real` / 定理 `mk_Ioo_real`

English:
theorem mk_Ioo_real
  given: {a b : Real} (h : a < b)
  statement: #(Ioo a b) = 𝔠
  proof: by
  refine le_antisymm (mk_real ▸ mk_set_le _) ?_
  have h1 : #((fun x => x - a) '' Ioo a b) <= #(Ioo a b) := mk_image_le
  refine le_trans ?_ h1
  rw [image_sub_const_Ioo]; rw [sub_self]
  replace h := sub_pos_of_lt h
  have h2 : #(Inv.inv '' Ioo 0 (b - a)) <= #(Ioo 0 (b - a)) := mk_image_le
  ref

中文:
定理 mk_Ioo_real
  条件: {a b : 实数} (h : a < b)
  结论: #(开区间 a b) = 𝔠
  证明: by
  refine le_antisymm (mk_real ▸ mk_set_le _) ?_
  have h1 : #((fun x => x - a) '' Ioo a b) <= #(Ioo a b) := mk_image_le
  refine le_trans ?_ h1
  rw [image_sub_const_Ioo]; rw [sub_self]
  replace h := sub_pos_of_lt h
  have h2 : #(Inv.inv '' Ioo 0 (b - a)) <= #(Ioo 0 (b - a)) := mk_image_le
  ref

Depends on / 依赖: Inv.inv, image_inv_eq_inv, image_sub_const_Ioo, inv_Ioo_0_left, le_antisymm, le_trans, mk_Ioi_real, mk_image_le, mk_real, mk_set_le, replace, sub_pos_of_lt, sub_self
-/
theorem mk_Ioo_real {a b : Real} (h : a < b) : #(Ioo a b) = 𝔠 := by
  refine le_antisymm (mk_real ▸ mk_set_le _) ?_
  have h1 : #((fun x => x - a) '' Ioo a b) <= #(Ioo a b) := mk_image_le
  refine le_trans ?_ h1
  rw [image_sub_const_Ioo]; rw [sub_self]
  replace h := sub_pos_of_lt h
  have h2 : #(Inv.inv '' Ioo 0 (b - a)) <= #(Ioo 0 (b - a)) := mk_image_le
  refine le_trans ?_ h2
  rw [image_inv_eq_inv]; rw [inv_Ioo_0_left h]; rw [mk_Ioi_real]

/--
theorem `mk_Ico_real` / 定理 `mk_Ico_real`

English:
theorem mk_Ico_real
  given: {a b : Real} (h : a < b)
  statement: #(Ico a b) = 𝔠
  proof: le_antisymm (mk_real ▸ mk_set_le _) (mk_Ioo_real h ▸ mk_le_mk_of_subset Ioo_subset_Ico_self)

中文:
定理 mk_Ico_real
  条件: {a b : 实数} (h : a < b)
  结论: #(左闭右开区间 a b) = 𝔠
  证明: le_antisymm (mk_real ▸ mk_set_le _) (mk_Ioo_real h ▸ mk_le_mk_of_subset Ioo_subset_Ico_self)

Depends on / 依赖: Ioo_subset_Ico_self, le_antisymm, mk_Ioo_real, mk_le_mk_of_subset, mk_real, mk_set_le
-/
theorem mk_Ico_real {a b : Real} (h : a < b) : #(Ico a b) = 𝔠 :=
  le_antisymm (mk_real ▸ mk_set_le _) (mk_Ioo_real h ▸ mk_le_mk_of_subset Ioo_subset_Ico_self)

/--
theorem `mk_Icc_real` / 定理 `mk_Icc_real`

English:
theorem mk_Icc_real
  given: {a b : Real} (h : a < b)
  statement: #(Icc a b) = 𝔠
  proof: le_antisymm (mk_real ▸ mk_set_le _) (mk_Ioo_real h ▸ mk_le_mk_of_subset Ioo_subset_Icc_self)

中文:
定理 mk_Icc_real
  条件: {a b : 实数} (h : a < b)
  结论: #(闭区间 a b) = 𝔠
  证明: le_antisymm (mk_real ▸ mk_set_le _) (mk_Ioo_real h ▸ mk_le_mk_of_subset Ioo_subset_Icc_self)

Depends on / 依赖: Ioo_subset_Icc_self, le_antisymm, mk_Ioo_real, mk_le_mk_of_subset, mk_real, mk_set_le
-/
theorem mk_Icc_real {a b : Real} (h : a < b) : #(Icc a b) = 𝔠 :=
  le_antisymm (mk_real ▸ mk_set_le _) (mk_Ioo_real h ▸ mk_le_mk_of_subset Ioo_subset_Icc_self)

/--
theorem `mk_Ioc_real` / 定理 `mk_Ioc_real`

English:
theorem mk_Ioc_real
  given: {a b : Real} (h : a < b)
  statement: #(Ioc a b) = 𝔠
  proof: le_antisymm (mk_real ▸ mk_set_le _) (mk_Ioo_real h ▸ mk_le_mk_of_subset Ioo_subset_Ioc_self)

@[simp]

中文:
定理 mk_Ioc_real
  条件: {a b : 实数} (h : a < b)
  结论: #(左开右闭区间 a b) = 𝔠
  证明: le_antisymm (mk_real ▸ mk_set_le _) (mk_Ioo_real h ▸ mk_le_mk_of_subset Ioo_subset_Ioc_self)

@[simp]

Depends on / 依赖: Ioo_subset_Ioc_self, le_antisymm, mk_Ioo_real, mk_le_mk_of_subset, mk_real, mk_set_le
-/
theorem mk_Ioc_real {a b : Real} (h : a < b) : #(Ioc a b) = 𝔠 :=
  le_antisymm (mk_real ▸ mk_set_le _) (mk_Ioo_real h ▸ mk_le_mk_of_subset Ioo_subset_Ioc_self)

@[simp]
/--
lemma `Real.Ioo_countable_iff` / 引理 `Real.Ioo_countable_iff`

English:
lemma Real.Ioo_countable_iff
  given: {x y : Real}
  proof: by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  contrapose! h
  rw [← Cardinal.le_aleph0_iff_set_countable]; rw [Cardinal.mk_Ioo_real h]; rw [not_le]
  exact Cardinal.aleph0_lt_continuum

@[simp]

中文:
引理 实数.Ioo_countable_iff
  条件: {x y : 实数}
  证明: by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  contrapose! h
  rw [← Cardinal.le_aleph0_iff_set_countable]; rw [Cardinal.mk_Ioo_real h]; rw [not_le]
  exact Cardinal.aleph0_lt_continuum

@[simp]

Depends on / 依赖: Cardinal, Cardinal.aleph0_lt_continuum, Cardinal.le_aleph0_iff_set_countable, Cardinal.mk_Ioo_real, aleph0_lt_continuum, contrapose, e.symm.isIso_functor, isIso_functor, le_aleph0_iff_set_countable, mk_Ioo_real, not_le
-/
lemma Real.Ioo_countable_iff {x y : Real} :
    (Ioo x y).Countable ↔ y <= x := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  contrapose! h
  rw [← Cardinal.le_aleph0_iff_set_countable]; rw [Cardinal.mk_Ioo_real h]; rw [not_le]
  exact Cardinal.aleph0_lt_continuum

@[simp]
/--
lemma `Real.Ico_countable_iff` / 引理 `Real.Ico_countable_iff`

English:
lemma Real.Ico_countable_iff
  given: {x y : Real}
  proof: by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  contrapose! h
  rw [← Cardinal.le_aleph0_iff_set_countable]; rw [Cardinal.mk_Ico_real h]; rw [not_le]
  exact Cardinal.aleph0_lt_continuum

@[simp]

中文:
引理 实数.Ico_countable_iff
  条件: {x y : 实数}
  证明: by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  contrapose! h
  rw [← Cardinal.le_aleph0_iff_set_countable]; rw [Cardinal.mk_Ico_real h]; rw [not_le]
  exact Cardinal.aleph0_lt_continuum

@[simp]

Depends on / 依赖: Cardinal, Cardinal.aleph0_lt_continuum, Cardinal.le_aleph0_iff_set_countable, Cardinal.mk_Ico_real, aleph0_lt_continuum, contrapose, le_aleph0_iff_set_countable, mk_Ico_real, not_le
-/
lemma Real.Ico_countable_iff {x y : Real} :
    (Ico x y).Countable ↔ y <= x := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  contrapose! h
  rw [← Cardinal.le_aleph0_iff_set_countable]; rw [Cardinal.mk_Ico_real h]; rw [not_le]
  exact Cardinal.aleph0_lt_continuum

@[simp]
/--
lemma `Real.Ioc_countable_iff` / 引理 `Real.Ioc_countable_iff`

English:
lemma Real.Ioc_countable_iff
  given: {x y : Real}
  proof: by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  contrapose! h
  rw [← Cardinal.le_aleph0_iff_set_countable]; rw [Cardinal.mk_Ioc_real h]; rw [not_le]
  exact Cardinal.aleph0_lt_continuum

@[simp]

中文:
引理 实数.Ioc_countable_iff
  条件: {x y : 实数}
  证明: by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  contrapose! h
  rw [← Cardinal.le_aleph0_iff_set_countable]; rw [Cardinal.mk_Ioc_real h]; rw [not_le]
  exact Cardinal.aleph0_lt_continuum

@[simp]

Depends on / 依赖: Cardinal, Cardinal.aleph0_lt_continuum, Cardinal.le_aleph0_iff_set_countable, Cardinal.mk_Ioc_real, aleph0_lt_continuum, contrapose, le_aleph0_iff_set_countable, mk_Ioc_real, not_le
-/
lemma Real.Ioc_countable_iff {x y : Real} :
    (Ioc x y).Countable ↔ y <= x := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  contrapose! h
  rw [← Cardinal.le_aleph0_iff_set_countable]; rw [Cardinal.mk_Ioc_real h]; rw [not_le]
  exact Cardinal.aleph0_lt_continuum

@[simp]
/--
lemma `Real.Icc_countable_iff` / 引理 `Real.Icc_countable_iff`

English:
lemma Real.Icc_countable_iff
  given: {x y : Real}
  proof: by
  refine ⟨fun h => ?_, fun h => by
    rcases le_iff_eq_or_lt.mp h with heq | hlt
    · simp [heq]
    · simp [hlt]⟩
  contrapose! h
  rw [← Cardinal.le_aleph0_iff_set_countable]; rw [Cardinal.mk_Icc_real h]; rw [not_le]
  exact Cardinal.aleph0_lt_continuum

中文:
引理 实数.Icc_countable_iff
  条件: {x y : 实数}
  证明: by
  refine ⟨fun h => ?_, fun h => by
    rcases le_iff_eq_or_lt.mp h with heq | hlt
    · simp [heq]
    · simp [hlt]⟩
  contrapose! h
  rw [← Cardinal.le_aleph0_iff_set_countable]; rw [Cardinal.mk_Icc_real h]; rw [not_le]
  exact Cardinal.aleph0_lt_continuum

Depends on / 依赖: Cardinal, Cardinal.aleph0_lt_continuum, Cardinal.le_aleph0_iff_set_countable, Cardinal.mk_Icc_real, aleph0_lt_continuum, contrapose, le_aleph0_iff_set_countable, le_iff_eq_or_lt, le_iff_eq_or_lt.mp, mk_Icc_real, not_le
-/
lemma Real.Icc_countable_iff {x y : Real} :
    (Icc x y).Countable ↔ y <= x := by
  refine ⟨fun h => ?_, fun h => by
    rcases le_iff_eq_or_lt.mp h with heq | hlt
    · simp [heq]
    · simp [hlt]⟩
  contrapose! h
  rw [← Cardinal.le_aleph0_iff_set_countable]; rw [Cardinal.mk_Icc_real h]; rw [not_le]
  exact Cardinal.aleph0_lt_continuum

end Cardinal
