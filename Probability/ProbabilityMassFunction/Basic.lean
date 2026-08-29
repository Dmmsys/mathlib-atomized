/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Devon Tuma
-/
module

public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.MeasureTheory.Measure.Dirac

/-!
# Probability mass functions

This file is about probability mass functions or discrete probability measures:
a function `α → ℝ≥0∞` such that the values have (infinite) sum `1`.

Construction of monadic `pure` and `bind` is found in
`Mathlib/Probability/ProbabilityMassFunction/Monad.lean`, other constructions of `PMF`s are found in
`Mathlib/Probability/ProbabilityMassFunction/Constructions.lean`.

Given `p : PMF α`, `PMF.toOuterMeasure` constructs an `OuterMeasure` on `α`,
by assigning each set the sum of the probabilities of each of its elements.
Under this outer measure, every set is Carathéodory-measurable,
so we can further extend this to a `Measure` on `α`, see `PMF.toMeasure`.
`PMF.toMeasure.isProbabilityMeasure` shows this associated measure is a probability measure.
Conversely, given a probability measure `μ` on a measurable space `α` with all singleton sets
measurable, `μ.toPMF` constructs a `PMF` on `α`, setting the probability mass of a point `x`
to be the measure of the singleton set `{x}`.

## Tags

probability mass function, discrete probability measure
-/

@[expose] public section


noncomputable section

variable {α : Type*}

open NNReal ENNReal MeasureTheory

/--
Definition of `PMF.` / `PMF.` 的定义

English:
definition PMF.{u}
  signature: (α : Type u)
  body: { f : α -> Real>=0∞ // HasSum f 1 }

中文:
定义 PMF.{u}
  签名: (α : 类型u)
  定义体: { f : α -> Real>=0∞ // HasSum f 1 }

Depends on / 依赖: HasSum
-/
def PMF.{u} (α : Type u) : Type u :=
  { f : α -> Real>=0∞ // HasSum f 1 }

namespace PMF

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike (PMF α) α Real>=0∞ where
  body: p.1 a
  coe_injective _ _ h := Subtype.ext h

@[ext]

中文:
实例 instFunLike
  签名: : 函数状 (PMF α) α 实数>=0∞ where
  定义体: p.1 a
  coe_injective _ _ h := Subtype.ext h

@[ext]
-/
instance instFunLike : FunLike (PMF α) α Real>=0∞ where
  coe p a := p.1 a
  coe_injective _ _ h := Subtype.ext h

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {p q : PMF α} (h : forall x, p x = q x)
  statement: p = q
  proof: DFunLike.ext p q h

中文:
定理 ext
  条件: {p q : PMF α} (h : 对任意 x, p x = q x)
  结论: p = q
  证明: DFunLike.ext p q h
-/
protected theorem ext {p q : PMF α} (h : forall x, p x = q x) : p = q :=
  DFunLike.ext p q h

/--
theorem `hasSum_coe_one` / 定理 `hasSum_coe_one`

English:
theorem hasSum_coe_one
  given: (p : PMF α)
  statement: HasSum p 1
  proof: p.2

@[simp]

中文:
定理 hasSum_coe_one
  条件: (p : PMF α)
  结论: HasSum p 1
  证明: p.2

@[simp]
-/
theorem hasSum_coe_one (p : PMF α) : HasSum p 1 :=
  p.2

@[simp]
/--
theorem `tsum_coe` / 定理 `tsum_coe`

English:
theorem tsum_coe
  given: (p : PMF α)
  statement: ∑' a, p a = 1
  proof: p.hasSum_coe_one.tsum_eq

中文:
定理 tsum_coe
  条件: (p : PMF α)
  结论: ∑' a, p a = 1
  证明: p.hasSum_coe_one.tsum_eq

Depends on / 依赖: hasSum_coe_one, p.hasSum_coe_one.tsum_eq, tsum_eq
-/
theorem tsum_coe (p : PMF α) : ∑' a, p a = 1 :=
  p.hasSum_coe_one.tsum_eq

/--
theorem `tsum_coe_ne_top` / 定理 `tsum_coe_ne_top`

English:
theorem tsum_coe_ne_top
  given: (p : PMF α)
  statement: ∑' a, p a != ∞
  proof: p.tsum_coe.symm ▸ ENNReal.one_ne_top

中文:
定理 tsum_coe_ne_top
  条件: (p : PMF α)
  结论: ∑' a, p a != ∞
  证明: p.tsum_coe.symm ▸ ENNReal.one_ne_top

Depends on / 依赖: ENNReal, ENNReal.one_ne_top, one_ne_top, p.tsum_coe.symm, tsum_coe
-/
theorem tsum_coe_ne_top (p : PMF α) : ∑' a, p a != ∞ :=
  p.tsum_coe.symm ▸ ENNReal.one_ne_top

/--
theorem `tsum_coe_indicator_ne_top` / 定理 `tsum_coe_indicator_ne_top`

English:
theorem tsum_coe_indicator_ne_top
  given: (p : PMF α) (s : Set α)
  statement: ∑' a, s.indicator p a != ∞
  proof: ne_of_lt (lt_of_le_of_lt
    (ENNReal.tsum_le_tsum (fun _ => Set.indicator_apply_le fun _ => le_rfl))
    (lt_of_le_of_ne le_top p.tsum_coe_ne_top))

@[simp]

中文:
定理 tsum_coe_indicator_ne_top
  条件: (p : PMF α) (s : 集合 α)
  结论: ∑' a, s.indicator p a != ∞
  证明: ne_of_lt (lt_of_le_of_lt
    (ENNReal.tsum_le_tsum (fun _ => Set.indicator_apply_le fun _ => le_rfl))
    (lt_of_le_of_ne le_top p.tsum_coe_ne_top))

@[simp]

Depends on / 依赖: ENNReal, ENNReal.tsum_le_tsum, Set.indicator_apply_le, indicator_apply_le, le_rfl, le_top, lt_of_le_of_lt, lt_of_le_of_ne, ne_of_lt, p.tsum_coe_ne_top, tsum_coe_ne_top, tsum_le_tsum
-/
theorem tsum_coe_indicator_ne_top (p : PMF α) (s : Set α) : ∑' a, s.indicator p a != ∞ :=
  ne_of_lt (lt_of_le_of_lt
    (ENNReal.tsum_le_tsum (fun _ => Set.indicator_apply_le fun _ => le_rfl))
    (lt_of_le_of_ne le_top p.tsum_coe_ne_top))

@[simp]
/--
theorem `coe_ne_zero` / 定理 `coe_ne_zero`

English:
theorem coe_ne_zero
  given: (p : PMF α)
  statement: ⇑p != 0
  proof: fun hp =>
  zero_ne_one ((tsum_zero.symm.trans (tsum_congr fun x => symm (congr_fun hp x))).trans p.tsum_coe)

中文:
定理 coe_ne_zero
  条件: (p : PMF α)
  结论: ⇑p != 0
  证明: fun hp =>
  zero_ne_one ((tsum_zero.symm.trans (tsum_congr fun x => symm (congr_fun hp x))).trans p.tsum_coe)
-/
theorem coe_ne_zero (p : PMF α) : ⇑p != 0 := fun hp =>
  zero_ne_one ((tsum_zero.symm.trans (tsum_congr fun x => symm (congr_fun hp x))).trans p.tsum_coe)

/--
Definition of `support` / `support` 的定义

English:
definition support
  signature: (p : PMF α)
  body: Function.support p

@[simp]

中文:
定义 support
  签名: (p : PMF α)
  定义体: Function.support p

@[simp]

Depends on / 依赖: Function, Function.support, support
-/
def support (p : PMF α) : Set α :=
  Function.support p

@[simp]
/--
theorem `mem_support_iff` / 定理 `mem_support_iff`

English:
theorem mem_support_iff
  given: (p : PMF α) (a : α)
  statement: a in p.support ↔ p a != 0
  proof: Iff.rfl

@[simp]

中文:
定理 mem_support_iff
  条件: (p : PMF α) (a : α)
  结论: a in p.support ↔ p a != 0
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_support_iff (p : PMF α) (a : α) : a in p.support ↔ p a != 0 := Iff.rfl

@[simp]
/--
theorem `support_nonempty` / 定理 `support_nonempty`

English:
theorem support_nonempty
  given: (p : PMF α)
  statement: p.support.Nonempty
  proof: Function.support_nonempty_iff.2 p.coe_ne_zero

@[simp]

中文:
定理 support_nonempty
  条件: (p : PMF α)
  结论: p.support.非空
  证明: Function.support_nonempty_iff.2 p.coe_ne_zero

@[simp]

Depends on / 依赖: Function, Function.support_nonempty_iff, coe_ne_zero, p.coe_ne_zero, support_nonempty_iff
-/
theorem support_nonempty (p : PMF α) : p.support.Nonempty :=
  Function.support_nonempty_iff.2 p.coe_ne_zero

@[simp]
/--
theorem `support_countable` / 定理 `support_countable`

English:
theorem support_countable
  given: (p : PMF α)
  statement: p.support.Countable
  proof: Summable.countable_support_ennreal (tsum_coe_ne_top p)

中文:
定理 support_countable
  条件: (p : PMF α)
  结论: p.support.可数
  证明: Summable.countable_support_ennreal (tsum_coe_ne_top p)

Depends on / 依赖: Summable, Summable.countable_support_ennreal, countable_support_ennreal, tsum_coe_ne_top
-/
theorem support_countable (p : PMF α) : p.support.Countable :=
  Summable.countable_support_ennreal (tsum_coe_ne_top p)

/--
theorem `apply_eq_zero_iff` / 定理 `apply_eq_zero_iff`

English:
theorem apply_eq_zero_iff
  given: (p : PMF α) (a : α)
  statement: p a = 0 ↔ a ∉ p.support
  proof: by
  rw [mem_support_iff]; rw [Classical.not_not]

中文:
定理 apply_eq_zero_iff
  条件: (p : PMF α) (a : α)
  结论: p a = 0 ↔ a ∉ p.support
  证明: by
  rw [mem_support_iff]; rw [Classical.not_not]

Depends on / 依赖: Classical, Classical.not_not, mem_support_iff, not_not
-/
theorem apply_eq_zero_iff (p : PMF α) (a : α) : p a = 0 ↔ a ∉ p.support := by
  rw [mem_support_iff]; rw [Classical.not_not]

/--
theorem `apply_pos_iff` / 定理 `apply_pos_iff`

English:
theorem apply_pos_iff
  given: (p : PMF α) (a : α)
  statement: 0 < p a ↔ a in p.support
  proof: pos_iff_ne_zero.trans (p.mem_support_iff a).symm

中文:
定理 apply_pos_iff
  条件: (p : PMF α) (a : α)
  结论: 0 < p a ↔ a in p.support
  证明: pos_iff_ne_zero.trans (p.mem_support_iff a).symm

Depends on / 依赖: mem_support_iff, p.mem_support_iff, pos_iff_ne_zero, pos_iff_ne_zero.trans
-/
theorem apply_pos_iff (p : PMF α) (a : α) : 0 < p a ↔ a in p.support :=
  pos_iff_ne_zero.trans (p.mem_support_iff a).symm

/--
theorem `apply_eq_one_iff` / 定理 `apply_eq_one_iff`

English:
theorem apply_eq_one_iff
  given: (p : PMF α) (a : α)
  statement: p a = 1 ↔ p.support = {a}
  proof: by
  refine ⟨fun h => Set.Subset.antisymm (fun a' ha' => by_contra fun ha => ?_)
fun a' ha' => ha'.symm ▸ (p.mem_support_iff a).2 fun ha => zero_ne_one ha.symm.trans h,
    fun h => _root_.trans (symm <| tsum_eq_single a
      fun a' ha' => (p.apply_eq_zero_iff a').2 (h.symm ▸ ha')) p.tsum_coe⟩
  suffices 1 < ∑' a, p a from ne_of_lt this p.tsum_coe.symm
  classical
  have : 0 < ∑' b, ite (b = a) 0 (p b) := by
    rw [pos_iff_ne_zero]; rw [ENNReal.summable.tsum_ne_zero_iff]
exact ⟨a', ite_ne_left_iff.2 ⟨ha, Ne.symm (p.mem_support_iff a').2 ha'⟩⟩
  calc
    1 = 1 + 0 := (add_zero 1).symm
    _ < p a + ∑' b, ite (b = a) 0 (p b) :=
      (ENNReal.add_lt_add_of_le_of_lt ENNReal.one_ne_top (le_of_eq h.symm) this)
    _ = ite (a = a) (p a) 0 + ∑' b, ite (b = a) 0 (p b) := by rw [eq_self_iff_true, if_true]
    _ = (∑' b, ite (b = a) (p b) 0) + ∑' b, ite (b = a) 0 (p b) := by
      congr
      exact symm (tsum_eq_single a fun b hb => if_neg hb)
    _ = ∑' b, (ite (b = a) (p b) 0 + ite (b = a) 0 (p b)) := ENNReal.tsum_add.symm
    _ = ∑' b, p b := tsum_congr fun b => by split_ifs <;> simp only [zero_add, add_zero]

中文:
定理 apply_eq_one_iff
  条件: (p : PMF α) (a : α)
  结论: p a = 1 ↔ p.support = {a}
  证明: by
  refine ⟨fun h => Set.Subset.antisymm (fun a' ha' => by_contra fun ha => ?_)
fun a' ha' => ha'.symm ▸ (p.mem_support_iff a).2 fun ha => zero_ne_one ha.symm.trans h,
    fun h => _root_.trans (symm <| tsum_eq_single a
      fun a' ha' => (p.apply_eq_zero_iff a').2 (h.symm ▸ ha')) p.tsum_coe⟩
  suffices 1 < ∑' a, p a from ne_of_lt this p.tsum_coe.symm
  classical
  have : 0 < ∑' b, ite (b = a) 0 (p b) := by
    rw [pos_iff_ne_zero]; rw [ENNReal.summable.tsum_ne_zero_iff]
exact ⟨a', ite_ne_left_iff.2 ⟨ha, Ne.symm (p.mem_support_iff a').2 ha'⟩⟩
  calc
    1 = 1 + 0 := (add_zero 1).symm
    _ < p a + ∑' b, ite (b = a) 0 (p b) :=
      (ENNReal.add_lt_add_of_le_of_lt ENNReal.one_ne_top (le_of_eq h.symm) this)
    _ = ite (a = a) (p a) 0 + ∑' b, ite (b = a) 0 (p b) := by rw [eq_self_iff_true, if_true]
    _ = (∑' b, ite (b = a) (p b) 0) + ∑' b, ite (b = a) 0 (p b) := by
      congr
      exact symm (tsum_eq_single a fun b hb => if_neg hb)
    _ = ∑' b, (ite (b = a) (p b) 0 + ite (b = a) 0 (p b)) := ENNReal.tsum_add.symm
    _ = ∑' b, p b := tsum_congr fun b => by split_ifs <;> simp only [zero_add, add_zero]

Depends on / 依赖: ENNReal, ENNReal.summable.tsum_ne_zero_iff, Ne.symm, Set.Subset.antisymm, Subset, _root_, _root_.trans, antisymm, apply_eq_zero_iff, classical, h.symm, ha.symm.trans, ite_ne_left_iff, mem_support_iff, ne_of_lt, p.apply_eq_zero_iff, p.mem_support_iff, p.tsum_coe, p.tsum_coe.symm, pos_iff_ne_zero
-/
theorem apply_eq_one_iff (p : PMF α) (a : α) : p a = 1 ↔ p.support = {a} := by
  refine ⟨fun h => Set.Subset.antisymm (fun a' ha' => by_contra fun ha => ?_)
fun a' ha' => ha'.symm ▸ (p.mem_support_iff a).2 fun ha => zero_ne_one ha.symm.trans h,
    fun h => _root_.trans (symm <| tsum_eq_single a
      fun a' ha' => (p.apply_eq_zero_iff a').2 (h.symm ▸ ha')) p.tsum_coe⟩
  suffices 1 < ∑' a, p a from ne_of_lt this p.tsum_coe.symm
  classical
  have : 0 < ∑' b, ite (b = a) 0 (p b) := by
    rw [pos_iff_ne_zero]; rw [ENNReal.summable.tsum_ne_zero_iff]
exact ⟨a', ite_ne_left_iff.2 ⟨ha, Ne.symm (p.mem_support_iff a').2 ha'⟩⟩
  calc
    1 = 1 + 0 := (add_zero 1).symm
    _ < p a + ∑' b, ite (b = a) 0 (p b) :=
      (ENNReal.add_lt_add_of_le_of_lt ENNReal.one_ne_top (le_of_eq h.symm) this)
    _ = ite (a = a) (p a) 0 + ∑' b, ite (b = a) 0 (p b) := by rw [eq_self_iff_true, if_true]
    _ = (∑' b, ite (b = a) (p b) 0) + ∑' b, ite (b = a) 0 (p b) := by
      congr
      exact symm (tsum_eq_single a fun b hb => if_neg hb)
    _ = ∑' b, (ite (b = a) (p b) 0 + ite (b = a) 0 (p b)) := ENNReal.tsum_add.symm
    _ = ∑' b, p b := tsum_congr fun b => by split_ifs <;> simp only [zero_add, add_zero]

/--
theorem `coe_le_one` / 定理 `coe_le_one`

English:
theorem coe_le_one
  given: (p : PMF α) (a : α)
  statement: p a <= 1
  proof: by
  classical
  refine hasSum_le (fun b => ?_) (hasSum_ite_eq a (p a)) (hasSum_coe_one p)
  split_ifs with h <;> simp [h]

中文:
定理 coe_le_one
  条件: (p : PMF α) (a : α)
  结论: p a <= 1
  证明: by
  classical
  refine hasSum_le (fun b => ?_) (hasSum_ite_eq a (p a)) (hasSum_coe_one p)
  split_ifs with h <;> simp [h]

Depends on / 依赖: classical, hasSum_coe_one, hasSum_ite_eq, hasSum_le, split_ifs
-/
theorem coe_le_one (p : PMF α) (a : α) : p a <= 1 := by
  classical
  refine hasSum_le (fun b => ?_) (hasSum_ite_eq a (p a)) (hasSum_coe_one p)
  split_ifs with h <;> simp [h]

/--
theorem `apply_ne_top` / 定理 `apply_ne_top`

English:
theorem apply_ne_top
  given: (p : PMF α) (a : α)
  statement: p a != ∞
  proof: ne_of_lt (lt_of_le_of_lt (p.coe_le_one a) ENNReal.one_lt_top)

中文:
定理 apply_ne_top
  条件: (p : PMF α) (a : α)
  结论: p a != ∞
  证明: ne_of_lt (lt_of_le_of_lt (p.coe_le_one a) ENNReal.one_lt_top)

Depends on / 依赖: ENNReal, ENNReal.one_lt_top, coe_le_one, lt_of_le_of_lt, ne_of_lt, one_lt_top, p.coe_le_one
-/
theorem apply_ne_top (p : PMF α) (a : α) : p a != ∞ :=
  ne_of_lt (lt_of_le_of_lt (p.coe_le_one a) ENNReal.one_lt_top)

/--
theorem `apply_lt_top` / 定理 `apply_lt_top`

English:
theorem apply_lt_top
  given: (p : PMF α) (a : α)
  statement: p a < ∞
  proof: lt_of_le_of_ne le_top (p.apply_ne_top a)

中文:
定理 apply_lt_top
  条件: (p : PMF α) (a : α)
  结论: p a < ∞
  证明: lt_of_le_of_ne le_top (p.apply_ne_top a)

Depends on / 依赖: apply_ne_top, le_top, lt_of_le_of_ne, p.apply_ne_top
-/
theorem apply_lt_top (p : PMF α) (a : α) : p a < ∞ :=
  lt_of_le_of_ne le_top (p.apply_ne_top a)

section OuterMeasure

open OuterMeasure

/--
Definition of `toOuterMeasure` / `toOuterMeasure` 的定义

English:
definition toOuterMeasure
  signature: (p : PMF α)
  body: OuterMeasure.sum fun x : α => p x • dirac x

中文:
定义 toOuterMeasure
  签名: (p : PMF α)
  定义体: OuterMeasure.sum fun x : α => p x • dirac x

Depends on / 依赖: OuterMeasure, OuterMeasure.sum
-/
def toOuterMeasure (p : PMF α) : OuterMeasure α :=
  OuterMeasure.sum fun x : α => p x • dirac x

variable (p : PMF α) (s : Set α)

/--
theorem `toOuterMeasure_apply` / 定理 `toOuterMeasure_apply`

English:
theorem toOuterMeasure_apply
  statement: p.toOuterMeasure s = ∑' x, s.indicator p x
  proof: tsum_congr fun x => smul_dirac_apply (p x) x s

@[simp]

中文:
定理 toOuterMeasure_apply
  结论: p.toOuterMeasure s = ∑' x, s.indicator p x
  证明: tsum_congr fun x => smul_dirac_apply (p x) x s

@[simp]

Depends on / 依赖: smul_dirac_apply, tsum_congr
-/
theorem toOuterMeasure_apply : p.toOuterMeasure s = ∑' x, s.indicator p x :=
  tsum_congr fun x => smul_dirac_apply (p x) x s

@[simp]
/--
theorem `toOuterMeasure_caratheodory` / 定理 `toOuterMeasure_caratheodory`

English:
theorem toOuterMeasure_caratheodory
  statement: p.toOuterMeasure.caratheodory = ⊤
  proof: by
refine eq_top_iff.2 le_trans (le_sInf fun x hx => ?_) (le_sum_caratheodory _)
  have ⟨y, hy⟩ := hx
  exact
    ((le_of_eq (dirac_caratheodory y).symm).trans (le_smul_caratheodory _ _)).trans (le_of_eq hy)

@[simp]

中文:
定理 toOuterMeasure_caratheodory
  结论: p.toOuterMeasure.caratheodory = ⊤
  证明: by
refine eq_top_iff.2 le_trans (le_sInf fun x hx => ?_) (le_sum_caratheodory _)
  have ⟨y, hy⟩ := hx
  exact
    ((le_of_eq (dirac_caratheodory y).symm).trans (le_smul_caratheodory _ _)).trans (le_of_eq hy)

@[simp]

Depends on / 依赖: dirac_caratheodory, eq_top_iff, le_of_eq, le_sInf, le_smul_caratheodory, le_sum_caratheodory, le_trans
-/
theorem toOuterMeasure_caratheodory : p.toOuterMeasure.caratheodory = ⊤ := by
refine eq_top_iff.2 le_trans (le_sInf fun x hx => ?_) (le_sum_caratheodory _)
  have ⟨y, hy⟩ := hx
  exact
    ((le_of_eq (dirac_caratheodory y).symm).trans (le_smul_caratheodory _ _)).trans (le_of_eq hy)

@[simp]
/--
theorem `toOuterMeasure_apply_finset` / 定理 `toOuterMeasure_apply_finset`

English:
theorem toOuterMeasure_apply_finset
  given: (s : Finset α)
  statement: p.toOuterMeasure s = ∑ x in s, p x
  proof: by
  refine (toOuterMeasure_apply p s).trans ((tsum_eq_sum (s := s) ?_).trans ?_)
  · exact fun x hx => Set.indicator_of_notMem (Finset.mem_coe.not.2 hx) _
  · exact Finset.sum_congr rfl fun x hx => Set.indicator_of_mem (Finset.mem_coe.2 hx) _

中文:
定理 toOuterMeasure_apply_finset
  条件: (s : 有限集 α)
  结论: p.toOuterMeasure s = ∑ x in s, p x
  证明: by
  refine (toOuterMeasure_apply p s).trans ((tsum_eq_sum (s := s) ?_).trans ?_)
  · exact fun x hx => Set.indicator_of_notMem (Finset.mem_coe.not.2 hx) _
  · exact Finset.sum_congr rfl fun x hx => Set.indicator_of_mem (Finset.mem_coe.2 hx) _

Depends on / 依赖: Finset, Finset.mem_coe, Finset.mem_coe.not, Finset.sum_congr, Set.indicator_of_mem, Set.indicator_of_notMem, indicator_of_mem, indicator_of_notMem, mem_coe, sum_congr, toOuterMeasure_apply, tsum_eq_sum
-/
theorem toOuterMeasure_apply_finset (s : Finset α) : p.toOuterMeasure s = ∑ x in s, p x := by
  refine (toOuterMeasure_apply p s).trans ((tsum_eq_sum (s := s) ?_).trans ?_)
  · exact fun x hx => Set.indicator_of_notMem (Finset.mem_coe.not.2 hx) _
  · exact Finset.sum_congr rfl fun x hx => Set.indicator_of_mem (Finset.mem_coe.2 hx) _

/--
theorem `toOuterMeasure_apply_singleton` / 定理 `toOuterMeasure_apply_singleton`

English:
theorem toOuterMeasure_apply_singleton
  given: (a : α)
  statement: p.toOuterMeasure {a} = p a
  proof: by
  refine (p.toOuterMeasure_apply {a}).trans ((tsum_eq_single a fun b hb => ?_).trans ?_)
· classical exact ite_eq_right_iff.2 fun hb' => False.elim hb hb'
· classical exact ite_eq_left_iff.2 fun ha' => False.elim ha' rfl

中文:
定理 toOuterMeasure_apply_singleton
  条件: (a : α)
  结论: p.toOuterMeasure {a} = p a
  证明: by
  refine (p.toOuterMeasure_apply {a}).trans ((tsum_eq_single a fun b hb => ?_).trans ?_)
· classical exact ite_eq_right_iff.2 fun hb' => False.elim hb hb'
· classical exact ite_eq_left_iff.2 fun ha' => False.elim ha' rfl

Depends on / 依赖: False.elim, classical, ite_eq_left_iff, ite_eq_right_iff, p.toOuterMeasure_apply, toOuterMeasure_apply, tsum_eq_single
-/
theorem toOuterMeasure_apply_singleton (a : α) : p.toOuterMeasure {a} = p a := by
  refine (p.toOuterMeasure_apply {a}).trans ((tsum_eq_single a fun b hb => ?_).trans ?_)
· classical exact ite_eq_right_iff.2 fun hb' => False.elim hb hb'
· classical exact ite_eq_left_iff.2 fun ha' => False.elim ha' rfl

/--
theorem `toOuterMeasure_injective` / 定理 `toOuterMeasure_injective`

English:
theorem toOuterMeasure_injective
  statement: (toOuterMeasure : PMF α -> OuterMeasure α).Injective
  proof: fun p q h => PMF.ext fun x => (p.toOuterMeasure_apply_singleton x).symm.trans
    ((congr_fun (congr_arg _ h) _).trans <| q.toOuterMeasure_apply_singleton x)

@[simp]

中文:
定理 toOuterMeasure_injective
  结论: (toOuterMeasure : PMF α -> 外测度 α).单射
  证明: fun p q h => PMF.ext fun x => (p.toOuterMeasure_apply_singleton x).symm.trans
    ((congr_fun (congr_arg _ h) _).trans <| q.toOuterMeasure_apply_singleton x)

@[simp]

Depends on / 依赖: PMF.ext, congr_arg, congr_fun, p.toOuterMeasure_apply_singleton, q.toOuterMeasure_apply_singleton, symm.trans, toOuterMeasure_apply_singleton
-/
theorem toOuterMeasure_injective : (toOuterMeasure : PMF α -> OuterMeasure α).Injective :=
  fun p q h => PMF.ext fun x => (p.toOuterMeasure_apply_singleton x).symm.trans
    ((congr_fun (congr_arg _ h) _).trans <| q.toOuterMeasure_apply_singleton x)

@[simp]
/--
theorem `toOuterMeasure_inj` / 定理 `toOuterMeasure_inj`

English:
theorem toOuterMeasure_inj
  given: {p q : PMF α}
  statement: p.toOuterMeasure = q.toOuterMeasure ↔ p = q
  proof: toOuterMeasure_injective.eq_iff

中文:
定理 toOuterMeasure_inj
  条件: {p q : PMF α}
  结论: p.toOuterMeasure = q.toOuterMeasure ↔ p = q
  证明: toOuterMeasure_injective.eq_iff

Depends on / 依赖: eq_iff, toOuterMeasure_injective, toOuterMeasure_injective.eq_iff
-/
theorem toOuterMeasure_inj {p q : PMF α} : p.toOuterMeasure = q.toOuterMeasure ↔ p = q :=
  toOuterMeasure_injective.eq_iff

/--
theorem `toOuterMeasure_apply_eq_zero_iff` / 定理 `toOuterMeasure_apply_eq_zero_iff`

English:
theorem toOuterMeasure_apply_eq_zero_iff
  statement: p.toOuterMeasure s = 0 ↔ Disjoint p.support s
  proof: by
  rw [toOuterMeasure_apply]; rw [ENNReal.tsum_eq_zero]
  exact funext_iff.symm.trans Set.indicator_eq_zero'

中文:
定理 toOuterMeasure_apply_eq_zero_iff
  结论: p.toOuterMeasure s = 0 ↔ Disjoint p.support s
  证明: by
  rw [toOuterMeasure_apply]; rw [ENNReal.tsum_eq_zero]
  exact funext_iff.symm.trans Set.indicator_eq_zero'

Depends on / 依赖: ENNReal, ENNReal.tsum_eq_zero, Set.indicator_eq_zero, funext_iff, funext_iff.symm.trans, indicator_eq_zero, toOuterMeasure_apply, tsum_eq_zero
-/
theorem toOuterMeasure_apply_eq_zero_iff : p.toOuterMeasure s = 0 ↔ Disjoint p.support s := by
  rw [toOuterMeasure_apply]; rw [ENNReal.tsum_eq_zero]
  exact funext_iff.symm.trans Set.indicator_eq_zero'

/--
theorem `toOuterMeasure_apply_eq_one_iff` / 定理 `toOuterMeasure_apply_eq_one_iff`

English:
theorem toOuterMeasure_apply_eq_one_iff
  statement: p.toOuterMeasure s = 1 ↔ p.support subseteq s
  proof: by
  refine (p.toOuterMeasure_apply s).symm ▸ ⟨fun h a hap => ?_, fun h => ?_⟩
  · refine by_contra fun hs => ne_of_lt ?_ (h.trans p.tsum_coe.symm)
have hs' : s.indicator p a = 0 := Set.indicator_apply_eq_zero.2 fun hs' => False.elim hs hs'
    have hsa : s.indicator p a < p a := hs'.symm ▸ (p.apply_pos_iff a).2 hap
    exact ENNReal.tsum_lt_tsum (p.tsum_coe_indicator_ne_top s)
      (fun x => Set.indicator_apply_le fun _ => le_rfl) hsa
  · classical suffices forall (x) (_ : x ∉ s), p x = 0 from
      _root_.trans (tsum_congr
        fun a => (Set.indicator_apply s p a).trans
          (ite_eq_left_iff.2 <| symm ∘ this a)) p.tsum_coe
exact fun a ha => (p.apply_eq_zero_iff a).2 Set.notMem_subset h ha

@[simp]

中文:
定理 toOuterMeasure_apply_eq_one_iff
  结论: p.toOuterMeasure s = 1 ↔ p.support subseteq s
  证明: by
  refine (p.toOuterMeasure_apply s).symm ▸ ⟨fun h a hap => ?_, fun h => ?_⟩
  · refine by_contra fun hs => ne_of_lt ?_ (h.trans p.tsum_coe.symm)
have hs' : s.indicator p a = 0 := Set.indicator_apply_eq_zero.2 fun hs' => False.elim hs hs'
    have hsa : s.indicator p a < p a := hs'.symm ▸ (p.apply_pos_iff a).2 hap
    exact ENNReal.tsum_lt_tsum (p.tsum_coe_indicator_ne_top s)
      (fun x => Set.indicator_apply_le fun _ => le_rfl) hsa
  · classical suffices forall (x) (_ : x ∉ s), p x = 0 from
      _root_.trans (tsum_congr
        fun a => (Set.indicator_apply s p a).trans
          (ite_eq_left_iff.2 <| symm ∘ this a)) p.tsum_coe
exact fun a ha => (p.apply_eq_zero_iff a).2 Set.notMem_subset h ha

@[simp]

Depends on / 依赖: ENNReal, ENNReal.tsum_lt_tsum, False.elim, Set.indicator_apply_eq_zero, Set.indicator_apply_le, _root_, _root_.trans, apply_pos_iff, classical, h.trans, indicator, indicator_apply_eq_zero, indicator_apply_le, le_rfl, ne_of_lt, p.apply_pos_iff, p.toOuterMeasure_apply, p.tsum_coe.symm, p.tsum_coe_indicator_ne_top, s.indicator
-/
theorem toOuterMeasure_apply_eq_one_iff : p.toOuterMeasure s = 1 ↔ p.support subseteq s := by
  refine (p.toOuterMeasure_apply s).symm ▸ ⟨fun h a hap => ?_, fun h => ?_⟩
  · refine by_contra fun hs => ne_of_lt ?_ (h.trans p.tsum_coe.symm)
have hs' : s.indicator p a = 0 := Set.indicator_apply_eq_zero.2 fun hs' => False.elim hs hs'
    have hsa : s.indicator p a < p a := hs'.symm ▸ (p.apply_pos_iff a).2 hap
    exact ENNReal.tsum_lt_tsum (p.tsum_coe_indicator_ne_top s)
      (fun x => Set.indicator_apply_le fun _ => le_rfl) hsa
  · classical suffices forall (x) (_ : x ∉ s), p x = 0 from
      _root_.trans (tsum_congr
        fun a => (Set.indicator_apply s p a).trans
          (ite_eq_left_iff.2 <| symm ∘ this a)) p.tsum_coe
exact fun a ha => (p.apply_eq_zero_iff a).2 Set.notMem_subset h ha

@[simp]
/--
theorem `toOuterMeasure_apply_inter_support` / 定理 `toOuterMeasure_apply_inter_support`

English:
theorem toOuterMeasure_apply_inter_support
  proof: by
  simp only [toOuterMeasure_apply, PMF.support, Set.indicator_inter_support]

中文:
定理 toOuterMeasure_apply_inter_support
  证明: by
  simp only [toOuterMeasure_apply, PMF.support, Set.indicator_inter_support]

Depends on / 依赖: PMF.support, Set.indicator_inter_support, indicator_inter_support, support, toOuterMeasure_apply
-/
theorem toOuterMeasure_apply_inter_support :
    p.toOuterMeasure (s inter p.support) = p.toOuterMeasure s := by
  simp only [toOuterMeasure_apply, PMF.support, Set.indicator_inter_support]

/--
theorem `toOuterMeasure_mono` / 定理 `toOuterMeasure_mono`

English:
theorem toOuterMeasure_mono
  given: {s t : Set α} (h : s inter p.support subseteq t)
  proof: le_trans (le_of_eq (toOuterMeasure_apply_inter_support p s).symm) (p.toOuterMeasure.mono h)

中文:
定理 toOuterMeasure_mono
  条件: {s t : 集合 α} (h : s inter p.support subseteq t)
  证明: le_trans (le_of_eq (toOuterMeasure_apply_inter_support p s).symm) (p.toOuterMeasure.mono h)

Depends on / 依赖: le_of_eq, le_trans, p.toOuterMeasure.mono, toOuterMeasure, toOuterMeasure_apply_inter_support
-/
theorem toOuterMeasure_mono {s t : Set α} (h : s inter p.support subseteq t) :
    p.toOuterMeasure s <= p.toOuterMeasure t :=
  le_trans (le_of_eq (toOuterMeasure_apply_inter_support p s).symm) (p.toOuterMeasure.mono h)

/--
theorem `toOuterMeasure_apply_eq_of_inter_support_eq` / 定理 `toOuterMeasure_apply_eq_of_inter_support_eq`

English:
theorem toOuterMeasure_apply_eq_of_inter_support_eq
  statement: {s t : Set α}
  proof: le_antisymm (p.toOuterMeasure_mono (h.symm ▸ Set.inter_subset_left))
    (p.toOuterMeasure_mono (h ▸ Set.inter_subset_left))

@[simp]

中文:
定理 toOuterMeasure_apply_eq_of_inter_support_eq
  结论: {s t : 集合 α}
  证明: le_antisymm (p.toOuterMeasure_mono (h.symm ▸ Set.inter_subset_left))
    (p.toOuterMeasure_mono (h ▸ Set.inter_subset_left))

@[simp]

Depends on / 依赖: Set.inter_subset_left, h.symm, inter_subset_left, le_antisymm, p.toOuterMeasure_mono, toOuterMeasure_mono
-/
theorem toOuterMeasure_apply_eq_of_inter_support_eq {s t : Set α}
    (h : s inter p.support = t inter p.support) : p.toOuterMeasure s = p.toOuterMeasure t :=
  le_antisymm (p.toOuterMeasure_mono (h.symm ▸ Set.inter_subset_left))
    (p.toOuterMeasure_mono (h ▸ Set.inter_subset_left))

@[simp]
/--
theorem `toOuterMeasure_apply_fintype` / 定理 `toOuterMeasure_apply_fintype`

English:
theorem toOuterMeasure_apply_fintype
  given: [Fintype α]
  statement: p.toOuterMeasure s = ∑ x, s.indicator p x
  proof: (p.toOuterMeasure_apply s).trans (tsum_eq_sum fun x h => absurd (Finset.mem_univ x) h)

中文:
定理 toOuterMeasure_apply_fintype
  条件: [有限类型 α]
  结论: p.toOuterMeasure s = ∑ x, s.indicator p x
  证明: (p.toOuterMeasure_apply s).trans (tsum_eq_sum fun x h => absurd (Finset.mem_univ x) h)

Depends on / 依赖: Finset, Finset.mem_univ, absurd, mem_univ, p.toOuterMeasure_apply, toOuterMeasure_apply, tsum_eq_sum
-/
theorem toOuterMeasure_apply_fintype [Fintype α] : p.toOuterMeasure s = ∑ x, s.indicator p x :=
  (p.toOuterMeasure_apply s).trans (tsum_eq_sum fun x h => absurd (Finset.mem_univ x) h)

end OuterMeasure

section Measure

/--
Definition of `toMeasure` / `toMeasure` 的定义

English:
definition toMeasure
  signature: [MeasurableSpace α] (p : PMF α)
  body: p.toOuterMeasure.toMeasure (p.toOuterMeasure_caratheodory.symm ▸ le_top)

中文:
定义 toMeasure
  签名: [可测空间 α] (p : PMF α)
  定义体: p.toOuterMeasure.toMeasure (p.toOuterMeasure_caratheodory.symm ▸ le_top)

Depends on / 依赖: le_top, p.toOuterMeasure.toMeasure, p.toOuterMeasure_caratheodory.symm, toMeasure, toOuterMeasure, toOuterMeasure_caratheodory
-/
def toMeasure [MeasurableSpace α] (p : PMF α) : Measure α :=
  p.toOuterMeasure.toMeasure (p.toOuterMeasure_caratheodory.symm ▸ le_top)

variable [MeasurableSpace α] (p : PMF α) {s : Set α}

/--
theorem `toOuterMeasure_apply_le_toMeasure_apply` / 定理 `toOuterMeasure_apply_le_toMeasure_apply`

English:
theorem toOuterMeasure_apply_le_toMeasure_apply
  given: (s : Set α)
  statement: p.toOuterMeasure s <= p.toMeasure s
  proof: le_toMeasure_apply p.toOuterMeasure _ s

中文:
定理 toOuterMeasure_apply_le_toMeasure_apply
  条件: (s : 集合 α)
  结论: p.toOuterMeasure s <= p.toMeasure s
  证明: le_toMeasure_apply p.toOuterMeasure _ s

Depends on / 依赖: le_toMeasure_apply, p.toOuterMeasure, toOuterMeasure
-/
theorem toOuterMeasure_apply_le_toMeasure_apply (s : Set α) : p.toOuterMeasure s <= p.toMeasure s :=
  le_toMeasure_apply p.toOuterMeasure _ s

/--
theorem `toMeasure_apply_eq_toOuterMeasure_apply` / 定理 `toMeasure_apply_eq_toOuterMeasure_apply`

English:
theorem toMeasure_apply_eq_toOuterMeasure_apply
  given: (hs : MeasurableSet s)
  proof: toMeasure_apply p.toOuterMeasure _ hs

中文:
定理 toMeasure_apply_eq_toOuterMeasure_apply
  条件: (hs : 可测集 s)
  证明: toMeasure_apply p.toOuterMeasure _ hs

Depends on / 依赖: p.toOuterMeasure, toMeasure_apply, toOuterMeasure
-/
theorem toMeasure_apply_eq_toOuterMeasure_apply (hs : MeasurableSet s) :
    p.toMeasure s = p.toOuterMeasure s :=
  toMeasure_apply p.toOuterMeasure _ hs

/--
theorem `toMeasure_apply` / 定理 `toMeasure_apply`

English:
theorem toMeasure_apply
  given: (hs : MeasurableSet s)
  statement: p.toMeasure s = ∑' x, s.indicator p x
  proof: (p.toMeasure_apply_eq_toOuterMeasure_apply hs).trans (p.toOuterMeasure_apply s)

中文:
定理 toMeasure_apply
  条件: (hs : 可测集 s)
  结论: p.toMeasure s = ∑' x, s.indicator p x
  证明: (p.toMeasure_apply_eq_toOuterMeasure_apply hs).trans (p.toOuterMeasure_apply s)

Depends on / 依赖: p.toMeasure_apply_eq_toOuterMeasure_apply, p.toOuterMeasure_apply, toMeasure_apply_eq_toOuterMeasure_apply, toOuterMeasure_apply
-/
theorem toMeasure_apply (hs : MeasurableSet s) : p.toMeasure s = ∑' x, s.indicator p x :=
  (p.toMeasure_apply_eq_toOuterMeasure_apply hs).trans (p.toOuterMeasure_apply s)

/--
theorem `toMeasure_apply_singleton` / 定理 `toMeasure_apply_singleton`

English:
theorem toMeasure_apply_singleton
  given: (a : α) (h : MeasurableSet ({a} : Set α))
  proof: by
  simp [p.toMeasure_apply_eq_toOuterMeasure_apply h, toOuterMeasure_apply_singleton]

中文:
定理 toMeasure_apply_singleton
  条件: (a : α) (h : 可测集 ({a} : 集合 α))
  证明: by
  simp [p.toMeasure_apply_eq_toOuterMeasure_apply h, toOuterMeasure_apply_singleton]

Depends on / 依赖: p.toMeasure_apply_eq_toOuterMeasure_apply, toMeasure_apply_eq_toOuterMeasure_apply, toOuterMeasure_apply_singleton
-/
theorem toMeasure_apply_singleton (a : α) (h : MeasurableSet ({a} : Set α)) :
    p.toMeasure {a} = p a := by
  simp [p.toMeasure_apply_eq_toOuterMeasure_apply h, toOuterMeasure_apply_singleton]

/--
theorem `toMeasure_apply_eq_zero_iff` / 定理 `toMeasure_apply_eq_zero_iff`

English:
theorem toMeasure_apply_eq_zero_iff
  given: (hs : MeasurableSet s)
  proof: by
  rw [p.toMeasure_apply_eq_toOuterMeasure_apply hs]; rw [toOuterMeasure_apply_eq_zero_iff]

中文:
定理 toMeasure_apply_eq_zero_iff
  条件: (hs : 可测集 s)
  证明: by
  rw [p.toMeasure_apply_eq_toOuterMeasure_apply hs]; rw [toOuterMeasure_apply_eq_zero_iff]

Depends on / 依赖: p.toMeasure_apply_eq_toOuterMeasure_apply, toMeasure_apply_eq_toOuterMeasure_apply, toOuterMeasure_apply_eq_zero_iff
-/
theorem toMeasure_apply_eq_zero_iff (hs : MeasurableSet s) :
    p.toMeasure s = 0 ↔ Disjoint p.support s := by
  rw [p.toMeasure_apply_eq_toOuterMeasure_apply hs]; rw [toOuterMeasure_apply_eq_zero_iff]

/--
theorem `toMeasure_apply_eq_one_iff` / 定理 `toMeasure_apply_eq_one_iff`

English:
theorem toMeasure_apply_eq_one_iff
  given: (hs : MeasurableSet s)
  statement: p.toMeasure s = 1 ↔ p.support subseteq s
  proof: (p.toMeasure_apply_eq_toOuterMeasure_apply hs).symm ▸ p.toOuterMeasure_apply_eq_one_iff s

中文:
定理 toMeasure_apply_eq_one_iff
  条件: (hs : 可测集 s)
  结论: p.toMeasure s = 1 ↔ p.support subseteq s
  证明: (p.toMeasure_apply_eq_toOuterMeasure_apply hs).symm ▸ p.toOuterMeasure_apply_eq_one_iff s

Depends on / 依赖: p.toMeasure_apply_eq_toOuterMeasure_apply, p.toOuterMeasure_apply_eq_one_iff, toMeasure_apply_eq_toOuterMeasure_apply, toOuterMeasure_apply_eq_one_iff
-/
theorem toMeasure_apply_eq_one_iff (hs : MeasurableSet s) : p.toMeasure s = 1 ↔ p.support subseteq s :=
  (p.toMeasure_apply_eq_toOuterMeasure_apply hs).symm ▸ p.toOuterMeasure_apply_eq_one_iff s

/--
theorem `toMeasure_mono` / 定理 `toMeasure_mono`

English:
theorem toMeasure_mono
  statement: {t : Set α} (hs : MeasurableSet s)
  proof: by
  rw [p.toMeasure_apply_eq_toOuterMeasure_apply hs]
  exact (p.toOuterMeasure_mono h).trans (p.toOuterMeasure_apply_le_toMeasure_apply t)

@[simp]

中文:
定理 toMeasure_mono
  结论: {t : 集合 α} (hs : 可测集 s)
  证明: by
  rw [p.toMeasure_apply_eq_toOuterMeasure_apply hs]
  exact (p.toOuterMeasure_mono h).trans (p.toOuterMeasure_apply_le_toMeasure_apply t)

@[simp]

Depends on / 依赖: p.toMeasure_apply_eq_toOuterMeasure_apply, p.toOuterMeasure_apply_le_toMeasure_apply, p.toOuterMeasure_mono, toMeasure_apply_eq_toOuterMeasure_apply, toOuterMeasure_apply_le_toMeasure_apply, toOuterMeasure_mono
-/
theorem toMeasure_mono {t : Set α} (hs : MeasurableSet s)
    (h : s inter p.support subseteq t) : p.toMeasure s <= p.toMeasure t := by
  rw [p.toMeasure_apply_eq_toOuterMeasure_apply hs]
  exact (p.toOuterMeasure_mono h).trans (p.toOuterMeasure_apply_le_toMeasure_apply t)

@[simp]
/--
theorem `toMeasure_apply_inter_support` / 定理 `toMeasure_apply_inter_support`

English:
theorem toMeasure_apply_inter_support
  given: (hs : MeasurableSet s)
  proof: (measure_mono s.inter_subset_left).antisymm (p.toMeasure_mono hs (refl _))

@[simp]

中文:
定理 toMeasure_apply_inter_support
  条件: (hs : 可测集 s)
  证明: (measure_mono s.inter_subset_left).antisymm (p.toMeasure_mono hs (refl _))

@[simp]

Depends on / 依赖: antisymm, inter_subset_left, measure_mono, p.toMeasure_mono, s.inter_subset_left, toMeasure_mono
-/
theorem toMeasure_apply_inter_support (hs : MeasurableSet s) :
    p.toMeasure (s inter p.support) = p.toMeasure s :=
  (measure_mono s.inter_subset_left).antisymm (p.toMeasure_mono hs (refl _))

@[simp]
/--
theorem `restrict_toMeasure_support` / 定理 `restrict_toMeasure_support`

English:
theorem restrict_toMeasure_support
  statement: p.toMeasure.restrict p.support = p.toMeasure
  proof: by
  ext s hs
  rw [Measure.restrict_apply hs]; rw [p.toMeasure_apply_inter_support hs]

中文:
定理 restrict_toMeasure_support
  结论: p.toMeasure.restrict p.support = p.toMeasure
  证明: by
  ext s hs
  rw [Measure.restrict_apply hs]; rw [p.toMeasure_apply_inter_support hs]

Depends on / 依赖: Measure, Measure.restrict_apply, p.toMeasure_apply_inter_support, restrict_apply, toMeasure_apply_inter_support
-/
theorem restrict_toMeasure_support : p.toMeasure.restrict p.support = p.toMeasure := by
  ext s hs
  rw [Measure.restrict_apply hs]; rw [p.toMeasure_apply_inter_support hs]

/--
theorem `toMeasure_apply_eq_of_inter_support_eq` / 定理 `toMeasure_apply_eq_of_inter_support_eq`

English:
theorem toMeasure_apply_eq_of_inter_support_eq
  statement: {t : Set α} (hs : MeasurableSet s)
  proof: by
  simpa only [p.toMeasure_apply_eq_toOuterMeasure_apply, hs, ht] using
    p.toOuterMeasure_apply_eq_of_inter_support_eq h

中文:
定理 toMeasure_apply_eq_of_inter_support_eq
  结论: {t : 集合 α} (hs : 可测集 s)
  证明: by
  simpa only [p.toMeasure_apply_eq_toOuterMeasure_apply, hs, ht] using
    p.toOuterMeasure_apply_eq_of_inter_support_eq h

Depends on / 依赖: p.toMeasure_apply_eq_toOuterMeasure_apply, p.toOuterMeasure_apply_eq_of_inter_support_eq, toMeasure_apply_eq_toOuterMeasure_apply, toOuterMeasure_apply_eq_of_inter_support_eq
-/
theorem toMeasure_apply_eq_of_inter_support_eq {t : Set α} (hs : MeasurableSet s)
    (ht : MeasurableSet t) (h : s inter p.support = t inter p.support) : p.toMeasure s = p.toMeasure t := by
  simpa only [p.toMeasure_apply_eq_toOuterMeasure_apply, hs, ht] using
    p.toOuterMeasure_apply_eq_of_inter_support_eq h

section MeasurableSingletonClass

variable [MeasurableSingletonClass α]

/--
theorem `toMeasure_injective` / 定理 `toMeasure_injective`

English:
theorem toMeasure_injective
  statement: (toMeasure : PMF α -> Measure α).Injective
  proof: by
  intro p q h
  ext x
  rw [← p.toMeasure_apply_singleton x <| measurableSet_singleton x]; rw [← q.toMeasure_apply_singleton x measurableSet_singleton x]; rw [h]

@[simp]

中文:
定理 toMeasure_injective
  结论: (toMeasure : PMF α -> 测度 α).单射
  证明: by
  intro p q h
  ext x
  rw [← p.toMeasure_apply_singleton x <| measurableSet_singleton x]; rw [← q.toMeasure_apply_singleton x measurableSet_singleton x]; rw [h]

@[simp]

Depends on / 依赖: measurableSet_singleton, p.toMeasure_apply_singleton, q.toMeasure_apply_singleton, toMeasure_apply_singleton
-/
theorem toMeasure_injective : (toMeasure : PMF α -> Measure α).Injective := by
  intro p q h
  ext x
  rw [← p.toMeasure_apply_singleton x <| measurableSet_singleton x]; rw [← q.toMeasure_apply_singleton x measurableSet_singleton x]; rw [h]

@[simp]
/--
theorem `toMeasure_inj` / 定理 `toMeasure_inj`

English:
theorem toMeasure_inj
  given: {p q : PMF α}
  statement: p.toMeasure = q.toMeasure ↔ p = q
  proof: toMeasure_injective.eq_iff

中文:
定理 toMeasure_inj
  条件: {p q : PMF α}
  结论: p.toMeasure = q.toMeasure ↔ p = q
  证明: toMeasure_injective.eq_iff

Depends on / 依赖: eq_iff, toMeasure_injective, toMeasure_injective.eq_iff
-/
theorem toMeasure_inj {p q : PMF α} : p.toMeasure = q.toMeasure ↔ p = q :=
  toMeasure_injective.eq_iff

/--
theorem `toMeasure_apply_eq_toOuterMeasure` / 定理 `toMeasure_apply_eq_toOuterMeasure`

English:
theorem toMeasure_apply_eq_toOuterMeasure
  given: (s : Set α)
  statement: p.toMeasure s = p.toOuterMeasure s
  proof: by
  have hs := (p.support_countable.mono s.inter_subset_right).measurableSet
  rw [← restrict_toMeasure_support]; rw [Measure.restrict_apply' p.support_countable.measurableSet]; rw [p.toMeasure_apply_eq_toOuterMeasure_apply hs]; rw [toOuterMeasure_apply_inter_support]

@[simp]

中文:
定理 toMeasure_apply_eq_toOuterMeasure
  条件: (s : 集合 α)
  结论: p.toMeasure s = p.toOuterMeasure s
  证明: by
  have hs := (p.support_countable.mono s.inter_subset_right).measurableSet
  rw [← restrict_toMeasure_support]; rw [Measure.restrict_apply' p.support_countable.measurableSet]; rw [p.toMeasure_apply_eq_toOuterMeasure_apply hs]; rw [toOuterMeasure_apply_inter_support]

@[simp]

Depends on / 依赖: Measure, Measure.restrict_apply, inter_subset_right, measurableSet, p.support_countable.measurableSet, p.support_countable.mono, p.toMeasure_apply_eq_toOuterMeasure_apply, restrict_apply, restrict_toMeasure_support, s.inter_subset_right, support_countable, toMeasure_apply_eq_toOuterMeasure_apply, toOuterMeasure_apply_inter_support
-/
theorem toMeasure_apply_eq_toOuterMeasure (s : Set α) : p.toMeasure s = p.toOuterMeasure s := by
  have hs := (p.support_countable.mono s.inter_subset_right).measurableSet
  rw [← restrict_toMeasure_support]; rw [Measure.restrict_apply' p.support_countable.measurableSet]; rw [p.toMeasure_apply_eq_toOuterMeasure_apply hs]; rw [toOuterMeasure_apply_inter_support]

@[simp]
/--
theorem `toMeasure_apply_finset` / 定理 `toMeasure_apply_finset`

English:
theorem toMeasure_apply_finset
  given: (s : Finset α)
  statement: p.toMeasure s = ∑ x in s, p x
  proof: (p.toMeasure_apply_eq_toOuterMeasure s).trans (p.toOuterMeasure_apply_finset s)

中文:
定理 toMeasure_apply_finset
  条件: (s : 有限集 α)
  结论: p.toMeasure s = ∑ x in s, p x
  证明: (p.toMeasure_apply_eq_toOuterMeasure s).trans (p.toOuterMeasure_apply_finset s)

Depends on / 依赖: p.toMeasure_apply_eq_toOuterMeasure, p.toOuterMeasure_apply_finset, toMeasure_apply_eq_toOuterMeasure, toOuterMeasure_apply_finset
-/
theorem toMeasure_apply_finset (s : Finset α) : p.toMeasure s = ∑ x in s, p x :=
  (p.toMeasure_apply_eq_toOuterMeasure s).trans (p.toOuterMeasure_apply_finset s)

/--
theorem `toMeasure_apply_eq_tsum` / 定理 `toMeasure_apply_eq_tsum`

English:
theorem toMeasure_apply_eq_tsum
  given: (s : Set α)
  statement: p.toMeasure s = ∑' x, s.indicator p x
  proof: (p.toMeasure_apply_eq_toOuterMeasure s).trans (p.toOuterMeasure_apply s)

@[simp]

中文:
定理 toMeasure_apply_eq_tsum
  条件: (s : 集合 α)
  结论: p.toMeasure s = ∑' x, s.indicator p x
  证明: (p.toMeasure_apply_eq_toOuterMeasure s).trans (p.toOuterMeasure_apply s)

@[simp]

Depends on / 依赖: p.toMeasure_apply_eq_toOuterMeasure, p.toOuterMeasure_apply, toMeasure_apply_eq_toOuterMeasure, toOuterMeasure_apply
-/
theorem toMeasure_apply_eq_tsum (s : Set α) : p.toMeasure s = ∑' x, s.indicator p x :=
  (p.toMeasure_apply_eq_toOuterMeasure s).trans (p.toOuterMeasure_apply s)

@[simp]
/--
theorem `toMeasure_apply_fintype` / 定理 `toMeasure_apply_fintype`

English:
theorem toMeasure_apply_fintype
  given: (s : Set α) [Fintype α]
  statement: p.toMeasure s = ∑ x, s.indicator p x
  proof: (p.toMeasure_apply_eq_toOuterMeasure s).trans (p.toOuterMeasure_apply_fintype s)

中文:
定理 toMeasure_apply_fintype
  条件: (s : 集合 α) [有限类型 α]
  结论: p.toMeasure s = ∑ x, s.indicator p x
  证明: (p.toMeasure_apply_eq_toOuterMeasure s).trans (p.toOuterMeasure_apply_fintype s)

Depends on / 依赖: p.toMeasure_apply_eq_toOuterMeasure, p.toOuterMeasure_apply_fintype, toMeasure_apply_eq_toOuterMeasure, toOuterMeasure_apply_fintype
-/
theorem toMeasure_apply_fintype (s : Set α) [Fintype α] : p.toMeasure s = ∑ x, s.indicator p x :=
  (p.toMeasure_apply_eq_toOuterMeasure s).trans (p.toOuterMeasure_apply_fintype s)

end MeasurableSingletonClass

end Measure

end PMF

namespace MeasureTheory

open PMF

namespace Measure

/--
Definition of `toPMF` / `toPMF` 的定义

English:
definition toPMF
  signature: [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α] (μ : Measure α)
  body: ⟨fun x => μ ({x} : Set α),
    ENNReal.summable.hasSum_iff.2
      (_root_.trans
        (symm <|
          (tsum_indicator_apply_singleton μ Set.univ MeasurableSet.univ).symm.trans
            (tsum_congr fun x => congr_fun (Set.indicator_univ _) x))
        h.measure_univ)⟩

中文:
定义 toPMF
  签名: [可数 α] [可测空间 α] [MeasurableSingleton类 α] (μ : 测度 α)
  定义体: ⟨fun x => μ ({x} : Set α),
    ENNReal.summable.hasSum_iff.2
      (_root_.trans
        (symm <|
          (tsum_indicator_apply_singleton μ Set.univ MeasurableSet.univ).symm.trans
            (tsum_congr fun x => congr_fun (Set.indicator_univ _) x))
        h.measure_univ)⟩

Depends on / 依赖: ENNReal, ENNReal.summable.hasSum_iff, MeasurableSet, MeasurableSet.univ, Set.indicator_univ, Set.univ, _root_, _root_.trans, congr_fun, h.measure_univ, hasSum_iff, indicator_univ, measure_univ, summable, symm.trans, tsum_congr, tsum_indicator_apply_singleton
-/
def toPMF [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α] (μ : Measure α)
    [h : IsProbabilityMeasure μ] : PMF α :=
  ⟨fun x => μ ({x} : Set α),
    ENNReal.summable.hasSum_iff.2
      (_root_.trans
        (symm <|
          (tsum_indicator_apply_singleton μ Set.univ MeasurableSet.univ).symm.trans
            (tsum_congr fun x => congr_fun (Set.indicator_univ _) x))
        h.measure_univ)⟩

variable [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α] (μ : Measure α)
  [IsProbabilityMeasure μ]

/--
theorem `toPMF_apply` / 定理 `toPMF_apply`

English:
theorem toPMF_apply
  given: (x : α)
  statement: μ.toPMF x = μ {x}
  proof: rfl

@[simp]

中文:
定理 toPMF_apply
  条件: (x : α)
  结论: μ.toPMF x = μ {x}
  证明: rfl

@[simp]
-/
theorem toPMF_apply (x : α) : μ.toPMF x = μ {x} := rfl

@[simp]
/--
theorem `toPMF_toMeasure` / 定理 `toPMF_toMeasure`

English:
theorem toPMF_toMeasure
  statement: μ.toPMF.toMeasure = μ
  proof: Measure.ext fun s hs => by
    rw [μ.toPMF.toMeasure_apply hs]; rw [← μ.tsum_indicator_apply_singleton s hs]
    rfl

中文:
定理 toPMF_toMeasure
  结论: μ.toPMF.toMeasure = μ
  证明: Measure.ext fun s hs => by
    rw [μ.toPMF.toMeasure_apply hs]; rw [← μ.tsum_indicator_apply_singleton s hs]
    rfl

Depends on / 依赖: Measure, Measure.ext, toMeasure_apply, toPMF.toMeasure_apply, tsum_indicator_apply_singleton
-/
theorem toPMF_toMeasure : μ.toPMF.toMeasure = μ :=
  Measure.ext fun s hs => by
    rw [μ.toPMF.toMeasure_apply hs]; rw [← μ.tsum_indicator_apply_singleton s hs]
    rfl

end Measure

end MeasureTheory

namespace PMF

/--
Instance `toMeasure.isProbabilityMeasure` / 实例 `toMeasure.isProbabilityMeasure`

English:
instance toMeasure.isProbabilityMeasure
  signature: [MeasurableSpace α] (p : PMF α)
  body: ⟨by
    simpa only [MeasurableSet.univ, toMeasure_apply_eq_toOuterMeasure_apply, Set.indicator_univ,
      toOuterMeasure_apply, ENNReal.coe_eq_one] using tsum_coe p⟩

中文:
实例 toMeasure.isProbabilityMeasure
  签名: [可测空间 α] (p : PMF α)
  定义体: ⟨by
    simpa only [MeasurableSet.univ, toMeasure_apply_eq_toOuterMeasure_apply, Set.indicator_univ,
      toOuterMeasure_apply, ENNReal.coe_eq_one] using tsum_coe p⟩

Depends on / 依赖: ENNReal, ENNReal.coe_eq_one, MeasurableSet, MeasurableSet.univ, Set.indicator_univ, coe_eq_one, indicator_univ, toMeasure_apply_eq_toOuterMeasure_apply, toOuterMeasure_apply, tsum_coe
-/
instance toMeasure.isProbabilityMeasure [MeasurableSpace α] (p : PMF α) :
    IsProbabilityMeasure p.toMeasure :=
  ⟨by
    simpa only [MeasurableSet.univ, toMeasure_apply_eq_toOuterMeasure_apply, Set.indicator_univ,
      toOuterMeasure_apply, ENNReal.coe_eq_one] using tsum_coe p⟩

variable [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α] (p : PMF α)

@[simp]
/--
theorem `toMeasure_toPMF` / 定理 `toMeasure_toPMF`

English:
theorem toMeasure_toPMF
  statement: p.toMeasure.toPMF = p
  proof: PMF.ext fun x => by
    rw [← p.toMeasure_apply_singleton x (measurableSet_singleton x)]; rw [p.toMeasure.toPMF_apply]

中文:
定理 toMeasure_toPMF
  结论: p.toMeasure.toPMF = p
  证明: PMF.ext fun x => by
    rw [← p.toMeasure_apply_singleton x (measurableSet_singleton x)]; rw [p.toMeasure.toPMF_apply]

Depends on / 依赖: PMF.ext, measurableSet_singleton, p.toMeasure.toPMF_apply, p.toMeasure_apply_singleton, toMeasure, toMeasure_apply_singleton, toPMF_apply
-/
theorem toMeasure_toPMF : p.toMeasure.toPMF = p :=
  PMF.ext fun x => by
    rw [← p.toMeasure_apply_singleton x (measurableSet_singleton x)]; rw [p.toMeasure.toPMF_apply]

/--
theorem `toMeasure_eq_iff_eq_toPMF` / 定理 `toMeasure_eq_iff_eq_toPMF`

English:
theorem toMeasure_eq_iff_eq_toPMF
  given: (μ : Measure α) [IsProbabilityMeasure μ]
  proof: by rw [← toMeasure_inj, Measure.toPMF_toMeasure]

中文:
定理 toMeasure_eq_iff_eq_toPMF
  条件: (μ : 测度 α) [是概率测度 μ]
  证明: by rw [← toMeasure_inj, Measure.toPMF_toMeasure]

Depends on / 依赖: Measure, Measure.toPMF_toMeasure, toMeasure_inj, toPMF_toMeasure
-/
theorem toMeasure_eq_iff_eq_toPMF (μ : Measure α) [IsProbabilityMeasure μ] :
    p.toMeasure = μ ↔ p = μ.toPMF := by rw [← toMeasure_inj, Measure.toPMF_toMeasure]

/--
theorem `toPMF_eq_iff_toMeasure_eq` / 定理 `toPMF_eq_iff_toMeasure_eq`

English:
theorem toPMF_eq_iff_toMeasure_eq
  given: (μ : Measure α) [IsProbabilityMeasure μ]
  proof: by rw [← toMeasure_inj, Measure.toPMF_toMeasure]

中文:
定理 toPMF_eq_iff_toMeasure_eq
  条件: (μ : 测度 α) [是概率测度 μ]
  证明: by rw [← toMeasure_inj, Measure.toPMF_toMeasure]

Depends on / 依赖: Measure, Measure.toPMF_toMeasure, toMeasure_inj, toPMF_toMeasure
-/
theorem toPMF_eq_iff_toMeasure_eq (μ : Measure α) [IsProbabilityMeasure μ] :
    μ.toPMF = p ↔ μ = p.toMeasure := by rw [← toMeasure_inj, Measure.toPMF_toMeasure]

end PMF
