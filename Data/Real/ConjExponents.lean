/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Data.ENNReal.Holder
public import Mathlib.Tactic.LinearCombination

/-!
# Real conjugate exponents

This file defines Hölder triple and Hölder conjugate exponents in `ℝ` and `ℝ≥0`. Real numbers `p`,
`q` and `r` form a *Hölder triple* if `0 < p` and `0 < q` and `p⁻¹ + q⁻¹ = r⁻¹` (which of course
implies `0 < r`). We say `p` and `q` are *Hölder conjugate* if `p`, `q` and `1` are a Hölder triple.
In this case, `1 < p` and `1 < q`. This property shows up often in analysis, especially when dealing
with `L^p` spaces.

These notions mimic the same notions for extended nonnegative reals where `p q r : ℝ≥0∞` are allowed
to take the values `0` and `∞`.

## Main declarations

* `Real.HolderTriple`: Predicate for two real numbers to be a Hölder triple.
* `Real.HolderConjugate`: Predicate for two real numbers to be Hölder conjugate.
* `Real.conjExponent`: Conjugate exponent of a real number.
* `NNReal.HolderTriple`: Predicate for two nonnegative real numbers to be a Hölder triple.
* `NNReal.HolderConjugate`: Predicate for two nonnegative real numbers to be Hölder conjugate.
* `NNReal.conjExponent`: Conjugate exponent of a nonnegative real number.
* `ENNReal.conjExponent`: Conjugate exponent of an extended nonnegative real number.

## TODO

* Eradicate the `1 / p` spelling in lemmas.
-/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal

namespace Real

/-- Real numbers `p q r : ℝ` are said to be a **Hölder triple** if `p` and `q` are positive
and `p⁻¹ + q⁻¹ = r⁻¹`. -/
@[mk_iff]
/--
Definition of `HolderTriple` / `HolderTriple` 的定义

English:
structure HolderTriple
  parameters: (p q r : Real)
  axioms and operations (3):
    - inv_add_inv_eq_inv : p⁻¹ + q⁻¹ = r⁻¹
    - left_pos : 0 < p
    - right_pos : 0 < q

中文:
结构 HolderTriple
  参数: (p q r : 实数)
  公理与运算 (3 个):
    - inv_add_inv_eq_inv : p⁻¹ + q⁻¹ = r⁻¹
    - left_pos : 0 < p
    - right_pos : 0 < q
-/
structure HolderTriple (p q r : Real) : Prop where
  inv_add_inv_eq_inv : p⁻¹ + q⁻¹ = r⁻¹
  left_pos : 0 < p
  right_pos : 0 < q

/--
Definition of `HolderConjugate` / `HolderConjugate` 的定义

English:
abbreviation HolderConjugate
  signature: (p q : Real)
  body: HolderTriple p q 1

中文:
缩写 HolderConjugate
  签名: (p q : 实数)
  定义体: HolderTriple p q 1

Depends on / 依赖: HolderTriple
-/
abbrev HolderConjugate (p q : Real) := HolderTriple p q 1

/--
Definition of `conjExponent` / `conjExponent` 的定义

English:
definition conjExponent
  signature: (p : Real)
  body: p / (p - 1)

中文:
定义 conjExponent
  签名: (p : 实数)
  定义体: p / (p - 1)
-/
def conjExponent (p : Real) : Real := p / (p - 1)

variable {a b p q r : Real}

namespace HolderTriple

/--
lemma `of_pos` / 引理 `of_pos`

English:
lemma of_pos
  given: (hp : 0 < p) (hq : 0 < q)
  statement: HolderTriple p q (p⁻¹ + q⁻¹)⁻¹ where
  proof: inv_inv _
  left_pos := hp
  right_pos := hq

中文:
引理 of_pos
  条件: (hp : 0 < p) (hq : 0 < q)
  结论: HolderTriple p q (p⁻¹ + q⁻¹)⁻¹ where
  证明: inv_inv _
  left_pos := hp
  right_pos := hq

Depends on / 依赖: inv_inv
-/
lemma of_pos (hp : 0 < p) (hq : 0 < q) : HolderTriple p q (p⁻¹ + q⁻¹)⁻¹ where
.symm inv_add_inv_eq_inv := inv_inv _
  left_pos := hp
  right_pos := hq

variable (h : p.HolderTriple q r)
include h

@[symm]
/--
lemma `symm` / 引理 `symm`

English:
lemma symm
  statement: q.HolderTriple p r where
  proof: add_comm p⁻¹ q⁻¹ ▸ h.inv_add_inv_eq_inv
  left_pos := h.right_pos
  right_pos := h.left_pos

中文:
引理 symm
  结论: q.HolderTriple p r where
  证明: add_comm p⁻¹ q⁻¹ ▸ h.inv_add_inv_eq_inv
  left_pos := h.right_pos
  right_pos := h.left_pos
-/
protected lemma symm : q.HolderTriple p r where
  inv_add_inv_eq_inv := add_comm p⁻¹ q⁻¹ ▸ h.inv_add_inv_eq_inv
  left_pos := h.right_pos
  right_pos := h.left_pos

/--
theorem `pos` / 定理 `pos`

English:
theorem pos
  statement: 0 < p
  proof: h.left_pos

中文:
定理 pos
  结论: 0 < p
  证明: h.left_pos

Depends on / 依赖: h.left_pos, left_pos
-/
theorem pos : 0 < p := h.left_pos
/--
theorem `nonneg` / 定理 `nonneg`

English:
theorem nonneg
  statement: 0 <= p
  proof: h.pos.le

中文:
定理 nonneg
  结论: 0 <= p
  证明: h.pos.le

Depends on / 依赖: h.pos.le
-/
theorem nonneg : 0 <= p := h.pos.le
/--
theorem `ne_zero` / 定理 `ne_zero`

English:
theorem ne_zero
  statement: p != 0
  proof: h.pos.ne'

中文:
定理 ne_zero
  结论: p != 0
  证明: h.pos.ne'

Depends on / 依赖: h.pos.ne
-/
theorem ne_zero : p != 0 := h.pos.ne'
/--
lemma `inv_pos` / 引理 `inv_pos`

English:
lemma inv_pos
  statement: 0 < p⁻¹
  proof: inv_pos.2 h.pos

中文:
引理 inv_pos
  结论: 0 < p⁻¹
  证明: inv_pos.2 h.pos
-/
protected lemma inv_pos : 0 < p⁻¹ := inv_pos.2 h.pos
/--
lemma `inv_nonneg` / 引理 `inv_nonneg`

English:
lemma inv_nonneg
  statement: 0 <= p⁻¹
  proof: h.inv_pos.le

中文:
引理 inv_nonneg
  结论: 0 <= p⁻¹
  证明: h.inv_pos.le
-/
protected lemma inv_nonneg : 0 <= p⁻¹ := h.inv_pos.le
/--
lemma `inv_ne_zero` / 引理 `inv_ne_zero`

English:
lemma inv_ne_zero
  statement: p⁻¹ != 0
  proof: h.inv_pos.ne'

中文:
引理 inv_ne_zero
  结论: p⁻¹ != 0
  证明: h.inv_pos.ne'
-/
protected lemma inv_ne_zero : p⁻¹ != 0 := h.inv_pos.ne'
/--
theorem `one_div_pos` / 定理 `one_div_pos`

English:
theorem one_div_pos
  statement: 0 < 1 / p
  proof: _root_.one_div_pos.2 h.pos

中文:
定理 one_div_pos
  结论: 0 < 1 / p
  证明: _root_.one_div_pos.2 h.pos

Depends on / 依赖: _root_, _root_.one_div_pos, h.pos, one_div_pos
-/
theorem one_div_pos : 0 < 1 / p := _root_.one_div_pos.2 h.pos
/--
theorem `one_div_nonneg` / 定理 `one_div_nonneg`

English:
theorem one_div_nonneg
  statement: 0 <= 1 / p
  proof: le_of_lt h.one_div_pos

中文:
定理 one_div_nonneg
  结论: 0 <= 1 / p
  证明: le_of_lt h.one_div_pos

Depends on / 依赖: h.one_div_pos, le_of_lt, one_div_pos
-/
theorem one_div_nonneg : 0 <= 1 / p := le_of_lt h.one_div_pos
/--
theorem `one_div_ne_zero` / 定理 `one_div_ne_zero`

English:
theorem one_div_ne_zero
  statement: 1 / p != 0
  proof: ne_of_gt h.one_div_pos

中文:
定理 one_div_ne_zero
  结论: 1 / p != 0
  证明: ne_of_gt h.one_div_pos

Depends on / 依赖: h.one_div_pos, ne_of_gt, one_div_pos
-/
theorem one_div_ne_zero : 1 / p != 0 := ne_of_gt h.one_div_pos

/--
theorem `pos'` / 定理 `pos'`

English:
theorem pos'
  statement: 0 < r
  proof: inv_pos.mp h.inv_add_inv_eq_inv ▸ add_pos h.inv_pos h.symm.inv_pos

中文:
定理 pos'
  结论: 0 < r
  证明: inv_pos.mp h.inv_add_inv_eq_inv ▸ add_pos h.inv_pos h.symm.inv_pos

Depends on / 依赖: add_pos, h.inv_add_inv_eq_inv, h.inv_pos, h.symm.inv_pos, inv_add_inv_eq_inv, inv_pos, inv_pos.mp
-/
theorem pos' : 0 < r := inv_pos.mp h.inv_add_inv_eq_inv ▸ add_pos h.inv_pos h.symm.inv_pos
/--
theorem `nonneg'` / 定理 `nonneg'`

English:
theorem nonneg'
  statement: 0 <= r
  proof: h.pos'.le

中文:
定理 nonneg'
  结论: 0 <= r
  证明: h.pos'.le

Depends on / 依赖: h.pos
-/
theorem nonneg' : 0 <= r := h.pos'.le
/--
theorem `ne_zero'` / 定理 `ne_zero'`

English:
theorem ne_zero'
  statement: r != 0
  proof: h.pos'.ne'

中文:
定理 ne_zero'
  结论: r != 0
  证明: h.pos'.ne'

Depends on / 依赖: h.pos
-/
theorem ne_zero' : r != 0 := h.pos'.ne'
/--
lemma `inv_pos'` / 引理 `inv_pos'`

English:
lemma inv_pos'
  statement: 0 < r⁻¹
  proof: inv_pos.2 h.pos'

中文:
引理 inv_pos'
  结论: 0 < r⁻¹
  证明: inv_pos.2 h.pos'
-/
protected lemma inv_pos' : 0 < r⁻¹ := inv_pos.2 h.pos'
/--
lemma `inv_nonneg'` / 引理 `inv_nonneg'`

English:
lemma inv_nonneg'
  statement: 0 <= r⁻¹
  proof: h.inv_pos'.le

中文:
引理 inv_nonneg'
  结论: 0 <= r⁻¹
  证明: h.inv_pos'.le
-/
protected lemma inv_nonneg' : 0 <= r⁻¹ := h.inv_pos'.le
/--
lemma `inv_ne_zero'` / 引理 `inv_ne_zero'`

English:
lemma inv_ne_zero'
  statement: r⁻¹ != 0
  proof: h.inv_pos'.ne'

中文:
引理 inv_ne_zero'
  结论: r⁻¹ != 0
  证明: h.inv_pos'.ne'
-/
protected lemma inv_ne_zero' : r⁻¹ != 0 := h.inv_pos'.ne'
/--
theorem `one_div_pos'` / 定理 `one_div_pos'`

English:
theorem one_div_pos'
  statement: 0 < 1 / r
  proof: _root_.one_div_pos.2 h.pos'

中文:
定理 one_div_pos'
  结论: 0 < 1 / r
  证明: _root_.one_div_pos.2 h.pos'

Depends on / 依赖: _root_, _root_.one_div_pos, h.pos, one_div_pos
-/
theorem one_div_pos' : 0 < 1 / r := _root_.one_div_pos.2 h.pos'
/--
theorem `one_div_nonneg'` / 定理 `one_div_nonneg'`

English:
theorem one_div_nonneg'
  statement: 0 <= 1 / r
  proof: le_of_lt h.one_div_pos'

中文:
定理 one_div_nonneg'
  结论: 0 <= 1 / r
  证明: le_of_lt h.one_div_pos'

Depends on / 依赖: h.one_div_pos, le_of_lt, one_div_pos
-/
theorem one_div_nonneg' : 0 <= 1 / r := le_of_lt h.one_div_pos'
/--
theorem `one_div_ne_zero'` / 定理 `one_div_ne_zero'`

English:
theorem one_div_ne_zero'
  statement: 1 / r != 0
  proof: ne_of_gt h.one_div_pos'

中文:
定理 one_div_ne_zero'
  结论: 1 / r != 0
  证明: ne_of_gt h.one_div_pos'

Depends on / 依赖: h.one_div_pos, ne_of_gt, one_div_pos
-/
theorem one_div_ne_zero' : 1 / r != 0 := ne_of_gt h.one_div_pos'

/-- useful for introducing all three facts simultaneously within a proof. -/
@[grind ->]
/--
theorem `all_pos` / 定理 `all_pos`

English:
theorem all_pos
  statement: 0 < p ∧ 0 < q ∧ 0 < r
  proof: ⟨h.pos, h.symm.pos, h.pos'⟩

中文:
定理 all_pos
  结论: 0 < p ∧ 0 < q ∧ 0 < r
  证明: ⟨h.pos, h.symm.pos, h.pos'⟩

Depends on / 依赖: h.pos, h.symm.pos
-/
theorem all_pos : 0 < p ∧ 0 < q ∧ 0 < r := ⟨h.pos, h.symm.pos, h.pos'⟩

/--
lemma `inv_eq` / 引理 `inv_eq`

English:
lemma inv_eq
  statement: r⁻¹ = p⁻¹ + q⁻¹
  proof: h.inv_add_inv_eq_inv.symm

中文:
引理 inv_eq
  结论: r⁻¹ = p⁻¹ + q⁻¹
  证明: h.inv_add_inv_eq_inv.symm

Depends on / 依赖: h.inv_add_inv_eq_inv.symm, inv_add_inv_eq_inv
-/
lemma inv_eq : r⁻¹ = p⁻¹ + q⁻¹ := h.inv_add_inv_eq_inv.symm
/--
lemma `one_div_add_one_div` / 引理 `one_div_add_one_div`

English:
lemma one_div_add_one_div
  statement: 1 / p + 1 / q = 1 / r
  proof: by simpa using h.inv_add_inv_eq_inv

中文:
引理 one_div_add_one_div
  结论: 1 / p + 1 / q = 1 / r
  证明: by simpa using h.inv_add_inv_eq_inv

Depends on / 依赖: h.inv_add_inv_eq_inv, inv_add_inv_eq_inv
-/
lemma one_div_add_one_div : 1 / p + 1 / q = 1 / r := by simpa using h.inv_add_inv_eq_inv
/--
lemma `one_div_eq` / 引理 `one_div_eq`

English:
lemma one_div_eq
  statement: 1 / r = 1 / p + 1 / q
  proof: h.one_div_add_one_div.symm

中文:
引理 one_div_eq
  结论: 1 / r = 1 / p + 1 / q
  证明: h.one_div_add_one_div.symm

Depends on / 依赖: h.one_div_add_one_div.symm, one_div_add_one_div
-/
lemma one_div_eq : 1 / r = 1 / p + 1 / q := h.one_div_add_one_div.symm
/--
lemma `inv_inv_add_inv` / 引理 `inv_inv_add_inv`

English:
lemma inv_inv_add_inv
  statement: (p⁻¹ + q⁻¹)⁻¹ = r
  proof: by simp [h.inv_add_inv_eq_inv]

中文:
引理 inv_inv_add_inv
  结论: (p⁻¹ + q⁻¹)⁻¹ = r
  证明: by simp [h.inv_add_inv_eq_inv]

Depends on / 依赖: h.inv_add_inv_eq_inv, inv_add_inv_eq_inv
-/
lemma inv_inv_add_inv : (p⁻¹ + q⁻¹)⁻¹ = r := by simp [h.inv_add_inv_eq_inv]

/--
lemma `inv_lt_inv` / 引理 `inv_lt_inv`

English:
lemma inv_lt_inv
  statement: p⁻¹ < r⁻¹
  proof: calc
.symm p⁻¹ = p⁻¹ + 0 := add_zero _
  _ < p⁻¹ + q⁻¹ := by gcongr; exact h.symm.inv_pos
  _ = r⁻¹ := h.inv_add_inv_eq_inv

中文:
引理 inv_lt_inv
  结论: p⁻¹ < r⁻¹
  证明: calc
.symm p⁻¹ = p⁻¹ + 0 := add_zero _
  _ < p⁻¹ + q⁻¹ := by gcongr; exact h.symm.inv_pos
  _ = r⁻¹ := h.inv_add_inv_eq_inv
-/
protected lemma inv_lt_inv : p⁻¹ < r⁻¹ := calc
.symm p⁻¹ = p⁻¹ + 0 := add_zero _
  _ < p⁻¹ + q⁻¹ := by gcongr; exact h.symm.inv_pos
  _ = r⁻¹ := h.inv_add_inv_eq_inv
/--
lemma `lt` / 引理 `lt`

English:
lemma lt
  statement: r < p
  proof: by simpa using inv_strictAnti₀ h.inv_pos h.inv_lt_inv

中文:
引理 lt
  结论: r < p
  证明: by simpa using inv_strictAnti₀ h.inv_pos h.inv_lt_inv

Depends on / 依赖: h.inv_lt_inv, h.inv_pos, inv_lt_inv, inv_pos
-/
lemma lt : r < p := by simpa using inv_strictAnti₀ h.inv_pos h.inv_lt_inv
/--
lemma `inv_sub_inv_eq_inv` / 引理 `inv_sub_inv_eq_inv`

English:
lemma inv_sub_inv_eq_inv
  statement: r⁻¹ - q⁻¹ = p⁻¹
  proof: sub_eq_of_eq_add h.inv_eq

中文:
引理 inv_sub_inv_eq_inv
  结论: r⁻¹ - q⁻¹ = p⁻¹
  证明: sub_eq_of_eq_add h.inv_eq

Depends on / 依赖: h.inv_eq, inv_eq, sub_eq_of_eq_add
-/
lemma inv_sub_inv_eq_inv : r⁻¹ - q⁻¹ = p⁻¹ := sub_eq_of_eq_add h.inv_eq

/--
lemma `holderConjugate_div_div` / 引理 `holderConjugate_div_div`

English:
lemma holderConjugate_div_div
  statement: (p / r).HolderConjugate (q / r) where
  proof: by
    simp [div_eq_mul_inv, ← mul_add, h.inv_add_inv_eq_inv, h.ne_zero']
  left_pos := by have := h.left_pos; have := h.pos'; positivity
  right_pos := by have := h.right_pos; have := h.pos'; positivity

中文:
引理 holderConjugate_div_div
  结论: (p / r).HolderConjugate (q / r) where
  证明: by
    simp [div_eq_mul_inv, ← mul_add, h.inv_add_inv_eq_inv, h.ne_zero']
  left_pos := by have := h.left_pos; have := h.pos'; positivity
  right_pos := by have := h.right_pos; have := h.pos'; positivity

Depends on / 依赖: div_eq_mul_inv, h.inv_add_inv_eq_inv, h.left_pos, h.ne_zero, h.pos, h.right_pos, inv_add_inv_eq_inv, left_pos, mul_add, ne_zero, right_pos
-/
lemma holderConjugate_div_div : (p / r).HolderConjugate (q / r) where
  inv_add_inv_eq_inv := by
    simp [div_eq_mul_inv, ← mul_add, h.inv_add_inv_eq_inv, h.ne_zero']
  left_pos := by have := h.left_pos; have := h.pos'; positivity
  right_pos := by have := h.right_pos; have := h.pos'; positivity

end HolderTriple

namespace HolderConjugate

/--
lemma `two_two` / 引理 `two_two`

English:
lemma two_two
  statement: HolderConjugate 2 2 where
  proof: by norm_num
  left_pos := zero_lt_two
  right_pos := zero_lt_two

中文:
引理 two_two
  结论: HolderConjugate 2 2 where
  证明: by norm_num
  left_pos := zero_lt_two
  right_pos := zero_lt_two

Depends on / 依赖: left_pos, right_pos, zero_lt_two
-/
lemma two_two : HolderConjugate 2 2 where
  inv_add_inv_eq_inv := by norm_num
  left_pos := zero_lt_two
  right_pos := zero_lt_two

section
variable (h : p.HolderConjugate q)
include h

@[symm]
/--
lemma `symm` / 引理 `symm`

English:
lemma symm
  statement: q.HolderConjugate p
  proof: HolderTriple.symm h

中文:
引理 symm
  结论: q.HolderConjugate p
  证明: HolderTriple.symm h
-/
protected lemma symm : q.HolderConjugate p := HolderTriple.symm h

/--
theorem `inv_add_inv_eq_one` / 定理 `inv_add_inv_eq_one`

English:
theorem inv_add_inv_eq_one
  statement: p⁻¹ + q⁻¹ = 1
  proof: inv_one (G := Real) ▸ h.inv_add_inv_eq_inv

中文:
定理 inv_add_inv_eq_one
  结论: p⁻¹ + q⁻¹ = 1
  证明: inv_one (G := Real) ▸ h.inv_add_inv_eq_inv

Depends on / 依赖: h.inv_add_inv_eq_inv, inv_add_inv_eq_inv, inv_one
-/
theorem inv_add_inv_eq_one : p⁻¹ + q⁻¹ = 1 := inv_one (G := Real) ▸ h.inv_add_inv_eq_inv

/--
theorem `sub_one_pos` / 定理 `sub_one_pos`

English:
theorem sub_one_pos
  statement: 0 < p - 1
  proof: sub_pos.2 h.lt

中文:
定理 sub_one_pos
  结论: 0 < p - 1
  证明: sub_pos.2 h.lt

Depends on / 依赖: h.lt, sub_pos
-/
theorem sub_one_pos : 0 < p - 1 := sub_pos.2 h.lt
/--
theorem `sub_one_ne_zero` / 定理 `sub_one_ne_zero`

English:
theorem sub_one_ne_zero
  statement: p - 1 != 0
  proof: h.sub_one_pos.ne'

中文:
定理 sub_one_ne_zero
  结论: p - 1 != 0
  证明: h.sub_one_pos.ne'

Depends on / 依赖: h.sub_one_pos.ne, sub_one_pos
-/
theorem sub_one_ne_zero : p - 1 != 0 := h.sub_one_pos.ne'

/--
theorem `conjugate_eq` / 定理 `conjugate_eq`

English:
theorem conjugate_eq
  statement: q = p / (p - 1)
  proof: by
  convert! inv_inv q ▸ congr($(h.symm.inv_sub_inv_eq_inv.symm)⁻¹) using 1
  field [h.ne_zero]

中文:
定理 conjugate_eq
  结论: q = p / (p - 1)
  证明: by
  convert! inv_inv q ▸ congr($(h.symm.inv_sub_inv_eq_inv.symm)⁻¹) using 1
  field [h.ne_zero]

Depends on / 依赖: convert, h.ne_zero, h.symm.inv_sub_inv_eq_inv.symm, inv_inv, inv_sub_inv_eq_inv, ne_zero
-/
theorem conjugate_eq : q = p / (p - 1) := by
  convert! inv_inv q ▸ congr($(h.symm.inv_sub_inv_eq_inv.symm)⁻¹) using 1
  field [h.ne_zero]

/--
lemma `conjExponent_eq` / 引理 `conjExponent_eq`

English:
lemma conjExponent_eq
  statement: conjExponent p = q
  proof: h.conjugate_eq.symm

中文:
引理 conjExponent_eq
  结论: conjExponent p = q
  证明: h.conjugate_eq.symm

Depends on / 依赖: conjugate_eq, h.conjugate_eq.symm
-/
lemma conjExponent_eq : conjExponent p = q := h.conjugate_eq.symm

/--
lemma `one_sub_inv` / 引理 `one_sub_inv`

English:
lemma one_sub_inv
  statement: 1 - p⁻¹ = q⁻¹
  proof: sub_eq_of_eq_add h.symm.inv_add_inv_eq_one.symm

中文:
引理 one_sub_inv
  结论: 1 - p⁻¹ = q⁻¹
  证明: sub_eq_of_eq_add h.symm.inv_add_inv_eq_one.symm

Depends on / 依赖: h.symm.inv_add_inv_eq_one.symm, inv_add_inv_eq_one, sub_eq_of_eq_add
-/
lemma one_sub_inv : 1 - p⁻¹ = q⁻¹ := sub_eq_of_eq_add h.symm.inv_add_inv_eq_one.symm
/--
lemma `inv_sub_one` / 引理 `inv_sub_one`

English:
lemma inv_sub_one
  statement: p⁻¹ - 1 = -q⁻¹
  proof: by simpa using congr(-$(h.one_sub_inv))

中文:
引理 inv_sub_one
  结论: p⁻¹ - 1 = -q⁻¹
  证明: by simpa using congr(-$(h.one_sub_inv))

Depends on / 依赖: h.one_sub_inv, one_sub_inv
-/
lemma inv_sub_one : p⁻¹ - 1 = -q⁻¹ := by simpa using congr(-$(h.one_sub_inv))

/--
theorem `sub_one_mul_conj` / 定理 `sub_one_mul_conj`

English:
theorem sub_one_mul_conj
  statement: (p - 1) * q = p
  proof: mul_comm q (p - 1) ▸ (eq_div_iff h.sub_one_ne_zero).1 h.conjugate_eq

中文:
定理 sub_one_mul_conj
  结论: (p - 1) * q = p
  证明: mul_comm q (p - 1) ▸ (eq_div_iff h.sub_one_ne_zero).1 h.conjugate_eq

Depends on / 依赖: conjugate_eq, eq_div_iff, h.conjugate_eq, h.sub_one_ne_zero, mul_comm, sub_one_ne_zero
-/
theorem sub_one_mul_conj : (p - 1) * q = p :=
  mul_comm q (p - 1) ▸ (eq_div_iff h.sub_one_ne_zero).1 h.conjugate_eq

/--
theorem `mul_eq_add` / 定理 `mul_eq_add`

English:
theorem mul_eq_add
  statement: p * q = p + q
  proof: by
  simpa only [sub_mul, sub_eq_iff_eq_add, one_mul] using h.sub_one_mul_conj

中文:
定理 mul_eq_add
  结论: p * q = p + q
  证明: by
  simpa only [sub_mul, sub_eq_iff_eq_add, one_mul] using h.sub_one_mul_conj

Depends on / 依赖: h.sub_one_mul_conj, one_mul, sub_eq_iff_eq_add, sub_mul, sub_one_mul_conj
-/
theorem mul_eq_add : p * q = p + q := by
  simpa only [sub_mul, sub_eq_iff_eq_add, one_mul] using h.sub_one_mul_conj

/--
theorem `div_conj_eq_sub_one` / 定理 `div_conj_eq_sub_one`

English:
theorem div_conj_eq_sub_one
  statement: p / q = p - 1
  proof: by
  field_simp [h.symm.ne_zero]
  linear_combination -h.sub_one_mul_conj

中文:
定理 div_conj_eq_sub_one
  结论: p / q = p - 1
  证明: by
  field_simp [h.symm.ne_zero]
  linear_combination -h.sub_one_mul_conj

Depends on / 依赖: h.sub_one_mul_conj, h.symm.ne_zero, linear_combination, ne_zero, sub_one_mul_conj
-/
theorem div_conj_eq_sub_one : p / q = p - 1 := by
  field_simp [h.symm.ne_zero]
  linear_combination -h.sub_one_mul_conj

/--
theorem `inv_add_inv_ennreal` / 定理 `inv_add_inv_ennreal`

English:
theorem inv_add_inv_ennreal
  statement: (ENNReal.ofReal p)⁻¹ + (ENNReal.ofReal q)⁻¹ = 1
  proof: by
  rw [← ENNReal.ofReal_one]; rw [← ENNReal.ofReal_inv_of_pos h.pos]; rw [← ENNReal.ofReal_inv_of_pos h.symm.pos]; rw [← ENNReal.ofReal_add h.inv_nonneg h.symm.inv_nonneg]; rw [h.inv_add_inv_eq_one]

中文:
定理 inv_add_inv_ennreal
  结论: (广义非负实数.of实数 p)⁻¹ + (广义非负实数.of实数 q)⁻¹ = 1
  证明: by
  rw [← ENNReal.ofReal_one]; rw [← ENNReal.ofReal_inv_of_pos h.pos]; rw [← ENNReal.ofReal_inv_of_pos h.symm.pos]; rw [← ENNReal.ofReal_add h.inv_nonneg h.symm.inv_nonneg]; rw [h.inv_add_inv_eq_one]

Depends on / 依赖: ENNReal, ENNReal.ofReal_add, ENNReal.ofReal_inv_of_pos, ENNReal.ofReal_one, h.inv_add_inv_eq_one, h.inv_nonneg, h.pos, h.symm.inv_nonneg, h.symm.pos, inv_add_inv_eq_one, inv_nonneg, ofReal_add, ofReal_inv_of_pos, ofReal_one
-/
theorem inv_add_inv_ennreal : (ENNReal.ofReal p)⁻¹ + (ENNReal.ofReal q)⁻¹ = 1 := by
  rw [← ENNReal.ofReal_one]; rw [← ENNReal.ofReal_inv_of_pos h.pos]; rw [← ENNReal.ofReal_inv_of_pos h.symm.pos]; rw [← ENNReal.ofReal_add h.inv_nonneg h.symm.inv_nonneg]; rw [h.inv_add_inv_eq_one]

end

/--
lemma `_root_.Real.holderConjugate_iff` / 引理 `_root_.Real.holderConjugate_iff`

English:
lemma _root_.Real.holderConjugate_iff
  statement: p.HolderConjugate q ↔ 1 < p ∧ p⁻¹ + q⁻¹ = 1
  proof: by
  refine ⟨fun h => ⟨h.lt, h.inv_add_inv_eq_one⟩, ?_⟩
  rintro ⟨hp, h⟩
  have hp' := zero_lt_one.trans hp
.symm ▸ h, hp', ?_⟩ refine ⟨inv_one (G := Real)
  rw [← inv_lt_one₀ hp']; rw [← sub_pos] at hp
exact inv_pos.mp eq_sub_of_add_eq' h ▸ hp

中文:
引理 _root_.实数.holderConjugate_iff
  结论: p.HolderConjugate q ↔ 1 < p ∧ p⁻¹ + q⁻¹ = 1
  证明: by
  refine ⟨fun h => ⟨h.lt, h.inv_add_inv_eq_one⟩, ?_⟩
  rintro ⟨hp, h⟩
  have hp' := zero_lt_one.trans hp
.symm ▸ h, hp', ?_⟩ refine ⟨inv_one (G := Real)
  rw [← inv_lt_one₀ hp']; rw [← sub_pos] at hp
exact inv_pos.mp eq_sub_of_add_eq' h ▸ hp

Depends on / 依赖: eq_sub_of_add_eq, h.inv_add_inv_eq_one, h.lt, inv_add_inv_eq_one, inv_one, inv_pos, inv_pos.mp, sub_pos, zero_lt_one, zero_lt_one.trans
-/
lemma _root_.Real.holderConjugate_iff : p.HolderConjugate q ↔ 1 < p ∧ p⁻¹ + q⁻¹ = 1 := by
  refine ⟨fun h => ⟨h.lt, h.inv_add_inv_eq_one⟩, ?_⟩
  rintro ⟨hp, h⟩
  have hp' := zero_lt_one.trans hp
.symm ▸ h, hp', ?_⟩ refine ⟨inv_one (G := Real)
  rw [← inv_lt_one₀ hp']; rw [← sub_pos] at hp
exact inv_pos.mp eq_sub_of_add_eq' h ▸ hp

/--
lemma `inv_inv` / 引理 `inv_inv`

English:
lemma inv_inv
  given: (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
  statement: a⁻¹.HolderConjugate b⁻¹ where
  proof: by simpa using hab
  left_pos := inv_pos.mpr ha
  right_pos := inv_pos.mpr hb

中文:
引理 inv_inv
  条件: (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
  结论: a⁻¹.HolderConjugate b⁻¹ where
  证明: by simpa using hab
  left_pos := inv_pos.mpr ha
  right_pos := inv_pos.mpr hb
-/
protected lemma inv_inv (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) : a⁻¹.HolderConjugate b⁻¹ where
  inv_add_inv_eq_inv := by simpa using hab
  left_pos := inv_pos.mpr ha
  right_pos := inv_pos.mpr hb

/--
lemma `inv_one_sub_inv` / 引理 `inv_one_sub_inv`

English:
lemma inv_one_sub_inv
  given: (ha₀ : 0 < a) (ha₁ : a < 1)
  statement: a⁻¹.HolderConjugate (1 - a)⁻¹
  proof: .mpr ha₁, by simp⟩ holderConjugate_iff.mpr ⟨one_lt_inv₀ ha₀

中文:
引理 inv_one_sub_inv
  条件: (ha₀ : 0 < a) (ha₁ : a < 1)
  结论: a⁻¹.HolderConjugate (1 - a)⁻¹
  证明: .mpr ha₁, by simp⟩ holderConjugate_iff.mpr ⟨one_lt_inv₀ ha₀

Depends on / 依赖: holderConjugate_iff, holderConjugate_iff.mpr
-/
lemma inv_one_sub_inv (ha₀ : 0 < a) (ha₁ : a < 1) : a⁻¹.HolderConjugate (1 - a)⁻¹ :=
.mpr ha₁, by simp⟩ holderConjugate_iff.mpr ⟨one_lt_inv₀ ha₀

/--
lemma `one_sub_inv_inv` / 引理 `one_sub_inv_inv`

English:
lemma one_sub_inv_inv
  given: (ha₀ : 0 < a) (ha₁ : a < 1)
  statement: (1 - a)⁻¹.HolderConjugate a⁻¹
  proof: (inv_one_sub_inv ha₀ ha₁).symm

中文:
引理 one_sub_inv_inv
  条件: (ha₀ : 0 < a) (ha₁ : a < 1)
  结论: (1 - a)⁻¹.HolderConjugate a⁻¹
  证明: (inv_one_sub_inv ha₀ ha₁).symm

Depends on / 依赖: inv_one_sub_inv
-/
lemma one_sub_inv_inv (ha₀ : 0 < a) (ha₁ : a < 1) : (1 - a)⁻¹.HolderConjugate a⁻¹ :=
  (inv_one_sub_inv ha₀ ha₁).symm

end HolderConjugate

/--
lemma `holderConjugate_comm` / 引理 `holderConjugate_comm`

English:
lemma holderConjugate_comm
  statement: p.HolderConjugate q ↔ q.HolderConjugate p
  proof: ⟨.symm, .symm⟩

中文:
引理 holderConjugate_comm
  结论: p.HolderConjugate q ↔ q.HolderConjugate p
  证明: ⟨.symm, .symm⟩
-/
lemma holderConjugate_comm : p.HolderConjugate q ↔ q.HolderConjugate p := ⟨.symm, .symm⟩

/--
lemma `holderConjugate_iff_eq_conjExponent` / 引理 `holderConjugate_iff_eq_conjExponent`

English:
lemma holderConjugate_iff_eq_conjExponent
  given: (hp : 1 < p)
  statement: p.HolderConjugate q ↔ q = p / (p - 1)
  proof: ⟨HolderConjugate.conjugate_eq, fun h => holderConjugate_iff.mpr ⟨hp, by simp [field, h]⟩⟩

中文:
引理 holderConjugate_iff_eq_conjExponent
  条件: (hp : 1 < p)
  结论: p.HolderConjugate q ↔ q = p / (p - 1)
  证明: ⟨HolderConjugate.conjugate_eq, fun h => holderConjugate_iff.mpr ⟨hp, by simp [field, h]⟩⟩

Depends on / 依赖: HolderConjugate, HolderConjugate.conjugate_eq, conjugate_eq, holderConjugate_iff, holderConjugate_iff.mpr
-/
lemma holderConjugate_iff_eq_conjExponent (hp : 1 < p) : p.HolderConjugate q ↔ q = p / (p - 1) :=
  ⟨HolderConjugate.conjugate_eq, fun h => holderConjugate_iff.mpr ⟨hp, by simp [field, h]⟩⟩

/--
lemma `HolderConjugate.conjExponent` / 引理 `HolderConjugate.conjExponent`

English:
lemma HolderConjugate.conjExponent
  given: (h : 1 < p)
  statement: p.HolderConjugate (conjExponent p)
  proof: (holderConjugate_iff_eq_conjExponent h).2 rfl

中文:
引理 HolderConjugate.conjExponent
  条件: (h : 1 < p)
  结论: p.HolderConjugate (conjExponent p)
  证明: (holderConjugate_iff_eq_conjExponent h).2 rfl

Depends on / 依赖: holderConjugate_iff_eq_conjExponent
-/
lemma HolderConjugate.conjExponent (h : 1 < p) : p.HolderConjugate (conjExponent p) :=
  (holderConjugate_iff_eq_conjExponent h).2 rfl

/--
lemma `holderConjugate_one_div` / 引理 `holderConjugate_one_div`

English:
lemma holderConjugate_one_div
  given: (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
  proof: by simpa using HolderConjugate.inv_inv ha hb hab

中文:
引理 holderConjugate_one_div
  条件: (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
  证明: by simpa using HolderConjugate.inv_inv ha hb hab

Depends on / 依赖: HolderConjugate, HolderConjugate.inv_inv, inv_inv
-/
lemma holderConjugate_one_div (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    (1 / a).HolderConjugate (1 / b) := by simpa using HolderConjugate.inv_inv ha hb hab

end Real

namespace NNReal

/-- Nonnegative real numbers `p q r : ℝ≥0` are said to be a **Hölder triple** if `p` and `q` are
positive and `p⁻¹ + q⁻¹ = r⁻¹`. -/
@[mk_iff]
/--
Definition of `HolderTriple` / `HolderTriple` 的定义

English:
structure HolderTriple
  parameters: (p q r : Real>=0)
  axioms and operations (3):
    - inv_add_inv_eq_inv : p⁻¹ + q⁻¹ = r⁻¹
    - left_pos : 0 < p
    - right_pos : 0 < q

中文:
结构 HolderTriple
  参数: (p q r : 实数>=0)
  公理与运算 (3 个):
    - inv_add_inv_eq_inv : p⁻¹ + q⁻¹ = r⁻¹
    - left_pos : 0 < p
    - right_pos : 0 < q
-/
structure HolderTriple (p q r : Real>=0) : Prop where
  inv_add_inv_eq_inv : p⁻¹ + q⁻¹ = r⁻¹
  left_pos : 0 < p
  right_pos : 0 < q

/--
Definition of `HolderConjugate` / `HolderConjugate` 的定义

English:
abbreviation HolderConjugate
  signature: (p q : Real>=0)
  body: HolderTriple p q 1

中文:
缩写 HolderConjugate
  签名: (p q : 实数>=0)
  定义体: HolderTriple p q 1

Depends on / 依赖: HolderTriple
-/
abbrev HolderConjugate (p q : Real>=0) := HolderTriple p q 1

/--
Definition of `conjExponent` / `conjExponent` 的定义

English:
definition conjExponent
  signature: (p : Real>=0)
  body: p / (p - 1)

@[simp, norm_cast]

中文:
定义 conjExponent
  签名: (p : 实数>=0)
  定义体: p / (p - 1)

@[simp, norm_cast]
-/
def conjExponent (p : Real>=0) : Real>=0 := p / (p - 1)

@[simp, norm_cast]
/--
lemma `holderTriple_coe_iff` / 引理 `holderTriple_coe_iff`

English:
lemma holderTriple_coe_iff
  given: {p q r : Real>=0}
  proof: by
  rw_mod_cast [Real.holderTriple_iff, holderTriple_iff]

alias ⟨_, HolderTriple.coe⟩ := holderTriple_coe_iff

@[simp, norm_cast]

中文:
引理 holderTriple_coe_iff
  条件: {p q r : 实数>=0}
  证明: by
  rw_mod_cast [Real.holderTriple_iff, holderTriple_iff]

alias ⟨_, HolderTriple.coe⟩ := holderTriple_coe_iff

@[simp, norm_cast]

Depends on / 依赖: Real.holderTriple_iff, holderTriple_iff, rw_mod_cast
-/
lemma holderTriple_coe_iff {p q r : Real>=0} :
    Real.HolderTriple (p : Real) (q : Real) (r : Real) ↔ HolderTriple p q r := by
  rw_mod_cast [Real.holderTriple_iff, holderTriple_iff]

alias ⟨_, HolderTriple.coe⟩ := holderTriple_coe_iff

@[simp, norm_cast]
/--
lemma `holderConjugate_coe_iff` / 引理 `holderConjugate_coe_iff`

English:
lemma holderConjugate_coe_iff
  given: {p q : Real>=0}
  proof: holderTriple_coe_iff (r := 1)

alias ⟨_, HolderConjugate.coe⟩ := holderConjugate_coe_iff

中文:
引理 holderConjugate_coe_iff
  条件: {p q : 实数>=0}
  证明: holderTriple_coe_iff (r := 1)

alias ⟨_, HolderConjugate.coe⟩ := holderConjugate_coe_iff

Depends on / 依赖: holderTriple_coe_iff
-/
lemma holderConjugate_coe_iff {p q : Real>=0} :
    Real.HolderConjugate (p : Real) (q : Real) ↔ HolderConjugate p q :=
  holderTriple_coe_iff (r := 1)

alias ⟨_, HolderConjugate.coe⟩ := holderConjugate_coe_iff

variable {a b p q r : Real>=0}

namespace HolderTriple

/--
lemma `of_pos` / 引理 `of_pos`

English:
lemma of_pos
  given: (hp : 0 < p) (hq : 0 < q)
  statement: HolderTriple p q (p⁻¹ + q⁻¹)⁻¹ where
  proof: inv_inv _
  left_pos := hp
  right_pos := hq

中文:
引理 of_pos
  条件: (hp : 0 < p) (hq : 0 < q)
  结论: HolderTriple p q (p⁻¹ + q⁻¹)⁻¹ where
  证明: inv_inv _
  left_pos := hp
  right_pos := hq

Depends on / 依赖: inv_inv
-/
lemma of_pos (hp : 0 < p) (hq : 0 < q) : HolderTriple p q (p⁻¹ + q⁻¹)⁻¹ where
.symm inv_add_inv_eq_inv := inv_inv _
  left_pos := hp
  right_pos := hq

variable (h : p.HolderTriple q r)
include h

@[symm]
/--
lemma `symm` / 引理 `symm`

English:
lemma symm
  statement: q.HolderTriple p r where
  proof: add_comm p⁻¹ q⁻¹ ▸ h.inv_add_inv_eq_inv
  left_pos := h.right_pos
  right_pos := h.left_pos

中文:
引理 symm
  结论: q.HolderTriple p r where
  证明: add_comm p⁻¹ q⁻¹ ▸ h.inv_add_inv_eq_inv
  left_pos := h.right_pos
  right_pos := h.left_pos
-/
protected lemma symm : q.HolderTriple p r where
  inv_add_inv_eq_inv := add_comm p⁻¹ q⁻¹ ▸ h.inv_add_inv_eq_inv
  left_pos := h.right_pos
  right_pos := h.left_pos

/--
theorem `pos` / 定理 `pos`

English:
theorem pos
  statement: 0 < p
  proof: h.left_pos

中文:
定理 pos
  结论: 0 < p
  证明: h.left_pos

Depends on / 依赖: h.left_pos, left_pos
-/
theorem pos : 0 < p := h.left_pos
/--
theorem `nonneg` / 定理 `nonneg`

English:
theorem nonneg
  statement: 0 <= p
  proof: h.pos.le

中文:
定理 nonneg
  结论: 0 <= p
  证明: h.pos.le

Depends on / 依赖: h.pos.le
-/
theorem nonneg : 0 <= p := h.pos.le
/--
theorem `ne_zero` / 定理 `ne_zero`

English:
theorem ne_zero
  statement: p != 0
  proof: h.pos.ne'

中文:
定理 ne_zero
  结论: p != 0
  证明: h.pos.ne'

Depends on / 依赖: h.pos.ne
-/
theorem ne_zero : p != 0 := h.pos.ne'
/--
lemma `inv_pos` / 引理 `inv_pos`

English:
lemma inv_pos
  statement: 0 < p⁻¹
  proof: inv_pos.2 h.pos

中文:
引理 inv_pos
  结论: 0 < p⁻¹
  证明: inv_pos.2 h.pos
-/
protected lemma inv_pos : 0 < p⁻¹ := inv_pos.2 h.pos
/--
lemma `inv_nonneg` / 引理 `inv_nonneg`

English:
lemma inv_nonneg
  statement: 0 <= p⁻¹
  proof: h.inv_pos.le

中文:
引理 inv_nonneg
  结论: 0 <= p⁻¹
  证明: h.inv_pos.le
-/
protected lemma inv_nonneg : 0 <= p⁻¹ := h.inv_pos.le
/--
lemma `inv_ne_zero` / 引理 `inv_ne_zero`

English:
lemma inv_ne_zero
  statement: p⁻¹ != 0
  proof: h.inv_pos.ne'

中文:
引理 inv_ne_zero
  结论: p⁻¹ != 0
  证明: h.inv_pos.ne'
-/
protected lemma inv_ne_zero : p⁻¹ != 0 := h.inv_pos.ne'
/--
theorem `one_div_pos` / 定理 `one_div_pos`

English:
theorem one_div_pos
  statement: 0 < 1 / p
  proof: _root_.one_div_pos.2 h.pos

中文:
定理 one_div_pos
  结论: 0 < 1 / p
  证明: _root_.one_div_pos.2 h.pos

Depends on / 依赖: _root_, _root_.one_div_pos, h.pos, one_div_pos
-/
theorem one_div_pos : 0 < 1 / p := _root_.one_div_pos.2 h.pos
/--
theorem `one_div_nonneg` / 定理 `one_div_nonneg`

English:
theorem one_div_nonneg
  statement: 0 <= 1 / p
  proof: le_of_lt h.one_div_pos

中文:
定理 one_div_nonneg
  结论: 0 <= 1 / p
  证明: le_of_lt h.one_div_pos

Depends on / 依赖: h.one_div_pos, le_of_lt, one_div_pos
-/
theorem one_div_nonneg : 0 <= 1 / p := le_of_lt h.one_div_pos
/--
theorem `one_div_ne_zero` / 定理 `one_div_ne_zero`

English:
theorem one_div_ne_zero
  statement: 1 / p != 0
  proof: ne_of_gt h.one_div_pos

中文:
定理 one_div_ne_zero
  结论: 1 / p != 0
  证明: ne_of_gt h.one_div_pos

Depends on / 依赖: h.one_div_pos, ne_of_gt, one_div_pos
-/
theorem one_div_ne_zero : 1 / p != 0 := ne_of_gt h.one_div_pos

/--
theorem `pos'` / 定理 `pos'`

English:
theorem pos'
  statement: 0 < r
  proof: inv_pos.mp h.inv_add_inv_eq_inv ▸ add_pos h.inv_pos h.symm.inv_pos

中文:
定理 pos'
  结论: 0 < r
  证明: inv_pos.mp h.inv_add_inv_eq_inv ▸ add_pos h.inv_pos h.symm.inv_pos

Depends on / 依赖: add_pos, h.inv_add_inv_eq_inv, h.inv_pos, h.symm.inv_pos, inv_add_inv_eq_inv, inv_pos, inv_pos.mp
-/
theorem pos' : 0 < r := inv_pos.mp h.inv_add_inv_eq_inv ▸ add_pos h.inv_pos h.symm.inv_pos
/--
theorem `nonneg'` / 定理 `nonneg'`

English:
theorem nonneg'
  statement: 0 <= r
  proof: h.pos'.le

中文:
定理 nonneg'
  结论: 0 <= r
  证明: h.pos'.le

Depends on / 依赖: h.pos
-/
theorem nonneg' : 0 <= r := h.pos'.le
/--
theorem `ne_zero'` / 定理 `ne_zero'`

English:
theorem ne_zero'
  statement: r != 0
  proof: h.pos'.ne'

中文:
定理 ne_zero'
  结论: r != 0
  证明: h.pos'.ne'

Depends on / 依赖: h.pos
-/
theorem ne_zero' : r != 0 := h.pos'.ne'
/--
lemma `inv_pos'` / 引理 `inv_pos'`

English:
lemma inv_pos'
  statement: 0 < r⁻¹
  proof: inv_pos.2 h.pos'

中文:
引理 inv_pos'
  结论: 0 < r⁻¹
  证明: inv_pos.2 h.pos'
-/
protected lemma inv_pos' : 0 < r⁻¹ := inv_pos.2 h.pos'
/--
lemma `inv_nonneg'` / 引理 `inv_nonneg'`

English:
lemma inv_nonneg'
  statement: 0 <= r⁻¹
  proof: h.inv_pos'.le

中文:
引理 inv_nonneg'
  结论: 0 <= r⁻¹
  证明: h.inv_pos'.le
-/
protected lemma inv_nonneg' : 0 <= r⁻¹ := h.inv_pos'.le
/--
lemma `inv_ne_zero'` / 引理 `inv_ne_zero'`

English:
lemma inv_ne_zero'
  statement: r⁻¹ != 0
  proof: h.inv_pos'.ne'

中文:
引理 inv_ne_zero'
  结论: r⁻¹ != 0
  证明: h.inv_pos'.ne'
-/
protected lemma inv_ne_zero' : r⁻¹ != 0 := h.inv_pos'.ne'
/--
theorem `one_div_pos'` / 定理 `one_div_pos'`

English:
theorem one_div_pos'
  statement: 0 < 1 / r
  proof: _root_.one_div_pos.2 h.pos'

中文:
定理 one_div_pos'
  结论: 0 < 1 / r
  证明: _root_.one_div_pos.2 h.pos'

Depends on / 依赖: _root_, _root_.one_div_pos, h.pos, one_div_pos
-/
theorem one_div_pos' : 0 < 1 / r := _root_.one_div_pos.2 h.pos'
/--
theorem `one_div_nonneg'` / 定理 `one_div_nonneg'`

English:
theorem one_div_nonneg'
  statement: 0 <= 1 / r
  proof: le_of_lt h.one_div_pos'

中文:
定理 one_div_nonneg'
  结论: 0 <= 1 / r
  证明: le_of_lt h.one_div_pos'

Depends on / 依赖: h.one_div_pos, le_of_lt, one_div_pos
-/
theorem one_div_nonneg' : 0 <= 1 / r := le_of_lt h.one_div_pos'
/--
theorem `one_div_ne_zero'` / 定理 `one_div_ne_zero'`

English:
theorem one_div_ne_zero'
  statement: 1 / r != 0
  proof: ne_of_gt h.one_div_pos'

中文:
定理 one_div_ne_zero'
  结论: 1 / r != 0
  证明: ne_of_gt h.one_div_pos'

Depends on / 依赖: h.one_div_pos, ne_of_gt, one_div_pos
-/
theorem one_div_ne_zero' : 1 / r != 0 := ne_of_gt h.one_div_pos'

/-- useful for introducing all three facts simultaneously within a proof. -/
@[grind ->]
/--
theorem `all_pos` / 定理 `all_pos`

English:
theorem all_pos
  statement: 0 < p ∧ 0 < q ∧ 0 < r
  proof: ⟨h.pos, h.symm.pos, h.pos'⟩

中文:
定理 all_pos
  结论: 0 < p ∧ 0 < q ∧ 0 < r
  证明: ⟨h.pos, h.symm.pos, h.pos'⟩

Depends on / 依赖: h.pos, h.symm.pos
-/
theorem all_pos : 0 < p ∧ 0 < q ∧ 0 < r := ⟨h.pos, h.symm.pos, h.pos'⟩

/--
lemma `inv_eq` / 引理 `inv_eq`

English:
lemma inv_eq
  statement: r⁻¹ = p⁻¹ + q⁻¹
  proof: h.inv_add_inv_eq_inv.symm

中文:
引理 inv_eq
  结论: r⁻¹ = p⁻¹ + q⁻¹
  证明: h.inv_add_inv_eq_inv.symm

Depends on / 依赖: h.inv_add_inv_eq_inv.symm, inv_add_inv_eq_inv
-/
lemma inv_eq : r⁻¹ = p⁻¹ + q⁻¹ := h.inv_add_inv_eq_inv.symm
/--
lemma `one_div_add_one_div` / 引理 `one_div_add_one_div`

English:
lemma one_div_add_one_div
  statement: 1 / p + 1 / q = 1 / r
  proof: by exact_mod_cast h.coe.one_div_add_one_div

中文:
引理 one_div_add_one_div
  结论: 1 / p + 1 / q = 1 / r
  证明: by exact_mod_cast h.coe.one_div_add_one_div

Depends on / 依赖: h.coe.one_div_add_one_div, one_div_add_one_div
-/
lemma one_div_add_one_div : 1 / p + 1 / q = 1 / r := by exact_mod_cast h.coe.one_div_add_one_div
/--
lemma `one_div_eq` / 引理 `one_div_eq`

English:
lemma one_div_eq
  statement: 1 / r = 1 / p + 1 / q
  proof: h.one_div_add_one_div.symm

中文:
引理 one_div_eq
  结论: 1 / r = 1 / p + 1 / q
  证明: h.one_div_add_one_div.symm

Depends on / 依赖: h.one_div_add_one_div.symm, one_div_add_one_div
-/
lemma one_div_eq : 1 / r = 1 / p + 1 / q := h.one_div_add_one_div.symm
/--
lemma `inv_inv_add_inv` / 引理 `inv_inv_add_inv`

English:
lemma inv_inv_add_inv
  statement: (p⁻¹ + q⁻¹)⁻¹ = r
  proof: by exact_mod_cast h.coe.inv_inv_add_inv

中文:
引理 inv_inv_add_inv
  结论: (p⁻¹ + q⁻¹)⁻¹ = r
  证明: by exact_mod_cast h.coe.inv_inv_add_inv

Depends on / 依赖: h.coe.inv_inv_add_inv, inv_inv_add_inv
-/
lemma inv_inv_add_inv : (p⁻¹ + q⁻¹)⁻¹ = r := by exact_mod_cast h.coe.inv_inv_add_inv

/--
lemma `inv_lt_inv` / 引理 `inv_lt_inv`

English:
lemma inv_lt_inv
  statement: p⁻¹ < r⁻¹
  proof: h.coe.inv_lt_inv

中文:
引理 inv_lt_inv
  结论: p⁻¹ < r⁻¹
  证明: h.coe.inv_lt_inv
-/
protected lemma inv_lt_inv : p⁻¹ < r⁻¹ := h.coe.inv_lt_inv
/--
lemma `lt` / 引理 `lt`

English:
lemma lt
  statement: r < p
  proof: h.coe.lt

中文:
引理 lt
  结论: r < p
  证明: h.coe.lt

Depends on / 依赖: h.coe.lt
-/
lemma lt : r < p := h.coe.lt
/--
lemma `inv_sub_inv_eq_inv` / 引理 `inv_sub_inv_eq_inv`

English:
lemma inv_sub_inv_eq_inv
  statement: r⁻¹ - q⁻¹ = p⁻¹
  proof: by
  have := h.symm.inv_lt_inv.le
  exact_mod_cast h.coe.inv_sub_inv_eq_inv

中文:
引理 inv_sub_inv_eq_inv
  结论: r⁻¹ - q⁻¹ = p⁻¹
  证明: by
  have := h.symm.inv_lt_inv.le
  exact_mod_cast h.coe.inv_sub_inv_eq_inv

Depends on / 依赖: h.coe.inv_sub_inv_eq_inv, h.symm.inv_lt_inv.le, inv_lt_inv, inv_sub_inv_eq_inv
-/
lemma inv_sub_inv_eq_inv : r⁻¹ - q⁻¹ = p⁻¹ := by
  have := h.symm.inv_lt_inv.le
  exact_mod_cast h.coe.inv_sub_inv_eq_inv

/--
lemma `holderConjugate_div_div` / 引理 `holderConjugate_div_div`

English:
lemma holderConjugate_div_div
  statement: (p / r).HolderConjugate (q / r) where
  proof: by
    simp [div_eq_mul_inv, ← mul_add, h.inv_add_inv_eq_inv, h.ne_zero']
  left_pos := by have := h.left_pos; have := h.pos'; positivity
  right_pos := by have := h.right_pos; have := h.pos'; positivity

中文:
引理 holderConjugate_div_div
  结论: (p / r).HolderConjugate (q / r) where
  证明: by
    simp [div_eq_mul_inv, ← mul_add, h.inv_add_inv_eq_inv, h.ne_zero']
  left_pos := by have := h.left_pos; have := h.pos'; positivity
  right_pos := by have := h.right_pos; have := h.pos'; positivity

Depends on / 依赖: div_eq_mul_inv, h.inv_add_inv_eq_inv, h.left_pos, h.ne_zero, h.pos, h.right_pos, inv_add_inv_eq_inv, left_pos, mul_add, ne_zero, right_pos
-/
lemma holderConjugate_div_div : (p / r).HolderConjugate (q / r) where
  inv_add_inv_eq_inv := by
    simp [div_eq_mul_inv, ← mul_add, h.inv_add_inv_eq_inv, h.ne_zero']
  left_pos := by have := h.left_pos; have := h.pos'; positivity
  right_pos := by have := h.right_pos; have := h.pos'; positivity

end HolderTriple

namespace HolderConjugate

/--
lemma `two_two` / 引理 `two_two`

English:
lemma two_two
  statement: HolderConjugate 2 2 where
  proof: by simpa using add_halves (1 : Real>=0)
  left_pos := zero_lt_two
  right_pos := zero_lt_two

中文:
引理 two_two
  结论: HolderConjugate 2 2 where
  证明: by simpa using add_halves (1 : Real>=0)
  left_pos := zero_lt_two
  right_pos := zero_lt_two

Depends on / 依赖: add_halves, left_pos, right_pos, zero_lt_two
-/
lemma two_two : HolderConjugate 2 2 where
  inv_add_inv_eq_inv := by simpa using add_halves (1 : Real>=0)
  left_pos := zero_lt_two
  right_pos := zero_lt_two

section
variable (h : p.HolderConjugate q)
include h

@[symm]
/--
lemma `symm` / 引理 `symm`

English:
lemma symm
  statement: q.HolderConjugate p
  proof: HolderTriple.symm h

中文:
引理 symm
  结论: q.HolderConjugate p
  证明: HolderTriple.symm h
-/
protected lemma symm : q.HolderConjugate p := HolderTriple.symm h

/--
theorem `inv_add_inv_eq_one` / 定理 `inv_add_inv_eq_one`

English:
theorem inv_add_inv_eq_one
  statement: p⁻¹ + q⁻¹ = 1
  proof: inv_one (G := Real>=0) ▸ h.inv_add_inv_eq_inv

中文:
定理 inv_add_inv_eq_one
  结论: p⁻¹ + q⁻¹ = 1
  证明: inv_one (G := Real>=0) ▸ h.inv_add_inv_eq_inv

Depends on / 依赖: h.inv_add_inv_eq_inv, inv_add_inv_eq_inv, inv_one
-/
theorem inv_add_inv_eq_one : p⁻¹ + q⁻¹ = 1 := inv_one (G := Real>=0) ▸ h.inv_add_inv_eq_inv

/--
theorem `sub_one_pos` / 定理 `sub_one_pos`

English:
theorem sub_one_pos
  statement: 0 < p - 1
  proof: tsub_pos_of_lt h.lt

中文:
定理 sub_one_pos
  结论: 0 < p - 1
  证明: tsub_pos_of_lt h.lt

Depends on / 依赖: h.lt, tsub_pos_of_lt
-/
theorem sub_one_pos : 0 < p - 1 := tsub_pos_of_lt h.lt
/--
theorem `sub_one_ne_zero` / 定理 `sub_one_ne_zero`

English:
theorem sub_one_ne_zero
  statement: p - 1 != 0
  proof: h.sub_one_pos.ne'

中文:
定理 sub_one_ne_zero
  结论: p - 1 != 0
  证明: h.sub_one_pos.ne'

Depends on / 依赖: h.sub_one_pos.ne, sub_one_pos
-/
theorem sub_one_ne_zero : p - 1 != 0 := h.sub_one_pos.ne'

/--
theorem `conjugate_eq` / 定理 `conjugate_eq`

English:
theorem conjugate_eq
  statement: q = p / (p - 1)
  proof: by
  have : ((1 : Real>=0) : Real) <= p := h.coe.lt.le
  exact_mod_cast NNReal.coe_sub this ▸ coe_one ▸ h.coe.conjugate_eq

中文:
定理 conjugate_eq
  结论: q = p / (p - 1)
  证明: by
  have : ((1 : Real>=0) : Real) <= p := h.coe.lt.le
  exact_mod_cast NNReal.coe_sub this ▸ coe_one ▸ h.coe.conjugate_eq

Depends on / 依赖: NNReal, NNReal.coe_sub, coe_one, coe_sub, conjugate_eq, h.coe.conjugate_eq, h.coe.lt.le
-/
theorem conjugate_eq : q = p / (p - 1) := by
  have : ((1 : Real>=0) : Real) <= p := h.coe.lt.le
  exact_mod_cast NNReal.coe_sub this ▸ coe_one ▸ h.coe.conjugate_eq

/--
lemma `conjExponent_eq` / 引理 `conjExponent_eq`

English:
lemma conjExponent_eq
  statement: conjExponent p = q
  proof: h.conjugate_eq.symm

中文:
引理 conjExponent_eq
  结论: conjExponent p = q
  证明: h.conjugate_eq.symm

Depends on / 依赖: conjugate_eq, h.conjugate_eq.symm
-/
lemma conjExponent_eq : conjExponent p = q := h.conjugate_eq.symm

/--
lemma `one_sub_inv` / 引理 `one_sub_inv`

English:
lemma one_sub_inv
  statement: 1 - p⁻¹ = q⁻¹
  proof: tsub_eq_of_eq_add h.symm.inv_add_inv_eq_one.symm

中文:
引理 one_sub_inv
  结论: 1 - p⁻¹ = q⁻¹
  证明: tsub_eq_of_eq_add h.symm.inv_add_inv_eq_one.symm

Depends on / 依赖: h.symm.inv_add_inv_eq_one.symm, inv_add_inv_eq_one, tsub_eq_of_eq_add
-/
lemma one_sub_inv : 1 - p⁻¹ = q⁻¹ := tsub_eq_of_eq_add h.symm.inv_add_inv_eq_one.symm

/--
theorem `sub_one_mul_conj` / 定理 `sub_one_mul_conj`

English:
theorem sub_one_mul_conj
  statement: (p - 1) * q = p
  proof: mul_comm q (p - 1) ▸ (eq_div_iff h.sub_one_ne_zero).1 h.conjugate_eq

中文:
定理 sub_one_mul_conj
  结论: (p - 1) * q = p
  证明: mul_comm q (p - 1) ▸ (eq_div_iff h.sub_one_ne_zero).1 h.conjugate_eq

Depends on / 依赖: conjugate_eq, eq_div_iff, h.conjugate_eq, h.sub_one_ne_zero, mul_comm, sub_one_ne_zero
-/
theorem sub_one_mul_conj : (p - 1) * q = p :=
  mul_comm q (p - 1) ▸ (eq_div_iff h.sub_one_ne_zero).1 h.conjugate_eq

/--
theorem `mul_eq_add` / 定理 `mul_eq_add`

English:
theorem mul_eq_add
  statement: p * q = p + q
  proof: by
  simpa [mul_add, add_mul, h.ne_zero, h.symm.ne_zero, add_comm q] using congr(p * $(h.inv_eq) * q)

中文:
定理 mul_eq_add
  结论: p * q = p + q
  证明: by
  simpa [mul_add, add_mul, h.ne_zero, h.symm.ne_zero, add_comm q] using congr(p * $(h.inv_eq) * q)

Depends on / 依赖: add_comm, add_mul, h.inv_eq, h.ne_zero, h.symm.ne_zero, inv_eq, mul_add, ne_zero
-/
theorem mul_eq_add : p * q = p + q := by
  simpa [mul_add, add_mul, h.ne_zero, h.symm.ne_zero, add_comm q] using congr(p * $(h.inv_eq) * q)

/--
theorem `div_conj_eq_sub_one` / 定理 `div_conj_eq_sub_one`

English:
theorem div_conj_eq_sub_one
  statement: p / q = p - 1
  proof: by
  field_simp [h.symm.ne_zero]
  linear_combination -h.sub_one_mul_conj

中文:
定理 div_conj_eq_sub_one
  结论: p / q = p - 1
  证明: by
  field_simp [h.symm.ne_zero]
  linear_combination -h.sub_one_mul_conj

Depends on / 依赖: h.sub_one_mul_conj, h.symm.ne_zero, linear_combination, ne_zero, sub_one_mul_conj
-/
theorem div_conj_eq_sub_one : p / q = p - 1 := by
  field_simp [h.symm.ne_zero]
  linear_combination -h.sub_one_mul_conj

/--
lemma `inv_add_inv_ennreal` / 引理 `inv_add_inv_ennreal`

English:
lemma inv_add_inv_ennreal
  statement: (p⁻¹ + q⁻¹ : Real>=0∞) = 1
  proof: by norm_cast; exact h.inv_add_inv_eq_one

中文:
引理 inv_add_inv_ennreal
  结论: (p⁻¹ + q⁻¹ : 实数>=0∞) = 1
  证明: by norm_cast; exact h.inv_add_inv_eq_one

Depends on / 依赖: h.inv_add_inv_eq_one, inv_add_inv_eq_one
-/
lemma inv_add_inv_ennreal : (p⁻¹ + q⁻¹ : Real>=0∞) = 1 := by norm_cast; exact h.inv_add_inv_eq_one

end

/--
lemma `_root_.NNReal.holderConjugate_iff` / 引理 `_root_.NNReal.holderConjugate_iff`

English:
lemma _root_.NNReal.holderConjugate_iff
  statement: p.HolderConjugate q ↔ 1 < p ∧ p⁻¹ + q⁻¹ = 1
  proof: by
  rw [← holderConjugate_coe_iff]; rw [Real.holderConjugate_iff]; rw [← coe_one]
  exact_mod_cast Iff.rfl

中文:
引理 _root_.非负实数.holderConjugate_iff
  结论: p.HolderConjugate q ↔ 1 < p ∧ p⁻¹ + q⁻¹ = 1
  证明: by
  rw [← holderConjugate_coe_iff]; rw [Real.holderConjugate_iff]; rw [← coe_one]
  exact_mod_cast Iff.rfl

Depends on / 依赖: Iff.rfl, Real.holderConjugate_iff, coe_one, holderConjugate_coe_iff, holderConjugate_iff
-/
lemma _root_.NNReal.holderConjugate_iff : p.HolderConjugate q ↔ 1 < p ∧ p⁻¹ + q⁻¹ = 1 := by
  rw [← holderConjugate_coe_iff]; rw [Real.holderConjugate_iff]; rw [← coe_one]
  exact_mod_cast Iff.rfl

/--
lemma `inv_inv` / 引理 `inv_inv`

English:
lemma inv_inv
  given: (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
  statement: a⁻¹.HolderConjugate b⁻¹ where
  proof: by simpa using hab
  left_pos := inv_pos.mpr ha
  right_pos := inv_pos.mpr hb

中文:
引理 inv_inv
  条件: (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
  结论: a⁻¹.HolderConjugate b⁻¹ where
  证明: by simpa using hab
  left_pos := inv_pos.mpr ha
  right_pos := inv_pos.mpr hb
-/
protected lemma inv_inv (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) : a⁻¹.HolderConjugate b⁻¹ where
  inv_add_inv_eq_inv := by simpa using hab
  left_pos := inv_pos.mpr ha
  right_pos := inv_pos.mpr hb

/--
lemma `inv_one_sub_inv` / 引理 `inv_one_sub_inv`

English:
lemma inv_one_sub_inv
  given: (ha₀ : 0 < a) (ha₁ : a < 1)
  statement: a⁻¹.HolderConjugate (1 - a)⁻¹
  proof: .mpr ha₁, by simpa using add_tsub_cancel_of_le ha₁.le⟩ holderConjugate_iff.mpr ⟨one_lt_inv₀ ha₀

中文:
引理 inv_one_sub_inv
  条件: (ha₀ : 0 < a) (ha₁ : a < 1)
  结论: a⁻¹.HolderConjugate (1 - a)⁻¹
  证明: .mpr ha₁, by simpa using add_tsub_cancel_of_le ha₁.le⟩ holderConjugate_iff.mpr ⟨one_lt_inv₀ ha₀

Depends on / 依赖: add_tsub_cancel_of_le, holderConjugate_iff, holderConjugate_iff.mpr
-/
lemma inv_one_sub_inv (ha₀ : 0 < a) (ha₁ : a < 1) : a⁻¹.HolderConjugate (1 - a)⁻¹ :=
.mpr ha₁, by simpa using add_tsub_cancel_of_le ha₁.le⟩ holderConjugate_iff.mpr ⟨one_lt_inv₀ ha₀

/--
lemma `one_sub_inv_inv` / 引理 `one_sub_inv_inv`

English:
lemma one_sub_inv_inv
  given: (ha₀ : 0 < a) (ha₁ : a < 1)
  statement: (1 - a)⁻¹.HolderConjugate a⁻¹
  proof: (inv_one_sub_inv ha₀ ha₁).symm

中文:
引理 one_sub_inv_inv
  条件: (ha₀ : 0 < a) (ha₁ : a < 1)
  结论: (1 - a)⁻¹.HolderConjugate a⁻¹
  证明: (inv_one_sub_inv ha₀ ha₁).symm

Depends on / 依赖: inv_one_sub_inv
-/
lemma one_sub_inv_inv (ha₀ : 0 < a) (ha₁ : a < 1) : (1 - a)⁻¹.HolderConjugate a⁻¹ :=
  (inv_one_sub_inv ha₀ ha₁).symm

end HolderConjugate

/--
lemma `holderConjugate_comm` / 引理 `holderConjugate_comm`

English:
lemma holderConjugate_comm
  statement: p.HolderConjugate q ↔ q.HolderConjugate p
  proof: ⟨.symm, .symm⟩

中文:
引理 holderConjugate_comm
  结论: p.HolderConjugate q ↔ q.HolderConjugate p
  证明: ⟨.symm, .symm⟩
-/
lemma holderConjugate_comm : p.HolderConjugate q ↔ q.HolderConjugate p := ⟨.symm, .symm⟩

/--
lemma `holderConjugate_iff_eq_conjExponent` / 引理 `holderConjugate_iff_eq_conjExponent`

English:
lemma holderConjugate_iff_eq_conjExponent
  given: (hp : 1 < p)
  statement: p.HolderConjugate q ↔ q = p / (p - 1)
  proof: by
  rw [← holderConjugate_coe_iff]; rw [Real.holderConjugate_iff_eq_conjExponent (by exact_mod_cast hp)]; rw [← coe_one]; rw [← NNReal.coe_sub hp.le]
  exact_mod_cast Iff.rfl

中文:
引理 holderConjugate_iff_eq_conjExponent
  条件: (hp : 1 < p)
  结论: p.HolderConjugate q ↔ q = p / (p - 1)
  证明: by
  rw [← holderConjugate_coe_iff]; rw [Real.holderConjugate_iff_eq_conjExponent (by exact_mod_cast hp)]; rw [← coe_one]; rw [← NNReal.coe_sub hp.le]
  exact_mod_cast Iff.rfl

Depends on / 依赖: Iff.rfl, NNReal, NNReal.coe_sub, Real.holderConjugate_iff_eq_conjExponent, coe_one, coe_sub, holderConjugate_coe_iff, holderConjugate_iff_eq_conjExponent, hp.le
-/
lemma holderConjugate_iff_eq_conjExponent (hp : 1 < p) : p.HolderConjugate q ↔ q = p / (p - 1) := by
  rw [← holderConjugate_coe_iff]; rw [Real.holderConjugate_iff_eq_conjExponent (by exact_mod_cast hp)]; rw [← coe_one]; rw [← NNReal.coe_sub hp.le]
  exact_mod_cast Iff.rfl

/--
lemma `HolderConjugate.conjExponent` / 引理 `HolderConjugate.conjExponent`

English:
lemma HolderConjugate.conjExponent
  given: (h : 1 < p)
  statement: p.HolderConjugate (conjExponent p)
  proof: (holderConjugate_iff_eq_conjExponent h).2 rfl

中文:
引理 HolderConjugate.conjExponent
  条件: (h : 1 < p)
  结论: p.HolderConjugate (conjExponent p)
  证明: (holderConjugate_iff_eq_conjExponent h).2 rfl
-/
lemma HolderConjugate.conjExponent (h : 1 < p) : p.HolderConjugate (conjExponent p) :=
  (holderConjugate_iff_eq_conjExponent h).2 rfl

/--
lemma `holderConjugate_one_div` / 引理 `holderConjugate_one_div`

English:
lemma holderConjugate_one_div
  given: (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
  proof: by simpa using HolderConjugate.inv_inv ha hb hab

中文:
引理 holderConjugate_one_div
  条件: (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
  证明: by simpa using HolderConjugate.inv_inv ha hb hab

Depends on / 依赖: HolderConjugate, HolderConjugate.inv_inv, inv_inv
-/
lemma holderConjugate_one_div (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    (1 / a).HolderConjugate (1 / b) := by simpa using HolderConjugate.inv_inv ha hb hab

end NNReal

/--
lemma `Real.HolderTriple.toNNReal` / 引理 `Real.HolderTriple.toNNReal`

English:
lemma Real.HolderTriple.toNNReal
  given: {p q r : Real} (h : p.HolderTriple q r)
  proof: by
  simpa [← NNReal.holderTriple_coe_iff, h.nonneg, h.symm.nonneg, h.nonneg']

中文:
引理 实数.HolderTriple.toNN实数
  条件: {p q r : 实数} (h : p.HolderTriple q r)
  证明: by
  simpa [← NNReal.holderTriple_coe_iff, h.nonneg, h.symm.nonneg, h.nonneg']
-/
protected lemma Real.HolderTriple.toNNReal {p q r : Real} (h : p.HolderTriple q r) :
    p.toNNReal.HolderTriple q.toNNReal r.toNNReal := by
  simpa [← NNReal.holderTriple_coe_iff, h.nonneg, h.symm.nonneg, h.nonneg']

/--
lemma `Real.HolderConjugate.toNNReal` / 引理 `Real.HolderConjugate.toNNReal`

English:
lemma Real.HolderConjugate.toNNReal
  given: {p q : Real} (h : p.HolderConjugate q)
  proof: by
  simpa using Real.HolderTriple.toNNReal h

中文:
引理 实数.HolderConjugate.toNN实数
  条件: {p q : 实数} (h : p.HolderConjugate q)
  证明: by
  simpa using Real.HolderTriple.toNNReal h
-/
protected lemma Real.HolderConjugate.toNNReal {p q : Real} (h : p.HolderConjugate q) :
    p.toNNReal.HolderConjugate q.toNNReal := by
  simpa using Real.HolderTriple.toNNReal h

namespace ENNReal

/--
Definition of `conjExponent` / `conjExponent` 的定义

English:
definition conjExponent
  signature: (p : Real>=0∞)
  body: 1 + (p - 1)⁻¹

中文:
定义 conjExponent
  签名: (p : 实数>=0∞)
  定义体: 1 + (p - 1)⁻¹
-/
noncomputable def conjExponent (p : Real>=0∞) : Real>=0∞ := 1 + (p - 1)⁻¹

/--
lemma `coe_conjExponent` / 引理 `coe_conjExponent`

English:
lemma coe_conjExponent
  given: {p : Real>=0} (hp : 1 < p)
  statement: p.conjExponent = conjExponent p
  proof: by
  rw [NNReal.conjExponent]; rw [conjExponent]
  norm_cast
  rw [← coe_inv (tsub_pos_of_lt hp).ne']
  norm_cast
  field_simp [(tsub_pos_of_lt hp).ne']
  rw [tsub_add_cancel_of_le hp.le]

中文:
引理 coe_conjExponent
  条件: {p : 实数>=0} (hp : 1 < p)
  结论: p.conjExponent = conjExponent p
  证明: by
  rw [NNReal.conjExponent]; rw [conjExponent]
  norm_cast
  rw [← coe_inv (tsub_pos_of_lt hp).ne']
  norm_cast
  field_simp [(tsub_pos_of_lt hp).ne']
  rw [tsub_add_cancel_of_le hp.le]

Depends on / 依赖: NNReal, NNReal.conjExponent, coe_inv, conjExponent, hp.le, tsub_add_cancel_of_le, tsub_pos_of_lt
-/
lemma coe_conjExponent {p : Real>=0} (hp : 1 < p) : p.conjExponent = conjExponent p := by
  rw [NNReal.conjExponent]; rw [conjExponent]
  norm_cast
  rw [← coe_inv (tsub_pos_of_lt hp).ne']
  norm_cast
  field_simp [(tsub_pos_of_lt hp).ne']
  rw [tsub_add_cancel_of_le hp.le]


variable {a b p q r : Real>=0∞}

@[simp, norm_cast]
/--
lemma `holderTriple_coe_iff` / 引理 `holderTriple_coe_iff`

English:
lemma holderTriple_coe_iff
  given: {p q r : Real>=0} (hr : r != 0)
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [NNReal.holderTriple_iff]
    obtain ⟨hp, hq⟩ : p != 0 ∧ q != 0 := by
      constructor
      all_goals
        rintro rfl
        apply hr
        exact_mod_cast (coe_zero ▸ h).unique _ _ r 0
    exact ⟨by exact_mod_cast h.inv_add_inv_eq_inv, hp.bot_lt, hq.bot_lt⟩
  · rw [holderTriple_iff]
    have hp := h.ne_zero
    have hq := h.symm.ne_zero
    exact_mod_cast h.inv_add_inv_eq_inv

alias ⟨_, _root_.NNReal.HolderTriple.coe_ennreal⟩ := holderTriple_coe_iff

@[simp, norm_cast]

中文:
引理 holderTriple_coe_iff
  条件: {p q r : 实数>=0} (hr : r != 0)
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [NNReal.holderTriple_iff]
    obtain ⟨hp, hq⟩ : p != 0 ∧ q != 0 := by
      constructor
      all_goals
        rintro rfl
        apply hr
        exact_mod_cast (coe_zero ▸ h).unique _ _ r 0
    exact ⟨by exact_mod_cast h.inv_add_inv_eq_inv, hp.bot_lt, hq.bot_lt⟩
  · rw [holderTriple_iff]
    have hp := h.ne_zero
    have hq := h.symm.ne_zero
    exact_mod_cast h.inv_add_inv_eq_inv

alias ⟨_, _root_.NNReal.HolderTriple.coe_ennreal⟩ := holderTriple_coe_iff

@[simp, norm_cast]

Depends on / 依赖: NNReal, NNReal.holderTriple_iff, all_goals, bot_lt, coe_zero, h.inv_add_inv_eq_inv, h.ne_zero, h.symm.ne_zero, holderTriple_iff, hp.bot_lt, hq.bot_lt, inv_add_inv_eq_inv, ne_zero, unique
-/
lemma holderTriple_coe_iff {p q r : Real>=0} (hr : r != 0) :
    HolderTriple (p : Real>=0∞) (q : Real>=0∞) (r : Real>=0∞) ↔ NNReal.HolderTriple p q r := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [NNReal.holderTriple_iff]
    obtain ⟨hp, hq⟩ : p != 0 ∧ q != 0 := by
      constructor
      all_goals
        rintro rfl
        apply hr
        exact_mod_cast (coe_zero ▸ h).unique _ _ r 0
    exact ⟨by exact_mod_cast h.inv_add_inv_eq_inv, hp.bot_lt, hq.bot_lt⟩
  · rw [holderTriple_iff]
    have hp := h.ne_zero
    have hq := h.symm.ne_zero
    exact_mod_cast h.inv_add_inv_eq_inv

alias ⟨_, _root_.NNReal.HolderTriple.coe_ennreal⟩ := holderTriple_coe_iff

@[simp, norm_cast]
/--
lemma `holderConjugate_coe_iff` / 引理 `holderConjugate_coe_iff`

English:
lemma holderConjugate_coe_iff
  given: {p q : Real>=0}
  proof: holderTriple_coe_iff one_ne_zero

alias ⟨_, _root_.NNReal.HolderConjugate.coe_ennreal⟩ := holderConjugate_coe_iff

中文:
引理 holderConjugate_coe_iff
  条件: {p q : 实数>=0}
  证明: holderTriple_coe_iff one_ne_zero

alias ⟨_, _root_.NNReal.HolderConjugate.coe_ennreal⟩ := holderConjugate_coe_iff

Depends on / 依赖: holderTriple_coe_iff, infer_instance, one_ne_zero, orthRadius
-/
lemma holderConjugate_coe_iff {p q : Real>=0} :
    HolderConjugate (p : Real>=0∞) (q : Real>=0∞) ↔ NNReal.HolderConjugate p q :=
  holderTriple_coe_iff one_ne_zero

alias ⟨_, _root_.NNReal.HolderConjugate.coe_ennreal⟩ := holderConjugate_coe_iff

namespace HolderTriple

/--
lemma `_root_.Real.HolderTriple.ennrealOfReal` / 引理 `_root_.Real.HolderTriple.ennrealOfReal`

English:
lemma _root_.Real.HolderTriple.ennrealOfReal
  given: {p q r : Real} (h : p.HolderTriple q r)
  proof: by
  simpa [holderTriple_iff, ofReal_inv_of_pos, h.pos, h.symm.pos, h.pos', ofReal_add, h.nonneg,
h.symm.nonneg] using congr(ENNReal.ofReal (h.inv_add_inv_eq_inv))

中文:
引理 _root_.实数.HolderTriple.ennrealOf实数
  条件: {p q r : 实数} (h : p.HolderTriple q r)
  证明: by
  simpa [holderTriple_iff, ofReal_inv_of_pos, h.pos, h.symm.pos, h.pos', ofReal_add, h.nonneg,
h.symm.nonneg] using congr(ENNReal.ofReal (h.inv_add_inv_eq_inv))

Depends on / 依赖: ENNReal, ENNReal.ofReal, h.inv_add_inv_eq_inv, h.nonneg, h.pos, h.symm.nonneg, h.symm.pos, holderTriple_iff, inv_add_inv_eq_inv, nonneg, ofReal, ofReal_add, ofReal_inv_of_pos
-/
lemma _root_.Real.HolderTriple.ennrealOfReal {p q r : Real} (h : p.HolderTriple q r) :
    HolderTriple (ENNReal.ofReal p) (ENNReal.ofReal q) (ENNReal.ofReal r) := by
  simpa [holderTriple_iff, ofReal_inv_of_pos, h.pos, h.symm.pos, h.pos', ofReal_add, h.nonneg,
h.symm.nonneg] using congr(ENNReal.ofReal (h.inv_add_inv_eq_inv))

/--
lemma `_root_.Real.HolderConjugate.ennrealOfReal` / 引理 `_root_.Real.HolderConjugate.ennrealOfReal`

English:
lemma _root_.Real.HolderConjugate.ennrealOfReal
  given: {p q : Real} (h : p.HolderConjugate q)
  proof: by
  simpa using Real.HolderTriple.ennrealOfReal h

中文:
引理 _root_.实数.HolderConjugate.ennrealOf实数
  条件: {p q : 实数} (h : p.HolderConjugate q)
  证明: by
  simpa using Real.HolderTriple.ennrealOfReal h

Depends on / 依赖: HolderTriple, Real.HolderTriple.ennrealOfReal, ennrealOfReal
-/
lemma _root_.Real.HolderConjugate.ennrealOfReal {p q : Real} (h : p.HolderConjugate q) :
    HolderConjugate (ENNReal.ofReal p) (ENNReal.ofReal q) := by
  simpa using Real.HolderTriple.ennrealOfReal h

/--
lemma `of_toReal` / 引理 `of_toReal`

English:
lemma of_toReal
  given: (h : Real.HolderTriple p.toReal q.toReal r.toReal)
  statement: HolderTriple p q r
  proof: by
  have hp := h.pos
  have hq := h.symm.pos
  have hr := h.pos'
  rw [toReal_pos_iff] at hp hq hr
  simpa [hp.2.ne, hq.2.ne, hr.2.ne] using h.ennrealOfReal

中文:
引理 of_to实数
  条件: (h : 实数.HolderTriple p.to实数 q.to实数 r.to实数)
  结论: HolderTriple p q r
  证明: by
  have hp := h.pos
  have hq := h.symm.pos
  have hr := h.pos'
  rw [toReal_pos_iff] at hp hq hr
  simpa [hp.2.ne, hq.2.ne, hr.2.ne] using h.ennrealOfReal

Depends on / 依赖: direction_orthRadius, ennrealOfReal, h.ennrealOfReal, h.pos, h.symm.pos, infer_instance, toReal_pos_iff
-/
lemma of_toReal (h : Real.HolderTriple p.toReal q.toReal r.toReal) : HolderTriple p q r := by
  have hp := h.pos
  have hq := h.symm.pos
  have hr := h.pos'
  rw [toReal_pos_iff] at hp hq hr
  simpa [hp.2.ne, hq.2.ne, hr.2.ne] using h.ennrealOfReal

variable (r) in
/--
lemma `toReal_iff` / 引理 `toReal_iff`

English:
lemma toReal_iff
  given: (hp : 0 < p.toReal) (hq : 0 < q.toReal)
  proof: by
  refine ⟨of_toReal, fun h => ⟨?_, hp, hq⟩⟩
  rw [toReal_pos_iff] at hp hq
  simpa [toReal_add, Finiteness.inv_ne_top, hp.1.ne', hq.1.ne']
    using congr(ENNReal.toReal $(h.inv_add_inv_eq_inv))

中文:
引理 to实数_iff
  条件: (hp : 0 < p.to实数) (hq : 0 < q.to实数)
  证明: by
  refine ⟨of_toReal, fun h => ⟨?_, hp, hq⟩⟩
  rw [toReal_pos_iff] at hp hq
  simpa [toReal_add, Finiteness.inv_ne_top, hp.1.ne', hq.1.ne']
    using congr(ENNReal.toReal $(h.inv_add_inv_eq_inv))

Depends on / 依赖: ENNReal, ENNReal.toReal, Finiteness, Finiteness.inv_ne_top, h.inv_add_inv_eq_inv, inv_add_inv_eq_inv, inv_ne_top, of_toReal, toReal, toReal_add, toReal_pos_iff
-/
lemma toReal_iff (hp : 0 < p.toReal) (hq : 0 < q.toReal) :
    Real.HolderTriple p.toReal q.toReal r.toReal ↔ HolderTriple p q r := by
  refine ⟨of_toReal, fun h => ⟨?_, hp, hq⟩⟩
  rw [toReal_pos_iff] at hp hq
  simpa [toReal_add, Finiteness.inv_ne_top, hp.1.ne', hq.1.ne']
    using congr(ENNReal.toReal $(h.inv_add_inv_eq_inv))

variable (r) in
/--
lemma `toReal` / 引理 `toReal`

English:
lemma toReal
  given: (hp : 0 < p.toReal) (hq : 0 < q.toReal) [HolderTriple p q r]
  proof: .mpr ‹_› toReal_iff r hp hq

中文:
引理 to实数
  条件: (hp : 0 < p.to实数) (hq : 0 < q.to实数) [HolderTriple p q r]
  证明: .mpr ‹_› toReal_iff r hp hq

Depends on / 依赖: toReal_iff
-/
lemma toReal (hp : 0 < p.toReal) (hq : 0 < q.toReal) [HolderTriple p q r] :
    Real.HolderTriple p.toReal q.toReal r.toReal :=
.mpr ‹_› toReal_iff r hp hq

/--
lemma `of_toNNReal` / 引理 `of_toNNReal`

English:
lemma of_toNNReal
  given: (h : NNReal.HolderTriple p.toNNReal q.toNNReal r.toNNReal)
  proof: .of_toReal by simpa only [coe_toNNReal_eq_toReal] using h.coe

中文:
引理 of_toNN实数
  条件: (h : 非负实数.HolderTriple p.toNN实数 q.toNN实数 r.toNN实数)
  证明: .of_toReal by simpa only [coe_toNNReal_eq_toReal] using h.coe

Depends on / 依赖: coe_toNNReal_eq_toReal, h.coe, of_toReal
-/
lemma of_toNNReal (h : NNReal.HolderTriple p.toNNReal q.toNNReal r.toNNReal) :
    HolderTriple p q r :=
.of_toReal by simpa only [coe_toNNReal_eq_toReal] using h.coe

variable (r) in
/--
lemma `toNNReal_iff` / 引理 `toNNReal_iff`

English:
lemma toNNReal_iff
  given: (hp : 0 < p.toNNReal) (hq : 0 < q.toNNReal)
  proof: by
  simp_rw [← NNReal.holderTriple_coe_iff, coe_toNNReal_eq_toReal]
  apply toReal_iff r ?_ ?_
  all_goals simpa [← coe_toNNReal_eq_toReal]

中文:
引理 toNN实数_iff
  条件: (hp : 0 < p.toNN实数) (hq : 0 < q.toNN实数)
  证明: by
  simp_rw [← NNReal.holderTriple_coe_iff, coe_toNNReal_eq_toReal]
  apply toReal_iff r ?_ ?_
  all_goals simpa [← coe_toNNReal_eq_toReal]

Depends on / 依赖: NNReal, NNReal.holderTriple_coe_iff, all_goals, coe_toNNReal_eq_toReal, holderTriple_coe_iff, simp_rw, toReal_iff
-/
lemma toNNReal_iff (hp : 0 < p.toNNReal) (hq : 0 < q.toNNReal) :
    NNReal.HolderTriple p.toNNReal q.toNNReal r.toNNReal ↔ HolderTriple p q r := by
  simp_rw [← NNReal.holderTriple_coe_iff, coe_toNNReal_eq_toReal]
  apply toReal_iff r ?_ ?_
  all_goals simpa [← coe_toNNReal_eq_toReal]

variable (r) in
/--
lemma `toNNReal` / 引理 `toNNReal`

English:
lemma toNNReal
  given: (hp : 0 < p.toNNReal) (hq : 0 < q.toNNReal) [HolderTriple p q r]
  proof: .mpr ‹_› toNNReal_iff r hp hq

中文:
引理 toNN实数
  条件: (hp : 0 < p.toNN实数) (hq : 0 < q.toNN实数) [HolderTriple p q r]
  证明: .mpr ‹_› toNNReal_iff r hp hq

Depends on / 依赖: toNNReal_iff
-/
lemma toNNReal (hp : 0 < p.toNNReal) (hq : 0 < q.toNNReal) [HolderTriple p q r] :
    NNReal.HolderTriple p.toNNReal q.toNNReal r.toNNReal :=
.mpr ‹_› toNNReal_iff r hp hq

end HolderTriple

namespace HolderConjugate

/--
lemma `of_toReal` / 引理 `of_toReal`

English:
lemma of_toReal
  given: (h : p.toReal.HolderConjugate q.toReal)
  statement: p.HolderConjugate q
  proof: by
  rw [Real.HolderConjugate] at h
  exact HolderTriple.of_toReal (toReal_one ▸ h)

中文:
引理 of_to实数
  条件: (h : p.to实数.HolderConjugate q.to实数)
  结论: p.HolderConjugate q
  证明: by
  rw [Real.HolderConjugate] at h
  exact HolderTriple.of_toReal (toReal_one ▸ h)

Depends on / 依赖: HolderConjugate, HolderTriple, HolderTriple.of_toReal, Real.HolderConjugate, of_toReal, toReal_one
-/
lemma of_toReal (h : p.toReal.HolderConjugate q.toReal) : p.HolderConjugate q := by
  rw [Real.HolderConjugate] at h
  exact HolderTriple.of_toReal (toReal_one ▸ h)

/--
lemma `toReal_iff` / 引理 `toReal_iff`

English:
lemma toReal_iff
  given: (hp : 1 < p.toReal)
  proof: by
  refine ⟨of_toReal, fun h => ?_⟩
  have hq : 0 < q.toReal := by
    rw [toReal_pos_iff]
.mpr ?_⟩ refine ⟨pos q p, lt_top_iff_one_lt q p
    contrapose! hp
    exact toReal_mono one_ne_top hp
  simpa using HolderTriple.toReal 1 (zero_lt_one.trans hp) hq

中文:
引理 to实数_iff
  条件: (hp : 1 < p.to实数)
  证明: by
  refine ⟨of_toReal, fun h => ?_⟩
  have hq : 0 < q.toReal := by
    rw [toReal_pos_iff]
.mpr ?_⟩ refine ⟨pos q p, lt_top_iff_one_lt q p
    contrapose! hp
    exact toReal_mono one_ne_top hp
  simpa using HolderTriple.toReal 1 (zero_lt_one.trans hp) hq

Depends on / 依赖: HolderTriple, HolderTriple.toReal, contrapose, lt_top_iff_one_lt, of_toReal, one_ne_top, q.toReal, toReal, toReal_mono, toReal_pos_iff, zero_lt_one, zero_lt_one.trans
-/
lemma toReal_iff (hp : 1 < p.toReal) :
    p.toReal.HolderConjugate q.toReal ↔ p.HolderConjugate q := by
  refine ⟨of_toReal, fun h => ?_⟩
  have hq : 0 < q.toReal := by
    rw [toReal_pos_iff]
.mpr ?_⟩ refine ⟨pos q p, lt_top_iff_one_lt q p
    contrapose! hp
    exact toReal_mono one_ne_top hp
  simpa using HolderTriple.toReal 1 (zero_lt_one.trans hp) hq

/--
lemma `toReal` / 引理 `toReal`

English:
lemma toReal
  given: (hp : 1 < p.toReal) [HolderConjugate p q]
  proof: .mpr ‹_› toReal_iff hp

中文:
引理 to实数
  条件: (hp : 1 < p.to实数) [HolderConjugate p q]
  证明: .mpr ‹_› toReal_iff hp

Depends on / 依赖: toReal_iff
-/
lemma toReal (hp : 1 < p.toReal) [HolderConjugate p q] :
    p.toReal.HolderConjugate q.toReal :=
.mpr ‹_› toReal_iff hp

/--
lemma `toReal_of_ne_top` / 引理 `toReal_of_ne_top`

English:
lemma toReal_of_ne_top
  given: (hp : p != ∞) (hq : q != ∞) [HolderConjugate p q]
  proof: toReal ((toReal_lt_toReal one_ne_top hp).mpr ((lt_top_iff_one_lt q p).mp hq.lt_top))

中文:
引理 to实数_of_ne_top
  条件: (hp : p != ∞) (hq : q != ∞) [HolderConjugate p q]
  证明: toReal ((toReal_lt_toReal one_ne_top hp).mpr ((lt_top_iff_one_lt q p).mp hq.lt_top))

Depends on / 依赖: hq.lt_top, lt_top, lt_top_iff_one_lt, one_ne_top, toReal, toReal_lt_toReal
-/
lemma toReal_of_ne_top (hp : p != ∞) (hq : q != ∞) [HolderConjugate p q] :
    p.toReal.HolderConjugate q.toReal :=
  toReal ((toReal_lt_toReal one_ne_top hp).mpr ((lt_top_iff_one_lt q p).mp hq.lt_top))

/--
lemma `of_toNNReal` / 引理 `of_toNNReal`

English:
lemma of_toNNReal
  given: (h : NNReal.HolderConjugate p.toNNReal q.toNNReal)
  proof: .of_toReal by simpa only [coe_toNNReal_eq_toReal] using h.coe

中文:
引理 of_toNN实数
  条件: (h : 非负实数.HolderConjugate p.toNN实数 q.toNN实数)
  证明: .of_toReal by simpa only [coe_toNNReal_eq_toReal] using h.coe

Depends on / 依赖: coe_toNNReal_eq_toReal, h.coe, of_toReal
-/
lemma of_toNNReal (h : NNReal.HolderConjugate p.toNNReal q.toNNReal) :
    HolderConjugate p q :=
.of_toReal by simpa only [coe_toNNReal_eq_toReal] using h.coe

/--
lemma `toNNReal_iff` / 引理 `toNNReal_iff`

English:
lemma toNNReal_iff
  given: (hp : 1 < p.toNNReal)
  proof: by
  simp_rw [← NNReal.holderTriple_coe_iff, coe_toNNReal_eq_toReal]
  apply toReal_iff ?_
  all_goals simpa [← coe_toNNReal_eq_toReal]

中文:
引理 toNN实数_iff
  条件: (hp : 1 < p.toNN实数)
  证明: by
  simp_rw [← NNReal.holderTriple_coe_iff, coe_toNNReal_eq_toReal]
  apply toReal_iff ?_
  all_goals simpa [← coe_toNNReal_eq_toReal]

Depends on / 依赖: NNReal, NNReal.holderTriple_coe_iff, all_goals, coe_toNNReal_eq_toReal, holderTriple_coe_iff, simp_rw, toReal_iff
-/
lemma toNNReal_iff (hp : 1 < p.toNNReal) :
    NNReal.HolderConjugate p.toNNReal q.toNNReal ↔ HolderConjugate p q := by
  simp_rw [← NNReal.holderTriple_coe_iff, coe_toNNReal_eq_toReal]
  apply toReal_iff ?_
  all_goals simpa [← coe_toNNReal_eq_toReal]

/--
lemma `toNNReal` / 引理 `toNNReal`

English:
lemma toNNReal
  given: (hp : 1 < p.toNNReal) [HolderConjugate p q]
  proof: .mpr ‹_› toNNReal_iff hp

中文:
引理 toNN实数
  条件: (hp : 1 < p.toNN实数) [HolderConjugate p q]
  证明: .mpr ‹_› toNNReal_iff hp

Depends on / 依赖: toNNReal_iff
-/
lemma toNNReal (hp : 1 < p.toNNReal) [HolderConjugate p q] :
    NNReal.HolderConjugate p.toNNReal q.toNNReal :=
.mpr ‹_› toNNReal_iff hp

/--
lemma `conjExponent` / 引理 `conjExponent`

English:
lemma conjExponent
  given: {p : Real>=0∞} (hp : 1 <= p)
  statement: p.HolderConjugate (conjExponent p)
  proof: by
  have : p != 0 := (zero_lt_one.trans_le hp).ne'
  rw [HolderConjugate]; rw [holderTriple_iff]; rw [conjExponent]; rw [add_comm]
  refine (AddLECancellable.eq_tsub_iff_add_eq_of_le (α := Real>=0∞) (by simpa) (by simpa)).1 ?_
  rw [inv_eq_iff_eq_inv]
  obtain rfl | hp₁ := hp.eq_or_lt
  · simp
  obtain rfl | hp := eq_or_ne p ∞
  · simp
  calc
    1 + (p - 1)⁻¹ = (p - 1 + 1) / (p - 1) := by
      rw [ENNReal.add_div]; rw [ENNReal.div_self ((tsub_pos_of_lt hp₁).ne') (sub_ne_top hp)]; rw [one_div]
    _ = (1⁻¹ - p⁻¹)⁻¹ := by
      rw [tsub_add_cancel_of_le]; rw [← inv_eq_iff_eq_inv]; rw [div_eq_mul_inv]; rw [ENNReal.mul_inv]; rw [inv_inv]; rw [ENNReal.mul_sub]; rw [ENNReal.inv_mul_cancel]; rw [mul_one] <;> simp [*]

中文:
引理 conjExponent
  条件: {p : 实数>=0∞} (hp : 1 <= p)
  结论: p.HolderConjugate (conjExponent p)
  证明: by
  have : p != 0 := (zero_lt_one.trans_le hp).ne'
  rw [HolderConjugate]; rw [holderTriple_iff]; rw [conjExponent]; rw [add_comm]
  refine (AddLECancellable.eq_tsub_iff_add_eq_of_le (α := Real>=0∞) (by simpa) (by simpa)).1 ?_
  rw [inv_eq_iff_eq_inv]
  obtain rfl | hp₁ := hp.eq_or_lt
  · simp
  obtain rfl | hp := eq_or_ne p ∞
  · simp
  calc
    1 + (p - 1)⁻¹ = (p - 1 + 1) / (p - 1) := by
      rw [ENNReal.add_div]; rw [ENNReal.div_self ((tsub_pos_of_lt hp₁).ne') (sub_ne_top hp)]; rw [one_div]
    _ = (1⁻¹ - p⁻¹)⁻¹ := by
      rw [tsub_add_cancel_of_le]; rw [← inv_eq_iff_eq_inv]; rw [div_eq_mul_inv]; rw [ENNReal.mul_inv]; rw [inv_inv]; rw [ENNReal.mul_sub]; rw [ENNReal.inv_mul_cancel]; rw [mul_one] <;> simp [*]
-/
protected lemma conjExponent {p : Real>=0∞} (hp : 1 <= p) : p.HolderConjugate (conjExponent p) := by
  have : p != 0 := (zero_lt_one.trans_le hp).ne'
  rw [HolderConjugate]; rw [holderTriple_iff]; rw [conjExponent]; rw [add_comm]
  refine (AddLECancellable.eq_tsub_iff_add_eq_of_le (α := Real>=0∞) (by simpa) (by simpa)).1 ?_
  rw [inv_eq_iff_eq_inv]
  obtain rfl | hp₁ := hp.eq_or_lt
  · simp
  obtain rfl | hp := eq_or_ne p ∞
  · simp
  calc
    1 + (p - 1)⁻¹ = (p - 1 + 1) / (p - 1) := by
      rw [ENNReal.add_div]; rw [ENNReal.div_self ((tsub_pos_of_lt hp₁).ne') (sub_ne_top hp)]; rw [one_div]
    _ = (1⁻¹ - p⁻¹)⁻¹ := by
      rw [tsub_add_cancel_of_le]; rw [← inv_eq_iff_eq_inv]; rw [div_eq_mul_inv]; rw [ENNReal.mul_inv]; rw [inv_inv]; rw [ENNReal.mul_sub]; rw [ENNReal.inv_mul_cancel]; rw [mul_one] <;> simp [*]

instance {p : Real>=0∞} [Fact (1 <= p)] : p.HolderConjugate (conjExponent p) := .conjExponent Fact.out

section

variable [h : HolderConjugate p q]

/--
lemma `conjExponent_eq` / 引理 `conjExponent_eq`

English:
lemma conjExponent_eq
  statement: conjExponent p = q
  proof: have : Fact (1 <= p) := ⟨one_le p q⟩
  unique p (conjExponent p) q

中文:
引理 conjExponent_eq
  结论: conjExponent p = q
  证明: have : Fact (1 <= p) := ⟨one_le p q⟩
  unique p (conjExponent p) q

Depends on / 依赖: conjExponent, one_le, unique
-/
lemma conjExponent_eq : conjExponent p = q :=
  have : Fact (1 <= p) := ⟨one_le p q⟩
  unique p (conjExponent p) q

/--
lemma `conj_eq` / 引理 `conj_eq`

English:
lemma conj_eq
  statement: q = 1 + (p - 1)⁻¹
  proof: conjExponent_eq.symm

中文:
引理 conj_eq
  结论: q = 1 + (p - 1)⁻¹
  证明: conjExponent_eq.symm

Depends on / 依赖: conjExponent_eq, conjExponent_eq.symm
-/
lemma conj_eq : q = 1 + (p - 1)⁻¹ := conjExponent_eq.symm

/--
lemma `mul_eq_add` / 引理 `mul_eq_add`

English:
lemma mul_eq_add
  statement: p * q = p + q
  proof: by
  obtain rfl | hp := eq_or_ne p ∞
  · simp [ne_zero q ∞]
  obtain rfl | hq := eq_or_ne q ∞
  · simp [ne_zero p ∞]
  simpa [add_comm p, mul_add, add_mul, hp, hq, ne_zero p q, ne_zero q p, ENNReal.mul_inv_cancel,
ENNReal.inv_mul_cancel_right] using congr(p * ((inv_add_inv_eq_one p q).symm) * q)

中文:
引理 mul_eq_add
  结论: p * q = p + q
  证明: by
  obtain rfl | hp := eq_or_ne p ∞
  · simp [ne_zero q ∞]
  obtain rfl | hq := eq_or_ne q ∞
  · simp [ne_zero p ∞]
  simpa [add_comm p, mul_add, add_mul, hp, hq, ne_zero p q, ne_zero q p, ENNReal.mul_inv_cancel,
ENNReal.inv_mul_cancel_right] using congr(p * ((inv_add_inv_eq_one p q).symm) * q)

Depends on / 依赖: ENNReal, ENNReal.inv_mul_cancel_right, ENNReal.mul_inv_cancel, add_comm, add_mul, eq_or_ne, inv_add_inv_eq_one, inv_mul_cancel_right, mul_add, mul_inv_cancel, ne_zero
-/
lemma mul_eq_add : p * q = p + q := by
  obtain rfl | hp := eq_or_ne p ∞
  · simp [ne_zero q ∞]
  obtain rfl | hq := eq_or_ne q ∞
  · simp [ne_zero p ∞]
  simpa [add_comm p, mul_add, add_mul, hp, hq, ne_zero p q, ne_zero q p, ENNReal.mul_inv_cancel,
ENNReal.inv_mul_cancel_right] using congr(p * ((inv_add_inv_eq_one p q).symm) * q)

/--
lemma `div_conj_eq_sub_one` / 引理 `div_conj_eq_sub_one`

English:
lemma div_conj_eq_sub_one
  statement: p / q = p - 1
  proof: by
  obtain rfl | hq := eq_or_ne q ∞
  · obtain rfl := unique ∞ p 1
    simp
  refine ENNReal.eq_sub_of_add_eq one_ne_top ?_
  rw [← ENNReal.div_self (ne_zero q p) hq]; rw [← ENNReal.add_div]; rw [← h.mul_eq_add]; rw [mul_div_assoc]; rw [ENNReal.div_self (ne_zero q p) hq]; rw [mul_one]

中文:
引理 div_conj_eq_sub_one
  结论: p / q = p - 1
  证明: by
  obtain rfl | hq := eq_or_ne q ∞
  · obtain rfl := unique ∞ p 1
    simp
  refine ENNReal.eq_sub_of_add_eq one_ne_top ?_
  rw [← ENNReal.div_self (ne_zero q p) hq]; rw [← ENNReal.add_div]; rw [← h.mul_eq_add]; rw [mul_div_assoc]; rw [ENNReal.div_self (ne_zero q p) hq]; rw [mul_one]

Depends on / 依赖: ENNReal, ENNReal.add_div, ENNReal.div_self, ENNReal.eq_sub_of_add_eq, add_div, div_self, eq_or_ne, eq_sub_of_add_eq, h.mul_eq_add, mul_div_assoc, mul_eq_add, mul_one, ne_zero, one_ne_top, unique
-/
lemma div_conj_eq_sub_one : p / q = p - 1 := by
  obtain rfl | hq := eq_or_ne q ∞
  · obtain rfl := unique ∞ p 1
    simp
  refine ENNReal.eq_sub_of_add_eq one_ne_top ?_
  rw [← ENNReal.div_self (ne_zero q p) hq]; rw [← ENNReal.add_div]; rw [← h.mul_eq_add]; rw [mul_div_assoc]; rw [ENNReal.div_self (ne_zero q p) hq]; rw [mul_one]

end

/--
lemma `inv_inv` / 引理 `inv_inv`

English:
lemma inv_inv
  given: (hab : a + b = 1)
  statement: a⁻¹.HolderConjugate b⁻¹ where
  proof: by simpa [inv_inv] using hab

中文:
引理 inv_inv
  条件: (hab : a + b = 1)
  结论: a⁻¹.HolderConjugate b⁻¹ where
  证明: by simpa [inv_inv] using hab
-/
protected lemma inv_inv (hab : a + b = 1) : a⁻¹.HolderConjugate b⁻¹ where
  inv_add_inv_eq_inv := by simpa [inv_inv] using hab

/--
lemma `inv_one_sub_inv` / 引理 `inv_one_sub_inv`

English:
lemma inv_one_sub_inv
  given: (ha : a <= 1)
  statement: a⁻¹.HolderConjugate (1 - a)⁻¹
  proof: .inv_inv add_tsub_cancel_of_le ha

中文:
引理 inv_one_sub_inv
  条件: (ha : a <= 1)
  结论: a⁻¹.HolderConjugate (1 - a)⁻¹
  证明: .inv_inv add_tsub_cancel_of_le ha

Depends on / 依赖: add_tsub_cancel_of_le, inv_inv
-/
lemma inv_one_sub_inv (ha : a <= 1) : a⁻¹.HolderConjugate (1 - a)⁻¹ :=
.inv_inv add_tsub_cancel_of_le ha

/--
lemma `inv_one_sub_inv'` / 引理 `inv_one_sub_inv'`

English:
lemma inv_one_sub_inv'
  given: (ha : 1 <= a)
  statement: a.HolderConjugate (1 - a⁻¹)⁻¹
  proof: by
  simpa using inv_one_sub_inv (ENNReal.inv_le_one.mpr ha)

中文:
引理 inv_one_sub_inv'
  条件: (ha : 1 <= a)
  结论: a.HolderConjugate (1 - a⁻¹)⁻¹
  证明: by
  simpa using inv_one_sub_inv (ENNReal.inv_le_one.mpr ha)

Depends on / 依赖: ENNReal, ENNReal.inv_le_one.mpr, inv_le_one, inv_one_sub_inv
-/
lemma inv_one_sub_inv' (ha : 1 <= a) : a.HolderConjugate (1 - a⁻¹)⁻¹ := by
  simpa using inv_one_sub_inv (ENNReal.inv_le_one.mpr ha)

/--
lemma `one_sub_inv_inv` / 引理 `one_sub_inv_inv`

English:
lemma one_sub_inv_inv
  given: (ha : a <= 1)
  statement: (1 - a)⁻¹.HolderConjugate a⁻¹
  proof: (inv_one_sub_inv ha).symm

中文:
引理 one_sub_inv_inv
  条件: (ha : a <= 1)
  结论: (1 - a)⁻¹.HolderConjugate a⁻¹
  证明: (inv_one_sub_inv ha).symm

Depends on / 依赖: inv_one_sub_inv
-/
lemma one_sub_inv_inv (ha : a <= 1) : (1 - a)⁻¹.HolderConjugate a⁻¹ := (inv_one_sub_inv ha).symm

/--
lemma `top_one` / 引理 `top_one`

English:
lemma top_one
  statement: HolderConjugate ∞ 1
  proof: ⟨by simp⟩

中文:
引理 top_one
  结论: HolderConjugate ∞ 1
  证明: ⟨by simp⟩
-/
lemma top_one : HolderConjugate ∞ 1 := ⟨by simp⟩
/--
lemma `one_top` / 引理 `one_top`

English:
lemma one_top
  statement: HolderConjugate 1 ∞
  proof: ⟨by simp⟩

中文:
引理 one_top
  结论: HolderConjugate 1 ∞
  证明: ⟨by simp⟩
-/
lemma one_top : HolderConjugate 1 ∞ := ⟨by simp⟩

end HolderConjugate

/--
lemma `isConjExponent_comm` / 引理 `isConjExponent_comm`

English:
lemma isConjExponent_comm
  statement: p.HolderConjugate q ↔ q.HolderConjugate p
  proof: ⟨(·.symm), (·.symm)⟩

中文:
引理 isConjExponent_comm
  结论: p.HolderConjugate q ↔ q.HolderConjugate p
  证明: ⟨(·.symm), (·.symm)⟩
-/
lemma isConjExponent_comm : p.HolderConjugate q ↔ q.HolderConjugate p := ⟨(·.symm), (·.symm)⟩

/--
lemma `isConjExponent_iff_eq_conjExponent` / 引理 `isConjExponent_iff_eq_conjExponent`

English:
lemma isConjExponent_iff_eq_conjExponent
  given: (hp : 1 <= p)
  statement: p.HolderConjugate q ↔ q = 1 + (p - 1)⁻¹
  proof: ⟨fun h => h.conj_eq, by rintro rfl; exact .conjExponent hp⟩

中文:
引理 isConjExponent_iff_eq_conjExponent
  条件: (hp : 1 <= p)
  结论: p.HolderConjugate q ↔ q = 1 + (p - 1)⁻¹
  证明: ⟨fun h => h.conj_eq, by rintro rfl; exact .conjExponent hp⟩

Depends on / 依赖: conjExponent, conj_eq, h.conj_eq
-/
lemma isConjExponent_iff_eq_conjExponent (hp : 1 <= p) : p.HolderConjugate q ↔ q = 1 + (p - 1)⁻¹ :=
  ⟨fun h => h.conj_eq, by rintro rfl; exact .conjExponent hp⟩

end ENNReal
