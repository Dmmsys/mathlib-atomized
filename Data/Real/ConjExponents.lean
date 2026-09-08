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
/-
**Real.HolderTriple** 是 Mathlib 中的一个归纳类型，位于命名空间 `Real`。
形式化陈述：ℝ → ℝ → ℝ → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Real numbers `p q r : ℝ` are said to be a **Hölder triple** if `p` and `q` are p
ositive
and `p⁻¹ + q⁻¹ = r⁻¹`.
-/
structure HolderTriple (p q r : ℝ) : Prop where
  inv_add_inv_eq_inv : p⁻¹ + q⁻¹ = r⁻¹
  left_pos : 0 < p
  right_pos : 0 < q

/-- Real numbers `p q : ℝ` are **Hölder conjugate** if they are positive and satisfy the
equality `p⁻¹ + q⁻¹ = 1`. This is an abbreviation for `Real.HolderTriple p q 1`. This condition
shows up in many theorems in analysis, notably related to `L^p` norms.

It is equivalent that `1 < p` and `p⁻¹ + q⁻¹ = 1`. See `Real.holderConjugate_iff`. -/
/-
**Real.HolderConjugate** 是 Mathlib 中的一个缩写定义，位于命名空间 `Real`。
形式化陈述：HolderConjugate (p q : Real)
参数：p q : Real。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Real numbers `p q : ℝ` are **Hölder conjugate** if they are positive and satisfy
 the
equality `p⁻¹ + q⁻¹ = 1`. This is an abbreviation for `Real.HolderTriple p q 1`.
 This condition
shows up in many theorems in analysis, notably related to `L^p` norms.

It is equivalent that `1 < p` and `p⁻¹ + q⁻¹ = 1`. See `Real.holderConjugate_iff
`.
-/
abbrev HolderConjugate (p q : ℝ) := HolderTriple p q 1

/-- The conjugate exponent of `p` is `q = p / (p-1)`, so that `p⁻¹ + q⁻¹ = 1`. -/
/-
**Real.conjExponent** 是 Mathlib 中的一个定义，位于命名空间 `Real`。
形式化陈述：conjExponent (p : Real) : Real
参数：p : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The conjugate exponent of `p` is `q = p / (p-1)`, so that `p⁻¹ + q⁻¹ = 1`.
-/
def conjExponent (p : ℝ) : ℝ := p / (p - 1)

variable {a b p q r : ℝ}

namespace HolderTriple

/-
**Real.HolderTriple.of_pos** 是 Mathlib 中的一个引理，位于命名空间 `Real.HolderTriple`。
形式化陈述：of_pos (hp : 0 < p) (hq : 0 < q) : HolderTriple p q (p⁻¹ + q⁻¹)⁻¹ where .s
ymm inv_add_inv_eq_inv
参数：hp : 0 < p；hq : 0 < q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
lemma of_pos (hp : 0 < p) (hq : 0 < q) : HolderTriple p q (p⁻¹ + q⁻¹)⁻¹ where
  inv_add_inv_eq_inv := inv_inv _ |>.symm
  left_pos := hp
  right_pos := hq

variable (h : p.HolderTriple q r)
include h

@[symm]
/-
**Real.HolderTriple.symm** 是 Mathlib 中的一个定理，位于命名空间 `Real.HolderTriple`。
形式化陈述：∀ {p q r : ℝ}, p.HolderTriple q r → q.HolderTriple p r
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.HolderTriple.inv_add_inv_eq_inv`：∀ {p q r : ℝ}, p.HolderTriple q r 
→ p⁻¹ + q⁻¹ = r⁻¹
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Real.HolderTriple.right_pos`：∀ {p q r : ℝ}, p.HolderTriple q r → 0 < q
· 使用定理 `Real.HolderTriple.left_pos`：∀ {p q r : ℝ}, p.HolderTriple q r → 0 < p
-/
protected lemma symm : q.HolderTriple p r where
  inv_add_inv_eq_inv := add_comm p⁻¹ q⁻¹ ▸ h.inv_add_inv_eq_inv
  left_pos := h.right_pos
  right_pos := h.left_pos
/-
**Real.HolderTriple.pos** 是 Mathlib 中的一个定理，位于命名空间 `Real.HolderTriple`。
形式化陈述：pos : 0 < p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.HolderTriple.left_pos`：∀ {p q r : ℝ}, p.HolderTriple q r → 0 < p
-/
theorem pos : 0 < p := h.left_pos
/-
**Real.HolderTriple.nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real.HolderTriple`。
形式化陈述：nonneg : 0 <= p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.HolderTriple.pos`：pos : 0 < p
-/
theorem nonneg : 0 ≤ p := h.pos.le
/-
**Real.HolderTriple.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real.HolderTriple`。
形式化陈述：ne_zero : p != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Real.HolderTriple.pos`：pos : 0 < p
-/
theorem ne_zero : p ≠ 0 := h.pos.ne'
/-
**Real.HolderTriple.inv_pos** 是 Mathlib 中的一个定理，位于命名空间 `Real.HolderTriple`。
形式化陈述：∀ {p q r : ℝ}, p.HolderTriple q r → 0 < p⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.HolderTriple.pos`：pos : 0 < p
-/
protected lemma inv_pos : 0 < p⁻¹ := inv_pos.2 h.pos
/-
**Real.HolderTriple.inv_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real.HolderTriple`。
形式化陈述：∀ {p q r : ℝ}, p.HolderTriple q r → 0 ≤ p⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.HolderTriple.inv_pos`：∀ {p q r : ℝ}, p.HolderTriple q r → 0 < p⁻¹
-/
protected lemma inv_nonneg : 0 ≤ p⁻¹ := h.inv_pos.le
/-
**Real.HolderTriple.inv_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real.HolderTriple`。
形式化陈述：∀ {p q r : ℝ}, p.HolderTriple q r → p⁻¹ ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Real.HolderTriple.inv_pos`：∀ {p q r : ℝ}, p.HolderTriple q r → 0 < p⁻¹
-/
protected lemma inv_ne_zero : p⁻¹ ≠ 0 := h.inv_pos.ne'
/-
**Real.HolderTriple.one_div_pos** 是 Mathlib 中的一个定理，位于命名空间 `Real.HolderTriple`。
形式化陈述：one_div_pos : 0 < 1 / p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `one_div_pos`：one_div_pos : 0 < 1 / a ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.HolderTriple.pos`：pos : 0 < p
-/
theorem one_div_pos : 0 < 1 / p := _root_.one_div_pos.2 h.pos
/-
**Real.HolderTriple.one_div_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real.HolderTriple`
。
形式化陈述：one_div_nonneg : 0 <= 1 / p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.HolderTriple.one_div_pos`：one_div_pos : 0 < 1 / p
-/
theorem one_div_nonneg : 0 ≤ 1 / p := le_of_lt h.one_div_pos
/-
**Real.HolderTriple.one_div_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real.HolderTriple
`。
形式化陈述：one_div_ne_zero : 1 / p != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Real.HolderTriple.one_div_pos`：one_div_pos : 0 < 1 / p
-/
theorem one_div_ne_zero : 1 / p ≠ 0 := ne_of_gt h.one_div_pos

/-- For `r`, instead of `p` -/
/-
**Real.HolderTriple.pos'** 是 Mathlib 中的一个定理，位于命名空间 `Real.HolderTriple`。
形式化陈述：pos' : 0 < r
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `add_pos`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder α] 
[AddLeftStrictMono α] {a b : α},   0 < a → 0 < b → 0 < a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.HolderTriple.inv_pos`：∀ {p q r : ℝ}, p.HolderTriple q r → 0 < p⁻¹
· 使用定理 `Real.HolderTriple.symm`：∀ {p q r : ℝ}, p.HolderTriple q r → q.HolderTrip
le p r
· 使用定理 `Real.HolderTriple.inv_add_inv_eq_inv`：∀ {p q r : ℝ}, p.HolderTriple q r 
→ p⁻¹ + q⁻¹ = r⁻¹

--- 原说明 ---
For `r`, instead of `p`
-/
theorem pos' : 0 < r := inv_pos.mp <| h.inv_add_inv_eq_inv ▸ add_pos h.inv_pos h.symm.inv_pos
/-- For `r`, instead of `p` -/
/-
**Real.HolderTriple.nonneg'** 是 Mathlib 中的一个定理，位于命名空间 `Real.HolderTriple`。
形式化陈述：nonneg' : 0 <= r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.HolderTriple.pos'`：pos' : 0 < r

--- 原说明 ---
For `r`, instead of `p`
-/
theorem nonneg' : 0 ≤ r := h.pos'.le
/-- For `r`, instead of `p` -/
/-
**Real.HolderTriple.ne_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Real.HolderTriple`。
形式化陈述：ne_zero' : r != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Real.HolderTriple.pos'`：pos' : 0 < r

--- 原说明 ---
For `r`, instead of `p`
-/
theorem ne_zero' : r ≠ 0 := h.pos'.ne'
/-- For `r`, instead of `p` -/
/-
**Real.HolderTriple.inv_pos'** 是 Mathlib 中的一个定理，位于命名空间 `Real.HolderTriple`。
形式化陈述：∀ {p q r : ℝ}, p.HolderTriple q r → 0 < r⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.HolderTriple.pos'`：pos' : 0 < r

--- 原说明 ---
For `r`, instead of `p`
-/
protected lemma inv_pos' : 0 < r⁻¹ := inv_pos.2 h.pos'
/-- For `r`, instead of `p` -/
/-
**Real.HolderTriple.inv_nonneg'** 是 Mathlib 中的一个定理，位于命名空间 `Real.HolderTriple`。
形式化陈述：∀ {p q r : ℝ}, p.HolderTriple q r → 0 ≤ r⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.HolderTriple.inv_pos'`：∀ {p q r : ℝ}, p.HolderTriple q r → 0 < r⁻¹

--- 原说明 ---
For `r`, instead of `p`
-/
protected lemma inv_nonneg' : 0 ≤ r⁻¹ := h.inv_pos'.le
/-- For `r`, instead of `p` -/
/-
**Real.HolderTriple.inv_ne_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Real.HolderTriple`。
形式化陈述：∀ {p q r : ℝ}, p.HolderTriple q r → r⁻¹ ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Real.HolderTriple.inv_pos'`：∀ {p q r : ℝ}, p.HolderTriple q r → 0 < r⁻¹

--- 原说明 ---
For `r`, instead of `p`
-/
protected lemma inv_ne_zero' : r⁻¹ ≠ 0 := h.inv_pos'.ne'
/-- For `r`, instead of `p` -/
/-
**Real.HolderTriple.one_div_pos'** 是 Mathlib 中的一个定理，位于命名空间 `Real.HolderTriple`。
形式化陈述：one_div_pos' : 0 < 1 / r
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `one_div_pos`：one_div_pos : 0 < 1 / a ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.HolderTriple.pos'`：pos' : 0 < r

--- 原说明 ---
For `r`, instead of `p`
-/
theorem one_div_pos' : 0 < 1 / r := _root_.one_div_pos.2 h.pos'
/-- For `r`, instead of `p` -/
/-
**Real.HolderTriple.one_div_nonneg'** 是 Mathlib 中的一个定理，位于命名空间 `Real.HolderTriple
`。
形式化陈述：one_div_nonneg' : 0 <= 1 / r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.HolderTriple.one_div_pos'`：one_div_pos' : 0 < 1 / r

--- 原说明 ---
For `r`, instead of `p`
-/
theorem one_div_nonneg' : 0 ≤ 1 / r := le_of_lt h.one_div_pos'
/-- For `r`, instead of `p` -/
/-
**Real.HolderTriple.one_div_ne_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Real.HolderTripl
e`。
形式化陈述：one_div_ne_zero' : 1 / r != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Real.HolderTriple.one_div_pos'`：one_div_pos' : 0 < 1 / r

--- 原说明 ---
For `r`, instead of `p`
-/
theorem one_div_ne_zero' : 1 / r ≠ 0 := ne_of_gt h.one_div_pos'

/-- useful for introducing all three facts simultaneously within a proof. -/
@[grind →]
/-
**Real.HolderTriple.all_pos** 是 Mathlib 中的一个定理，位于命名空间 `Real.HolderTriple`。
形式化陈述：all_pos : 0 < p ∧ 0 < q ∧ 0 < r
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.HolderTriple.pos`：pos : 0 < p
· 使用定理 `Real.HolderTriple.symm`：∀ {p q r : ℝ}, p.HolderTriple q r → q.HolderTrip
le p r
· 使用定理 `Real.HolderTriple.pos'`：pos' : 0 < r

--- 原说明 ---
useful for introducing all three facts simultaneously within a proof.
-/
theorem all_pos : 0 < p ∧ 0 < q ∧ 0 < r := ⟨h.pos, h.symm.pos, h.pos'⟩
/-
**Real.HolderTriple.inv_eq** 是 Mathlib 中的一个引理，位于命名空间 `Real.HolderTriple`。
形式化陈述：inv_eq : r⁻¹ = p⁻¹ + q⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.HolderTriple.inv_add_inv_eq_inv`：∀ {p q r : ℝ}, p.HolderTriple q r 
→ p⁻¹ + q⁻¹ = r⁻¹
-/
lemma inv_eq : r⁻¹ = p⁻¹ + q⁻¹ := h.inv_add_inv_eq_inv.symm
/-
**Real.HolderTriple.one_div_add_one_div** 是 Mathlib 中的一个引理，位于命名空间 `Real.HolderTr
iple`。
形式化陈述：one_div_add_one_div : 1 / p + 1 / q = 1 / r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Real.HolderTriple.inv_add_inv_eq_inv`：∀ {p q r : ℝ}, p.HolderTriple q r 
→ p⁻¹ + q⁻¹ = r⁻¹
-/
lemma one_div_add_one_div : 1 / p + 1 / q = 1 / r := by simpa using h.inv_add_inv_eq_inv
/-
**Real.HolderTriple.one_div_eq** 是 Mathlib 中的一个引理，位于命名空间 `Real.HolderTriple`。
形式化陈述：one_div_eq : 1 / r = 1 / p + 1 / q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Real.HolderTriple.one_div_add_one_div`：one_div_add_one_div : 1 / p + 1 /
 q = 1 / r
-/
lemma one_div_eq : 1 / r = 1 / p + 1 / q := h.one_div_add_one_div.symm
/-
**Real.HolderTriple.inv_inv_add_inv** 是 Mathlib 中的一个引理，位于命名空间 `Real.HolderTriple
`。
形式化陈述：inv_inv_add_inv : (p⁻¹ + q⁻¹)⁻¹ = r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.HolderTriple.inv_add_inv_eq_inv`：∀ {p q r : ℝ}, p.HolderTriple q r 
→ p⁻¹ + q⁻¹ = r⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inv_inv_add_inv : (p⁻¹ + q⁻¹)⁻¹ = r := by simp [h.inv_add_inv_eq_inv]
/-
**Real.HolderTriple.inv_lt_inv** 是 Mathlib 中的一个定理，位于命名空间 `Real.HolderTriple`。
形式化陈述：∀ {p q r : ℝ}, p.HolderTriple q r → p⁻¹ < r⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `add_lt_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [AddLe
ftStrictMono α] {b c : α}, b < c → ∀ (a : α), a + b < a + c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.HolderTriple.inv_pos`：∀ {p q r : ℝ}, p.HolderTriple q r → 0 < p⁻¹
· 使用定理 `Real.HolderTriple.symm`：∀ {p q r : ℝ}, p.HolderTriple q r → q.HolderTrip
le p r
· 使用定理 `Real.HolderTriple.inv_add_inv_eq_inv`：∀ {p q r : ℝ}, p.HolderTriple q r 
→ p⁻¹ + q⁻¹ = r⁻¹
-/
protected lemma inv_lt_inv : p⁻¹ < r⁻¹ := calc
  p⁻¹ = p⁻¹ + 0 := add_zero _ |>.symm
  _ < p⁻¹ + q⁻¹ := by gcongr; exact h.symm.inv_pos
  _ = r⁻¹ := h.inv_add_inv_eq_inv
/-
**Real.HolderTriple.lt** 是 Mathlib 中的一个引理，位于命名空间 `Real.HolderTriple`。
形式化陈述：lt : r < p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用引理 `inv_strictAnti₀`：inv_strictAnti₀ (hb : 0 < b) (hba : b < a) : a⁻¹ < b⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Real.HolderTriple.inv_pos`：∀ {p q r : ℝ}, p.HolderTriple q r → 0 < p⁻¹
· 使用定理 `Real.HolderTriple.inv_lt_inv`：∀ {p q r : ℝ}, p.HolderTriple q r → p⁻¹ < 
r⁻¹
-/
lemma lt : r < p := by simpa using inv_strictAnti₀ h.inv_pos h.inv_lt_inv
/-
**Real.HolderTriple.inv_sub_inv_eq_inv** 是 Mathlib 中的一个引理，位于命名空间 `Real.HolderTri
ple`。
形式化陈述：inv_sub_inv_eq_inv : r⁻¹ - q⁻¹ = p⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sub_eq_of_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a = 
c + b → a - b = c
· 使用引理 `Real.HolderTriple.inv_eq`：inv_eq : r⁻¹ = p⁻¹ + q⁻¹
-/
lemma inv_sub_inv_eq_inv : r⁻¹ - q⁻¹ = p⁻¹ := sub_eq_of_eq_add h.inv_eq
/-
**Real.HolderTriple.holderConjugate_div_div** 是 Mathlib 中的一个引理，位于命名空间 `Real.Hold
erTriple`。
形式化陈述：holderConjugate_div_div : (p / r).HolderConjugate (q / r) where inv_add_in
v_eq_inv
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Real.HolderTriple.inv_add_inv_eq_inv`：∀ {p q r : ℝ}, p.HolderTriple q r 
→ p⁻¹ + q⁻¹ = r⁻¹
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Real.HolderTriple.ne_zero'`：ne_zero' : r != 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Real.HolderTriple.left_pos`：∀ {p q r : ℝ}, p.HolderTriple q r → 0 < p
· 使用定理 `Real.HolderTriple.pos'`：pos' : 0 < r
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.HolderTriple.right_pos`：∀ {p q r : ℝ}, p.HolderTriple q r → 0 < q
-/
lemma holderConjugate_div_div : (p / r).HolderConjugate (q / r) where
  inv_add_inv_eq_inv := by
    simp [div_eq_mul_inv, ← mul_add, h.inv_add_inv_eq_inv, h.ne_zero']
  left_pos := by have := h.left_pos; have := h.pos'; positivity
  right_pos := by have := h.right_pos; have := h.pos'; positivity

end HolderTriple

namespace HolderConjugate

/-
**Real.HolderConjugate.two_two** 是 Mathlib 中的一个引理，位于命名空间 `Real.HolderConjugate`。
形式化陈述：two_two : HolderConjugate 2 2 where inv_add_inv_eq_inv
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_true`：∀ {α : Type u} [inst : AddMonoidWith
One α] {a b : α} {c : ℕ},   Mathlib.Meta.NormNum.IsNat a c → Mathlib.Meta.NormNu
m.IsNat b c → a = b
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isNat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n 1 → Mathlib.Meta.NormNum
.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_add`：isNNRat_add {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HAdd.hAdd -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
lemma two_two : HolderConjugate 2 2 where
  inv_add_inv_eq_inv := by norm_num
  left_pos := zero_lt_two
  right_pos := zero_lt_two

section
variable (h : p.HolderConjugate q)
include h

@[symm]
/-
**Real.HolderConjugate.symm** 是 Mathlib 中的一个定理，位于命名空间 `Real.HolderConjugate`。
形式化陈述：∀ {p q : ℝ}, p.HolderConjugate q → q.HolderConjugate p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.HolderTriple.symm`：∀ {p q r : ℝ}, p.HolderTriple q r → q.HolderTrip
le p r
-/
protected lemma symm : q.HolderConjugate p := HolderTriple.symm h
/-
**Real.HolderConjugate.inv_add_inv_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Real.Holder
Conjugate`。
形式化陈述：inv_add_inv_eq_one : p⁻¹ + q⁻¹ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.HolderTriple.inv_add_inv_eq_inv`：∀ {p q r : ℝ}, p.HolderTriple q r 
→ p⁻¹ + q⁻¹ = r⁻¹
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
-/
theorem inv_add_inv_eq_one : p⁻¹ + q⁻¹ = 1 := inv_one (G := ℝ) ▸ h.inv_add_inv_eq_inv
/-
**Real.HolderConjugate.sub_one_pos** 是 Mathlib 中的一个定理，位于命名空间 `Real.HolderConjuga
te`。
形式化陈述：sub_one_pos : 0 < p - 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `Real.HolderTriple.lt`：lt : r < p
-/
theorem sub_one_pos : 0 < p - 1 := sub_pos.2 h.lt
/-
**Real.HolderConjugate.sub_one_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real.HolderCon
jugate`。
形式化陈述：sub_one_ne_zero : p - 1 != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Real.HolderConjugate.sub_one_pos`：sub_one_pos : 0 < p - 1
-/
theorem sub_one_ne_zero : p - 1 ≠ 0 := h.sub_one_pos.ne'
/-
**Real.HolderConjugate.conjugate_eq** 是 Mathlib 中的一个定理，位于命名空间 `Real.HolderConjug
ate`。
形式化陈述：conjugate_eq : q = p / (p - 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_sub`：subst_sub {M : Type*} [Ring M] {x₁ x
₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ - X₂ = Y) 
(hy : a * Y = y) : x₁ - …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_eq_eval`：one_eq_eval [GroupWithZero M] :
 (1:M) = NF.eval (M
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₃`：div_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval / l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval`：eval_cons_mul_eval [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : ((n, e) ::ᵣ L).eval * l.eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_subst`：eq_div_of_subst {M : Type*} [D
iv M] {l l_n l_d n d : M} (h : l = l_n / l_d) (hn : l_n = n) (hd : l_d = d) : l 
= n / d
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div'`：cons_eq_div_of_eq_di
v' [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.
eval / t_d.eval) : ((-n, e) ::ᵣ t).eval …
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.inv_eq_eval`：inv_eq_eval [CommGroupWithZero 
M] {l : NF M} {x : M} (h : x = l.eval) : x⁻¹ = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval_cons_neg`：eval_cons_mul_e
val_cons_neg [CommGroupWithZero M] (n : Int) {e : M} (he : e != 0) {L l l' : NF 
M} (h : L.eval * l.eval = l'.eval) : ((n, e) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Real.HolderTriple.ne_zero`：ne_zero : p != 0
（共 64 条，此处仅展示前 30 条）
-/
theorem conjugate_eq : q = p / (p - 1) := by
  convert! inv_inv q ▸ congr($(h.symm.inv_sub_inv_eq_inv.symm)⁻¹) using 1
  field [h.ne_zero]
/-
**Real.HolderConjugate.conjExponent_eq** 是 Mathlib 中的一个引理，位于命名空间 `Real.HolderCon
jugate`。
形式化陈述：conjExponent_eq : conjExponent p = q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.HolderConjugate.conjugate_eq`：conjugate_eq : q = p / (p - 1)
-/
lemma conjExponent_eq : conjExponent p = q := h.conjugate_eq.symm
/-
**Real.HolderConjugate.one_sub_inv** 是 Mathlib 中的一个引理，位于命名空间 `Real.HolderConjuga
te`。
形式化陈述：one_sub_inv : 1 - p⁻¹ = q⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sub_eq_of_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a = 
c + b → a - b = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.HolderConjugate.inv_add_inv_eq_one`：inv_add_inv_eq_one : p⁻¹ + q⁻¹ 
= 1
· 使用定理 `Real.HolderConjugate.symm`：∀ {p q : ℝ}, p.HolderConjugate q → q.HolderCo
njugate p
-/
lemma one_sub_inv : 1 - p⁻¹ = q⁻¹ := sub_eq_of_eq_add h.symm.inv_add_inv_eq_one.symm
/-
**Real.HolderConjugate.inv_sub_one** 是 Mathlib 中的一个引理，位于命名空间 `Real.HolderConjuga
te`。
形式化陈述：inv_sub_one : p⁻¹ - 1 = -q⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用引理 `Real.HolderConjugate.one_sub_inv`：one_sub_inv : 1 - p⁻¹ = q⁻¹
-/
lemma inv_sub_one : p⁻¹ - 1 = -q⁻¹ := by simpa using congr(-$(h.one_sub_inv))
/-
**Real.HolderConjugate.sub_one_mul_conj** 是 Mathlib 中的一个定理，位于命名空间 `Real.HolderCo
njugate`。
形式化陈述：sub_one_mul_conj : (p - 1) * q = p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `eq_div_iff`：eq_div_iff (hb : b != 0) : c = a / b ↔ c * b = a
· 使用定理 `Real.HolderConjugate.sub_one_ne_zero`：sub_one_ne_zero : p - 1 != 0
· 使用定理 `Real.HolderConjugate.conjugate_eq`：conjugate_eq : q = p / (p - 1)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem sub_one_mul_conj : (p - 1) * q = p :=
  mul_comm q (p - 1) ▸ (eq_div_iff h.sub_one_ne_zero).1 h.conjugate_eq
/-
**Real.HolderConjugate.mul_eq_add** 是 Mathlib 中的一个定理，位于命名空间 `Real.HolderConjugat
e`。
形式化陈述：mul_eq_add : p * q = p + q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Real.HolderConjugate.sub_one_mul_conj`：sub_one_mul_conj : (p - 1) * q = 
p
-/
theorem mul_eq_add : p * q = p + q := by
  simpa only [sub_mul, sub_eq_iff_eq_add, one_mul] using h.sub_one_mul_conj
/-
**Real.HolderConjugate.div_conj_eq_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `Real.Holde
rConjugate`。
形式化陈述：div_conj_eq_sub_one : p / q = p - 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₃`：div_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval / l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval`：eval_cons_mul_eval [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : ((n, e) ::ᵣ L).eval * l.eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_sub`：subst_sub {M : Type*} [Ring M] {x₁ x
₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ - X₂ = Y) 
(hy : a * Y = y) : x₁ - …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_eq_eval`：one_eq_eval [GroupWithZero M] :
 (1:M) = NF.eval (M
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval_cons_neg`：eval_cons_mul_e
val_cons_neg [CommGroupWithZero M] (n : Int) {e : M} (he : e != 0) {L l l' : NF 
M} (h : L.eval * l.eval = l'.eval) : ((n, e) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Real.HolderTriple.ne_zero`：ne_zero : p != 0
· 使用定理 `Real.HolderConjugate.symm`：∀ {p q : ℝ}, p.HolderConjugate q → q.HolderCo
njugate p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_ne_zero`：cons_ne_zero [GroupWithZero M]
 (r : Int) {x : M} (hx : x != 0) {l : NF M} (hl : l.eval != 0) : ((r, x) ::ᵣ l).
eval != 0
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
（共 74 条，此处仅展示前 30 条）
-/
theorem div_conj_eq_sub_one : p / q = p - 1 := by
  field_simp [h.symm.ne_zero]
  linear_combination -h.sub_one_mul_conj
/-
**Real.HolderConjugate.inv_add_inv_ennreal** 是 Mathlib 中的一个定理，位于命名空间 `Real.Holde
rConjugate`。
形式化陈述：inv_add_inv_ennreal : (ENNReal.ofReal p)⁻¹ + (ENNReal.ofReal q)⁻¹ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofReal_one`：ENNReal.ofReal 1 = 1
· 使用定理 `ENNReal.ofReal_inv_of_pos`：ofReal_inv_of_pos {x : Real} (hx : 0 < x) : E
NNReal.ofReal x⁻¹ = (ENNReal.ofReal x)⁻¹
· 使用定理 `Real.HolderTriple.pos`：pos : 0 < p
· 使用定理 `Real.HolderConjugate.symm`：∀ {p q : ℝ}, p.HolderConjugate q → q.HolderCo
njugate p
· 使用定理 `ENNReal.ofReal_add`：ofReal_add {p q : Real} (hp : 0 <= p) (hq : 0 <= q) 
: ENNReal.ofReal (p + q) = ENNReal.ofReal p + ENNReal.ofReal q
· 使用定理 `Real.HolderTriple.inv_nonneg`：∀ {p q r : ℝ}, p.HolderTriple q r → 0 ≤ p⁻
¹
· 使用定理 `Real.HolderConjugate.inv_add_inv_eq_one`：inv_add_inv_eq_one : p⁻¹ + q⁻¹ 
= 1
-/
theorem inv_add_inv_ennreal : (ENNReal.ofReal p)⁻¹ + (ENNReal.ofReal q)⁻¹ = 1 := by
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_inv_of_pos h.pos,
    ← ENNReal.ofReal_inv_of_pos h.symm.pos, ← ENNReal.ofReal_add h.inv_nonneg h.symm.inv_nonneg,
    h.inv_add_inv_eq_one]

end

/-
**Real.HolderConjugate._root_.Real.holderConjugate_iff** 是 Mathlib 中的一个引理，位于命名空间
 `Real.HolderConjugate`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Real.holderConjugate_iff : p.HolderConjugate q ↔ 1 < p ∧ p⁻¹ + q⁻¹ = 1 := by
  refine ⟨fun h ↦ ⟨h.lt, h.inv_add_inv_eq_one⟩, ?_⟩
  rintro ⟨hp, h⟩
  have hp' := zero_lt_one.trans hp
  refine ⟨inv_one (G := ℝ) |>.symm ▸ h, hp', ?_⟩
  rw [← inv_lt_one₀ hp', ← sub_pos] at hp
  exact inv_pos.mp <| eq_sub_of_add_eq' h ▸ hp
/-
**Real.HolderConjugate.inv_inv** 是 Mathlib 中的一个定理，位于命名空间 `Real.HolderConjugate`。
形式化陈述：∀ {a b : ℝ}, 0 < a → 0 < b → a + b = 1 → a⁻¹.HolderConjugate b⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
-/
protected lemma inv_inv (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) : a⁻¹.HolderConjugate b⁻¹ where
  inv_add_inv_eq_inv := by simpa using hab
  left_pos := inv_pos.mpr ha
  right_pos := inv_pos.mpr hb
/-
**Real.HolderConjugate.inv_one_sub_inv** 是 Mathlib 中的一个引理，位于命名空间 `Real.HolderCon
jugate`。
形式化陈述：inv_one_sub_inv (ha₀ : 0 < a) (ha₁ : a < 1) : a⁻¹.HolderConjugate (1 - a)⁻
¹
参数：ha₀ : 0 < a；ha₁ : a < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.holderConjugate_iff`：∀ {p q : ℝ}, p.HolderConjugate q ↔ 1 < p ∧ p⁻¹
 + q⁻¹ = 1
· 使用引理 `one_lt_inv₀`：one_lt_inv₀ (ha : 0 < a) : 1 < a⁻¹ ↔ a < 1
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inv_one_sub_inv (ha₀ : 0 < a) (ha₁ : a < 1) : a⁻¹.HolderConjugate (1 - a)⁻¹ :=
  holderConjugate_iff.mpr ⟨one_lt_inv₀ ha₀ |>.mpr ha₁, by simp⟩
/-
**Real.HolderConjugate.one_sub_inv_inv** 是 Mathlib 中的一个引理，位于命名空间 `Real.HolderCon
jugate`。
形式化陈述：one_sub_inv_inv (ha₀ : 0 < a) (ha₁ : a < 1) : (1 - a)⁻¹.HolderConjugate a⁻
¹
参数：ha₀ : 0 < a；ha₁ : a < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.HolderConjugate.symm`：∀ {p q : ℝ}, p.HolderConjugate q → q.HolderCo
njugate p
· 使用引理 `Real.HolderConjugate.inv_one_sub_inv`：inv_one_sub_inv (ha₀ : 0 < a) (ha₁
 : a < 1) : a⁻¹.HolderConjugate (1 - a)⁻¹
-/
lemma one_sub_inv_inv (ha₀ : 0 < a) (ha₁ : a < 1) : (1 - a)⁻¹.HolderConjugate a⁻¹ :=
  (inv_one_sub_inv ha₀ ha₁).symm

end HolderConjugate

/-
**Real.holderConjugate_comm** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：holderConjugate_comm : p.HolderConjugate q ↔ q.HolderConjugate p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.HolderConjugate.symm`：∀ {p q : ℝ}, p.HolderConjugate q → q.HolderCo
njugate p
-/
lemma holderConjugate_comm : p.HolderConjugate q ↔ q.HolderConjugate p := ⟨.symm, .symm⟩
/-
**Real.holderConjugate_iff_eq_conjExponent** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：holderConjugate_iff_eq_conjExponent (hp : 1 < p) : p.HolderConjugate q ↔ q
 = p / (p - 1)
参数：hp : 1 < p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.HolderConjugate.conjugate_eq`：conjugate_eq : q = p / (p - 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.holderConjugate_iff`：∀ {p q : ℝ}, p.HolderConjugate q ↔ 1 < p ∧ p⁻¹
 + q⁻¹ = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_add`：subst_add {M : Type*} [Semiring M] {
x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ =
 Y) (hy : a * Y = y) : x…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.inv_eq_eval`：inv_eq_eval [CommGroupWithZero 
M] {l : NF M} {x : M} (h : x = l.eval) : x⁻¹ = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval`：eval_cons_mul_eval [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : ((n, e) ::ᵣ L).eval * l.eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_sub`：subst_sub {M : Type*} [Ring M] {x₁ x
₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ - X₂ = Y) 
(hy : a * Y = y) : x₁ - …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_eq_eval`：one_eq_eval [GroupWithZero M] :
 (1:M) = NF.eval (M
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₁`：div_eq_eval₁ [CommGroupWithZer
o M] (a₁ : Int × M) {a₂ : Int × M} {l₁ l₂ l : NF M} (h : l₁.eval / (a₂ ::ᵣ l₂).e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
（共 44 条，此处仅展示前 30 条）
-/
lemma holderConjugate_iff_eq_conjExponent (hp : 1 < p) : p.HolderConjugate q ↔ q = p / (p - 1) :=
  ⟨HolderConjugate.conjugate_eq, fun h ↦ holderConjugate_iff.mpr ⟨hp, by simp [field, h]⟩⟩
/-
**Real.HolderConjugate.conjExponent** 是 Mathlib 中的一个定理，位于命名空间 `Real.HolderConjug
ate`。
形式化陈述：∀ {p : ℝ}, 1 < p → p.HolderConjugate p.conjExponent
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Real.holderConjugate_iff_eq_conjExponent`：holderConjugate_iff_eq_conjExp
onent (hp : 1 < p) : p.HolderConjugate q ↔ q = p / (p - 1)
-/
lemma HolderConjugate.conjExponent (h : 1 < p) : p.HolderConjugate (conjExponent p) :=
  (holderConjugate_iff_eq_conjExponent h).2 rfl
/-
**Real.holderConjugate_one_div** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：holderConjugate_one_div (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) : (1 /
 a).HolderConjugate (1 / b)
参数：ha : 0 < a；hb : 0 < b；hab : a + b = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Real.HolderConjugate.inv_inv`：∀ {a b : ℝ}, 0 < a → 0 < b → a + b = 1 → a
⁻¹.HolderConjugate b⁻¹
-/
lemma holderConjugate_one_div (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    (1 / a).HolderConjugate (1 / b) := by simpa using HolderConjugate.inv_inv ha hb hab

end Real

namespace NNReal

/-- Nonnegative real numbers `p q r : ℝ≥0` are said to be a **Hölder triple** if `p` and `q` are
positive and `p⁻¹ + q⁻¹ = r⁻¹`. -/
@[mk_iff]
/-
**NNReal.HolderTriple** 是 Mathlib 中的一个归纳类型，位于命名空间 `NNReal`。
形式化陈述：NNReal → NNReal → NNReal → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Nonnegative real numbers `p q r : ℝ≥0` are said to be a **Hölder triple** if `p`
 and `q` are
positive and `p⁻¹ + q⁻¹ = r⁻¹`.
-/
structure HolderTriple (p q r : ℝ≥0) : Prop where
  inv_add_inv_eq_inv : p⁻¹ + q⁻¹ = r⁻¹
  left_pos : 0 < p
  right_pos : 0 < q

/-- Nonnegative real numbers `p q : ℝ≥0` are **Hölder conjugate** if they are positive and satisfy
the equality `p⁻¹ + q⁻¹ = 1`. This is an abbreviation for `NNReal.HolderTriple p q 1`. This
condition shows up in many theorems in analysis, notably related to `L^p` norms.

It is equivalent that `1 < p` and `p⁻¹ + q⁻¹ = 1`. See `NNReal.holderConjugate_iff`. -/
/-
**NNReal.HolderConjugate** 是 Mathlib 中的一个缩写定义，位于命名空间 `NNReal`。
形式化陈述：HolderConjugate (p q : Real>=0)
参数：p q : Real>=0。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Nonnegative real numbers `p q : ℝ≥0` are **Hölder conjugate** if they are positi
ve and satisfy
the equality `p⁻¹ + q⁻¹ = 1`. This is an abbreviation for `NNReal.HolderTriple p
 q 1`. This
condition shows up in many theorems in analysis, notably related to `L^p` norms.

It is equivalent that `1 < p` and `p⁻¹ + q⁻¹ = 1`. See `NNReal.holderConjugate_i
ff`.
-/
abbrev HolderConjugate (p q : ℝ≥0) := HolderTriple p q 1

/-- The conjugate exponent of `p` is `q = p/(p-1)`, so that `p⁻¹ + q⁻¹ = 1`. -/
/-
**NNReal.conjExponent** 是 Mathlib 中的一个定义，位于命名空间 `NNReal`。
形式化陈述：conjExponent (p : Real>=0) : Real>=0
参数：p : Real>=0。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The conjugate exponent of `p` is `q = p/(p-1)`, so that `p⁻¹ + q⁻¹ = 1`.
-/
def conjExponent (p : ℝ≥0) : ℝ≥0 := p / (p - 1)

@[simp, norm_cast]
/-
**NNReal.holderTriple_coe_iff** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：holderTriple_coe_iff {p q r : Real>=0} : Real.HolderTriple (p : Real) (q :
 Real) (r : Real) ↔ HolderTriple p q r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.holderTriple_iff`：∀ (p q r : ℝ), p.HolderTriple q r ↔ p⁻¹ + q⁻¹ = r
⁻¹ ∧ 0 < p ∧ 0 < q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `NNReal.holderTriple_iff`：∀ (p q r : NNReal), p.HolderTriple q r ↔ p⁻¹ + 
q⁻¹ = r⁻¹ ∧ 0 < p ∧ 0 < q
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma holderTriple_coe_iff {p q r : ℝ≥0} :
    Real.HolderTriple (p : ℝ) (q : ℝ) (r : ℝ) ↔ HolderTriple p q r := by
  rw_mod_cast [Real.holderTriple_iff, holderTriple_iff]

alias ⟨_, HolderTriple.coe⟩ := holderTriple_coe_iff

@[simp, norm_cast]
/-
**NNReal.holderConjugate_coe_iff** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：holderConjugate_coe_iff {p q : Real>=0} : Real.HolderConjugate (p : Real) 
(q : Real) ↔ HolderConjugate p q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NNReal.holderTriple_coe_iff`：holderTriple_coe_iff {p q r : Real>=0} : Re
al.HolderTriple (p : Real) (q : Real) (r : Real) ↔ HolderTriple p q r
-/
lemma holderConjugate_coe_iff {p q : ℝ≥0} :
    Real.HolderConjugate (p : ℝ) (q : ℝ) ↔ HolderConjugate p q :=
  holderTriple_coe_iff (r := 1)

alias ⟨_, HolderConjugate.coe⟩ := holderConjugate_coe_iff

variable {a b p q r : ℝ≥0}

namespace HolderTriple

/-
**NNReal.HolderTriple.of_pos** 是 Mathlib 中的一个引理，位于命名空间 `NNReal.HolderTriple`。
形式化陈述：of_pos (hp : 0 < p) (hq : 0 < q) : HolderTriple p q (p⁻¹ + q⁻¹)⁻¹ where .s
ymm inv_add_inv_eq_inv
参数：hp : 0 < p；hq : 0 < q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
lemma of_pos (hp : 0 < p) (hq : 0 < q) : HolderTriple p q (p⁻¹ + q⁻¹)⁻¹ where
  inv_add_inv_eq_inv := inv_inv _ |>.symm
  left_pos := hp
  right_pos := hq

variable (h : p.HolderTriple q r)
include h

@[symm]
/-
**NNReal.HolderTriple.symm** 是 Mathlib 中的一个定理，位于命名空间 `NNReal.HolderTriple`。
形式化陈述：∀ {p q r : NNReal}, p.HolderTriple q r → q.HolderTriple p r
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.HolderTriple.inv_add_inv_eq_inv`：∀ {p q r : NNReal}, p.HolderTrip
le q r → p⁻¹ + q⁻¹ = r⁻¹
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `NNReal.HolderTriple.right_pos`：∀ {p q r : NNReal}, p.HolderTriple q r → 
0 < q
· 使用定理 `NNReal.HolderTriple.left_pos`：∀ {p q r : NNReal}, p.HolderTriple q r → 0
 < p
-/
protected lemma symm : q.HolderTriple p r where
  inv_add_inv_eq_inv := add_comm p⁻¹ q⁻¹ ▸ h.inv_add_inv_eq_inv
  left_pos := h.right_pos
  right_pos := h.left_pos
/-
**NNReal.HolderTriple.pos** 是 Mathlib 中的一个定理，位于命名空间 `NNReal.HolderTriple`。
形式化陈述：pos : 0 < p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.HolderTriple.left_pos`：∀ {p q r : NNReal}, p.HolderTriple q r → 0
 < p
-/
theorem pos : 0 < p := h.left_pos
/-
**NNReal.HolderTriple.nonneg** 是 Mathlib 中的一个定理，位于命名空间 `NNReal.HolderTriple`。
形式化陈述：nonneg : 0 <= p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `NNReal.HolderTriple.pos`：pos : 0 < p
-/
theorem nonneg : 0 ≤ p := h.pos.le
/-
**NNReal.HolderTriple.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `NNReal.HolderTriple`。
形式化陈述：ne_zero : p != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `NNReal.HolderTriple.pos`：pos : 0 < p
-/
theorem ne_zero : p ≠ 0 := h.pos.ne'
/-
**NNReal.HolderTriple.inv_pos** 是 Mathlib 中的一个定理，位于命名空间 `NNReal.HolderTriple`。
形式化陈述：∀ {p q r : NNReal}, p.HolderTriple q r → 0 < p⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `NNReal.HolderTriple.pos`：pos : 0 < p
-/
protected lemma inv_pos : 0 < p⁻¹ := inv_pos.2 h.pos
/-
**NNReal.HolderTriple.inv_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `NNReal.HolderTriple`
。
形式化陈述：∀ {p q r : NNReal}, p.HolderTriple q r → 0 ≤ p⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `NNReal.HolderTriple.inv_pos`：∀ {p q r : NNReal}, p.HolderTriple q r → 0 
< p⁻¹
-/
protected lemma inv_nonneg : 0 ≤ p⁻¹ := h.inv_pos.le
/-
**NNReal.HolderTriple.inv_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `NNReal.HolderTriple
`。
形式化陈述：∀ {p q r : NNReal}, p.HolderTriple q r → p⁻¹ ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `NNReal.HolderTriple.inv_pos`：∀ {p q r : NNReal}, p.HolderTriple q r → 0 
< p⁻¹
-/
protected lemma inv_ne_zero : p⁻¹ ≠ 0 := h.inv_pos.ne'
/-
**NNReal.HolderTriple.one_div_pos** 是 Mathlib 中的一个定理，位于命名空间 `NNReal.HolderTriple
`。
形式化陈述：one_div_pos : 0 < 1 / p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `one_div_pos`：one_div_pos : 0 < 1 / a ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `NNReal.HolderTriple.pos`：pos : 0 < p
-/
theorem one_div_pos : 0 < 1 / p := _root_.one_div_pos.2 h.pos
/-
**NNReal.HolderTriple.one_div_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `NNReal.HolderTri
ple`。
形式化陈述：one_div_nonneg : 0 <= 1 / p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `NNReal.HolderTriple.one_div_pos`：one_div_pos : 0 < 1 / p
-/
theorem one_div_nonneg : 0 ≤ 1 / p := le_of_lt h.one_div_pos
/-
**NNReal.HolderTriple.one_div_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `NNReal.HolderTr
iple`。
形式化陈述：one_div_ne_zero : 1 / p != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `NNReal.HolderTriple.one_div_pos`：one_div_pos : 0 < 1 / p
-/
theorem one_div_ne_zero : 1 / p ≠ 0 := ne_of_gt h.one_div_pos

/-- For `r`, instead of `p` -/
/-
**NNReal.HolderTriple.pos'** 是 Mathlib 中的一个定理，位于命名空间 `NNReal.HolderTriple`。
形式化陈述：pos' : 0 < r
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `add_pos`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder α] 
[AddLeftStrictMono α] {a b : α},   0 < a → 0 < b → 0 < a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `NNReal.HolderTriple.inv_pos`：∀ {p q r : NNReal}, p.HolderTriple q r → 0 
< p⁻¹
· 使用定理 `NNReal.HolderTriple.symm`：∀ {p q r : NNReal}, p.HolderTriple q r → q.Hol
derTriple p r
· 使用定理 `NNReal.HolderTriple.inv_add_inv_eq_inv`：∀ {p q r : NNReal}, p.HolderTrip
le q r → p⁻¹ + q⁻¹ = r⁻¹

--- 原说明 ---
For `r`, instead of `p`
-/
theorem pos' : 0 < r := inv_pos.mp <| h.inv_add_inv_eq_inv ▸ add_pos h.inv_pos h.symm.inv_pos
/-- For `r`, instead of `p` -/
/-
**NNReal.HolderTriple.nonneg'** 是 Mathlib 中的一个定理，位于命名空间 `NNReal.HolderTriple`。
形式化陈述：nonneg' : 0 <= r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `NNReal.HolderTriple.pos'`：pos' : 0 < r

--- 原说明 ---
For `r`, instead of `p`
-/
theorem nonneg' : 0 ≤ r := h.pos'.le
/-- For `r`, instead of `p` -/
/-
**NNReal.HolderTriple.ne_zero'** 是 Mathlib 中的一个定理，位于命名空间 `NNReal.HolderTriple`。
形式化陈述：ne_zero' : r != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `NNReal.HolderTriple.pos'`：pos' : 0 < r

--- 原说明 ---
For `r`, instead of `p`
-/
theorem ne_zero' : r ≠ 0 := h.pos'.ne'
/-- For `r`, instead of `p` -/
/-
**NNReal.HolderTriple.inv_pos'** 是 Mathlib 中的一个定理，位于命名空间 `NNReal.HolderTriple`。
形式化陈述：∀ {p q r : NNReal}, p.HolderTriple q r → 0 < r⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `NNReal.HolderTriple.pos'`：pos' : 0 < r

--- 原说明 ---
For `r`, instead of `p`
-/
protected lemma inv_pos' : 0 < r⁻¹ := inv_pos.2 h.pos'
/-- For `r`, instead of `p` -/
/-
**NNReal.HolderTriple.inv_nonneg'** 是 Mathlib 中的一个定理，位于命名空间 `NNReal.HolderTriple
`。
形式化陈述：∀ {p q r : NNReal}, p.HolderTriple q r → 0 ≤ r⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `NNReal.HolderTriple.inv_pos'`：∀ {p q r : NNReal}, p.HolderTriple q r → 0
 < r⁻¹

--- 原说明 ---
For `r`, instead of `p`
-/
protected lemma inv_nonneg' : 0 ≤ r⁻¹ := h.inv_pos'.le
/-- For `r`, instead of `p` -/
/-
**NNReal.HolderTriple.inv_ne_zero'** 是 Mathlib 中的一个定理，位于命名空间 `NNReal.HolderTripl
e`。
形式化陈述：∀ {p q r : NNReal}, p.HolderTriple q r → r⁻¹ ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `NNReal.HolderTriple.inv_pos'`：∀ {p q r : NNReal}, p.HolderTriple q r → 0
 < r⁻¹

--- 原说明 ---
For `r`, instead of `p`
-/
protected lemma inv_ne_zero' : r⁻¹ ≠ 0 := h.inv_pos'.ne'
/-- For `r`, instead of `p` -/
/-
**NNReal.HolderTriple.one_div_pos'** 是 Mathlib 中的一个定理，位于命名空间 `NNReal.HolderTripl
e`。
形式化陈述：one_div_pos' : 0 < 1 / r
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `one_div_pos`：one_div_pos : 0 < 1 / a ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `NNReal.HolderTriple.pos'`：pos' : 0 < r

--- 原说明 ---
For `r`, instead of `p`
-/
theorem one_div_pos' : 0 < 1 / r := _root_.one_div_pos.2 h.pos'
/-- For `r`, instead of `p` -/
/-
**NNReal.HolderTriple.one_div_nonneg'** 是 Mathlib 中的一个定理，位于命名空间 `NNReal.HolderTr
iple`。
形式化陈述：one_div_nonneg' : 0 <= 1 / r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `NNReal.HolderTriple.one_div_pos'`：one_div_pos' : 0 < 1 / r

--- 原说明 ---
For `r`, instead of `p`
-/
theorem one_div_nonneg' : 0 ≤ 1 / r := le_of_lt h.one_div_pos'
/-- For `r`, instead of `p` -/
/-
**NNReal.HolderTriple.one_div_ne_zero'** 是 Mathlib 中的一个定理，位于命名空间 `NNReal.HolderT
riple`。
形式化陈述：one_div_ne_zero' : 1 / r != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `NNReal.HolderTriple.one_div_pos'`：one_div_pos' : 0 < 1 / r

--- 原说明 ---
For `r`, instead of `p`
-/
theorem one_div_ne_zero' : 1 / r ≠ 0 := ne_of_gt h.one_div_pos'

/-- useful for introducing all three facts simultaneously within a proof. -/
@[grind →]
/-
**NNReal.HolderTriple.all_pos** 是 Mathlib 中的一个定理，位于命名空间 `NNReal.HolderTriple`。
形式化陈述：all_pos : 0 < p ∧ 0 < q ∧ 0 < r
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.HolderTriple.pos`：pos : 0 < p
· 使用定理 `NNReal.HolderTriple.symm`：∀ {p q r : NNReal}, p.HolderTriple q r → q.Hol
derTriple p r
· 使用定理 `NNReal.HolderTriple.pos'`：pos' : 0 < r

--- 原说明 ---
useful for introducing all three facts simultaneously within a proof.
-/
theorem all_pos : 0 < p ∧ 0 < q ∧ 0 < r := ⟨h.pos, h.symm.pos, h.pos'⟩
/-
**NNReal.HolderTriple.inv_eq** 是 Mathlib 中的一个引理，位于命名空间 `NNReal.HolderTriple`。
形式化陈述：inv_eq : r⁻¹ = p⁻¹ + q⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.HolderTriple.inv_add_inv_eq_inv`：∀ {p q r : NNReal}, p.HolderTrip
le q r → p⁻¹ + q⁻¹ = r⁻¹
-/
lemma inv_eq : r⁻¹ = p⁻¹ + q⁻¹ := h.inv_add_inv_eq_inv.symm
/-
**NNReal.HolderTriple.one_div_add_one_div** 是 Mathlib 中的一个引理，位于命名空间 `NNReal.Hold
erTriple`。
形式化陈述：one_div_add_one_div : 1 / p + 1 / q = 1 / r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `Real.HolderTriple.one_div_add_one_div`：one_div_add_one_div : 1 / p + 1 /
 q = 1 / r
· 使用定理 `NNReal.HolderTriple.coe`：∀ {p q r : NNReal}, p.HolderTriple q r → (↑p).H
olderTriple ↑q ↑r
-/
lemma one_div_add_one_div : 1 / p + 1 / q = 1 / r := by exact_mod_cast h.coe.one_div_add_one_div
/-
**NNReal.HolderTriple.one_div_eq** 是 Mathlib 中的一个引理，位于命名空间 `NNReal.HolderTriple`
。
形式化陈述：one_div_eq : 1 / r = 1 / p + 1 / q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `NNReal.HolderTriple.one_div_add_one_div`：one_div_add_one_div : 1 / p + 1
 / q = 1 / r
-/
lemma one_div_eq : 1 / r = 1 / p + 1 / q := h.one_div_add_one_div.symm
/-
**NNReal.HolderTriple.inv_inv_add_inv** 是 Mathlib 中的一个引理，位于命名空间 `NNReal.HolderTr
iple`。
形式化陈述：inv_inv_add_inv : (p⁻¹ + q⁻¹)⁻¹ = r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.HolderTriple.inv_inv_add_inv`：inv_inv_add_inv : (p⁻¹ + q⁻¹)⁻¹ = r
· 使用定理 `NNReal.HolderTriple.coe`：∀ {p q r : NNReal}, p.HolderTriple q r → (↑p).H
olderTriple ↑q ↑r
-/
lemma inv_inv_add_inv : (p⁻¹ + q⁻¹)⁻¹ = r := by exact_mod_cast h.coe.inv_inv_add_inv
/-
**NNReal.HolderTriple.inv_lt_inv** 是 Mathlib 中的一个定理，位于命名空间 `NNReal.HolderTriple`
。
形式化陈述：∀ {p q r : NNReal}, p.HolderTriple q r → p⁻¹ < r⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.HolderTriple.inv_lt_inv`：∀ {p q r : ℝ}, p.HolderTriple q r → p⁻¹ < 
r⁻¹
· 使用定理 `NNReal.HolderTriple.coe`：∀ {p q r : NNReal}, p.HolderTriple q r → (↑p).H
olderTriple ↑q ↑r
-/
protected lemma inv_lt_inv : p⁻¹ < r⁻¹ := h.coe.inv_lt_inv
/-
**NNReal.HolderTriple.lt** 是 Mathlib 中的一个引理，位于命名空间 `NNReal.HolderTriple`。
形式化陈述：lt : r < p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.HolderTriple.lt`：lt : r < p
· 使用定理 `NNReal.HolderTriple.coe`：∀ {p q r : NNReal}, p.HolderTriple q r → (↑p).H
olderTriple ↑q ↑r
-/
lemma lt : r < p := h.coe.lt
/-
**NNReal.HolderTriple.inv_sub_inv_eq_inv** 是 Mathlib 中的一个引理，位于命名空间 `NNReal.Holde
rTriple`。
形式化陈述：inv_sub_inv_eq_inv : r⁻¹ - q⁻¹ = p⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `NNReal.HolderTriple.inv_lt_inv`：∀ {p q r : NNReal}, p.HolderTriple q r →
 p⁻¹ < r⁻¹
· 使用定理 `NNReal.HolderTriple.symm`：∀ {p q r : NNReal}, p.HolderTriple q r → q.Hol
derTriple p r
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Real.HolderTriple.inv_sub_inv_eq_inv`：inv_sub_inv_eq_inv : r⁻¹ - q⁻¹ = p
⁻¹
· 使用定理 `NNReal.HolderTriple.coe`：∀ {p q r : NNReal}, p.HolderTriple q r → (↑p).H
olderTriple ↑q ↑r
-/
lemma inv_sub_inv_eq_inv : r⁻¹ - q⁻¹ = p⁻¹ := by
  have := h.symm.inv_lt_inv.le
  exact_mod_cast h.coe.inv_sub_inv_eq_inv
/-
**NNReal.HolderTriple.holderConjugate_div_div** 是 Mathlib 中的一个引理，位于命名空间 `NNReal.
HolderTriple`。
形式化陈述：holderConjugate_div_div : (p / r).HolderConjugate (q / r) where inv_add_in
v_eq_inv
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `NNReal.HolderTriple.inv_add_inv_eq_inv`：∀ {p q r : NNReal}, p.HolderTrip
le q r → p⁻¹ + q⁻¹ = r⁻¹
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `NNReal.HolderTriple.ne_zero'`：ne_zero' : r != 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `NNReal.HolderTriple.left_pos`：∀ {p q r : NNReal}, p.HolderTriple q r → 0
 < p
· 使用定理 `NNReal.HolderTriple.pos'`：pos' : 0 < r
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `NNReal.HolderTriple.right_pos`：∀ {p q r : NNReal}, p.HolderTriple q r → 
0 < q
-/
lemma holderConjugate_div_div : (p / r).HolderConjugate (q / r) where
  inv_add_inv_eq_inv := by
    simp [div_eq_mul_inv, ← mul_add, h.inv_add_inv_eq_inv, h.ne_zero']
  left_pos := by have := h.left_pos; have := h.pos'; positivity
  right_pos := by have := h.right_pos; have := h.pos'; positivity

end HolderTriple

namespace HolderConjugate

/-
**NNReal.HolderConjugate.two_two** 是 Mathlib 中的一个引理，位于命名空间 `NNReal.HolderConjuga
te`。
形式化陈述：two_two : HolderConjugate 2 2 where inv_add_inv_eq_inv
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `add_halves`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2] (a :
 K), a / 2 + a / 2 = a
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
-/
lemma two_two : HolderConjugate 2 2 where
  inv_add_inv_eq_inv := by simpa using add_halves (1 : ℝ≥0)
  left_pos := zero_lt_two
  right_pos := zero_lt_two

section
variable (h : p.HolderConjugate q)
include h

@[symm]
/-
**NNReal.HolderConjugate.symm** 是 Mathlib 中的一个定理，位于命名空间 `NNReal.HolderConjugate`
。
形式化陈述：∀ {p q : NNReal}, p.HolderConjugate q → q.HolderConjugate p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.HolderTriple.symm`：∀ {p q r : NNReal}, p.HolderTriple q r → q.Hol
derTriple p r
-/
protected lemma symm : q.HolderConjugate p := HolderTriple.symm h
/-
**NNReal.HolderConjugate.inv_add_inv_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `NNReal.Ho
lderConjugate`。
形式化陈述：inv_add_inv_eq_one : p⁻¹ + q⁻¹ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.HolderTriple.inv_add_inv_eq_inv`：∀ {p q r : NNReal}, p.HolderTrip
le q r → p⁻¹ + q⁻¹ = r⁻¹
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
-/
theorem inv_add_inv_eq_one : p⁻¹ + q⁻¹ = 1 := inv_one (G := ℝ≥0) ▸ h.inv_add_inv_eq_inv
/-
**NNReal.HolderConjugate.sub_one_pos** 是 Mathlib 中的一个定理，位于命名空间 `NNReal.HolderCon
jugate`。
形式化陈述：sub_one_pos : 0 < p - 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsub_pos_of_lt`：tsub_pos_of_lt (h : a < b) : 0 < b - a
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `NNReal.instOrderedSub`：OrderedSub NNReal
· 使用引理 `NNReal.HolderTriple.lt`：lt : r < p
-/
theorem sub_one_pos : 0 < p - 1 := tsub_pos_of_lt h.lt
/-
**NNReal.HolderConjugate.sub_one_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `NNReal.Holde
rConjugate`。
形式化陈述：sub_one_ne_zero : p - 1 != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `NNReal.HolderConjugate.sub_one_pos`：sub_one_pos : 0 < p - 1
-/
theorem sub_one_ne_zero : p - 1 ≠ 0 := h.sub_one_pos.ne'
/-
**NNReal.HolderConjugate.conjugate_eq** 是 Mathlib 中的一个定理，位于命名空间 `NNReal.HolderCo
njugate`。
形式化陈述：conjugate_eq : q = p / (p - 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Real.HolderTriple.lt`：lt : r < p
· 使用定理 `NNReal.HolderConjugate.coe`：∀ {p q : NNReal}, p.HolderConjugate q → (↑p)
.HolderConjugate ↑q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Real.HolderConjugate.conjugate_eq`：conjugate_eq : q = p / (p - 1)
· 使用定理 `NNReal.coe_one`：↑1 = 1
· 使用定理 `NNReal.coe_sub`：∀ {r₁ r₂ : NNReal}, r₂ ≤ r₁ → ↑(r₁ - r₂) = ↑r₁ - ↑r₂
-/
theorem conjugate_eq : q = p / (p - 1) := by
  have : ((1 : ℝ≥0) : ℝ) ≤ p := h.coe.lt.le
  exact_mod_cast NNReal.coe_sub this ▸ coe_one ▸ h.coe.conjugate_eq
/-
**NNReal.HolderConjugate.conjExponent_eq** 是 Mathlib 中的一个引理，位于命名空间 `NNReal.Holde
rConjugate`。
形式化陈述：conjExponent_eq : conjExponent p = q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.HolderConjugate.conjugate_eq`：conjugate_eq : q = p / (p - 1)
-/
lemma conjExponent_eq : conjExponent p = q := h.conjugate_eq.symm
/-
**NNReal.HolderConjugate.one_sub_inv** 是 Mathlib 中的一个引理，位于命名空间 `NNReal.HolderCon
jugate`。
形式化陈述：one_sub_inv : 1 - p⁻¹ = q⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsub_eq_of_eq_add`：tsub_eq_of_eq_add (h : a = c + b) : a - b = c
· 使用定理 `NNReal.instOrderedSub`：OrderedSub NNReal
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.HolderConjugate.inv_add_inv_eq_one`：inv_add_inv_eq_one : p⁻¹ + q⁻
¹ = 1
· 使用定理 `NNReal.HolderConjugate.symm`：∀ {p q : NNReal}, p.HolderConjugate q → q.H
olderConjugate p
-/
lemma one_sub_inv : 1 - p⁻¹ = q⁻¹ := tsub_eq_of_eq_add h.symm.inv_add_inv_eq_one.symm
/-
**NNReal.HolderConjugate.sub_one_mul_conj** 是 Mathlib 中的一个定理，位于命名空间 `NNReal.Hold
erConjugate`。
形式化陈述：sub_one_mul_conj : (p - 1) * q = p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `eq_div_iff`：eq_div_iff (hb : b != 0) : c = a / b ↔ c * b = a
· 使用定理 `NNReal.HolderConjugate.sub_one_ne_zero`：sub_one_ne_zero : p - 1 != 0
· 使用定理 `NNReal.HolderConjugate.conjugate_eq`：conjugate_eq : q = p / (p - 1)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem sub_one_mul_conj : (p - 1) * q = p :=
  mul_comm q (p - 1) ▸ (eq_div_iff h.sub_one_ne_zero).1 h.conjugate_eq
/-
**NNReal.HolderConjugate.mul_eq_add** 是 Mathlib 中的一个定理，位于命名空间 `NNReal.HolderConj
ugate`。
形式化陈述：mul_eq_add : p * q = p + q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `NNReal.HolderTriple.ne_zero`：ne_zero : p != 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `inv_mul_cancel_right₀`：inv_mul_cancel_right₀ (h : b != 0) (a : G₀) : a *
 b⁻¹ * b = a
· 使用定理 `NNReal.HolderConjugate.symm`：∀ {p q : NNReal}, p.HolderConjugate q → q.H
olderConjugate p
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `NNReal.HolderTriple.inv_eq`：inv_eq : r⁻¹ = p⁻¹ + q⁻¹
-/
theorem mul_eq_add : p * q = p + q := by
  simpa [mul_add, add_mul, h.ne_zero, h.symm.ne_zero, add_comm q] using congr(p * $(h.inv_eq) * q)
/-
**NNReal.HolderConjugate.div_conj_eq_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `NNReal.H
olderConjugate`。
形式化陈述：div_conj_eq_sub_one : p / q = p - 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₃`：div_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval / l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval`：eval_cons_mul_eval [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : ((n, e) ::ᵣ L).eval * l.eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval_cons_neg`：eval_cons_mul_e
val_cons_neg [CommGroupWithZero M] (n : Int) {e : M} (he : e != 0) {L l l' : NF 
M} (h : L.eval * l.eval = l'.eval) : ((n, e) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `NNReal.HolderTriple.ne_zero`：ne_zero : p != 0
· 使用定理 `NNReal.HolderConjugate.symm`：∀ {p q : NNReal}, p.HolderConjugate q → q.H
olderConjugate p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_ne_zero`：cons_ne_zero [GroupWithZero M]
 (r : Int) {x : M} (hx : x != 0) {l : NF M} (hl : l.eval != 0) : ((r, x) ::ᵣ l).
eval != 0
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_of_eq`：eq_of_eq [Add α] [IsRightCanc
elAdd α] (p : (a : α) = b) (H : a' + b = b' + a) : a' = b'
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
（共 51 条，此处仅展示前 30 条）
-/
theorem div_conj_eq_sub_one : p / q = p - 1 := by
  field_simp [h.symm.ne_zero]
  linear_combination -h.sub_one_mul_conj
/-
**NNReal.HolderConjugate.inv_add_inv_ennreal** 是 Mathlib 中的一个引理，位于命名空间 `NNReal.H
olderConjugate`。
形式化陈述：inv_add_inv_ennreal : (p⁻¹ + q⁻¹ : Real>=0∞) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `NNReal.HolderConjugate.inv_add_inv_eq_one`：inv_add_inv_eq_one : p⁻¹ + q⁻
¹ = 1
-/
lemma inv_add_inv_ennreal : (p⁻¹ + q⁻¹ : ℝ≥0∞) = 1 := by norm_cast; exact h.inv_add_inv_eq_one

end

/-
**NNReal.HolderConjugate._root_.NNReal.holderConjugate_iff** 是 Mathlib 中的一个引理，位于
命名空间 `NNReal.HolderConjugate`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.NNReal.holderConjugate_iff : p.HolderConjugate q ↔ 1 < p ∧ p⁻¹ + q⁻¹ = 1 := by
  rw [← holderConjugate_coe_iff, Real.holderConjugate_iff, ← coe_one]
  exact_mod_cast Iff.rfl
/-
**NNReal.HolderConjugate.inv_inv** 是 Mathlib 中的一个定理，位于命名空间 `NNReal.HolderConjuga
te`。
形式化陈述：∀ {a b : NNReal}, 0 < a → 0 < b → a + b = 1 → a⁻¹.HolderConjugate b⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
-/
protected lemma inv_inv (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) : a⁻¹.HolderConjugate b⁻¹ where
  inv_add_inv_eq_inv := by simpa using hab
  left_pos := inv_pos.mpr ha
  right_pos := inv_pos.mpr hb
/-
**NNReal.HolderConjugate.inv_one_sub_inv** 是 Mathlib 中的一个引理，位于命名空间 `NNReal.Holde
rConjugate`。
形式化陈述：inv_one_sub_inv (ha₀ : 0 < a) (ha₁ : a < 1) : a⁻¹.HolderConjugate (1 - a)⁻
¹
参数：ha₀ : 0 < a；ha₁ : a < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NNReal.holderConjugate_iff`：∀ {p q : NNReal}, p.HolderConjugate q ↔ 1 < 
p ∧ p⁻¹ + q⁻¹ = 1
· 使用引理 `one_lt_inv₀`：one_lt_inv₀ (ha : 0 < a) : 1 < a⁻¹ ↔ a < 1
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `NNReal.instOrderedSub`：OrderedSub NNReal
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma inv_one_sub_inv (ha₀ : 0 < a) (ha₁ : a < 1) : a⁻¹.HolderConjugate (1 - a)⁻¹ :=
  holderConjugate_iff.mpr ⟨one_lt_inv₀ ha₀ |>.mpr ha₁, by simpa using add_tsub_cancel_of_le ha₁.le⟩
/-
**NNReal.HolderConjugate.one_sub_inv_inv** 是 Mathlib 中的一个引理，位于命名空间 `NNReal.Holde
rConjugate`。
形式化陈述：one_sub_inv_inv (ha₀ : 0 < a) (ha₁ : a < 1) : (1 - a)⁻¹.HolderConjugate a⁻
¹
参数：ha₀ : 0 < a；ha₁ : a < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.HolderConjugate.symm`：∀ {p q : NNReal}, p.HolderConjugate q → q.H
olderConjugate p
· 使用引理 `NNReal.HolderConjugate.inv_one_sub_inv`：inv_one_sub_inv (ha₀ : 0 < a) (h
a₁ : a < 1) : a⁻¹.HolderConjugate (1 - a)⁻¹
-/
lemma one_sub_inv_inv (ha₀ : 0 < a) (ha₁ : a < 1) : (1 - a)⁻¹.HolderConjugate a⁻¹ :=
  (inv_one_sub_inv ha₀ ha₁).symm

end HolderConjugate

/-
**NNReal.holderConjugate_comm** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：holderConjugate_comm : p.HolderConjugate q ↔ q.HolderConjugate p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.HolderConjugate.symm`：∀ {p q : NNReal}, p.HolderConjugate q → q.H
olderConjugate p
-/
lemma holderConjugate_comm : p.HolderConjugate q ↔ q.HolderConjugate p := ⟨.symm, .symm⟩
/-
**NNReal.holderConjugate_iff_eq_conjExponent** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：holderConjugate_iff_eq_conjExponent (hp : 1 < p) : p.HolderConjugate q ↔ q
 = p / (p - 1)
参数：hp : 1 < p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `NNReal.holderConjugate_coe_iff`：holderConjugate_coe_iff {p q : Real>=0} 
: Real.HolderConjugate (p : Real) (q : Real) ↔ HolderConjugate p q
· 使用引理 `Real.holderConjugate_iff_eq_conjExponent`：holderConjugate_iff_eq_conjExp
onent (hp : 1 < p) : p.HolderConjugate q ↔ q = p / (p - 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `NNReal.coe_one`：↑1 = 1
· 使用定理 `NNReal.coe_sub`：∀ {r₁ r₂ : NNReal}, r₂ ≤ r₁ → ↑(r₁ - r₂) = ↑r₁ - ↑r₂
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma holderConjugate_iff_eq_conjExponent (hp : 1 < p) : p.HolderConjugate q ↔ q = p / (p - 1) := by
  rw [← holderConjugate_coe_iff, Real.holderConjugate_iff_eq_conjExponent (by exact_mod_cast hp),
    ← coe_one, ← NNReal.coe_sub hp.le]
  exact_mod_cast Iff.rfl
/-
**NNReal.HolderConjugate.conjExponent** 是 Mathlib 中的一个定理，位于命名空间 `NNReal.HolderCo
njugate`。
形式化陈述：∀ {p : NNReal}, 1 < p → p.HolderConjugate p.conjExponent
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `NNReal.holderConjugate_iff_eq_conjExponent`：holderConjugate_iff_eq_conjE
xponent (hp : 1 < p) : p.HolderConjugate q ↔ q = p / (p - 1)
-/
lemma HolderConjugate.conjExponent (h : 1 < p) : p.HolderConjugate (conjExponent p) :=
  (holderConjugate_iff_eq_conjExponent h).2 rfl
/-
**NNReal.holderConjugate_one_div** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：holderConjugate_one_div (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) : (1 /
 a).HolderConjugate (1 / b)
参数：ha : 0 < a；hb : 0 < b；hab : a + b = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `NNReal.HolderConjugate.inv_inv`：∀ {a b : NNReal}, 0 < a → 0 < b → a + b 
= 1 → a⁻¹.HolderConjugate b⁻¹
-/
lemma holderConjugate_one_div (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    (1 / a).HolderConjugate (1 / b) := by simpa using HolderConjugate.inv_inv ha hb hab

end NNReal

/-
**Real.HolderTriple.toNNReal** 是 Mathlib 中的一个定理，位于命名空间 `Real.HolderTriple`。
形式化陈述：∀ {p q r : ℝ}, p.HolderTriple q r → p.toNNReal.HolderTriple q.toNNReal r.t
oNNReal
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `Real.HolderTriple.nonneg`：nonneg : 0 <= p
· 使用定理 `Real.HolderTriple.symm`：∀ {p q r : ℝ}, p.HolderTriple q r → q.HolderTrip
le p r
· 使用定理 `Real.HolderTriple.nonneg'`：nonneg' : 0 <= r
-/
protected lemma Real.HolderTriple.toNNReal {p q r : ℝ} (h : p.HolderTriple q r) :
    p.toNNReal.HolderTriple q.toNNReal r.toNNReal := by
  simpa [← NNReal.holderTriple_coe_iff, h.nonneg, h.symm.nonneg, h.nonneg']
/-
**Real.HolderConjugate.toNNReal** 是 Mathlib 中的一个定理，位于命名空间 `Real.HolderConjugate`
。
形式化陈述：∀ {p q : ℝ}, p.HolderConjugate q → p.toNNReal.HolderConjugate q.toNNReal
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.toNNReal_one`：toNNReal_one : Real.toNNReal 1 = 1
· 使用定理 `Real.HolderTriple.toNNReal`：∀ {p q r : ℝ}, p.HolderTriple q r → p.toNNRe
al.HolderTriple q.toNNReal r.toNNReal
-/
protected lemma Real.HolderConjugate.toNNReal {p q : ℝ} (h : p.HolderConjugate q) :
    p.toNNReal.HolderConjugate q.toNNReal := by
  simpa using Real.HolderTriple.toNNReal h

namespace ENNReal

/-- The conjugate exponent of `p` is `q = 1 + (p - 1)⁻¹`, so that `p⁻¹ + q⁻¹ = 1`. -/
/-
**ENNReal.conjExponent** 是 Mathlib 中的一个定义，位于命名空间 `ENNReal`。
形式化陈述：conjExponent (p : Real>=0∞) : Real>=0∞
参数：p : Real>=0∞。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The conjugate exponent of `p` is `q = 1 + (p - 1)⁻¹`, so that `p⁻¹ + q⁻¹ = 1`.
-/
noncomputable def conjExponent (p : ℝ≥0∞) : ℝ≥0∞ := 1 + (p - 1)⁻¹
/-
**ENNReal.coe_conjExponent** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：coe_conjExponent {p : Real>=0} (hp : 1 < p) : p.conjExponent = conjExponen
t p
参数：hp : 1 < p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.conjExponent.eq_1`：∀ (p : NNReal), p.conjExponent = p / (p - 1)
· 使用定理 `ENNReal.conjExponent.eq_1`：∀ (p : ENNReal), p.conjExponent = 1 + (p - 1)
⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `ENNReal.coe_inv`：coe_inv (hr : r != 0) : (↑r⁻¹ : Real>=0∞) = (↑r)⁻¹
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `tsub_pos_of_lt`：tsub_pos_of_lt (h : a < b) : 0 < b - a
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `NNReal.instOrderedSub`：OrderedSub NNReal
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₃`：div_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval / l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval`：eval_cons_mul_eval [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : ((n, e) ::ᵣ L).eval * l.eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_add`：subst_add {M : Type*} [Semiring M] {
x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ =
 Y) (hy : a * Y = y) : x…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_eq_eval`：one_eq_eval [GroupWithZero M] :
 (1:M) = NF.eval (M
（共 44 条，此处仅展示前 30 条）
-/
lemma coe_conjExponent {p : ℝ≥0} (hp : 1 < p) : p.conjExponent = conjExponent p := by
  rw [NNReal.conjExponent, conjExponent]
  norm_cast
  rw [← coe_inv (tsub_pos_of_lt hp).ne']
  norm_cast
  field_simp [(tsub_pos_of_lt hp).ne']
  rw [tsub_add_cancel_of_le hp.le]


variable {a b p q r : ℝ≥0∞}

@[simp, norm_cast]
/-
**ENNReal.holderTriple_coe_iff** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：holderTriple_coe_iff {p q r : Real>=0} (hr : r != 0) : HolderTriple (p : R
eal>=0∞) (q : Real>=0∞) (r : Real>=0∞) ↔ NNReal.HolderTriple p q r
参数：hr : r != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.holderTriple_iff`：∀ (p q r : NNReal), p.HolderTriple q r ↔ p⁻¹ + 
q⁻¹ = r⁻¹ ∧ 0 < p ∧ 0 < q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用引理 `ENNReal.HolderTriple.unique`：unique (r' : Real>=0∞) [hr' : HolderTriple 
p q r'] : r = r'
· 使用定理 `ENNReal.coe_zero`：↑0 = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ENNReal.HolderTriple.inv_add_inv_eq_inv`：∀ (p q : ENNReal) (r : semiOutP
aram ENNReal) [self : p.HolderTriple q r], p⁻¹ + q⁻¹ = r⁻¹
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `ENNReal.holderTriple_iff`：∀ (p q : ENNReal) (r : semiOutParam ENNReal), 
p.HolderTriple q r ↔ p⁻¹ + q⁻¹ = r⁻¹
· 使用定理 `NNReal.HolderTriple.ne_zero`：ne_zero : p != 0
· 使用定理 `NNReal.HolderTriple.symm`：∀ {p q r : NNReal}, p.HolderTriple q r → q.Hol
derTriple p r
· 使用定理 `NNReal.HolderTriple.inv_add_inv_eq_inv`：∀ {p q r : NNReal}, p.HolderTrip
le q r → p⁻¹ + q⁻¹ = r⁻¹
-/
lemma holderTriple_coe_iff {p q r : ℝ≥0} (hr : r ≠ 0) :
    HolderTriple (p : ℝ≥0∞) (q : ℝ≥0∞) (r : ℝ≥0∞) ↔ NNReal.HolderTriple p q r := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [NNReal.holderTriple_iff]
    obtain ⟨hp, hq⟩ : p ≠ 0 ∧ q ≠ 0 := by
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
/-
**ENNReal.holderConjugate_coe_iff** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：holderConjugate_coe_iff {p q : Real>=0} : HolderConjugate (p : Real>=0∞) (
q : Real>=0∞) ↔ NNReal.HolderConjugate p q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.holderTriple_coe_iff`：holderTriple_coe_iff {p q r : Real>=0} (hr
 : r != 0) : HolderTriple (p : Real>=0∞) (q : Real>=0∞) (r : Real>=0∞) ↔ NNReal.
HolderTriple p q r
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
-/
lemma holderConjugate_coe_iff {p q : ℝ≥0} :
    HolderConjugate (p : ℝ≥0∞) (q : ℝ≥0∞) ↔ NNReal.HolderConjugate p q :=
  holderTriple_coe_iff one_ne_zero

alias ⟨_, _root_.NNReal.HolderConjugate.coe_ennreal⟩ := holderConjugate_coe_iff

namespace HolderTriple

/-
**ENNReal.HolderTriple._root_.Real.HolderTriple.ennrealOfReal** 是 Mathlib 中的一个引理
，位于命名空间 `ENNReal.HolderTriple`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Real.HolderTriple.ennrealOfReal {p q r : ℝ} (h : p.HolderTriple q r) :
    HolderTriple (ENNReal.ofReal p) (ENNReal.ofReal q) (ENNReal.ofReal r) := by
  simpa [holderTriple_iff, ofReal_inv_of_pos, h.pos, h.symm.pos, h.pos', ofReal_add, h.nonneg,
    h.symm.nonneg] using congr(ENNReal.ofReal $(h.inv_add_inv_eq_inv))
/-
**ENNReal.HolderTriple._root_.Real.HolderConjugate.ennrealOfReal** 是 Mathlib 中的一
个引理，位于命名空间 `ENNReal.HolderTriple`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Real.HolderConjugate.ennrealOfReal {p q : ℝ} (h : p.HolderConjugate q) :
    HolderConjugate (ENNReal.ofReal p) (ENNReal.ofReal q) := by
  simpa using Real.HolderTriple.ennrealOfReal h
/-
**ENNReal.HolderTriple.of_toReal** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal.HolderTriple
`。
形式化陈述：of_toReal (h : Real.HolderTriple p.toReal q.toReal r.toReal) : HolderTripl
e p q r
参数：h : Real.HolderTriple p.toReal q.toReal r.toReal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.HolderTriple.pos`：pos : 0 < p
· 使用定理 `Real.HolderTriple.symm`：∀ {p q r : ℝ}, p.HolderTriple q r → q.HolderTrip
le p r
· 使用定理 `Real.HolderTriple.pos'`：pos' : 0 < r
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ENNReal.toReal_pos_iff`：toReal_pos_iff : 0 < a.toReal ↔ 0 < a ∧ a < ∞
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Real.HolderTriple.ennrealOfReal`：∀ {p q r : ℝ}, p.HolderTriple q r → (EN
NReal.ofReal p).HolderTriple (ENNReal.ofReal q) (ENNReal.ofReal r)
-/
lemma of_toReal (h : Real.HolderTriple p.toReal q.toReal r.toReal) : HolderTriple p q r := by
  have hp := h.pos
  have hq := h.symm.pos
  have hr := h.pos'
  rw [toReal_pos_iff] at hp hq hr
  simpa [hp.2.ne, hq.2.ne, hr.2.ne] using h.ennrealOfReal

variable (r) in
/-
**ENNReal.HolderTriple.toReal_iff** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal.HolderTripl
e`。
形式化陈述：toReal_iff (hp : 0 < p.toReal) (hq : 0 < q.toReal) : Real.HolderTriple p.t
oReal q.toReal r.toReal ↔ HolderTriple p q r
参数：hp : 0 < p.toReal；hq : 0 < q.toReal。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.HolderTriple.of_toReal`：of_toReal (h : Real.HolderTriple p.toRea
l q.toReal r.toReal) : HolderTriple p q r
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENNReal.toReal_add`：toReal_add (ha : a != ∞) (hb : b != ∞) : (a + b).toR
eal = a.toReal + b.toReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ENNReal.toReal_pos_iff`：toReal_pos_iff : 0 < a.toReal ↔ 0 < a ∧ a < ∞
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ENNReal.toReal_inv`：∀ (a : ENNReal), a⁻¹.toReal = a.toReal⁻¹
· 使用定理 `ENNReal.HolderTriple.inv_add_inv_eq_inv`：∀ (p q : ENNReal) (r : semiOutP
aram ENNReal) [self : p.HolderTriple q r], p⁻¹ + q⁻¹ = r⁻¹
-/
lemma toReal_iff (hp : 0 < p.toReal) (hq : 0 < q.toReal) :
    Real.HolderTriple p.toReal q.toReal r.toReal ↔ HolderTriple p q r := by
  refine ⟨of_toReal, fun h ↦ ⟨?_, hp, hq⟩⟩
  rw [toReal_pos_iff] at hp hq
  simpa [toReal_add, Finiteness.inv_ne_top, hp.1.ne', hq.1.ne']
    using congr(ENNReal.toReal $(h.inv_add_inv_eq_inv))

variable (r) in
/-
**ENNReal.HolderTriple.toReal** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal.HolderTriple`。
形式化陈述：toReal (hp : 0 < p.toReal) (hq : 0 < q.toReal) [HolderTriple p q r] : Real
.HolderTriple p.toReal q.toReal r.toReal
参数：hp : 0 < p.toReal；hq : 0 < q.toReal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `ENNReal.HolderTriple.toReal_iff`：toReal_iff (hp : 0 < p.toReal) (hq : 0 
< q.toReal) : Real.HolderTriple p.toReal q.toReal r.toReal ↔ HolderTriple p q r
-/
lemma toReal (hp : 0 < p.toReal) (hq : 0 < q.toReal) [HolderTriple p q r] :
    Real.HolderTriple p.toReal q.toReal r.toReal :=
  toReal_iff r hp hq |>.mpr ‹_›
/-
**ENNReal.HolderTriple.of_toNNReal** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal.HolderTrip
le`。
形式化陈述：of_toNNReal (h : NNReal.HolderTriple p.toNNReal q.toNNReal r.toNNReal) : H
olderTriple p q r
参数：h : NNReal.HolderTriple p.toNNReal q.toNNReal r.toNNReal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.HolderTriple.of_toReal`：of_toReal (h : Real.HolderTriple p.toRea
l q.toReal r.toReal) : HolderTriple p q r
· 使用定理 `NNReal.HolderTriple.coe`：∀ {p q r : NNReal}, p.HolderTriple q r → (↑p).H
olderTriple ↑q ↑r
-/
lemma of_toNNReal (h : NNReal.HolderTriple p.toNNReal q.toNNReal r.toNNReal) :
    HolderTriple p q r :=
  .of_toReal <| by simpa only [coe_toNNReal_eq_toReal] using h.coe

variable (r) in
/-
**ENNReal.HolderTriple.toNNReal_iff** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal.HolderTri
ple`。
形式化陈述：toNNReal_iff (hp : 0 < p.toNNReal) (hq : 0 < q.toNNReal) : NNReal.HolderTr
iple p.toNNReal q.toNNReal r.toNNReal ↔ HolderTriple p q r
参数：hp : 0 < p.toNNReal；hq : 0 < q.toNNReal。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ENNReal.HolderTriple.toReal_iff`：toReal_iff (hp : 0 < p.toReal) (hq : 0 
< q.toReal) : Real.HolderTriple p.toReal q.toReal r.toReal ↔ HolderTriple p q r
-/
lemma toNNReal_iff (hp : 0 < p.toNNReal) (hq : 0 < q.toNNReal) :
    NNReal.HolderTriple p.toNNReal q.toNNReal r.toNNReal ↔ HolderTriple p q r := by
  simp_rw [← NNReal.holderTriple_coe_iff, coe_toNNReal_eq_toReal]
  apply toReal_iff r ?_ ?_
  all_goals simpa [← coe_toNNReal_eq_toReal]

variable (r) in
/-
**ENNReal.HolderTriple.toNNReal** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal.HolderTriple`
。
形式化陈述：toNNReal (hp : 0 < p.toNNReal) (hq : 0 < q.toNNReal) [HolderTriple p q r] 
: NNReal.HolderTriple p.toNNReal q.toNNReal r.toNNReal
参数：hp : 0 < p.toNNReal；hq : 0 < q.toNNReal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `ENNReal.HolderTriple.toNNReal_iff`：toNNReal_iff (hp : 0 < p.toNNReal) (h
q : 0 < q.toNNReal) : NNReal.HolderTriple p.toNNReal q.toNNReal r.toNNReal ↔ Hol
derTriple p q r
-/
lemma toNNReal (hp : 0 < p.toNNReal) (hq : 0 < q.toNNReal) [HolderTriple p q r] :
    NNReal.HolderTriple p.toNNReal q.toNNReal r.toNNReal :=
  toNNReal_iff r hp hq |>.mpr ‹_›

end HolderTriple

namespace HolderConjugate

/-
**ENNReal.HolderConjugate.of_toReal** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal.HolderCon
jugate`。
形式化陈述：of_toReal (h : p.toReal.HolderConjugate q.toReal) : p.HolderConjugate q
参数：h : p.toReal.HolderConjugate q.toReal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.HolderTriple.of_toReal`：of_toReal (h : Real.HolderTriple p.toRea
l q.toReal r.toReal) : HolderTriple p q r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.HolderConjugate.eq_1`：∀ (p q : ℝ), p.HolderConjugate q = p.HolderTr
iple q 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.toReal_one`：ENNReal.toReal 1 = 1
-/
lemma of_toReal (h : p.toReal.HolderConjugate q.toReal) : p.HolderConjugate q := by
  rw [Real.HolderConjugate] at h
  exact HolderTriple.of_toReal (toReal_one ▸ h)
/-
**ENNReal.HolderConjugate.toReal_iff** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal.HolderCo
njugate`。
形式化陈述：toReal_iff (hp : 1 < p.toReal) : p.toReal.HolderConjugate q.toReal ↔ p.Hol
derConjugate q
参数：hp : 1 < p.toReal。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.HolderConjugate.of_toReal`：of_toReal (h : p.toReal.HolderConjuga
te q.toReal) : p.HolderConjugate q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.toReal_pos_iff`：toReal_pos_iff : 0 < a.toReal ↔ 0 < a ∧ a < ∞
· 使用引理 `ENNReal.HolderConjugate.pos`：pos : 0 < p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `ENNReal.HolderConjugate.lt_top_iff_one_lt`：lt_top_iff_one_lt : p < ∞ ↔ 1
 < q
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `ENNReal.toReal_mono`：toReal_mono (hb : b != ∞) (h : a <= b) : a.toReal <
= b.toReal
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用引理 `ENNReal.HolderTriple.toReal`：toReal (hp : 0 < p.toReal) (hq : 0 < q.toRe
al) [HolderTriple p q r] : Real.HolderTriple p.toReal q.toReal r.toReal
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
lemma toReal_iff (hp : 1 < p.toReal) :
    p.toReal.HolderConjugate q.toReal ↔ p.HolderConjugate q := by
  refine ⟨of_toReal, fun h ↦ ?_⟩
  have hq : 0 < q.toReal := by
    rw [toReal_pos_iff]
    refine ⟨pos q p, lt_top_iff_one_lt q p |>.mpr ?_⟩
    contrapose! hp
    exact toReal_mono one_ne_top hp
  simpa using HolderTriple.toReal 1 (zero_lt_one.trans hp) hq
/-
**ENNReal.HolderConjugate.toReal** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal.HolderConjug
ate`。
形式化陈述：toReal (hp : 1 < p.toReal) [HolderConjugate p q] : p.toReal.HolderConjugat
e q.toReal
参数：hp : 1 < p.toReal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `ENNReal.HolderConjugate.toReal_iff`：toReal_iff (hp : 1 < p.toReal) : p.t
oReal.HolderConjugate q.toReal ↔ p.HolderConjugate q
-/
lemma toReal (hp : 1 < p.toReal) [HolderConjugate p q] :
    p.toReal.HolderConjugate q.toReal :=
  toReal_iff hp |>.mpr ‹_›
/-
**ENNReal.HolderConjugate.toReal_of_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal.Ho
lderConjugate`。
形式化陈述：toReal_of_ne_top (hp : p != ∞) (hq : q != ∞) [HolderConjugate p q] : p.toR
eal.HolderConjugate q.toReal
参数：hp : p != ∞；hq : q != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.HolderConjugate.toReal`：toReal (hp : 1 < p.toReal) [HolderConjug
ate p q] : p.toReal.HolderConjugate q.toReal
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.toReal_lt_toReal`：toReal_lt_toReal (ha : a != ∞) (hb : b != ∞) :
 a.toReal < b.toReal ↔ a < b
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `ENNReal.HolderConjugate.lt_top_iff_one_lt`：lt_top_iff_one_lt : p < ∞ ↔ 1
 < q
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
-/
lemma toReal_of_ne_top (hp : p ≠ ∞) (hq : q ≠ ∞) [HolderConjugate p q] :
    p.toReal.HolderConjugate q.toReal :=
  toReal ((toReal_lt_toReal one_ne_top hp).mpr ((lt_top_iff_one_lt q p).mp hq.lt_top))
/-
**ENNReal.HolderConjugate.of_toNNReal** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal.HolderC
onjugate`。
形式化陈述：of_toNNReal (h : NNReal.HolderConjugate p.toNNReal q.toNNReal) : HolderCon
jugate p q
参数：h : NNReal.HolderConjugate p.toNNReal q.toNNReal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.HolderConjugate.of_toReal`：of_toReal (h : p.toReal.HolderConjuga
te q.toReal) : p.HolderConjugate q
· 使用定理 `NNReal.HolderConjugate.coe`：∀ {p q : NNReal}, p.HolderConjugate q → (↑p)
.HolderConjugate ↑q
-/
lemma of_toNNReal (h : NNReal.HolderConjugate p.toNNReal q.toNNReal) :
    HolderConjugate p q :=
  .of_toReal <| by simpa only [coe_toNNReal_eq_toReal] using h.coe
/-
**ENNReal.HolderConjugate.toNNReal_iff** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal.Holder
Conjugate`。
形式化陈述：toNNReal_iff (hp : 1 < p.toNNReal) : NNReal.HolderConjugate p.toNNReal q.t
oNNReal ↔ HolderConjugate p q
参数：hp : 1 < p.toNNReal。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ENNReal.HolderConjugate.toReal_iff`：toReal_iff (hp : 1 < p.toReal) : p.t
oReal.HolderConjugate q.toReal ↔ p.HolderConjugate q
-/
lemma toNNReal_iff (hp : 1 < p.toNNReal) :
    NNReal.HolderConjugate p.toNNReal q.toNNReal ↔ HolderConjugate p q := by
  simp_rw [← NNReal.holderTriple_coe_iff, coe_toNNReal_eq_toReal]
  apply toReal_iff ?_
  all_goals simpa [← coe_toNNReal_eq_toReal]
/-
**ENNReal.HolderConjugate.toNNReal** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal.HolderConj
ugate`。
形式化陈述：toNNReal (hp : 1 < p.toNNReal) [HolderConjugate p q] : NNReal.HolderConjug
ate p.toNNReal q.toNNReal
参数：hp : 1 < p.toNNReal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `ENNReal.HolderConjugate.toNNReal_iff`：toNNReal_iff (hp : 1 < p.toNNReal)
 : NNReal.HolderConjugate p.toNNReal q.toNNReal ↔ HolderConjugate p q
-/
lemma toNNReal (hp : 1 < p.toNNReal) [HolderConjugate p q] :
    NNReal.HolderConjugate p.toNNReal q.toNNReal :=
  toNNReal_iff hp |>.mpr ‹_›
/-
**ENNReal.HolderConjugate.conjExponent** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal.Holder
Conjugate`。
形式化陈述：∀ {p : ENNReal}, 1 ≤ p → p.HolderConjugate p.conjExponent
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.HolderConjugate.eq_1`：∀ (p q : ENNReal), p.HolderConjugate q = p
.HolderTriple q 1
· 使用定理 `ENNReal.holderTriple_iff`：∀ (p q : ENNReal) (r : semiOutParam ENNReal), 
p.HolderTriple q r ↔ p⁻¹ + q⁻¹ = r⁻¹
· 使用定理 `ENNReal.conjExponent.eq_1`：∀ (p : ENNReal), p.conjExponent = 1 + (p - 1)
⁻¹
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AddLECancellable.eq_tsub_iff_add_eq_of_le`：∀ {α : Type u_1} [inst : AddC
ommSemigroup α] [inst_1 : PartialOrder α] [ExistsAddOfLE α] [AddLeftMono α]   [i
nst_4 : Sub α] [OrderedSub α] {…
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `inv_eq_iff_eq_inv`：inv_eq_iff_eq_inv : a⁻¹ = b ↔ a = b⁻¹
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `ENNReal.inv_zero`：0⁻¹ = ⊤
· 使用定理 `add_top`：add_top (a : α) : a + ⊤ = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `ENNReal.top_sub`：∀ {a : ENNReal}, a ≠ ⊤ → ⊤ - a = ⊤
（共 54 条，此处仅展示前 30 条）
-/
protected lemma conjExponent {p : ℝ≥0∞} (hp : 1 ≤ p) : p.HolderConjugate (conjExponent p) := by
  have : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  rw [HolderConjugate, holderTriple_iff, conjExponent, add_comm]
  refine (AddLECancellable.eq_tsub_iff_add_eq_of_le (α := ℝ≥0∞) (by simpa) (by simpa)).1 ?_
  rw [inv_eq_iff_eq_inv]
  obtain rfl | hp₁ := hp.eq_or_lt
  · simp
  obtain rfl | hp := eq_or_ne p ∞
  · simp
  calc
    1 + (p - 1)⁻¹ = (p - 1 + 1) / (p - 1) := by
      rw [ENNReal.add_div, ENNReal.div_self ((tsub_pos_of_lt hp₁).ne') (sub_ne_top hp), one_div]
    _ = (1⁻¹ - p⁻¹)⁻¹ := by
      rw [tsub_add_cancel_of_le, ← inv_eq_iff_eq_inv, div_eq_mul_inv, ENNReal.mul_inv, inv_inv,
        ENNReal.mul_sub, ENNReal.inv_mul_cancel, mul_one] <;> simp [*]
/-
**ENNReal.HolderConjugate.** 是 Mathlib 中的一个实例，位于命名空间 `ENNReal.HolderConjugate`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {p : ℝ≥0∞} [Fact (1 ≤ p)] : p.HolderConjugate (conjExponent p) := .conjExponent Fact.out

section

variable [h : HolderConjugate p q]

/-
**ENNReal.HolderConjugate.conjExponent_eq** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal.Hol
derConjugate`。
形式化陈述：conjExponent_eq : conjExponent p = q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.HolderConjugate.one_le`：one_le : 1 <= p
· 使用引理 `ENNReal.HolderConjugate.unique`：unique (q' : Real>=0∞) [hq' : HolderConj
ugate p q'] : q = q'
· 使用定理 `ENNReal.HolderConjugate.instConjExponentOfFactLeOfNat`：∀ {p : ENNReal} [
Fact (1 ≤ p)], p.HolderConjugate p.conjExponent
-/
lemma conjExponent_eq : conjExponent p = q :=
  have : Fact (1 ≤ p) := ⟨one_le p q⟩
  unique p (conjExponent p) q
/-
**ENNReal.HolderConjugate.conj_eq** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal.HolderConju
gate`。
形式化陈述：conj_eq : q = 1 + (p - 1)⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ENNReal.HolderConjugate.conjExponent_eq`：conjExponent_eq : conjExponent 
p = q
-/
lemma conj_eq : q = 1 + (p - 1)⁻¹ := conjExponent_eq.symm
/-
**ENNReal.HolderConjugate.mul_eq_add** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal.HolderCo
njugate`。
形式化陈述：mul_eq_add : p * q = p + q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.top_mul`：∀ {a : ENNReal}, a ≠ 0 → ⊤ * a = ⊤
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ENNReal.HolderConjugate.ne_zero`：∀ (p q : ENNReal) [p.HolderConjugate q]
, p ≠ 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.mul_top`：∀ {a : ENNReal}, a ≠ 0 → a * ⊤ = ⊤
· 使用定理 `add_top`：add_top (a : α) : a + ⊤ = ⊤
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `ENNReal.mul_inv_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a * a⁻¹ = 1
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `ENNReal.inv_mul_cancel_right`：∀ {a b : ENNReal}, b ≠ 0 → b ≠ ⊤ → a * b⁻¹
 * b = a
· 使用引理 `ENNReal.HolderConjugate.inv_add_inv_eq_one`：inv_add_inv_eq_one : p⁻¹ + q
⁻¹ = 1
-/
lemma mul_eq_add : p * q = p + q := by
  obtain rfl | hp := eq_or_ne p ∞
  · simp [ne_zero q ∞]
  obtain rfl | hq := eq_or_ne q ∞
  · simp [ne_zero p ∞]
  simpa [add_comm p, mul_add, add_mul, hp, hq, ne_zero p q, ne_zero q p, ENNReal.mul_inv_cancel,
    ENNReal.inv_mul_cancel_right] using congr(p * $((inv_add_inv_eq_one p q).symm) * q)
/-
**ENNReal.HolderConjugate.div_conj_eq_sub_one** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal
.HolderConjugate`。
形式化陈述：div_conj_eq_sub_one : p / q = p - 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `ENNReal.inv_top`：⊤⁻¹ = 0
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ENNReal.HolderConjugate.unique`：unique (q' : Real>=0∞) [hq' : HolderConj
ugate p q'] : q = q'
· 使用定理 `ENNReal.eq_sub_of_add_eq`：∀ {a b c : ENNReal}, c ≠ ⊤ → a + c = b → a = b
 - c
· 使用定理 `ENNReal.one_ne_top`：1 ≠ ⊤
· 使用定理 `ENNReal.div_self`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a / a = 1
· 使用定理 `ENNReal.HolderConjugate.ne_zero`：∀ (p q : ENNReal) [p.HolderConjugate q]
, p ≠ 0
· 使用定理 `ENNReal.add_div`：∀ {a b c : ENNReal}, (a + b) / c = a / c + b / c
· 使用引理 `ENNReal.HolderConjugate.mul_eq_add`：mul_eq_add : p * q = p + q
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma div_conj_eq_sub_one : p / q = p - 1 := by
  obtain rfl | hq := eq_or_ne q ∞
  · obtain rfl := unique ∞ p 1
    simp
  refine ENNReal.eq_sub_of_add_eq one_ne_top ?_
  rw [← ENNReal.div_self (ne_zero q p) hq, ← ENNReal.add_div, ← h.mul_eq_add, mul_div_assoc,
    ENNReal.div_self (ne_zero q p) hq, mul_one]

end

/-
**ENNReal.HolderConjugate.inv_inv** 是 Mathlib 中的一个定理，位于命名空间 `ENNReal.HolderConju
gate`。
形式化陈述：∀ {a b : ENNReal}, a + b = 1 → a⁻¹.HolderConjugate b⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
-/
protected lemma inv_inv (hab : a + b = 1) : a⁻¹.HolderConjugate b⁻¹ where
  inv_add_inv_eq_inv := by simpa [inv_inv] using hab
/-
**ENNReal.HolderConjugate.inv_one_sub_inv** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal.Hol
derConjugate`。
形式化陈述：inv_one_sub_inv (ha : a <= 1) : a⁻¹.HolderConjugate (1 - a)⁻¹
参数：ha : a <= 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.HolderConjugate.inv_inv`：∀ {a b : ENNReal}, a + b = 1 → a⁻¹.Hold
erConjugate b⁻¹
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
-/
lemma inv_one_sub_inv (ha : a ≤ 1) : a⁻¹.HolderConjugate (1 - a)⁻¹ :=
  .inv_inv <| add_tsub_cancel_of_le ha
/-
**ENNReal.HolderConjugate.inv_one_sub_inv'** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal.Ho
lderConjugate`。
形式化陈述：inv_one_sub_inv' (ha : 1 <= a) : a.HolderConjugate (1 - a⁻¹)⁻¹
参数：ha : 1 <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用引理 `ENNReal.HolderConjugate.inv_one_sub_inv`：inv_one_sub_inv (ha : a <= 1) :
 a⁻¹.HolderConjugate (1 - a)⁻¹
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.inv_le_one`：∀ {a : ENNReal}, a⁻¹ ≤ 1 ↔ 1 ≤ a
-/
lemma inv_one_sub_inv' (ha : 1 ≤ a) : a.HolderConjugate (1 - a⁻¹)⁻¹ := by
  simpa using inv_one_sub_inv (ENNReal.inv_le_one.mpr ha)
/-
**ENNReal.HolderConjugate.one_sub_inv_inv** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal.Hol
derConjugate`。
形式化陈述：one_sub_inv_inv (ha : a <= 1) : (1 - a)⁻¹.HolderConjugate a⁻¹
参数：ha : a <= 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.HolderConjugate.inv_one_sub_inv`：inv_one_sub_inv (ha : a <= 1) :
 a⁻¹.HolderConjugate (1 - a)⁻¹
-/
lemma one_sub_inv_inv (ha : a ≤ 1) : (1 - a)⁻¹.HolderConjugate a⁻¹ := (inv_one_sub_inv ha).symm
/-
**ENNReal.HolderConjugate.top_one** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal.HolderConju
gate`。
形式化陈述：top_one : HolderConjugate ∞ 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.inv_top`：⊤⁻¹ = 0
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma top_one : HolderConjugate ∞ 1 := ⟨by simp⟩
/-
**ENNReal.HolderConjugate.one_top** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal.HolderConju
gate`。
形式化陈述：one_top : HolderConjugate 1 ∞
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `ENNReal.inv_top`：⊤⁻¹ = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma one_top : HolderConjugate 1 ∞ := ⟨by simp⟩

end HolderConjugate

/-
**ENNReal.isConjExponent_comm** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`。
形式化陈述：isConjExponent_comm : p.HolderConjugate q ↔ q.HolderConjugate p
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isConjExponent_comm : p.HolderConjugate q ↔ q.HolderConjugate p := ⟨(·.symm), (·.symm)⟩
/-
**ENNReal.isConjExponent_iff_eq_conjExponent** 是 Mathlib 中的一个引理，位于命名空间 `ENNReal`
。
形式化陈述：isConjExponent_iff_eq_conjExponent (hp : 1 <= p) : p.HolderConjugate q ↔ q
 = 1 + (p - 1)⁻¹
参数：hp : 1 <= p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ENNReal.HolderConjugate.conj_eq`：conj_eq : q = 1 + (p - 1)⁻¹
· 使用定理 `ENNReal.HolderConjugate.conjExponent`：∀ {p : ENNReal}, 1 ≤ p → p.HolderC
onjugate p.conjExponent
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isConjExponent_iff_eq_conjExponent (hp : 1 ≤ p) : p.HolderConjugate q ↔ q = 1 + (p - 1)⁻¹ :=
  ⟨fun h ↦ h.conj_eq, by rintro rfl; exact .conjExponent hp⟩

end ENNReal

