/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
module

public meta import Mathlib.Data.Tree.Basic
public import Mathlib.Algebra.Field.Basic
public meta import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Data.Tree.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Util.SynthesizeUsing

/-!
# A tactic for canceling numeric denominators

This file defines tactics that cancel numeric denominators from field Expressions.

As an example, we want to transform a comparison `5*(a/3 + b/4) < c/3` into the equivalent
`5*(4*a + 3*b) < 4*c`.

## Implementation notes

The tooling here was originally written for `linarith`, not intended as an interactive tactic.
The interactive version has been split off because it is sometimes convenient to use on its own.
There are likely some rough edges to it.

Improving this tactic would be a good project for someone interested in learning tactic programming.
-/

public meta section

open Lean Parser Tactic Mathlib Meta NormNum Qq

initialize registerTraceClass `CancelDenoms

namespace Mathlib.Tactic.CancelDenoms

/-! ### Lemmas used in the procedure -/

/-
**Mathlib.Tactic.CancelDenoms.mul_subst** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tacti
c.CancelDenoms`。
形式化陈述：mul_subst {α} [CommRing α] {n1 n2 k e1 e2 t1 t2 : α} (h1 : n1 * e1 = t1) (
h2 : n2 * e2 = t2) (h3 : n1 * n2 = k) : k * (e1 * e2) = t1 * t2
参数：h1 : n1 * e1 = t1；h2 : n2 * e2 = t2；h3 : n1 * n2 = k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)

--- 原说明 ---
### Lemmas used in the procedure
-/
theorem mul_subst {α} [CommRing α] {n1 n2 k e1 e2 t1 t2 : α}
    (h1 : n1 * e1 = t1) (h2 : n2 * e2 = t2) (h3 : n1 * n2 = k) : k * (e1 * e2) = t1 * t2 := by
  rw [← h3, mul_comm n1, mul_assoc n2, ← mul_assoc n1, h1,
      ← mul_assoc n2, mul_comm n2, mul_assoc, h2]
/-
**Mathlib.Tactic.CancelDenoms.div_subst** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tacti
c.CancelDenoms`。
形式化陈述：div_subst {α} [Field α] {n1 n2 k e1 e2 t1 : α} (h1 : n1 * e1 = t1) (h2 : n
2 / e2 = 1) (h3 : n1 * n2 = k) : k * (e1 / e2) = t1
参数：h1 : n1 * e1 = t1；h2 : n2 / e2 = 1；h3 : n1 * n2 = k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_div_left_comm`：mul_div_left_comm : a * (b / c) = b * (a / c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem div_subst {α} [Field α] {n1 n2 k e1 e2 t1 : α}
    (h1 : n1 * e1 = t1) (h2 : n2 / e2 = 1) (h3 : n1 * n2 = k) : k * (e1 / e2) = t1 := by
  rw [← h3, mul_assoc, mul_div_left_comm, h2, ← mul_assoc, h1, mul_comm, one_mul]
/-
**Mathlib.Tactic.CancelDenoms.cancel_factors_eq_div** 是 Mathlib 中的一个定理，位于命名空间 `M
athlib.Tactic.CancelDenoms`。
形式化陈述：cancel_factors_eq_div {α} [Field α] {n e e' : α} (h : n * e = e') (h2 : n 
!= 0) : e = e' / n
参数：h : n * e = e'；h2 : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `eq_div_of_mul_eq`：eq_div_of_mul_eq (hc : c != 0) : a * c = b -> a = b / 
c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem cancel_factors_eq_div {α} [Field α] {n e e' : α}
    (h : n * e = e') (h2 : n ≠ 0) : e = e' / n :=
  eq_div_of_mul_eq h2 <| by rwa [mul_comm] at h
/-
**Mathlib.Tactic.CancelDenoms.add_subst** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tacti
c.CancelDenoms`。
形式化陈述：add_subst {α} [Ring α] {n e1 e2 t1 t2 : α} (h1 : n * e1 = t1) (h2 : n * e2
 = t2) : n * (e1 + e2) = t1 + t2
参数：h1 : n * e1 = t1；h2 : n * e2 = t2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `left_distrib`：left_distrib [Mul R] [Add R] [LeftDistribClass R] (a b c :
 R) : a * (b + c) = a * b + a * c
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem add_subst {α} [Ring α] {n e1 e2 t1 t2 : α} (h1 : n * e1 = t1) (h2 : n * e2 = t2) :
    n * (e1 + e2) = t1 + t2 := by simp [left_distrib, *]
/-
**Mathlib.Tactic.CancelDenoms.sub_subst** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tacti
c.CancelDenoms`。
形式化陈述：sub_subst {α} [Ring α] {n e1 e2 t1 t2 : α} (h1 : n * e1 = t1) (h2 : n * e2
 = t2) : n * (e1 - e2) = t1 - t2
参数：h1 : n * e1 = t1；h2 : n * e2 = t2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `left_distrib`：left_distrib [Mul R] [Add R] [LeftDistribClass R] (a b c :
 R) : a * (b + c) = a * b + a * c
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sub_subst {α} [Ring α] {n e1 e2 t1 t2 : α} (h1 : n * e1 = t1) (h2 : n * e2 = t2) :
    n * (e1 - e2) = t1 - t2 := by simp [left_distrib, *, sub_eq_add_neg]
/-
**Mathlib.Tactic.CancelDenoms.neg_subst** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tacti
c.CancelDenoms`。
形式化陈述：neg_subst {α} [Ring α] {n e t : α} (h1 : n * e = t) : n * -e = -t
参数：h1 : n * e = t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem neg_subst {α} [Ring α] {n e t : α} (h1 : n * e = t) : n * -e = -t := by simp [*]
/-
**Mathlib.Tactic.CancelDenoms.pow_subst** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tacti
c.CancelDenoms`。
形式化陈述：pow_subst {α} [CommRing α] {n e1 t1 k l : α} {e2 : Nat} (h1 : n * e1 = t1)
 (h2 : l * n ^ e2 = k) : k * (e1 ^ e2) = l * t1 ^ e2
参数：h1 : n * e1 = t1；h2 : l * n ^ e2 = k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem pow_subst {α} [CommRing α] {n e1 t1 k l : α} {e2 : ℕ}
    (h1 : n * e1 = t1) (h2 : l * n ^ e2 = k) : k * (e1 ^ e2) = l * t1 ^ e2 := by
  rw [← h2, ← h1, mul_pow, mul_assoc]
/-
**Mathlib.Tactic.CancelDenoms.inv_subst** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tacti
c.CancelDenoms`。
形式化陈述：inv_subst {α} [Field α] {n k e : α} (h2 : e != 0) (h3 : n * e = k) : k * (
e ⁻¹) = n
参数：h2 : e != 0；h3 : n * e = k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_div_cancel_right₀`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [ins
t_1 : Div M₀] [MulDivCancelClass M₀] (a : M₀) {b : M₀},   b ≠ 0 → a * b / b = a
· 使用定理 `GroupWithZero.toMulDivCancelClass`：∀ {G₀ : Type u} [inst : GroupWithZero
 G₀], MulDivCancelClass G₀
-/
theorem inv_subst {α} [Field α] {n k e : α} (h2 : e ≠ 0) (h3 : n * e = k) :
    k * (e ⁻¹) = n := by rw [← div_eq_mul_inv, ← h3, mul_div_cancel_right₀ _ h2]
/-
**Mathlib.Tactic.CancelDenoms.cancel_factors_lt** 是 Mathlib 中的一个定理，位于命名空间 `Mathl
ib.Tactic.CancelDenoms`。
形式化陈述：cancel_factors_lt {α} [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a
 b ad bd a' b' gcd : α} (ha : ad * a = a') (hb : bd * b = b') (had : 0 < ad) (hb
d : 0 < bd) (hgcd : 0 < gcd) : (a < b) = (1 / gcd * (bd * a') < 1 / gcd * (ad * 
b'))
参数：ha : ad * a = a'；hb : bd * b = b'；had : 0 < ad；hbd : 0 < bd；hgcd : 0 < gcd。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_lt_mul_iff_right₀`：mul_lt_mul_iff_right₀ [PosMulStrictMono α] [PosMu
lReflectLT α] (a0 : 0 < a) : a * b < a * c ↔ b < c where mp h
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `one_div_pos`：one_div_pos : 0 < 1 / a ↔ 0 < a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
-/
theorem cancel_factors_lt {α} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    {a b ad bd a' b' gcd : α}
    (ha : ad * a = a') (hb : bd * b = b') (had : 0 < ad) (hbd : 0 < bd) (hgcd : 0 < gcd) :
    (a < b) = (1 / gcd * (bd * a') < 1 / gcd * (ad * b')) := by
  rw [mul_lt_mul_iff_right₀, ← ha, ← hb, ← mul_assoc, ← mul_assoc, mul_comm bd,
    mul_lt_mul_iff_right₀]
  · exact mul_pos had hbd
  · exact one_div_pos.2 hgcd
/-
**Mathlib.Tactic.CancelDenoms.cancel_factors_le** 是 Mathlib 中的一个定理，位于命名空间 `Mathl
ib.Tactic.CancelDenoms`。
形式化陈述：cancel_factors_le {α} [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a
 b ad bd a' b' gcd : α} (ha : ad * a = a') (hb : bd * b = b') (had : 0 < ad) (hb
d : 0 < bd) (hgcd : 0 < gcd) : (a <= b) = (1 / gcd * (bd * a') <= 1 / gcd * (ad 
* b'))
参数：ha : ad * a = a'；hb : bd * b = b'；had : 0 < ad；hbd : 0 < bd；hgcd : 0 < gcd。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_le_mul_iff_right₀`：mul_le_mul_iff_right₀ [PosMulMono α] [PosMulRefle
ctLE α] (a0 : 0 < a) : a * b <= a * c ↔ b <= c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `one_div_pos`：one_div_pos : 0 < 1 / a ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
-/
theorem cancel_factors_le {α} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    {a b ad bd a' b' gcd : α}
    (ha : ad * a = a') (hb : bd * b = b') (had : 0 < ad) (hbd : 0 < bd) (hgcd : 0 < gcd) :
    (a ≤ b) = (1 / gcd * (bd * a') ≤ 1 / gcd * (ad * b')) := by
  rw [mul_le_mul_iff_right₀, ← ha, ← hb, ← mul_assoc, ← mul_assoc, mul_comm bd,
    mul_le_mul_iff_right₀]
  · exact mul_pos had hbd
  · exact one_div_pos.2 hgcd
/-
**Mathlib.Tactic.CancelDenoms.cancel_factors_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mathl
ib.Tactic.CancelDenoms`。
形式化陈述：cancel_factors_eq {α} [Field α] {a b ad bd a' b' gcd : α} (ha : ad * a = a
') (hb : bd * b = b') (had : ad != 0) (hbd : bd != 0) (hgcd : gcd != 0) : (a = b
) = (1 / gcd * (bd * a') = 1 / gcd * (ad * b'))
参数：ha : ad * a = a'；hb : bd * b = b'；had : ad != 0；hbd : bd != 0；hgcd : gcd != 0
。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cancel_factors_eq {α} [Field α] {a b ad bd a' b' gcd : α} (ha : ad * a = a')
    (hb : bd * b = b') (had : ad ≠ 0) (hbd : bd ≠ 0) (hgcd : gcd ≠ 0) :
    (a = b) = (1 / gcd * (bd * a') = 1 / gcd * (ad * b')) := by
  grind
/-
**Mathlib.Tactic.CancelDenoms.cancel_factors_ne** 是 Mathlib 中的一个定理，位于命名空间 `Mathl
ib.Tactic.CancelDenoms`。
形式化陈述：cancel_factors_ne {α} [Field α] {a b ad bd a' b' gcd : α} (ha : ad * a = a
') (hb : bd * b = b') (had : ad != 0) (hbd : bd != 0) (hgcd : gcd != 0) : (a != 
b) = (1 / gcd * (bd * a') != 1 / gcd * (ad * b'))
参数：ha : ad * a = a'；hb : bd * b = b'；had : ad != 0；hbd : bd != 0；hgcd : gcd != 0
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_iff_iff`：∀ {a b : Prop}, a = b ↔ (a ↔ b)
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Mathlib.Tactic.CancelDenoms.cancel_factors_eq`：cancel_factors_eq {α} [Fi
eld α] {a b ad bd a' b' gcd : α} (ha : ad * a = a') (hb : bd * b = b') (had : ad
 != 0) (hbd : bd != 0) (hgcd : gcd …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem cancel_factors_ne {α} [Field α] {a b ad bd a' b' gcd : α} (ha : ad * a = a')
    (hb : bd * b = b') (had : ad ≠ 0) (hbd : bd ≠ 0) (hgcd : gcd ≠ 0) :
    (a ≠ b) = (1 / gcd * (bd * a') ≠ 1 / gcd * (ad * b')) := by
  rw [eq_iff_iff, not_iff_not, cancel_factors_eq ha hb had hbd hgcd]

/-! ### Computing cancellation factors -/

/--
`findCancelFactor e` produces a natural number `n`, such that multiplying `e` by `n` will
be able to cancel all the numeric denominators in `e`. The returned `Tree` describes how to
distribute the value `n` over products inside `e`.
-/
/-
**Mathlib.Tactic.CancelDenoms.findCancelFactor** 是 Mathlib 中的一个不透明定义，位于命名空间 `Mat
hlib.Tactic.CancelDenoms`。
形式化陈述：Expr → ℕ × BinaryTree ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`findCancelFactor e` produces a natural number `n`, such that multiplying `e` by
 `n` will
be able to cancel all the numeric denominators in `e`. The returned `Tree` descr
ibes how to
distribute the value `n` over products inside `e`.
-/
partial def findCancelFactor (e : Expr) : ℕ × BinaryTree ℕ :=
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, e1, e2]) | (``HSub.hSub, #[_, _, _, _, e1, e2]) =>
    let (v1, t1) := findCancelFactor e1
    let (v2, t2) := findCancelFactor e2
    let lcm := v1.lcm v2
    (lcm, .node lcm t1 t2)
  | (``HMul.hMul, #[_, _, _, _, e1, e2]) =>
    let (v1, t1) := findCancelFactor e1
    let (v2, t2) := findCancelFactor e2
    let pd := v1 * v2
    (pd, .node pd t1 t2)
  | (``HDiv.hDiv, #[_, _, _, _, e1, e2]) =>
    -- If e2 is a rational, then it's a natural number due to the simp lemmas in `deriveThms`.
    match e2.nat? with
    | some q =>
      let (v1, t1) := findCancelFactor e1
      let n := v1 * q
      (n, .node n t1 <| .node q .nil .nil)
    | none => (1, .node 1 .nil .nil)
  | (``Neg.neg, #[_, _, e]) => findCancelFactor e
  | (``HPow.hPow, #[_, ℕ, _, _, e1, e2]) =>
    match e2.nat? with
    | some k =>
      let (v1, t1) := findCancelFactor e1
      let n := v1 ^ k
      (n, .node n t1 <| .node k .nil .nil)
    | none => (1, .node 1 .nil .nil)
  | (``Inv.inv, #[_, _, e]) =>
    match e.nat? with
    | some q => (q, .node q .nil <| .node q .nil .nil)
    | none => (1, .node 1 .nil .nil)
  | _ => (1, .node 1 .nil .nil)
/-
**Mathlib.Tactic.CancelDenoms.synthesizeUsingNormNum** 是 Mathlib 中的一个定义，位于命名空间 `
Mathlib.Tactic.CancelDenoms`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def synthesizeUsingNormNum (type : Q(Prop)) : MetaM Q($type) := do
  try
    synthesizeUsingTactic' type (← `(tactic| norm_num))
  catch e =>
    throwError "Could not prove {type} using norm_num. {e.toMessageData}"

/-- `CancelResult mα e v'` provides a value for `v * e` where the denominators have been cancelled.
-/
/-
**Mathlib.Tactic.CancelDenoms.CancelResult** 是 Mathlib 中的一个结构，位于命名空间 `Mathlib.Ta
ctic.CancelDenoms`。
形式化陈述：CancelResult {u : Level} {α : Q(Type u)} (mα : Q(Mul $α)) (e : Q($α)) (v :
 Q($α)) where /-- An expression with denominators cancelled. -/ cancelled : Q($α
) /-- The proof that `cancelled` is valid. -/ pf : Q($v * $e = $cancelled)  /-- 
`mkProdPrf α sα v v' tr e` produces a proof of `v'*e = e'`, where numeric denomi
nators have been canceled in `e'`, distributing `v` proportionally according to 
the tree `tr` computed by `findCancelFactor`.  The `v'` argument is a numeral ex
pression corresponding to 
参数：Type u；mα : Q(Mul $α)；e : Q($α)；v : Q($α)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`CancelResult mα e v'` provides a value for `v * e` where the denominators have 
been cancelled. -/
-/
structure CancelResult {u : Level} {α : Q(Type u)} (mα : Q(Mul $α)) (e : Q($α)) (v : Q($α)) where
  /-- An expression with denominators cancelled. -/
  cancelled : Q($α)
  /-- The proof that `cancelled` is valid. -/
  pf : Q($v * $e = $cancelled)

/--
`mkProdPrf α sα v v' tr e` produces a proof of `v'*e = e'`, where numeric denominators have been
canceled in `e'`, distributing `v` proportionally according to the tree `tr` computed
by `findCancelFactor`.

The `v'` argument is a numeral expression corresponding to `v`, which we need in order to state
the return type accurately.
-/
/-
**Mathlib.Tactic.CancelDenoms.mkProdPrf** 是 Mathlib 中的一个不透明定义，位于命名空间 `Mathlib.Ta
ctic.CancelDenoms`。
形式化陈述：{u : Level} →   (α : Q(Type u)) →     (sα : Q(Field «$α»)) →       ℕ →    
     (v' : Q(«$α»)) →           BinaryTree ℕ → (e : Q(«$α»)) → MetaM (Mathlib.Ta
ctic.CancelDenoms.CancelResult q(inferInstance) e v')
参数：α : Q(Type u)；sα : Q(Field «$α»)；v' : Q(«$α»)；e : Q(«$α»)；Mathlib.Tactic.Canc
elDenoms.CancelResult q(inferInstance) e v'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`mkProdPrf α sα v v' tr e` produces a proof of `v'*e = e'`, where numeric denomi
nators have been
canceled in `e'`, distributing `v` proportionally according to the tree `tr` com
puted
by `findCancelFactor`.

The `v'` argument is a numeral expression corresponding to `v`, which we need in
 order to state
the return type accurately.
-/
partial def mkProdPrf {u : Level} (α : Q(Type u)) (sα : Q(Field $α)) (v : ℕ) (v' : Q($α))
    (t : BinaryTree ℕ) (e : Q($α)) : MetaM (CancelResult q(inferInstance) e v') := do
  let amwo : Q(AddMonoidWithOne $α) := q(inferInstance)
  trace[CancelDenoms] "mkProdPrf {e} {v}"
  match t, e with
  | .node _ lhs rhs, ~q($e1 + $e2) => do
    let ⟨v1, hv1⟩ ← mkProdPrf α sα v v' lhs e1
    let ⟨v2, hv2⟩ ← mkProdPrf α sα v v' rhs e2
    return ⟨q($v1 + $v2), q(CancelDenoms.add_subst $hv1 $hv2)⟩
  | .node _ lhs rhs, ~q($e1 - $e2) => do
    let ⟨v1, hv1⟩ ← mkProdPrf α sα v v' lhs e1
    let ⟨v2, hv2⟩ ← mkProdPrf α sα v v' rhs e2
    return ⟨q($v1 - $v2), q(CancelDenoms.sub_subst $hv1 $hv2)⟩
  | .node _ lhs@(.node ln _ _) rhs, ~q($e1 * $e2) => do
    trace[CancelDenoms] "recursing into mul"
    have ln' := (← mkOfNat α amwo <| mkRawNatLit ln).1
    have vln' := (← mkOfNat α amwo <| mkRawNatLit (v/ln)).1
    let ⟨v1, hv1⟩ ← mkProdPrf α sα ln ln' lhs e1
    let ⟨v2, hv2⟩ ← mkProdPrf α sα (v / ln) vln' rhs e2
    let npf ← synthesizeUsingNormNum q($ln' * $vln' = $v')
    return ⟨q($v1 * $v2), q(CancelDenoms.mul_subst $hv1 $hv2 $npf)⟩
  | .node _ lhs (.node rn _ _), ~q($e1 / $e2) => do
    -- Invariant: e2 is equal to the natural number rn
    have rn' := (← mkOfNat α amwo <| mkRawNatLit rn).1
    have vrn' := (← mkOfNat α amwo <| mkRawNatLit <| v / rn).1
    let ⟨v1, hv1⟩ ← mkProdPrf α sα (v / rn) vrn' lhs e1
    let npf ← synthesizeUsingNormNum q($rn' / $e2 = 1)
    let npf2 ← synthesizeUsingNormNum q($vrn' * $rn' = $v')
    return ⟨q($v1), q(CancelDenoms.div_subst $hv1 $npf $npf2)⟩
  | t, ~q(-$e) => do
    let ⟨v, hv⟩ ← mkProdPrf α sα v v' t e
    return ⟨q(-$v), q(CancelDenoms.neg_subst $hv)⟩
  | .node _ lhs@(.node k1 _ _) (.node k2 .nil .nil), ~q($e1 ^ $e2) => do
    have k1' := (← mkOfNat α amwo <| mkRawNatLit k1).1
    let ⟨v1, hv1⟩ ← mkProdPrf α sα k1 k1' lhs e1
    have l : ℕ := v / (k1 ^ k2)
    have l' := (← mkOfNat α amwo <| mkRawNatLit l).1
    let npf ← synthesizeUsingNormNum q($l' * $k1' ^ $e2 = $v')
    return ⟨q($l' * $v1 ^ $e2), q(CancelDenoms.pow_subst $hv1 $npf)⟩
  | .node _ .nil (.node rn _ _), ~q($ei ⁻¹) => do
    have rn' := (← mkOfNat α amwo <| mkRawNatLit rn).1
    have vrn' := (← mkOfNat α amwo <| mkRawNatLit <| v / rn).1
    have _ : $rn' =Q $ei := ⟨⟩
    let npf ← synthesizeUsingNormNum q($rn' ≠ 0)
    let npf2 ← synthesizeUsingNormNum q($vrn' * $rn' = $v')
    return ⟨q($vrn'), q(CancelDenoms.inv_subst $npf $npf2)⟩
  | _, _ => do
    return ⟨q($v' * $e), q(rfl)⟩

/-- Theorems to get expression into a form that `findCancelFactor` and `mkProdPrf`
can more easily handle. These are important for dividing by rationals and negative integers. -/
/-
**Mathlib.Tactic.CancelDenoms.deriveThms** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tact
ic.CancelDenoms`。
形式化陈述：deriveThms : List Name
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Theorems to get expression into a form that `findCancelFactor` and `mkProdPrf`
can more easily handle. These are important for dividing by rationals and negati
ve integers.
-/
def deriveThms : List Name :=
  [``div_div_eq_mul_div, ``div_neg]

/-- Helper lemma to chain together a `simp` proof and the result of `mkProdPrf`. -/
/-
**Mathlib.Tactic.CancelDenoms.derive_trans** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Ta
ctic.CancelDenoms`。
形式化陈述：derive_trans {α} [Mul α] {a b c d : α} (h : a = b) (h' : c * b = d) : c * 
a = d
参数：h : a = b；h' : c * b = d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Helper lemma to chain together a `simp` proof and the result of `mkProdPrf`.
-/
theorem derive_trans {α} [Mul α] {a b c d : α} (h : a = b) (h' : c * b = d) : c * a = d := h ▸ h'

/-- Helper lemma to chain together two `simp` proofs and the result of `mkProdPrf`. -/
/-
**Mathlib.Tactic.CancelDenoms.derive_trans** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Ta
ctic.CancelDenoms`。
形式化陈述：derive_trans {α} [Mul α] {a b c d : α} (h : a = b) (h' : c * b = d) : c * 
a = d
参数：h : a = b；h' : c * b = d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Helper lemma to chain together two `simp` proofs and the result of `mkProdPrf`.
-/
theorem derive_trans₂ {α} [Mul α] {a b c d e : α} (h : a = b) (h' : b = c) (h'' : d * c = e) :
    d * a = e := h ▸ h' ▸ h''

/--
Given `e`, a term with rational division, produces a natural number `n` and a proof of `n*e = e'`,
where `e'` has no division. Assumes "well-behaved" division.
-/
/-
**Mathlib.Tactic.CancelDenoms.derive** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic.C
ancelDenoms`。
形式化陈述：derive (e : Expr) : MetaM (Nat × Expr)
参数：e : Expr。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `e`, a term with rational division, produces a natural number `n` and a pr
oof of `n*e = e'`,
where `e'` has no division. Assumes "well-behaved" division.
-/
def derive (e : Expr) : MetaM (ℕ × Expr) := do
  trace[CancelDenoms] "e = {e}"
  let eSimp ← simpOnlyNames (config := Simp.neutralConfig) deriveThms e
  trace[CancelDenoms] "e simplified = {eSimp.expr}"
  let eSimpNormNum ← Mathlib.Meta.NormNum.deriveSimp (← Simp.mkContext) false eSimp.expr
  trace[CancelDenoms] "e norm_num'd = {eSimpNormNum.expr}"
  let (n, t) := findCancelFactor eSimpNormNum.expr
  let ⟨u, tp, e⟩ ← inferTypeQ' eSimpNormNum.expr
  let stp : Q(Field $tp) ← synthInstanceQ q(Field $tp)
  try
    have n' := (← mkOfNat tp q(inferInstance) <| mkRawNatLit <| n).1
    let r ← mkProdPrf tp stp n n' t e
    trace[CancelDenoms] "pf : {← inferType r.pf}"
    let pf' ←
      match eSimp.proof?, eSimpNormNum.proof? with
      | some pfSimp, some pfSimp' => mkAppM ``derive_trans₂ #[pfSimp, pfSimp', r.pf]
      | some pfSimp, none | none, some pfSimp => mkAppM ``derive_trans #[pfSimp, r.pf]
      | none, none => pure r.pf
    return (n, pf')
  catch E => do
    throwError "CancelDenoms.derive failed to normalize {e}.\n{E.toMessageData}"

/--
`findCompLemma e` arranges `e` in the form `lhs R rhs`, where `R ∈ {<, ≤, =, ≠}`, and returns
`lhs`, `rhs`, the `cancel_factors` lemma corresponding to `R`, and a Boolean indicating whether
`R` involves the order (i.e. `<` and `≤`) or not (i.e. `=` and `≠`).
In the case of `LT`, `LE`, `GE`, and `GT` an order on the type is needed, in the last case
it is not, the final component of the return value tracks this.
-/
/-
**Mathlib.Tactic.CancelDenoms.findCompLemma** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.T
actic.CancelDenoms`。
形式化陈述：findCompLemma (e : Expr) : MetaM (Option (Expr × Expr × Name × Bool))
参数：e : Expr。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`findCompLemma e` arranges `e` in the form `lhs R rhs`, where `R ∈ {<, ≤, =, ≠}`
, and returns
`lhs`, `rhs`, the `cancel_factors` lemma corresponding to `R`, and a Boolean ind
icating whether
`R` involves the order (i.e. `<` and `≤`) or not (i.e. `=` and `≠`).
In the case of `LT`, `LE`, `GE`, and `GT` an order on the type is needed, in the
 last case
it is not, the final component of the return value tracks this.
-/
def findCompLemma (e : Expr) : MetaM (Option (Expr × Expr × Name × Bool)) := do
  match (← whnfR e).getAppFnArgs with
  | (``LT.lt, #[_, _, a, b]) => return (a, b, ``cancel_factors_lt, true)
  | (``LE.le, #[_, _, a, b]) => return (a, b, ``cancel_factors_le, true)
  | (``Eq, #[_, a, b]) => return (a, b, ``cancel_factors_eq, false)
  -- `a ≠ b` reduces to `¬ a = b` under `whnf`
  | (``Not, #[p]) => match (← whnfR p).getAppFnArgs with
    | (``Eq, #[_, a, b]) => return (a, b, ``cancel_factors_ne, false)
    | _ => return none
  | (``GE.ge, #[_, _, a, b]) => return (b, a, ``cancel_factors_le, true)
  | (``GT.gt, #[_, _, a, b]) => return (b, a, ``cancel_factors_lt, true)
  | _ => return none

/--
`cancelDenominatorsInType h` assumes that `h` is of the form `lhs R rhs`,
where `R ∈ {<, ≤, =, ≠, ≥, >}`.
It produces an Expression `h'` of the form `lhs' R rhs'` and a proof that `h = h'`.
Numeric denominators have been canceled in `lhs'` and `rhs'`.
-/
/-
**Mathlib.Tactic.CancelDenoms.cancelDenominatorsInType** 是 Mathlib 中的一个定义，位于命名空间
 `Mathlib.Tactic.CancelDenoms`。
形式化陈述：cancelDenominatorsInType (h : Expr) : MetaM (Expr × Expr)
参数：h : Expr。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`cancelDenominatorsInType h` assumes that `h` is of the form `lhs R rhs`,
where `R ∈ {<, ≤, =, ≠, ≥, >}`.
It produces an Expression `h'` of the form `lhs' R rhs'` and a proof that `h = h
'`.
Numeric denominators have been canceled in `lhs'` and `rhs'`.
-/
def cancelDenominatorsInType (h : Expr) : MetaM (Expr × Expr) := do
  let some (lhs, rhs, lem, ord) ← findCompLemma h | throwError m!"cannot kill factors"
  let (al, lhs_p) ← derive lhs
  let ⟨u, α, _⟩ ← inferTypeQ' lhs
  let amwo ← synthInstanceQ q(AddMonoidWithOne $α)
  let (ar, rhs_p) ← derive rhs
  let gcd := al.gcd ar
  have al := (← mkOfNat α amwo <| mkRawNatLit al).1
  have ar := (← mkOfNat α amwo <| mkRawNatLit ar).1
  have gcd := (← mkOfNat α amwo <| mkRawNatLit gcd).1
  let (al_cond, ar_cond, gcd_cond) ← if ord then do
      let _ ← synthInstanceQ q(Field $α)
      let _ ← synthInstanceQ q(LinearOrder $α)
      let _ ← synthInstanceQ q(IsStrictOrderedRing $α)
      let al_pos : Q(Prop) := q(0 < $al)
      let ar_pos : Q(Prop) := q(0 < $ar)
      let gcd_pos : Q(Prop) := q(0 < $gcd)
      pure (al_pos, ar_pos, gcd_pos)
    else do
      let _ ← synthInstanceQ q(Field $α)
      let al_ne : Q(Prop) := q($al ≠ 0)
      let ar_ne : Q(Prop) := q($ar ≠ 0)
      let gcd_ne : Q(Prop) := q($gcd ≠ 0)
      pure (al_ne, ar_ne, gcd_ne)
  let al_cond ← synthesizeUsingNormNum al_cond
  let ar_cond ← synthesizeUsingNormNum ar_cond
  let gcd_cond ← synthesizeUsingNormNum gcd_cond
  let pf ← mkAppM lem #[lhs_p, rhs_p, al_cond, ar_cond, gcd_cond]
  let pf_tp ← inferType pf
  return ((← findCompLemma pf_tp).elim default (Prod.fst ∘ Prod.snd), pf)

end CancelDenoms

/--
`cancel_denoms` attempts to remove numerals from the denominators of fractions.
It works on propositions that are field-valued inequalities.

```lean
variable [LinearOrderedField α] (a b c : α)

example (h : a / 5 + b / 4 < c) : 4*a + 5*b < 20*c := by
  cancel_denoms at h
  exact h

example (h : a > 0) : a / 5 > 0 := by
  cancel_denoms
  exact h
```
-/
syntax (name := cancelDenoms) "cancel_denoms" (location)? : tactic

open Elab Tactic

/-
**Mathlib.Tactic.cancelDenominatorsAt** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def cancelDenominatorsAt (fvar : FVarId) : TacticM Unit := do
  let t ← instantiateMVars (← fvar.getDecl).type
  let (new, eqPrf) ← CancelDenoms.cancelDenominatorsInType t
  liftMetaTactic' fun g => do
    let res ← g.replaceLocalDecl fvar new eqPrf
    return res.mvarId
/-
**Mathlib.Tactic.cancelDenominatorsTarget** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tac
tic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def cancelDenominatorsTarget : TacticM Unit := do
  let (new, eqPrf) ← CancelDenoms.cancelDenominatorsInType (← getMainTarget)
  liftMetaTactic' fun g => g.replaceTargetEq new eqPrf
/-
**Mathlib.Tactic.cancelDenominators** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Tactic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def cancelDenominators (loc : Location) : TacticM Unit := do
  withLocation loc cancelDenominatorsAt cancelDenominatorsTarget
    (fun _ ↦ throwError "Failed to cancel any denominators")

@[tactic_alt cancelDenoms]
elab "cancel_denoms" loc?:(location)? : tactic => do
  cancelDenominators (expandOptLocation (Lean.mkOptionalNode loc?))
  Lean.Elab.Tactic.evalTactic (← `(tactic| try norm_num [← mul_assoc] $[$loc?]?))

end Mathlib.Tactic

