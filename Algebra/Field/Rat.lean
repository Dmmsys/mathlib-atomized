/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.NNRat.Defs

/-!
# The rational numbers form a field

This file contains the field instance on the rational numbers.

See note [foundational algebra order theory].

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom
-/

@[expose] public section

namespace Rat

/-
**Rat.instField** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
形式化陈述：instField : Field Rat where __
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CommGroupWithZero.div_eq_mul_inv`：∀ {G₀ : Type u_2} [self : CommGroupWit
hZero G₀] (a b : G₀), a / b = a * b⁻¹
· 使用定理 `CommGroupWithZero.zpow_zero'`：∀ {G₀ : Type u_2} [self : CommGroupWithZer
o G₀] (a : G₀), a ^ 0 = 1
· 使用定理 `CommGroupWithZero.zpow_succ'`：∀ {G₀ : Type u_2} [self : CommGroupWithZer
o G₀] (n : ℕ) (a : G₀), a ^ ↑n.succ = a ^ ↑n * a
· 使用定理 `CommGroupWithZero.zpow_neg'`：∀ {G₀ : Type u_2} [self : CommGroupWithZero
 G₀] (n : ℕ) (a : G₀), a ^ Int.negSucc n = (a ^ ↑n.succ)⁻¹
· 使用定理 `CommGroupWithZero.toNontrivial`：∀ {G₀ : Type u_2} [self : CommGroupWithZ
ero G₀], Nontrivial G₀
· 使用定理 `CommGroupWithZero.mul_inv_cancel`：∀ {G₀ : Type u_2} [self : CommGroupWit
hZero G₀] (a : G₀), a ≠ 0 → a * a⁻¹ = 1
· 使用定理 `CommGroupWithZero.inv_zero`：∀ {G₀ : Type u_2} [self : CommGroupWithZero 
G₀], 0⁻¹ = 0
-/
instance instField : Field ℚ where
  __ := commRing
  __ := commGroupWithZero
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl
  nnratCast_def q := by
    rw [← NNRat.den_coe, ← Int.cast_natCast q.num, ← NNRat.num_coe]; exact (num_div_den _).symm
  ratCast_def _ := (num_div_den _).symm

/-!
### Extra instances to short-circuit type class resolution

These also prevent non-computable instances being used to construct these instances non-computably.
-/

/-
**Rat.instDivisionRing** 是 Mathlib 中的一个实例，位于命名空间 `Rat`。
形式化陈述：instDivisionRing : DivisionRing Rat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Extra instances to short-circuit type class resolution

These also prevent non-computable instances being used to construct these instan
ces non-computably.
-/
instance instDivisionRing : DivisionRing ℚ := inferInstance
/-
**Rat.inv_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ {a : ℚ}, 0 ≤ a → 0 ≤ a⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.inv_def`：∀ (a : ℚ), a⁻¹ = Rat.divInt (↑a.den) a.num
· 使用定理 `Rat.divInt_nonneg`：∀ {a b : ℤ}, 0 ≤ a → 0 ≤ b → 0 ≤ Rat.divInt a b
· 使用定理 `Int.natCast_nonneg`：∀ (n : ℕ), 0 ≤ ↑n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Rat.num_nonneg`：∀ {q : ℚ}, 0 ≤ q.num ↔ 0 ≤ q
-/
protected lemma inv_nonneg {a : ℚ} (ha : 0 ≤ a) : 0 ≤ a⁻¹ := by
  rw [inv_def]
  exact divInt_nonneg (Int.natCast_nonneg a.den) (num_nonneg.mpr ha)
/-
**Rat.div_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：∀ {a b : ℚ}, 0 ≤ a → 0 ≤ b → 0 ≤ a / b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `Rat.inv_nonneg`：∀ {a : ℚ}, 0 ≤ a → 0 ≤ a⁻¹
-/
protected lemma div_nonneg {a b : ℚ} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a / b :=
  mul_nonneg ha (Rat.inv_nonneg hb)

end Rat

namespace NNRat

/-
**NNRat.instInv** 是 Mathlib 中的一个实例，位于命名空间 `NNRat`。
形式化陈述：instInv : Inv Rat>=0 where inv x
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInv : Inv ℚ≥0 where
  inv x := ⟨x⁻¹, Rat.inv_nonneg x.2⟩
/-
**NNRat.instDiv** 是 Mathlib 中的一个实例，位于命名空间 `NNRat`。
形式化陈述：instDiv : Div Rat>=0 where div x y
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDiv : Div ℚ≥0 where
  div x y := ⟨x / y, Rat.div_nonneg x.2 y.2⟩
/-
**NNRat.instZPow** 是 Mathlib 中的一个实例，位于命名空间 `NNRat`。
形式化陈述：instZPow : Pow Rat>=0 Int where pow x n
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instZPow : Pow ℚ≥0 ℤ where
  pow x n := ⟨x ^ n, Rat.zpow_nonneg x.2⟩
/-
**NNRat.coe_inv** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ (q : ℚ≥0), ↑q⁻¹ = (↑q)⁻¹
参数：q : ℚ≥0；↑q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_inv (q : ℚ≥0) : ((q⁻¹ : ℚ≥0) : ℚ) = (q : ℚ)⁻¹ := rfl
/-
**NNRat.coe_div** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ (p q : ℚ≥0), ↑(p / q) = ↑p / ↑q
参数：p q : ℚ≥0；p / q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_div (p q : ℚ≥0) : ((p / q : ℚ≥0) : ℚ) = p / q := rfl
/-
**NNRat.coe_zpow** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：∀ (p : ℚ≥0) (n : ℤ), ↑(p ^ n) = ↑p ^ n
参数：p : ℚ≥0；n : ℤ；p ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_zpow (p : ℚ≥0) (n : ℤ) : ((p ^ n : ℚ≥0) : ℚ) = p ^ n := rfl
/-
**NNRat.inv_def** 是 Mathlib 中的一个引理，位于命名空间 `NNRat`。
形式化陈述：inv_def (q : Rat>=0) : q⁻¹ = divNat q.den q.num
参数：q : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNRat.ext`：ext : (p : Rat) = (q : Rat) -> p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.inv_def`：∀ (a : ℚ), a⁻¹ = Rat.divInt (↑a.den) a.num
· 使用定理 `NNRat.num_coe`：∀ (q : ℚ≥0), (↑q).num = ↑q.num
· 使用定理 `Rat.divInt_ofNat`：∀ (num : ℤ) (den : ℕ), Rat.divInt num ↑den = mkRat num
 den
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inv_def (q : ℚ≥0) : q⁻¹ = divNat q.den q.num := by ext; simp [Rat.inv_def, num_coe, den_coe]
/-
**NNRat.div_def** 是 Mathlib 中的一个引理，位于命名空间 `NNRat`。
形式化陈述：div_def (p q : Rat>=0) : p / q = divNat (p.num * q.den) (p.den * q.num)
参数：p q : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNRat.ext`：ext : (p : Rat) = (q : Rat) -> p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Rat.div_def'`：div_def' (q r : Rat) : q / r = (q.num * r.den) /. (q.den *
 r.num)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NNRat.num_coe`：∀ (q : ℚ≥0), (↑q).num = ↑q.num
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma div_def (p q : ℚ≥0) : p / q = divNat (p.num * q.den) (p.den * q.num) := by
  ext; simp [Rat.div_def', num_coe, den_coe]
/-
**NNRat.divNat_eq_div** 是 Mathlib 中的一个定理，位于命名空间 `NNRat`。
形式化陈述：divNat_eq_div (a b : Nat) : divNat a b = a / b
参数：a b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNRat.ext`：ext : (p : Rat) = (q : Rat) -> p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.divInt_ofNat`：∀ (num : ℤ) (den : ℕ), Rat.divInt num ↑den = mkRat num
 den
· 使用定理 `Rat.mkRat_eq_div`：∀ (a : ℤ) (b : ℕ), mkRat a b = ↑a / ↑b
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem divNat_eq_div (a b : ℕ) : divNat a b = a / b := by
  ext
  simp [Rat.mkRat_eq_div]

set_option backward.isDefEq.respectTransparency false in
/-
**NNRat.num_inv_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `NNRat`。
形式化陈述：num_inv_of_ne_zero {q : Rat>=0} (hq : q != 0) : q⁻¹.num = q.den
参数：hq : q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NNRat.inv_def`：inv_def (q : Rat>=0) : q⁻¹ = divNat q.den q.num
· 使用定理 `NNRat.divNat.eq_1`：∀ (n d : ℕ), NNRat.divNat n d = ⟨Rat.divInt ↑n ↑d, ⋯⟩
· 使用定理 `NNRat.num.eq_1`：∀ (q : ℚ≥0), q.num = (↑q).num.natAbs
· 使用定理 `NNRat.coe_mk`：∀ (q : ℚ) (hq : 0 ≤ q), ↑⟨q, hq⟩ = q
· 使用定理 `Rat.divInt_ofNat`：∀ (num : ℤ) (den : ℕ), Rat.divInt num ↑den = mkRat num
 den
· 使用引理 `Rat.mk'`：mk'_num_den (q : Rat) : mk' q.num q.den q.den_nz q.reduced = q
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NNRat.num_ne_zero`：∀ {q : ℚ≥0}, q.num ≠ 0 ↔ q ≠ 0
· 使用定理 `Nat.Coprime.symm`：∀ {n m : ℕ}, n.Coprime m → m.Coprime n
· 使用引理 `NNRat.coprime_num_den`：coprime_num_den (q : Rat>=0) : q.num.Coprime q.de
n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.mk_eq_mkRat`：∀ (num : ℤ) (den : ℕ) (nz : den ≠ 0) (c : num.natAbs.Co
prime den),   { num := num, den := den, den_nz := nz, reduced := c } = mkRat num
 den
· 使用定理 `Int.natAbs_natCast`：∀ (n : ℕ), (↑n).natAbs = n
-/
lemma num_inv_of_ne_zero {q : ℚ≥0} (hq : q ≠ 0) : q⁻¹.num = q.den := by
  rw [inv_def, divNat, num, coe_mk, Rat.divInt_ofNat, ← Rat.mk_eq_mkRat _ _ (num_ne_zero.mpr hq),
    Int.natAbs_natCast]
  simpa using q.coprime_num_den.symm

set_option backward.isDefEq.respectTransparency false in
/-
**NNRat.den_inv_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `NNRat`。
形式化陈述：den_inv_of_ne_zero {q : Rat>=0} (hq : q != 0) : q⁻¹.den = q.num
参数：hq : q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NNRat.inv_def`：inv_def (q : Rat>=0) : q⁻¹ = divNat q.den q.num
· 使用定理 `NNRat.divNat.eq_1`：∀ (n d : ℕ), NNRat.divNat n d = ⟨Rat.divInt ↑n ↑d, ⋯⟩
· 使用定理 `NNRat.den.eq_1`：∀ (q : ℚ≥0), q.den = (↑q).den
· 使用定理 `NNRat.coe_mk`：∀ (q : ℚ) (hq : 0 ≤ q), ↑⟨q, hq⟩ = q
· 使用定理 `Rat.divInt_ofNat`：∀ (num : ℤ) (den : ℕ), Rat.divInt num ↑den = mkRat num
 den
· 使用引理 `Rat.mk'`：mk'_num_den (q : Rat) : mk' q.num q.den q.den_nz q.reduced = q
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NNRat.num_ne_zero`：∀ {q : ℚ≥0}, q.num ≠ 0 ↔ q ≠ 0
· 使用定理 `Nat.Coprime.symm`：∀ {n m : ℕ}, n.Coprime m → m.Coprime n
· 使用引理 `NNRat.coprime_num_den`：coprime_num_den (q : Rat>=0) : q.num.Coprime q.de
n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.mk_eq_mkRat`：∀ (num : ℤ) (den : ℕ) (nz : den ≠ 0) (c : num.natAbs.Co
prime den),   { num := num, den := den, den_nz := nz, reduced := c } = mkRat num
 den
-/
lemma den_inv_of_ne_zero {q : ℚ≥0} (hq : q ≠ 0) : q⁻¹.den = q.num := by
  rw [inv_def, divNat, den, coe_mk, Rat.divInt_ofNat, ← Rat.mk_eq_mkRat _ _ (num_ne_zero.mpr hq)]
  simpa using q.coprime_num_den.symm

@[simp]
/-
**NNRat.num_div_den** 是 Mathlib 中的一个引理，位于命名空间 `NNRat`。
形式化陈述：num_div_den (q : Rat>=0) : (q.num : Rat>=0) / q.den = q
参数：q : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNRat.ext`：ext : (p : Rat) = (q : Rat) -> p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNRat.coe_div`：∀ (p q : ℚ≥0), ↑(p / q) = ↑p / ↑q
· 使用定理 `NNRat.coe_natCast`：∀ (n : ℕ), ↑↑n = ↑n
· 使用定理 `NNRat.num.eq_1`：∀ (q : ℚ≥0), q.num = (↑q).num.natAbs
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用引理 `NNRat.cast_def`：cast_def (q : Rat>=0) : (q : K) = q.num / q.den
-/
lemma num_div_den (q : ℚ≥0) : (q.num : ℚ≥0) / q.den = q := by
  ext1
  rw [coe_div, coe_natCast, coe_natCast, num, ← Int.cast_natCast]
  exact (cast_def _).symm
/-
**NNRat.instSemifield** 是 Mathlib 中的一个实例，位于命名空间 `NNRat`。
形式化陈述：instSemifield : Semifield Rat>=0 where inv_zero
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemifield : Semifield ℚ≥0 where
  inv_zero := by ext; simp
  mul_inv_cancel q h := by ext; simp [h]
  nnratCast_def q := q.num_div_den.symm
  nnqsmul q a := q * a
  nnqsmul_def q a := rfl
  zpow n a := a ^ n
  zpow_zero' a := by ext; apply Field.zpow_zero'
  zpow_succ' n a := by ext; apply Field.zpow_succ'
  zpow_neg' n a := by ext; apply Field.zpow_neg'

end NNRat

/-
**NNRatCast.ofScientific_eq_ite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NNRatCast.ofScientific_eq_ite {K} [NNRatCast K] (m : Nat) (b : Bool) (d : 
Nat) : (OfScientific.ofScientific m b d : K) = if b = true then NNRat.divNat m (
10 ^ d) else ↑(m * 10 ^ d)
参数：m : Nat；b : Bool；d : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.ofScientific_nonneg`：ofScientific_nonneg (m : Nat) (s : Bool) (e : N
at) : 0 <= Rat.ofScientific m s e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNRatCast.toOfScientific_def`：∀ {K : Type u_1} [inst : NNRatCast K] (m :
 ℕ) (b : Bool) (d : ℕ),   OfScientific.ofScientific m b d = ↑⟨OfScientific.ofSci
entific m b d, ⋯⟩
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.ofScientific_eq_ofScientific`：Rat.ofScientific_eq_ofScientific (m : 
Nat) (s : Bool) (e : Nat) : Rat.ofScientific (OfNat.ofNat m) s (OfNat.ofNat e) =
 OfScientific.ofScient…
· 使用定理 `Rat.ofScientific_def`：∀ {m : ℕ} {s : Bool} {e : ℕ}, Rat.ofScientific m s
 e = if s = true then mkRat (↑m) (10 ^ e) else ↑(m * 10 ^ e)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem NNRatCast.ofScientific_eq_ite {K} [NNRatCast K] (m : ℕ) (b : Bool) (d : ℕ) :
    (OfScientific.ofScientific m b d : K) =
      if b = true then NNRat.divNat m (10 ^ d) else ↑(m * 10 ^ d) := by
  rw [NNRatCast.toOfScientific_def]
  split_ifs
  · congr 2
    rw [← Rat.ofScientific_eq_ofScientific, Rat.ofScientific_def, if_pos ‹_›]
    congr
  · congr 2
    rw [← Rat.ofScientific_eq_ofScientific, Rat.ofScientific_def, if_neg ‹_›]
    congr
