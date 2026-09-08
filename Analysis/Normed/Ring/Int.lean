/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# The integers as normed ring

This file contains basic facts about the integers as normed ring.

Recall that `‖n‖` denotes the norm of `n` as real number.
This norm is always nonnegative, so we can bundle the norm together with this fact,
to obtain a term of type `NNReal` (the nonnegative real numbers).
The resulting nonnegative real number is denoted by `‖n‖₊`.
-/

public section


namespace Int

/-
**Int.nnnorm_coe_units** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：nnnorm_coe_units (e : Intˣ) : ‖(e : Int)‖₊ = 1
参数：e : Intˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Int.units_eq_one_or`：units_eq_one_or (u : Intˣ) : u = 1 ∨ u = -1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nnnorm_one`：∀ {G : Type u_1} [inst : SeminormedAddCommGroup G] [inst_1 :
 One G] [NormOneClass G], ‖1‖₊ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nnnorm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖
₊ = ‖a‖₊
-/
theorem nnnorm_coe_units (e : ℤˣ) : ‖(e : ℤ)‖₊ = 1 := by
  obtain rfl | rfl := units_eq_one_or e <;>
    simp only [Units.coe_neg_one, Units.val_one, nnnorm_neg, nnnorm_one]
/-
**Int.norm_coe_units** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：norm_coe_units (e : Intˣ) : ‖(e : Int)‖ = 1
参数：e : Intˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `coe_nnnorm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ↑‖a‖
₊ = ‖a‖
· 使用定理 `Int.nnnorm_coe_units`：nnnorm_coe_units (e : Intˣ) : ‖(e : Int)‖₊ = 1
· 使用定理 `NNReal.coe_one`：↑1 = 1
-/
theorem norm_coe_units (e : ℤˣ) : ‖(e : ℤ)‖ = 1 := by
  rw [← coe_nnnorm, nnnorm_coe_units, NNReal.coe_one]

@[simp]
/-
**Int.nnnorm_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：nnnorm_natCast (n : Nat) : ‖(n : Int)‖₊ = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.nnnorm_natCast`：∀ (n : ℕ), ‖↑n‖₊ = ↑n
-/
theorem nnnorm_natCast (n : ℕ) : ‖(n : ℤ)‖₊ = n :=
  Real.nnnorm_natCast _
/-
**Int.enorm_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ (n : ℕ), ‖↑n‖ₑ = ↑n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.enorm_natCast`：∀ (n : ℕ), ‖↑n‖ₑ = ↑n
-/
@[simp] lemma enorm_natCast (n : ℕ) : ‖(n : ℤ)‖ₑ = n := Real.enorm_natCast _

@[simp]
/-
**Int.toNat_add_toNat_neg_eq_nnnorm** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：toNat_add_toNat_neg_eq_nnnorm (n : Int) : ↑n.toNat + ↑(-n).toNat = ‖n‖₊
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Int.toNat_add_toNat_neg_eq_natAbs`：∀ (n : ℤ), n.toNat + (-n).toNat = n.n
atAbs
· 使用定理 `NNReal.natCast_natAbs`：∀ (n : ℤ), ↑n.natAbs = ‖n‖₊
-/
theorem toNat_add_toNat_neg_eq_nnnorm (n : ℤ) : ↑n.toNat + ↑(-n).toNat = ‖n‖₊ := by
  rw [← Nat.cast_add, toNat_add_toNat_neg_eq_natAbs, NNReal.natCast_natAbs]

@[simp]
/-
**Int.toNat_add_toNat_neg_eq_norm** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：toNat_add_toNat_neg_eq_norm (n : Int) : ↑n.toNat + ↑(-n).toNat = ‖n‖
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NNReal.coe_natCast`：∀ (n : ℕ), ↑↑n = ↑n
· 使用定理 `Int.toNat_add_toNat_neg_eq_nnnorm`：toNat_add_toNat_neg_eq_nnnorm (n : In
t) : ↑n.toNat + ↑(-n).toNat = ‖n‖₊
-/
theorem toNat_add_toNat_neg_eq_norm (n : ℤ) : ↑n.toNat + ↑(-n).toNat = ‖n‖ := by
  simpa only [NNReal.coe_natCast, NNReal.coe_add] using!
    congrArg NNReal.toReal (toNat_add_toNat_neg_eq_nnnorm n)

end Int

