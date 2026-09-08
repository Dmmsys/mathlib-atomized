/-
Copyright (c) 2025 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Kevin Klinge, Andrew Yang
-/
module

public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.RingTheory.OreLocalization.Basic

/-!
# Ore Localization over nonZeroDivisors in monoids with zeros.
-/

@[expose] public section

open scoped nonZeroDivisors

namespace OreLocalization

section MonoidWithZero

variable {R : Type*} [MonoidWithZero R] {S : Submonoid R} [OreSet S]

/-
**OreLocalization.nontrivial_of_nonZeroDivisorsLeft** 是 Mathlib 中的一个定理，位于命名空间 `O
reLocalization`。
形式化陈述：nontrivial_of_nonZeroDivisorsLeft [Nontrivial R] (hS : S <= nonZeroDivisor
sLeft R) : Nontrivial R[S⁻¹]
参数：hS : S <= nonZeroDivisorsLeft R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `OreLocalization.nontrivial_iff`：nontrivial_iff : Nontrivial R[S⁻¹] ↔ 0 ∉
 S
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem nontrivial_of_nonZeroDivisorsLeft [Nontrivial R] (hS : S ≤ nonZeroDivisorsLeft R) :
    Nontrivial R[S⁻¹] :=
  nontrivial_iff.mpr (fun e ↦ one_ne_zero <| hS e 1 (zero_mul _))
/-
**OreLocalization.nontrivial_of_nonZeroDivisorsRight** 是 Mathlib 中的一个定理，位于命名空间 `
OreLocalization`。
形式化陈述：nontrivial_of_nonZeroDivisorsRight [Nontrivial R] (hS : S <= nonZeroDiviso
rsRight R) : Nontrivial R[S⁻¹]
参数：hS : S <= nonZeroDivisorsRight R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `OreLocalization.nontrivial_iff`：nontrivial_iff : Nontrivial R[S⁻¹] ↔ 0 ∉
 S
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem nontrivial_of_nonZeroDivisorsRight [Nontrivial R] (hS : S ≤ nonZeroDivisorsRight R) :
    Nontrivial R[S⁻¹] :=
  nontrivial_iff.mpr (fun e ↦ one_ne_zero <| hS e 1 (mul_zero _))
/-
**OreLocalization.nontrivial_of_nonZeroDivisors** 是 Mathlib 中的一个定理，位于命名空间 `OreLo
calization`。
形式化陈述：nontrivial_of_nonZeroDivisors [Nontrivial R] (hS : S <= R⁰) : Nontrivial R
[S⁻¹]
参数：hS : S <= R⁰。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OreLocalization.nontrivial_of_nonZeroDivisorsLeft`：nontrivial_of_nonZero
DivisorsLeft [Nontrivial R] (hS : S <= nonZeroDivisorsLeft R) : Nontrivial R[S⁻¹
]
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem nontrivial_of_nonZeroDivisors [Nontrivial R] (hS : S ≤ R⁰) :
    Nontrivial R[S⁻¹] :=
  nontrivial_of_nonZeroDivisorsLeft (hS.trans inf_le_left)

variable [Nontrivial R] [OreSet R⁰]
/-
**OreLocalization.nontrivial** 是 Mathlib 中的一个实例，位于命名空间 `OreLocalization`。
形式化陈述：nontrivial : Nontrivial R[R⁰⁻¹]
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `OreLocalization.nontrivial_of_nonZeroDivisors`：nontrivial_of_nonZeroDivi
sors [Nontrivial R] (hS : S <= R⁰) : Nontrivial R[S⁻¹]
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
-/
instance nontrivial : Nontrivial R[R⁰⁻¹] :=
  nontrivial_of_nonZeroDivisors (refl R⁰)

variable [NoZeroDivisors R]

open scoped Classical in
/-- The inversion of Ore fractions for a ring without zero divisors, satisfying `0⁻¹ = 0` and
`(r /ₒ r')⁻¹ = r' /ₒ r` for `r ≠ 0`. -/
@[irreducible]
/-
**OreLocalization.inv** 是 Mathlib 中的一个定义，位于命名空间 `OreLocalization`。
形式化陈述：{R : Type u_1} →   [inst : MonoidWithZero R] →     [Nontrivial R] →       
[inst_2 : OreLocalization.OreSet (nonZeroDivisors R)] →         [NoZeroDivisors 
R] → OreLocalization (nonZeroDivisors R) R → OreLocalization (nonZeroDivisors R)
 R
参数：nonZeroDivisors R；nonZeroDivisors R；nonZeroDivisors R。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `mem_nonZeroDivisors_of_ne_zero`：mem_nonZeroDivisors_of_ne_zero (hx : x !
= 0) : x in M₀⁰

--- 原说明 ---
The inversion of Ore fractions for a ring without zero divisors, satisfying `0⁻¹
 = 0` and
`(r /ₒ r')⁻¹ = r' /ₒ r` for `r ≠ 0`.
-/
protected noncomputable def inv : R[R⁰⁻¹] → R[R⁰⁻¹] :=
  liftExpand
    (fun r s =>
      if hr : r = (0 : R) then (0 : R[R⁰⁻¹])
      else s /ₒ ⟨r, mem_nonZeroDivisors_of_ne_zero hr⟩)
    (by
      intro r t s hst
      by_cases hr : r = 0
      · simp [hr]
      · by_cases ht : t = 0
        · exfalso
          apply nonZeroDivisors.coe_ne_zero ⟨_, hst⟩
          simp [ht]
        · simp only [hr, ht, dif_neg, not_false_iff, or_self_iff, mul_eq_zero, smul_eq_mul]
          apply OreLocalization.expand)
/-
**OreLocalization.inv'** 是 Mathlib 中的一个实例，位于命名空间 `OreLocalization`。
形式化陈述：inv' : Inv R[R⁰⁻¹]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance inv' : Inv R[R⁰⁻¹] :=
  ⟨OreLocalization.inv⟩

open scoped Classical in
/-
**OreLocalization.inv_def** 是 Mathlib 中的一个定理，位于命名空间 `OreLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : MonoidWithZero R] [inst_1 : Nontrivial R] [inst_2
 : OreLocalization.OreSet (nonZeroDivisors R)]   [inst_3 : NoZeroDivisors R] {r 
: R} {s : ↥(nonZeroDivisors R)}, (r /ₒ s)⁻¹ = if hr : r = 0 then 0 else ↑s /ₒ ⟨r
, ⋯⟩
参数：nonZeroDivisors R；nonZeroDivisors R；r /ₒ s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem inv_def {r : R} {s : R⁰} :
    (r /ₒ s)⁻¹ =
      if hr : r = (0 : R) then (0 : R[R⁰⁻¹])
      else s /ₒ ⟨r, mem_nonZeroDivisors_of_ne_zero hr⟩ := by
  with_unfolding_all rfl
/-
**OreLocalization.mul_inv_cancel** 是 Mathlib 中的一个定理，位于命名空间 `OreLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : MonoidWithZero R] [inst_1 : Nontrivial R] [inst_2
 : OreLocalization.OreSet (nonZeroDivisors R)]   [inst_3 : NoZeroDivisors R] (x 
: OreLocalization (nonZeroDivisors R) R), x ≠ 0 → x * x⁻¹ = 1
参数：nonZeroDivisors R；x : OreLocalization (nonZeroDivisors R) R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OreLocalization.ind`：∀ {R : Type u_1} [inst : Monoid R] {S : Submonoid R
} [inst_1 : OreLocalization.OreSet S] {X : Type u_2}   [inst_2 : MulAction R X] 
{β : OreL…
· 使用定理 `mem_nonZeroDivisors_of_ne_zero`：mem_nonZeroDivisors_of_ne_zero (hx : x !
= 0) : x in M₀⁰
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OreLocalization.inv_def`：∀ {R : Type u_1} [inst : MonoidWithZero R] [ins
t_1 : Nontrivial R] [inst_2 : OreLocalization.OreSet (nonZeroDivisors R)]   [ins
t_3 : NoZeroD…
· 使用定理 `OreLocalization.one_def`：∀ {R : Type u_1} [inst : Monoid R] {S : Submono
id R} [inst_1 : OreLocalization.OreSet S] {X : Type u_2}   [inst_2 : MulAction R
 X] [inst_3 :…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `OreLocalization.zero_oreDiv'`：zero_oreDiv' (s : S) : (0 : R) /ₒ s = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `OreLocalization.mul_inv`：∀ {R : Type u_1} [inst : Monoid R] {S : Submono
id R} [inst_1 : OreLocalization.OreSet S] (s s' : ↥S),   ↑s /ₒ s' * (↑s' /ₒ s) =
 1
· 使用定理 `not_false`：¬False
-/
protected theorem mul_inv_cancel (x : R[R⁰⁻¹]) (h : x ≠ 0) : x * x⁻¹ = 1 := by
  induction x with | _ r s
  rw [OreLocalization.inv_def, OreLocalization.one_def]
  have hr : r ≠ 0 := by
    rintro rfl
    simp at h
  simp only [hr]
  with_unfolding_all apply OreLocalization.mul_inv ⟨r, _⟩
/-
**OreLocalization.inv_zero** 是 Mathlib 中的一个定理，位于命名空间 `OreLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : MonoidWithZero R] [inst_1 : Nontrivial R] [inst_2
 : OreLocalization.OreSet (nonZeroDivisors R)]   [inst_3 : NoZeroDivisors R], 0⁻
¹ = 0
参数：nonZeroDivisors R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OreLocalization.zero_def`：∀ {R : Type u_1} [inst : Monoid R] {S : Submon
oid R} [inst_1 : OreLocalization.OreSet S] {X : Type u_2}   [inst_2 : Zero X] [i
nst_3 : MulAct…
· 使用定理 `mem_nonZeroDivisors_of_ne_zero`：mem_nonZeroDivisors_of_ne_zero (hx : x !
= 0) : x in M₀⁰
· 使用定理 `OreLocalization.inv_def`：∀ {R : Type u_1} [inst : MonoidWithZero R] [ins
t_1 : Nontrivial R] [inst_2 : OreLocalization.OreSet (nonZeroDivisors R)]   [ins
t_3 : NoZeroD…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `OreLocalization.zero_oreDiv'`：zero_oreDiv' (s : S) : (0 : R) /ₒ s = 0
-/
protected theorem inv_zero : (0 : R[R⁰⁻¹])⁻¹ = 0 := by
  rw [OreLocalization.zero_def, OreLocalization.inv_def]
  simp
/-
**OreLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `OreLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : GroupWithZero R[R⁰⁻¹] where
  inv_zero := OreLocalization.inv_zero
  mul_inv_cancel := OreLocalization.mul_inv_cancel

end MonoidWithZero

section CommMonoidWithZero

variable {R : Type*} [CommMonoidWithZero R] [Nontrivial R] [OreSet R⁰] [NoZeroDivisors R]

/-
**OreLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `OreLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : CommGroupWithZero R[R⁰⁻¹] where

end CommMonoidWithZero

end OreLocalization

