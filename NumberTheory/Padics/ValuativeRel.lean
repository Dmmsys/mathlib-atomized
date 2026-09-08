/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.Valuation.RankOne

/-!
# p-adic numbers with a valuative relation

## Tags

p-adic, p adic, padic, norm, valuation, cauchy, completion, p-adic completion
-/

public section

variable {p : ℕ} [hp : Fact p.Prime] {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]
    (v : Valuation ℚ_[p] Γ₀)

open ValuativeRel WithZero

namespace Padic

-- TODO: should this be automatic from a nonarchimedean nontrivially normed field?
/-
**Padic.** 是 Mathlib 中的一个实例，位于命名空间 `Padic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : ValuativeRel ℚ_[p] := .ofValuation mulValuation
/-
**Padic.** 是 Mathlib 中的一个实例，位于命名空间 `Padic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Valuation.Compatible (mulValuation (p := p)) := .ofValuation _

variable [v.Compatible]
/-
**Padic.valuation_p_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Padic`。
形式化陈述：valuation_p_ne_zero : v p != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `Valuation.IsEquiv.eq_zero`：eq_zero (h : v₁.IsEquiv v₂) {r : R} : v₁ r = 
0 ↔ v₂ r = 0
· 使用引理 `ValuativeRel.isEquiv`：isEquiv {Γ₁ Γ₂ : Type*} [LinearOrderedCommMonoidWi
thZero Γ₁] [LinearOrderedCommMonoidWithZero Γ₂] (v₁ : Valuation R Γ₁) (v₂ : Valu
ation R Γ₂…
· 使用定理 `Padic.instCompatibleWithZeroMultiplicativeIntMulValuation`：∀ {p : ℕ} [hp
 : Fact (Nat.Prime p)], Padic.mulValuation.Compatible
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Padic.mulValuation_toFun`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (x : ℚ_[p]
), Padic.mulValuation x = if x = 0 then 0 else WithZero.exp (-x.valuation)
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Padic.instCharZero`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)], CharZero ℚ_[p
]
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用引理 `Padic.valuation_natCast`：valuation_natCast (n : Nat) : valuation (n : Ra
t_[p]) = padicValNat p n
· 使用定理 `padicValNat_self`：padicValNat_self [Fact p.Prime] : padicValNat p p = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma valuation_p_ne_zero : v p ≠ 0 := by
  simp [(isEquiv v (Padic.mulValuation)).eq_zero, hp.out.ne_zero]

@[simp]
/-
**Padic.valuation_p_lt_one** 是 Mathlib 中的一个引理，位于命名空间 `Padic`。
形式化陈述：valuation_p_lt_one : v p < 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用引理 `Valuation.IsEquiv.lt_one_iff_lt_one`：lt_one_iff_lt_one (h : v₁.IsEquiv v
₂) {x : R} : v₁ x < 1 ↔ v₂ x < 1
· 使用引理 `ValuativeRel.isEquiv`：isEquiv {Γ₁ Γ₂ : Type*} [LinearOrderedCommMonoidWi
thZero Γ₁] [LinearOrderedCommMonoidWithZero Γ₂] (v₁ : Valuation R Γ₁) (v₂ : Valu
ation R Γ₂…
· 使用定理 `Padic.instCompatibleWithZeroMultiplicativeIntMulValuation`：∀ {p : ℕ} [hp
 : Fact (Nat.Prime p)], Padic.mulValuation.Compatible
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Padic.mulValuation_toFun`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (x : ℚ_[p]
), Padic.mulValuation x = if x = 0 then 0 else WithZero.exp (-x.valuation)
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Padic.instCharZero`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)], CharZero ℚ_[p
]
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用引理 `Padic.valuation_natCast`：valuation_natCast (n : Nat) : valuation (n : Ra
t_[p]) = padicValNat p n
· 使用定理 `padicValNat_self`：padicValNat_self [Fact p.Prime] : padicValNat p p = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `instPosMulStrictMonoWithZeroOfMulLeftStrictMono`：∀ {α : Type u_1} [inst 
: Mul α] [inst_1 : Preorder α] [MulLeftStrictMono α], PosMulStrictMono (WithZero
 α)
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `WithZero.instNontrivial`：∀ {α : Type u} [Nonempty α], Nontrivial (WithZe
ro α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma valuation_p_lt_one : v p < 1 := by
  simp [(isEquiv v (Padic.mulValuation)).lt_one_iff_lt_one, hp.out.ne_zero, inv_lt_one₀,
    ← log_lt_iff_lt_exp]
/-
**Padic.** 是 Mathlib 中的一个实例，位于命名空间 `Padic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsNontrivial ℚ_[p] where
  condition := ⟨ValuativeRel.valuation _ p, valuation_p_ne_zero _, (valuation_p_lt_one _).ne⟩
/-
**Padic.** 是 Mathlib 中的一个实例，位于命名空间 `Padic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsRankLeOne ℚ_[p] := .of_compatible_mulArchimedean mulValuation

end Padic

