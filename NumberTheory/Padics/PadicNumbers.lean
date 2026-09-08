/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
module

public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.NumberTheory.Padics.PadicNorm
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Tactic.Peel
public import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
# p-adic numbers

This file defines the `p`-adic numbers (rationals) `ℚ_[p]` as
the completion of `ℚ` with respect to the `p`-adic norm.
We show that the `p`-adic norm on `ℚ` extends to `ℚ_[p]`, that `ℚ` is embedded in `ℚ_[p]`,
and that `ℚ_[p]` is Cauchy complete.

## Important definitions

* `Padic` : the type of `p`-adic numbers
* `padicNormE` : the rational-valued `p`-adic norm on `ℚ_[p]`
* `Padic.addValuation` : the additive `p`-adic valuation on `ℚ_[p]`, with values in `WithTop ℤ`

## Notation

We introduce the notation `ℚ_[p]` for the `p`-adic numbers.

## Implementation notes

Much, but not all, of this file assumes that `p` is prime. This assumption is inferred automatically
by taking `[Fact p.Prime]` as a type class argument.

We use the same concrete Cauchy sequence construction that is used to construct `ℝ`.
`ℚ_[p]` inherits a field structure from this construction.
The extension of the norm on `ℚ` to `ℚ_[p]` is *not* analogous to extending the absolute value to
`ℝ` and hence the proof that `ℚ_[p]` is complete is different from the proof that ℝ is complete.

`padicNormE` is the rational-valued `p`-adic norm on `ℚ_[p]`.
To instantiate `ℚ_[p]` as a normed field, we must cast this into an `ℝ`-valued norm.
The `ℝ`-valued norm, using notation `‖ ‖` from normed spaces,
is the canonical representation of this norm.

`simp` prefers `padicNorm` to `padicNormE` when possible.
Since `padicNormE` and `‖ ‖` have different types, `simp` does not rewrite one to the other.

Coercions from `ℚ` to `ℚ_[p]` are set up to work with the `norm_cast` tactic.

## References

* [F. Q. Gouvêa, *p-adic numbers*][gouvea1997]
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/P-adic_number>

## Tags

p-adic, p adic, padic, norm, valuation, cauchy, completion, p-adic completion
-/

@[expose] public section

open WithZero

-- TODO: fix non-terminal simp; acts on 8 goals, leaving one
set_option linter.flexible false in
/-- The p-adic valuation on rationals, sending `p` to `(exp (-1) : ℤᵐ⁰)` -/
/-
**Rat.padicValuation** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Rat.padicValuation (p : Nat) [Fact p.Prime] : Valuation Rat Intᵐ⁰ where to
Fun x
参数：p : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The p-adic valuation on rationals, sending `p` to `(exp (-1) : ℤᵐ⁰)`
-/
def Rat.padicValuation (p : ℕ) [Fact p.Prime] : Valuation ℚ ℤᵐ⁰ where
  toFun x := if x = 0 then 0 else exp (-padicValRat p x)
  map_zero' := by simp
  map_one' := by simp
  map_mul' := by
    intros
    split_ifs <;>
    simp_all [padicValRat.mul, exp_add, mul_comm]
  map_add_le_max' := by
    intros
    split_ifs
    any_goals simp_all [-exp_neg]
    rw [← min_le_iff]
    exact padicValRat.min_le_padicValRat_add ‹_›

/-- The p-adic valuation on integers, sending `p` to `(exp (-1) : ℤᵐ⁰)` -/
/-
**Int.padicValuation** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Int.padicValuation (p : Nat) [Fact p.Prime] : Valuation Int Intᵐ⁰
参数：p : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The p-adic valuation on integers, sending `p` to `(exp (-1) : ℤᵐ⁰)`
-/
def Int.padicValuation (p : ℕ) [Fact p.Prime] : Valuation ℤ ℤᵐ⁰ :=
  (Rat.padicValuation p).comap (Int.castRingHom ℚ)
/-
**Rat.padicValuation_cast** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Rat.padicValuation_cast (p : Nat) [Fact p.Prime] (x : Int) : Rat.padicValu
ation p (Int.cast x) = Int.padicValuation p x
参数：p : Nat；x : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
-/
lemma Rat.padicValuation_cast (p : ℕ) [Fact p.Prime] (x : ℤ) :
    Rat.padicValuation p (Int.cast x) = Int.padicValuation p x :=
  rfl
/-
**Rat.padicValuation_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Rat.padicValuation_eq_zero_iff {p : Nat} [Fact p.Prime] {x : Rat} : Rat.pa
dicValuation p x = 0 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithZero.instNontrivial`：∀ {α : Type u} [Nonempty α], Nontrivial (WithZe
ro α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Rat.padicValuation_eq_zero_iff {p : ℕ} [Fact p.Prime] {x : ℚ} :
    Rat.padicValuation p x = 0 ↔ x = 0 := by
  simp

@[simp]
/-
**Int.padicValuation_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Int.padicValuation_eq_zero_iff {p : Nat} [Fact p.Prime] {x : Int} : Int.pa
dicValuation p x = 0 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithZero.instNontrivial`：∀ {α : Type u} [Nonempty α], Nontrivial (WithZe
ro α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Int.padicValuation_eq_zero_iff {p : ℕ} [Fact p.Prime] {x : ℤ} :
    Int.padicValuation p x = 0 ↔ x = 0 := by
  simp [← Rat.padicValuation_cast]

@[simp]
/-
**Rat.padicValuation_self** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Rat.padicValuation_self (p : Nat) [Fact p.Prime] : Rat.padicValuation p p 
= exp (-1)
参数：p : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `padicValRat.of_nat`：of_nat {n : Nat} : padicValRat p n = padicValNat p n
· 使用定理 `padicValNat_self`：padicValNat_self [Fact p.Prime] : padicValNat p p = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Rat.padicValuation_self (p : ℕ) [Fact p.Prime] :
    Rat.padicValuation p p = exp (-1) := by
  simp [Rat.padicValuation, Nat.Prime.ne_zero Fact.out]

@[simp]
/-
**Int.padicValuation_self** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Int.padicValuation_self (p : Nat) [Fact p.Prime] : Int.padicValuation p p 
= exp (-1)
参数：p : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用引理 `Rat.padicValuation_self`：Rat.padicValuation_self (p : Nat) [Fact p.Prime
] : Rat.padicValuation p p = exp (-1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Int.padicValuation_self (p : ℕ) [Fact p.Prime] :
    Int.padicValuation p p = exp (-1) := by
  simp [← Rat.padicValuation_cast]
/-
**Int.padicValuation_le_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Int.padicValuation_le_one (p : Nat) [Fact p.Prime] (x : Int) : Int.padicVa
luation p x <= 1
参数：p : Nat；x : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `padicValRat.of_int`：of_int {z : Int} : padicValRat p z = padicValInt p z
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `WithZero.instIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α], IsBotZeroCl
ass (WithZero α)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WithZero.le_log_iff_exp_le`：le_log_iff_exp_le (hx : x != 0) : a <= log x
 ↔ exp a <= x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `WithZero.instNontrivial`：∀ {α : Type u} [Nonempty α], Nontrivial (WithZe
ro α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
lemma Int.padicValuation_le_one (p : ℕ) [Fact p.Prime] (x : ℤ) :
    Int.padicValuation p x ≤ 1 := by
  simp only [← Rat.padicValuation_cast, Rat.padicValuation, Valuation.coe_mk,
    MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, Rat.intCast_eq_zero_iff, padicValRat.of_int]
  split_ifs
  · simp
  · rw [← le_log_iff_exp_le] <;>
    simp_all
/-
**Int.padicValuation_eq_one_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Int.padicValuation_eq_one_iff {p : Nat} [Fact p.Prime] {x : Int} : Int.pad
icValuation p x = 1 ↔ ¬ (p : Int) ∣ x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `padicValRat.of_int`：of_int {z : Int} : padicValRat p z = padicValInt p z
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `WithZero.instNontrivial`：∀ {α : Type u} [Nonempty α], Nontrivial (WithZe
ro α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithZero.exp_zero`：∀ {M : Type u_4} [inst : AddMonoid M], WithZero.exp 0
 = 1
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `WithZero.exp_injective`：exp_injective : Injective (exp : M -> Mᵐ⁰)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
lemma Int.padicValuation_eq_one_iff {p : ℕ} [Fact p.Prime] {x : ℤ} :
    Int.padicValuation p x = 1 ↔ ¬ (p : ℤ) ∣ x := by
  simp only [← Rat.padicValuation_cast, Rat.padicValuation, Valuation.coe_mk,
    MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, Rat.intCast_eq_zero_iff, padicValRat.of_int]
  split_ifs
  · simp_all
  · rw [← exp_zero, exp_injective.eq_iff]
    simp_all [Nat.Prime.ne_one Fact.out]
/-
**Int.padicValuation_lt_one_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Int.padicValuation_lt_one_iff {p : Nat} [Fact p.Prime] {x : Int} : Int.pad
icValuation p x < 1 ↔ (p : Int) ∣ x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Int.padicValuation_lt_one_iff {p : ℕ} [Fact p.Prime] {x : ℤ} :
    Int.padicValuation p x < 1 ↔ (p : ℤ) ∣ x := by
  simp [lt_iff_le_and_ne, padicValuation_eq_one_iff, Int.padicValuation_le_one]
/-
**Rat.padicValuation_le_one_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Rat.padicValuation_le_one_iff {p : Nat} [Fact p.Prime] {x : Rat} : Rat.pad
icValuation p x <= 1 ↔ ¬ p ∣ x.den
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Rat.num_div_den`：num_div_den (r : Rat) : (r.num : Rat) / (r.den : Rat) =
 r
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Int.natCast_dvd_natCast`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
· 使用引理 `Int.padicValuation_eq_one_iff`：Int.padicValuation_eq_one_iff {p : Nat} [
Fact p.Prime] {x : Int} : Int.padicValuation p x = 1 ↔ ¬ (p : Int) ∣ x
· 使用引理 `Rat.padicValuation_cast`：Rat.padicValuation_cast (p : Nat) [Fact p.Prime
] (x : Int) : Rat.padicValuation p (Int.cast x) = Int.padicValuation p x
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用引理 `div_le_one₀`：div_le_one₀ (hb : 0 < b) : a / b <= 1 ↔ a <= b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `instMulPosStrictMonoWithZeroOfMulRightStrictMono`：∀ {α : Type u_1} [inst
 : Mul α] [inst_1 : Preorder α] [MulRightStrictMono α], MulPosStrictMono (WithZe
ro α)
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `WithZero.instIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α], IsBotZeroCl
ass (WithZero α)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用引理 `Int.padicValuation_le_one`：Int.padicValuation_le_one (p : Nat) [Fact p.P
rime] (x : Int) : Int.padicValuation p x <= 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
（共 41 条，此处仅展示前 30 条）
-/
lemma Rat.padicValuation_le_one_iff {p : ℕ} [Fact p.Prime] {x : ℚ} :
    Rat.padicValuation p x ≤ 1 ↔ ¬ p ∣ x.den := by
  nth_rw 1 [← x.num_div_den, map_div₀, ← Int.natCast_dvd_natCast, ← Int.padicValuation_eq_one_iff,
    Rat.padicValuation_cast, ← Int.cast_natCast, Rat.padicValuation_cast, div_le_one₀]
  · rcases (Int.padicValuation_le_one p x.den).eq_or_lt with h | h
    · simp [h, Int.padicValuation_le_one]
    · simp only [h.ne, iff_false, not_le]
      rcases (Int.padicValuation_le_one p x.num).eq_or_lt with h' | h'
      · simp [h, h']
      · rw [Int.padicValuation_lt_one_iff] at h h'
        exfalso
        rw [Int.natCast_dvd_natCast] at h
        rw [Int.natCast_dvd] at h'
        exact Nat.not_coprime_of_dvd_of_dvd (Nat.Prime.one_lt Fact.out) h h' x.reduced.symm
  · simp [zero_lt_iff]
/-
**Rat.surjective_padicValuation** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Rat.surjective_padicValuation (p : Nat) [hp : Fact (p.Prime)] : Function.S
urjective (Rat.padicValuation p)
参数：p : Nat；p.Prime。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `WithZero.instNontrivial`：∀ {α : Type u} [Nonempty α], Nontrivial (WithZe
ro α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `padicValRat.inv`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (q : ℚ), padicValRa
t p q⁻¹ = -padicValRat p q
· 使用定理 `padicValRat.pow`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (q : ℚ) {k : ℕ}, pa
dicValRat p (q ^ k) = ↑k * padicValRat p q
· 使用定理 `Nat.cast_natAbs`：∀ {α : Type u_1} [inst : AddGroupWithOne α] (n : ℤ), ↑n
.natAbs = ↑|n|
· 使用引理 `Int.cast_abs`：cast_abs : (↑|a| : R) = |(a : R)|
· 使用定理 `padicValRat.of_nat`：of_nat {n : Nat} : padicValRat p n = padicValNat p n
· 使用定理 `padicValNat_self`：padicValNat_self [Fact p.Prime] : padicValNat p p = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
（共 35 条，此处仅展示前 30 条）
-/
theorem Rat.surjective_padicValuation (p : ℕ) [hp : Fact (p.Prime)] :
    Function.Surjective (Rat.padicValuation p) := by
  intro x
  induction x with
  | zero => simp
  | coe x =>
    induction x with | ofAdd x
    simp_rw [Rat.padicValuation, WithZero.exp, Valuation.coe_mk, MonoidWithZeroHom.coe_mk]
    rcases le_or_gt 0 x with (hx | hx)
    · exact ⟨(p ^ x.natAbs)⁻¹, by simp [hp.out.ne_zero, hx]⟩
    · exact ⟨p ^ x.natAbs, by simp [hp.out.ne_zero, padicValRat.pow, abs_eq_neg_self.2 hx.le]⟩

noncomputable section

open Nat padicNorm CauSeq CauSeq.Completion Metric

/-- The type of Cauchy sequences of rationals with respect to the `p`-adic norm. -/
/-
**PadicSeq** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：PadicSeq (p : Nat)
参数：p : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of Cauchy sequences of rationals with respect to the `p`-adic norm.
-/
abbrev PadicSeq (p : ℕ) :=
  CauSeq _ (padicNorm p)

namespace PadicSeq

section

variable {p : ℕ} [Fact p.Prime]

/-- The `p`-adic norm of the entries of a nonzero Cauchy sequence of rationals is eventually
constant. -/
/-
**PadicSeq.stationary** 是 Mathlib 中的一个定理，位于命名空间 `PadicSeq`。
形式化陈述：stationary {f : CauSeq Rat (padicNorm p)} (hf : ¬f ≈ 0) : exists N, forall
 m n, N <= m -> N <= n -> padicNorm p (f n) = padicNorm p (f m)
参数：padicNorm p；hf : ¬f ≈ 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)
· 使用定理 `CauSeq.abv_pos_of_not_limZero`：abv_pos_of_not_limZero {f : CauSeq β abv}
 (hf : ¬LimZero f) : exists K > 0, exists i, forall j >= i, K <= abv (f j)
· 使用定理 `CauSeq.not_limZero_of_not_congr_zero`：not_limZero_of_not_congr_zero {f :
 CauSeq _ abv} (hf : ¬f ≈ 0) : ¬LimZero f
· 使用定理 `CauSeq.cauchy₂`：cauchy₂ (f : CauSeq β abv) {ε} : 0 < ε -> exists i, fora
ll j >= i, forall k >= i, abv (f j - f k) < ε
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `max_le_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, max a b ≤
 c ↔ a ≤ c ∧ b ≤ c
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_max_iff`：lt_max_iff : a < max b c ↔ a < b ∨ a < c
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `padicNorm.add_eq_max_of_ne`：add_eq_max_of_ne {q r : Rat} (hne : padicNor
m p q != padicNorm p r) : padicNorm p (q + r) = max (padicNorm p q) (padicNorm p
 r)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `padicNorm.neg`：∀ {p : ℕ} (q : ℚ), padicNorm p (-q) = padicNorm p q
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `max_comm`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), max a b = m
ax b a

--- 原说明 ---
The `p`-adic norm of the entries of a nonzero Cauchy sequence of rationals is ev
entually
constant.
-/
theorem stationary {f : CauSeq ℚ (padicNorm p)} (hf : ¬f ≈ 0) :
    ∃ N, ∀ m n, N ≤ m → N ≤ n → padicNorm p (f n) = padicNorm p (f m) :=
  have : ∃ ε > 0, ∃ N1, ∀ j ≥ N1, ε ≤ padicNorm p (f j) :=
    CauSeq.abv_pos_of_not_limZero <| not_limZero_of_not_congr_zero hf
  let ⟨ε, hε, N1, hN1⟩ := this
  let ⟨N2, hN2⟩ := CauSeq.cauchy₂ f hε
  ⟨max N1 N2, fun n m hn hm ↦ by
    have : padicNorm p (f n - f m) < ε := hN2 _ (max_le_iff.1 hn).2 _ (max_le_iff.1 hm).2
    have : padicNorm p (f n - f m) < padicNorm p (f n) :=
      lt_of_lt_of_le this <| hN1 _ (max_le_iff.1 hn).1
    have : padicNorm p (f n - f m) < max (padicNorm p (f n)) (padicNorm p (f m)) :=
      lt_max_iff.2 (Or.inl this)
    by_contra hne
    rw [← padicNorm.neg (f m)] at hne
    have hnam := add_eq_max_of_ne hne
    rw [padicNorm.neg, max_comm] at hnam
    rw [← hnam, sub_eq_add_neg, add_comm] at this
    apply _root_.lt_irrefl _ this⟩

/-- For all `n ≥ stationaryPoint f hf`, the `p`-adic norm of `f n` is the same. -/
/-
**PadicSeq.stationaryPoint** 是 Mathlib 中的一个定义，位于命名空间 `PadicSeq`。
形式化陈述：stationaryPoint {f : PadicSeq p} (hf : ¬f ≈ 0) : Nat
参数：hf : ¬f ≈ 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)
· 使用定理 `PadicSeq.stationary`：stationary {f : CauSeq Rat (padicNorm p)} (hf : ¬f 
≈ 0) : exists N, forall m n, N <= m -> N <= n -> padicNorm p (f n) = padicNorm p
 (f m)

--- 原说明 ---
For all `n ≥ stationaryPoint f hf`, the `p`-adic norm of `f n` is the same.
-/
def stationaryPoint {f : PadicSeq p} (hf : ¬f ≈ 0) : ℕ :=
  Classical.choose <| stationary hf
/-
**PadicSeq.stationaryPoint_spec** 是 Mathlib 中的一个定理，位于命名空间 `PadicSeq`。
形式化陈述：stationaryPoint_spec {f : PadicSeq p} (hf : ¬f ≈ 0) : forall {m n}, statio
naryPoint hf <= m -> stationaryPoint hf <= n -> padicNorm p (f n) = padicNorm p 
(f m)
参数：hf : ¬f ≈ 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `PadicSeq.stationary`：stationary {f : CauSeq Rat (padicNorm p)} (hf : ¬f 
≈ 0) : exists N, forall m n, N <= m -> N <= n -> padicNorm p (f n) = padicNorm p
 (f m)
-/
theorem stationaryPoint_spec {f : PadicSeq p} (hf : ¬f ≈ 0) :
    ∀ {m n},
      stationaryPoint hf ≤ m → stationaryPoint hf ≤ n → padicNorm p (f n) = padicNorm p (f m) :=
  @(Classical.choose_spec <| stationary hf)

open scoped Classical in
/-- Since the norm of the entries of a Cauchy sequence is eventually stationary,
we can lift the norm to sequences. -/
/-
**PadicSeq.norm** 是 Mathlib 中的一个定义，位于命名空间 `PadicSeq`。
形式化陈述：norm (f : PadicSeq p) : Rat
参数：f : PadicSeq p。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)

--- 原说明 ---
Since the norm of the entries of a Cauchy sequence is eventually stationary,
we can lift the norm to sequences.
-/
def norm (f : PadicSeq p) : ℚ :=
  if hf : f ≈ 0 then 0 else padicNorm p (f (stationaryPoint hf))
/-
**PadicSeq.norm_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `PadicSeq`。
形式化陈述：norm_zero_iff (f : PadicSeq p) : f.norm = 0 ↔ f ≈ 0
参数：f : PadicSeq p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `PadicSeq.stationaryPoint_spec`：stationaryPoint_spec {f : PadicSeq p} (hf
 : ¬f ≈ 0) : forall {m n}, stationaryPoint hf <= m -> stationaryPoint hf <= n ->
 padicNorm p (f n) …
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_zero_iff (f : PadicSeq p) : f.norm = 0 ↔ f ≈ 0 := by
  constructor
  · intro h
    by_contra hf
    unfold norm at h
    split_ifs at h
    apply hf
    intro ε hε
    exists stationaryPoint hf
    intro j hj
    have heq := stationaryPoint_spec hf le_rfl hj
    simpa [h, heq]
  · intro h
    simp [norm, h]

end

section Embedding

open CauSeq

variable {p : ℕ} [Fact p.Prime]

/-
**PadicSeq.equiv_zero_of_val_eq_of_equiv_zero** 是 Mathlib 中的一个定理，位于命名空间 `PadicSe
q`。
形式化陈述：equiv_zero_of_val_eq_of_equiv_zero {f g : PadicSeq p} (h : forall k, padic
Norm p (f k) = padicNorm p (g k)) (hf : f ≈ 0) : g ≈ 0
参数：h : forall k, padicNorm p (f k) = padicNorm p (g k)；hf : f ≈ 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem equiv_zero_of_val_eq_of_equiv_zero {f g : PadicSeq p}
    (h : ∀ k, padicNorm p (f k) = padicNorm p (g k)) (hf : f ≈ 0) : g ≈ 0 := fun ε hε ↦
  let ⟨i, hi⟩ := hf _ hε
  ⟨i, fun j hj ↦ by simpa [h] using hi _ hj⟩
/-
**PadicSeq.norm_nonzero_of_not_equiv_zero** 是 Mathlib 中的一个定理，位于命名空间 `PadicSeq`。
形式化陈述：norm_nonzero_of_not_equiv_zero {f : PadicSeq p} (hf : ¬f ≈ 0) : f.norm != 
0
参数：hf : ¬f ≈ 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PadicSeq.norm_zero_iff`：norm_zero_iff (f : PadicSeq p) : f.norm = 0 ↔ f 
≈ 0
-/
theorem norm_nonzero_of_not_equiv_zero {f : PadicSeq p} (hf : ¬f ≈ 0) : f.norm ≠ 0 :=
  hf ∘ f.norm_zero_iff.1
/-
**PadicSeq.norm_eq_norm_app_of_nonzero** 是 Mathlib 中的一个定理，位于命名空间 `PadicSeq`。
形式化陈述：norm_eq_norm_app_of_nonzero {f : PadicSeq p} (hf : ¬f ≈ 0) : exists k, f.n
orm = padicNorm p k ∧ k != 0
参数：hf : ¬f ≈ 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `PadicSeq.norm_nonzero_of_not_equiv_zero`：norm_nonzero_of_not_equiv_zero 
{f : PadicSeq p} (hf : ¬f ≈ 0) : f.norm != 0
· 使用定理 `padicNorm.zero`：∀ {p : ℕ}, padicNorm p 0 = 0
-/
theorem norm_eq_norm_app_of_nonzero {f : PadicSeq p} (hf : ¬f ≈ 0) :
    ∃ k, f.norm = padicNorm p k ∧ k ≠ 0 :=
  have heq : f.norm = padicNorm p (f <| stationaryPoint hf) := by simp [norm, hf]
  ⟨f <| stationaryPoint hf, heq, fun h ↦
    norm_nonzero_of_not_equiv_zero hf (by simpa [h] using heq)⟩
/-
**PadicSeq.not_limZero_const_of_nonzero** 是 Mathlib 中的一个定理，位于命名空间 `PadicSeq`。
形式化陈述：not_limZero_const_of_nonzero {q : Rat} (hq : q != 0) : ¬LimZero (const (pa
dicNorm p) q)
参数：hq : q != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CauSeq.const_limZero`：const_limZero {x : β} : LimZero (const x) ↔ x = 0
-/
theorem not_limZero_const_of_nonzero {q : ℚ} (hq : q ≠ 0) : ¬LimZero (const (padicNorm p) q) :=
  fun h' ↦ hq <| const_limZero.1 h'
/-
**PadicSeq.not_equiv_zero_const_of_nonzero** 是 Mathlib 中的一个定理，位于命名空间 `PadicSeq`。
形式化陈述：not_equiv_zero_const_of_nonzero {q : Rat} (hq : q != 0) : ¬const (padicNor
m p) q ≈ 0
参数：hq : q != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)
· 使用定理 `PadicSeq.not_limZero_const_of_nonzero`：not_limZero_const_of_nonzero {q :
 Rat} (hq : q != 0) : ¬LimZero (const (padicNorm p) q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
-/
theorem not_equiv_zero_const_of_nonzero {q : ℚ} (hq : q ≠ 0) : ¬const (padicNorm p) q ≈ 0 :=
  fun h : LimZero (const (padicNorm p) q - 0) ↦
    not_limZero_const_of_nonzero (p := p) hq <| by simpa using h
/-
**PadicSeq.norm_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `PadicSeq`。
形式化陈述：norm_nonneg (f : PadicSeq p) : 0 <= f.norm
参数：f : PadicSeq p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
-/
theorem norm_nonneg (f : PadicSeq p) : 0 ≤ f.norm := by
  classical exact if hf : f ≈ 0 then by simp [hf, norm] else by simp [norm, hf, padicNorm.nonneg]

/-- An auxiliary lemma for manipulating sequence indices. -/
/-
**PadicSeq.lift_index_left_left** 是 Mathlib 中的一个定理，位于命名空间 `PadicSeq`。
形式化陈述：lift_index_left_left {f : PadicSeq p} (hf : ¬f ≈ 0) (v2 v3 : Nat) : padicN
orm p (f (stationaryPoint hf)) = padicNorm p (f (max (stationaryPoint hf) (max v
2 v3)))
参数：hf : ¬f ≈ 0；v2 v3 : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)
· 使用定理 `PadicSeq.stationaryPoint_spec`：stationaryPoint_spec {f : PadicSeq p} (hf
 : ¬f ≈ 0) : forall {m n}, stationaryPoint hf <= m -> stationaryPoint hf <= n ->
 padicNorm p (f n) …
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
An auxiliary lemma for manipulating sequence indices.
-/
theorem lift_index_left_left {f : PadicSeq p} (hf : ¬f ≈ 0) (v2 v3 : ℕ) :
    padicNorm p (f (stationaryPoint hf)) =
    padicNorm p (f (max (stationaryPoint hf) (max v2 v3))) := by
  apply stationaryPoint_spec hf
  · apply le_max_left
  · exact le_rfl

/-- An auxiliary lemma for manipulating sequence indices. -/
/-
**PadicSeq.lift_index_left** 是 Mathlib 中的一个定理，位于命名空间 `PadicSeq`。
形式化陈述：lift_index_left {f : PadicSeq p} (hf : ¬f ≈ 0) (v1 v3 : Nat) : padicNorm p
 (f (stationaryPoint hf)) = padicNorm p (f (max v1 (max (stationaryPoint hf) v3)
))
参数：hf : ¬f ≈ 0；v1 v3 : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)
· 使用定理 `PadicSeq.stationaryPoint_spec`：stationaryPoint_spec {f : PadicSeq p} (hf
 : ¬f ≈ 0) : forall {m n}, stationaryPoint hf <= m -> stationaryPoint hf <= n ->
 padicNorm p (f n) …
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
An auxiliary lemma for manipulating sequence indices.
-/
theorem lift_index_left {f : PadicSeq p} (hf : ¬f ≈ 0) (v1 v3 : ℕ) :
    padicNorm p (f (stationaryPoint hf)) =
    padicNorm p (f (max v1 (max (stationaryPoint hf) v3))) := by
  apply stationaryPoint_spec hf
  · apply le_trans
    · apply le_max_left _ v3
    · apply le_max_right
  · exact le_rfl

/-- An auxiliary lemma for manipulating sequence indices. -/
/-
**PadicSeq.lift_index_right** 是 Mathlib 中的一个定理，位于命名空间 `PadicSeq`。
形式化陈述：lift_index_right {f : PadicSeq p} (hf : ¬f ≈ 0) (v1 v2 : Nat) : padicNorm 
p (f (stationaryPoint hf)) = padicNorm p (f (max v1 (max v2 (stationaryPoint hf)
)))
参数：hf : ¬f ≈ 0；v1 v2 : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)
· 使用定理 `PadicSeq.stationaryPoint_spec`：stationaryPoint_spec {f : PadicSeq p} (hf
 : ¬f ≈ 0) : forall {m n}, stationaryPoint hf <= m -> stationaryPoint hf <= n ->
 padicNorm p (f n) …
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
An auxiliary lemma for manipulating sequence indices.
-/
theorem lift_index_right {f : PadicSeq p} (hf : ¬f ≈ 0) (v1 v2 : ℕ) :
    padicNorm p (f (stationaryPoint hf)) =
    padicNorm p (f (max v1 (max v2 (stationaryPoint hf)))) := by
  apply stationaryPoint_spec hf
  · apply le_trans
    · apply le_max_right v2
    · apply le_max_right
  · exact le_rfl

end Embedding

section Valuation

open CauSeq

variable {p : ℕ} [Fact p.Prime]

/-! ### Valuation on `PadicSeq` -/

open scoped Classical in
/-- The `p`-adic valuation on `ℚ` lifts to `PadicSeq p`.
`Valuation f` is defined to be the valuation of the (`ℚ`-valued) stationary point of `f`. -/
/-
**PadicSeq.valuation** 是 Mathlib 中的一个定义，位于命名空间 `PadicSeq`。
形式化陈述：valuation (f : PadicSeq p) : Int
参数：f : PadicSeq p。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)

--- 原说明 ---
The `p`-adic valuation on `ℚ` lifts to `PadicSeq p`.
`Valuation f` is defined to be the valuation of the (`ℚ`-valued) stationary poin
t of `f`.
-/
def valuation (f : PadicSeq p) : ℤ :=
  if hf : f ≈ 0 then 0 else padicValRat p (f (stationaryPoint hf))
/-
**PadicSeq.norm_eq_zpow_neg_valuation** 是 Mathlib 中的一个定理，位于命名空间 `PadicSeq`。
形式化陈述：norm_eq_zpow_neg_valuation {f : PadicSeq p} (hf : ¬f ≈ 0) : f.norm = (p : 
Rat) ^ (-f.valuation : Int)
参数：hf : ¬f ≈ 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PadicSeq.norm.eq_1`：∀ {p : ℕ} [inst : Fact (Nat.Prime p)] (f : PadicSeq 
p),   f.norm = if hf : f ≈ 0 then 0 else padicNorm p (↑f (PadicSeq.stationaryPoi
nt hf))
· 使用定理 `PadicSeq.valuation.eq_1`：∀ {p : ℕ} [inst : Fact (Nat.Prime p)] (f : Padi
cSeq p),   f.valuation = if hf : f ≈ 0 then 0 else padicValRat p (↑f (PadicSeq.s
tationaryPoin…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `padicNorm.eq_1`：∀ (p : ℕ) (q : ℚ), padicNorm p q = if q = 0 then 0 else 
↑p ^ (-padicValRat p q)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `CauSeq.not_limZero_of_not_congr_zero`：not_limZero_of_not_congr_zero {f :
 CauSeq _ abv} (hf : ¬f ≈ 0) : ¬LimZero f
· 使用定理 `PadicSeq.stationaryPoint_spec`：stationaryPoint_spec {f : PadicSeq p} (hf
 : ¬f ≈ 0) : forall {m n}, stationaryPoint hf <= m -> stationaryPoint hf <= n ->
 padicNorm p (f n) …
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `padicNorm.zero`：∀ {p : ℕ}, padicNorm p 0 = 0
-/
theorem norm_eq_zpow_neg_valuation {f : PadicSeq p} (hf : ¬f ≈ 0) :
    f.norm = (p : ℚ) ^ (-f.valuation : ℤ) := by
  rw [norm, valuation, dif_neg hf, dif_neg hf, padicNorm, if_neg]
  intro H
  apply CauSeq.not_limZero_of_not_congr_zero hf
  intro ε hε
  use stationaryPoint hf
  intro n hn
  rw [stationaryPoint_spec hf le_rfl hn]
  simpa [H] using hε
/-
**PadicSeq.val_eq_iff_norm_eq** 是 Mathlib 中的一个定理，位于命名空间 `PadicSeq`。
形式化陈述：val_eq_iff_norm_eq {f g : PadicSeq p} (hf : ¬f ≈ 0) (hg : ¬g ≈ 0) : f.valu
ation = g.valuation ↔ f.norm = g.norm
参数：hf : ¬f ≈ 0；hg : ¬g ≈ 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PadicSeq.norm_eq_zpow_neg_valuation`：norm_eq_zpow_neg_valuation {f : Pad
icSeq p} (hf : ¬f ≈ 0) : f.norm = (p : Rat) ^ (-f.valuation : Int)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `zpow_right_inj₀`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : L
inearOrder G₀] {a : G₀} {m n : ℤ} [PosMulStrictMono G₀]   [ZeroLEOneClass G₀], 0
 < a …
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem val_eq_iff_norm_eq {f g : PadicSeq p} (hf : ¬f ≈ 0) (hg : ¬g ≈ 0) :
    f.valuation = g.valuation ↔ f.norm = g.norm := by
  rw [norm_eq_zpow_neg_valuation hf, norm_eq_zpow_neg_valuation hg, ← neg_inj, zpow_right_inj₀]
  · exact mod_cast (Fact.out : p.Prime).pos
  · exact mod_cast (Fact.out : p.Prime).ne_one

end Valuation

end PadicSeq

-- Porting note: Commented out `padic_index_simp` tactic

/-
section

open PadicSeq

private unsafe def index_simp_core (hh hf hg : expr)
    (at_ : Interactive.Loc := Interactive.Loc.ns [none]) : tactic Unit := do
  let [v1, v2, v3] ← [hh, hf, hg].mapM fun n => tactic.mk_app `` stationary_point [n] <|> return n
  let e1 ← tactic.mk_app `` lift_index_left_left [hh, v2, v3] <|> return q(True)
  let e2 ← tactic.mk_app `` lift_index_left [hf, v1, v3] <|> return q(True)
  let e3 ← tactic.mk_app `` lift_index_right [hg, v1, v2] <|> return q(True)
  let sl ← [e1, e2, e3].foldlM (fun s e => simp_lemmas.add s e) simp_lemmas.mk
  when at_ (tactic.simp_target sl >> tactic.skip)
  let hs ← at_.get_locals
  hs (tactic.simp_hyp sl [])

/-- This is a special-purpose tactic that lifts `padicNorm (f (stationary_point f))` to
`padicNorm (f (max _ _ _))`. -/
unsafe def tactic.interactive.padic_index_simp (l : interactive.parse interactive.types.pexpr_list)
    (at_ : interactive.parse interactive.types.location) : tactic Unit := do
  let [h, f, g] ← l.mapM tactic.i_to_expr
  index_simp_core h f g at_

end
-/

namespace PadicSeq

section Embedding

open CauSeq

variable {p : ℕ} [hp : Fact p.Prime]

/-
**PadicSeq.norm_mul** 是 Mathlib 中的一个定理，位于命名空间 `PadicSeq`。
形式化陈述：norm_mul (f g : PadicSeq p) : (f * g).norm = f.norm * g.norm
参数：f g : PadicSeq p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)
· 使用定理 `CauSeq.mul_equiv_zero'`：mul_equiv_zero' (g : CauSeq _ abv) {f : CauSeq _
 abv} (hf : f ≈ 0) : f * g ≈ 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CauSeq.mul_equiv_zero`：mul_equiv_zero (g : CauSeq _ abv) {f : CauSeq _ a
bv} (hf : f ≈ 0) : g * f ≈ 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `CauSeq.mul_not_equiv_zero`：mul_not_equiv_zero {f g : CauSeq _ abv} (hf :
 ¬f ≈ 0) (hg : ¬g ≈ 0) : ¬f * g ≈ 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false`：¬False
· 使用定理 `PadicSeq.lift_index_left_left`：lift_index_left_left {f : PadicSeq p} (hf
 : ¬f ≈ 0) (v2 v3 : Nat) : padicNorm p (f (stationaryPoint hf)) = padicNorm p (f
 (max (stationaryPo…
· 使用定理 `PadicSeq.lift_index_left`：lift_index_left {f : PadicSeq p} (hf : ¬f ≈ 0)
 (v1 v3 : Nat) : padicNorm p (f (stationaryPoint hf)) = padicNorm p (f (max v1 (
max (stationar…
· 使用定理 `PadicSeq.lift_index_right`：lift_index_right {f : PadicSeq p} (hf : ¬f ≈ 
0) (v1 v2 : Nat) : padicNorm p (f (stationaryPoint hf)) = padicNorm p (f (max v1
 (max v2 (stati…
· 使用定理 `padicNorm.mul`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (q r : ℚ), padicNorm 
p (q * r) = padicNorm p q * padicNorm p r
-/
theorem norm_mul (f g : PadicSeq p) : (f * g).norm = f.norm * g.norm := by
  classical
  exact if hf : f ≈ 0 then by
    have hg : f * g ≈ 0 := mul_equiv_zero' _ hf
    simp only [hf, hg, norm, dif_pos, zero_mul]
  else
    if hg : g ≈ 0 then by
      have hf : f * g ≈ 0 := mul_equiv_zero _ hg
      simp only [hf, hg, norm, dif_pos, mul_zero]
    else by
      unfold norm
      have hfg := mul_not_equiv_zero hf hg
      simp only [hfg, hf, hg, dite_false]
      -- Porting note: originally `padic_index_simp [hfg, hf, hg]`
      rw [lift_index_left_left hfg, lift_index_left hf, lift_index_right hg]
      apply padicNorm.mul
/-
**PadicSeq.eq_zero_iff_equiv_zero** 是 Mathlib 中的一个定理，位于命名空间 `PadicSeq`。
形式化陈述：eq_zero_iff_equiv_zero (f : PadicSeq p) : mk f = 0 ↔ f ≈ 0
参数：f : PadicSeq p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CauSeq.Completion.mk_eq`：mk_eq {f g : CauSeq _ abv} : mk f = mk g ↔ LimZ
ero (f - g)
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)
-/
theorem eq_zero_iff_equiv_zero (f : PadicSeq p) : mk f = 0 ↔ f ≈ 0 :=
  mk_eq
/-
**PadicSeq.ne_zero_iff_nequiv_zero** 是 Mathlib 中的一个定理，位于命名空间 `PadicSeq`。
形式化陈述：ne_zero_iff_nequiv_zero (f : PadicSeq p) : mk f != 0 ↔ ¬f ≈ 0
参数：f : PadicSeq p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)
· 使用定理 `PadicSeq.eq_zero_iff_equiv_zero`：eq_zero_iff_equiv_zero (f : PadicSeq p)
 : mk f = 0 ↔ f ≈ 0
-/
theorem ne_zero_iff_nequiv_zero (f : PadicSeq p) : mk f ≠ 0 ↔ ¬f ≈ 0 :=
  eq_zero_iff_equiv_zero _ |>.not
/-
**PadicSeq.norm_const** 是 Mathlib 中的一个定理，位于命名空间 `PadicSeq`。
形式化陈述：norm_const (q : Rat) : norm (const (padicNorm p) q) = padicNorm p q
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `padicNorm.zero`：∀ {p : ℕ}, padicNorm p 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `PadicSeq.not_equiv_zero_const_of_nonzero`：not_equiv_zero_const_of_nonzer
o {q : Rat} (hq : q != 0) : ¬const (padicNorm p) q ≈ 0
-/
theorem norm_const (q : ℚ) : norm (const (padicNorm p) q) = padicNorm p q := by
  obtain rfl | hq := eq_or_ne q 0
  · simp [norm]
  · simp [norm, not_equiv_zero_const_of_nonzero hq]
/-
**PadicSeq.norm_values_discrete** 是 Mathlib 中的一个定理，位于命名空间 `PadicSeq`。
形式化陈述：norm_values_discrete (a : PadicSeq p) (ha : ¬a ≈ 0) : exists z : Int, a.no
rm = (p : Rat) ^ (-z)
参数：a : PadicSeq p；ha : ¬a ≈ 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)
· 使用定理 `PadicSeq.norm_eq_norm_app_of_nonzero`：norm_eq_norm_app_of_nonzero {f : P
adicSeq p} (hf : ¬f ≈ 0) : exists k, f.norm = padicNorm p k ∧ k != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `padicNorm.values_discrete`：∀ {p : ℕ} {q : ℚ}, q ≠ 0 → ∃ z, padicNorm p q
 = ↑p ^ (-z)
-/
theorem norm_values_discrete (a : PadicSeq p) (ha : ¬a ≈ 0) : ∃ z : ℤ, a.norm = (p : ℚ) ^ (-z) := by
  let ⟨k, hk, hk'⟩ := norm_eq_norm_app_of_nonzero ha
  simpa [hk] using padicNorm.values_discrete hk'
/-
**PadicSeq.norm_one** 是 Mathlib 中的一个定理，位于命名空间 `PadicSeq`。
形式化陈述：norm_one : norm (1 : PadicSeq p) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)
· 使用定理 `CauSeq.one_not_equiv_zero`：one_not_equiv_zero : ¬const abv 1 ≈ const abv
 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `padicNorm.eq_zpow_of_nonzero`：∀ {p : ℕ} {q : ℚ}, q ≠ 0 → padicNorm p q =
 ↑p ^ (-padicValRat p q)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `padicValRat.one`：∀ {p : ℕ}, padicValRat p 1 = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_one : norm (1 : PadicSeq p) = 1 := by
  have h1 : ¬(1 : PadicSeq p) ≈ 0 := one_not_equiv_zero _
  simp [h1, norm]
/-
**PadicSeq.norm_eq_of_equiv_aux** 是 Mathlib 中的一个定理，位于命名空间 `PadicSeq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem norm_eq_of_equiv_aux {f g : PadicSeq p} (hf : ¬f ≈ 0) (hg : ¬g ≈ 0) (hfg : f ≈ g)
    (h : padicNorm p (f (stationaryPoint hf)) ≠ padicNorm p (g (stationaryPoint hg)))
    (hlt : padicNorm p (g (stationaryPoint hg)) < padicNorm p (f (stationaryPoint hf))) :
    False := by
  have hpn : 0 < padicNorm p (f (stationaryPoint hf)) - padicNorm p (g (stationaryPoint hg)) :=
    sub_pos_of_lt hlt
  obtain ⟨N, hN⟩ := hfg _ hpn
  let i := max N (max (stationaryPoint hf) (stationaryPoint hg))
  have hi : N ≤ i := le_max_left _ _
  have hN' := hN _ hi
  -- Porting note: originally `padic_index_simp [N, hf, hg] at hN' h hlt`
  rw [lift_index_left hf N (stationaryPoint hg), lift_index_right hg N (stationaryPoint hf)]
    at hN' h hlt
  have hpne : padicNorm p (f i) ≠ padicNorm p (-g i) := by rwa [← padicNorm.neg (g i)] at h
  rw [CauSeq.sub_apply, sub_eq_add_neg, add_eq_max_of_ne hpne, padicNorm.neg, max_eq_left_of_lt hlt]
    at hN'
  have : padicNorm p (f i) < padicNorm p (f i) := by
    apply lt_of_lt_of_le hN'
    apply sub_le_self
    apply padicNorm.nonneg
  exact lt_irrefl _ this
/-
**PadicSeq.norm_eq_of_equiv** 是 Mathlib 中的一个定理，位于命名空间 `PadicSeq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem norm_eq_of_equiv {f g : PadicSeq p} (hf : ¬f ≈ 0) (hg : ¬g ≈ 0) (hfg : f ≈ g) :
    padicNorm p (f (stationaryPoint hf)) = padicNorm p (g (stationaryPoint hg)) := by
  by_contra h
  cases lt_or_ge (padicNorm p (g (stationaryPoint hg))) (padicNorm p (f (stationaryPoint hf))) with
  | inl hlt =>
    exact norm_eq_of_equiv_aux hf hg hfg h hlt
  | inr hle =>
    apply norm_eq_of_equiv_aux hg hf (Setoid.symm hfg) (Ne.symm h)
    exact lt_of_le_of_ne hle h
/-
**PadicSeq.norm_equiv** 是 Mathlib 中的一个定理，位于命名空间 `PadicSeq`。
形式化陈述：norm_equiv {f g : PadicSeq p} (hfg : f ≈ g) : f.norm = g.norm
参数：hfg : f ≈ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)
· 使用定理 `Setoid.trans`：∀ {α : Sort u} [inst : Setoid α] {a b c : α}, a ≈ b → b ≈ 
c → a ≈ c
· 使用定理 `Setoid.symm`：∀ {α : Sort u} [inst : Setoid α] {a b : α}, a ≈ b → b ≈ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `_private.Mathlib.NumberTheory.Padics.PadicNumbers.0.PadicSeq.norm_eq_of_
equiv`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] {f g : PadicSeq p} (hf : ¬f ≈ 0) (hg 
: ¬g ≈ 0),   f ≈ g → padicNorm p (↑f (PadicSeq.stationaryPoint hf))…
-/
theorem norm_equiv {f g : PadicSeq p} (hfg : f ≈ g) : f.norm = g.norm := by
  classical
  exact if hf : f ≈ 0 then by
    have hg : g ≈ 0 := Setoid.trans (Setoid.symm hfg) hf
    simp [norm, hf, hg]
  else by
    have hg : ¬g ≈ 0 := hf ∘ Setoid.trans hfg
    unfold norm; split_ifs; exact norm_eq_of_equiv hf hg hfg
/-
**PadicSeq.norm_nonarchimedean_aux** 是 Mathlib 中的一个定理，位于命名空间 `PadicSeq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem norm_nonarchimedean_aux {f g : PadicSeq p} (hfg : ¬f + g ≈ 0) (hf : ¬f ≈ 0)
    (hg : ¬g ≈ 0) : (f + g).norm ≤ max f.norm g.norm := by
  unfold norm; split_ifs
  -- Porting note: originally `padic_index_simp [hfg, hf, hg]`
  rw [lift_index_left_left hfg, lift_index_left hf, lift_index_right hg]
  apply padicNorm.nonarchimedean
/-
**PadicSeq.norm_nonarchimedean** 是 Mathlib 中的一个定理，位于命名空间 `PadicSeq`。
形式化陈述：norm_nonarchimedean (f g : PadicSeq p) : (f + g).norm <= max f.norm g.norm
参数：f g : PadicSeq p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)
· 使用定理 `le_max_of_le_left`：le_max_of_le_left : a <= b -> a <= max b c
· 使用定理 `PadicSeq.norm_nonneg`：norm_nonneg (f : PadicSeq p) : 0 <= f.norm
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `PadicSeq.norm_equiv`：norm_equiv {f g : PadicSeq p} (hfg : f ≈ g) : f.nor
m = g.norm
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PadicSeq.norm_zero_iff`：norm_zero_iff (f : PadicSeq p) : f.norm = 0 ↔ f 
≈ 0
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用定理 `_private.Mathlib.NumberTheory.Padics.PadicNumbers.0.PadicSeq.norm_nonarc
himedean_aux`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] {f g : PadicSeq p}, ¬f + g ≈ 0
 → ¬f ≈ 0 → ¬g ≈ 0 → (f + g).norm ≤ max f.norm g.norm
-/
theorem norm_nonarchimedean (f g : PadicSeq p) : (f + g).norm ≤ max f.norm g.norm := by
  classical
  exact if hfg : f + g ≈ 0 then by
    have : 0 ≤ max f.norm g.norm := le_max_of_le_left (norm_nonneg _)
    simpa only [hfg, norm]
  else
    if hf : f ≈ 0 then by
      have hfg' : f + g ≈ g := by
        change LimZero (f - 0) at hf
        change LimZero (f + g - g); · simpa only [sub_zero, add_sub_cancel_right] using hf
      have hcfg : (f + g).norm = g.norm := norm_equiv hfg'
      have hcl : f.norm = 0 := (norm_zero_iff f).2 hf
      have : max f.norm g.norm = g.norm := by rw [hcl]; exact max_eq_right (norm_nonneg _)
      rw [this, hcfg]
    else
      if hg : g ≈ 0 then by
        have hfg' : f + g ≈ f := by
          change LimZero (g - 0) at hg
          change LimZero (f + g - f); · simpa only [add_sub_cancel_left, sub_zero] using hg
        have hcfg : (f + g).norm = f.norm := norm_equiv hfg'
        have hcl : g.norm = 0 := (norm_zero_iff g).2 hg
        have : max f.norm g.norm = f.norm := by rw [hcl]; exact max_eq_left (norm_nonneg _)
        rw [this, hcfg]
      else norm_nonarchimedean_aux hfg hf hg
/-
**PadicSeq.norm_eq** 是 Mathlib 中的一个定理，位于命名空间 `PadicSeq`。
形式化陈述：norm_eq {f g : PadicSeq p} (h : forall k, padicNorm p (f k) = padicNorm p 
(g k)) : f.norm = g.norm
参数：h : forall k, padicNorm p (f k) = padicNorm p (g k)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)
· 使用定理 `PadicSeq.equiv_zero_of_val_eq_of_equiv_zero`：equiv_zero_of_val_eq_of_equ
iv_zero {f g : PadicSeq p} (h : forall k, padicNorm p (f k) = padicNorm p (g k))
 (hf : f ≈ 0) : g ≈ 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `PadicSeq.stationaryPoint_spec`：stationaryPoint_spec {f : PadicSeq p} (hf
 : ¬f ≈ 0) : forall {m n}, stationaryPoint hf <= m -> stationaryPoint hf <= n ->
 padicNorm p (f n) …
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
-/
theorem norm_eq {f g : PadicSeq p} (h : ∀ k, padicNorm p (f k) = padicNorm p (g k)) :
    f.norm = g.norm := by
  classical
  exact if hf : f ≈ 0 then by
    have hg : g ≈ 0 := equiv_zero_of_val_eq_of_equiv_zero h hf
    simp only [hf, hg, norm, dif_pos]
  else by
    have hg : ¬g ≈ 0 := fun hg ↦
      hf <| equiv_zero_of_val_eq_of_equiv_zero (by simp only [h, forall_const]) hg
    simp only [hg, hf, norm, dif_neg, not_false_iff]
    let i := max (stationaryPoint hf) (stationaryPoint hg)
    have hpf : padicNorm p (f (stationaryPoint hf)) = padicNorm p (f i) := by
      apply stationaryPoint_spec
      · apply le_max_left
      · exact le_rfl
    have hpg : padicNorm p (g (stationaryPoint hg)) = padicNorm p (g i) := by
      apply stationaryPoint_spec
      · apply le_max_right
      · exact le_rfl
    rw [hpf, hpg, h]
/-
**PadicSeq.norm_neg** 是 Mathlib 中的一个定理，位于命名空间 `PadicSeq`。
形式化陈述：norm_neg (a : PadicSeq p) : (-a).norm = a.norm
参数：a : PadicSeq p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PadicSeq.norm_eq`：norm_eq {f g : PadicSeq p} (h : forall k, padicNorm p 
(f k) = padicNorm p (g k)) : f.norm = g.norm
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `padicNorm.neg`：∀ {p : ℕ} (q : ℚ), padicNorm p (-q) = padicNorm p q
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem norm_neg (a : PadicSeq p) : (-a).norm = a.norm :=
  norm_eq <| by simp
/-
**PadicSeq.norm_eq_of_add_equiv_zero** 是 Mathlib 中的一个定理，位于命名空间 `PadicSeq`。
形式化陈述：norm_eq_of_add_equiv_zero {f g : PadicSeq p} (h : f + g ≈ 0) : f.norm = g.
norm
参数：h : f + g ≈ 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `PadicSeq.norm_equiv`：norm_equiv {f g : PadicSeq p} (hfg : f ≈ g) : f.nor
m = g.norm
· 使用定理 `PadicSeq.norm_neg`：norm_neg (a : PadicSeq p) : (-a).norm = a.norm
-/
theorem norm_eq_of_add_equiv_zero {f g : PadicSeq p} (h : f + g ≈ 0) : f.norm = g.norm := by
  have : LimZero (f + g - 0) := h
  have : f ≈ -g := show LimZero (f - -g) by simpa only [sub_zero, sub_neg_eq_add]
  have : f.norm = (-g).norm := norm_equiv this
  simpa only [norm_neg] using this
/-
**PadicSeq.add_eq_max_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `PadicSeq`。
形式化陈述：add_eq_max_of_ne {f g : PadicSeq p} (hfgne : f.norm != g.norm) : (f + g).n
orm = max f.norm g.norm
参数：hfgne : f.norm != g.norm。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `PadicSeq.norm_eq_of_add_equiv_zero`：norm_eq_of_add_equiv_zero {f g : Pad
icSeq p} (h : f + g ≈ 0) : f.norm = g.norm
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `PadicSeq.norm_equiv`：norm_equiv {f g : PadicSeq p} (hfg : f ≈ g) : f.nor
m = g.norm
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PadicSeq.norm_zero_iff`：norm_zero_iff (f : PadicSeq p) : f.norm = 0 ↔ f 
≈ 0
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用定理 `PadicSeq.norm_nonneg`：norm_nonneg (f : PadicSeq p) : 0 <= f.norm
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `PadicSeq.lift_index_left_left`：lift_index_left_left {f : PadicSeq p} (hf
 : ¬f ≈ 0) (v2 v3 : Nat) : padicNorm p (f (stationaryPoint hf)) = padicNorm p (f
 (max (stationaryPo…
· 使用定理 `PadicSeq.lift_index_left`：lift_index_left {f : PadicSeq p} (hf : ¬f ≈ 0)
 (v1 v3 : Nat) : padicNorm p (f (stationaryPoint hf)) = padicNorm p (f (max v1 (
max (stationar…
· 使用定理 `PadicSeq.lift_index_right`：lift_index_right {f : PadicSeq p} (hf : ¬f ≈ 
0) (v1 v2 : Nat) : padicNorm p (f (stationaryPoint hf)) = padicNorm p (f (max v1
 (max v2 (stati…
· 使用定理 `padicNorm.add_eq_max_of_ne`：add_eq_max_of_ne {q r : Rat} (hne : padicNor
m p q != padicNorm p r) : padicNorm p (q + r) = max (padicNorm p q) (padicNorm p
 r)
-/
theorem add_eq_max_of_ne {f g : PadicSeq p} (hfgne : f.norm ≠ g.norm) :
    (f + g).norm = max f.norm g.norm := by
  classical
  have hfg : ¬f + g ≈ 0 := mt norm_eq_of_add_equiv_zero hfgne
  exact if hf : f ≈ 0 then by
    have : LimZero (f - 0) := hf
    have : f + g ≈ g := show LimZero (f + g - g) by simpa only [sub_zero, add_sub_cancel_right]
    have h1 : (f + g).norm = g.norm := norm_equiv this
    have h2 : f.norm = 0 := (norm_zero_iff _).2 hf
    rw [h1, h2, max_eq_right (norm_nonneg _)]
  else
    if hg : g ≈ 0 then by
      have : LimZero (g - 0) := hg
      have : f + g ≈ f := show LimZero (f + g - f) by simpa only [add_sub_cancel_left, sub_zero]
      have h1 : (f + g).norm = f.norm := norm_equiv this
      have h2 : g.norm = 0 := (norm_zero_iff _).2 hg
      rw [h1, h2, max_eq_left (norm_nonneg _)]
    else by
      unfold norm at hfgne ⊢; split_ifs at hfgne ⊢
      -- Porting note: originally `padic_index_simp [hfg, hf, hg] at hfgne ⊢`
      rw [lift_index_left hf, lift_index_right hg] at hfgne
      · rw [lift_index_left_left hfg, lift_index_left hf, lift_index_right hg]
        exact padicNorm.add_eq_max_of_ne hfgne

end Embedding

end PadicSeq

/-- The `p`-adic numbers `ℚ_[p]` are the Cauchy completion of `ℚ` with respect to the `p`-adic norm.
-/
@[wikidata Q311627]
/-
**Padic** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Padic (p : Nat) [Fact p.Prime]
参数：p : Nat。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)

--- 原说明 ---
The `p`-adic numbers `ℚ_[p]` are the Cauchy completion of `ℚ` with respect to th
e `p`-adic norm.
-/
def Padic (p : ℕ) [Fact p.Prime] :=
  CauSeq.Completion.Cauchy (padicNorm p)
deriving Zero, One, Add, Neg, Sub, Mul, Div, AddCommGroup, Ring, CommRing, Field, Inhabited

/-- notation for p-padic rationals -/
notation "ℚ_[" p "]" => Padic p

namespace Padic

section Completion

variable {p : ℕ} [Fact p.Prime]

/-- Builds the equivalence class of a Cauchy sequence of rationals. -/
/-
**Padic.mk** 是 Mathlib 中的一个定义，位于命名空间 `Padic`。
形式化陈述：mk : PadicSeq p -> Rat_[p]
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)

--- 原说明 ---
Builds the equivalence class of a Cauchy sequence of rationals.
-/
def mk : PadicSeq p → ℚ_[p] :=
  Quotient.mk'

variable (p)
/-
**Padic.zero_def** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：zero_def : (0 : Rat_[p]) = ⟦0⟧
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_def : (0 : ℚ_[p]) = ⟦0⟧ := rfl
/-
**Padic.mk_eq** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：mk_eq {f g : PadicSeq p} : mk f = mk g ↔ f ≈ g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.eq'`：∀ {α : Sort u_1} {s₁ : Setoid α} {a b : α}, Quotient.mk' a
 = Quotient.mk' b ↔ s₁ a b
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)
-/
theorem mk_eq {f g : PadicSeq p} : mk f = mk g ↔ f ≈ g :=
  Quotient.eq'
/-
**Padic.const_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：const_equiv {q r : Rat} : const (padicNorm p) q ≈ const (padicNorm p) r ↔ 
q = r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)
· 使用定理 `eq_of_sub_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a b : 
α}, a - b = 0 → a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CauSeq.const_limZero`：const_limZero {x : β} : LimZero (const x) ↔ x = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Setoid.refl`：∀ {α : Sort u} [inst : Setoid α] (a : α), a ≈ a
-/
theorem const_equiv {q r : ℚ} : const (padicNorm p) q ≈ const (padicNorm p) r ↔ q = r :=
  ⟨fun heq ↦ eq_of_sub_eq_zero <| const_limZero.1 heq, fun heq ↦ by
    rw [heq]⟩

@[norm_cast]
/-
**Padic.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：coe_inj {q r : Rat} : (↑q : Rat_[p]) = ↑r ↔ q = r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Padic.const_equiv`：const_equiv {q r : Rat} : const (padicNorm p) q ≈ con
st (padicNorm p) r ↔ q = r
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `Quotient.eq'`：∀ {α : Sort u_1} {s₁ : Setoid α} {a b : α}, Quotient.mk' a
 = Quotient.mk' b ↔ s₁ a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem coe_inj {q r : ℚ} : (↑q : ℚ_[p]) = ↑r ↔ q = r :=
  ⟨(const_equiv p).1 ∘ Quotient.eq'.1, fun h ↦ by rw [h]⟩
/-
**Padic.** 是 Mathlib 中的一个实例，位于命名空间 `Padic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CharZero ℚ_[p] :=
  ⟨fun m n ↦ by
    rw [← Rat.cast_natCast]
    norm_cast
    exact id⟩

@[norm_cast]
/-
**Padic.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：coe_add : forall {x y : Rat}, (↑(x + y) : Rat_[p]) = ↑x + ↑y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.cast_add`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p + q) = ↑p + ↑q
· 使用定理 `Padic.instCharZero`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)], CharZero ℚ_[p
]
-/
theorem coe_add : ∀ {x y : ℚ}, (↑(x + y) : ℚ_[p]) = ↑x + ↑y :=
  Rat.cast_add _ _

@[norm_cast]
/-
**Padic.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：coe_neg : forall {x : Rat}, (↑(-x) : Rat_[p]) = -↑x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.cast_neg`：∀ {α : Type u_3} [inst : DivisionRing α] (q : ℚ), ↑(-q) = 
-↑q
-/
theorem coe_neg : ∀ {x : ℚ}, (↑(-x) : ℚ_[p]) = -↑x :=
  Rat.cast_neg _

@[norm_cast]
/-
**Padic.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：coe_mul : forall {x y : Rat}, (↑(x * y) : Rat_[p]) = ↑x * ↑y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.cast_mul`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p * q) = ↑p * ↑q
· 使用定理 `Padic.instCharZero`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)], CharZero ℚ_[p
]
-/
theorem coe_mul : ∀ {x y : ℚ}, (↑(x * y) : ℚ_[p]) = ↑x * ↑y :=
  Rat.cast_mul _ _

@[norm_cast]
/-
**Padic.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：coe_sub : forall {x y : Rat}, (↑(x - y) : Rat_[p]) = ↑x - ↑y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.cast_sub`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p - q) = ↑p - ↑q
· 使用定理 `Padic.instCharZero`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)], CharZero ℚ_[p
]
-/
theorem coe_sub : ∀ {x y : ℚ}, (↑(x - y) : ℚ_[p]) = ↑x - ↑y :=
  Rat.cast_sub _ _

@[norm_cast]
/-
**Padic.coe_div** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：coe_div : forall {x y : Rat}, (↑(x / y) : Rat_[p]) = ↑x / ↑y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.cast_div`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p / q) = ↑p / ↑q
· 使用定理 `Padic.instCharZero`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)], CharZero ℚ_[p
]
-/
theorem coe_div : ∀ {x y : ℚ}, (↑(x / y) : ℚ_[p]) = ↑x / ↑y :=
  Rat.cast_div _ _

@[norm_cast]
/-
**Padic.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：coe_one : (↑(1 : Rat) : Rat_[p]) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : (↑(1 : ℚ) : ℚ_[p]) = 1 := rfl

@[norm_cast]
/-
**Padic.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：coe_zero : (↑(0 : Rat) : Rat_[p]) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zero : (↑(0 : ℚ) : ℚ_[p]) = 0 := rfl

end Completion

end Padic

/-- The rational-valued `p`-adic norm on `ℚ_[p]` is lifted from the norm on Cauchy sequences. The
canonical form of this function is the normed space instance, with notation `‖ ‖`. -/
/-
**padicNormE** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：padicNormE {p : Nat} [hp : Fact p.Prime] : AbsoluteValue Rat_[p] Rat where
 toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)
· 使用定理 `PadicSeq.norm_equiv`：norm_equiv {f g : PadicSeq p} (hfg : f ≈ g) : f.nor
m = g.norm

--- 原说明 ---
The rational-valued `p`-adic norm on `ℚ_[p]` is lifted from the norm on Cauchy s
equences. The
canonical form of this function is the normed space instance, with notation `‖ ‖
`.
-/
def padicNormE {p : ℕ} [hp : Fact p.Prime] : AbsoluteValue ℚ_[p] ℚ where
  toFun := Quotient.lift PadicSeq.norm <| @PadicSeq.norm_equiv _ _
  map_mul' q r := Quotient.inductionOn₂ q r <| PadicSeq.norm_mul
  nonneg' q := Quotient.inductionOn q <| PadicSeq.norm_nonneg
  eq_zero' q := Quotient.inductionOn q fun r ↦ by
    rw [Padic.zero_def, Quotient.lift_mk, PadicSeq.norm_zero_iff r]
    exact Quotient.eq.symm
  add_le' q r := by
    trans
      max ((Quotient.lift PadicSeq.norm <| @PadicSeq.norm_equiv _ _) q)
        ((Quotient.lift PadicSeq.norm <| @PadicSeq.norm_equiv _ _) r)
    · induction q, r using Quotient.inductionOn₂; apply PadicSeq.norm_nonarchimedean
    · apply max_le_add_of_nonneg
      · induction q using Quotient.inductionOn; apply PadicSeq.norm_nonneg
      · induction r using Quotient.inductionOn; apply PadicSeq.norm_nonneg

namespace padicNormE

section Embedding

open PadicSeq

variable {p : ℕ} [Fact p.Prime]

/-
**padicNormE.defn** 是 Mathlib 中的一个定理，位于命名空间 `padicNormE`。
形式化陈述：defn (f : PadicSeq p) {ε : Rat} (hε : 0 < ε) : exists N, forall i >= N, pa
dicNormE (Padic.mk f - f i : Rat_[p]) < ε
参数：f : PadicSeq p；hε : 0 < ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `CauSeq.cauchy₂`：cauchy₂ (f : CauSeq β abv) {ε} : 0 < ε -> exists i, fora
ll j >= i, forall k >= i, abv (f j - f k) < ε
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `not_lt_of_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `PadicSeq.norm.eq_1`：∀ {p : ℕ} [inst : Fact (Nat.Prime p)] (f : PadicSeq 
p),   f.norm = if hf : f ≈ 0 then 0 else padicNorm p (↑f (PadicSeq.stationaryPoi
nt hf))
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `PadicSeq.stationaryPoint_spec`：stationaryPoint_spec {f : PadicSeq p} (hf
 : ¬f ≈ 0) : forall {m n}, stationaryPoint hf <= m -> stationaryPoint hf <= n ->
 padicNorm p (f n) …
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `PadicSeq.norm_equiv`：norm_equiv {f g : PadicSeq p} (hfg : f ≈ g) : f.nor
m = g.norm
· 使用定理 `forall_imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∀ (a : α), p a) → ∀ (a : α), q a
-/
theorem defn (f : PadicSeq p) {ε : ℚ} (hε : 0 < ε) :
    ∃ N, ∀ i ≥ N, padicNormE (Padic.mk f - f i : ℚ_[p]) < ε := by
  dsimp [padicNormE]
  -- `change ∃ N, ∀ i ≥ N, (f - const _ (f i)).norm < ε` also works, but is very slow
  suffices hyp : ∃ N, ∀ i ≥ N, (f - const _ (f i)).norm < ε by peel hyp with N; use N
  by_contra! h
  obtain ⟨N, hN⟩ := cauchy₂ f hε
  rcases h N with ⟨i, hi, hge⟩
  have hne : ¬f - const (padicNorm p) (f i) ≈ 0 := fun h ↦ by
    rw [PadicSeq.norm, dif_pos h] at hge
    exact not_lt_of_ge hge hε
  unfold PadicSeq.norm at hge; split_ifs at hge
  apply not_le_of_gt _ hge
  cases _root_.le_total N (stationaryPoint hne) with
  | inl hgen =>
    exact hN _ hgen _ hi
  | inr hngen =>
    have := stationaryPoint_spec hne le_rfl hngen
    rw [← this]
    exact hN _ le_rfl _ hi

/-- Theorems about `padicNormE` are named with a `'` so the names do not conflict with the
equivalent theorems about `norm` (`‖ ‖`). -/
/-
**padicNormE.nonarchimedean'** 是 Mathlib 中的一个定理，位于命名空间 `padicNormE`。
形式化陈述：nonarchimedean' (q r : Rat_[p]) : padicNormE (q + r : Rat_[p]) <= max (pad
icNormE q) (padicNormE r)
参数：q r : Rat_[p]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)
· 使用定理 `PadicSeq.norm_nonarchimedean`：norm_nonarchimedean (f g : PadicSeq p) : (
f + g).norm <= max f.norm g.norm

--- 原说明 ---
Theorems about `padicNormE` are named with a `'` so the names do not conflict wi
th the
equivalent theorems about `norm` (`‖ ‖`).
-/
theorem nonarchimedean' (q r : ℚ_[p]) :
    padicNormE (q + r : ℚ_[p]) ≤ max (padicNormE q) (padicNormE r) :=
  Quotient.inductionOn₂ q r <| norm_nonarchimedean

/-- Theorems about `padicNormE` are named with a `'` so the names do not conflict with the
equivalent theorems about `norm` (`‖ ‖`). -/
/-
**padicNormE.add_eq_max_of_ne'** 是 Mathlib 中的一个定理，位于命名空间 `padicNormE`。
形式化陈述：add_eq_max_of_ne' {q r : Rat_[p]} : padicNormE q != padicNormE r -> padicN
ormE (q + r : Rat_[p]) = max (padicNormE q) (padicNormE r)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)
· 使用定理 `PadicSeq.add_eq_max_of_ne`：add_eq_max_of_ne {f g : PadicSeq p} (hfgne : 
f.norm != g.norm) : (f + g).norm = max f.norm g.norm

--- 原说明 ---
Theorems about `padicNormE` are named with a `'` so the names do not conflict wi
th the
equivalent theorems about `norm` (`‖ ‖`).
-/
theorem add_eq_max_of_ne' {q r : ℚ_[p]} :
    padicNormE q ≠ padicNormE r → padicNormE (q + r : ℚ_[p]) = max (padicNormE q) (padicNormE r) :=
  Quotient.inductionOn₂ q r fun _ _ ↦ PadicSeq.add_eq_max_of_ne

@[simp]
/-
**padicNormE.eq_padic_norm'** 是 Mathlib 中的一个定理，位于命名空间 `padicNormE`。
形式化陈述：eq_padic_norm' (q : Rat) : padicNormE (q : Rat_[p]) = padicNorm p q
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PadicSeq.norm_const`：norm_const (q : Rat) : norm (const (padicNorm p) q)
 = padicNorm p q
-/
theorem eq_padic_norm' (q : ℚ) : padicNormE (q : ℚ_[p]) = padicNorm p q :=
  norm_const _
/-
**padicNormE.image'** 是 Mathlib 中的一个定理，位于命名空间 `padicNormE`。
形式化陈述：∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {q : ℚ_[p]}, q ≠ 0 → ∃ n, padicNormE
 q = ↑p ^ (-n)
参数：Nat.Prime p；-n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PadicSeq.ne_zero_iff_nequiv_zero`：ne_zero_iff_nequiv_zero (f : PadicSeq 
p) : mk f != 0 ↔ ¬f ≈ 0
· 使用定理 `PadicSeq.norm_values_discrete`：norm_values_discrete (a : PadicSeq p) (ha
 : ¬a ≈ 0) : exists z : Int, a.norm = (p : Rat) ^ (-z)
-/
protected theorem image' {q : ℚ_[p]} : q ≠ 0 → ∃ n : ℤ, padicNormE q = (p : ℚ) ^ (-n) :=
  Quotient.inductionOn q fun f hf ↦
    have : ¬f ≈ 0 := (ne_zero_iff_nequiv_zero f).1 hf
    norm_values_discrete f this

end Embedding

end padicNormE

namespace Padic

section Complete

open PadicSeq Padic

variable {p : ℕ} [Fact p.Prime] (f : CauSeq _ (@padicNormE p _))

/-
**Padic.rat_dense'** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：rat_dense' (q : Rat_[p]) {ε : Rat} (hε : 0 < ε) : exists r : Rat, padicNor
mE (q - r : Rat_[p]) < ε
参数：q : Rat_[p]；hε : 0 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)
· 使用定理 `CauSeq.cauchy₂`：cauchy₂ (f : CauSeq β abv) {ε} : 0 < ε -> exists i, fora
ll j >= i, forall k >= i, abv (f j - f k) < ε
· 使用定理 `PadicSeq.norm_equiv`：norm_equiv {f g : PadicSeq p} (hfg : f ≈ g) : f.nor
m = g.norm
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Decidable.em`：∀ (p : Prop) [Decidable p], p ∨ ¬p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `PadicSeq.stationaryPoint_spec`：stationaryPoint_spec {f : PadicSeq p} (hf
 : ¬f ≈ 0) : forall {m n}, stationaryPoint hf <= m -> stationaryPoint hf <= n ->
 padicNorm p (f n) …
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `padicNorm.zero`：∀ {p : ℕ}, padicNorm p 0 = 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
-/
theorem rat_dense' (q : ℚ_[p]) {ε : ℚ} (hε : 0 < ε) : ∃ r : ℚ, padicNormE (q - r : ℚ_[p]) < ε :=
  Quotient.inductionOn q fun q' ↦
    have : ∃ N, ∀ m ≥ N, ∀ n ≥ N, padicNorm p (q' m - q' n) < ε := cauchy₂ _ hε
    let ⟨N, hN⟩ := this
    ⟨q' N, by
      classical
      dsimp [padicNormE]
      convert_to! PadicSeq.norm (q' - const _ (q' N)) < ε -- `change` times out here.
      rcases Decidable.em (q' - const (padicNorm p) (q' N) ≈ 0) with heq | hne'
      · simpa only [heq, PadicSeq.norm, dif_pos]
      · simp only [PadicSeq.norm, dif_neg hne']
        change padicNorm p (q' _ - q' _) < ε
        rcases Decidable.em (stationaryPoint hne' ≤ N) with hle | hle
        · have := (stationaryPoint_spec hne' le_rfl hle).symm
          simp only [const_apply, CauSeq.sub_apply, padicNorm.zero, sub_self] at this
          simpa only [this]
        · exact hN _ (lt_of_not_ge hle).le _ le_rfl⟩

set_option backward.privateInPublic true in
/-
**Padic.div_nat_pos** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem div_nat_pos (n : ℕ) : 0 < 1 / (n + 1 : ℚ) :=
  div_pos zero_lt_one (mod_cast succ_pos _)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- `limSeq f`, for `f` a Cauchy sequence of `p`-adic numbers, is a sequence of rationals with the
same limit point as `f`. -/
/-
**Padic.limSeq** 是 Mathlib 中的一个定义，位于命名空间 `Padic`。
形式化陈述：limSeq : Nat -> Rat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`limSeq f`, for `f` a Cauchy sequence of `p`-adic numbers, is a sequence of rati
onals with the
same limit point as `f`.
-/
def limSeq : ℕ → ℚ :=
  fun n ↦ Classical.choose (rat_dense' (f n) (div_nat_pos n))
/-
**Padic.exi_rat_seq_conv** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：exi_rat_seq_conv {ε : Rat} (hε : 0 < ε) : exists N, forall i >= N, padicNo
rmE (f i - (limSeq f i : Rat_[p]) : Rat_[p]) < ε
参数：hε : 0 < ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Padic.rat_dense'`：rat_dense' (q : Rat_[p]) {ε : Rat} (hε : 0 < ε) : exis
ts r : Rat, padicNormE (q - r : Rat_[p]) < ε
· 使用定理 `_private.Mathlib.NumberTheory.Padics.PadicNumbers.0.Padic.div_nat_pos`：∀
 (n : ℕ), 0 < 1 / (↑n + 1)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `div_le_iff₀'`：div_le_iff₀' (hc : 0 < c) : b / c <= a ↔ b <= c * a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `right_distrib`：right_distrib [Mul R] [Add R] [RightDistribClass R] (a b 
c : R) : (a + b) * c = a * c + b * c
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `le_add_of_le_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1
 : Preorder α] [AddLeftMono α] {a b c : α}, b ≤ c → 0 ≤ a → b ≤ c + a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `div_le_iff₀`：div_le_iff₀ (hc : 0 < c) : b / c <= a ↔ b <= a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `exists_nat_gt`：exists_nat_gt (x : R) : exists n : Nat, x < n
（共 31 条，此处仅展示前 30 条）
-/
theorem exi_rat_seq_conv {ε : ℚ} (hε : 0 < ε) :
    ∃ N, ∀ i ≥ N, padicNormE (f i - (limSeq f i : ℚ_[p]) : ℚ_[p]) < ε := by
  refine (exists_nat_gt (1 / ε)).imp fun N hN i hi ↦ ?_
  have h := Classical.choose_spec (rat_dense' (f i) (div_nat_pos i))
  refine lt_of_lt_of_le h ((div_le_iff₀' <| mod_cast succ_pos _).mpr ?_)
  rw [right_distrib]
  apply le_add_of_le_of_nonneg
  · exact (div_le_iff₀ hε).mp (le_trans (le_of_lt hN) (mod_cast hi))
  · apply le_of_lt
    simpa
/-
**Padic.exi_rat_seq_conv_cauchy** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：exi_rat_seq_conv_cauchy : IsCauSeq (padicNorm p) (limSeq f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Padic.exi_rat_seq_conv`：exi_rat_seq_conv {ε : Rat} (hε : 0 < ε) : exists
 N, forall i >= N, padicNormE (f i - (limSeq f i : Rat_[p]) : Rat_[p]) < ε
· 使用定理 `CauSeq.cauchy₂`：cauchy₂ (f : CauSeq β abv) {ε} : 0 < ε -> exists i, fora
ll j >= i, forall k >= i, abv (f j - f k) < ε
· 使用定理 `AbsoluteValue.isAbsoluteValue`：∀ {S : Type u_5} [inst : Semiring S] [ins
t_1 : PartialOrder S] {R : Type u_6} [inst_2 : Semiring R]   (abv : AbsoluteValu
e R S), IsAbsoluteV…
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `AbsoluteValue.add_le`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring R
] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) (x
 y : R), a…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_thirds`：add_thirds (a : α) : a / 3 + a / 3 + a / 3 = a
· 使用定理 `add_lt_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftStrictMono α] [AddRightStrictMono α] {a b c d : α},   a < b → c < d → a + c < 
…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
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
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `AbsoluteValue.map_sub`：∀ {R : Type u_3} {S : Type u_4} [inst : CommRing 
S] [inst_1 : PartialOrder S] [IsOrderedRing S] [inst_3 : Ring R]   (abv : Absolu
teValue R S…
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `le_of_max_le_left`：le_of_max_le_left {a b c : α} (h : max a b <= c) : a 
<= c
（共 65 条，此处仅展示前 30 条）
-/
theorem exi_rat_seq_conv_cauchy : IsCauSeq (padicNorm p) (limSeq f) := fun ε hε ↦ by
  have hε3 : 0 < ε / 3 := div_pos hε (by simp)
  let ⟨N, hN⟩ := exi_rat_seq_conv f hε3
  let ⟨N2, hN2⟩ := f.cauchy₂ hε3
  exists max N N2
  intro j hj
  suffices
    padicNormE (limSeq f j - f (max N N2) + (f (max N N2) - limSeq f (max N N2)) : ℚ_[p]) < ε by
    ring_nf at this
    rw [← padicNormE.eq_padic_norm']
    exact mod_cast this
  apply lt_of_le_of_lt
  · apply padicNormE.add_le
  · rw [← add_thirds ε]
    apply _root_.add_lt_add
    · suffices padicNormE (limSeq f j - f j + (f j - f (max N N2)) : ℚ_[p]) < ε / 3 + ε / 3 by
        simpa only [sub_add_sub_cancel]
      apply lt_of_le_of_lt
      · apply padicNormE.add_le
      · apply _root_.add_lt_add
        · rw [padicNormE.map_sub]
          apply mod_cast hN j
          exact le_of_max_le_left hj
        · exact hN2 _ (le_of_max_le_right hj) _ (le_max_right _ _)
    · apply mod_cast hN (max N N2)
      apply le_max_left
/-
**Padic.lim'** 是 Mathlib 中的一个定义，位于命名空间 `Padic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def lim' : PadicSeq p :=
  ⟨_, exi_rat_seq_conv_cauchy f⟩
/-
**Padic.lim** 是 Mathlib 中的一个定义，位于命名空间 `Padic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def lim : ℚ_[p] :=
  ⟦lim' f⟧
/-
**Padic.complete'** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：complete' : exists q : Rat_[p], forall ε > 0, exists N, forall i >= N, pad
icNormE (q - f i : Rat_[p]) < ε
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Padic.exi_rat_seq_conv`：exi_rat_seq_conv {ε : Rat} (hε : 0 < ε) : exists
 N, forall i >= N, padicNormE (f i - (limSeq f i : Rat_[p]) : Rat_[p]) < ε
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `padicNormE.defn`：defn (f : PadicSeq p) {ε : Rat} (hε : 0 < ε) : exists N
, forall i >= N, padicNormE (Padic.mk f - f i : Rat_[p]) < ε
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_add_sub_cancel`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : G), a 
- b + (b - c) = a - c
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `AbsoluteValue.add_le`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring R
] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) (x
 y : R), a…
· 使用定理 `add_halves`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2] (a :
 K), a / 2 + a / 2 = a
· 使用定理 `add_lt_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftStrictMono α] [AddRightStrictMono α] {a b c d : α},   a < b → c < d → a + c < 
…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
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
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_of_max_le_right`：le_of_max_le_right {a b c : α} (h : max a b <= c) : 
b <= c
· 使用定理 `AbsoluteValue.map_sub`：∀ {R : Type u_3} {S : Type u_4} [inst : CommRing 
S] [inst_1 : PartialOrder S] [IsOrderedRing S] [inst_3 : Ring R]   (abv : Absolu
teValue R S…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `le_of_max_le_left`：le_of_max_le_left {a b c : α} (h : max a b <= c) : a 
<= c
-/
theorem complete' : ∃ q : ℚ_[p], ∀ ε > 0, ∃ N, ∀ i ≥ N, padicNormE (q - f i : ℚ_[p]) < ε :=
  ⟨lim f, fun ε hε ↦ by
    obtain ⟨N, hN⟩ := exi_rat_seq_conv f (half_pos hε)
    obtain ⟨N2, hN2⟩ := padicNormE.defn (lim' f) (half_pos hε)
    refine ⟨max N N2, fun i hi ↦ ?_⟩
    rw [← sub_add_sub_cancel _ (lim' f i : ℚ_[p]) _]
    refine (padicNormE.add_le _ _).trans_lt ?_
    rw [← add_halves ε]
    apply _root_.add_lt_add
    · apply hN2 _ (le_of_max_le_right hi)
    · rw [padicNormE.map_sub]
      exact hN _ (le_of_max_le_left hi)⟩
/-
**Padic.complete''** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：complete'' : exists q : Rat_[p], forall ε > 0, exists N, forall i >= N, pa
dicNormE (f i - q : Rat_[p]) < ε
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Padic.complete'`：complete' : exists q : Rat_[p], forall ε > 0, exists N,
 forall i >= N, padicNormE (q - f i : Rat_[p]) < ε
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AbsoluteValue.map_sub`：∀ {R : Type u_3} {S : Type u_4} [inst : CommRing 
S] [inst_1 : PartialOrder S] [IsOrderedRing S] [inst_3 : Ring R]   (abv : Absolu
teValue R S…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
-/
theorem complete'' : ∃ q : ℚ_[p], ∀ ε > 0, ∃ N, ∀ i ≥ N, padicNormE (f i - q : ℚ_[p]) < ε := by
  obtain ⟨x, hx⟩ := complete' f
  refine ⟨x, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hx ε hε
  refine ⟨N, fun i hi => ?_⟩
  rw [padicNormE.map_sub]
  exact hN i hi
end Complete

section NormedSpace

variable (p : ℕ) [Fact p.Prime]

/-
**Padic.** 是 Mathlib 中的一个实例，位于命名空间 `Padic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Dist ℚ_[p] :=
  ⟨fun x y ↦ padicNormE (x - y : ℚ_[p])⟩
/-
**Padic.** 是 Mathlib 中的一个实例，位于命名空间 `Padic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsUltrametricDist ℚ_[p] :=
  ⟨fun x y z ↦ by simpa [dist] using padicNormE.nonarchimedean' (x - y) (y - z)⟩
/-
**Padic.metricSpace** 是 Mathlib 中的一个实例，位于命名空间 `Padic`。
形式化陈述：metricSpace : MetricSpace Rat_[p] where dist_self
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance metricSpace : MetricSpace ℚ_[p] where
  dist_self := by simp [dist]
  dist := dist
  dist_comm x y := by simp [dist, ← padicNormE.map_neg (x - y : ℚ_[p])]
  dist_triangle x y z := by
    dsimp [dist]
    exact mod_cast padicNormE.sub_le x y z
  eq_of_dist_eq_zero := by
    dsimp [dist]; intro _ _ h
    apply eq_of_sub_eq_zero
    apply padicNormE.eq_zero.1
    exact mod_cast h
/-
**Padic.** 是 Mathlib 中的一个实例，位于命名空间 `Padic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Norm ℚ_[p] :=
  ⟨fun x ↦ padicNormE x⟩
/-
**Padic.normedField** 是 Mathlib 中的一个实例，位于命名空间 `Padic`。
形式化陈述：normedField : NormedField Rat_[p] where dist_eq x y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance normedField : NormedField ℚ_[p] where
  dist_eq x y := by
    rw [add_comm, ← sub_eq_add_neg]
    change ‖x - y‖ = ‖y - x‖
    have : y - x = (-1) * (x - y) := by ring
    simp only [this, Norm.norm, map_mul, map_neg_eq_map, AbsoluteValue.map_one, one_mul]
  norm_mul := by simp [Norm.norm, map_mul]
  norm := norm
/-
**Padic.isAbsoluteValue** 是 Mathlib 中的一个实例，位于命名空间 `Padic`。
形式化陈述：isAbsoluteValue : IsAbsoluteValue fun a : Rat_[p] => ‖a‖ where abv_nonneg'
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `norm_eq_zero`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a‖ = 
0 ↔ a = 0
· 使用定理 `norm_add_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), ‖
a + b‖ ≤ ‖a‖ + ‖b‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `Rat.cast_mul`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p * q) = ↑p * ↑q
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
instance isAbsoluteValue : IsAbsoluteValue fun a : ℚ_[p] ↦ ‖a‖ where
  abv_nonneg' := norm_nonneg
  abv_eq_zero' := norm_eq_zero
  abv_add' := norm_add_le
  abv_mul' := by simp [Norm.norm, map_mul]
/-
**Padic.rat_dense** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：rat_dense (q : Rat_[p]) {ε : Real} (hε : 0 < ε) : exists r : Rat, ‖q - r‖ 
< ε
参数：q : Rat_[p]；hε : 0 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_rat_btwn`：exists_rat_btwn {x y : K} (h : x < y) : exists q : Rat,
 x < q ∧ q < y
· 使用定理 `Padic.rat_dense'`：rat_dense' (q : Rat_[p]) {ε : Rat} (hε : 0 < ε) : exis
ts r : Rat, padicNormE (q - r : Rat_[p]) < ε
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
-/
theorem rat_dense (q : ℚ_[p]) {ε : ℝ} (hε : 0 < ε) : ∃ r : ℚ, ‖q - r‖ < ε :=
  let ⟨ε', hε'l, hε'r⟩ := exists_rat_btwn hε
  let ⟨r, hr⟩ := rat_dense' q (ε := ε') (by simpa using hε'l)
  ⟨r, lt_trans (by simpa [Norm.norm] using hr) hε'r⟩
/-
**Padic.denseRange_ratCast** 是 Mathlib 中的一个引理，位于命名空间 `Padic`。
形式化陈述：denseRange_ratCast : DenseRange ((↑) : Rat -> Rat_[p])
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.mem_closure_range_iff`：mem_closure_range_iff {e : β -> α} {a : α}
 : a in closure (range e) ↔ forall ε > 0, exists k : β, dist a (e k) < ε
· 使用定理 `Padic.rat_dense`：rat_dense (q : Rat_[p]) {ε : Real} (hε : 0 < ε) : exist
s r : Rat, ‖q - r‖ < ε
-/
lemma denseRange_ratCast : DenseRange ((↑) : ℚ → ℚ_[p]) := by
  intro x
  rw [Metric.mem_closure_range_iff]
  exact fun _ ↦ Padic.rat_dense _ x

end NormedSpace

end Padic

namespace Padic

variable {p : ℕ} [hp : Fact p.Prime]

section NormedSpace

/-
**Padic.padicNormE.mul** 是 Mathlib 中的一个定理，位于命名空间 `Padic.padicNormE`。
形式化陈述：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (q r : ℚ_[p]), ‖q * r‖ = ‖q‖ * ‖r‖
参数：Nat.Prime p；q r : ℚ_[p]。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `Rat.cast_mul`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p * q) = ↑p * ↑q
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem padicNormE.mul (q r : ℚ_[p]) : ‖q * r‖ = ‖q‖ * ‖r‖ := by simp [Norm.norm, map_mul]
/-
**Padic.padicNormE.is_norm** 是 Mathlib 中的一个定理，位于命名空间 `Padic.padicNormE`。
形式化陈述：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (q : ℚ_[p]), ↑(padicNormE q) = ‖q‖
参数：Nat.Prime p；q : ℚ_[p]；padicNormE q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem padicNormE.is_norm (q : ℚ_[p]) : ↑(padicNormE q) = ‖q‖ := rfl
/-
**Padic.nonarchimedean** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：nonarchimedean (q r : Rat_[p]) : ‖q + r‖ <= max ‖q‖ ‖r‖
参数：q r : Rat_[p]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `padicNormE.nonarchimedean'`：nonarchimedean' (q r : Rat_[p]) : padicNormE
 (q + r : Rat_[p]) <= max (padicNormE q) (padicNormE r)
-/
theorem nonarchimedean (q r : ℚ_[p]) : ‖q + r‖ ≤ max ‖q‖ ‖r‖ := by
  dsimp [norm]
  exact mod_cast padicNormE.nonarchimedean' _ _
/-
**Padic.add_eq_max_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：add_eq_max_of_ne {q r : Rat_[p]} (h : ‖q‖ != ‖r‖) : ‖q + r‖ = max ‖q‖ ‖r‖
参数：h : ‖q‖ != ‖r‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `padicNormE.add_eq_max_of_ne'`：add_eq_max_of_ne' {q r : Rat_[p]} : padicN
ormE q != padicNormE r -> padicNormE (q + r : Rat_[p]) = max (padicNormE q) (pad
icNormE r)
-/
theorem add_eq_max_of_ne {q r : ℚ_[p]} (h : ‖q‖ ≠ ‖r‖) : ‖q + r‖ = max ‖q‖ ‖r‖ := by
  dsimp [norm] at h ⊢
  have : padicNormE q ≠ padicNormE r := mod_cast h
  exact mod_cast padicNormE.add_eq_max_of_ne' this

@[simp]
/-
**Padic.eq_padicNorm** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：eq_padicNorm (q : Rat) : ‖(q : Rat_[p])‖ = padicNorm p q
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `padicNormE.eq_padic_norm'`：eq_padic_norm' (q : Rat) : padicNormE (q : Ra
t_[p]) = padicNorm p q
-/
theorem eq_padicNorm (q : ℚ) : ‖(q : ℚ_[p])‖ = padicNorm p q := by
  dsimp [norm]
  rw [← padicNormE.eq_padic_norm']

@[simp]
/-
**Padic.norm_p** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：norm_p : ‖(p : Rat_[p])‖ = (p : Real)⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `padicNormE.eq_padic_norm'`：eq_padic_norm' (q : Rat) : padicNormE (q : Ra
t_[p]) = padicNorm p q
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `padicValNat_self`：padicValNat_self [Fact p.Prime] : padicValNat p p = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `padicValNat_one_right`：∀ (p : ℕ), padicValNat p 1 = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Rat.cast_inv`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p :
 ℚ), ↑p⁻¹ = (↑p)⁻¹
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_p : ‖(p : ℚ_[p])‖ = (p : ℝ)⁻¹ := by
  rw [← @Rat.cast_natCast ℝ _ p]
  rw [← @Rat.cast_natCast ℚ_[p] _ p]
  simp [hp.1.ne_zero, norm, padicNorm, padicValRat, padicValInt, zpow_neg,
    -Rat.cast_natCast]
/-
**Padic.norm_p_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：norm_p_lt_one : ‖(p : Rat_[p])‖ < 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Padic.norm_p`：norm_p : ‖(p : Rat_[p])‖ = (p : Real)⁻¹
· 使用引理 `inv_lt_one_of_one_lt₀`：inv_lt_one_of_one_lt₀ (ha : 1 < a) : a⁻¹ < 1
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
-/
theorem norm_p_lt_one : ‖(p : ℚ_[p])‖ < 1 := by
  rw [norm_p]
  exact inv_lt_one_of_one_lt₀ <| mod_cast hp.1.one_lt

@[simp high] -- Shortcut lemma with higher priority.
/-
**Padic.norm_p_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：norm_p_zpow (n : Int) : ‖(p : Rat_[p]) ^ n‖ = (p : Real) ^ (-n)
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_zpow`：norm_zpow : forall (a : α) (n : Int), ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `Padic.norm_p`：norm_p : ‖(p : Rat_[p])‖ = (p : Real)⁻¹
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `inv_zpow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a⁻
¹ ^ n = (a ^ n)⁻¹
-/
theorem norm_p_zpow (n : ℤ) : ‖(p : ℚ_[p]) ^ n‖ = (p : ℝ) ^ (-n) := by
  rw [norm_zpow, norm_p, zpow_neg, inv_zpow]

@[simp high] -- Shortcut lemma with higher priority.
/-
**Padic.norm_p_pow** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：norm_p_pow (n : Nat) : ‖(p : Rat_[p]) ^ n‖ = (p : Real) ^ (-n : Int)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Padic.norm_p_zpow`：norm_p_zpow (n : Int) : ‖(p : Rat_[p]) ^ n‖ = (p : Re
al) ^ (-n)
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
-/
theorem norm_p_pow (n : ℕ) : ‖(p : ℚ_[p]) ^ n‖ = (p : ℝ) ^ (-n : ℤ) := by
  rw [← norm_p_zpow, zpow_natCast]
/-
**Padic.** 是 Mathlib 中的一个实例，位于命名空间 `Padic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NontriviallyNormedField ℚ_[p] :=
  { Padic.normedField p with
    non_trivial :=
      ⟨p⁻¹, by
        rw [norm_inv, norm_p, inv_inv]
        exact mod_cast hp.1.one_lt⟩ }
/-
**Padic.padicNormE.image** 是 Mathlib 中的一个定理，位于命名空间 `Padic.padicNormE`。
形式化陈述：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] {q : ℚ_[p]}, q ≠ 0 → ∃ n, ‖q‖ = ↑(↑p ^
 (-n))
参数：Nat.Prime p；↑p ^ (-n)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PadicSeq.ne_zero_iff_nequiv_zero`：ne_zero_iff_nequiv_zero (f : PadicSeq 
p) : mk f != 0 ↔ ¬f ≈ 0
· 使用定理 `PadicSeq.norm_values_discrete`：norm_values_discrete (a : PadicSeq p) (ha
 : ¬a ≈ 0) : exists z : Int, a.norm = (p : Rat) ^ (-z)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected theorem padicNormE.image {q : ℚ_[p]} : q ≠ 0 → ∃ n : ℤ, ‖q‖ = ↑((p : ℚ) ^ (-n)) :=
  Quotient.inductionOn q fun f hf ↦
    have : ¬f ≈ 0 := (PadicSeq.ne_zero_iff_nequiv_zero f).1 hf
    let ⟨n, hn⟩ := PadicSeq.norm_values_discrete f this
    ⟨n, by rw [← hn]; rfl⟩
/-
**Padic.padicNormE.is_rat** 是 Mathlib 中的一个定理，位于命名空间 `Padic.padicNormE`。
形式化陈述：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (q : ℚ_[p]), ∃ q', ‖q‖ = ↑q'
参数：Nat.Prime p；q : ℚ_[p]。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Rat.cast_zero`：cast_zero : ((0 : Rat) : α) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Padic.padicNormE.image`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] {q : ℚ_[p]},
 q ≠ 0 → ∃ n, ‖q‖ = ↑(↑p ^ (-n))
-/
protected theorem padicNormE.is_rat (q : ℚ_[p]) : ∃ q' : ℚ, ‖q‖ = q' := by
  classical
  exact if h : q = 0 then ⟨0, by simp [h]⟩
  else
    let ⟨n, hn⟩ := padicNormE.image h
    ⟨_, hn⟩

/-- `ratNorm q`, for a `p`-adic number `q` is the `p`-adic norm of `q`, as rational number.

The lemma `padicNormE.eq_ratNorm` asserts `‖q‖ = ratNorm q`. -/
/-
**Padic.ratNorm** 是 Mathlib 中的一个定义，位于命名空间 `Padic`。
形式化陈述：ratNorm (q : Rat_[p]) : Rat
参数：q : Rat_[p]。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Padic.padicNormE.is_rat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (q : ℚ_[p])
, ∃ q', ‖q‖ = ↑q'

--- 原说明 ---
`ratNorm q`, for a `p`-adic number `q` is the `p`-adic norm of `q`, as rational 
number.

The lemma `padicNormE.eq_ratNorm` asserts `‖q‖ = ratNorm q`.
-/
def ratNorm (q : ℚ_[p]) : ℚ :=
  Classical.choose (padicNormE.is_rat q)
/-
**Padic.eq_ratNorm** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：eq_ratNorm (q : Rat_[p]) : ‖q‖ = ratNorm q
参数：q : Rat_[p]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Padic.padicNormE.is_rat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (q : ℚ_[p])
, ∃ q', ‖q‖ = ↑q'
-/
theorem eq_ratNorm (q : ℚ_[p]) : ‖q‖ = ratNorm q :=
  Classical.choose_spec (padicNormE.is_rat q)
/-
**Padic.norm_rat_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：norm_rat_le_one : forall {q : Rat} (_ : ¬p ∣ q.den), ‖(q : Rat_[p])‖ <= 1 
| ⟨n, d, hn, hd⟩ => fun hq : ¬p ∣ d => if hnz : n = 0 then by have : (⟨n, d, hn,
 hd⟩ : Rat) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Rat.mk'`：mk'_num_den (q : Rat) : mk' q.num q.den q.den_nz q.reduced = q
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Rat.zero_iff_num_zero`：zero_iff_num_zero {q : Rat} : q = 0 ↔ q.num = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.cast_zero`：cast_zero : ((0 : Rat) : α) = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Padic.eq_padicNorm`：eq_padicNorm (q : Rat) : ‖(q : Rat_[p])‖ = padicNorm
 p q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `padicNorm.eq_zpow_of_nonzero`：∀ {p : ℕ} {q : ℚ}, q ≠ 0 → padicNorm p q =
 ↑p ^ (-padicValRat p q)
· 使用定理 `padicValRat.eq_1`：∀ (p : ℕ) (q : ℚ), padicValRat p q = ↑(padicValInt p q
.num) - ↑(padicValNat p q.den)
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `padicValNat.eq_zero_of_not_dvd`：eq_zero_of_not_dvd {n : Nat} (h : ¬p ∣ n
) : padicValNat p n = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用引理 `inv_le_one_of_one_le₀`：inv_le_one_of_one_le₀ (ha : 1 <= a) : a⁻¹ <= 1
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `Nat.one_le_pow`：∀ (n m : ℕ), 0 < m → 1 ≤ m ^ n
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
（共 31 条，此处仅展示前 30 条）
-/
theorem norm_rat_le_one : ∀ {q : ℚ} (_ : ¬p ∣ q.den), ‖(q : ℚ_[p])‖ ≤ 1
  | ⟨n, d, hn, hd⟩ => fun hq : ¬p ∣ d ↦
    if hnz : n = 0 then by
      have : (⟨n, d, hn, hd⟩ : ℚ) = 0 := Rat.zero_iff_num_zero.mpr hnz
      norm_num [this]
    else by
      have hnz' : (⟨n, d, hn, hd⟩ : ℚ) ≠ 0 := mt Rat.zero_iff_num_zero.1 hnz
      rw [eq_padicNorm]
      norm_cast
      -- Porting note: `Nat.cast_zero` instead of another `norm_cast` call
      rw [padicNorm.eq_zpow_of_nonzero hnz', padicValRat, neg_sub,
        padicValNat.eq_zero_of_not_dvd hq, Nat.cast_zero, zero_sub, zpow_neg, zpow_natCast]
      apply inv_le_one_of_one_le₀
      norm_cast
      apply one_le_pow
      exact hp.1.pos
/-
**Padic.norm_int_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：norm_int_le_one (z : Int) : ‖(z : Rat_[p])‖ <= 1
参数：z : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Padic.norm_rat_le_one`：norm_rat_le_one : forall {q : Rat} (_ : ¬p ∣ q.de
n), ‖(q : Rat_[p])‖ <= 1 | ⟨n, d, hn, hd⟩ => fun hq : ¬p ∣ d => if hnz : n = 0 t
hen by have…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
-/
theorem norm_int_le_one (z : ℤ) : ‖(z : ℚ_[p])‖ ≤ 1 :=
  suffices ‖((z : ℚ) : ℚ_[p])‖ ≤ 1 by simpa
  norm_rat_le_one <| by simp [hp.1.ne_one]

@[simp]
/-
**Padic.norm_intCast_lt_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：norm_intCast_lt_one_iff {k : Int} : ‖(k : Rat_[p])‖ < 1 ↔ ↑p ∣ k
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `Padic.eq_padicNorm`：eq_padicNorm (q : Rat) : ‖(q : Rat_[p])‖ = padicNorm
 p q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Rat.cast_one`：cast_one : ((1 : Rat) : α) = 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `padicNorm.int_eq_one_iff`：int_eq_one_iff (m : Int) : padicNorm p m = 1 ↔
 ¬(p : Int) ∣ m
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Padic.padicNormE.mul`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (q r : ℚ_[p]),
 ‖q * r‖ = ‖q‖ * ‖r‖
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Padic.norm_int_le_one`：norm_int_le_one (z : Int) : ‖(z : Rat_[p])‖ <= 1
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Padic.norm_p`：norm_p : ‖(p : Rat_[p])‖ = (p : Real)⁻¹
· 使用引理 `inv_lt_one_of_one_lt₀`：inv_lt_one_of_one_lt₀ (ha : 1 < a) : a⁻¹ < 1
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
（共 33 条，此处仅展示前 30 条）
-/
theorem norm_intCast_lt_one_iff {k : ℤ} : ‖(k : ℚ_[p])‖ < 1 ↔ ↑p ∣ k := by
  constructor
  · intro h
    contrapose! h
    apply le_of_eq
    rw [eq_comm]
    calc
      ‖(k : ℚ_[p])‖ = ‖((k : ℚ) : ℚ_[p])‖ := by norm_cast
      _ = padicNorm p k := eq_padicNorm _
      _ = 1 := mod_cast (int_eq_one_iff k).mpr h
  · rintro ⟨x, rfl⟩
    push_cast
    rw [padicNormE.mul]
    calc
      _ ≤ ‖(p : ℚ_[p])‖ * 1 :=
        mul_le_mul le_rfl (by simpa using norm_int_le_one _) (norm_nonneg _) (norm_nonneg _)
      _ < 1 := by
        rw [mul_one, norm_p]
        exact inv_lt_one_of_one_lt₀ <| mod_cast hp.1.one_lt

@[simp]
/-
**Padic.norm_natCast_lt_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `Padic`。
形式化陈述：norm_natCast_lt_one_iff {n : Nat} : ‖(n : Rat_[p])‖ < 1 ↔ p ∣ n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Padic.norm_intCast_lt_one_iff`：norm_intCast_lt_one_iff {k : Int} : ‖(k :
 Rat_[p])‖ < 1 ↔ ↑p ∣ k
-/
lemma norm_natCast_lt_one_iff {n : ℕ} :
    ‖(n : ℚ_[p])‖ < 1 ↔ p ∣ n := by
  simpa [Int.natCast_dvd_natCast] using norm_intCast_lt_one_iff (p := p) (k := n)

@[simp]
/-
**Padic.norm_intCast_eq_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `Padic`。
形式化陈述：norm_intCast_eq_one_iff {z : Int} : ‖(z : Rat_[p])‖ = 1 ↔ IsCoprime z p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.Prime.dvd_iff_not_coprime`：∀ {p n : ℕ}, Nat.Prime p → (p ∣ n ↔ ¬p.Co
prime n)
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `norm_natAbs`：norm_natAbs (z : Int) : ‖(z.natAbs : α)‖ = ‖(z : α)‖
-/
lemma norm_intCast_eq_one_iff {z : ℤ} :
    ‖(z : ℚ_[p])‖ = 1 ↔ IsCoprime z p := by
  rw [← not_iff_not]
  simp [Nat.coprime_comm, ← norm_natCast_lt_one_iff, -norm_intCast_lt_one_iff,
    Int.isCoprime_iff_gcd_eq_one, Nat.coprime_iff_gcd_eq_one, Int.gcd,
    ← hp.out.dvd_iff_not_coprime, norm_natAbs, -cast_natAbs, norm_int_le_one]

@[simp]
/-
**Padic.norm_natCast_eq_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `Padic`。
形式化陈述：norm_natCast_eq_one_iff {n : Nat} : ‖(n : Rat_[p])‖ = 1 ↔ p.Coprime n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.coprime_comm`：∀ {n m : ℕ}, n.Coprime m ↔ m.Coprime n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用引理 `Padic.norm_intCast_eq_one_iff`：norm_intCast_eq_one_iff {z : Int} : ‖(z :
 Rat_[p])‖ = 1 ↔ IsCoprime z p
-/
lemma norm_natCast_eq_one_iff {n : ℕ} :
    ‖(n : ℚ_[p])‖ = 1 ↔ p.Coprime n := by
  simpa [p.coprime_comm] using norm_intCast_eq_one_iff (p := p) (z := n)
/-
**Padic.norm_int_le_pow_iff_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：norm_int_le_pow_iff_dvd (k : Int) (n : Nat) : ‖(k : Rat_[p])‖ <= (p : Real
) ^ (-n : Int) ↔ (p ^ n : Int) ∣ k
参数：k : Int；n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `Padic.instCharZero`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)], CharZero ℚ_[p
]
· 使用定理 `Padic.eq_padicNorm`：eq_padicNorm (q : Rat) : ‖(q : Rat_[p])‖ = padicNorm
 p q
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `padicNorm.dvd_iff_norm_le`：dvd_iff_norm_le {n : Nat} {z : Int} : ↑(p ^ n
) ∣ z ↔ padicNorm p z <= (p : Rat) ^ (-n : Int)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem norm_int_le_pow_iff_dvd (k : ℤ) (n : ℕ) :
    ‖(k : ℚ_[p])‖ ≤ (p : ℝ) ^ (-n : ℤ) ↔ (p ^ n : ℤ) ∣ k := by
  have : (p : ℝ) ^ (-n : ℤ) = (p : ℚ) ^ (-n : ℤ) := by simp
  rw [show (k : ℚ_[p]) = ((k : ℚ) : ℚ_[p]) by norm_cast, eq_padicNorm, this]
  norm_cast
  rw [← padicNorm.dvd_iff_norm_le]
/-
**Padic.norm_eq_of_norm_add_lt_right** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：norm_eq_of_norm_add_lt_right {z1 z2 : Rat_[p]} (h : ‖z1 + z2‖ < ‖z2‖) : ‖z
1‖ = ‖z2‖
参数：h : ‖z1 + z2‖ < ‖z2‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_contradiction`：by_contradiction {p : Prop} : (¬p -> False) -> p
· 使用定理 `not_lt_of_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Padic.add_eq_max_of_ne`：add_eq_max_of_ne {q r : Rat_[p]} (h : ‖q‖ != ‖r‖
) : ‖q + r‖ = max ‖q‖ ‖r‖
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
-/
theorem norm_eq_of_norm_add_lt_right {z1 z2 : ℚ_[p]} (h : ‖z1 + z2‖ < ‖z2‖) : ‖z1‖ = ‖z2‖ :=
  _root_.by_contradiction fun hne ↦
    not_lt_of_ge (by rw [add_eq_max_of_ne hne]; apply le_max_right) h
/-
**Padic.norm_eq_of_norm_add_lt_left** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：norm_eq_of_norm_add_lt_left {z1 z2 : Rat_[p]} (h : ‖z1 + z2‖ < ‖z1‖) : ‖z1
‖ = ‖z2‖
参数：h : ‖z1 + z2‖ < ‖z1‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_contradiction`：by_contradiction {p : Prop} : (¬p -> False) -> p
· 使用定理 `not_lt_of_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Padic.add_eq_max_of_ne`：add_eq_max_of_ne {q r : Rat_[p]} (h : ‖q‖ != ‖r‖
) : ‖q + r‖ = max ‖q‖ ‖r‖
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
-/
theorem norm_eq_of_norm_add_lt_left {z1 z2 : ℚ_[p]} (h : ‖z1 + z2‖ < ‖z1‖) : ‖z1‖ = ‖z2‖ :=
  _root_.by_contradiction fun hne ↦
    not_lt_of_ge (by rw [add_eq_max_of_ne hne]; apply le_max_left) h
/-
**Padic.norm_eq_of_norm_sub_lt_right** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：norm_eq_of_norm_sub_lt_right {z1 z2 : Rat_[p]} (h : ‖z1 - z2‖ < ‖z2‖) : ‖z
1‖ = ‖z2‖
参数：h : ‖z1 - z2‖ < ‖z2‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `Padic.norm_eq_of_norm_add_lt_right`：norm_eq_of_norm_add_lt_right {z1 z2 
: Rat_[p]} (h : ‖z1 + z2‖ < ‖z2‖) : ‖z1‖ = ‖z2‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem norm_eq_of_norm_sub_lt_right {z1 z2 : ℚ_[p]} (h : ‖z1 - z2‖ < ‖z2‖) : ‖z1‖ = ‖z2‖ := by
  rw [← norm_neg z2]
  apply norm_eq_of_norm_add_lt_right
  simp [← sub_eq_add_neg, h]
/-
**Padic.norm_eq_of_norm_sub_lt_left** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：norm_eq_of_norm_sub_lt_left {z1 z2 : Rat_[p]} (h : ‖z1 - z2‖ < ‖z1‖) : ‖z1
‖ = ‖z2‖
参数：h : ‖z1 - z2‖ < ‖z1‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Padic.norm_eq_of_norm_sub_lt_right`：norm_eq_of_norm_sub_lt_right {z1 z2 
: Rat_[p]} (h : ‖z1 - z2‖ < ‖z2‖) : ‖z1‖ = ‖z2‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
-/
theorem norm_eq_of_norm_sub_lt_left {z1 z2 : ℚ_[p]} (h : ‖z1 - z2‖ < ‖z1‖) : ‖z1‖ = ‖z2‖ := by
  rw [eq_comm]
  apply norm_eq_of_norm_sub_lt_right
  simpa [← norm_neg (z1 - _)] using h

@[simp]
/-
**Padic.norm_natCast_p_sub_one** 是 Mathlib 中的一个引理，位于命名空间 `Padic`。
形式化陈述：norm_natCast_p_sub_one : ‖((p - 1 : Nat) : Rat_[p])‖ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Padic.norm_natCast_eq_one_iff`：norm_natCast_eq_one_iff {n : Nat} : ‖(n :
 Rat_[p])‖ = 1 ↔ p.Coprime n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.coprime_self_sub_right`：coprime_self_sub_right {m n : Nat} (h : m <=
 n) : Coprime n (n - m) ↔ Coprime n m
· 使用定理 `Nat.Prime.one_le`：∀ {p : ℕ}, Nat.Prime p → 1 ≤ p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Nat.coprime_one_right`：∀ (n : ℕ), n.Coprime 1
-/
lemma norm_natCast_p_sub_one :
    ‖((p - 1 : ℕ) : ℚ_[p])‖ = 1 := by
  rw [norm_natCast_eq_one_iff]
  exact (coprime_self_sub_right hp.out.one_le).mpr p.coprime_one_right

end NormedSpace

/-
**Padic.complete** 是 Mathlib 中的一个实例，位于命名空间 `Padic`。
形式化陈述：complete : CauSeq.IsComplete Rat_[p] norm where isComplete f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CauSeq.isCauSeq`：isCauSeq (f : CauSeq β abv) : IsCauSeq abv f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Padic.complete''`：complete'' : exists q : Rat_[p], forall ε > 0, exists 
N, forall i >= N, padicNormE (f i - q : Rat_[p]) < ε
· 使用定理 `exists_rat_btwn`：exists_rat_btwn {x y : K} (h : x < y) : exists q : Rat,
 x < q ∧ q < y
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
instance complete : CauSeq.IsComplete ℚ_[p] norm where
  isComplete f := by
    have cau_seq_norm_e : IsCauSeq padicNormE f := fun ε hε => by
      have h := isCauSeq f ε (mod_cast hε)
      dsimp [norm] at h
      exact mod_cast h
    -- Porting note: Padic.complete' works with `f i - q`, but the goal needs `q - f i`,
    -- using `rewrite [padicNormE.map_sub]` causes time out, so a separate lemma is created
    obtain ⟨q, hq⟩ := Padic.complete'' ⟨f, cau_seq_norm_e⟩
    exists q
    intro ε hε
    obtain ⟨ε', hε'⟩ := exists_rat_btwn hε
    norm_cast at hε'
    obtain ⟨N, hN⟩ := hq ε' hε'.1
    exists N
    intro i hi
    have h := hN i hi
    change norm (f i - q) < ε
    refine lt_trans ?_ hε'.2
    dsimp [norm]
    exact mod_cast h
/-
**Padic.padicNormE_lim_le** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：padicNormE_lim_le {f : CauSeq Rat_[p] norm} {a : Real} (ha : 0 < a) (hf : 
forall i, ‖f i‖ <= a) : ‖f.lim‖ <= a
参数：ha : 0 < a；hf : forall i, ‖f i‖ <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.symm`：∀ {α : Sort u} [inst : Setoid α] {a b : α}, a ≈ b → b ≈ a
· 使用定理 `CauSeq.equiv_lim`：equiv_lim (s : CauSeq β abv) : s ≈ const abv (lim s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Padic.nonarchimedean`：nonarchimedean (q r : Rat_[p]) : ‖q + r‖ <= max ‖q
‖ ‖r‖
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem padicNormE_lim_le {f : CauSeq ℚ_[p] norm} {a : ℝ} (ha : 0 < a) (hf : ∀ i, ‖f i‖ ≤ a) :
    ‖f.lim‖ ≤ a := by
  obtain ⟨N, hN⟩ := Setoid.symm (CauSeq.equiv_lim f) _ ha
  calc
    ‖f.lim‖ = ‖f.lim - f N + f N‖ := by simp
    _ ≤ max ‖f.lim - f N‖ ‖f N‖ := nonarchimedean _ _
    _ ≤ a := max_le (le_of_lt (hN _ le_rfl)) (hf _)

open Filter Set
/-
**Padic.** 是 Mathlib 中的一个实例，位于命名空间 `Padic`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompleteSpace ℚ_[p] := by
  apply complete_of_cauchySeq_tendsto
  intro u hu
  let c : CauSeq ℚ_[p] norm := ⟨u, Metric.cauchySeq_iff'.mp hu⟩
  refine ⟨c.lim, fun s h ↦ ?_⟩
  rcases Metric.mem_nhds_iff.1 h with ⟨ε, ε0, hε⟩
  have := c.equiv_lim ε ε0
  simp only [mem_map, mem_atTop_sets]
  exact this.imp fun N hN n hn ↦ hε (hN n hn)

/-! ### Valuation on `ℚ_[p]` -/


/-- `Padic.valuation` lifts the `p`-adic valuation on rationals to `ℚ_[p]`. -/
/-
**Padic.valuation** 是 Mathlib 中的一个定义，位于命名空间 `Padic`。
形式化陈述：valuation : Rat_[p] -> Int
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)

--- 原说明 ---
`Padic.valuation` lifts the `p`-adic valuation on rationals to `ℚ_[p]`.
-/
def valuation : ℚ_[p] → ℤ :=
  Quotient.lift (@PadicSeq.valuation p _) fun f g h ↦ by
    by_cases hf : f ≈ 0
    · have hg : g ≈ 0 := Setoid.trans (Setoid.symm h) hf
      simp [hf, hg, PadicSeq.valuation]
    · have hg : ¬g ≈ 0 := fun hg ↦ hf (Setoid.trans h hg)
      rw [PadicSeq.val_eq_iff_norm_eq hf hg]
      exact PadicSeq.norm_equiv h

@[simp]
/-
**Padic.valuation_zero** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：valuation_zero : valuation (0 : Rat_[p]) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Padic.const_equiv`：const_equiv {q r : Rat} : const (padicNorm p) q ≈ con
st (padicNorm p) r ↔ q = r
-/
theorem valuation_zero : valuation (0 : ℚ_[p]) = 0 :=
  dif_pos ((const_equiv p).2 rfl)
/-
**Padic.norm_eq_zpow_neg_valuation** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：norm_eq_zpow_neg_valuation {x : Rat_[p]} : x != 0 -> ‖x‖ = (p : Real) ^ (-
x.valuation)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PadicSeq.norm_eq_zpow_neg_valuation`：norm_eq_zpow_neg_valuation {f : Pad
icSeq p} (hf : ¬f ≈ 0) : f.norm = (p : Rat) ^ (-f.valuation : Int)
· 使用定理 `CauSeq.not_limZero_of_not_congr_zero`：not_limZero_of_not_congr_zero {f :
 CauSeq _ abv} (hf : ¬f ≈ 0) : ¬LimZero f
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用引理 `Rat.cast_zpow`：cast_zpow (p : Rat) (n : Int) : ↑(p ^ n) = (p ^ n : α)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
-/
theorem norm_eq_zpow_neg_valuation {x : ℚ_[p]} : x ≠ 0 → ‖x‖ = (p : ℝ) ^ (-x.valuation) := by
  induction x using Quotient.inductionOn with | _ f
  intro hf
  change (PadicSeq.norm _ : ℝ) = (p : ℝ) ^ (-PadicSeq.valuation _)
  rw [PadicSeq.norm_eq_zpow_neg_valuation]
  · rw [Rat.cast_zpow, Rat.cast_natCast]
  · apply CauSeq.not_limZero_of_not_congr_zero
    contrapose hf
    apply Quotient.sound
    simpa using hf

@[simp]
/-
**Padic.valuation_ratCast** 是 Mathlib 中的一个引理，位于命名空间 `Padic`。
形式化陈述：valuation_ratCast (q : Rat) : valuation (q : Rat_[p]) = padicValRat p q
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.cast_zero`：cast_zero : ((0 : Rat) : α) = 0
· 使用定理 `Padic.valuation_zero`：valuation_zero : valuation (0 : Rat_[p]) = 0
· 使用定理 `padicValRat.zero`：∀ {p : ℕ}, padicValRat p 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_injective`：∀ {G : Type u_3} [inst : InvolutiveNeg G], Function.Injec
tive Neg.neg
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用引理 `zpow_right_strictMono₀`：zpow_right_strictMono₀ (ha : 1 < a) : StrictMono
 fun n : Int => a ^ n
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Padic.norm_eq_zpow_neg_valuation`：norm_eq_zpow_neg_valuation {x : Rat_[p
]} : x != 0 -> ‖x‖ = (p : Real) ^ (-x.valuation)
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Padic.instCharZero`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)], CharZero ℚ_[p
]
· 使用定理 `Padic.eq_padicNorm`：eq_padicNorm (q : Rat) : ‖(q : Rat_[p])‖ = padicNorm
 p q
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
· 使用引理 `Rat.cast_zpow`：cast_zpow (p : Rat) (n : Int) : ↑(p ^ n) = (p ^ n : α)
· 使用定理 `Rat.cast_inj`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] {p q
 : ℚ}, ↑p = ↑q ↔ p = q
· 使用定理 `padicNorm.eq_zpow_of_nonzero`：∀ {p : ℕ} {q : ℚ}, q ≠ 0 → padicNorm p q =
 ↑p ^ (-padicValRat p q)
-/
lemma valuation_ratCast (q : ℚ) : valuation (q : ℚ_[p]) = padicValRat p q := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp only [Rat.cast_zero, valuation_zero, padicValRat.zero]
  refine neg_injective ((zpow_right_strictMono₀ (mod_cast hp.out.one_lt)).injective
    <| (norm_eq_zpow_neg_valuation (mod_cast hq)).symm.trans ?_)
  rw [eq_padicNorm, ← Rat.cast_natCast, ← Rat.cast_zpow, Rat.cast_inj]
  exact padicNorm.eq_zpow_of_nonzero hq

@[simp]
/-
**Padic.valuation_intCast** 是 Mathlib 中的一个引理，位于命名空间 `Padic`。
形式化陈述：valuation_intCast (n : Int) : valuation (n : Rat_[p]) = padicValInt p n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用引理 `Padic.valuation_ratCast`：valuation_ratCast (q : Rat) : valuation (q : Ra
t_[p]) = padicValRat p q
· 使用定理 `padicValRat.of_int`：of_int {z : Int} : padicValRat p z = padicValInt p z
-/
lemma valuation_intCast (n : ℤ) : valuation (n : ℚ_[p]) = padicValInt p n := by
  rw [← Rat.cast_intCast, valuation_ratCast, padicValRat.of_int]

@[simp]
/-
**Padic.valuation_natCast** 是 Mathlib 中的一个引理，位于命名空间 `Padic`。
形式化陈述：valuation_natCast (n : Nat) : valuation (n : Rat_[p]) = padicValNat p n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
· 使用引理 `Padic.valuation_ratCast`：valuation_ratCast (q : Rat) : valuation (q : Ra
t_[p]) = padicValRat p q
· 使用定理 `padicValRat.of_nat`：of_nat {n : Nat} : padicValRat p n = padicValNat p n
-/
lemma valuation_natCast (n : ℕ) : valuation (n : ℚ_[p]) = padicValNat p n := by
  rw [← Rat.cast_natCast, valuation_ratCast, padicValRat.of_nat]

@[simp]
/-
**Padic.valuation_ofNat** 是 Mathlib 中的一个引理，位于命名空间 `Padic`。
形式化陈述：valuation_ofNat (n : Nat) [n.AtLeastTwo] : valuation (ofNat(n) : Rat_[p]) 
= padicValNat p n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Padic.valuation_natCast`：valuation_natCast (n : Nat) : valuation (n : Ra
t_[p]) = padicValNat p n
-/
lemma valuation_ofNat (n : ℕ) [n.AtLeastTwo] :
    valuation (ofNat(n) : ℚ_[p]) = padicValNat p n :=
  valuation_natCast n

@[simp]
/-
**Padic.valuation_one** 是 Mathlib 中的一个引理，位于命名空间 `Padic`。
形式化陈述：valuation_one : valuation (1 : Rat_[p]) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `Padic.valuation_natCast`：valuation_natCast (n : Nat) : valuation (n : Ra
t_[p]) = padicValNat p n
· 使用定理 `padicValNat_one_right`：∀ (p : ℕ), padicValNat p 1 = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
-/
lemma valuation_one : valuation (1 : ℚ_[p]) = 0 := by
  rw [← Nat.cast_one, valuation_natCast, padicValNat_one_right, cast_zero]

-- not @[simp], since simp can prove it
/-
**Padic.valuation_p** 是 Mathlib 中的一个引理，位于命名空间 `Padic`。
形式化陈述：valuation_p : valuation (p : Rat_[p]) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Padic.valuation_natCast`：valuation_natCast (n : Nat) : valuation (n : Ra
t_[p]) = padicValNat p n
· 使用定理 `padicValNat_self`：padicValNat_self [Fact p.Prime] : padicValNat p p = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
lemma valuation_p : valuation (p : ℚ_[p]) = 1 := by
  rw [valuation_natCast, padicValNat_self, cast_one]
/-
**Padic.le_valuation_add** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：le_valuation_add {x y : Rat_[p]} (hxy : x + y != 0) : min x.valuation y.va
luation <= (x + y).valuation
参数：hxy : x + y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用定理 `Padic.nonarchimedean`：nonarchimedean (q r : Rat_[p]) : ‖q + r‖ <= max ‖q
‖ ‖r‖
· 使用定理 `Padic.norm_eq_zpow_neg_valuation`：norm_eq_zpow_neg_valuation {x : Rat_[p
]} : x != 0 -> ‖x‖ = (p : Real) ^ (-x.valuation)
· 使用定理 `zpow_le_zpow_iff_right₀`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [in
st_1 : PartialOrder G₀] [PosMulReflectLT G₀] {a : G₀} [ZeroLEOneClass G₀]   {m n
 : ℤ}, 1 < a …
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem le_valuation_add {x y : ℚ_[p]} (hxy : x + y ≠ 0) :
    min x.valuation y.valuation ≤ (x + y).valuation := by
  by_cases hx : x = 0
  · simpa only [hx, zero_add] using min_le_right _ _
  by_cases hy : y = 0
  · simpa only [hy, add_zero] using min_le_left _ _
  have : ‖x + y‖ ≤ max ‖x‖ ‖y‖ := nonarchimedean x y
  simpa only [norm_eq_zpow_neg_valuation hxy, norm_eq_zpow_neg_valuation hx,
    norm_eq_zpow_neg_valuation hy, le_max_iff,
    zpow_le_zpow_iff_right₀ (mod_cast hp.out.one_lt : 1 < (p : ℝ)), neg_le_neg_iff, ← min_le_iff]

@[simp]
/-
**Padic.valuation_mul** 是 Mathlib 中的一个引理，位于命名空间 `Padic`。
形式化陈述：valuation_mul {x y : Rat_[p]} (hx : x != 0) (hy : y != 0) : (x * y).valuat
ion = x.valuation + y.valuation
参数：hx : x != 0；hy : y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `NeZero.pos`：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] :
 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `neg_add`：neg_add {R} [CommRing R] {a₁ a₂ b₁ b₂ : R} (_ : -a₁ = b₁) (_ : 
-a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂
· 使用定理 `zpow_right_inj₀`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : L
inearOrder G₀] {a : G₀} {m n : ℤ} [PosMulStrictMono G₀]   [ZeroLEOneClass G₀], 0
 < a …
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `zpow_add₀`：zpow_add₀ (ha : a != 0) (m n : Int) : a ^ (m + n) = a ^ m * a
 ^ n
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Padic.norm_eq_zpow_neg_valuation`：norm_eq_zpow_neg_valuation {x : Rat_[p
]} : x != 0 -> ‖x‖ = (p : Real) ^ (-x.valuation)
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
-/
lemma valuation_mul {x y : ℚ_[p]} (hx : x ≠ 0) (hy : y ≠ 0) :
    (x * y).valuation = x.valuation + y.valuation := by
  have h_norm : ‖x * y‖ = ‖x‖ * ‖y‖ := norm_mul x y
  have hp_ne_one : (p : ℝ) ≠ 1 := mod_cast (Fact.out : p.Prime).ne_one
  have hp_pos : (0 : ℝ) < p := mod_cast NeZero.pos _
  rwa [norm_eq_zpow_neg_valuation hx, norm_eq_zpow_neg_valuation hy,
    norm_eq_zpow_neg_valuation (mul_ne_zero hx hy), ← zpow_add₀ hp_pos.ne',
    zpow_right_inj₀ hp_pos hp_ne_one, ← neg_add, neg_inj] at h_norm

@[simp]
/-
**Padic.valuation_inv** 是 Mathlib 中的一个引理，位于命名空间 `Padic`。
形式化陈述：valuation_inv (x : Rat_[p]) : x⁻¹.valuation = -x.valuation
参数：x : Rat_[p]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `Padic.valuation_zero`：valuation_zero : valuation (0 : Rat_[p]) = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `NeZero.pos`：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] :
 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `zpow_right_inj₀`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : L
inearOrder G₀] {a : G₀} {m n : ℤ} [PosMulStrictMono G₀]   [ZeroLEOneClass G₀], 0
 < a …
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `Padic.norm_eq_zpow_neg_valuation`：norm_eq_zpow_neg_valuation {x : Rat_[p
]} : x != 0 -> ‖x‖ = (p : Real) ^ (-x.valuation)
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
-/
lemma valuation_inv (x : ℚ_[p]) : x⁻¹.valuation = -x.valuation := by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  have h_norm : ‖x⁻¹‖ = ‖x‖⁻¹ := norm_inv x
  have hp_ne_one : (p : ℝ) ≠ 1 := mod_cast (Fact.out : p.Prime).ne_one
  have hp_pos : (0 : ℝ) < p := mod_cast NeZero.pos _
  rwa [norm_eq_zpow_neg_valuation hx, norm_eq_zpow_neg_valuation <| inv_ne_zero hx,
    ← zpow_neg, zpow_right_inj₀ hp_pos hp_ne_one, neg_inj] at h_norm

@[simp]
/-
**Padic.valuation_pow** 是 Mathlib 中的一个引理，位于命名空间 `Padic`。
形式化陈述：valuation_pow (x : Rat_[p]) : forall n : Nat, (x ^ n).valuation = n * x.va
luation | 0 => by simp | n + 1 => by obtain rfl | hx
参数：x : Rat_[p]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma valuation_pow (x : ℚ_[p]) : ∀ n : ℕ, (x ^ n).valuation = n * x.valuation
  | 0 => by simp
  | n + 1 => by
    obtain rfl | hx := eq_or_ne x 0
    · simp
    · simp [pow_succ, hx, valuation_mul, valuation_pow, _root_.add_one_mul]

@[simp]
/-
**Padic.valuation_zpow** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (x : ℚ_[p]) (n : ℤ), (x ^ n).valuation
 = n * x.valuation
参数：Nat.Prime p；x : ℚ_[p]；n : ℤ；x ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用引理 `Padic.valuation_pow`：valuation_pow (x : Rat_[p]) : forall n : Nat, (x ^ 
n).valuation = n * x.valuation | 0 => by simp | n + 1 => by obtain rfl | hx
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用引理 `Padic.valuation_inv`：valuation_inv (x : Rat_[p]) : x⁻¹.valuation = -x.va
luation
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `Int.instIsCancelMulZero`：IsCancelMulZero ℤ
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
lemma valuation_zpow (x : ℚ_[p]) : ∀ n : ℤ, (x ^ n).valuation = n * x.valuation
  | (n : ℕ) => by simp
  | .negSucc n => by simp [← neg_mul]; simp [Int.negSucc_eq]

open scoped Classical in
/-- The additive `p`-adic valuation on `ℚ_[p]`, with values in `WithTop ℤ`. -/
/-
**Padic.addValuationDef** 是 Mathlib 中的一个定义，位于命名空间 `Padic`。
形式化陈述：addValuationDef : Rat_[p] -> WithTop Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The additive `p`-adic valuation on `ℚ_[p]`, with values in `WithTop ℤ`.
-/
def addValuationDef : ℚ_[p] → WithTop ℤ :=
  fun x ↦ if x = 0 then ⊤ else x.valuation

@[simp]
/-
**Padic.AddValuation.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `Padic.AddValuation`。
形式化陈述：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], Padic.addValuationDef 0 = ⊤
参数：Nat.Prime p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Padic.addValuationDef.eq_1`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (x : ℚ_[
p]), x.addValuationDef = if x = 0 then ⊤ else ↑x.valuation
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem AddValuation.map_zero : addValuationDef (0 : ℚ_[p]) = ⊤ := by
  rw [addValuationDef, if_pos rfl]

@[simp]
/-
**Padic.AddValuation.map_one** 是 Mathlib 中的一个定理，位于命名空间 `Padic.AddValuation`。
形式化陈述：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], Padic.addValuationDef 1 = 0
参数：Nat.Prime p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Padic.addValuationDef.eq_1`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (x : ℚ_[
p]), x.addValuationDef = if x = 0 then ⊤ else ↑x.valuation
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Padic.instCharZero`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)], CharZero ℚ_[p
]
· 使用引理 `Padic.valuation_one`：valuation_one : valuation (1 : Rat_[p]) = 0
· 使用定理 `WithTop.coe_zero`：∀ {α : Type u} [inst : Zero α], ↑0 = 0
-/
theorem AddValuation.map_one : addValuationDef (1 : ℚ_[p]) = 0 := by
  rw [addValuationDef, if_neg one_ne_zero, valuation_one, WithTop.coe_zero]
/-
**Padic.AddValuation.map_mul** 是 Mathlib 中的一个定理，位于命名空间 `Padic.AddValuation`。
形式化陈述：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (x y : ℚ_[p]), (x * y).addValuationDef
 = x.addValuationDef + y.addValuationDef
参数：Nat.Prime p；x y : ℚ_[p]；x * y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `WithTop.top_add`：∀ {α : Type u} [inst : Add α] (x : WithTop α), ⊤ + x = 
⊤
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `WithTop.add_top`：∀ {α : Type u} [inst : Add α] (x : WithTop α), x + ⊤ = 
⊤
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.coe_add`：∀ {α : Type u} [inst : Add α] (a b : α), ↑(a + b) = ↑a 
+ ↑b
· 使用定理 `WithTop.coe_eq_coe`：∀ {α : Type u_1} {a b : α}, ↑a = ↑b ↔ a = b
· 使用引理 `Padic.valuation_mul`：valuation_mul {x y : Rat_[p]} (hx : x != 0) (hy : y
 != 0) : (x * y).valuation = x.valuation + y.valuation
-/
theorem AddValuation.map_mul (x y : ℚ_[p]) :
    addValuationDef (x * y : ℚ_[p]) = addValuationDef x + addValuationDef y := by
  simp only [addValuationDef]
  by_cases hx : x = 0
  · rw [hx, if_pos rfl, zero_mul, if_pos rfl, WithTop.top_add]
  · by_cases hy : y = 0
    · rw [hy, if_pos rfl, mul_zero, if_pos rfl, WithTop.add_top]
    · rw [if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy), ← WithTop.coe_add, WithTop.coe_eq_coe,
        valuation_mul hx hy]
/-
**Padic.AddValuation.map_add** 是 Mathlib 中的一个定理，位于命名空间 `Padic.AddValuation`。
形式化陈述：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (x y : ℚ_[p]), min x.addValuationDef y
.addValuationDef ≤ (x + y).addValuationDef
参数：Nat.Prime p；x y : ℚ_[p]；x + y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用引理 `min_eq_right`：min_eq_right (h : b <= a) : min a b = b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.coe_min`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), ↑(mi
n a b) = min ↑a ↑b
· 使用定理 `WithTop.coe_le_coe`：∀ {α : Type u_1} {a b : α} [inst : LE α], ↑b ≤ ↑a ↔ 
b ≤ a
· 使用定理 `Padic.le_valuation_add`：le_valuation_add {x y : Rat_[p]} (hxy : x + y !=
 0) : min x.valuation y.valuation <= (x + y).valuation
-/
theorem AddValuation.map_add (x y : ℚ_[p]) :
    min (addValuationDef x) (addValuationDef y) ≤ addValuationDef (x + y : ℚ_[p]) := by
  simp only [addValuationDef]
  by_cases hxy : x + y = 0
  · rw [hxy, if_pos rfl]
    exact le_top
  · by_cases hx : x = 0
    · rw [hx, if_pos rfl, min_eq_right, zero_add]
      exact le_top
    · by_cases hy : y = 0
      · rw [hy, if_pos rfl, min_eq_left, add_zero]
        exact le_top
      · rw [if_neg hx, if_neg hy, if_neg hxy, ← WithTop.coe_min, WithTop.coe_le_coe]
        exact le_valuation_add hxy

open WithZero

open scoped Classical in
/-- The `p`-adic valuation on `ℚ_[p]`, as a `Valuation`, bundled `Padic.valuation`. -/
@[simps]
/-
**Padic.mulValuation** 是 Mathlib 中的一个定义，位于命名空间 `Padic`。
形式化陈述：mulValuation : Valuation Rat_[p] Intᵐ⁰ where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `p`-adic valuation on `ℚ_[p]`, as a `Valuation`, bundled `Padic.valuation`.
-/
noncomputable def mulValuation : Valuation ℚ_[p] ℤᵐ⁰ where
  toFun x := if x = 0 then 0 else exp (-x.valuation)
  map_zero' := by simp
  map_one' := by simp
  map_mul' _ _ := by split_ifs <;> simp_all [add_comm]
  map_add_le_max' _ _ := by
    split_ifs
    any_goals simp_all [inv_le_inv₀]
    simpa using le_valuation_add ‹_›
/-
**Padic.comap_mulValuation_eq_padicValuation** 是 Mathlib 中的一个引理，位于命名空间 `Padic`。
形式化陈述：comap_mulValuation_eq_padicValuation : (mulValuation (p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.ext`：ext {v₁ v₂ : Valuation R Γ₀} (h : forall r, v₁ r = v₂ r) 
: v₁ = v₂
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `Padic.instCharZero`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)], CharZero ℚ_[p
]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_ratCast`：∀ {F : Type u_1} {α : Type u_3} [inst : DivisionRing α] [ins
t_1 : FunLike F ℚ α] [RingHomClass F ℚ α] (f : F) (q : ℚ),   f q = ↑q
· 使用定理 `Padic.mulValuation_toFun`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (x : ℚ_[p]
), Padic.mulValuation x = if x = 0 then 0 else WithZero.exp (-x.valuation)
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用引理 `Padic.valuation_ratCast`：valuation_ratCast (q : Rat) : valuation (q : Ra
t_[p]) = padicValRat p q
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comap_mulValuation_eq_padicValuation :
    (mulValuation (p := p)).comap (Rat.castHom _) = Rat.padicValuation p := by
  ext
  simp [Rat.padicValuation]
/-
**Padic.comap_mulValuation_eq_int_padicValuation** 是 Mathlib 中的一个引理，位于命名空间 `Padi
c`。
形式化陈述：comap_mulValuation_eq_int_padicValuation : (mulValuation (p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.ext`：ext {v₁ v₂ : Valuation R Γ₀} (h : forall r, v₁ r = v₂ r) 
: v₁ = v₂
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `Padic.mulValuation_toFun`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (x : ℚ_[p]
), Padic.mulValuation x = if x = 0 then 0 else WithZero.exp (-x.valuation)
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `Padic.instCharZero`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)], CharZero ℚ_[p
]
· 使用引理 `Padic.valuation_intCast`：valuation_intCast (n : Int) : valuation (n : Ra
t_[p]) = padicValInt p n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_intCast`：map_intCast [FunLike F α β] [RingHomClass F α β] (f : F) (n
 : Int) : f n = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comap_mulValuation_eq_int_padicValuation :
    (mulValuation (p := p)).comap (Int.castRingHom _) = Int.padicValuation p := by
  ext
  simp [← Rat.padicValuation_cast, ← comap_mulValuation_eq_padicValuation]
/-
**Padic.norm_eq_zpow_log_mulValuation** 是 Mathlib 中的一个引理，位于命名空间 `Padic`。
形式化陈述：norm_eq_zpow_log_mulValuation {x : Rat_[p]} (hx : x != 0) : ‖x‖ = (p : Rea
l) ^ (log (mulValuation x))
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Padic.norm_eq_zpow_neg_valuation`：norm_eq_zpow_neg_valuation {x : Rat_[p
]} : x != 0 -> ‖x‖ = (p : Real) ^ (-x.valuation)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `Padic.mulValuation_toFun`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (x : ℚ_[p]
), Padic.mulValuation x = if x = 0 then 0 else WithZero.exp (-x.valuation)
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `WithZero.log_inv`：∀ {G : Type u_5} [inst : AddGroup G] (x : WithZero (Mu
ltiplicative G)), x⁻¹.log = -x.log
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma norm_eq_zpow_log_mulValuation {x : ℚ_[p]} (hx : x ≠ 0) :
    ‖x‖ = (p : ℝ) ^ (log (mulValuation x)) := by
  simp [norm_eq_zpow_neg_valuation, hx]

/-- The additive `p`-adic valuation on `ℚ_[p]`, as an `addValuation`. -/
/-
**Padic.addValuation** 是 Mathlib 中的一个定义，位于命名空间 `Padic`。
形式化陈述：addValuation : AddValuation Rat_[p] (WithTop Int)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Padic.AddValuation.map_zero`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], Padic.
addValuationDef 0 = ⊤
· 使用定理 `Padic.AddValuation.map_one`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], Padic.a
ddValuationDef 1 = 0
· 使用定理 `Padic.AddValuation.map_add`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (x y : ℚ
_[p]), min x.addValuationDef y.addValuationDef ≤ (x + y).addValuationDef
· 使用定理 `Padic.AddValuation.map_mul`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (x y : ℚ
_[p]), (x * y).addValuationDef = x.addValuationDef + y.addValuationDef

--- 原说明 ---
The additive `p`-adic valuation on `ℚ_[p]`, as an `addValuation`.
-/
def addValuation : AddValuation ℚ_[p] (WithTop ℤ) :=
  AddValuation.of addValuationDef AddValuation.map_zero AddValuation.map_one AddValuation.map_add
    AddValuation.map_mul

@[simp]
/-
**Padic.addValuation.apply** 是 Mathlib 中的一个定理，位于命名空间 `Padic.addValuation`。
形式化陈述：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] {x : ℚ_[p]}, x ≠ 0 → Padic.addValuatio
n x = ↑x.valuation
参数：Nat.Prime p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem addValuation.apply {x : ℚ_[p]} (hx : x ≠ 0) :
    Padic.addValuation x = (x.valuation : WithTop ℤ) := by
  simp only [Padic.addValuation, AddValuation.of_apply, addValuationDef, if_neg hx]

section NormLEIff

/-! ### Various characterizations of open unit balls -/


/-
**Padic.norm_le_pow_iff_norm_lt_pow_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：norm_le_pow_iff_norm_lt_pow_add_one (x : Rat_[p]) (n : Int) : ‖x‖ <= (p : 
Real) ^ n ↔ ‖x‖ < (p : Real) ^ (n + 1)
参数：x : Rat_[p]；n : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zpow_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialO
rder G₀] [PosMulReflectLT G₀] {a : G₀}   [ZeroLEOneClass G₀], 0 < a → ∀ (n : ℤ…
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Padic.norm_eq_zpow_neg_valuation`：norm_eq_zpow_neg_valuation {x : Rat_[p
]} : x != 0 -> ‖x‖ = (p : Real) ^ (-x.valuation)
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用引理 `zpow_right_strictMono₀`：zpow_right_strictMono₀ (ha : 1 < a) : StrictMono
 fun n : Int => a ^ n
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用定理 `Int.lt_add_one_iff`：∀ {a b : ℤ}, a < b + 1 ↔ a ≤ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
### Various characterizations of open unit balls
-/
theorem norm_le_pow_iff_norm_lt_pow_add_one (x : ℚ_[p]) (n : ℤ) :
    ‖x‖ ≤ (p : ℝ) ^ n ↔ ‖x‖ < (p : ℝ) ^ (n + 1) := by
  have aux (n : ℤ) : 0 < ((p : ℝ) ^ n) := zpow_pos (mod_cast hp.1.pos) _
  by_cases hx0 : x = 0
  · simp [hx0, norm_zero, aux, le_of_lt (aux _)]
  rw [norm_eq_zpow_neg_valuation hx0]
  have h1p : 1 < (p : ℝ) := mod_cast hp.1.one_lt
  have H := zpow_right_strictMono₀ h1p
  rw [H.le_iff_le, H.lt_iff_lt, Int.lt_add_one_iff]
/-
**Padic.norm_lt_pow_iff_norm_le_pow_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：norm_lt_pow_iff_norm_le_pow_sub_one (x : Rat_[p]) (n : Int) : ‖x‖ < (p : R
eal) ^ n ↔ ‖x‖ <= (p : Real) ^ (n - 1)
参数：x : Rat_[p]；n : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Padic.norm_le_pow_iff_norm_lt_pow_add_one`：norm_le_pow_iff_norm_lt_pow_a
dd_one (x : Rat_[p]) (n : Int) : ‖x‖ <= (p : Real) ^ n ↔ ‖x‖ < (p : Real) ^ (n +
 1)
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem norm_lt_pow_iff_norm_le_pow_sub_one (x : ℚ_[p]) (n : ℤ) :
    ‖x‖ < (p : ℝ) ^ n ↔ ‖x‖ ≤ (p : ℝ) ^ (n - 1) := by
  rw [norm_le_pow_iff_norm_lt_pow_add_one, sub_add_cancel]
/-
**Padic.norm_le_one_iff_val_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：norm_le_one_iff_val_nonneg (x : Rat_[p]) : ‖x‖ <= 1 ↔ 0 <= x.valuation
参数：x : Rat_[p]。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Padic.valuation_zero`：valuation_zero : valuation (0 : Rat_[p]) = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Padic.norm_eq_zpow_neg_valuation`：norm_eq_zpow_neg_valuation {x : Rat_[p
]} : x != 0 -> ‖x‖ = (p : Real) ^ (-x.valuation)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_zero`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a : G), a ^ 0 = 1
· 使用定理 `zpow_le_zpow_iff_right₀`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [in
st_1 : PartialOrder G₀] [PosMulReflectLT G₀] {a : G₀} [ZeroLEOneClass G₀]   {m n
 : ℤ}, 1 < a …
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_lt_cast`：one_lt_cast : 1 < (n : α) ↔ 1 < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `neg_nonpos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, -a ≤ 0 ↔ 0 ≤ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem norm_le_one_iff_val_nonneg (x : ℚ_[p]) : ‖x‖ ≤ 1 ↔ 0 ≤ x.valuation := by
  by_cases hx : x = 0
  · simp only [hx, norm_zero, valuation_zero, zero_le_one, le_refl]
  · rw [norm_eq_zpow_neg_valuation hx, ← zpow_zero (p : ℝ), zpow_le_zpow_iff_right₀, neg_nonpos]
    exact Nat.one_lt_cast.2 (Nat.Prime.one_lt' p).1

end NormLEIff

end Padic

