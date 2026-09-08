/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.Order.AbsoluteValue.Euclidean
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Absolute value on polynomials over a finite field.

Let `𝔽_q` be a finite field of cardinality `q`, then the map sending a polynomial `p`
to `q ^ degree p` (where `q ^ degree 0 = 0`) is an absolute value.

## Main definitions

* `Polynomial.cardPowDegree` is an absolute value on `𝔽_q[t]`, the ring of
  polynomials over a finite field of cardinality `q`, mapping a polynomial `p`
  to `q ^ degree p` (where `q ^ degree 0 = 0`)

## Main results
* `Polynomial.cardPowDegree_isEuclidean`: `cardPowDegree` respects the
  Euclidean domain structure on the ring of polynomials

-/

@[expose] public section


namespace Polynomial

variable {Fq : Type*} [Field Fq] [Fintype Fq]

open AbsoluteValue

open Polynomial

/-- `cardPowDegree` is the absolute value on `𝔽_q[t]` sending `f` to `q ^ degree f`.

`cardPowDegree 0` is defined to be `0`. -/
/-
**Polynomial.cardPowDegree** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：cardPowDegree : AbsoluteValue Fq[X] Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`cardPowDegree` is the absolute value on `𝔽_q[t]` sending `f` to `q ^ degree f`.

`cardPowDegree 0` is defined to be `0`.
-/
noncomputable def cardPowDegree : AbsoluteValue Fq[X] ℤ :=
  have card_pos : 0 < Fintype.card Fq := Fintype.card_pos_iff.mpr inferInstance
  have pow_pos : ∀ n, 0 < (Fintype.card Fq : ℤ) ^ n := fun n =>
    pow_pos (Int.natCast_pos.mpr card_pos) n
  letI := Classical.decEq Fq
  { toFun := fun p => if p = 0 then 0 else (Fintype.card Fq : ℤ) ^ p.natDegree
    nonneg' := fun p => by
      split_ifs
      · rfl
      exact pow_nonneg (Int.natCast_nonneg _) _
    eq_zero' := fun p =>
      ite_eq_left_iff.trans
        ⟨fun h => by
          contrapose! h
          exact ⟨h, (pow_pos _).ne'⟩, absurd⟩
    add_le' := fun p q => by
      by_cases hp : p = 0; · simp [hp]
      by_cases hq : q = 0; · simp [hq]
      by_cases hpq : p + q = 0
      · simp only [hpq, hp, hq, if_true, if_false]
        exact add_nonneg (pow_pos _).le (pow_pos _).le
      simp only [hpq, hp, hq, if_false]
      exact le_trans (pow_right_mono₀ (by lia) (Polynomial.natDegree_add_le _ _)) (by grind)
    map_mul' := fun p q => by
      by_cases hp : p = 0; · simp [hp]
      by_cases hq : q = 0; · simp [hq]
      have hpq : p * q ≠ 0 := mul_ne_zero hp hq
      simp only [hpq, hp, hq, if_false, Polynomial.natDegree_mul hp hq, pow_add] }
/-
**Polynomial.cardPowDegree_apply** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：cardPowDegree_apply [DecidableEq Fq] (p : Fq[X]) : cardPowDegree p = if p 
= 0 then 0 else (Fintype.card Fq : Int) ^ natDegree p
参数：p : Fq[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem cardPowDegree_apply [DecidableEq Fq] (p : Fq[X]) :
    cardPowDegree p = if p = 0 then 0 else (Fintype.card Fq : ℤ) ^ natDegree p := by
  simp [cardPowDegree]

@[simp]
/-
**Polynomial.cardPowDegree_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：cardPowDegree_zero : cardPowDegree (0 : Fq[X]) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cardPowDegree_zero : cardPowDegree (0 : Fq[X]) = 0 := rfl

@[simp]
/-
**Polynomial.cardPowDegree_nonzero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：cardPowDegree_nonzero (p : Fq[X]) (hp : p != 0) : cardPowDegree p = (Finty
pe.card Fq : Int) ^ p.natDegree
参数：p : Fq[X]；hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem cardPowDegree_nonzero (p : Fq[X]) (hp : p ≠ 0) :
    cardPowDegree p = (Fintype.card Fq : ℤ) ^ p.natDegree :=
  if_neg hp
/-
**Polynomial.cardPowDegree_isEuclidean** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：cardPowDegree_isEuclidean : IsEuclidean (cardPowDegree : AbsoluteValue Fq[
X] Int)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fintype.card_pos_iff`：card_pos_iff : 0 < card α ↔ Nonempty α
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Int.natCast_pos`：∀ {n : ℕ}, 0 < ↑n ↔ 0 < n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.cardPowDegree_apply`：cardPowDegree_apply [DecidableEq Fq] (p 
: Fq[X]) : cardPowDegree p = if p = 0 then 0 else (Fintype.card Fq : Int) ^ natD
egree p
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `pow_lt_pow_iff_right₀`：pow_lt_pow_iff_right₀ (h : 1 < a) : a ^ n < a ^ m
 ↔ n < m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Fintype.one_lt_card`：one_lt_card [h : Nontrivial α] : 1 < Fintype.card α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem cardPowDegree_isEuclidean : IsEuclidean (cardPowDegree : AbsoluteValue Fq[X] ℤ) :=
  have card_pos : 0 < Fintype.card Fq := Fintype.card_pos_iff.mpr inferInstance
  have pow_pos : ∀ n, 0 < (Fintype.card Fq : ℤ) ^ n := fun n =>
    pow_pos (Int.natCast_pos.mpr card_pos) n
  { map_lt_map_iff' := fun {p q} => by
      classical
      change cardPowDegree p < cardPowDegree q ↔ degree p < degree q
      simp only [cardPowDegree_apply]
      split_ifs with hp hq hq
      · simp only [hp, hq, lt_self_iff_false]
      · simp only [hp, hq, degree_zero, Ne, bot_lt_iff_ne_bot, degree_eq_bot, pow_pos,
          not_false_iff]
      · simp only [hq, degree_zero, not_lt_bot, (pow_pos _).not_gt]
      · rw [degree_eq_natDegree hp, degree_eq_natDegree hq, Nat.cast_lt, pow_lt_pow_iff_right₀]
        exact mod_cast @Fintype.one_lt_card Fq _ _ }

end Polynomial

