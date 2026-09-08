/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Matthew Robert Ballard
-/
module

public import Mathlib.Data.Nat.MaxPowDiv
public import Mathlib.RingTheory.Multiplicity
public import Mathlib.Data.Nat.Factors

/-!
# `p`-adic Valuation

This file defines the `p`-adic valuation on `ℕ`, `ℤ`, and `ℚ`.

The `p`-adic valuation on `ℚ` is the difference of the multiplicities of `p` in the numerator and
denominator of `q`. This function obeys the standard properties of a valuation, with the appropriate
assumptions on `p`. The `p`-adic valuations on `ℕ` and `ℤ` agree with that on `ℚ`.

The valuation induces a norm on `ℚ`. This norm is defined in
`Mathlib/NumberTheory/Padics/PadicNorm.lean`.
-/

@[expose] public section

assert_not_exists Field

universe u

open Nat

variable {p : ℕ}

/-
**padicValNat_eq_emultiplicity_of_ne_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：padicValNat_eq_emultiplicity_of_ne_one (hp : p != 1) {n : Nat} (hn : n != 
0) : padicValNat p n = emultiplicity p n
参数：hp : p != 1；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `emultiplicity_eq_coe`：emultiplicity_eq_coe {n : Nat} : emultiplicity a b
 = n ↔ a ^ n ∣ b ∧ ¬a ^ (n + 1) ∣ b
· 使用定理 `Nat.pow_dvd_iff_le_padicValNat`：pow_dvd_iff_le_padicValNat {p k n : Nat}
 (hp : p != 1) (hn : n != 0) : p ^ k ∣ n ↔ k <= padicValNat p n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem padicValNat_eq_emultiplicity_of_ne_one (hp : p ≠ 1) {n : ℕ} (hn : n ≠ 0) :
    padicValNat p n = emultiplicity p n := by
  rw [eq_comm, emultiplicity_eq_coe, pow_dvd_iff_le_padicValNat hp hn,
    pow_dvd_iff_le_padicValNat hp hn]
  simp

@[simp]
/-
**Nat.toNat_emultiplicity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.toNat_emultiplicity (p n : Nat) : (emultiplicity p n).toNat = padicVal
Nat p n
参数：p n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `emultiplicity_one_left`：emultiplicity_one_left (b : α) : emultiplicity 1
 b = ⊤
· 使用定理 `padicValNat_one_left`：∀ (n : ℕ), padicValNat 1 n = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `emultiplicity_zero`：emultiplicity_zero (a : α) : emultiplicity a 0 = ⊤
· 使用定理 `padicValNat_zero_right`：∀ (p : ℕ), padicValNat p 0 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem Nat.toNat_emultiplicity (p n : ℕ) : (emultiplicity p n).toNat = padicValNat p n := by
  rcases eq_or_ne p 1 with rfl | hp
  · simp
  · rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [← padicValNat_eq_emultiplicity_of_ne_one, *]
/-
**padicValNat_def'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：padicValNat_def' {n : Nat} (hp : p != 1) (hn : n != 0) : padicValNat p n =
 multiplicity p n
参数：hp : p != 1；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `multiplicity_eq_of_emultiplicity_eq_some`：multiplicity_eq_of_emultiplici
ty_eq_some {n : Nat} (h : emultiplicity a b = n) : multiplicity a b = n
· 使用定理 `padicValNat_eq_emultiplicity_of_ne_one`：padicValNat_eq_emultiplicity_of_
ne_one (hp : p != 1) {n : Nat} (hn : n != 0) : padicValNat p n = emultiplicity p
 n
-/
theorem padicValNat_def' {n : ℕ} (hp : p ≠ 1) (hn : n ≠ 0) :
    padicValNat p n = multiplicity p n :=
  .symm <| multiplicity_eq_of_emultiplicity_eq_some <| .symm <|
    padicValNat_eq_emultiplicity_of_ne_one hp hn

/-- A simplification of `padicValNat` when one input is prime, by analogy with
`padicValRat_def`. -/
/-
**padicValNat_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：padicValNat_def [hp : Fact p.Prime] {n : Nat} (hn : n != 0) : padicValNat 
p n = multiplicity p n
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `padicValNat_def'`：padicValNat_def' {n : Nat} (hp : p != 1) (hn : n != 0)
 : padicValNat p n = multiplicity p n
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p

--- 原说明 ---
A simplification of `padicValNat` when one input is prime, by analogy with
`padicValRat_def`.
-/
theorem padicValNat_def [hp : Fact p.Prime] {n : ℕ} (hn : n ≠ 0) :
    padicValNat p n = multiplicity p n :=
  padicValNat_def' hp.out.ne_one hn

/-- A simplification of `padicValNat` when one input is prime, by analogy with
`padicValRat_def`. -/
/-
**padicValNat_eq_emultiplicity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：padicValNat_eq_emultiplicity [hp : Fact p.Prime] {n : Nat} (hn : n != 0) :
 padicValNat p n = emultiplicity p n
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `padicValNat_eq_emultiplicity_of_ne_one`：padicValNat_eq_emultiplicity_of_
ne_one (hp : p != 1) {n : Nat} (hn : n != 0) : padicValNat p n = emultiplicity p
 n
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p

--- 原说明 ---
A simplification of `padicValNat` when one input is prime, by analogy with
`padicValRat_def`.
-/
theorem padicValNat_eq_emultiplicity [hp : Fact p.Prime] {n : ℕ} (hn : n ≠ 0) :
    padicValNat p n = emultiplicity p n :=
  padicValNat_eq_emultiplicity_of_ne_one hp.out.ne_one hn

namespace padicValNat

@[deprecated (since := "2026-03-15")]
alias maxPowDiv_eq_emultiplicity := padicValNat_eq_emultiplicity

@[deprecated (since := "2026-03-15")]
alias maxPowDiv_eq_multiplicity := padicValNat_def'

@[deprecated padicValNat_zero_right (since := "2026-03-15")]
/-
**padicValNat.zero** 是 Mathlib 中的一个定理，位于命名空间 `padicValNat`。
形式化陈述：∀ {p : ℕ}, padicValNat p 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `padicValNat_zero_right`：∀ (p : ℕ), padicValNat p 0 = 0
-/
protected theorem zero : padicValNat p 0 = 0 := padicValNat_zero_right p

@[deprecated padicValNat_one_right (since := "2026-03-15")]
/-
**padicValNat.one** 是 Mathlib 中的一个定理，位于命名空间 `padicValNat`。
形式化陈述：∀ {p : ℕ}, padicValNat p 1 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `padicValNat_one_right`：∀ (p : ℕ), padicValNat p 1 = 0
-/
protected theorem one : padicValNat p 1 = 0 := padicValNat_one_right p

@[simp]
/-
**padicValNat.eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `padicValNat`。
形式化陈述：eq_zero_iff {n : Nat} : padicValNat p n = 0 ↔ p = 1 ∨ n = 0 ∨ ¬p ∣ n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `padicValNat_zero_right`：∀ (p : ℕ), padicValNat p 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `padicValNat_one_left`：∀ (n : ℕ), padicValNat 1 n = 0
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Nat.pow_dvd_iff_le_padicValNat`：pow_dvd_iff_le_padicValNat {p k n : Nat}
 (hp : p != 1) (hn : n != 0) : p ^ k ∣ n ↔ k <= padicValNat p n
-/
theorem eq_zero_iff {n : ℕ} : padicValNat p n = 0 ↔ p = 1 ∨ n = 0 ∨ ¬p ∣ n := by
  rcases eq_or_ne n 0 with rfl | hn₀; · simp
  rcases eq_or_ne p 1 with rfl | hp₁; · simp
  simpa [*] using pow_dvd_iff_le_padicValNat (k := 1) hp₁ hn₀ |>.symm |>.not

end padicValNat

open List

/-
**le_emultiplicity_iff_replicate_subperm_primeFactorsList** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：le_emultiplicity_iff_replicate_subperm_primeFactorsList {a b : Nat} {n : N
at} (ha : a.Prime) (hb : b != 0) : ↑n <= emultiplicity a b ↔ replicate n a <+~ b
.primeFactorsList
参数：ha : a.Prime；hb : b != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Nat.replicate_subperm_primeFactorsList_iff`：replicate_subperm_primeFacto
rsList_iff {a b n : Nat} (ha : Prime a) (hb : b != 0) : replicate n a <+~ primeF
actorsList b ↔ a ^ n ∣ b
· 使用定理 `pow_dvd_iff_le_emultiplicity`：pow_dvd_iff_le_emultiplicity {k : Nat} : a
 ^ k ∣ b ↔ k <= emultiplicity a b
-/
theorem le_emultiplicity_iff_replicate_subperm_primeFactorsList {a b : ℕ} {n : ℕ} (ha : a.Prime)
    (hb : b ≠ 0) :
    ↑n ≤ emultiplicity a b ↔ replicate n a <+~ b.primeFactorsList :=
  (replicate_subperm_primeFactorsList_iff ha hb).trans
    pow_dvd_iff_le_emultiplicity |>.symm
/-
**le_padicValNat_iff_replicate_subperm_primeFactorsList** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：le_padicValNat_iff_replicate_subperm_primeFactorsList {a b : Nat} {n : Nat
} (ha : a.Prime) (hb : b != 0) : n <= padicValNat a b ↔ replicate n a <+~ b.prim
eFactorsList
参数：ha : a.Prime；hb : b != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_emultiplicity_iff_replicate_subperm_primeFactorsList`：le_emultiplicit
y_iff_replicate_subperm_primeFactorsList {a b : Nat} {n : Nat} (ha : a.Prime) (h
b : b != 0) : ↑n <= emultiplicity a b ↔ repli…
· 使用定理 `FiniteMultiplicity.emultiplicity_eq_multiplicity`：FiniteMultiplicity.emu
ltiplicity_eq_multiplicity (h : FiniteMultiplicity a b) : emultiplicity a b = mu
ltiplicity a b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.finiteMultiplicity_iff`：Nat.finiteMultiplicity_iff {a b : Nat} : Fin
iteMultiplicity a b ↔ a != 1 ∧ 0 < b
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `padicValNat_def'`：padicValNat_def' {n : Nat} (hp : p != 1) (hn : n != 0)
 : padicValNat p n = multiplicity p n
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_padicValNat_iff_replicate_subperm_primeFactorsList {a b : ℕ} {n : ℕ} (ha : a.Prime)
    (hb : b ≠ 0) :
    n ≤ padicValNat a b ↔ replicate n a <+~ b.primeFactorsList := by
  rw [← le_emultiplicity_iff_replicate_subperm_primeFactorsList ha hb,
    Nat.finiteMultiplicity_iff.2 ⟨ha.ne_one, Nat.pos_of_ne_zero hb⟩
      |>.emultiplicity_eq_multiplicity, ← padicValNat_def' ha.ne_one hb,
    Nat.cast_le]
