/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.RingTheory.Multiplicity
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Order

/-! # Formal power series (in one variable) - Order

The `PowerSeries.order` of a formal power series `φ` is the multiplicity of the variable `X` in `φ`.

If the coefficients form an integral domain, then `PowerSeries.order` is an
additive valuation (`PowerSeries.order_mul`, `PowerSeries.min_order_le_order_add`).

We prove that if the commutative ring `R` of coefficients is an integral domain,
then the ring `R⟦X⟧` of formal power series in one variable over `R`
is an integral domain.

Given a non-zero power series `f`, `divided_by_X_pow_order f` is the power series obtained by
dividing out the largest power of X that divides `f`, that is its order. This is useful when
proving that `R⟦X⟧` is a normalization monoid, which is done in `PowerSeries.Inverse`.

-/

@[expose] public section
noncomputable section

open Polynomial

open Finset (antidiagonal mem_antidiagonal)

namespace PowerSeries

open Finsupp (single)

variable {R : Type*}

section OrderBasic

variable [Semiring R] {φ : R⟦X⟧}

/-
**PowerSeries.exists_coeff_ne_zero_iff_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `PowerS
eries`。
形式化陈述：exists_coeff_ne_zero_iff_ne_zero : (exists n : Nat, coeff n φ != 0) ↔ φ !=
 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₃`：contrapose_iff₃ {p q : Prop} 
: (¬ p ↔ q) -> (p ↔ ¬ q)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem exists_coeff_ne_zero_iff_ne_zero : (∃ n : ℕ, coeff n φ ≠ 0) ↔ φ ≠ 0 := by
  contrapose!
  simp

/-- The order of a formal power series `φ` is the greatest `n : ℕ∞`
such that `X^n` divides `φ`. The order is `⊤` if and only if `φ = 0`. -/
/-
**PowerSeries.order** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：order (φ : R⟦X⟧) : Nat∞
参数：φ : R⟦X⟧。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The order of a formal power series `φ` is the greatest `n : ℕ∞`
such that `X^n` divides `φ`. The order is `⊤` if and only if `φ = 0`.
-/
def order (φ : R⟦X⟧) : ℕ∞ :=
  letI := Classical.decEq R
  letI := Classical.decEq R⟦X⟧
  if h : φ = 0 then ⊤ else Nat.find (exists_coeff_ne_zero_iff_ne_zero.mpr h)

/-- The order of the `0` power series is infinite. -/
@[simp]
/-
**PowerSeries.order_zero** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：order_zero : order (0 : R⟦X⟧) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc

--- 原说明 ---
The order of the `0` power series is infinite.
-/
theorem order_zero : order (0 : R⟦X⟧) = ⊤ :=
  dif_pos rfl
/-
**PowerSeries.order_finite_iff_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：order_finite_iff_ne_zero : (order φ < ⊤) ↔ φ != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
-/
theorem order_finite_iff_ne_zero : (order φ < ⊤) ↔ φ ≠ 0 := by
  simp only [order]
  split_ifs with h <;> simpa

/-- The `0` power series is the unique power series with infinite order. -/
@[simp]
/-
**PowerSeries.order_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：order_eq_top {φ : R⟦X⟧} : φ.order = ⊤ ↔ φ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.not_left`：Iff.not_left (h : a ↔ ¬b) : ¬a ↔ b
· 使用定理 `PowerSeries.order_finite_iff_ne_zero`：order_finite_iff_ne_zero : (order 
φ < ⊤) ↔ φ != 0

--- 原说明 ---
The `0` power series is the unique power series with infinite order.
-/
theorem order_eq_top {φ : R⟦X⟧} : φ.order = ⊤ ↔ φ = 0 := by
  simpa using order_finite_iff_ne_zero.not_left
/-
**PowerSeries.coe_toNat_order** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coe_toNat_order {φ : R⟦X⟧} (hf : φ != 0) : φ.order.toNat = φ.order
参数：hf : φ != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENat.natCast_toNat_eq_self`：natCast_toNat_eq_self : ENat.toNat n = n ↔ n
 != ⊤
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `PowerSeries.order_eq_top`：order_eq_top {φ : R⟦X⟧} : φ.order = ⊤ ↔ φ = 0
-/
theorem coe_toNat_order {φ : R⟦X⟧} (hf : φ ≠ 0) : φ.order.toNat = φ.order := by
  rw [ENat.natCast_toNat_eq_self.mpr (order_eq_top.not.mpr hf)]

/-- If the order of a formal power series is finite,
then the coefficient indexed by the order is nonzero. -/
/-
**PowerSeries.coeff_order** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_order (h : φ != 0) : coeff φ.order.toNat φ != 0
参数：h : φ != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)

--- 原说明 ---
If the order of a formal power series is finite,
then the coefficient indexed by the order is nonzero.
-/
theorem coeff_order (h : φ ≠ 0) : coeff φ.order.toNat φ ≠ 0 := by
  classical
  simp only [order, h, not_false_iff, dif_neg]
  generalize_proofs h
  exact Nat.find_spec h

/-- If the `n`th coefficient of a formal power series is nonzero,
then the order of the power series is less than or equal to `n`. -/
/-
**PowerSeries.order_le** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：order_le (n : Nat) (h : coeff n φ != 0) : order φ <= n
参数：n : Nat；h : coeff n φ != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.order.eq_1`：∀ {R : Type u_1} [inst : Semiring R] (φ : PowerS
eries R), φ.order = if h : φ = 0 then ⊤ else ↑(Nat.find ⋯)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PowerSeries.exists_coeff_ne_zero_iff_ne_zero`：exists_coeff_ne_zero_iff_n
e_zero : (exists n : Nat, coeff n φ != 0) ↔ φ != 0
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
If the `n`th coefficient of a formal power series is nonzero,
then the order of the power series is less than or equal to `n`.
-/
theorem order_le (n : ℕ) (h : coeff n φ ≠ 0) : order φ ≤ n := by
  rw [order, dif_neg]
  · simpa using ⟨n, le_rfl, h⟩
  · exact exists_coeff_ne_zero_iff_ne_zero.mp ⟨n, h⟩

/-- The `n`th coefficient of a formal power series is `0` if `n` is strictly
smaller than the order of the power series. -/
/-
**PowerSeries.coeff_of_lt_order** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_of_lt_order (n : Nat) (h : ↑n < order φ) : coeff n φ = 0
参数：n : Nat；h : ↑n < order φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `PowerSeries.order_le`：order_le (n : Nat) (h : coeff n φ != 0) : order φ 
<= n

--- 原说明 ---
The `n`th coefficient of a formal power series is `0` if `n` is strictly
smaller than the order of the power series.
-/
theorem coeff_of_lt_order (n : ℕ) (h : ↑n < order φ) : coeff n φ = 0 := by
  contrapose! h
  exact order_le _ h
/-
**PowerSeries.coeff_of_lt_order_toNat** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_of_lt_order_toNat (n : Nat) (h : n < φ.order.toNat) : coeff n φ = 0
参数：n : Nat；h : n < φ.order.toNat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `PowerSeries.coeff_of_lt_order`：coeff_of_lt_order (n : Nat) (h : ↑n < ord
er φ) : coeff n φ = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerSeries.coe_toNat_order`：coe_toNat_order {φ : R⟦X⟧} (hf : φ != 0) : 
φ.order.toNat = φ.order
· 使用引理 `ENat.natCast_lt_natCast`：natCast_lt_natCast {n m : Nat} : (n : Nat∞) < (
m : Nat∞) ↔ n < m
-/
theorem coeff_of_lt_order_toNat (n : ℕ) (h : n < φ.order.toNat) : coeff n φ = 0 := by
  by_cases h' : φ = 0
  · simp [h']
  · refine coeff_of_lt_order _ ?_
    rwa [← coe_toNat_order h', ENat.natCast_lt_natCast]

/-- The order of a formal power series is at least `n` if
the `i`th coefficient is `0` for all `i < n`. -/
/-
**PowerSeries.nat_le_order** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：nat_le_order (φ : R⟦X⟧) (n : Nat) (h : forall i < n, coeff i φ = 0) : ↑n <
= order φ
参数：φ : R⟦X⟧；n : Nat；h : forall i < n, coeff i φ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
The order of a formal power series is at least `n` if
the `i`th coefficient is `0` for all `i < n`.
-/
theorem nat_le_order (φ : R⟦X⟧) (n : ℕ) (h : ∀ i < n, coeff i φ = 0) : ↑n ≤ order φ := by
  simp only [order]
  split_ifs
  · simp
  · simpa [Nat.le_find_iff]

/-- The order of a formal power series is at least `n` if
the `i`th coefficient is `0` for all `i < n`. -/
/-
**PowerSeries.le_order** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：le_order (φ : R⟦X⟧) (n : Nat∞) (h : forall i : Nat, ↑i < n -> coeff i φ = 
0) : n <= order φ
参数：φ : R⟦X⟧；n : Nat∞；h : forall i : Nat, ↑i < n -> coeff i φ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerSeries.nat_le_order`：nat_le_order (φ : R⟦X⟧) (n : Nat) (h : forall 
i < n, coeff i φ = 0) : ↑n <= order φ
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞

--- 原说明 ---
The order of a formal power series is at least `n` if
the `i`th coefficient is `0` for all `i < n`.
-/
theorem le_order (φ : R⟦X⟧) (n : ℕ∞) (h : ∀ i : ℕ, ↑i < n → coeff i φ = 0) :
    n ≤ order φ := by
  cases n with
  | top => simpa using ext (by simpa using h)
  | coe n =>
    convert! nat_le_order φ n _
    simpa using h

/-- The order of a formal power series is exactly `n` if the `n`th coefficient is nonzero,
and the `i`th coefficient is `0` for all `i < n`. -/
/-
**PowerSeries.order_eq_nat** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：order_eq_nat {φ : R⟦X⟧} {n : Nat} : order φ = n ↔ coeff n φ != 0 ∧ forall 
i, i < n -> coeff i φ = 0
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
· 使用定理 `PowerSeries.order_zero`：order_zero : order (0 : R⟦X⟧) = ⊤
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `instCharZeroENat`：CharZero ℕ∞

--- 原说明 ---
The order of a formal power series is exactly `n` if the `n`th coefficient is no
nzero,
and the `i`th coefficient is `0` for all `i < n`.
-/
theorem order_eq_nat {φ : R⟦X⟧} {n : ℕ} :
    order φ = n ↔ coeff n φ ≠ 0 ∧ ∀ i, i < n → coeff i φ = 0 := by
  rcases eq_or_ne φ 0 with (rfl | hφ)
  · simp
  simp [order, dif_neg hφ, Nat.find_eq_iff]

/-- The order of a formal power series is exactly `n` if the `n`th coefficient is nonzero,
and the `i`th coefficient is `0` for all `i < n`. -/
/-
**PowerSeries.order_eq** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：order_eq {φ : R⟦X⟧} {n : Nat∞} : order φ = n ↔ (forall i : Nat, ↑i = n -> 
coeff i φ != 0) ∧ forall i : Nat, ↑i < n -> coeff i φ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞

--- 原说明 ---
The order of a formal power series is exactly `n` if the `n`th coefficient is no
nzero,
and the `i`th coefficient is `0` for all `i < n`.
-/
theorem order_eq {φ : R⟦X⟧} {n : ℕ∞} :
    order φ = n ↔ (∀ i : ℕ, ↑i = n → coeff i φ ≠ 0) ∧ ∀ i : ℕ, ↑i < n → coeff i φ = 0 := by
  cases n with
  | top => simp
  | coe n => simp [order_eq_nat]
/-
**PowerSeries.order_eq_order** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：order_eq_order {φ : R⟦X⟧} : φ.order = MvPowerSeries.order φ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_le_of_ge`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `MvPowerSeries.le_order`：le_order {n : Nat∞} (h : forall d : σ ->₀ Nat, d
egree d < n -> coeff d f = 0) : n <= f.order
· 使用定理 `PowerSeries.coeff_of_lt_order`：coeff_of_lt_order (n : Nat) (h : ↑n < ord
er φ) : coeff n φ = 0
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `PowerSeries.coeff_def`：coeff_def {s : Unit ->₀ Nat} {n : Nat} (h : s () 
= n) : coeff (R
· 使用定理 `PowerSeries.le_order`：le_order (φ : R⟦X⟧) (n : Nat∞) (h : forall i : Nat
, ↑i < n -> coeff i φ = 0) : n <= order φ
· 使用定理 `MvPowerSeries.coeff_of_lt_order`：coeff_of_lt_order {d : σ ->₀ Nat} (h : 
degree d < f.order) : coeff d f = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.degree_single`：degree_single (a : σ) (r : R) : (Finsupp.single a
 r).degree = r
-/
theorem order_eq_order {φ : R⟦X⟧} : φ.order = MvPowerSeries.order φ := by
  refine eq_of_le_of_ge ?_ ?_
  · refine MvPowerSeries.le_order fun d hd => by
      have : coeff ↑(Finsupp.degree d) φ = 0 := coeff_of_lt_order _ hd
      have eq_aux : d.degree = d () := Finset.sum_eq_single _ (by simp) (by simp)
      exact (PowerSeries.coeff_def rfl (R := R)) ▸ (eq_aux ▸ this)
  · refine le_order φ (MvPowerSeries.order φ) fun i hi => by
      rw [← Finsupp.degree_single () i] at hi
      exact MvPowerSeries.coeff_of_lt_order hi

/-- The order of the sum of two formal power series
is at least the minimum of their orders. -/
/-
**PowerSeries.min_order_le_order_add** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：min_order_le_order_add (φ ψ : R⟦X⟧) : min (order φ) (order ψ) <= order (φ 
+ ψ)
参数：φ ψ : R⟦X⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.le_order`：le_order (φ : R⟦X⟧) (n : Nat∞) (h : forall i : Nat
, ↑i < n -> coeff i φ = 0) : n <= order φ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `PowerSeries.coeff_of_lt_order`：coeff_of_lt_order (n : Nat) (h : ↑n < ord
er φ) : coeff n φ = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
The order of the sum of two formal power series
is at least the minimum of their orders.
-/
theorem min_order_le_order_add (φ ψ : R⟦X⟧) : min (order φ) (order ψ) ≤ order (φ + ψ) := by
  refine le_order _ _ ?_
  simp +contextual [coeff_of_lt_order]
/-
**PowerSeries.order_add_of_order_ne.aux** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem order_add_of_order_ne.aux (φ ψ : R⟦X⟧)
    (H : order φ < order ψ) : order (φ + ψ) ≤ order φ ⊓ order ψ := by
  suffices order (φ + ψ) = order φ by
    rw [le_inf_iff, this]
    exact ⟨le_rfl, le_of_lt H⟩
  rw [order_eq]
  constructor
  · intro i hi
    rw [← hi] at H
    rw [(coeff _).map_add, coeff_of_lt_order i H, add_zero]
    exact (order_eq_nat.1 hi.symm).1
  · intro i hi
    rw [(coeff _).map_add, coeff_of_lt_order i hi, coeff_of_lt_order i (lt_trans hi H),
      zero_add]

/-- The order of the sum of two formal power series
is the minimum of their orders if their orders differ. -/
/-
**PowerSeries.order_add_of_order_ne** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：order_add_of_order_ne (φ ψ : R⟦X⟧) (h : order φ != order ψ) : order (φ + ψ
) = order φ ⊓ order ψ
参数：φ ψ : R⟦X⟧；h : order φ != order ψ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `_private.Mathlib.RingTheory.PowerSeries.Order.0.PowerSeries.order_add_of
_order_ne.aux`：∀ {R : Type u_1} [inst : Semiring R] (φ ψ : PowerSeries R), φ.ord
er < ψ.order → (φ + ψ).order ≤ min φ.order ψ.order
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `PowerSeries.min_order_le_order_add`：min_order_le_order_add (φ ψ : R⟦X⟧) 
: min (order φ) (order ψ) <= order (φ + ψ)

--- 原说明 ---
The order of the sum of two formal power series
is the minimum of their orders if their orders differ.
-/
theorem order_add_of_order_ne (φ ψ : R⟦X⟧) (h : order φ ≠ order ψ) :
    order (φ + ψ) = order φ ⊓ order ψ := by
  refine le_antisymm ?_ (min_order_le_order_add _ _)
  rcases h.lt_or_gt with (φ_lt_ψ | ψ_lt_φ)
  · apply order_add_of_order_ne.aux _ _ φ_lt_ψ
  · simpa only [add_comm, inf_comm] using order_add_of_order_ne.aux _ _ ψ_lt_φ
/-
**PowerSeries.le_order_map** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：le_order_map {S : Type*} [Semiring S] (f : R ->+* S) : φ.order <= (φ.map f
).order
参数：f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.le_order`：le_order (φ : R⟦X⟧) (n : Nat∞) (h : forall i : Nat
, ↑i < n -> coeff i φ = 0) : n <= order φ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_of_lt_order`：coeff_of_lt_order (n : Nat) (h : ↑n < ord
er φ) : coeff n φ = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem le_order_map {S : Type*} [Semiring S] (f : R →+* S) :
    φ.order ≤ (φ.map f).order :=
  le_order _ _ fun i hi => by simp [coeff_of_lt_order i hi]
/-
**PowerSeries.le_order_smul** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：le_order_smul {a : R} : φ.order <= (a • φ).order
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.le_order`：le_order (φ : R⟦X⟧) (n : Nat∞) (h : forall i : Nat
, ↑i < n -> coeff i φ = 0) : n <= order φ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `PowerSeries.coeff_of_lt_order`：coeff_of_lt_order (n : Nat) (h : ↑n < ord
er φ) : coeff n φ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem le_order_smul {a : R} :
    φ.order ≤ (a • φ).order :=
  le_order _ φ.order fun i hi => by simp [coeff_of_lt_order i hi]

/-- The order of the product of two formal power series
is at least the sum of their orders. -/
/-
**PowerSeries.le_order_mul** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：le_order_mul (φ ψ : R⟦X⟧) : order φ + order ψ <= order (φ * ψ)
参数：φ ψ : R⟦X⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.le_order`：le_order (φ : R⟦X⟧) (n : Nat∞) (h : forall i : Nat
, ↑i < n -> coeff i φ = 0) : n <= order φ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_mul`：coeff_mul (n : Nat) (φ ψ : R⟦X⟧) : coeff n (φ * ψ
) = ∑ p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `PowerSeries.coeff_of_lt_order`：coeff_of_lt_order (n : Nat) (h : ↑n < ord
er φ) : coeff n φ = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Finset.HasAntidiagonal.mem_antidiagonal`：∀ {A : Type u_1} {inst : AddMon
oid A} [self : Finset.HasAntidiagonal A] {n : A} {a : A × A},   a ∈ Finset.HasAn
tidiagonal.antidiagonal n ↔ a…

--- 原说明 ---
The order of the product of two formal power series
is at least the sum of their orders.
-/
theorem le_order_mul (φ ψ : R⟦X⟧) : order φ + order ψ ≤ order (φ * ψ) := by
  apply le_order
  intro n hn; rw [coeff_mul, Finset.sum_eq_zero]
  rintro ⟨i, j⟩ hij
  by_cases! hi : ↑i < order φ
  · rw [coeff_of_lt_order i hi, zero_mul]
  by_cases! hj : ↑j < order ψ
  · rw [coeff_of_lt_order j hj, mul_zero]
  rw [mem_antidiagonal] at hij
  exfalso
  apply ne_of_lt (lt_of_lt_of_le hn <| add_le_add hi hj)
  rw [← Nat.cast_add, hij]
/-
**PowerSeries.le_order_pow** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：le_order_pow (φ : R⟦X⟧) (n : Nat) : n • order φ <= order (φ ^ n)
参数：φ : R⟦X⟧；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `PowerSeries.le_order_mul`：le_order_mul (φ ψ : R⟦X⟧) : order φ + order ψ 
<= order (φ * ψ)
-/
theorem le_order_pow (φ : R⟦X⟧) (n : ℕ) : n • order φ ≤ order (φ ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => grw [add_smul, one_smul, pow_succ, ih, le_order_mul]
/-
**PowerSeries.le_order_prod** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：le_order_prod {R : Type*} [CommSemiring R] {ι : Type*} (φ : ι -> R⟦X⟧) (s 
: Finset ι) : ∑ i in s, (φ i).order <= (∏ i in s, φ i).order
参数：φ : ι -> R⟦X⟧；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `PowerSeries.le_order_mul`：le_order_mul (φ ψ : R⟦X⟧) : order φ + order ψ 
<= order (φ * ψ)
-/
theorem le_order_prod {R : Type*} [CommSemiring R] {ι : Type*} (φ : ι → R⟦X⟧) (s : Finset ι) :
    ∑ i ∈ s, (φ i).order ≤ (∏ i ∈ s, φ i).order := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => grw [Finset.sum_cons ha, Finset.prod_cons ha, ih, le_order_mul]

alias order_mul_ge := le_order_mul
/-
**PowerSeries.one_le_order_iff_constCoeff_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Pow
erSeries`。
形式化陈述：one_le_order_iff_constCoeff_eq_zero : 1 <= φ.order ↔ φ.constantCoeff = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerSeries.coeff_zero_eq_constantCoeff`：coeff_zero_eq_constantCoeff : ⇑
(coeff (R
· 使用定理 `PowerSeries.coeff_of_lt_order`：coeff_of_lt_order (n : Nat) (h : ↑n < ord
er φ) : coeff n φ = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Order.one_le_iff_pos`：one_le_iff_pos [AddMonoidWithOne α] [ZeroLEOneClas
s α] [NeZero (1 : α)] [SuccAddOrder α] : 1 <= x ↔ 0 < x
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `PowerSeries.le_order`：le_order (φ : R⟦X⟧) (n : Nat∞) (h : forall i : Nat
, ↑i < n -> coeff i φ = 0) : n <= order φ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_lt_one`：cast_lt_one : (n : α) < 1 ↔ n = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem one_le_order_iff_constCoeff_eq_zero :
    1 ≤ φ.order ↔ φ.constantCoeff = 0 := by
  constructor
  · intro h
    rw [← coeff_zero_eq_constantCoeff]
    apply coeff_of_lt_order
    simpa using Order.one_le_iff_pos.mp h
  · intro h
    refine le_order _ _ fun d hd ↦ ?_
    rw [Nat.cast_lt_one] at hd
    simp [hd, h]
/-
**PowerSeries.order_ne_zero_iff_constCoeff_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Po
werSeries`。
形式化陈述：order_ne_zero_iff_constCoeff_eq_zero {φ : R⟦X⟧} : φ.order != 0 ↔ φ.constan
tCoeff = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.one_le_iff_ne_zero`：one_le_iff_ne_zero [AddMonoidWithOne α] [NeZer
o (1 : α)] [SuccAddOrder α] [IsBotZeroClass α] : 1 <= x ↔ x != 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `PowerSeries.one_le_order_iff_constCoeff_eq_zero`：one_le_order_iff_constC
oeff_eq_zero : 1 <= φ.order ↔ φ.constantCoeff = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem order_ne_zero_iff_constCoeff_eq_zero {φ : R⟦X⟧} :
    φ.order ≠ 0 ↔ φ.constantCoeff = 0 := by
  rw [← Order.one_le_iff_ne_zero, one_le_order_iff_constCoeff_eq_zero]
/-
**PowerSeries.le_order_pow_of_constantCoeff_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `P
owerSeries`。
形式化陈述：le_order_pow_of_constantCoeff_eq_zero (n : Nat) (hf : φ.constantCoeff = 0)
 : n <= (φ ^ n).order
参数：n : Nat；hf : φ.constantCoeff = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `le_mul_of_one_le_right'`：le_mul_of_one_le_right' [MulLeftMono α] {a b : 
α} (h : 1 <= b) : a <= a * b
· 使用定理 `CanonicallyOrderedAdd.toMulLeftMono`：∀ {R : Type u} [inst : NonUnitalNon
AssocSemiring R] [inst_1 : LE R] [CanonicallyOrderedAdd R], MulLeftMono R
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PowerSeries.one_le_order_iff_constCoeff_eq_zero`：one_le_order_iff_constC
oeff_eq_zero : 1 <= φ.order ↔ φ.constantCoeff = 0
· 使用定理 `PowerSeries.le_order_pow`：le_order_pow (φ : R⟦X⟧) (n : Nat) : n • order 
φ <= order (φ ^ n)
-/
theorem le_order_pow_of_constantCoeff_eq_zero (n : ℕ) (hf : φ.constantCoeff = 0) :
    n ≤ (φ ^ n).order := by
  refine .trans ?_ (le_order_pow _ n)
  simpa using le_mul_of_one_le_right' (one_le_order_iff_constCoeff_eq_zero.mpr hf)

/-- The order of the monomial `a*X^n` is infinite if `a = 0` and `n` otherwise. -/
/-
**PowerSeries.order_monomial** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：order_monomial (n : Nat) (a : R) [Decidable (a = 0)] : order (monomial n a
) = if a = 0 then (⊤ : Nat∞) else n
参数：n : Nat；a : R；a = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `PowerSeries.order_eq_top`：order_eq_top {φ : R⟦X⟧} : φ.order = ⊤ ↔ φ = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `PowerSeries.order_eq`：order_eq {φ : R⟦X⟧} {n : Nat∞} : order φ = n ↔ (fo
rall i : Nat, ↑i = n -> coeff i φ != 0) ∧ forall i : Nat, ↑i < n -> coeff i φ = 
0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `PowerSeries.coeff_monomial_same`：coeff_monomial_same (n : Nat) (a : R) :
 coeff n (monomial n a) = a
· 使用定理 `PowerSeries.coeff_monomial`：coeff_monomial (m n : Nat) (a : R) : coeff m
 (monomial n a) = if m = n then a else 0
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞

--- 原说明 ---
The order of the monomial `a*X^n` is infinite if `a = 0` and `n` otherwise.
-/
theorem order_monomial (n : ℕ) (a : R) [Decidable (a = 0)] :
    order (monomial n a) = if a = 0 then (⊤ : ℕ∞) else n := by
  split_ifs with h
  · rw [h, order_eq_top, map_zero]
  · rw [order_eq]
    constructor <;> intro i hi
    · simp only [Nat.cast_inj] at hi
      rwa [hi, coeff_monomial_same]
    · simp only [Nat.cast_lt] at hi
      rw [coeff_monomial, if_neg]
      exact ne_of_lt hi

/-- The order of the monomial `a*X^n` is `n` if `a ≠ 0`. -/
/-
**PowerSeries.order_monomial_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：order_monomial_of_ne_zero (n : Nat) (a : R) (h : a != 0) : order (monomial
 n a) = n
参数：n : Nat；a : R；h : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.order_monomial`：order_monomial (n : Nat) (a : R) [Decidable 
(a = 0)] : order (monomial n a) = if a = 0 then (⊤ : Nat∞) else n
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e

--- 原说明 ---
The order of the monomial `a*X^n` is `n` if `a ≠ 0`.
-/
theorem order_monomial_of_ne_zero (n : ℕ) (a : R) (h : a ≠ 0) : order (monomial n a) = n := by
  classical
  rw [order_monomial, if_neg h]

/-- If `n` is strictly smaller than the order of `ψ`, then the `n`th coefficient of its product
with any other power series is `0`. -/
/-
**PowerSeries.coeff_mul_of_lt_order** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_mul_of_lt_order {φ ψ : R⟦X⟧} {n : Nat} (h : ↑n < ψ.order) : coeff n 
(φ * ψ) = 0
参数：h : ↑n < ψ.order。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_mul`：coeff_mul (n : Nat) (φ ψ : R⟦X⟧) : coeff n (φ * ψ
) = ∑ p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_eq_zero_of_right`：mul_eq_zero_of_right (a : M₀) {b : M₀} (h : b = 0)
 : a * b = 0
· 使用定理 `PowerSeries.coeff_of_lt_order`：coeff_of_lt_order (n : Nat) (h : ↑n < ord
er φ) : coeff n φ = 0
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Finset.HasAntidiagonal.mem_antidiagonal`：∀ {A : Type u_1} {inst : AddMon
oid A} [self : Finset.HasAntidiagonal A] {n : A} {a : A × A},   a ∈ Finset.HasAn
tidiagonal.antidiagonal n ↔ a…
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0

--- 原说明 ---
If `n` is strictly smaller than the order of `ψ`, then the `n`th coefficient of 
its product
with any other power series is `0`.
-/
theorem coeff_mul_of_lt_order {φ ψ : R⟦X⟧} {n : ℕ} (h : ↑n < ψ.order) :
    coeff n (φ * ψ) = 0 := by
  suffices coeff n (φ * ψ) = ∑ p ∈ antidiagonal n, 0 by rw [this, Finset.sum_const_zero]
  rw [coeff_mul]
  apply Finset.sum_congr rfl
  intro x hx
  refine mul_eq_zero_of_right (coeff x.fst φ) (coeff_of_lt_order x.snd (lt_of_le_of_lt ?_ h))
  rw [mem_antidiagonal] at hx
  norm_cast
  lia
/-
**PowerSeries.coeff_mul_one_sub_of_lt_order** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeri
es`。
形式化陈述：coeff_mul_one_sub_of_lt_order {R : Type*} [Ring R] {φ ψ : R⟦X⟧} (n : Nat) 
(h : ↑n < ψ.order) : coeff n (φ * (1 - ψ)) = coeff n φ
参数：n : Nat；h : ↑n < ψ.order。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `PowerSeries.coeff_mul_of_lt_order`：coeff_mul_of_lt_order {φ ψ : R⟦X⟧} {n
 : Nat} (h : ↑n < ψ.order) : coeff n (φ * ψ) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_mul_one_sub_of_lt_order {R : Type*} [Ring R] {φ ψ : R⟦X⟧} (n : ℕ)
    (h : ↑n < ψ.order) : coeff n (φ * (1 - ψ)) = coeff n φ := by
  simp [coeff_mul_of_lt_order h, mul_sub]
/-
**PowerSeries.coeff_mul_prod_one_sub_of_lt_order** 是 Mathlib 中的一个定理，位于命名空间 `Powe
rSeries`。
形式化陈述：coeff_mul_prod_one_sub_of_lt_order {R ι : Type*} [CommRing R] (k : Nat) (s
 : Finset ι) (φ : R⟦X⟧) (f : ι -> R⟦X⟧) : (forall i in s, ↑k < (f i).order) -> c
oeff k (φ * ∏ i in s, (1 - f i)) = coeff k φ
参数：k : Nat；s : Finset ι；φ : R⟦X⟧；f : ι -> R⟦X⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `PowerSeries.coeff_mul_one_sub_of_lt_order`：coeff_mul_one_sub_of_lt_order
 {R : Type*} [Ring R] {φ ψ : R⟦X⟧} (n : Nat) (h : ↑n < ψ.order) : coeff n (φ * (
1 - ψ)) = coeff n φ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem coeff_mul_prod_one_sub_of_lt_order {R ι : Type*} [CommRing R] (k : ℕ) (s : Finset ι)
    (φ : R⟦X⟧) (f : ι → R⟦X⟧) :
    (∀ i ∈ s, ↑k < (f i).order) → coeff k (φ * ∏ i ∈ s, (1 - f i)) = coeff k φ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    intro t
    simp only [Finset.mem_insert, forall_eq_or_imp] at t
    rw [Finset.prod_insert ha, ← mul_assoc, mul_right_comm, coeff_mul_one_sub_of_lt_order _ t.1]
    exact ih t.2

@[simp]
/-
**PowerSeries.order_neg** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：order_neg {R : Type*} [Ring R] (φ : PowerSeries R) : (-φ).order = φ.order
参数：φ : PowerSeries R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `PowerSeries.order_zero`：order_zero : order (0 : R⟦X⟧) = ⊤
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerSeries.order_add_of_order_ne`：order_add_of_order_ne (φ ψ : R⟦X⟧) (h
 : order φ != order ψ) : order (φ + ψ) = order φ ⊓ order ψ
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
theorem order_neg {R : Type*} [Ring R] (φ : PowerSeries R) : (-φ).order = φ.order := by
  by_contra! h
  have : φ = 0 := by simpa using (order_add_of_order_ne _ _ h).symm
  simp [this] at h

/-- Given a non-zero power series `f`, `divXPowOrder f` is the power series obtained by
dividing out the largest power of X that divides `f`, that is its order -/
/-
**PowerSeries.divXPowOrder** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：divXPowOrder (f : R⟦X⟧) : R⟦X⟧
参数：f : R⟦X⟧。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a non-zero power series `f`, `divXPowOrder f` is the power series obtained
 by
dividing out the largest power of X that divides `f`, that is its order
-/
def divXPowOrder (f : R⟦X⟧) : R⟦X⟧ :=
  .mk fun n ↦ coeff (n + f.order.toNat) f

@[simp]
/-
**PowerSeries.coeff_divXPowOrder** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_divXPowOrder {f : R⟦X⟧} {n : Nat} : coeff n (divXPowOrder f) = coeff
 (n + f.order.toNat) f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.coeff_mk`：coeff_mk (n : Nat) (f : Nat -> R) : coeff n (mk f)
 = f n
-/
lemma coeff_divXPowOrder {f : R⟦X⟧} {n : ℕ} :
    coeff n (divXPowOrder f) = coeff (n + f.order.toNat) f :=
  coeff_mk _ _

@[simp]
/-
**PowerSeries.divXPowOrder_zero** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：divXPowOrder_zero : divXPowOrder (0 : R⟦X⟧) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PowerSeries.coeff_divXPowOrder`：coeff_divXPowOrder {f : R⟦X⟧} {n : Nat} 
: coeff n (divXPowOrder f) = coeff (n + f.order.toNat) f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PowerSeries.order_zero`：order_zero : order (0 : R⟦X⟧) = ⊤
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma divXPowOrder_zero :
    divXPowOrder (0 : R⟦X⟧) = 0 := by
  ext
  simp
/-
**PowerSeries.constantCoeff_divXPowOrder** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`
。
形式化陈述：constantCoeff_divXPowOrder {f : R⟦X⟧} : constantCoeff (divXPowOrder f) = c
oeff f.order.toNat f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `PowerSeries.coeff_divXPowOrder`：coeff_divXPowOrder {f : R⟦X⟧} {n : Nat} 
: coeff n (divXPowOrder f) = coeff (n + f.order.toNat) f
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma constantCoeff_divXPowOrder {f : R⟦X⟧} :
    constantCoeff (divXPowOrder f) = coeff f.order.toNat f := by
  simp [← coeff_zero_eq_constantCoeff]
/-
**PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `
PowerSeries`。
形式化陈述：constantCoeff_divXPowOrder_eq_zero_iff {f : R⟦X⟧} : constantCoeff (divXPow
Order f) = 0 ↔ f = 0
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
· 使用引理 `PowerSeries.divXPowOrder_zero`：divXPowOrder_zero : divXPowOrder (0 : R⟦X
⟧) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `PowerSeries.constantCoeff_divXPowOrder`：constantCoeff_divXPowOrder {f : 
R⟦X⟧} : constantCoeff (divXPowOrder f) = coeff f.order.toNat f
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `PowerSeries.coeff_order`：coeff_order (h : φ != 0) : coeff φ.order.toNat 
φ != 0
-/
lemma constantCoeff_divXPowOrder_eq_zero_iff {f : R⟦X⟧} :
    constantCoeff (divXPowOrder f) = 0 ↔ f = 0 := by
  by_cases h : f = 0
  · simp [h]
  · simp [constantCoeff_divXPowOrder, coeff_order h, h]
/-
**PowerSeries.X_pow_order_mul_divXPowOrder** 是 Mathlib 中的一个定理，位于命名空间 `PowerSerie
s`。
形式化陈述：X_pow_order_mul_divXPowOrder {f : R⟦X⟧} : X ^ f.order.toNat * divXPowOrder
 f = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_X_pow_mul'`：coeff_X_pow_mul' (p : R⟦X⟧) (n d : Nat) : 
coeff d (X ^ n * p) = ite (n <= d) (coeff (d - n) p) 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `PowerSeries.coeff_divXPowOrder`：coeff_divXPowOrder {f : R⟦X⟧} {n : Nat} 
: coeff n (divXPowOrder f) = coeff (n + f.order.toNat) f
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `PowerSeries.coeff_of_lt_order_toNat`：coeff_of_lt_order_toNat (n : Nat) (
h : n < φ.order.toNat) : coeff n φ = 0
-/
theorem X_pow_order_mul_divXPowOrder {f : R⟦X⟧} :
    X ^ f.order.toNat * divXPowOrder f = f := by
  ext n
  rw [coeff_X_pow_mul']
  split_ifs with h
  · simp [h]
  · push Not at h
    rw [coeff_of_lt_order_toNat _ h]
/-
**PowerSeries.X_pow_order_dvd** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：X_pow_order_dvd : X ^ φ.order.toNat ∣ φ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.coeff_of_lt_order_toNat`：coeff_of_lt_order_toNat (n : Nat) (
h : n < φ.order.toNat) : coeff n φ = 0
-/
theorem X_pow_order_dvd : X ^ φ.order.toNat ∣ φ := by
  simpa only [X_pow_dvd_iff] using coeff_of_lt_order_toNat
/-
**PowerSeries.order_eq_emultiplicity_X** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：order_eq_emultiplicity_X {R : Type*} [Semiring R] (φ : R⟦X⟧) : order φ = e
multiplicity X φ
参数：φ : R⟦X⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.order_zero`：order_zero : order (0 : R⟦X⟧) = ⊤
· 使用定理 `emultiplicity_zero`：emultiplicity_zero (a : α) : emultiplicity a 0 = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Order.le_of_lt_add_one`：le_of_lt_add_one (h : x < y + 1) : x <= y
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `pow_dvd_iff_le_emultiplicity`：pow_dvd_iff_le_emultiplicity {k : Nat} : a
 ^ k ∣ b ↔ k <= emultiplicity a b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_order`：coeff_order (h : φ != 0) : coeff φ.order.toNat 
φ != 0
· 使用定理 `PowerSeries.coeff_mul_of_lt_order`：coeff_mul_of_lt_order {φ ψ : R⟦X⟧} {n
 : Nat} (h : ↑n < ψ.order) : coeff n (φ * ψ) = 0
· 使用定理 `PowerSeries.X_pow_eq`：X_pow_eq (n : Nat) : (X : R⟦X⟧) ^ n = monomial n 1
· 使用定理 `PowerSeries.order_monomial`：order_monomial (n : Nat) (a : R) [Decidable 
(a = 0)] : order (monomial n a) = if a = 0 then (⊤ : Nat∞) else n
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `ENat.natCast_lt_natCast`：natCast_lt_natCast {n m : Nat} : (n : Nat∞) < (
m : Nat∞) ↔ n < m
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
（共 35 条，此处仅展示前 30 条）
-/
theorem order_eq_emultiplicity_X {R : Type*} [Semiring R] (φ : R⟦X⟧) :
    order φ = emultiplicity X φ := by
  classical
  rcases eq_or_ne φ 0 with (rfl | hφ)
  · simp
  cases ho : order φ with
  | top => simp [hφ] at ho
  | coe n =>
    have hn : φ.order.toNat = n := by simp [ho]
    rw [← hn, eq_comm]
    apply le_antisymm _
    · apply le_emultiplicity_of_pow_dvd
      apply X_pow_order_dvd
    · apply Order.le_of_lt_add_one
      rw [← not_le, ← Nat.cast_one, ← Nat.cast_add, ← pow_dvd_iff_le_emultiplicity]
      rintro ⟨ψ, H⟩
      have := congr_arg (coeff n) H
      rw [X_pow_mul, coeff_mul_of_lt_order, ← hn] at this
      · exact coeff_order hφ this
      · rw [X_pow_eq, order_monomial]
        split_ifs
        · simp
        · rw [← hn, ENat.natCast_lt_natCast]
          simp

end OrderBasic

section OrderZeroNeOne

variable [Semiring R] [Nontrivial R]

/-- The order of the formal power series `1` is `0`. -/
@[simp]
/-
**PowerSeries.order_one** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：order_one : order (1 : R⟦X⟧) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `PowerSeries.monomial_zero_eq_C`：monomial_zero_eq_C : ⇑(monomial (R
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `PowerSeries.order_monomial_of_ne_zero`：order_monomial_of_ne_zero (n : Na
t) (a : R) (h : a != 0) : order (monomial n a) = n
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0

--- 原说明 ---
The order of the formal power series `1` is `0`.
-/
theorem order_one : order (1 : R⟦X⟧) = 0 := by
  simpa using order_monomial_of_ne_zero 0 (1 : R) one_ne_zero

/-- The order of an invertible power series is `0`. -/
/-
**PowerSeries.order_zero_of_unit** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：order_zero_of_unit {f : R⟦X⟧} : IsUnit f -> f.order = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_eq_zero`：∀ {α : Type u} [inst : AddCommMonoid α] [Subsingleton (AddU
nits α)] {a b : α}, a + b = 0 ↔ a = 0 ∧ b = 0
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `PowerSeries.order_one`：order_one : order (1 : R⟦X⟧) = 0
· 使用定理 `PowerSeries.order_mul_ge`：∀ {R : Type u_1} [inst : Semiring R] (φ ψ : Po
werSeries R), φ.order + ψ.order ≤ (φ * ψ).order

--- 原说明 ---
The order of an invertible power series is `0`.
-/
theorem order_zero_of_unit {f : R⟦X⟧} : IsUnit f → f.order = 0 := by
  rintro ⟨⟨u, v, hu, hv⟩, hf⟩
  apply And.left
  rw [← add_eq_zero, ← hf, ← nonpos_iff_eq_zero, ← @order_one R _ _, ← hu]
  exact order_mul_ge _ _

/-- The order of the formal power series `X` is `1`. -/
@[simp]
/-
**PowerSeries.order_X** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：order_X : order (X : R⟦X⟧) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `PowerSeries.order_monomial_of_ne_zero`：order_monomial_of_ne_zero (n : Na
t) (a : R) (h : a != 0) : order (monomial n a) = n
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0

--- 原说明 ---
The order of the formal power series `X` is `1`.
-/
theorem order_X : order (X : R⟦X⟧) = 1 := by
  simpa only [Nat.cast_one] using! order_monomial_of_ne_zero 1 (1 : R) one_ne_zero

/-- The order of the formal power series `X^n` is `n`. -/
@[simp]
/-
**PowerSeries.order_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：order_X_pow (n : Nat) : order ((X : R⟦X⟧) ^ n) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.X_pow_eq`：X_pow_eq (n : Nat) : (X : R⟦X⟧) ^ n = monomial n 1
· 使用定理 `PowerSeries.order_monomial_of_ne_zero`：order_monomial_of_ne_zero (n : Na
t) (a : R) (h : a != 0) : order (monomial n a) = n
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0

--- 原说明 ---
The order of the formal power series `X^n` is `n`.
-/
theorem order_X_pow (n : ℕ) : order ((X : R⟦X⟧) ^ n) = n := by
  rw [X_pow_eq, order_monomial_of_ne_zero]
  exact one_ne_zero

/-- Dividing `X` by the maximal power of `X` dividing it leaves `1`. -/
@[simp]
/-
**PowerSeries.divXPowOrder_X** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：divXPowOrder_X : divXPowOrder X = (1 : R⟦X⟧)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PowerSeries.coeff_divXPowOrder`：coeff_divXPowOrder {f : R⟦X⟧} {n : Nat} 
: coeff n (divXPowOrder f) = coeff (n + f.order.toNat) f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PowerSeries.order_X`：order_X : order (X : R⟦X⟧) = 1
· 使用定理 `PowerSeries.coeff_X`：coeff_X (n : Nat) : coeff n (X : R⟦X⟧) = if n = 1 t
hen 1 else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `PowerSeries.coeff_one`：coeff_one (n : Nat) : coeff n (1 : R⟦X⟧) = if n =
 0 then 1 else 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Dividing `X` by the maximal power of `X` dividing it leaves `1`.
-/
theorem divXPowOrder_X :
    divXPowOrder X = (1 : R⟦X⟧) := by
  ext n
  simp [coeff_X]
/-
**PowerSeries.divXPowOrder_one** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：divXPowOrder_one : divXPowOrder 1 = (1 : R⟦X⟧)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PowerSeries.coeff_divXPowOrder`：coeff_divXPowOrder {f : R⟦X⟧} {n : Nat} 
: coeff n (divXPowOrder f) = coeff (n + f.order.toNat) f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PowerSeries.order_one`：order_one : order (1 : R⟦X⟧) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `PowerSeries.coeff_one`：coeff_one (n : Nat) : coeff n (1 : R⟦X⟧) = if n =
 0 then 1 else 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem divXPowOrder_one : divXPowOrder 1 = (1 : R⟦X⟧) := by
  ext k
  simp

end OrderZeroNeOne

section NoZeroDivisors

variable [Semiring R] [NoZeroDivisors R]

/-- The order of the product of two formal power series over an integral domain
is the sum of their orders. -/
/-
**PowerSeries.order_mul** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：order_mul (φ ψ : R⟦X⟧) : order (φ * ψ) = order φ + order ψ
参数：φ ψ : R⟦X⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `PowerSeries.order_zero`：order_zero : order (0 : R⟦X⟧) = ⊤
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_top`：add_top (a : α) : a + ⊤ = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerSeries.coe_toNat_order`：coe_toNat_order {φ : R⟦X⟧} (hf : φ != 0) : 
φ.order.toNat = φ.order
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ENat.natCast_add`：natCast_add (m n : Nat) : ↑(m + n) = (m + n : Nat∞)
· 使用定理 `PowerSeries.order_le`：order_le (n : Nat) (h : coeff n φ != 0) : order φ 
<= n
· 使用定理 `PowerSeries.coeff_mul`：coeff_mul (n : Nat) (φ ψ : R⟦X⟧) : coeff n (φ * ψ
) = ∑ p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ
· 使用定理 `Finset.sum_eq_single_of_mem`：∀ {ι : Type u_1} {M : Type u_4} [inst : Add
CommMonoid M] {s : Finset ι} {f : ι → M},   ∀ a ∈ s, (∀ b ∈ s, b ≠ a → f b = 0) 
→ ∑ x ∈ s, f x = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `trichotomy_of_add_eq_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Line
arOrder α] {a b c d : α} [AddLeftStrictMono α] [AddRightStrictMono α],   a + b =
 c + d → a = c…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
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
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
The order of the product of two formal power series over an integral domain
is the sum of their orders.
-/
theorem order_mul (φ ψ : R⟦X⟧) : order (φ * ψ) = order φ + order ψ := by
  apply le_antisymm _ (le_order_mul _ _)
  by_cases! h : φ = 0 ∨ ψ = 0
  · rcases h with h | h <;> simp [h]
  · rw [← coe_toNat_order h.1, ← coe_toNat_order h.2, ← ENat.natCast_add]
    apply order_le
    rw [coeff_mul, Finset.sum_eq_single_of_mem ⟨φ.order.toNat, ψ.order.toNat⟩ (by simp)]
    · exact mul_ne_zero (coeff_order h.1) (coeff_order h.2)
    · intro ij hij h
      rcases trichotomy_of_add_eq_add (mem_antidiagonal.mp hij) with h' | h' | h'
      · exact False.elim (h (by simp [Prod.ext_iff, h'.1, h'.2]))
      · rw [coeff_of_lt_order_toNat ij.1 h', zero_mul]
      · rw [coeff_of_lt_order_toNat ij.2 h', mul_zero]

/-- The operation of dividing a power series by the largest possible power of `X`
preserves multiplication. -/
/-
**PowerSeries.divXPowOrder_mul** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：divXPowOrder_mul {f g : R⟦X⟧} : divXPowOrder (f * g) = divXPowOrder f * di
vXPowOrder g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用引理 `PowerSeries.divXPowOrder_zero`：divXPowOrder_zero : divXPowOrder (0 : R⟦X
⟧) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `PowerSeries.X_pow_mul_cancel`：X_pow_mul_cancel {k : Nat} {φ ψ : R⟦X⟧} (h
 : X ^ k * φ = X ^ k * ψ) : φ = ψ
· 使用定理 `PowerSeries.order_mul`：order_mul (φ ψ : R⟦X⟧) : order (φ * ψ) = order φ 
+ order ψ
· 使用定理 `ENat.toNat_add`：toNat_add {m n : Nat∞} (hm : m != ⊤) (hn : n != ⊤) : toN
at (m + n) = toNat m + toNat n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `PowerSeries.order_eq_top`：order_eq_top {φ : R⟦X⟧} : φ.order = ⊤ ↔ φ = 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `PowerSeries.X_pow_order_mul_divXPowOrder`：X_pow_order_mul_divXPowOrder {
f : R⟦X⟧} : X ^ f.order.toNat * divXPowOrder f = f
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `PowerSeries.X_pow_mul`：X_pow_mul {φ : R⟦X⟧} {n : Nat} : X ^ n * φ = φ * 
X ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a

--- 原说明 ---
The operation of dividing a power series by the largest possible power of `X`
preserves multiplication.
-/
theorem divXPowOrder_mul {f g : R⟦X⟧} :
    divXPowOrder (f * g) = divXPowOrder f * divXPowOrder g := by
  by_cases! h : f = 0 ∨ g = 0
  · rcases h with (h | h) <;> simp [h]
  apply X_pow_mul_cancel (k := f.order.toNat + g.order.toNat)
  calc
    _ = X ^ ((f * g).order.toNat) * (f * g).divXPowOrder := by
        rw [order_mul, ENat.toNat_add (order_eq_top.not.mpr h.1) (order_eq_top.not.mpr h.2)]
    _ = f * g := by
        simp [X_pow_order_mul_divXPowOrder]
    _ = (X ^ f.order.toNat * f.divXPowOrder) * (X ^ g.order.toNat * g.divXPowOrder) := by
        simp [X_pow_order_mul_divXPowOrder]
    _ = f.divXPowOrder * g.divXPowOrder * X ^ (g.order.toNat + f.order.toNat) := by
        rw [mul_assoc, X_pow_mul, X_pow_mul, ← mul_assoc, mul_assoc, ← pow_add]
    _ = X ^ (f.order.toNat + g.order.toNat) * (f.divXPowOrder * g.divXPowOrder) := by
        rw [X_pow_mul, add_comm]

variable [Nontrivial R]

/-- `PowerSeries.order` as a `MonoidHom`. -/
/-
**PowerSeries.orderHom** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：orderHom : R⟦X⟧ ->* Multiplicative Nat∞ where toFun g
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.order_one`：order_one : order (1 : R⟦X⟧) = 0
· 使用定理 `PowerSeries.order_mul`：order_mul (φ ψ : R⟦X⟧) : order (φ * ψ) = order φ 
+ order ψ

--- 原说明 ---
`PowerSeries.order` as a `MonoidHom`.
-/
def orderHom : R⟦X⟧ →* Multiplicative ℕ∞ where
  toFun g := .ofAdd g.order
  map_one' := order_one
  map_mul' := order_mul

@[simp, norm_cast]
/-
**PowerSeries.coe_orderHom** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：coe_orderHom : (orderHom : R⟦X⟧ -> Nat∞) = order
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_orderHom : (orderHom : R⟦X⟧ → ℕ∞) = order := rfl
/-
**PowerSeries.order_pow** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：order_pow (φ : R⟦X⟧) (n : Nat) : order (φ ^ n) = n • order φ
参数：φ : R⟦X⟧；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
-/
theorem order_pow (φ : R⟦X⟧) (n : ℕ) : order (φ ^ n) = n • order φ :=
  map_pow orderHom φ n
/-
**PowerSeries.order_prod** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：order_prod {R : Type*} [CommSemiring R] [NoZeroDivisors R] [Nontrivial R] 
{ι : Type*} (φ : ι -> R⟦X⟧) (s : Finset ι) : (∏ i in s, φ i).order = ∑ i in s, (
φ i).order
参数：φ : ι -> R⟦X⟧；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
-/
theorem order_prod {R : Type*} [CommSemiring R] [NoZeroDivisors R] [Nontrivial R] {ι : Type*}
    (φ : ι → R⟦X⟧) (s : Finset ι) : (∏ i ∈ s, φ i).order = ∑ i ∈ s, (φ i).order :=
  map_prod orderHom φ s

/-- `PowerSeries.divXPowOrder` as a `MonoidHom`. -/
/-
**PowerSeries.divXPowOrderHom** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：divXPowOrderHom : R⟦X⟧ ->* R⟦X⟧ where toFun g
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.divXPowOrder_one`：divXPowOrder_one : divXPowOrder 1 = (1 : R
⟦X⟧)
· 使用定理 `PowerSeries.divXPowOrder_mul`：divXPowOrder_mul {f g : R⟦X⟧} : divXPowOrd
er (f * g) = divXPowOrder f * divXPowOrder g

--- 原说明 ---
`PowerSeries.divXPowOrder` as a `MonoidHom`.
-/
def divXPowOrderHom : R⟦X⟧ →* R⟦X⟧ where
  toFun g := g.divXPowOrder
  map_one' := divXPowOrder_one
  map_mul' f g := divXPowOrder_mul (f := f) (g := g)

@[simp, norm_cast]
/-
**PowerSeries.coe_divXPowOrderHom** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：coe_divXPowOrderHom : (divXPowOrderHom : R⟦X⟧ -> R⟦X⟧) = divXPowOrder
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_divXPowOrderHom : (divXPowOrderHom : R⟦X⟧ → R⟦X⟧) = divXPowOrder := rfl
/-
**PowerSeries.divXPowOrder_pow** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：divXPowOrder_pow (φ : R⟦X⟧) (n : Nat) : divXPowOrder (φ ^ n) = (divXPowOrd
er φ) ^ n
参数：φ : R⟦X⟧；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
-/
theorem divXPowOrder_pow (φ : R⟦X⟧) (n : ℕ) : divXPowOrder (φ ^ n) = (divXPowOrder φ) ^ n :=
  map_pow divXPowOrderHom φ n
/-
**PowerSeries.divXPowOrder_prod** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：divXPowOrder_prod {R : Type*} [CommSemiring R] [NoZeroDivisors R] [Nontriv
ial R] {ι : Type*} (φ : ι -> R⟦X⟧) (s : Finset ι) : (∏ i in s, φ i).divXPowOrder
 = ∏ i in s, (φ i).divXPowOrder
参数：φ : ι -> R⟦X⟧；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
-/
theorem divXPowOrder_prod {R : Type*} [CommSemiring R] [NoZeroDivisors R] [Nontrivial R] {ι : Type*}
    (φ : ι → R⟦X⟧) (s : Finset ι) : (∏ i ∈ s, φ i).divXPowOrder = ∏ i ∈ s, (φ i).divXPowOrder :=
  map_prod divXPowOrderHom φ s

end NoZeroDivisors

section Ring

variable [Ring R] (p : PowerSeries R) (T : Subring R) (hp : ∀ n, p.coeff n ∈ T)

@[simp]
/-
**PowerSeries.order_toSubring** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：order_toSubring : (p.toSubring T hp).order = p.order
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_le_of_ge`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `PowerSeries.le_order`：le_order (φ : R⟦X⟧) (n : Nat∞) (h : forall i : Nat
, ↑i < n -> coeff i φ = 0) : n <= order φ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerSeries.coeff_toSubring`：coeff_toSubring {n : Nat} : (p.toSubring T 
hp).coeff n = p.coeff n
· 使用定理 `PowerSeries.coeff_of_lt_order`：coeff_of_lt_order (n : Nat) (h : ↑n < ord
er φ) : coeff n φ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
-/
theorem order_toSubring : (p.toSubring T hp).order = p.order := by
  refine eq_of_le_of_ge ?_ ?_
  · refine le_order _ _ fun d hd => by simp [coeff_of_lt_order d hd, ← coeff_toSubring p T hp]
  · exact le_order _ _ fun d hd => by
      exact_mod_cast (coeff_toSubring p T hp) ▸ (coeff_of_lt_order d hd)

end Ring

end PowerSeries

end

