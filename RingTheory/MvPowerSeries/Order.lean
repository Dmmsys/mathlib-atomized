/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos Fernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
module

public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.RingTheory.MvPowerSeries.Basic

/-! # Order of multivariate power series

We work with `MvPowerSeries σ R`, for `Semiring R`, and `w : σ → ℕ`.

## Weighted Order

- `MvPowerSeries.weightedOrder`: the weighted order of a multivariate power series,
  with respect to `w`, as an element of `ℕ∞`.

- `MvPowerSeries.weightedOrder_zero`: the weighted order of `0` is `0`.

- `MvPowerSeries.ne_zero_iff_weightedOrder_finite`: a multivariate power series is nonzero if
  and only if its weighted order is finite.

- `MvPowerSeries.exists_coeff_ne_zero_of_weightedOrder`: if the weighted order is finite,
  then there exists a nonzero coefficient of weight the weighted order.

- `MvPowerSeries.weightedOrder_le` : if a coefficient is nonzero, then the weighted order is at
  most the weight of that exponent.

- `MvPowerSeries.coeff_eq_zero_of_lt_weightedOrder`: all coefficients of weights strictly less
  than the weighted order vanish.

- `MvPowerSeries.weightedOrder_eq_top_iff`: the weighted order of `f` is `⊤` if and only if `f = 0`.

- `MvPowerSeries.nat_le_weightedOrder`: if all coefficients of weight `< n` vanish, then the
  weighted order is at least `n`.

- `MvPowerSeries.weightedOrder_eq_nat_iff`: the weighted order is some integer `n` iff there
  exists a nonzero coefficient of weight `n`, and all coefficients of strictly smaller weight
  vanish.

- `MvPowerSeries.weightedOrder_monomial`, `MvPowerSeries.weightedOrder_monomial_of_ne_zero`:
  the weighted order of a monomial, of a monomial with nonzero coefficient.

- `MvPowerSeries.min_weightedOrder_le_add`: the order of the sum of two multivariate power series
  is at least the minimum of their orders.

- `MvPowerSeries.weightedOrder_add_of_weightedOrder_ne`: the `weightedOrder` of the sum of two
  formal power series is the minimum of their orders if their orders differ.

- `MvPowerSeries.le_weightedOrder_mul`: the `weightedOrder` of the product of two formal power
  series is at least the sum of their orders.

- `MvPowerSeries.coeff_mul_left_one_sub_of_lt_weightedOrder`,
  `MvPowerSeries.coeff_mul_right_one_sub_of_lt_weightedOrder`: the coefficients of `f * (1 - g)`
  and `(1 - g) * f` in weights strictly less than the weighted order of `g`.

- `MvPowerSeries.coeff_mul_prod_one_sub_of_lt_weightedOrder`: the coefficients of
  `f * Π i in s, (1 - g i)`, in weights strictly less than the weighted orders of `g i`, for
  `i ∈ s`.

## Order

- `MvPowerSeries.order`: the weighted order, for `w = (1 : σ → ℕ)`.

- `MvPowerSeries.ne_zero_iff_order_finite`: `f` is nonzero iff its order is finite.

- `MvPowerSeries.order_eq_top_iff`: the order of `f` is infinite iff `f = 0`.

- `MvPowerSeries.exists_coeff_ne_zero_of_order`: if the order is finite, then there exists a
  nonzero coefficient of degree equal to the order.

- `MvPowerSeries.order_le` : if a coefficient of some degree is nonzero, then the order
  is at least that degree.

- `MvPowerSeries.nat_le_order`: if all coefficients of degree strictly smaller than some integer
  vanish, then the order is at least that integer.

- `MvPowerSeries.order_eq_nat_iff`:  the order of a power series is an integer `n` iff there exists
  a nonzero coefficient in that degree, and all coefficients below that degree vanish.

- `MvPowerSeries.order_monomial`, `MvPowerSeries.order_monomial_of_ne_zero`: the order of a
  monomial, with a nonzero coefficient

- `MvPowerSeries.min_order_le_add`: the order of a sum of two power series is at least the minimum
  of their orders.

- `MvPowerSeries.order_add_of_order_ne`: the order of a sum of two power series of distinct orders
  is the minimum of their orders.

- `MvPowerSeries.order_mul_ge`: the order of a product of two power series is at least the sum of
  their orders.

- `MvPowerSeries.coeff_mul_left_one_sub_of_lt_order`,
  `MvPowerSeries.coeff_mul_right_one_sub_of_lt_order`: the coefficients of `f * (1 - g)` and
  `(1 - g) * f` below the order of `g` coincide with that of `f`.

- `MvPowerSeries.coeff_mul_prod_one_sub_of_lt_order`: the coefficients of `f * Π i in s, (1 - g i)`
  coincide with that of `f` below the minimum of the orders of the `g i`, for `i ∈ s`.

## Homogeneous components

- `MvPowerSeries.weightedHomogeneousComponent`, `MvPowerSeries.homogeneousComponent`: the power
  series which is the sum of all monomials of given weighted degree, resp. degree.

NOTE:
Under `Finite σ`, one can use `Finsupp.finite_of_degree_le` and `Finsupp.finite_of_weight_le` to
show that they have finite support, hence correspond to `MvPolynomial`.

However, when `σ` is finite, this is not necessarily an `MvPolynomial`.
(For example: the homogeneous components of degree 1 of the multivariate power
series, all of which coefficients are `1`, is the sum of all indeterminates.)

TODO: Define a coercion to MvPolynomial.

-/

@[expose] public section

namespace MvPowerSeries

noncomputable section

open ENat WithTop Finsupp

variable {σ R : Type*} [Semiring R]

section WeightedOrder

variable (w : σ → ℕ) {f g : MvPowerSeries σ R}

/-
**MvPowerSeries.ne_zero_iff_exists_coeff_ne_zero_and_weight** 是 Mathlib 中的一个定理，位
于命名空间 `MvPowerSeries`。
形式化陈述：ne_zero_iff_exists_coeff_ne_zero_and_weight : f != 0 ↔ (exists n : Nat, ex
ists d : σ ->₀ Nat, coeff d f != 0 ∧ weight w d = n)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `MvPowerSeries.ne_zero_iff_exists_coeff_ne_zero`：ne_zero_iff_exists_coeff
_ne_zero (f : MvPowerSeries σ R) : f != 0 ↔ (exists d : σ ->₀ Nat, coeff d f != 
0)
-/
theorem ne_zero_iff_exists_coeff_ne_zero_and_weight :
    f ≠ 0 ↔ (∃ n : ℕ, ∃ d : σ →₀ ℕ, coeff d f ≠ 0 ∧ weight w d = n) := by
  simpa using ne_zero_iff_exists_coeff_ne_zero f

/-- The weighted order with respect to `w : σ → ℕ`. This is the minimum value
of `weight w d` over all exponents `d` with nonzero coefficient `coeff d f`. -/
/-
**MvPowerSeries.weightedOrder** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
形式化陈述：weightedOrder (f : MvPowerSeries σ R) : Nat∞
参数：f : MvPowerSeries σ R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The weighted order with respect to `w : σ → ℕ`. This is the minimum value
of `weight w d` over all exponents `d` with nonzero coefficient `coeff d f`.
-/
def weightedOrder (f : MvPowerSeries σ R) : ℕ∞ := by
  classical
  exact dite (f = 0) (fun _ => ⊤) fun h =>
    Nat.find ((ne_zero_iff_exists_coeff_ne_zero_and_weight w).mp h)
/-
**MvPowerSeries.weightedOrder_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_2} [inst : Semiring R] (w : σ → ℕ), MvPowerSe
ries.weightedOrder w 0 = ⊤
参数：w : σ → ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.weightedOrder.eq_1`：∀ {σ : Type u_1} {R : Type u_2} [inst 
: Semiring R] (w : σ → ℕ) (f : MvPowerSeries σ R),   MvPowerSeries.weightedOrder
 w f = if x : f = 0 th…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
@[simp] theorem weightedOrder_zero : (0 : MvPowerSeries σ R).weightedOrder w = ⊤ := by
  rw [weightedOrder, dif_pos rfl]
/-
**MvPowerSeries.ne_zero_iff_weightedOrder_finite** 是 Mathlib 中的一个定理，位于命名空间 `MvPo
werSeries`。
形式化陈述：ne_zero_iff_weightedOrder_finite : f != 0 ↔ (f.weightedOrder w).toNat = f.
weightedOrder w
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ne_zero_iff_weightedOrder_finite :
    f ≠ 0 ↔ (f.weightedOrder w).toNat = f.weightedOrder w := by
  simp only [weightedOrder, ne_eq, natCast_toNat_eq_self, dite_eq_left_iff,
    ENat.natCast_ne_top, imp_false, not_not]

/-- The `0` power series is the unique power series with infinite order. -/
@[simp]
/-
**MvPowerSeries.weightedOrder_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSerie
s`。
形式化陈述：weightedOrder_eq_top_iff : f.weightedOrder w = ⊤ ↔ f = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `MvPowerSeries.ne_zero_iff_weightedOrder_finite`：ne_zero_iff_weightedOrde
r_finite : f != 0 ↔ (f.weightedOrder w).toNat = f.weightedOrder w
· 使用定理 `ENat.natCast_toNat_eq_self`：natCast_toNat_eq_self : ENat.toNat n = n ↔ n
 != ⊤
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The `0` power series is the unique power series with infinite order.
-/
theorem weightedOrder_eq_top_iff :
    f.weightedOrder w = ⊤ ↔ f = 0 := by
  rw [← not_iff_not, ← ne_eq, ← ne_eq, ne_zero_iff_weightedOrder_finite w, natCast_toNat_eq_self]

/-- If the order of a formal power series `f` is finite,
then some coefficient of weight equal to the order of `f` is nonzero. -/
/-
**MvPowerSeries.exists_coeff_ne_zero_and_weightedOrder** 是 Mathlib 中的一个定理，位于命名空间
 `MvPowerSeries`。
形式化陈述：exists_coeff_ne_zero_and_weightedOrder (h : (toNat (f.weightedOrder w) : N
at∞) = f.weightedOrder w) : exists d, coeff d f != 0 ∧ weight w d = f.weightedOr
der w
参数：h : (toNat (f.weightedOrder w) : Nat∞) = f.weightedOrder w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MvPowerSeries.ne_zero_iff_weightedOrder_finite`：ne_zero_iff_weightedOrde
r_finite : f != 0 ↔ (f.weightedOrder w).toNat = f.weightedOrder w
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)

--- 原说明 ---
If the order of a formal power series `f` is finite,
then some coefficient of weight equal to the order of `f` is nonzero.
-/
theorem exists_coeff_ne_zero_and_weightedOrder
    (h : (toNat (f.weightedOrder w) : ℕ∞) = f.weightedOrder w) :
    ∃ d, coeff d f ≠ 0 ∧ weight w d = f.weightedOrder w := by
  classical
  simp_rw [weightedOrder, dif_neg ((ne_zero_iff_weightedOrder_finite w).mpr h), Nat.cast_inj]
  generalize_proofs h1
  exact Nat.find_spec h1

/-- If the `d`th coefficient of a formal power series is nonzero,
then the weighted order of the power series is less than or equal to `weight d w`. -/
/-
**MvPowerSeries.weightedOrder_le** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：weightedOrder_le {d : σ ->₀ Nat} (h : coeff d f != 0) : f.weightedOrder w 
<= weight w d
参数：h : coeff d f != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.weightedOrder.eq_1`：∀ {σ : Type u_1} {R : Type u_2} [inst 
: Semiring R] (w : σ → ℕ) (f : MvPowerSeries σ R),   MvPowerSeries.weightedOrder
 w f = if x : f = 0 th…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MvPowerSeries.ne_zero_iff_exists_coeff_ne_zero_and_weight`：ne_zero_iff_e
xists_coeff_ne_zero_and_weight : f != 0 ↔ (exists n : Nat, exists d : σ ->₀ Nat,
 coeff d f != 0 ∧ weight w d = n)
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
If the `d`th coefficient of a formal power series is nonzero,
then the weighted order of the power series is less than or equal to `weight d w
`.
-/
theorem weightedOrder_le {d : σ →₀ ℕ} (h : coeff d f ≠ 0) :
    f.weightedOrder w ≤ weight w d := by
  rw [weightedOrder, dif_neg]
  · simp only [ne_eq, Nat.cast_le, Nat.find_le_iff]
    exact ⟨weight w d, le_rfl, d, h, rfl⟩
  · exact (f.ne_zero_iff_exists_coeff_ne_zero_and_weight w).mpr ⟨weight w d, d, h, rfl⟩

/-- The `n`th coefficient of a formal power series is `0` if `n` is strictly
smaller than the order of the power series. -/
/-
**MvPowerSeries.coeff_eq_zero_of_lt_weightedOrder** 是 Mathlib 中的一个定理，位于命名空间 `MvP
owerSeries`。
形式化陈述：coeff_eq_zero_of_lt_weightedOrder {d : σ ->₀ Nat} (h : (weight w d) < f.we
ightedOrder w) : coeff d f = 0
参数：h : (weight w d) < f.weightedOrder w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `MvPowerSeries.weightedOrder_le`：weightedOrder_le {d : σ ->₀ Nat} (h : co
eff d f != 0) : f.weightedOrder w <= weight w d

--- 原说明 ---
The `n`th coefficient of a formal power series is `0` if `n` is strictly
smaller than the order of the power series.
-/
theorem coeff_eq_zero_of_lt_weightedOrder {d : σ →₀ ℕ} (h : (weight w d) < f.weightedOrder w) :
    coeff d f = 0 := by
  contrapose! h; exact weightedOrder_le w h

/-- The order of a formal power series is at least `n` if
the `d`th coefficient is `0` for all `d` such that `weight w d < n`. -/
/-
**MvPowerSeries.nat_le_weightedOrder** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：nat_le_weightedOrder {n : Nat} (h : forall d, weight w d < n -> coeff d f 
= 0) : n <= f.weightedOrder w
参数：h : forall d, weight w d < n -> coeff d f = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENat.natCast_toNat_eq_self`：natCast_toNat_eq_self : ENat.toNat n = n ↔ n
 != ⊤
· 使用定理 `ne_top_of_lt`：ne_top_of_lt (h : a < b) : a != ⊤
· 使用定理 `MvPowerSeries.exists_coeff_ne_zero_and_weightedOrder`：exists_coeff_ne_ze
ro_and_weightedOrder (h : (toNat (f.weightedOrder w) : Nat∞) = f.weightedOrder w
) : exists d, coeff d f != 0 ∧ weight w d …
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The order of a formal power series is at least `n` if
the `d`th coefficient is `0` for all `d` such that `weight w d < n`.
-/
theorem nat_le_weightedOrder {n : ℕ} (h : ∀ d, weight w d < n → coeff d f = 0) :
    n ≤ f.weightedOrder w := by
  by_contra! H
  have : (f.weightedOrder w).toNat = f.weightedOrder w := by
    rw [natCast_toNat_eq_self]; exact ne_top_of_lt H
  obtain ⟨d, hfd, hd⟩ := exists_coeff_ne_zero_and_weightedOrder w this
  rw [← hd, Nat.cast_lt] at H
  exact hfd (h d H)

/-- The order of a formal power series is at least `n` if
the `d`th coefficient is `0` for all `d` such that `weight w d < n`. -/
/-
**MvPowerSeries.le_weightedOrder** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：le_weightedOrder {n : Nat∞} (h : forall d : σ ->₀ Nat, weight w d < n -> c
oeff d f = 0) : n <= f.weightedOrder w
参数：h : forall d : σ ->₀ Nat, weight w d < n -> coeff d f = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `MvPowerSeries.weightedOrder_eq_top_iff`：weightedOrder_eq_top_iff : f.wei
ghtedOrder w = ⊤ ↔ f = 0
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用引理 `ENat.natCast_lt_top`：natCast_lt_top (n : Nat) : (n : Nat∞) < ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.nat_le_weightedOrder`：nat_le_weightedOrder {n : Nat} (h : 
forall d, weight w d < n -> coeff d f = 0) : n <= f.weightedOrder w
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞

--- 原说明 ---
The order of a formal power series is at least `n` if
the `d`th coefficient is `0` for all `d` such that `weight w d < n`.
-/
theorem le_weightedOrder {n : ℕ∞} (h : ∀ d : σ →₀ ℕ, weight w d < n → coeff d f = 0) :
    n ≤ f.weightedOrder w := by
  cases n
  · rw [top_le_iff, weightedOrder_eq_top_iff]
    ext d; exact h d (ENat.natCast_lt_top _)
  · apply nat_le_weightedOrder;
    simpa only [ENat.some_eq_natCast, Nat.cast_lt] using h

/-- The order of a formal power series is exactly `n` if and only if some coefficient of weight `n`
is nonzero, and the `d`th coefficient is `0` for all `d` such that `weight w d < n`. -/
/-
**MvPowerSeries.weightedOrder_eq_nat** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：weightedOrder_eq_nat {n : Nat} : f.weightedOrder w = n ↔ (exists d, coeff 
d f != 0 ∧ weight w d = n) ∧ forall d, weight w d < n -> coeff d f = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.exists_coeff_ne_zero_and_weightedOrder`：exists_coeff_ne_ze
ro_and_weightedOrder (h : (toNat (f.weightedOrder w) : Nat∞) = f.weightedOrder w
) : exists d, coeff d f != 0 ∧ weight w d …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `MvPowerSeries.coeff_eq_zero_of_lt_weightedOrder`：coeff_eq_zero_of_lt_wei
ghtedOrder {d : σ ->₀ Nat} (h : (weight w d) < f.weightedOrder w) : coeff d f = 
0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MvPowerSeries.weightedOrder_le`：weightedOrder_le {d : σ ->₀ Nat} (h : co
eff d f != 0) : f.weightedOrder w <= weight w d
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.nat_le_weightedOrder`：nat_le_weightedOrder {n : Nat} (h : 
forall d, weight w d < n -> coeff d f = 0) : n <= f.weightedOrder w

--- 原说明 ---
The order of a formal power series is exactly `n` if and only if some coefficien
t of weight `n`
is nonzero, and the `d`th coefficient is `0` for all `d` such that `weight w d <
 n`.
-/
theorem weightedOrder_eq_nat {n : ℕ} :
    f.weightedOrder w = n ↔
      (∃ d, coeff d f ≠ 0 ∧ weight w d = n) ∧ ∀ d, weight w d < n → coeff d f = 0 := by
  constructor
  · intro h
    obtain ⟨d, hd⟩ := f.exists_coeff_ne_zero_and_weightedOrder w (by simp only [h, toNat_natCast])
    exact ⟨⟨d, by simpa [h, Nat.cast_inj, ne_eq] using hd⟩,
      fun e he ↦ f.coeff_eq_zero_of_lt_weightedOrder w (by simp only [h, Nat.cast_lt, he])⟩
  · rintro ⟨⟨d, hd', hd⟩, h⟩
    exact le_antisymm (hd.symm ▸ f.weightedOrder_le w hd') (nat_le_weightedOrder w h)

/-- The `weightedOrder` of the monomial `a*X^d` is infinite if `a = 0` and `weight w d` otherwise.
-/
/-
**MvPowerSeries.weightedOrder_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`
。
形式化陈述：weightedOrder_monomial {d : σ ->₀ Nat} {a : R} [Decidable (a = 0)] : weigh
tedOrder w (monomial d a) = if a = 0 then (⊤ : Nat∞) else weight w d
参数：a = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `MvPowerSeries.weightedOrder_eq_top_iff`：weightedOrder_eq_top_iff : f.wei
ghtedOrder w = ⊤ ↔ f = 0
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
· 使用定理 `MvPowerSeries.weightedOrder_eq_nat`：weightedOrder_eq_nat {n : Nat} : f.w
eightedOrder w = n ↔ (exists d, coeff d f != 0 ∧ weight w d = n) ∧ forall d, wei
ght w d < n -> coeff d f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPowerSeries.coeff_monomial_same`：coeff_monomial_same (n : σ ->₀ Nat) (
a : R) : coeff n (monomial n a) = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `MvPowerSeries.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n : σ ->
₀ Nat) (a : R) : coeff m (monomial n a) = if m = n then a else 0
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False

--- 原说明 ---
The `weightedOrder` of the monomial `a*X^d` is infinite if `a = 0` and `weight w
 d` otherwise.
-/
theorem weightedOrder_monomial {d : σ →₀ ℕ} {a : R} [Decidable (a = 0)] :
    weightedOrder w (monomial d a) = if a = 0 then (⊤ : ℕ∞) else weight w d := by
  classical
  split_ifs with h
  · rw [h, weightedOrder_eq_top_iff, map_zero]
  · rw [weightedOrder_eq_nat]
    constructor
    · use d
      simp only [coeff_monomial_same, ne_eq, h, not_false_eq_true, and_self]
    · intro b hb
      rw [coeff_monomial, if_neg]
      rintro rfl
      exact hb.false

/-- The order of the monomial `a*X^n` is `n` if `a ≠ 0`. -/
/-
**MvPowerSeries.weightedOrder_monomial_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvP
owerSeries`。
形式化陈述：weightedOrder_monomial_of_ne_zero {d : σ ->₀ Nat} {a : R} (h : a != 0) : w
eightedOrder w (monomial d a) = weight w d
参数：h : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.weightedOrder_monomial`：weightedOrder_monomial {d : σ ->₀ 
Nat} {a : R} [Decidable (a = 0)] : weightedOrder w (monomial d a) = if a = 0 the
n (⊤ : Nat∞) else weight w…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e

--- 原说明 ---
The order of the monomial `a*X^n` is `n` if `a ≠ 0`.
-/
theorem weightedOrder_monomial_of_ne_zero {d : σ →₀ ℕ} {a : R} (h : a ≠ 0) :
    weightedOrder w (monomial d a) = weight w d := by
  classical
  rw [weightedOrder_monomial, if_neg h]

@[simp]
/-
**MvPowerSeries.weightedOrder_one** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：weightedOrder_one [Nontrivial R] : (1 : MvPowerSeries σ R).weightedOrder w
 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.weightedOrder_monomial_of_ne_zero`：weightedOrder_monomial_
of_ne_zero {d : σ ->₀ Nat} {a : R} (h : a != 0) : weightedOrder w (monomial d a)
 = weight w d
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
theorem weightedOrder_one [Nontrivial R] : (1 : MvPowerSeries σ R).weightedOrder w = 0 :=
  weightedOrder_monomial_of_ne_zero w one_ne_zero

/-- The order of the sum of two formal power series is at least the minimum of their orders. -/
/-
**MvPowerSeries.min_weightedOrder_le_add** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSerie
s`。
形式化陈述：min_weightedOrder_le_add : min (f.weightedOrder w) (g.weightedOrder w) <= 
(f + g).weightedOrder w
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.le_weightedOrder`：le_weightedOrder {n : Nat∞} (h : forall 
d : σ ->₀ Nat, weight w d < n -> coeff d f = 0) : n <= f.weightedOrder w
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
· 使用定理 `MvPowerSeries.coeff_eq_zero_of_lt_weightedOrder`：coeff_eq_zero_of_lt_wei
ghtedOrder {d : σ ->₀ Nat} (h : (weight w d) < f.weightedOrder w) : coeff d f = 
0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The order of the sum of two formal power series is at least the minimum of their
 orders.
-/
theorem min_weightedOrder_le_add :
    min (f.weightedOrder w) (g.weightedOrder w) ≤ (f + g).weightedOrder w := by
  apply le_weightedOrder w
  simp +contextual only
    [coeff_eq_zero_of_lt_weightedOrder w, lt_min_iff, map_add, add_zero,
      imp_true_iff]
/-
**MvPowerSeries.weightedOrder_add_of_weightedOrder_lt.aux** 是 Mathlib 中的一个定理，位于命
名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem weightedOrder_add_of_weightedOrder_lt.aux
    (H : f.weightedOrder w < g.weightedOrder w) :
    (f + g).weightedOrder w = f.weightedOrder w := by
  obtain ⟨n, hn : (n : ℕ∞) = _⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt H)
  rw [← hn, weightedOrder_eq_nat]
  obtain ⟨d, hd', hd⟩ := ((weightedOrder_eq_nat w).mp hn.symm).1
  constructor
  · refine ⟨d, ?_, hd⟩
    rw [← hn, ← hd] at H
    rw [(coeff _).map_add, coeff_eq_zero_of_lt_weightedOrder w H, add_zero]
    exact hd'
  · intro b hb
    suffices weight w b < weightedOrder w f by
      rw [(coeff _).map_add, coeff_eq_zero_of_lt_weightedOrder w this,
        coeff_eq_zero_of_lt_weightedOrder w (lt_trans this H), add_zero]
    rw [← hn, Nat.cast_lt]
    exact hb

/-- The `weightedOrder` of the sum of two formal power series
is the minimum of their orders if their orders differ. -/
/-
**MvPowerSeries.weightedOrder_add_of_weightedOrder_ne** 是 Mathlib 中的一个定理，位于命名空间 
`MvPowerSeries`。
形式化陈述：weightedOrder_add_of_weightedOrder_ne (h : f.weightedOrder w != g.weighted
Order w) : weightedOrder w (f + g) = weightedOrder w f ⊓ weightedOrder w g
参数：h : f.weightedOrder w != g.weightedOrder w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.RingTheory.MvPowerSeries.Order.0.MvPowerSeries.weighted
Order_add_of_weightedOrder_lt.aux`：∀ {σ : Type u_1} {R : Type u_2} [inst : Semir
ing R] (w : σ → ℕ) {f g : MvPowerSeries σ R},   MvPowerSeries.weightedOrder w f 
< MvPowerSeries…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LE.le.lt_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `MvPowerSeries.min_weightedOrder_le_add`：min_weightedOrder_le_add : min (
f.weightedOrder w) (g.weightedOrder w) <= (f + g).weightedOrder w

--- 原说明 ---
The `weightedOrder` of the sum of two formal power series
is the minimum of their orders if their orders differ.
-/
theorem weightedOrder_add_of_weightedOrder_ne (h : f.weightedOrder w ≠ g.weightedOrder w) :
    weightedOrder w (f + g) = weightedOrder w f ⊓ weightedOrder w g := by
  refine le_antisymm ?_ (min_weightedOrder_le_add w)
  wlog H₁ : f.weightedOrder w < g.weightedOrder w
  · rw [add_comm f g, inf_comm]
    exact this _ h.symm ((le_of_not_gt H₁).lt_of_ne' h)
  simp only [le_inf_iff, weightedOrder_add_of_weightedOrder_lt.aux w H₁]
  exact ⟨le_rfl, le_of_lt H₁⟩

/-- The `weightedOrder` of the product of two formal power series
is at least the sum of their orders. -/
/-
**MvPowerSeries.le_weightedOrder_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：le_weightedOrder_mul : f.weightedOrder w + g.weightedOrder w <= weightedOr
der w (f * g)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.le_weightedOrder`：le_weightedOrder {n : Nat∞} (h : forall 
d : σ ->₀ Nat, weight w d < n -> coeff d f = 0) : n <= f.weightedOrder w
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_mul`：coeff_mul [DecidableEq σ] : coeff n (φ * ψ) = ∑
 p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `MvPowerSeries.coeff_eq_zero_of_lt_weightedOrder`：coeff_eq_zero_of_lt_wei
ghtedOrder {d : σ ->₀ Nat} (h : (weight w d) < f.weightedOrder w) : coeff d f = 
0
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
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n

--- 原说明 ---
The `weightedOrder` of the product of two formal power series
is at least the sum of their orders.
-/
theorem le_weightedOrder_mul :
    f.weightedOrder w + g.weightedOrder w ≤ weightedOrder w (f * g) := by
  classical
  apply le_weightedOrder
  intro d hd
  rw [coeff_mul, Finset.sum_eq_zero]
  rintro ⟨i, j⟩ hij
  by_cases! hi : weight w i < f.weightedOrder w
  · rw [coeff_eq_zero_of_lt_weightedOrder w hi, zero_mul]
  · by_cases! hj : weight w j < g.weightedOrder w
    · rw [coeff_eq_zero_of_lt_weightedOrder w hj, mul_zero]
    · simp only [Finset.mem_antidiagonal] at hij
      exfalso
      apply ne_of_lt (lt_of_lt_of_le hd <| add_le_add hi hj)
      rw [← hij, map_add, Nat.cast_add]
/-
**MvPowerSeries.le_weightedOrder_pow** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：le_weightedOrder_pow (n : Nat) : n • f.weightedOrder w <= (f ^ n).weighted
Order w
参数：n : Nat。
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
· 使用定理 `succ_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (n : ℕ), (n + 
1) • a = n • a + a
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
· 使用定理 `MvPowerSeries.le_weightedOrder_mul`：le_weightedOrder_mul : f.weightedOrd
er w + g.weightedOrder w <= weightedOrder w (f * g)
-/
theorem le_weightedOrder_pow (n : ℕ) : n • f.weightedOrder w ≤ (f ^ n).weightedOrder w := by
  induction n with
  | zero => simp
  | succ n hn => grw [succ_nsmul, pow_succ, hn, le_weightedOrder_mul]
/-
**MvPowerSeries.le_weightedOrder_prod** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：le_weightedOrder_prod {R : Type*} [CommSemiring R] {ι : Type*} (w : σ -> N
at) (f : ι -> MvPowerSeries σ R) (s : Finset ι) : ∑ i in s, (f i).weightedOrder 
w <= (∏ i in s, f i).weightedOrder w
参数：w : σ -> Nat；f : ι -> MvPowerSeries σ R；s : Finset ι。
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
· 使用定理 `MvPowerSeries.le_weightedOrder_mul`：le_weightedOrder_mul : f.weightedOrd
er w + g.weightedOrder w <= weightedOrder w (f * g)
-/
theorem le_weightedOrder_prod {R : Type*} [CommSemiring R] {ι : Type*} (w : σ → ℕ)
    (f : ι → MvPowerSeries σ R) (s : Finset ι) :
    ∑ i ∈ s, (f i).weightedOrder w ≤ (∏ i ∈ s, f i).weightedOrder w := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => grw [Finset.sum_cons ha, Finset.prod_cons ha, ih, le_weightedOrder_mul]

alias weightedOrder_mul_ge := le_weightedOrder_mul
/-
**MvPowerSeries.le_weightedOrder_smul** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：le_weightedOrder_smul {a : R} : f.weightedOrder w <= (a • f).weightedOrder
 w
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.le_weightedOrder`：le_weightedOrder {n : Nat∞} (h : forall 
d : σ ->₀ Nat, weight w d < n -> coeff d f = 0) : n <= f.weightedOrder w
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
· 使用定理 `MvPowerSeries.coeff_eq_zero_of_lt_weightedOrder`：coeff_eq_zero_of_lt_wei
ghtedOrder {d : σ ->₀ Nat} (h : (weight w d) < f.weightedOrder w) : coeff d f = 
0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem le_weightedOrder_smul {a : R} :
    f.weightedOrder w ≤ (a • f).weightedOrder w :=
  le_weightedOrder _ fun i hi => by simp [coeff_eq_zero_of_lt_weightedOrder _ hi]

section

variable {S : Type*} [Semiring S]

/-
**MvPowerSeries.le_weightedOrder_map** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：le_weightedOrder_map (φ : R ->+* S) : f.weightedOrder w <= (f.map φ).weigh
tedOrder w
参数：φ : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.le_weightedOrder`：le_weightedOrder {n : Nat∞} (h : forall 
d : σ ->₀ Nat, weight w d < n -> coeff d f = 0) : n <= f.weightedOrder w
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_eq_zero_of_lt_weightedOrder`：coeff_eq_zero_of_lt_wei
ghtedOrder {d : σ ->₀ Nat} (h : (weight w d) < f.weightedOrder w) : coeff d f = 
0
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
theorem le_weightedOrder_map (φ : R →+* S) :
    f.weightedOrder w ≤ (f.map φ).weightedOrder w :=
  le_weightedOrder w fun i hi => by simp [coeff_eq_zero_of_lt_weightedOrder _ hi]

end

section Ring

variable {R : Type*} [Ring R] {f g : MvPowerSeries σ R}

/-
**MvPowerSeries.coeff_mul_left_one_sub_of_lt_weightedOrder** 是 Mathlib 中的一个定理，位于
命名空间 `MvPowerSeries`。
形式化陈述：coeff_mul_left_one_sub_of_lt_weightedOrder {d : σ ->₀ Nat} (h : (weight w 
d) < g.weightedOrder w) : coeff d (f * (1 - g)) = coeff d f
参数：h : (weight w d) < g.weightedOrder w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `MvPowerSeries.coeff_eq_zero_of_lt_weightedOrder`：coeff_eq_zero_of_lt_wei
ghtedOrder {d : σ ->₀ Nat} (h : (weight w d) < f.weightedOrder w) : coeff d f = 
0
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `le_add_self`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ b + a
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `MvPowerSeries.le_weightedOrder_mul`：le_weightedOrder_mul : f.weightedOrd
er w + g.weightedOrder w <= weightedOrder w (f * g)
-/
theorem coeff_mul_left_one_sub_of_lt_weightedOrder
    {d : σ →₀ ℕ} (h : (weight w d) < g.weightedOrder w) :
    coeff d (f * (1 - g)) = coeff d f := by
  simp only [mul_sub, mul_one, map_sub, sub_eq_self]
  apply coeff_eq_zero_of_lt_weightedOrder w
  exact lt_of_lt_of_le (lt_of_lt_of_le h le_add_self) (le_weightedOrder_mul w)
/-
**MvPowerSeries.coeff_mul_right_one_sub_of_lt_weightedOrder** 是 Mathlib 中的一个定理，位
于命名空间 `MvPowerSeries`。
形式化陈述：coeff_mul_right_one_sub_of_lt_weightedOrder {d : σ ->₀ Nat} (h : (weight w
 d) < g.weightedOrder w) : coeff d ((1 - g) * f) = coeff d f
参数：h : (weight w d) < g.weightedOrder w。
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
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `MvPowerSeries.coeff_eq_zero_of_lt_weightedOrder`：coeff_eq_zero_of_lt_wei
ghtedOrder {d : σ ->₀ Nat} (h : (weight w d) < f.weightedOrder w) : coeff d f = 
0
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `MvPowerSeries.le_weightedOrder_mul`：le_weightedOrder_mul : f.weightedOrd
er w + g.weightedOrder w <= weightedOrder w (f * g)
-/
theorem coeff_mul_right_one_sub_of_lt_weightedOrder
    {d : σ →₀ ℕ} (h : (weight w d) < g.weightedOrder w) :
    coeff d ((1 - g) * f) = coeff d f := by
  simp only [sub_mul, one_mul, map_sub, sub_eq_self]
  apply coeff_eq_zero_of_lt_weightedOrder w
  apply lt_of_lt_of_le (lt_of_lt_of_le h le_self_add) (le_weightedOrder_mul w)
/-
**MvPowerSeries.coeff_mul_prod_one_sub_of_lt_weightedOrder** 是 Mathlib 中的一个定理，位于
命名空间 `MvPowerSeries`。
形式化陈述：coeff_mul_prod_one_sub_of_lt_weightedOrder {R ι : Type*} [CommRing R] (d :
 σ ->₀ Nat) (s : Finset ι) (f : MvPowerSeries σ R) (g : ι -> MvPowerSeries σ R) 
(h : forall i in s, (weight w d) < weightedOrder w (g i)) : coeff d (f * ∏ i in 
s, (1 - g i)) = coeff d f
参数：d : σ ->₀ Nat；s : Finset ι；f : MvPowerSeries σ R；g : ι -> MvPowerSeries σ R；h
 : forall i in s, (weight w d) < weightedOrder w (g i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `MvPowerSeries.coeff_mul_left_one_sub_of_lt_weightedOrder`：coeff_mul_left
_one_sub_of_lt_weightedOrder {d : σ ->₀ Nat} (h : (weight w d) < g.weightedOrder
 w) : coeff d (f * (1 - g)) = coeff d f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem coeff_mul_prod_one_sub_of_lt_weightedOrder {R ι : Type*} [CommRing R] (d : σ →₀ ℕ)
    (s : Finset ι) (f : MvPowerSeries σ R) (g : ι → MvPowerSeries σ R)
    (h : ∀ i ∈ s, (weight w d) < weightedOrder w (g i)) :
    coeff d (f * ∏ i ∈ s, (1 - g i)) = coeff d f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, mul_one]
  | insert a s ha ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp] at h
    rw [Finset.prod_insert ha, ← mul_assoc, mul_right_comm,
      coeff_mul_left_one_sub_of_lt_weightedOrder w h.1, ih h.2]

@[simp]
/-
**MvPowerSeries.weightedOrder_neg** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：weightedOrder_neg (f : MvPowerSeries σ R) : (-f).weightedOrder w = f.weigh
tedOrder w
参数：f : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `MvPowerSeries.weightedOrder_zero`：∀ {σ : Type u_1} {R : Type u_2} [inst 
: Semiring R] (w : σ → ℕ), MvPowerSeries.weightedOrder w 0 = ⊤
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.weightedOrder_add_of_weightedOrder_ne`：weightedOrder_add_o
f_weightedOrder_ne (h : f.weightedOrder w != g.weightedOrder w) : weightedOrder 
w (f + g) = weightedOrder w f ⊓ weightedO…
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
theorem weightedOrder_neg (f : MvPowerSeries σ R) : (-f).weightedOrder w = f.weightedOrder w := by
  by_contra! h
  have : f = 0 := by simpa using (weightedOrder_add_of_weightedOrder_ne w h).symm
  simp [this] at h

@[simp]
/-
**MvPowerSeries.weightedOrder_toSubring** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries
`。
形式化陈述：weightedOrder_toSubring (p : MvPowerSeries σ R) (T : Subring R) (hp : fora
ll n, p.coeff n in T) : (p.toSubring T hp).weightedOrder w = p.weightedOrder w
参数：p : MvPowerSeries σ R；T : Subring R；hp : forall n, p.coeff n in T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_le_of_ge`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `MvPowerSeries.le_weightedOrder`：le_weightedOrder {n : Nat∞} (h : forall 
d : σ ->₀ Nat, weight w d < n -> coeff d f = 0) : n <= f.weightedOrder w
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.coeff_toSubring`：coeff_toSubring {n : σ ->₀ Nat} : (p.toSu
bring T hp).coeff n = p.coeff n
· 使用定理 `MvPowerSeries.coeff_eq_zero_of_lt_weightedOrder`：coeff_eq_zero_of_lt_wei
ghtedOrder {d : σ ->₀ Nat} (h : (weight w d) < f.weightedOrder w) : coeff d f = 
0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
-/
theorem weightedOrder_toSubring (p : MvPowerSeries σ R) (T : Subring R) (hp : ∀ n, p.coeff n ∈ T) :
    (p.toSubring T hp).weightedOrder w = p.weightedOrder w := by
  refine eq_of_le_of_ge ?_ ?_
  · refine le_weightedOrder w fun d hd => by
      simp [coeff_eq_zero_of_lt_weightedOrder w hd, ← p.coeff_toSubring T hp]
  · refine le_weightedOrder w fun d hd => by
      exact_mod_cast (coeff_toSubring p T hp) ▸ (coeff_eq_zero_of_lt_weightedOrder w hd)

end Ring

end WeightedOrder

section Order

variable {f g : MvPowerSeries σ R}

@[deprecated (since := "2026-01-06")]
alias eq_zero_iff_forall_coeff_eq_zero_and := eq_zero_iff_forall_coeff_zero

/-
**MvPowerSeries.ne_zero_iff_exists_coeff_ne_zero_and_degree** 是 Mathlib 中的一个定理，位
于命名空间 `MvPowerSeries`。
形式化陈述：ne_zero_iff_exists_coeff_ne_zero_and_degree : f != 0 ↔ (exists n : Nat, ex
ists d : σ ->₀ Nat, coeff d f != 0 ∧ degree d = n)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.degree_eq_weight_one`：degree_eq_weight_one {R : Type*} [Semiring
 R] : degree (R
· 使用定理 `MvPowerSeries.ne_zero_iff_exists_coeff_ne_zero_and_weight`：ne_zero_iff_e
xists_coeff_ne_zero_and_weight : f != 0 ↔ (exists n : Nat, exists d : σ ->₀ Nat,
 coeff d f != 0 ∧ weight w d = n)
-/
theorem ne_zero_iff_exists_coeff_ne_zero_and_degree :
    f ≠ 0 ↔ (∃ n : ℕ, ∃ d : σ →₀ ℕ, coeff d f ≠ 0 ∧ degree d = n) := by
  simp_rw [degree_eq_weight_one]
  exact ne_zero_iff_exists_coeff_ne_zero_and_weight (fun _ => 1)

/-- The order of a multivariate power series is the the minimum total degree over all
exponents `d` with nonzero coefficient `coeff d f`. -/
/-
**MvPowerSeries.order** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
形式化陈述：order (f : MvPowerSeries σ R) : Nat∞
参数：f : MvPowerSeries σ R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The order of a multivariate power series is the the minimum total degree over al
l
exponents `d` with nonzero coefficient `coeff d f`.
-/
def order (f : MvPowerSeries σ R) : ℕ∞ := weightedOrder (fun _ => 1) f

@[simp]
/-
**MvPowerSeries.order_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：order_zero : (0 : MvPowerSeries σ R).order = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.weightedOrder_zero`：∀ {σ : Type u_1} {R : Type u_2} [inst 
: Semiring R] (w : σ → ℕ), MvPowerSeries.weightedOrder w 0 = ⊤
-/
theorem order_zero : (0 : MvPowerSeries σ R).order = ⊤ :=
  weightedOrder_zero _
/-
**MvPowerSeries.ne_zero_iff_order_finite** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSerie
s`。
形式化陈述：ne_zero_iff_order_finite : f != 0 ↔ f.order.toNat = f.order
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.ne_zero_iff_weightedOrder_finite`：ne_zero_iff_weightedOrde
r_finite : f != 0 ↔ (f.weightedOrder w).toNat = f.weightedOrder w
-/
theorem ne_zero_iff_order_finite : f ≠ 0 ↔ f.order.toNat = f.order :=
  ne_zero_iff_weightedOrder_finite 1

/-- The `0` power series is the unique power series with infinite order. -/
/-
**MvPowerSeries.order_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_2} [inst : Semiring R] {f : MvPowerSeries σ R
}, f.order = ⊤ ↔ f = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.weightedOrder_eq_top_iff`：weightedOrder_eq_top_iff : f.wei
ghtedOrder w = ⊤ ↔ f = 0

--- 原说明 ---
The `0` power series is the unique power series with infinite order.
-/
@[simp] theorem order_eq_top_iff : f.order = ⊤ ↔ f = 0 :=
  weightedOrder_eq_top_iff _

/-- If the order of a formal power series `f` is finite,
then some coefficient of degree the order of `f` is nonzero. -/
/-
**MvPowerSeries.exists_coeff_ne_zero_and_order** 是 Mathlib 中的一个定理，位于命名空间 `MvPowe
rSeries`。
形式化陈述：exists_coeff_ne_zero_and_order (h : f.order.toNat = f.order) : exists d : 
σ ->₀ Nat, coeff d f != 0 ∧ degree d = f.order
参数：h : f.order.toNat = f.order。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.degree_eq_weight_one`：degree_eq_weight_one {R : Type*} [Semiring
 R] : degree (R
· 使用定理 `MvPowerSeries.exists_coeff_ne_zero_and_weightedOrder`：exists_coeff_ne_ze
ro_and_weightedOrder (h : (toNat (f.weightedOrder w) : Nat∞) = f.weightedOrder w
) : exists d, coeff d f != 0 ∧ weight w d …

--- 原说明 ---
If the order of a formal power series `f` is finite,
then some coefficient of degree the order of `f` is nonzero.
-/
theorem exists_coeff_ne_zero_and_order (h : f.order.toNat = f.order) :
    ∃ d : σ →₀ ℕ, coeff d f ≠ 0 ∧ degree d = f.order := by
  simp_rw [degree_eq_weight_one]
  exact exists_coeff_ne_zero_and_weightedOrder _ h

/-- If the `d`th coefficient of a formal power series is nonzero,
then the order of the power series is less than or equal to `degree d`. -/
/-
**MvPowerSeries.order_le** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：order_le {d : σ ->₀ Nat} (h : coeff d f != 0) : f.order <= degree d
参数：h : coeff d f != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.degree_eq_weight_one`：degree_eq_weight_one {R : Type*} [Semiring
 R] : degree (R
· 使用定理 `MvPowerSeries.weightedOrder_le`：weightedOrder_le {d : σ ->₀ Nat} (h : co
eff d f != 0) : f.weightedOrder w <= weight w d

--- 原说明 ---
If the `d`th coefficient of a formal power series is nonzero,
then the order of the power series is less than or equal to `degree d`.
-/
theorem order_le {d : σ →₀ ℕ} (h : coeff d f ≠ 0) : f.order ≤ degree d := by
  rw [degree_eq_weight_one]
  exact weightedOrder_le _ h

/-- The `n`th coefficient of a formal power series is `0` if `n` is strictly
smaller than the order of the power series. -/
/-
**MvPowerSeries.coeff_of_lt_order** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_of_lt_order {d : σ ->₀ Nat} (h : degree d < f.order) : coeff d f = 0
参数：h : degree d < f.order。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.coeff_eq_zero_of_lt_weightedOrder`：coeff_eq_zero_of_lt_wei
ghtedOrder {d : σ ->₀ Nat} (h : (weight w d) < f.weightedOrder w) : coeff d f = 
0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.degree_eq_weight_one`：degree_eq_weight_one {R : Type*} [Semiring
 R] : degree (R

--- 原说明 ---
The `n`th coefficient of a formal power series is `0` if `n` is strictly
smaller than the order of the power series.
-/
theorem coeff_of_lt_order {d : σ →₀ ℕ} (h : degree d < f.order) :
    coeff d f = 0 := by
  rw [degree_eq_weight_one] at h
  exact coeff_eq_zero_of_lt_weightedOrder _ h

/-- The order of a formal power series is at least `n` if
the `d`th coefficient is `0` for all `d` such that `degree d < n`. -/
/-
**MvPowerSeries.nat_le_order** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：nat_le_order {n : Nat} (h : forall d, degree d < n -> coeff d f = 0) : n <
= f.order
参数：h : forall d, degree d < n -> coeff d f = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.nat_le_weightedOrder`：nat_le_weightedOrder {n : Nat} (h : 
forall d, weight w d < n -> coeff d f = 0) : n <= f.weightedOrder w
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.degree_eq_weight_one`：degree_eq_weight_one {R : Type*} [Semiring
 R] : degree (R

--- 原说明 ---
The order of a formal power series is at least `n` if
the `d`th coefficient is `0` for all `d` such that `degree d < n`.
-/
theorem nat_le_order {n : ℕ} (h : ∀ d, degree d < n → coeff d f = 0) :
    n ≤ f.order := by
  simp_rw [degree_eq_weight_one] at h
  exact nat_le_weightedOrder _ h

/-- The order of a formal power series is at least `n` if
the `d`th coefficient is `0` for all `d` such that `degree d < n`. -/
/-
**MvPowerSeries.le_order** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：le_order {n : Nat∞} (h : forall d : σ ->₀ Nat, degree d < n -> coeff d f =
 0) : n <= f.order
参数：h : forall d : σ ->₀ Nat, degree d < n -> coeff d f = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.le_weightedOrder`：le_weightedOrder {n : Nat∞} (h : forall 
d : σ ->₀ Nat, weight w d < n -> coeff d f = 0) : n <= f.weightedOrder w
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.degree_eq_weight_one`：degree_eq_weight_one {R : Type*} [Semiring
 R] : degree (R

--- 原说明 ---
The order of a formal power series is at least `n` if
the `d`th coefficient is `0` for all `d` such that `degree d < n`.
-/
theorem le_order {n : ℕ∞} (h : ∀ d : σ →₀ ℕ, degree d < n → coeff d f = 0) :
    n ≤ f.order := by
  simp_rw [degree_eq_weight_one] at h
  exact le_weightedOrder _ h

/-- The order of a formal power series is exactly `n` some coefficient
of degree `n` is nonzero,
and the `d`th coefficient is `0` for all `d` such that `degree d < n`. -/
/-
**MvPowerSeries.order_eq_nat** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：order_eq_nat {n : Nat} : f.order = n ↔ (exists d, coeff d f != 0 ∧ degree 
d = n) ∧ forall d, degree d < n -> coeff d f = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.degree_eq_weight_one`：degree_eq_weight_one {R : Type*} [Semiring
 R] : degree (R
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `MvPowerSeries.weightedOrder_eq_nat`：weightedOrder_eq_nat {n : Nat} : f.w
eightedOrder w = n ↔ (exists d, coeff d f != 0 ∧ weight w d = n) ∧ forall d, wei
ght w d < n -> coeff d f…

--- 原说明 ---
The order of a formal power series is exactly `n` some coefficient
of degree `n` is nonzero,
and the `d`th coefficient is `0` for all `d` such that `degree d < n`.
-/
theorem order_eq_nat {n : ℕ} :
    f.order = n ↔
      (∃ d, coeff d f ≠ 0 ∧ degree d = n) ∧ ∀ d, degree d < n → coeff d f = 0 := by
  simp_rw [degree_eq_weight_one]
  exact weightedOrder_eq_nat _

/-- The order of the monomial `a*X^d` is infinite if `a = 0` and `degree d` otherwise. -/
/-
**MvPowerSeries.order_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：order_monomial {d : σ ->₀ Nat} {a : R} [Decidable (a = 0)] : order (monomi
al d a) = if a = 0 then (⊤ : Nat∞) else ↑(degree d)
参数：a = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.degree_eq_weight_one`：degree_eq_weight_one {R : Type*} [Semiring
 R] : degree (R
· 使用定理 `MvPowerSeries.weightedOrder_monomial`：weightedOrder_monomial {d : σ ->₀ 
Nat} {a : R} [Decidable (a = 0)] : weightedOrder w (monomial d a) = if a = 0 the
n (⊤ : Nat∞) else weight w…

--- 原说明 ---
The order of the monomial `a*X^d` is infinite if `a = 0` and `degree d` otherwis
e.
-/
theorem order_monomial {d : σ →₀ ℕ} {a : R} [Decidable (a = 0)] :
    order (monomial d a) = if a = 0 then (⊤ : ℕ∞) else ↑(degree d) := by
  rw [degree_eq_weight_one]
  exact weightedOrder_monomial _

/-- The order of the monomial `a*X^n` is `n` if `a ≠ 0`. -/
/-
**MvPowerSeries.order_monomial_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeri
es`。
形式化陈述：order_monomial_of_ne_zero {d : σ ->₀ Nat} {a : R} (h : a != 0) : order (mo
nomial d a) = degree d
参数：h : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.degree_eq_weight_one`：degree_eq_weight_one {R : Type*} [Semiring
 R] : degree (R
· 使用定理 `MvPowerSeries.weightedOrder_monomial_of_ne_zero`：weightedOrder_monomial_
of_ne_zero {d : σ ->₀ Nat} {a : R} (h : a != 0) : weightedOrder w (monomial d a)
 = weight w d

--- 原说明 ---
The order of the monomial `a*X^n` is `n` if `a ≠ 0`.
-/
theorem order_monomial_of_ne_zero {d : σ →₀ ℕ} {a : R} (h : a ≠ 0) :
    order (monomial d a) = degree d := by
  rw [degree_eq_weight_one]
  exact weightedOrder_monomial_of_ne_zero _ h

/-- The order of the sum of two formal power series
is at least the minimum of their orders. -/
/-
**MvPowerSeries.min_order_le_add** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：min_order_le_add : min f.order g.order <= (f + g).order
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.min_weightedOrder_le_add`：min_weightedOrder_le_add : min (
f.weightedOrder w) (g.weightedOrder w) <= (f + g).weightedOrder w

--- 原说明 ---
The order of the sum of two formal power series
is at least the minimum of their orders.
-/
theorem min_order_le_add : min f.order g.order ≤ (f + g).order :=
  min_weightedOrder_le_add _

/-- The order of the sum of two formal power series
is the minimum of their orders if their orders differ. -/
/-
**MvPowerSeries.order_add_of_order_ne** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：order_add_of_order_ne (h : f.order != g.order) : order (f + g) = order f ⊓
 order g
参数：h : f.order != g.order。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.weightedOrder_add_of_weightedOrder_ne`：weightedOrder_add_o
f_weightedOrder_ne (h : f.weightedOrder w != g.weightedOrder w) : weightedOrder 
w (f + g) = weightedOrder w f ⊓ weightedO…

--- 原说明 ---
The order of the sum of two formal power series
is the minimum of their orders if their orders differ.
-/
theorem order_add_of_order_ne (h : f.order ≠ g.order) :
    order (f + g) = order f ⊓ order g :=
  weightedOrder_add_of_weightedOrder_ne _ h

/-- The order of the product of two formal power series
is at least the sum of their orders. -/
/-
**MvPowerSeries.le_order_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：le_order_mul : f.order + g.order <= order (f * g)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.le_weightedOrder_mul`：le_weightedOrder_mul : f.weightedOrd
er w + g.weightedOrder w <= weightedOrder w (f * g)

--- 原说明 ---
The order of the product of two formal power series
is at least the sum of their orders.
-/
theorem le_order_mul : f.order + g.order ≤ order (f * g) :=
  le_weightedOrder_mul _

alias order_mul_ge := le_order_mul
/-
**MvPowerSeries.le_order_pow** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：le_order_pow (n : Nat) : n • f.order <= (f ^ n).order
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.le_weightedOrder_pow`：le_weightedOrder_pow (n : Nat) : n •
 f.weightedOrder w <= (f ^ n).weightedOrder w
-/
theorem le_order_pow (n : ℕ) : n • f.order ≤ (f ^ n).order :=
  le_weightedOrder_pow _ n
/-
**MvPowerSeries.le_order_prod** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：le_order_prod {R : Type*} [CommSemiring R] {ι : Type*} (f : ι -> MvPowerSe
ries σ R) (s : Finset ι) : ∑ i in s, (f i).order <= (∏ i in s, f i).order
参数：f : ι -> MvPowerSeries σ R；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.le_weightedOrder_prod`：le_weightedOrder_prod {R : Type*} [
CommSemiring R] {ι : Type*} (w : σ -> Nat) (f : ι -> MvPowerSeries σ R) (s : Fin
set ι) : ∑ i in s, (f i).…
-/
theorem le_order_prod {R : Type*} [CommSemiring R] {ι : Type*}
    (f : ι → MvPowerSeries σ R) (s : Finset ι) : ∑ i ∈ s, (f i).order ≤ (∏ i ∈ s, f i).order :=
  le_weightedOrder_prod _ _ _
/-
**MvPowerSeries.one_le_order_iff_constCoeff_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `M
vPowerSeries`。
形式化陈述：one_le_order_iff_constCoeff_eq_zero : 1 <= f.order ↔ f.constantCoeff = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.coeff_of_lt_order`：coeff_of_lt_order {d : σ ->₀ Nat} (h : 
degree d < f.order) : coeff d f = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Order.one_le_iff_pos`：one_le_iff_pos [AddMonoidWithOne α] [ZeroLEOneClas
s α] [NeZero (1 : α)] [SuccAddOrder α] : 1 <= x ↔ 0 < x
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `MvPowerSeries.le_order`：le_order {n : Nat∞} (h : forall d : σ ->₀ Nat, d
egree d < n -> coeff d f = 0) : n <= f.order
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Finsupp.degree_eq_zero_iff`：degree_eq_zero_iff {R : Type*} [AddCommMonoi
d R] [PartialOrder R] [CanonicallyOrderedAdd R] (d : σ ->₀ R) : degree d = 0 ↔ d
 = 0
· 使用定理 `Nat.cast_lt_one`：cast_lt_one : (n : α) < 1 ↔ n = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem one_le_order_iff_constCoeff_eq_zero :
    1 ≤ f.order ↔ f.constantCoeff = 0 := by
  constructor
  · intro h
    apply coeff_of_lt_order
    simpa using Order.one_le_iff_pos.mp h
  · intro h
    refine MvPowerSeries.le_order fun d hd ↦ ?_
    rw [Nat.cast_lt_one] at hd
    simp [(degree_eq_zero_iff d).mp hd, h]
/-
**MvPowerSeries.order_ne_zero_iff_constCoeff_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `
MvPowerSeries`。
形式化陈述：order_ne_zero_iff_constCoeff_eq_zero : f.order != 0 ↔ f.constantCoeff = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.one_le_iff_ne_zero`：one_le_iff_ne_zero [AddMonoidWithOne α] [NeZer
o (1 : α)] [SuccAddOrder α] [IsBotZeroClass α] : 1 <= x ↔ x != 0
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `MvPowerSeries.one_le_order_iff_constCoeff_eq_zero`：one_le_order_iff_cons
tCoeff_eq_zero : 1 <= f.order ↔ f.constantCoeff = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem order_ne_zero_iff_constCoeff_eq_zero :
    f.order ≠ 0 ↔ f.constantCoeff = 0 := by
  rw [← Order.one_le_iff_ne_zero, one_le_order_iff_constCoeff_eq_zero]
/-
**MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 
`MvPowerSeries`。
形式化陈述：le_order_pow_of_constantCoeff_eq_zero (n : Nat) (hf : f.constantCoeff = 0)
 : n <= (f ^ n).order
参数：n : Nat；hf : f.constantCoeff = 0。
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
· 使用定理 `MvPowerSeries.one_le_order_iff_constCoeff_eq_zero`：one_le_order_iff_cons
tCoeff_eq_zero : 1 <= f.order ↔ f.constantCoeff = 0
· 使用定理 `MvPowerSeries.le_order_pow`：le_order_pow (n : Nat) : n • f.order <= (f ^
 n).order
-/
theorem le_order_pow_of_constantCoeff_eq_zero (n : ℕ) (hf : f.constantCoeff = 0) :
    n ≤ (f ^ n).order := by
  refine .trans ?_ (le_order_pow n)
  simpa using le_mul_of_one_le_right' (one_le_order_iff_constCoeff_eq_zero.mpr hf)
/-
**MvPowerSeries.le_order_smul** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：le_order_smul {a : R} : f.order <= (a • f).order
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.le_weightedOrder_smul`：le_weightedOrder_smul {a : R} : f.w
eightedOrder w <= (a • f).weightedOrder w
-/
theorem le_order_smul {a : R} : f.order ≤ (a • f).order := le_weightedOrder_smul _

section

variable {S : Type*} [Semiring S]

/-
**MvPowerSeries.le_order_map** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：le_order_map (f : R ->+* S) {φ : MvPowerSeries σ R} : φ.order <= (φ.map f)
.order
参数：f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.le_weightedOrder_map`：le_weightedOrder_map (φ : R ->+* S) 
: f.weightedOrder w <= (f.map φ).weightedOrder w
-/
theorem le_order_map (f : R →+* S) {φ : MvPowerSeries σ R} : φ.order ≤ (φ.map f).order :=
  le_weightedOrder_map _ _

end

section Ring

variable {R : Type*} [Ring R] {f g : MvPowerSeries σ R}

/-
**MvPowerSeries.coeff_mul_left_one_sub_of_lt_order** 是 Mathlib 中的一个定理，位于命名空间 `Mv
PowerSeries`。
形式化陈述：coeff_mul_left_one_sub_of_lt_order (d : σ ->₀ Nat) (h : degree d < g.order
) : coeff d (f * (1 - g)) = coeff d f
参数：d : σ ->₀ Nat；h : degree d < g.order。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.coeff_mul_left_one_sub_of_lt_weightedOrder`：coeff_mul_left
_one_sub_of_lt_weightedOrder {d : σ ->₀ Nat} (h : (weight w d) < g.weightedOrder
 w) : coeff d (f * (1 - g)) = coeff d f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.degree_eq_weight_one`：degree_eq_weight_one {R : Type*} [Semiring
 R] : degree (R
-/
theorem coeff_mul_left_one_sub_of_lt_order (d : σ →₀ ℕ) (h : degree d < g.order) :
    coeff d (f * (1 - g)) = coeff d f := by
  rw [degree_eq_weight_one] at h
  exact coeff_mul_left_one_sub_of_lt_weightedOrder _ h
/-
**MvPowerSeries.coeff_mul_right_one_sub_of_lt_order** 是 Mathlib 中的一个定理，位于命名空间 `M
vPowerSeries`。
形式化陈述：coeff_mul_right_one_sub_of_lt_order (d : σ ->₀ Nat) (h : degree d < g.orde
r) : coeff d ((1 - g) * f) = coeff d f
参数：d : σ ->₀ Nat；h : degree d < g.order。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.coeff_mul_right_one_sub_of_lt_weightedOrder`：coeff_mul_rig
ht_one_sub_of_lt_weightedOrder {d : σ ->₀ Nat} (h : (weight w d) < g.weightedOrd
er w) : coeff d ((1 - g) * f) = coeff d f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.degree_eq_weight_one`：degree_eq_weight_one {R : Type*} [Semiring
 R] : degree (R
-/
theorem coeff_mul_right_one_sub_of_lt_order (d : σ →₀ ℕ) (h : degree d < g.order) :
    coeff d ((1 - g) * f) = coeff d f := by
  rw [degree_eq_weight_one] at h
  exact coeff_mul_right_one_sub_of_lt_weightedOrder _ h
/-
**MvPowerSeries.coeff_mul_prod_one_sub_of_lt_order** 是 Mathlib 中的一个定理，位于命名空间 `Mv
PowerSeries`。
形式化陈述：coeff_mul_prod_one_sub_of_lt_order {R ι : Type*} [CommRing R] (d : σ ->₀ N
at) (s : Finset ι) (f : MvPowerSeries σ R) (g : ι -> MvPowerSeries σ R) : (foral
l i in s, degree d < order (g i)) -> coeff d (f * ∏ i in s, (1 - g i)) = coeff d
 f
参数：d : σ ->₀ Nat；s : Finset ι；f : MvPowerSeries σ R；g : ι -> MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.degree_eq_weight_one`：degree_eq_weight_one {R : Type*} [Semiring
 R] : degree (R
· 使用定理 `MvPowerSeries.coeff_mul_prod_one_sub_of_lt_weightedOrder`：coeff_mul_prod
_one_sub_of_lt_weightedOrder {R ι : Type*} [CommRing R] (d : σ ->₀ Nat) (s : Fin
set ι) (f : MvPowerSeries σ R) (g : ι -> MvPow…
-/
theorem coeff_mul_prod_one_sub_of_lt_order {R ι : Type*} [CommRing R] (d : σ →₀ ℕ) (s : Finset ι)
    (f : MvPowerSeries σ R) (g : ι → MvPowerSeries σ R) :
    (∀ i ∈ s, degree d < order (g i)) → coeff d (f * ∏ i ∈ s, (1 - g i)) = coeff d f := by
  rw [degree_eq_weight_one]
  exact coeff_mul_prod_one_sub_of_lt_weightedOrder _ d s f g

@[simp]
/-
**MvPowerSeries.order_neg** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：order_neg (f : MvPowerSeries σ R) : (-f).order = f.order
参数：f : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.weightedOrder_neg`：weightedOrder_neg (f : MvPowerSeries σ 
R) : (-f).weightedOrder w = f.weightedOrder w
-/
theorem order_neg (f : MvPowerSeries σ R) : (-f).order = f.order := weightedOrder_neg _ f

@[simp]
/-
**MvPowerSeries.order_toSubring** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：order_toSubring (p : MvPowerSeries σ R) (T : Subring R) (hp : forall n, p.
coeff n in T) : (p.toSubring T hp).order = p.order
参数：p : MvPowerSeries σ R；T : Subring R；hp : forall n, p.coeff n in T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_le_of_ge`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `MvPowerSeries.le_order`：le_order {n : Nat∞} (h : forall d : σ ->₀ Nat, d
egree d < n -> coeff d f = 0) : n <= f.order
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.coeff_toSubring`：coeff_toSubring {n : σ ->₀ Nat} : (p.toSu
bring T hp).coeff n = p.coeff n
· 使用定理 `MvPowerSeries.coeff_of_lt_order`：coeff_of_lt_order {d : σ ->₀ Nat} (h : 
degree d < f.order) : coeff d f = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
-/
theorem order_toSubring (p : MvPowerSeries σ R) (T : Subring R) (hp : ∀ n, p.coeff n ∈ T) :
    (p.toSubring T hp).order = p.order := by
  refine eq_of_le_of_ge ?_ ?_
  · exact le_order fun d hd => by simp [coeff_of_lt_order hd, ← p.coeff_toSubring T hp]
  · exact le_order fun d hd => by exact_mod_cast (coeff_toSubring p T hp) ▸ (coeff_of_lt_order hd)

end Ring

end Order

section HomogeneousComponent

variable (w : σ → ℕ)

/-- Weighted homogeneous power series -/
/-
**MvPowerSeries.IsWeightedHomogeneous** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
形式化陈述：IsWeightedHomogeneous (f : MvPowerSeries σ R) (p : Nat) : Prop
参数：f : MvPowerSeries σ R；p : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Weighted homogeneous power series
-/
def IsWeightedHomogeneous (f : MvPowerSeries σ R) (p : ℕ) : Prop :=
  ∀ {d : σ →₀ ℕ}, f.coeff d ≠ 0 → weight w d = p

variable {w} in
/-
**MvPowerSeries.IsWeightedHomogeneous.coeff_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `M
vPowerSeries.IsWeightedHomogeneous`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_2} [inst : Semiring R] {w : σ → ℕ} {f : MvPow
erSeries σ R} {p : ℕ},   MvPowerSeries.IsWeightedHomogeneous w f p → ∀ {d : σ →₀
 ℕ}, (Finsupp.weight w) d ≠ p → (MvPowerSeries.coeff d) f = 0
参数：Finsupp.weight w；MvPowerSeries.coeff d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
-/
theorem IsWeightedHomogeneous.coeff_eq_zero {f : MvPowerSeries σ R} {p : ℕ}
    (hf : f.IsWeightedHomogeneous w p) {d : σ →₀ ℕ} (hd : weight w d ≠ p) :
    f.coeff d = 0 := by
  simpa [Classical.not_not] using mt (@hf d) hd

variable {w} in
/-
**MvPowerSeries.IsWeightedHomogeneous.add** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeri
es.IsWeightedHomogeneous`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_2} [inst : Semiring R] {w : σ → ℕ} {f g : MvP
owerSeries σ R} {p : ℕ},   MvPowerSeries.IsWeightedHomogeneous w f p →     MvPow
erSeries.IsWeightedHomogeneous w g p → MvPowerSeries.IsWeightedHomogeneous w (f 
+ g) p
参数：f + g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_imp_comm`：not_imp_comm : ¬a -> b ↔ ¬b -> a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `MvPowerSeries.IsWeightedHomogeneous.coeff_eq_zero`：∀ {σ : Type u_1} {R :
 Type u_2} [inst : Semiring R] {w : σ → ℕ} {f : MvPowerSeries σ R} {p : ℕ},   Mv
PowerSeries.IsWeightedHomogeneous w f p…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
protected theorem IsWeightedHomogeneous.add {f g : MvPowerSeries σ R} {p : ℕ}
    (hf : f.IsWeightedHomogeneous w p) (hg : g.IsWeightedHomogeneous w p) :
    (f + g).IsWeightedHomogeneous w p := fun {d} ↦ by
  rw [not_imp_comm]
  intro hd
  rw [map_add, hf.coeff_eq_zero hd, hg.coeff_eq_zero hd, add_zero]

variable {w} in
/-
**MvPowerSeries.IsWeightedHomogeneous.mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeri
es.IsWeightedHomogeneous`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_2} [inst : Semiring R] {w : σ → ℕ} {f g : MvP
owerSeries σ R} {p q : ℕ},   MvPowerSeries.IsWeightedHomogeneous w f p →     MvP
owerSeries.IsWeightedHomogeneous w g q → MvPowerSeries.IsWeightedHomogeneous w (
f * g) (p + q)
参数：f * g；p + q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_imp_comm`：not_imp_comm : ¬a -> b ↔ ¬b -> a
· 使用定理 `MvPowerSeries.coeff_mul`：coeff_mul [DecidableEq σ] : coeff n (φ * ψ) = ∑
 p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `Finset.HasAntidiagonal.mem_antidiagonal`：∀ {A : Type u_1} {inst : AddMon
oid A} [self : Finset.HasAntidiagonal A] {n : A} {a : A × A},   a ∈ Finset.HasAn
tidiagonal.antidiagonal n ↔ a…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `MvPowerSeries.IsWeightedHomogeneous.coeff_eq_zero`：∀ {σ : Type u_1} {R :
 Type u_2} [inst : Semiring R] {w : σ → ℕ} {f : MvPowerSeries σ R} {p : ℕ},   Mv
PowerSeries.IsWeightedHomogeneous w f p…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
protected theorem IsWeightedHomogeneous.mul {f g : MvPowerSeries σ R} {p q : ℕ}
    (hf : f.IsWeightedHomogeneous w p) (hg : g.IsWeightedHomogeneous w q) :
    (f * g).IsWeightedHomogeneous w (p + q) := fun {d} ↦ by
  classical
  rw [not_imp_comm]
  intro hd
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro x hx
  rw [Finset.mem_antidiagonal] at hx
  suffices weight w x.1 ≠ p ∨ weight w x.2 ≠ q by
    rcases this with hp | hq
    · rw [hf.coeff_eq_zero hp, zero_mul]
    · rw [hg.coeff_eq_zero hq, mul_zero]
  rw [← not_and_or]
  rintro ⟨hp, hq⟩
  apply hd
  rw [← hx, map_add, hp, hq]

set_option backward.isDefEq.respectTransparency false in
/-- The weighted homogeneous components of an `MvPowerSeries f`. -/
/-
**MvPowerSeries.weightedHomogeneousComponent** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerS
eries`。
形式化陈述：weightedHomogeneousComponent (p : Nat) : MvPowerSeries σ R ->ₗ[R] MvPowerS
eries σ R where toFun f d
参数：p : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The weighted homogeneous components of an `MvPowerSeries f`.
-/
def weightedHomogeneousComponent (p : ℕ) : MvPowerSeries σ R →ₗ[R] MvPowerSeries σ R where
  toFun f d := if weight w d = p then coeff d f else 0
  map_add' f g := by
    ext d
    simp only [map_add, coeff_apply]
    split_ifs with h
    · rfl
    · rw [add_zero]
  map_smul' a f := by
    ext d
    simp only [map_smul,
      smul_eq_mul, RingHom.id_apply, coeff_apply, mul_ite, mul_zero]
/-
**MvPowerSeries.coeff_weightedHomogeneousComponent** 是 Mathlib 中的一个定理，位于命名空间 `Mv
PowerSeries`。
形式化陈述：coeff_weightedHomogeneousComponent (p : Nat) (d : σ ->₀ Nat) (f : MvPowerS
eries σ R) : coeff d (weightedHomogeneousComponent w p f) = if weight w d = p th
en coeff d f else 0
参数：p : Nat；d : σ ->₀ Nat；f : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_weightedHomogeneousComponent (p : ℕ) (d : σ →₀ ℕ) (f : MvPowerSeries σ R) :
    coeff d (weightedHomogeneousComponent w p f) =
      if weight w d = p then coeff d f else 0 :=
  rfl

variable {w} in
/-
**MvPowerSeries.weightedHomogeneousComponent_of_lt_weightedOrder_eq_zero** 是 Mat
hlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：weightedHomogeneousComponent_of_lt_weightedOrder_eq_zero {f : MvPowerSerie
s σ R} {p : Nat} (hf : p < f.weightedOrder w) : f.weightedHomogeneousComponent w
 p = 0
参数：hf : p < f.weightedOrder w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_weightedHomogeneousComponent`：coeff_weightedHomogene
ousComponent (p : Nat) (d : σ ->₀ Nat) (f : MvPowerSeries σ R) : coeff d (weight
edHomogeneousComponent w p f) = if wei…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `MvPowerSeries.coeff_zero`：coeff_zero (n : σ ->₀ Nat) : coeff n (0 : MvPo
werSeries σ R) = 0
· 使用定理 `MvPowerSeries.coeff_eq_zero_of_lt_weightedOrder`：coeff_eq_zero_of_lt_wei
ghtedOrder {d : σ ->₀ Nat} (h : (weight w d) < f.weightedOrder w) : coeff d f = 
0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
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
-/
theorem weightedHomogeneousComponent_of_lt_weightedOrder_eq_zero
    {f : MvPowerSeries σ R} {p : ℕ} (hf : p < f.weightedOrder w) :
    f.weightedHomogeneousComponent w p = 0 := by
  ext d
  rw [coeff_weightedHomogeneousComponent]
  split_ifs with hd
  · rw [coeff_zero]
    apply coeff_eq_zero_of_lt_weightedOrder w
    rw [hd]
    exact hf
  · rw [map_zero]

variable {w} in
/-
**MvPowerSeries.weightedHomogeneousComponent_of_weightedOrder** 是 Mathlib 中的一个定理
，位于命名空间 `MvPowerSeries`。
形式化陈述：weightedHomogeneousComponent_of_weightedOrder {f : MvPowerSeries σ R} {p :
 Nat} (hf : p = f.weightedOrder w) : f.weightedHomogeneousComponent w p != 0
参数：hf : p = f.weightedOrder w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.exists_coeff_ne_zero_and_weightedOrder`：exists_coeff_ne_ze
ro_and_weightedOrder (h : (toNat (f.weightedOrder w) : Nat∞) = f.weightedOrder w
) : exists d, coeff d f != 0 ∧ weight w d …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENat.toNat_natCast`：toNat_natCast (n : Nat) : toNat n = n
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `MvPowerSeries.ext_iff`：∀ {σ : Type u_1} {R : Type u_2} [inst : Semiring 
R] {φ ψ : MvPowerSeries σ R},   φ = ψ ↔ ∀ (n : σ →₀ ℕ), (MvPowerSeries.coeff n) 
φ = (MvPowe…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem weightedHomogeneousComponent_of_weightedOrder
    {f : MvPowerSeries σ R} {p : ℕ} (hf : p = f.weightedOrder w) :
    f.weightedHomogeneousComponent w p ≠ 0 := by
  intro hf'
  obtain ⟨d, hd⟩ := f.exists_coeff_ne_zero_and_weightedOrder w (by rw [← hf, toNat_natCast])
  simp only [ne_eq, ← hf, Nat.cast_inj] at hd
  apply hd.1
  rw [MvPowerSeries.ext_iff] at hf'
  specialize hf' d
  simp only [coeff_weightedHomogeneousComponent, coeff_zero, ite_eq_right_iff] at hf'
  exact hf' hd.2
/-
**MvPowerSeries.isWeightedHomogeneous_weightedHomogeneousComponent** 是 Mathlib 中
的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：isWeightedHomogeneous_weightedHomogeneousComponent (f : MvPowerSeries σ R)
 (p : Nat) : IsWeightedHomogeneous w (f.weightedHomogeneousComponent w p) p
参数：f : MvPowerSeries σ R；p : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_imp_comm`：not_imp_comm : ¬a -> b ↔ ¬b -> a
· 使用定理 `MvPowerSeries.coeff_weightedHomogeneousComponent`：coeff_weightedHomogene
ousComponent (p : Nat) (d : σ ->₀ Nat) (f : MvPowerSeries σ R) : coeff d (weight
edHomogeneousComponent w p f) = if wei…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem isWeightedHomogeneous_weightedHomogeneousComponent (f : MvPowerSeries σ R) (p : ℕ) :
    IsWeightedHomogeneous w (f.weightedHomogeneousComponent w p) p := fun {d} ↦ by
  rw [not_imp_comm]
  intro hd
  rw [coeff_weightedHomogeneousComponent, if_neg hd]

variable {w} in
/-
**MvPowerSeries.isWeightedHomogeneous_iff_eq_weightedHomogeneousComponent** 是 Ma
thlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：isWeightedHomogeneous_iff_eq_weightedHomogeneousComponent {f : MvPowerSeri
es σ R} {p : Nat} : IsWeightedHomogeneous w f p ↔ f = f.weightedHomogeneousCompo
nent w p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_weightedHomogeneousComponent`：coeff_weightedHomogene
ousComponent (p : Nat) (d : σ ->₀ Nat) (f : MvPowerSeries σ R) : coeff d (weight
edHomogeneousComponent w p f) = if wei…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MvPowerSeries.IsWeightedHomogeneous.coeff_eq_zero`：∀ {σ : Type u_1} {R :
 Type u_2} [inst : Semiring R] {w : σ → ℕ} {f : MvPowerSeries σ R} {p : ℕ},   Mv
PowerSeries.IsWeightedHomogeneous w f p…
· 使用定理 `MvPowerSeries.isWeightedHomogeneous_weightedHomogeneousComponent`：isWeig
htedHomogeneous_weightedHomogeneousComponent (f : MvPowerSeries σ R) (p : Nat) :
 IsWeightedHomogeneous w (f.weightedHomogeneousCompone…
-/
theorem isWeightedHomogeneous_iff_eq_weightedHomogeneousComponent
    {f : MvPowerSeries σ R} {p : ℕ} :
    IsWeightedHomogeneous w f p ↔ f = f.weightedHomogeneousComponent w p := by
  constructor
  · intro hf
    ext d
    rw [coeff_weightedHomogeneousComponent]
    split_ifs with hd
    · rfl
    · exact hf.coeff_eq_zero hd
  · intro hf
    rw [hf]
    exact isWeightedHomogeneous_weightedHomogeneousComponent w f p

variable {w} in
/-
**MvPowerSeries.weightedHomogeneousComponent_mul_of_le_weightedOrder** 是 Mathlib
 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：weightedHomogeneousComponent_mul_of_le_weightedOrder {f g : MvPowerSeries 
σ R} {p q : Nat} (hf : p <= f.weightedOrder w) (hg : q <= g.weightedOrder w) : w
eightedHomogeneousComponent w (p + q) (f * g) = weightedHomogeneousComponent w p
 f * weightedHomogeneousComponent w q g
参数：hf : p <= f.weightedOrder w；hg : q <= g.weightedOrder w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_weightedHomogeneousComponent`：coeff_weightedHomogene
ousComponent (p : Nat) (d : σ ->₀ Nat) (f : MvPowerSeries σ R) : coeff d (weight
edHomogeneousComponent w p f) = if wei…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
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
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.HasAntidiagonal.mem_antidiagonal`：∀ {A : Type u_1} {inst : AddMon
oid A} [self : Finset.HasAntidiagonal A] {n : A} {a : A × A},   a ∈ Finset.HasAn
tidiagonal.antidiagonal n ↔ a…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MvPowerSeries.coeff_eq_zero_of_lt_weightedOrder`：coeff_eq_zero_of_lt_wei
ghtedOrder {d : σ ->₀ Nat} (h : (weight w d) < f.weightedOrder w) : coeff d f = 
0
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `ENat.natCast_lt_natCast`：natCast_lt_natCast {n m : Nat} : (n : Nat∞) < (
m : Nat∞) ↔ n < m
（共 34 条，此处仅展示前 30 条）
-/
theorem weightedHomogeneousComponent_mul_of_le_weightedOrder {f g : MvPowerSeries σ R} {p q : ℕ}
    (hf : p ≤ f.weightedOrder w) (hg : q ≤ g.weightedOrder w) :
    weightedHomogeneousComponent w (p + q) (f * g) =
      weightedHomogeneousComponent w p f * weightedHomogeneousComponent w q g := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent]
  split_ifs with hd
  · apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mem_antidiagonal] at hx
    rw [← hx, map_add] at hd
    simp only [coeff_weightedHomogeneousComponent]
    rcases trichotomy_of_add_eq_add hd with h | h | h
    · rw [if_pos h.1, if_pos h.2]
    · rw [if_neg (ne_of_lt h), zero_mul]
      rw [← ENat.natCast_lt_natCast] at h
      rw [coeff_eq_zero_of_lt_weightedOrder w (lt_of_lt_of_le h hf), zero_mul]
    · rw [if_neg (ne_of_lt h), mul_zero]
      rw [← ENat.natCast_lt_natCast] at h
      rw [coeff_eq_zero_of_lt_weightedOrder w (lt_of_lt_of_le h hg), mul_zero]
  · symm
    apply IsWeightedHomogeneous.coeff_eq_zero _ hd
    exact IsWeightedHomogeneous.mul
      (isWeightedHomogeneous_weightedHomogeneousComponent w f p)
      (isWeightedHomogeneous_weightedHomogeneousComponent w g q)

/-- Homogeneous power series -/
/-
**MvPowerSeries.IsHomogeneous** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
形式化陈述：IsHomogeneous (f : MvPowerSeries σ R) (p : Nat) : Prop
参数：f : MvPowerSeries σ R；p : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Homogeneous power series
-/
def IsHomogeneous (f : MvPowerSeries σ R) (p : ℕ) : Prop :=
  IsWeightedHomogeneous 1 f p
/-
**MvPowerSeries.IsHomogeneous.coeff_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSe
ries.IsHomogeneous`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_2} [inst : Semiring R] {f : MvPowerSeries σ R
} {p : ℕ},   f.IsHomogeneous p → ∀ {d : σ →₀ ℕ}, Finsupp.degree d ≠ p → (MvPower
Series.coeff d) f = 0
参数：MvPowerSeries.coeff d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.IsWeightedHomogeneous.coeff_eq_zero`：∀ {σ : Type u_1} {R :
 Type u_2} [inst : Semiring R] {w : σ → ℕ} {f : MvPowerSeries σ R} {p : ℕ},   Mv
PowerSeries.IsWeightedHomogeneous w f p…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.degree_eq_weight_one`：degree_eq_weight_one {R : Type*} [Semiring
 R] : degree (R
-/
theorem IsHomogeneous.coeff_eq_zero {f : MvPowerSeries σ R} {p : ℕ}
    (hf : f.IsHomogeneous p) {d : σ →₀ ℕ} (hd : degree d ≠ p) :
    f.coeff d = 0 := by
  apply IsWeightedHomogeneous.coeff_eq_zero hf
  rwa [degree_eq_weight_one] at hd
/-
**MvPowerSeries.IsHomogeneous.add** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries.IsHom
ogeneous`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_2} [inst : Semiring R] {f g : MvPowerSeries σ
 R} {p : ℕ},   f.IsHomogeneous p → g.IsHomogeneous p → (f + g).IsHomogeneous p
参数：f + g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.IsWeightedHomogeneous.add`：∀ {σ : Type u_1} {R : Type u_2}
 [inst : Semiring R] {w : σ → ℕ} {f g : MvPowerSeries σ R} {p : ℕ},   MvPowerSer
ies.IsWeightedHomogeneous w f…
-/
protected theorem IsHomogeneous.add {f g : MvPowerSeries σ R} {p : ℕ}
    (hf : f.IsHomogeneous p) (hg : g.IsHomogeneous p) :
    (f + g).IsHomogeneous p :=
  IsWeightedHomogeneous.add hf hg
/-
**MvPowerSeries.IsHomogeneous.mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries.IsHom
ogeneous`。
形式化陈述：∀ {σ : Type u_1} {R : Type u_2} [inst : Semiring R] {f g : MvPowerSeries σ
 R} {p q : ℕ},   f.IsHomogeneous p → g.IsHomogeneous q → (f * g).IsHomogeneous (
p + q)
参数：f * g；p + q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.IsWeightedHomogeneous.mul`：∀ {σ : Type u_1} {R : Type u_2}
 [inst : Semiring R] {w : σ → ℕ} {f g : MvPowerSeries σ R} {p q : ℕ},   MvPowerS
eries.IsWeightedHomogeneous w…
-/
protected theorem IsHomogeneous.mul {f g : MvPowerSeries σ R} {p q : ℕ}
    (hf : f.IsHomogeneous p) (hg : g.IsHomogeneous q) :
    (f * g).IsHomogeneous (p + q) :=
  IsWeightedHomogeneous.mul hf hg

/-- The homogeneous components of an `MvPowerSeries` -/
/-
**MvPowerSeries.homogeneousComponent** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
形式化陈述：homogeneousComponent (p : Nat) : MvPowerSeries σ R ->ₗ[R] MvPowerSeries σ 
R
参数：p : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homogeneous components of an `MvPowerSeries`
-/
def homogeneousComponent (p : ℕ) : MvPowerSeries σ R →ₗ[R] MvPowerSeries σ R :=
  weightedHomogeneousComponent 1 p
/-
**MvPowerSeries.coeff_homogeneousComponent** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSer
ies`。
形式化陈述：coeff_homogeneousComponent (p : Nat) (d : σ ->₀ Nat) (f : MvPowerSeries σ 
R) : coeff d (homogeneousComponent p f) = if degree d = p then coeff d f else 0
参数：p : Nat；d : σ ->₀ Nat；f : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.degree_eq_weight_one`：degree_eq_weight_one {R : Type*} [Semiring
 R] : degree (R
· 使用定理 `MvPowerSeries.coeff_weightedHomogeneousComponent`：coeff_weightedHomogene
ousComponent (p : Nat) (d : σ ->₀ Nat) (f : MvPowerSeries σ R) : coeff d (weight
edHomogeneousComponent w p f) = if wei…
-/
theorem coeff_homogeneousComponent (p : ℕ) (d : σ →₀ ℕ) (f : MvPowerSeries σ R) :
    coeff d (homogeneousComponent p f) =
      if degree d = p then coeff d f else 0 := by
  rw [degree_eq_weight_one]
  exact coeff_weightedHomogeneousComponent 1 p d f
/-
**MvPowerSeries.homogeneousComponent_of_lt_order_eq_zero** 是 Mathlib 中的一个定理，位于命名
空间 `MvPowerSeries`。
形式化陈述：homogeneousComponent_of_lt_order_eq_zero {f : MvPowerSeries σ R} {p : Nat}
 (hf : p < f.order) : f.homogeneousComponent p = 0
参数：hf : p < f.order。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.weightedHomogeneousComponent_of_lt_weightedOrder_eq_zero`：
weightedHomogeneousComponent_of_lt_weightedOrder_eq_zero {f : MvPowerSeries σ R}
 {p : Nat} (hf : p < f.weightedOrder w) : f.weightedHomogene…
-/
theorem homogeneousComponent_of_lt_order_eq_zero
    {f : MvPowerSeries σ R} {p : ℕ} (hf : p < f.order) :
    f.homogeneousComponent p = 0 :=
  weightedHomogeneousComponent_of_lt_weightedOrder_eq_zero hf
/-
**MvPowerSeries.homogeneousComponent_of_order** 是 Mathlib 中的一个定理，位于命名空间 `MvPower
Series`。
形式化陈述：homogeneousComponent_of_order {f : MvPowerSeries σ R} {p : Nat} (hf : p = 
f.order) : f.homogeneousComponent p != 0
参数：hf : p = f.order。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.weightedHomogeneousComponent_of_weightedOrder`：weightedHom
ogeneousComponent_of_weightedOrder {f : MvPowerSeries σ R} {p : Nat} (hf : p = f
.weightedOrder w) : f.weightedHomogeneousComponen…
-/
theorem homogeneousComponent_of_order
    {f : MvPowerSeries σ R} {p : ℕ} (hf : p = f.order) :
    f.homogeneousComponent p ≠ 0 :=
  weightedHomogeneousComponent_of_weightedOrder hf
/-
**MvPowerSeries.isHomogeneous_homogeneousComponent** 是 Mathlib 中的一个定理，位于命名空间 `Mv
PowerSeries`。
形式化陈述：isHomogeneous_homogeneousComponent (f : MvPowerSeries σ R) (p : Nat) : IsH
omogeneous (f.homogeneousComponent p) p
参数：f : MvPowerSeries σ R；p : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.isWeightedHomogeneous_weightedHomogeneousComponent`：isWeig
htedHomogeneous_weightedHomogeneousComponent (f : MvPowerSeries σ R) (p : Nat) :
 IsWeightedHomogeneous w (f.weightedHomogeneousCompone…
-/
theorem isHomogeneous_homogeneousComponent (f : MvPowerSeries σ R) (p : ℕ) :
    IsHomogeneous (f.homogeneousComponent p) p :=
  isWeightedHomogeneous_weightedHomogeneousComponent 1 f p
/-
**MvPowerSeries.isHomogeneous_iff_eq_homogeneousComponent** 是 Mathlib 中的一个定理，位于命
名空间 `MvPowerSeries`。
形式化陈述：isHomogeneous_iff_eq_homogeneousComponent {f : MvPowerSeries σ R} {p : Nat
} : IsHomogeneous f p ↔ f = f.homogeneousComponent p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.isWeightedHomogeneous_iff_eq_weightedHomogeneousComponent`
：isWeightedHomogeneous_iff_eq_weightedHomogeneousComponent {f : MvPowerSeries σ 
R} {p : Nat} : IsWeightedHomogeneous w f p ↔ f = f.weightedHo…
-/
theorem isHomogeneous_iff_eq_homogeneousComponent
    {f : MvPowerSeries σ R} {p : ℕ} :
    IsHomogeneous f p ↔ f = f.homogeneousComponent p :=
  isWeightedHomogeneous_iff_eq_weightedHomogeneousComponent
/-
**MvPowerSeries.homogeneousComponent_mul_of_le_order** 是 Mathlib 中的一个定理，位于命名空间 `
MvPowerSeries`。
形式化陈述：homogeneousComponent_mul_of_le_order {f g : MvPowerSeries σ R} {p q : Nat}
 (hf : p <= f.order) (hg : q <= g.order) : homogeneousComponent (p + q) (f * g) 
= homogeneousComponent p f * homogeneousComponent q g
参数：hf : p <= f.order；hg : q <= g.order。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.weightedHomogeneousComponent_mul_of_le_weightedOrder`：weig
htedHomogeneousComponent_mul_of_le_weightedOrder {f g : MvPowerSeries σ R} {p q 
: Nat} (hf : p <= f.weightedOrder w) (hg : q <= g.weight…
-/
theorem homogeneousComponent_mul_of_le_order {f g : MvPowerSeries σ R} {p q : ℕ}
    (hf : p ≤ f.order) (hg : q ≤ g.order) :
    homogeneousComponent (p + q) (f * g) =
      homogeneousComponent p f * homogeneousComponent q g :=
  weightedHomogeneousComponent_mul_of_le_weightedOrder hf hg

end HomogeneousComponent

end

end MvPowerSeries

