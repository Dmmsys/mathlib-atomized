/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Emirhan Duysak, Adem Alp Gök, Junyan Xu
-/
module

public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Unbundled.Int
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Data.Int.GCD
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Order.BooleanAlgebra.Set

/-!
# The integers form a linear ordered ring

This file contains:
* instances on `ℤ`. The stronger one is `Int.instLinearOrderedCommRing`.
* basic lemmas about integers that involve order properties.

## Recursors

* `Int.rec`: Sign disjunction. Something is true/defined on `ℤ` if it's true/defined for nonnegative
  and for negative values. (Defined in core Lean 3)
* `Int.inductionOn`: Simple growing induction on positive numbers, plus simple decreasing induction
  on negative numbers. Note that this recursor is currently only `Prop`-valued.
* `Int.inductionOn'`: Simple growing induction for numbers greater than `b`, plus simple decreasing
  induction on numbers less than `b`.
-/

public section

-- We should need only a minimal development of sets in order to get here.
assert_not_exists Set.Subsingleton

open Function Nat

namespace Int

/-
**Int.instIsStrictOrderedRing** 是 Mathlib 中的一个实例，位于命名空间 `Int`。
形式化陈述：instIsStrictOrderedRing : IsStrictOrderedRing Int
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `IsStrictOrderedRing.of_mul_pos`：IsStrictOrderedRing.of_mul_pos [Ring R] 
[PartialOrder R] [IsOrderedAddMonoid R] [ZeroLEOneClass R] [Nontrivial R] (mul_p
os : forall a b : R,…
· 使用定理 `Int.mul_pos`：∀ {a b : ℤ}, 0 < a → 0 < b → 0 < a * b
-/
instance instIsStrictOrderedRing : IsStrictOrderedRing ℤ := .of_mul_pos @Int.mul_pos

/-! ### Miscellaneous lemmas -/

/-
**Int.isCompl_even_odd** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：isCompl_even_odd : IsCompl { n : Int | Even n } { n | Odd n }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
### Miscellaneous lemmas
-/
lemma isCompl_even_odd : IsCompl { n : ℤ | Even n } { n | Odd n } := by
  simp [← not_even_iff_odd, ← Set.compl_ofPred, isCompl_compl]

@[simp]
/-
**Int._root_.Nat.cast_natAbs** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Nat.cast_natAbs {α : Type*} [AddGroupWithOne α] (n : ℤ) : (n.natAbs : α) = |n| := by
  rw [← natCast_natAbs, Int.cast_natCast]
/-
**Int.two_le_iff_pos_of_even** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：two_le_iff_pos_of_even {m : Int} (even : Even m) : 2 <= m ↔ 0 < m
参数：even : Even m。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Int.le_iff_pos_of_dvd`：le_iff_pos_of_dvd (ha : 0 < a) (hab : a ∣ b) : a 
<= b ↔ 0 < b
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Even.two_dvd`：∀ {α : Type u_2} [inst : Semiring α] {a : α}, Even a → 2 ∣
 a
-/
lemma two_le_iff_pos_of_even {m : ℤ} (even : Even m) : 2 ≤ m ↔ 0 < m :=
  le_iff_pos_of_dvd (by decide) even.two_dvd
/-
**Int.add_two_le_iff_lt_of_even_sub** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：add_two_le_iff_lt_of_even_sub {m n : Int} (even : Even (n - m)) : m + 2 <=
 n ↔ m < n
参数：even : Even (n - m)。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma add_two_le_iff_lt_of_even_sub {m n : ℤ} (even : Even (n - m)) : m + 2 ≤ n ↔ m < n := by
  grind

end Int

/-- If the gcd of two natural numbers `p` and `q` divides a third natural number `n`,
and if `n` is at least `(p - 1) * (q - 1)`, then `n` can be represented as an `ℕ`-linear
combination of `p` and `q`.

TODO: show that if `p.gcd q = 1` and `0 ≤ n ≤ (p - 1) * (q - 1) - 1 = N`, then `n` is
representable iff `N - n` is not. In particular `N` is not representable, solving the
coin problem for two coins: https://en.wikipedia.org/wiki/Coin_problem#n_=_2. -/
/-
**Nat.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le (p q n : Nat) (dvd : p.gcd
 q ∣ n) (le : p.pred * q.pred <= n) : exists a b : Nat, a * p + b * q = n
参数：p q n : Nat；dvd : p.gcd q ∣ n；le : p.pred * q.pred <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.gcd_zero_left`：∀ (y : ℕ), Nat.gcd 0 y = y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.gcd_zero_right`：∀ (n : ℕ), n.gcd 0 = n
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Int.gcd_dvd_iff`：gcd_dvd_iff {a b : Int} {n : Nat} : gcd a b ∣ n ↔ exist
s x y : Int, ↑n = a * x + b * y
· 使用定理 `Int.gcd_natCast_natCast`：∀ (a b : ℕ), (↑a).gcd ↑b = a.gcd b
· 使用定理 `Nat.cast_injective`：cast_injective : Function.Injective (Nat.cast : Nat 
-> R)
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `Int.emod_add_ediv_mul`：∀ (a b : ℤ), a % b + a / b * b = a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.natCast_toNat_eq_self`：∀ {a : ℤ}, ↑a.toNat = a ↔ 0 ≤ a
· 使用定理 `Int.emod_nonneg`：∀ (a : ℤ) {b : ℤ}, b ≠ 0 → 0 ≤ a % b
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `Int.emod_lt`：∀ (a : ℤ) {b : ℤ}, b ≠ 0 → a % b < ↑b.natAbs
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
If the gcd of two natural numbers `p` and `q` divides a third natural number `n`
,
and if `n` is at least `(p - 1) * (q - 1)`, then `n` can be represented as an `ℕ
`-linear
combination of `p` and `q`.

TODO: show that if `p.gcd q = 1` and `0 ≤ n ≤ (p - 1) * (q - 1) - 1 = N`, then `
n` is
representable iff `N - n` is not. In particular `N` is not representable, solvin
g the
coin problem for two coins: https://en.wikipedia.org/wiki/Coin_problem#n_=_2.
-/
theorem Nat.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le (p q n : ℕ) (dvd : p.gcd q ∣ n)
    (le : p.pred * q.pred ≤ n) : ∃ a b : ℕ, a * p + b * q = n := by
  obtain _ | p := p
  · have ⟨b, eq⟩ := q.gcd_zero_left ▸ dvd
    exact ⟨0, b, by simpa [mul_comm, eq_comm] using eq⟩
  obtain _ | q := q
  · have ⟨a, eq⟩ := p.gcd_zero_right ▸ dvd
    exact ⟨a, 0, by simpa [mul_comm, eq_comm] using eq⟩
  rw [← Int.gcd_natCast_natCast, Int.gcd_dvd_iff] at dvd
  have ⟨a_n, b_n, eq⟩ := dvd
  let a := a_n % q.succ
  let b := b_n + a_n / q.succ * p.succ
  refine ⟨a.toNat, b.toNat, Nat.cast_injective (R := ℤ) ?_⟩
  have : a * p.succ + b * q.succ = n := by rw [add_mul, ← add_assoc,
    add_right_comm, mul_right_comm, ← add_mul, Int.emod_add_ediv_mul, eq, mul_comm, mul_comm b_n]
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Int.natCast_toNat_eq_self.mpr
    (Int.emod_nonneg _ <| by lia), Int.natCast_toNat_eq_self.mpr, this]
  -- show b ≥ 0 by contradiction
  by_contra hb
  replace hb : b ≤ -1 := by lia
  apply lt_irrefl (n : ℤ)
  have ha := Int.emod_lt a_n (by lia : (q.succ : ℤ) ≠ 0)
  rw [p.pred_succ, q.pred_succ] at le
  calc n = a * p.succ + b * q.succ := this.symm
       _ ≤ q * p.succ + -1 * q.succ := by gcongr <;> lia
       _ = p * q - 1 := by simp_rw [Nat.cast_succ, mul_add, mul_comm]; lia
       _ ≤ n - 1 := by rwa [sub_le_sub_iff_right, ← Nat.cast_mul, Nat.cast_le]
       _ < n := by lia
