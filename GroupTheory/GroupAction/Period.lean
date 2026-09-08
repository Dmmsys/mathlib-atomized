/-
Copyright (c) 2024 Emilie Burgun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emilie Burgun
-/
module

public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.GroupTheory.Exponent
public import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Period of a group action

This module defines some helpful lemmas around [`MulAction.period`] and [`AddAction.period`].
The period of a point `a` by a group element `g` is the smallest `m` such that `g ^ m • a = a`
(resp. `(m • g) +ᵥ a = a`) for a given `g : G` and `a : α`.

If such an `m` does not exist,
then by convention `MulAction.period` and `AddAction.period` return 0.
-/

public section

namespace MulAction

universe u v
variable {α : Type v}
variable {G : Type u} [Group G] [MulAction G α]
variable {M : Type u} [Monoid M] [MulAction M α]

/-- If the action is periodic, then a lower bound for its period can be computed. -/
@[to_additive /-- If the action is periodic, then a lower bound for its period can be computed. -/]
/-
**MulAction.le_period** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：le_period {m : M} {a : α} {n : Nat} (period_pos : 0 < period m a) (moved :
 forall k, 0 < k -> k < n -> m ^ k • a != a) : n <= period m a
参数：period_pos : 0 < period m a；moved : forall k, 0 < k -> k < n -> m ^ k • a != 
a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `MulAction.pow_period_smul`：∀ {α : Type v} {M : Type u} [inst : Monoid M]
 [inst_1 : MulAction M α] (m : M) (a : α), m ^ MulAction.period m a • a = a

--- 原说明 ---
If the action is periodic, then a lower bound for its period can be computed.
-/
theorem le_period {m : M} {a : α} {n : ℕ} (period_pos : 0 < period m a)
    (moved : ∀ k, 0 < k → k < n → m ^ k • a ≠ a) : n ≤ period m a :=
  le_of_not_gt fun period_lt_n =>
    moved _ period_pos period_lt_n <| pow_period_smul m a

/-- If for some `n`, `m ^ n • a = a`, then `period m a ≤ n`. -/
@[to_additive /-- If for some `n`, `(n • m) +ᵥ a = a`, then `period m a ≤ n`. -/]
/-
**MulAction.period_le_of_fixed** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：period_le_of_fixed {m : M} {a : α} {n : Nat} (n_pos : 0 < n) (fixed : m ^ 
n • a = a) : period m a <= n
参数：n_pos : 0 < n；fixed : m ^ n • a = a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.IsPeriodicPt.minimalPeriod_le`：∀ {α : Type u_1} {f : α → α} {x 
: α} {n : ℕ}, 0 < n → Function.IsPeriodicPt f n x → Function.minimalPeriod f x ≤
 n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MulAction.isPeriodicPt_smul_iff`：∀ {α : Type v} {M : Type u} [inst : Mon
oid M] [inst_1 : MulAction M α] {m : M} {a : α} {n : ℕ},   Function.IsPeriodicPt
 (fun x => m • x) n a…

--- 原说明 ---
If for some `n`, `m ^ n • a = a`, then `period m a ≤ n`.
-/
theorem period_le_of_fixed {m : M} {a : α} {n : ℕ} (n_pos : 0 < n) (fixed : m ^ n • a = a) :
    period m a ≤ n :=
  (isPeriodicPt_smul_iff.mpr fixed).minimalPeriod_le n_pos

/-- If for some `n`, `m ^ n • a = a`, then `0 < period m a`. -/
@[to_additive /-- If for some `n`, `(n • m) +ᵥ a = a`, then `0 < period m a`. -/]
/-
**MulAction.period_pos_of_fixed** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：period_pos_of_fixed {m : M} {a : α} {n : Nat} (n_pos : 0 < n) (fixed : m ^
 n • a = a) : 0 < period m a
参数：n_pos : 0 < n；fixed : m ^ n • a = a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.IsPeriodicPt.minimalPeriod_pos`：∀ {α : Type u_1} {f : α → α} {x
 : α} {n : ℕ}, 0 < n → Function.IsPeriodicPt f n x → 0 < Function.minimalPeriod 
f x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MulAction.isPeriodicPt_smul_iff`：∀ {α : Type v} {M : Type u} [inst : Mon
oid M] [inst_1 : MulAction M α] {m : M} {a : α} {n : ℕ},   Function.IsPeriodicPt
 (fun x => m • x) n a…

--- 原说明 ---
If for some `n`, `m ^ n • a = a`, then `0 < period m a`.
-/
theorem period_pos_of_fixed {m : M} {a : α} {n : ℕ} (n_pos : 0 < n) (fixed : m ^ n • a = a) :
    0 < period m a :=
  (isPeriodicPt_smul_iff.mpr fixed).minimalPeriod_pos n_pos

@[to_additive]
/-
**MulAction.period_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：period_eq_one_iff {m : M} {a : α} : period m a = 1 ↔ m • a = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.pow_period_smul`：∀ {α : Type v} {M : Type u} [inst : Monoid M]
 [inst_1 : MulAction M α] (m : M) (a : α), m ^ MulAction.period m a • a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MulAction.period_le_of_fixed`：period_le_of_fixed {m : M} {a : α} {n : Na
t} (n_pos : 0 < n) (fixed : m ^ n • a = a) : period m a <= n
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.period_pos_of_fixed`：period_pos_of_fixed {m : M} {a : α} {n : 
Nat} (n_pos : 0 < n) (fixed : m ^ n • a = a) : 0 < period m a
-/
theorem period_eq_one_iff {m : M} {a : α} : period m a = 1 ↔ m • a = a :=
  ⟨fun eq_one => pow_one m ▸ eq_one ▸ pow_period_smul m a,
   fun fixed => le_antisymm
    (period_le_of_fixed one_pos (by simpa))
    (period_pos_of_fixed one_pos (by simpa))⟩

/-- For any non-zero `n` less than the period of `m` on `a`, `a` is moved by `m ^ n`. -/
@[to_additive
/-- For any non-zero `n` less than the period of `m` on `a`, `a` is moved by `n • m`. -/]
/-
**MulAction.pow_smul_ne_of_lt_period** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：pow_smul_ne_of_lt_period {m : M} {a : α} {n : Nat} (n_pos : 0 < n) (n_lt_p
eriod : n < period m a) : m ^ n • a != a
参数：n_pos : 0 < n；n_lt_period : n < period m a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `MulAction.period_le_of_fixed`：period_le_of_fixed {m : M} {a : α} {n : Na
t} (n_pos : 0 < n) (fixed : m ^ n • a = a) : period m a <= n
-/
theorem pow_smul_ne_of_lt_period {m : M} {a : α} {n : ℕ} (n_pos : 0 < n)
    (n_lt_period : n < period m a) : m ^ n • a ≠ a := fun a_fixed =>
  not_le_of_gt n_lt_period <| period_le_of_fixed n_pos a_fixed

section Identities

/-! ### `MulAction.period` for common group elements
-/

variable (M) in
@[to_additive (attr := simp)]
/-
**MulAction.period_one** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：period_one (a : α) : period (1 : M) a = 1
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MulAction.period_eq_one_iff`：period_eq_one_iff {m : M} {a : α} : period 
m a = 1 ↔ m • a = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem period_one (a : α) : period (1 : M) a = 1 := period_eq_one_iff.mpr (one_smul M a)

@[to_additive (attr := simp)]
/-
**MulAction.period_inv** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：period_inv (g : G) (a : α) : period g⁻¹ a = period g a
参数：g : G；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_eq_iff_eq_inv_smul`：smul_eq_iff_eq_inv_smul (g : α) {x y : β} : g •
 x = y ↔ x = g⁻¹ • y
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `inv_zpow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a⁻
¹ ^ n = (a ^ n)⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem period_inv (g : G) (a : α) : period g⁻¹ a = period g a := by
  simp only [period_eq_minimalPeriod, Function.minimalPeriod_eq_minimalPeriod_iff,
    isPeriodicPt_smul_iff]
  intro n
  rw [smul_eq_iff_eq_inv_smul, eq_comm, ← zpow_natCast, inv_zpow, inv_inv, zpow_natCast]

end Identities

section MonoidExponent

/-! ### `MulAction.period` and group exponents

The period of a given element `m : M` can be bounded by the `Monoid.exponent M` or `orderOf m`.
-/

@[to_additive]
/-
**MulAction.period_dvd_orderOf** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：period_dvd_orderOf (m : M) (a : α) : period m a ∣ orderOf m
参数：m : M；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulAction.pow_smul_eq_iff_period_dvd`：∀ {α : Type v} {M : Type u} [inst 
: Monoid M] [inst_1 : MulAction M α] {n : ℕ} {m : M} {a : α},   m ^ n • a = a ↔ 
MulAction.period m a ∣ n
· 使用定理 `pow_orderOf_eq_one`：pow_orderOf_eq_one (x : G) : x ^ orderOf x = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b

--- 原说明 ---
### `MulAction.period` and group exponents

The period of a given element `m : M` can be bounded by the `Monoid.exponent M` 
or `orderOf m`.
-/
theorem period_dvd_orderOf (m : M) (a : α) : period m a ∣ orderOf m := by
  rw [← pow_smul_eq_iff_period_dvd, pow_orderOf_eq_one, one_smul]

@[to_additive]
/-
**MulAction.period_pos_of_orderOf_pos** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：period_pos_of_orderOf_pos {m : M} (order_pos : 0 < orderOf m) (a : α) : 0 
< period m a
参数：order_pos : 0 < orderOf m；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.pos_of_dvd_of_pos`：∀ {m n : ℕ}, m ∣ n → 0 < n → 0 < m
· 使用定理 `MulAction.period_dvd_orderOf`：period_dvd_orderOf (m : M) (a : α) : perio
d m a ∣ orderOf m
-/
theorem period_pos_of_orderOf_pos {m : M} (order_pos : 0 < orderOf m) (a : α) :
    0 < period m a :=
  Nat.pos_of_dvd_of_pos (period_dvd_orderOf m a) order_pos

@[to_additive]
/-
**MulAction.period_le_orderOf** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：period_le_orderOf {m : M} (order_pos : 0 < orderOf m) (a : α) : period m a
 <= orderOf m
参数：order_pos : 0 < orderOf m；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `MulAction.period_dvd_orderOf`：period_dvd_orderOf (m : M) (a : α) : perio
d m a ∣ orderOf m
-/
theorem period_le_orderOf {m : M} (order_pos : 0 < orderOf m) (a : α) :
    period m a ≤ orderOf m :=
  Nat.le_of_dvd order_pos (period_dvd_orderOf m a)

@[to_additive]
/-
**MulAction.period_dvd_exponent** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：period_dvd_exponent (m : M) (a : α) : period m a ∣ Monoid.exponent M
参数：m : M；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulAction.pow_smul_eq_iff_period_dvd`：∀ {α : Type v} {M : Type u} [inst 
: Monoid M] [inst_1 : MulAction M α] {n : ℕ} {m : M} {a : α},   m ^ n • a = a ↔ 
MulAction.period m a ∣ n
· 使用定理 `Monoid.pow_exponent_eq_one`：pow_exponent_eq_one (g : G) : g ^ exponent G
 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem period_dvd_exponent (m : M) (a : α) : period m a ∣ Monoid.exponent M := by
  rw [← pow_smul_eq_iff_period_dvd, Monoid.pow_exponent_eq_one, one_smul]

@[to_additive]
/-
**MulAction.period_pos_of_exponent_pos** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：period_pos_of_exponent_pos (exp_pos : 0 < Monoid.exponent M) (m : M) (a : 
α) : 0 < period m a
参数：exp_pos : 0 < Monoid.exponent M；m : M；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.pos_of_dvd_of_pos`：∀ {m n : ℕ}, m ∣ n → 0 < n → 0 < m
· 使用定理 `MulAction.period_dvd_exponent`：period_dvd_exponent (m : M) (a : α) : per
iod m a ∣ Monoid.exponent M
-/
theorem period_pos_of_exponent_pos (exp_pos : 0 < Monoid.exponent M) (m : M) (a : α) :
    0 < period m a :=
  Nat.pos_of_dvd_of_pos (period_dvd_exponent m a) exp_pos

@[to_additive]
/-
**MulAction.period_le_exponent** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`。
形式化陈述：period_le_exponent (exp_pos : 0 < Monoid.exponent M) (m : M) (a : α) : per
iod m a <= Monoid.exponent M
参数：exp_pos : 0 < Monoid.exponent M；m : M；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `MulAction.period_dvd_exponent`：period_dvd_exponent (m : M) (a : α) : per
iod m a ∣ Monoid.exponent M
-/
theorem period_le_exponent (exp_pos : 0 < Monoid.exponent M) (m : M) (a : α) :
    period m a ≤ Monoid.exponent M :=
  Nat.le_of_dvd exp_pos (period_dvd_exponent m a)

variable (α)

@[to_additive]
/-
**MulAction.period_bounded_of_exponent_pos** 是 Mathlib 中的一个定理，位于命名空间 `MulAction`
。
形式化陈述：period_bounded_of_exponent_pos (exp_pos : 0 < Monoid.exponent M) (m : M) :
 BddAbove (Set.range (fun a : α => period m a))
参数：exp_pos : 0 < Monoid.exponent M；m : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `MulAction.period_le_exponent`：period_le_exponent (exp_pos : 0 < Monoid.e
xponent M) (m : M) (a : α) : period m a <= Monoid.exponent M
-/
theorem period_bounded_of_exponent_pos (exp_pos : 0 < Monoid.exponent M) (m : M) :
    BddAbove (Set.range (fun a : α => period m a)) := by
  use Monoid.exponent M
  simpa [upperBounds] using period_le_exponent exp_pos _

end MonoidExponent


end MulAction

