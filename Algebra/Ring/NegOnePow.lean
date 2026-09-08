/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Johan Commelin
-/
module

public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Algebra.Ring.Int.Units
public import Mathlib.Data.ZMod.IntUnitsPower

/-!
# Integer powers of (-1)

This file defines the map `negOnePow : ℤ → ℤˣ` which sends `n` to `(-1 : ℤˣ) ^ n`.

The definition of `negOnePow` and some lemmas first appeared in contributions by
Johan Commelin to the Liquid Tensor Experiment.

-/

@[expose] public section

assert_not_exists Field
assert_not_exists TwoSidedIdeal

namespace Int

/-- The map `ℤ → ℤˣ` which sends `n` to `(-1 : ℤˣ) ^ n`. -/
/-
**Int.negOnePow** 是 Mathlib 中的一个定义，位于命名空间 `Int`。
形式化陈述：negOnePow (n : Int) : Intˣ
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `ℤ → ℤˣ` which sends `n` to `(-1 : ℤˣ) ^ n`.
-/
def negOnePow (n : ℤ) : ℤˣ := (-1 : ℤˣ) ^ n
/-
**Int.negOnePow_def** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：negOnePow_def (n : Int) : n.negOnePow = (-1 : Intˣ) ^ n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma negOnePow_def (n : ℤ) : n.negOnePow = (-1 : ℤˣ) ^ n := rfl
/-
**Int.negOnePow_add** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：negOnePow_add (n₁ n₂ : Int) : (n₁ + n₂).negOnePow = n₁.negOnePow * n₂.negO
nePow
参数：n₁ n₂ : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `zpow_add`：zpow_add (a : G) (m n : Int) : a ^ (m + n) = a ^ m * a ^ n
-/
lemma negOnePow_add (n₁ n₂ : ℤ) :
    (n₁ + n₂).negOnePow = n₁.negOnePow * n₂.negOnePow :=
  zpow_add _ _ _

@[simp]
/-
**Int.negOnePow_zero** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：negOnePow_zero : negOnePow 0 = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma negOnePow_zero : negOnePow 0 = 1 := rfl

@[simp]
/-
**Int.negOnePow_one** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：negOnePow_one : negOnePow 1 = -1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma negOnePow_one : negOnePow 1 = -1 := rfl
/-
**Int.negOnePow_succ** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：negOnePow_succ (n : Int) : (n + 1).negOnePow = -n.negOnePow
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Int.negOnePow_add`：negOnePow_add (n₁ n₂ : Int) : (n₁ + n₂).negOnePow = n
₁.negOnePow * n₂.negOnePow
· 使用引理 `Int.negOnePow_one`：negOnePow_one : negOnePow 1 = -1
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma negOnePow_succ (n : ℤ) : (n + 1).negOnePow = -n.negOnePow := by
  rw [negOnePow_add, negOnePow_one, mul_neg, mul_one]
/-
**Int.negOnePow_even** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：negOnePow_even (n : Int) (hn : Even n) : n.negOnePow = 1
参数：n : Int；hn : Even n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Int.negOnePow_add`：negOnePow_add (n₁ n₂ : Int) : (n₁ + n₂).negOnePow = n
₁.negOnePow * n₂.negOnePow
· 使用定理 `Int.units_mul_self`：units_mul_self (u : Intˣ) : u * u = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma negOnePow_even (n : ℤ) (hn : Even n) : n.negOnePow = 1 := by
  obtain ⟨k, rfl⟩ := hn
  rw [negOnePow_add, units_mul_self]

@[simp]
/-
**Int.negOnePow_two_mul** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：negOnePow_two_mul (n : Int) : (2 * n).negOnePow = 1
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Int.negOnePow_even`：negOnePow_even (n : Int) (hn : Even n) : n.negOnePow
 = 1
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
-/
lemma negOnePow_two_mul (n : ℤ) : (2 * n).negOnePow = 1 :=
  negOnePow_even _ ⟨n, two_mul n⟩
/-
**Int.negOnePow_odd** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：negOnePow_odd (n : Int) (hn : Odd n) : n.negOnePow = -1
参数：n : Int；hn : Odd n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Int.negOnePow_add`：negOnePow_add (n₁ n₂ : Int) : (n₁ + n₂).negOnePow = n
₁.negOnePow * n₂.negOnePow
· 使用引理 `Int.negOnePow_two_mul`：negOnePow_two_mul (n : Int) : (2 * n).negOnePow =
 1
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma negOnePow_odd (n : ℤ) (hn : Odd n) : n.negOnePow = -1 := by
  obtain ⟨k, rfl⟩ := hn
  simp only [negOnePow_add, negOnePow_two_mul, negOnePow_one, mul_neg, mul_one]

@[simp]
/-
**Int.negOnePow_two_mul_add_one** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：negOnePow_two_mul_add_one (n : Int) : (2 * n + 1).negOnePow = -1
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Int.negOnePow_odd`：negOnePow_odd (n : Int) (hn : Odd n) : n.negOnePow = 
-1
-/
lemma negOnePow_two_mul_add_one (n : ℤ) : (2 * n + 1).negOnePow = -1 :=
  negOnePow_odd _ ⟨n, rfl⟩
/-
**Int.negOnePow_eq_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：negOnePow_eq_one_iff (n : Int) : n.negOnePow = 1 ↔ Even n
参数：n : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.not_odd_iff_even`：∀ {n : ℤ}, ¬Odd n ↔ Even n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Int.negOnePow_odd`：negOnePow_odd (n : Int) (hn : Odd n) : n.negOnePow = 
-1
· 使用定理 `of_decide_eq_false`：∀ {p : Prop} [inst : Decidable p], decide p = false 
→ ¬p
· 使用引理 `Int.negOnePow_even`：negOnePow_even (n : Int) (hn : Even n) : n.negOnePow
 = 1
-/
lemma negOnePow_eq_one_iff (n : ℤ) : n.negOnePow = 1 ↔ Even n := by
  constructor
  · intro h
    rw [← Int.not_odd_iff_even]
    intro h'
    simp only [negOnePow_odd _ h'] at h
    contradiction
  · exact negOnePow_even n
/-
**Int.negOnePow_eq_neg_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：negOnePow_eq_neg_one_iff (n : Int) : n.negOnePow = -1 ↔ Odd n
参数：n : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.not_even_iff_odd`：∀ {n : ℤ}, ¬Even n ↔ Odd n
· 使用引理 `Int.negOnePow_even`：negOnePow_even (n : Int) (hn : Even n) : n.negOnePow
 = 1
· 使用定理 `of_decide_eq_false`：∀ {p : Prop} [inst : Decidable p], decide p = false 
→ ¬p
· 使用引理 `Int.negOnePow_odd`：negOnePow_odd (n : Int) (hn : Odd n) : n.negOnePow = 
-1
-/
lemma negOnePow_eq_neg_one_iff (n : ℤ) : n.negOnePow = -1 ↔ Odd n := by
  constructor
  · intro h
    rw [← Int.not_even_iff_odd]
    intro h'
    rw [negOnePow_even _ h'] at h
    contradiction
  · exact negOnePow_odd n
/-
**Int.abs_negOnePow** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：abs_negOnePow (n : Int) : |(n.negOnePow : Int)| = 1
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.abs_eq_natAbs`：∀ (a : ℤ), |a| = ↑a.natAbs
· 使用引理 `Int.units_natAbs`：units_natAbs (u : Intˣ) : natAbs u = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
theorem abs_negOnePow (n : ℤ) : |(n.negOnePow : ℤ)| = 1 := by
  rw [abs_eq_natAbs, Int.units_natAbs, Nat.cast_one]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Int.negOnePow_neg** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：negOnePow_neg (n : Int) : (-n).negOnePow = n.negOnePow
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用引理 `inv_neg`：inv_neg : (-a)⁻¹ = -a⁻¹
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma negOnePow_neg (n : ℤ) : (-n).negOnePow = n.negOnePow := by
  dsimp [negOnePow]
  simp only [zpow_neg, ← inv_zpow, inv_neg, inv_one]

@[simp]
/-
**Int.negOnePow_abs** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：negOnePow_abs (n : Int) : |n|.negOnePow = n.negOnePow
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `abs_choice`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α
] (x : α), |x| = x ∨ |x| = -x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Int.negOnePow_neg`：negOnePow_neg (n : Int) : (-n).negOnePow = n.negOnePo
w
-/
lemma negOnePow_abs (n : ℤ) : |n|.negOnePow = n.negOnePow := by
  obtain h | h := abs_choice n <;> simp only [h, negOnePow_neg]
/-
**Int.negOnePow_sub** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：negOnePow_sub (n₁ n₂ : Int) : (n₁ - n₂).negOnePow = n₁.negOnePow * n₂.negO
nePow
参数：n₁ n₂ : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `Int.negOnePow_add`：negOnePow_add (n₁ n₂ : Int) : (n₁ + n₂).negOnePow = n
₁.negOnePow * n₂.negOnePow
· 使用引理 `Int.negOnePow_neg`：negOnePow_neg (n : Int) : (-n).negOnePow = n.negOnePo
w
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma negOnePow_sub (n₁ n₂ : ℤ) :
    (n₁ - n₂).negOnePow = n₁.negOnePow * n₂.negOnePow := by
  simp only [sub_eq_add_neg, negOnePow_add, negOnePow_neg]
/-
**Int.negOnePow_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：negOnePow_eq_iff (n₁ n₂ : Int) : n₁.negOnePow = n₂.negOnePow ↔ Even (n₁ - 
n₂)
参数：n₁ n₂ : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Int.negOnePow_even`：negOnePow_even (n : Int) (hn : Even n) : n.negOnePow
 = 1
· 使用引理 `Int.even_sub`：even_sub : Even (m - n) ↔ (Even m ↔ Even n)
· 使用引理 `Int.negOnePow_eq_one_iff`：negOnePow_eq_one_iff (n : Int) : n.negOnePow =
 1 ↔ Even n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Decidable.iff_iff_and_or_not_and_not`：∀ {a b : Prop} [Decidable b], (a ↔
 b) ↔ a ∧ b ∨ ¬a ∧ ¬b
· 使用引理 `Int.negOnePow_odd`：negOnePow_odd (n : Int) (hn : Odd n) : n.negOnePow = 
-1
· 使用定理 `Int.not_even_iff_odd`：∀ {n : ℤ}, ¬Even n ↔ Odd n
· 使用引理 `Int.negOnePow_eq_neg_one_iff`：negOnePow_eq_neg_one_iff (n : Int) : n.neg
OnePow = -1 ↔ Odd n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.not_odd_iff_even`：∀ {n : ℤ}, ¬Odd n ↔ Even n
· 使用定理 `Decidable.of_not_not`：∀ {p : Prop} [Decidable p], ¬¬p → p
-/
lemma negOnePow_eq_iff (n₁ n₂ : ℤ) :
    n₁.negOnePow = n₂.negOnePow ↔ Even (n₁ - n₂) := by
  by_cases h₂ : Even n₂
  · rw [negOnePow_even _ h₂, Int.even_sub, negOnePow_eq_one_iff]
    tauto
  · rw [Int.not_even_iff_odd] at h₂
    rw [negOnePow_odd _ h₂, Int.even_sub, negOnePow_eq_neg_one_iff,
      ← Int.not_odd_iff_even, ← Int.not_odd_iff_even]
    tauto

@[simp]
/-
**Int.negOnePow_mul_self** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：negOnePow_mul_self (n : Int) : (n * n).negOnePow = n.negOnePow
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `Int.even_mul_pred_self`：even_mul_pred_self (n : Int) : Even (n * (n - 1)
)
-/
lemma negOnePow_mul_self (n : ℤ) : (n * n).negOnePow = n.negOnePow := by
  simpa [mul_sub, negOnePow_eq_iff] using n.even_mul_pred_self
/-
**Int.cast_negOnePow_natCast** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：cast_negOnePow_natCast (R : Type*) [Ring R] (n : Nat) : negOnePow n = (-1 
: R) ^ n
参数：R : Type*；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.even_or_odd'`：even_or_odd' (n : Nat) : exists k, n = 2 * k ∨ n = 2 *
 k + 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用引理 `Int.negOnePow_two_mul`：negOnePow_two_mul (n : Int) : (2 * n).negOnePow =
 1
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `Int.negOnePow_two_mul_add_one`：negOnePow_two_mul_add_one (n : Int) : (2 
* n + 1).negOnePow = -1
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
-/
lemma cast_negOnePow_natCast (R : Type*) [Ring R] (n : ℕ) : negOnePow n = (-1 : R) ^ n := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n <;> simp [pow_succ, pow_mul]
/-
**Int.coe_negOnePow_natCast** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：coe_negOnePow_natCast (n : Nat) : negOnePow n = (-1 : Int) ^ n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Int.cast_negOnePow_natCast`：cast_negOnePow_natCast (R : Type*) [Ring R] 
(n : Nat) : negOnePow n = (-1 : R) ^ n
-/
lemma coe_negOnePow_natCast (n : ℕ) : negOnePow n = (-1 : ℤ) ^ n := cast_negOnePow_natCast ..

set_option backward.isDefEq.respectTransparency false in
/-- The cast of `negOnePow n` to a ring equals `(-1) ^ n.natAbs`. -/
@[simp]
/-
**Int.coe_negOnePow** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：coe_negOnePow (R : Type*) [Ring R] (n : Int) : (n.negOnePow : R) = (-1 : R
) ^ n.natAbs
参数：R : Type*；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Int.cast_negOnePow_natCast`：cast_negOnePow_natCast (R : Type*) [Ring R] 
(n : Nat) : negOnePow n = (-1 : R) ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `Int.units_inv_eq_self`：units_inv_eq_self (u : Intˣ) : u⁻¹ = u
· 使用定理 `Int.cast_pow`：∀ {R : Type u_1} [inst : Ring R] (n : ℤ) (m : ℕ), ↑(n ^ m)
 = ↑n ^ m
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The cast of `negOnePow n` to a ring equals `(-1) ^ n.natAbs`.
-/
lemma coe_negOnePow (R : Type*) [Ring R] (n : ℤ) :
    (n.negOnePow : R) = (-1 : R) ^ n.natAbs := by
  cases n with
  | ofNat n => exact cast_negOnePow_natCast R n
  | negSucc n => simp [negOnePow_def, Units.val_pow_eq_pow_val]

end Int

