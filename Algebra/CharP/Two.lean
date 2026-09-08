/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Ring.Parity

/-!
# Lemmas about rings of characteristic two

This file contains results about `CharP R 2`, in the `CharTwo` namespace.

The lemmas in this file with a `_sq` suffix are just special cases of the `_pow_char` lemmas
elsewhere, with a shorter name for ease of discovery, and no need for a `[Fact (Prime 2)]` argument.
-/

public section

-- TODO: `assert_not_exists Field` is added because of `Mathlib.GroupTheory.OrderOfElement`.
-- If you want to import fields here, please refactor the import hierarchy for
-- `Mathlib.GroupTheory.OrderOfElement`.
assert_not_exists Algebra LinearMap Field

variable {R ι : Type*}

namespace CharTwo

section AddMonoidWithOne

variable [AddMonoidWithOne R]

/-- The only hypotheses required to build a `CharP R 2` instance are `1 ≠ 0` and `2 = 0`. -/
/-
**CharTwo.of_one_ne_zero_of_two_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `CharTwo`。
形式化陈述：of_one_ne_zero_of_two_eq_zero (h₁ : (1 : R) != 0) (h₂ : (2 : R) = 0) : Cha
rP R 2 where cast_eq_zero_iff n
参数：h₁ : (1 : R) != 0；h₂ : (2 : R) = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Nat.even_or_odd`：even_or_odd (n : Nat) : Even n ∨ Odd n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Even.two_dvd`：∀ {α : Type u_2} [inst : Semiring α] {a : α}, Even a → 2 ∣
 a
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `natCast_eq_zero_of_even_of_two_eq_zero`：natCast_eq_zero_of_even_of_two_e
q_zero {n : Nat} (hn : Even n) (h : (2 : R) = 0) : (n : R) = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Odd.not_two_dvd_nat`：∀ {n : ℕ}, Odd n → ¬2 ∣ n
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `natCast_eq_one_of_odd_of_two_eq_zero`：natCast_eq_one_of_odd_of_two_eq_ze
ro {n : Nat} (hn : Odd n) (h : (2 : R) = 0) : (n : R) = 1

--- 原说明 ---
The only hypotheses required to build a `CharP R 2` instance are `1 ≠ 0` and `2 
= 0`.
-/
theorem of_one_ne_zero_of_two_eq_zero (h₁ : (1 : R) ≠ 0) (h₂ : (2 : R) = 0) : CharP R 2 where
  cast_eq_zero_iff n := by
    obtain hn | hn := Nat.even_or_odd n
    · simp_rw [hn.two_dvd, iff_true]
      exact natCast_eq_zero_of_even_of_two_eq_zero hn h₂
    · simp_rw [hn.not_two_dvd_nat, iff_false]
      rwa [natCast_eq_one_of_odd_of_two_eq_zero hn h₂]

variable [CharP R 2]

@[scoped simp]
/-
**CharTwo.two_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `CharTwo`。
形式化陈述：two_eq_zero : (2 : R) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_two`：cast_two [NatCast R] : ((2 : Nat) : R) = (2 : R)
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
-/
theorem two_eq_zero : (2 : R) = 0 := by
  rw [← Nat.cast_two, CharP.cast_eq_zero]
/-
**CharTwo.natCast_eq_ite** 是 Mathlib 中的一个定理，位于命名空间 `CharTwo`。
形式化陈述：natCast_eq_ite (n : Nat) : (n : R) = if Even n then 0 else 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
· 使用定理 `CharTwo.two_eq_zero`：two_eq_zero : (2 : R) = 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem natCast_eq_ite (n : ℕ) : (n : R) = if Even n then 0 else 1 := by
  induction n <;> aesop (add simp [one_add_one_eq_two])

@[simp]
/-
**CharTwo.range_natCast** 是 Mathlib 中的一个定理，位于命名空间 `CharTwo`。
形式化陈述：range_natCast : Set.range ((↑) : Nat -> R) = {0, 1}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CharTwo.natCast_eq_ite`：natCast_eq_ite (n : Nat) : (n : R) = if Even n t
hen 0 else 1
· 使用定理 `Set.range_ite_const`：range_ite_const {p : α -> Prop} [DecidablePred p] {
x y : β} (hp : exists a, p a) (hn : exists a, ¬ p a) : Set.range (fun a => if p 
a then x …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem range_natCast : Set.range ((↑) : ℕ → R) = {0, 1} := by
  rw [funext natCast_eq_ite, Set.range_ite_const]
  · use 0; simp
  · use 1; simp

variable (R) in
/-
**CharTwo.natCast_cases** 是 Mathlib 中的一个定理，位于命名空间 `CharTwo`。
形式化陈述：natCast_cases (n : Nat) : (n : R) = 0 ∨ (n : R) = 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `CharTwo.range_natCast`：range_natCast : Set.range ((↑) : Nat -> R) = {0, 
1}
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
theorem natCast_cases (n : ℕ) : (n : R) = 0 ∨ (n : R) = 1 :=
  range_natCast.le (Set.mem_range_self _)
/-
**CharTwo.natCast_eq_mod** 是 Mathlib 中的一个定理，位于命名空间 `CharTwo`。
形式化陈述：natCast_eq_mod (n : Nat) : (n : R) = (n % 2 : Nat)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CharTwo.natCast_eq_ite`：natCast_eq_ite (n : Nat) : (n : R) = if Even n t
hen 0 else 1
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.mod_mod_of_dvd`：∀ {c b : ℕ} (a : ℕ), c ∣ b → a % b % c = a % c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem natCast_eq_mod (n : ℕ) : (n : R) = (n % 2 : ℕ) := by
  simp [natCast_eq_ite, Nat.even_iff]

@[scoped simp]
/-
**CharTwo.ofNat_eq_mod** 是 Mathlib 中的一个定理，位于命名空间 `CharTwo`。
形式化陈述：ofNat_eq_mod (n : Nat) [n.AtLeastTwo] : (OfNat.ofNat n : R) = (ofNat(n) % 
2 : Nat)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CharTwo.natCast_eq_mod`：natCast_eq_mod (n : Nat) : (n : R) = (n % 2 : Na
t)
-/
theorem ofNat_eq_mod (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : R) = (ofNat(n) % 2 : ℕ) :=
  natCast_eq_mod n
/-
**CharTwo.** 是 Mathlib 中的一个示例，位于命名空间 `CharTwo`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : (37 : R) = 1 := by simp

end AddMonoidWithOne

section Semiring

variable [Semiring R] [CharP R 2]

@[scoped simp]
/-
**CharTwo.add_self_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `CharTwo`。
形式化陈述：add_self_eq_zero (x : R) : x + x = 0
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `CharTwo.two_eq_zero`：two_eq_zero : (2 : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem add_self_eq_zero (x : R) : x + x = 0 := by rw [← two_mul x, two_eq_zero, zero_mul]

@[scoped simp]
/-
**CharTwo.two_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `CharTwo`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [CharP R 2] (x : R), 2 • x = 0
参数：x : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `two_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 2 • a = a + a
· 使用定理 `CharTwo.add_self_eq_zero`：add_self_eq_zero (x : R) : x + x = 0
-/
protected theorem two_nsmul (x : R) : 2 • x = 0 := by rw [two_nsmul, add_self_eq_zero]

@[scoped simp]
/-
**CharTwo.add_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `CharTwo`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [CharP R 2] (a b : R), a + (a + b) = 
b
参数：a b : R；a + b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `CharTwo.add_self_eq_zero`：add_self_eq_zero (x : R) : x + x = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
protected theorem add_cancel_left (a b : R) : a + (a + b) = b := by
  rw [← add_assoc, add_self_eq_zero, zero_add]

@[scoped simp]
/-
**CharTwo.add_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `CharTwo`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [CharP R 2] (a b : R), a + b + b = a
参数：a b : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `CharTwo.add_self_eq_zero`：add_self_eq_zero (x : R) : x + x = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
protected theorem add_cancel_right (a b : R) : a + b + b = a := by
  rw [add_assoc, add_self_eq_zero, add_zero]

end Semiring

section Ring

variable [Ring R] [CharP R 2]

@[scoped simp]
/-
**CharTwo.neg_eq** 是 Mathlib 中的一个定理，位于命名空间 `CharTwo`。
形式化陈述：neg_eq (x : R) : -x = x
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_eq_iff_add_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
-a = b ↔ a + b = 0
· 使用定理 `CharTwo.add_self_eq_zero`：add_self_eq_zero (x : R) : x + x = 0
-/
theorem neg_eq (x : R) : -x = x := by
  rw [neg_eq_iff_add_eq_zero, add_self_eq_zero]
/-
**CharTwo.neg_eq'** 是 Mathlib 中的一个定理，位于命名空间 `CharTwo`。
形式化陈述：neg_eq' : Neg.neg = (id : R -> R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CharTwo.neg_eq`：neg_eq (x : R) : -x = x
-/
theorem neg_eq' : Neg.neg = (id : R → R) :=
  funext neg_eq

@[scoped simp]
/-
**CharTwo.sub_eq_add** 是 Mathlib 中的一个定理，位于命名空间 `CharTwo`。
形式化陈述：sub_eq_add (x y : R) : x - y = x + y
参数：x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `CharTwo.neg_eq`：neg_eq (x : R) : -x = x
-/
theorem sub_eq_add (x y : R) : x - y = x + y := by rw [sub_eq_add_neg, neg_eq]
/-
**CharTwo.add_eq_iff_eq_add** 是 Mathlib 中的一个定理，位于命名空间 `CharTwo`。
形式化陈述：add_eq_iff_eq_add {a b c : R} : a + b = c ↔ a = c + b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_iff_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a -
 b = c ↔ a = c + b
· 使用定理 `CharTwo.sub_eq_add`：sub_eq_add (x y : R) : x - y = x + y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem add_eq_iff_eq_add {a b c : R} : a + b = c ↔ a = c + b := by
  rw [← sub_eq_iff_eq_add, sub_eq_add]
/-
**CharTwo.eq_add_iff_add_eq** 是 Mathlib 中的一个定理，位于命名空间 `CharTwo`。
形式化陈述：eq_add_iff_add_eq {a b c : R} : a = b + c ↔ a + c = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_sub_iff_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a =
 b - c ↔ a + c = b
· 使用定理 `CharTwo.sub_eq_add`：sub_eq_add (x y : R) : x - y = x + y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eq_add_iff_add_eq {a b c : R} : a = b + c ↔ a + c = b := by
  rw [← eq_sub_iff_add_eq, sub_eq_add]

@[scoped simp]
/-
**CharTwo.two_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `CharTwo`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] [CharP R 2] (x : R), 2 • x = 0
参数：x : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `two_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 2 • a = a +
 a
· 使用定理 `CharTwo.add_self_eq_zero`：add_self_eq_zero (x : R) : x + x = 0
-/
protected theorem two_zsmul (x : R) : (2 : ℤ) • x = 0 := by
  rw [two_zsmul, add_self_eq_zero]
/-
**CharTwo.add_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `CharTwo`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] [CharP R 2] {a b : R}, a + b = 0 ↔ a = b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CharTwo.sub_eq_add`：sub_eq_add (x y : R) : x - y = x + y
· 使用定理 `sub_eq_iff_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a -
 b = c ↔ a = c + b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem add_eq_zero {a b : R} : a + b = 0 ↔ a = b := by
  rw [← CharTwo.sub_eq_add, sub_eq_iff_eq_add, zero_add]
/-
**CharTwo.intCast_eq_ite** 是 Mathlib 中的一个定理，位于命名空间 `CharTwo`。
形式化陈述：intCast_eq_ite (n : Int) : (n : R) = if Even n then 0 else 1
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.eq_nat_or_neg`：∀ (a : ℤ), ∃ n, a = ↑n ∨ a = -↑n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `CharTwo.natCast_eq_ite`：natCast_eq_ite (n : Nat) : (n : R) = if Even n t
hen 0 else 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `CharTwo.neg_eq`：neg_eq (x : R) : -x = x
-/
theorem intCast_eq_ite (n : ℤ) : (n : R) = if Even n then 0 else 1 := by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg <;> simpa using natCast_eq_ite n

@[simp]
/-
**CharTwo.range_intCast** 是 Mathlib 中的一个定理，位于命名空间 `CharTwo`。
形式化陈述：range_intCast : Set.range ((↑) : Int -> R) = {0, 1}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CharTwo.intCast_eq_ite`：intCast_eq_ite (n : Int) : (n : R) = if Even n t
hen 0 else 1
· 使用定理 `Set.range_ite_const`：range_ite_const {p : α -> Prop} [DecidablePred p] {
x y : β} (hp : exists a, p a) (hn : exists a, ¬ p a) : Set.range (fun a => if p 
a then x …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem range_intCast : Set.range ((↑) : ℤ → R) = {0, 1} := by
  rw [funext intCast_eq_ite, Set.range_ite_const]
  · use 0; simp
  · use 1; simp

variable (R) in
/-
**CharTwo.intCast_cases** 是 Mathlib 中的一个定理，位于命名空间 `CharTwo`。
形式化陈述：intCast_cases (n : Int) : (n : R) = 0 ∨ (n : R) = 1
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `CharTwo.range_intCast`：range_intCast : Set.range ((↑) : Int -> R) = {0, 
1}
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
theorem intCast_cases (n : ℤ) : (n : R) = 0 ∨ (n : R) = 1 :=
  (Set.ext_iff.1 range_intCast _).1 (Set.mem_range_self _)
/-
**CharTwo.intCast_eq_mod** 是 Mathlib 中的一个定理，位于命名空间 `CharTwo`。
形式化陈述：intCast_eq_mod (n : Int) : (n : R) = (n % 2 : Int)
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CharTwo.intCast_eq_ite`：intCast_eq_ite (n : Int) : (n : R) = if Even n t
hen 0 else 1
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.emod_emod_of_dvd`：∀ (n : ℤ) {m k : ℤ}, m ∣ k → n % k % m = n % m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem intCast_eq_mod (n : ℤ) : (n : R) = (n % 2 : ℤ) := by
  simp [intCast_eq_ite, Int.even_iff]

end Ring

section CommSemiring

variable [CommSemiring R] [CharP R 2]

/-
**CharTwo.add_sq** 是 Mathlib 中的一个定理，位于命名空间 `CharTwo`。
形式化陈述：add_sq (x y : R) : (x + y) ^ 2 = x ^ 2 + y ^ 2
参数：x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `add_pow_two`：∀ {α : Type u} [inst : CommSemiring α] (a b : α), (a + b) ^
 2 = a ^ 2 + 2 * a * b + b ^ 2
· 使用定理 `CharTwo.ofNat_eq_mod`：ofNat_eq_mod (n : Nat) [n.AtLeastTwo] : (OfNat.ofN
at n : R) = (ofNat(n) % 2 : Nat)
· 使用定理 `Nat.mod_self`：∀ (n : ℕ), n % n = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem add_sq (x y : R) : (x + y) ^ 2 = x ^ 2 + y ^ 2 := by
  simp [add_pow_two]
/-
**CharTwo.add_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `CharTwo`。
形式化陈述：add_mul_self (x y : R) : (x + y) * (x + y) = x * x + y * y
参数：x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `CharTwo.add_sq`：add_sq (x y : R) : (x + y) ^ 2 = x ^ 2 + y ^ 2
-/
theorem add_mul_self (x y : R) : (x + y) * (x + y) = x * x + y * y := by
  rw [← pow_two, ← pow_two, ← pow_two, add_sq]

/-- See `frobenius` for the Frobenius map. -/
/-
**CharTwo.sqAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `CharTwo`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `frobenius` for the Frobenius map.
-/
private def sqAddMonoidHom : R →+ R where
  toFun := (· ^ 2)
  map_zero' := zero_pow two_ne_zero
  map_add' := add_sq
/-
**CharTwo.list_sum_sq** 是 Mathlib 中的一个定理，位于命名空间 `CharTwo`。
形式化陈述：list_sum_sq (l : List R) : l.sum ^ 2 = (l.map (· ^ 2)).sum
参数：l : List R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_list_sum`：∀ {M : Type u_4} {N : Type u_5} [inst : AddMonoid M] [inst
_1 : AddMonoid N] {F : Type u_8} [inst_2 : FunLike F M N]   [AddMonoidHomClass F
 M…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem list_sum_sq (l : List R) : l.sum ^ 2 = (l.map (· ^ 2)).sum :=
  map_list_sum sqAddMonoidHom _
/-
**CharTwo.list_sum_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `CharTwo`。
形式化陈述：list_sum_mul_self (l : List R) : l.sum * l.sum = (List.map (fun x => x * x
) l).sum
参数：l : List R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CharTwo.list_sum_sq`：list_sum_sq (l : List R) : l.sum ^ 2 = (l.map (· ^ 
2)).sum
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem list_sum_mul_self (l : List R) : l.sum * l.sum = (List.map (fun x => x * x) l).sum := by
  simp_rw [← pow_two, list_sum_sq]
/-
**CharTwo.multiset_sum_sq** 是 Mathlib 中的一个定理，位于命名空间 `CharTwo`。
形式化陈述：multiset_sum_sq (l : Multiset R) : l.sum ^ 2 = (l.map (· ^ 2)).sum
参数：l : Multiset R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_multiset_sum`：∀ {F : Type u_1} {M : Type u_5} {N : Type u_6} [inst :
 AddCommMonoid M] [inst_1 : AddCommMonoid N]   [inst_2 : FunLike F M N] [AddMono
idHomC…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem multiset_sum_sq (l : Multiset R) : l.sum ^ 2 = (l.map (· ^ 2)).sum :=
  map_multiset_sum sqAddMonoidHom _
/-
**CharTwo.multiset_sum_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `CharTwo`。
形式化陈述：multiset_sum_mul_self (l : Multiset R) : l.sum * l.sum = (Multiset.map (fu
n x => x * x) l).sum
参数：l : Multiset R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CharTwo.multiset_sum_sq`：multiset_sum_sq (l : Multiset R) : l.sum ^ 2 = 
(l.map (· ^ 2)).sum
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem multiset_sum_mul_self (l : Multiset R) :
    l.sum * l.sum = (Multiset.map (fun x => x * x) l).sum := by simp_rw [← pow_two, multiset_sum_sq]
/-
**CharTwo.sum_sq** 是 Mathlib 中的一个定理，位于命名空间 `CharTwo`。
形式化陈述：sum_sq (s : Finset ι) (f : ι -> R) : (∑ i in s, f i) ^ 2 = ∑ i in s, f i ^
 2
参数：s : Finset ι；f : ι -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem sum_sq (s : Finset ι) (f : ι → R) : (∑ i ∈ s, f i) ^ 2 = ∑ i ∈ s, f i ^ 2 :=
  map_sum sqAddMonoidHom _ _
/-
**CharTwo.sum_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `CharTwo`。
形式化陈述：sum_mul_self (s : Finset ι) (f : ι -> R) : ((∑ i in s, f i) * ∑ i in s, f 
i) = ∑ i in s, f i * f i
参数：s : Finset ι；f : ι -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CharTwo.sum_sq`：sum_sq (s : Finset ι) (f : ι -> R) : (∑ i in s, f i) ^ 2
 = ∑ i in s, f i ^ 2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_mul_self (s : Finset ι) (f : ι → R) :
    ((∑ i ∈ s, f i) * ∑ i ∈ s, f i) = ∑ i ∈ s, f i * f i := by simp_rw [← pow_two, sum_sq]

end CommSemiring

section CommRing

variable [CommRing R] [CharP R 2] [NoZeroDivisors R]

/-
**CharTwo.sq_injective** 是 Mathlib 中的一个定理，位于命名空间 `CharTwo`。
形式化陈述：sq_injective : Function.Injective fun x : R => x ^ 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CharTwo.add_eq_zero`：∀ {R : Type u_1} [inst : Ring R] [CharP R 2] {a b :
 R}, a + b = 0 ↔ a = b
· 使用定理 `pow_eq_zero_iff`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] {a : M₀} {
n : ℕ} [IsReduced M₀], n ≠ 0 → (a ^ n = 0 ↔ a = 0)
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CharTwo.add_sq`：add_sq (x y : R) : (x + y) ^ 2 = x ^ 2 + y ^ 2
-/
theorem sq_injective : Function.Injective fun x : R ↦ x ^ 2 := by
  intro x y h
  rwa [← CharTwo.add_eq_zero, ← add_sq, pow_eq_zero_iff two_ne_zero, CharTwo.add_eq_zero] at h

@[scoped simp]
/-
**CharTwo.sq_inj** 是 Mathlib 中的一个定理，位于命名空间 `CharTwo`。
形式化陈述：sq_inj {x y : R} : x ^ 2 = y ^ 2 ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `CharTwo.sq_injective`：sq_injective : Function.Injective fun x : R => x ^
 2
-/
theorem sq_inj {x y : R} : x ^ 2 = y ^ 2 ↔ x = y :=
  sq_injective.eq_iff

end CommRing

@[deprecated (since := "2026-02-05")]
alias CommRing.sq_injective := sq_injective

@[deprecated (since := "2026-02-05")]
alias CommRing.sq_inj := sq_inj

end CharTwo

section ringChar

variable [Ring R]

/-
**neg_one_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：neg_one_eq_one_iff [Nontrivial R] : (-1 : R) = 1 ↔ ringChar R = 2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.dvd_prime`：dvd_prime {p m : Nat} (pp : Prime p) : m ∣ p ↔ m = 1 ∨ m 
= p
· 使用定理 `Nat.prime_two`：prime_two : Prime 2
· 使用引理 `ringChar.dvd`：dvd {x : Nat} (hx : (x : R) = 0) : ringChar R ∣ x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `CharP.ringChar_ne_one`：ringChar_ne_one [Nontrivial R] : ringChar R != 1
· 使用定理 `CharTwo.neg_eq`：neg_eq (x : R) : -x = x
· 使用引理 `ringChar.of_eq`：of_eq {p : Nat} (h : ringChar R = p) : CharP R p
-/
theorem neg_one_eq_one_iff [Nontrivial R] : (-1 : R) = 1 ↔ ringChar R = 2 := by
  refine ⟨fun h => ?_, fun h => @CharTwo.neg_eq _ _ (ringChar.of_eq h) 1⟩
  rw [eq_comm, ← sub_eq_zero, sub_neg_eq_add, ← Nat.cast_one, ← Nat.cast_add] at h
  exact ((Nat.dvd_prime Nat.prime_two).mp (ringChar.dvd h)).resolve_left CharP.ringChar_ne_one

end ringChar

