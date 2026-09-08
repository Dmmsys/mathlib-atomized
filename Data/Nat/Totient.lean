/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Nat.Cast.Field
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Factorization.Induction
public import Mathlib.Data.Nat.Periodic

/-!
# Euler's totient function

This file defines [Euler's totient function](https://en.wikipedia.org/wiki/Euler's_totient_function)
`Nat.totient n` which counts the number of naturals less than `n` that are coprime with `n`.
We prove the divisor sum formula, namely that `n` equals `φ` summed over the divisors of `n`. See
`sum_totient`. We also prove two lemmas to help compute totients, namely `totient_mul` and
`totient_prime_pow`.
-/

@[expose] public section

assert_not_exists Algebra LinearMap

open Finset

namespace Nat

/-- Euler's totient function. This counts the number of naturals strictly less than `n` which are
coprime with `n`. -/
/-
**Nat.totient** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：totient (n : Nat) : Nat
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Euler's totient function. This counts the number of naturals strictly less than 
`n` which are
coprime with `n`.
-/
def totient (n : ℕ) : ℕ := #{a ∈ range n | n.Coprime a}

@[inherit_doc]
scoped notation "φ" => Nat.totient

@[simp]
/-
**Nat.totient_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：totient_zero : φ 0 = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem totient_zero : φ 0 = 0 :=
  rfl

@[simp]
/-
**Nat.totient_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：totient_one : φ 1 = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem totient_one : φ 1 = 1 := rfl
/-
**Nat.totient_eq_card_coprime** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：totient_eq_card_coprime (n : Nat) : φ n = #{a in range n | n.Coprime a}
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem totient_eq_card_coprime (n : ℕ) : φ n = #{a ∈ range n | n.Coprime a} := rfl

/-- A characterisation of `Nat.totient` that avoids `Finset`. -/
/-
**Nat.totient_eq_card_lt_and_coprime** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：totient_eq_card_lt_and_coprime (n : Nat) : φ n = Nat.card { m | m < n ∧ n.
Coprime m }
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.totient_eq_card_coprime`：totient_eq_card_coprime (n : Nat) : φ n = #
{a in range n | n.Coprime a}
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s

--- 原说明 ---
A characterisation of `Nat.totient` that avoids `Finset`.
-/
theorem totient_eq_card_lt_and_coprime (n : ℕ) : φ n = Nat.card { m | m < n ∧ n.Coprime m } := by
  let e : { m | m < n ∧ n.Coprime m } ≃ {x ∈ range n | n.Coprime x} :=
    { toFun := fun m => ⟨m, by simpa only [Finset.mem_filter, Finset.mem_range] using! m.property⟩
      invFun := fun m => ⟨m, by simpa only [Finset.mem_filter, Finset.mem_range] using! m.property⟩
      left_inv := fun m => by simp only [Subtype.coe_eta]
      right_inv := fun m => by simp only }
  rw [totient_eq_card_coprime, card_congr e, card_eq_fintype_card, Fintype.card_coe]
/-
**Nat.totient_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：totient_le (n : Nat) : φ n <= n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Finset.card_filter_le`：card_filter_le (s : Finset α) (p : α -> Prop) [De
cidablePred p] : #(s.filter p) <= #s
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
-/
theorem totient_le (n : ℕ) : φ n ≤ n :=
  ((range n).card_filter_le _).trans_eq (card_range n)
/-
**Nat.totient_lt** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：totient_lt (n : Nat) (hn : 1 < n) : φ n < n
参数：n : Nat；hn : 1 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `Finset.card_lt_card`：∀ {α : Type u_1} {s t : Finset α}, s ⊂ t → s.card <
 t.card
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.filter_ssubset`：∀ {α : Type u_1} {p : α → Prop} [inst : Decidable
Pred p] {s : Finset α}, Finset.filter p s ⊂ s ↔ ∃ x ∈ s, ¬p x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `pos_of_gt`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], a < b → 0 < b
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
-/
theorem totient_lt (n : ℕ) (hn : 1 < n) : φ n < n :=
  (card_lt_card (filter_ssubset.2 ⟨0, by simp [hn.ne', pos_of_gt hn]⟩)).trans_eq (card_range n)

@[simp]
/-
**Nat.totient_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n : ℕ}, n.totient = 0 ↔ n = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.gcd_comm`：∀ (m n : ℕ), m.gcd n = n.gcd m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.gcd_rec`：∀ (m n : ℕ), m.gcd n = (n % m).gcd m
· 使用定理 `Nat.gcd_one_right`：∀ (n : ℕ), n.gcd 1 = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem totient_eq_zero : ∀ {n : ℕ}, φ n = 0 ↔ n = 0
  | 0 => by decide
  | n + 1 =>
    suffices ∃ x < n + 1, (n + 1).gcd x = 1 by simpa [totient, filter_eq_empty_iff]
    ⟨1 % (n + 1), mod_lt _ n.succ_pos, by rw [gcd_comm, ← gcd_rec, gcd_one_right]⟩
/-
**Nat.totient_pos** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {n : ℕ}, 0 < n.totient ↔ 0 < n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem totient_pos {n : ℕ} : 0 < φ n ↔ 0 < n := by simp [pos_iff_ne_zero]
/-
**Nat.neZero_totient** 是 Mathlib 中的一个实例，位于命名空间 `Nat`。
形式化陈述：neZero_totient {n : Nat} [NeZero n] : NeZero n.totient
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.totient_pos`：∀ {n : ℕ}, 0 < n.totient ↔ 0 < n
· 使用定理 `NeZero.pos`：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] :
 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
instance neZero_totient {n : ℕ} [NeZero n] : NeZero n.totient :=
  ⟨(totient_pos.mpr <| NeZero.pos n).ne'⟩
/-
**Nat.filter_coprime_Ico_eq_totient** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：filter_coprime_Ico_eq_totient (a n : Nat) : #{x in Ico n (n + a) | a.Copri
me x} = totient a
参数：a n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.totient.eq_1`：∀ (n : ℕ), n.totient = {a ∈ Finset.range n | n.Coprime
 a}.card
· 使用定理 `Nat.filter_Ico_card_eq_of_periodic`：filter_Ico_card_eq_of_periodic (n a 
: Nat) (p : Nat -> Prop) [DecidablePred p] (pp : Periodic p a) : ((Ico n (n + a)
).filter p).card = a.cou…
· 使用定理 `Nat.periodic_coprime`：periodic_coprime (a : Nat) : Periodic (Coprime a) 
a
· 使用定理 `Nat.count_eq_card_filter_range`：count_eq_card_filter_range (n : Nat) : c
ount p n = #{x in range n | p x}
-/
theorem filter_coprime_Ico_eq_totient (a n : ℕ) :
    #{x ∈ Ico n (n + a) | a.Coprime x} = totient a := by
  rw [totient, filter_Ico_card_eq_of_periodic, count_eq_card_filter_range]
  exact periodic_coprime a
/-
**Nat.Ico_filter_coprime_le** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：Ico_filter_coprime_le {a : Nat} (k n : Nat) (a_ne_zero : a != 0) : #{x in 
Ico k (k + n) | a.Coprime x} <= totient a * (n / a + 1)
参数：k n : Nat；a_ne_zero : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.mod_add_div`：∀ (m k : ℕ), m % k + k * (m / k) = m
· 使用定理 `Nat.filter_coprime_Ico_eq_totient`：filter_coprime_Ico_eq_totient (a n : 
Nat) : #{x in Ico n (n + a) | a.Coprime x} = totient a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.filter.congr_simp`：∀ {α : Type u_1} (p p_1 : α → Prop),   p = p_1
 →     ∀ {inst : DecidablePred p} [inst_1 : DecidablePred p_1] (s s_1 : Finset α
),       s = s…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `Finset.filter_subset_filter`：∀ {α : Type u_1} (p : α → Prop) [inst : Dec
idablePred p] {s t : Finset α}, s ⊆ t → Finset.filter p s ⊆ Finset.filter p t
· 使用定理 `Finset.Ico_subset_Ico`：Ico_subset_Ico (ha : a₂ <= a₁) (hb : b₁ <= b₂) : 
Ico a₁ b₁ subseteq Ico a₂ b₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.Ico_subset_Ico_union_Ico`：Ico_subset_Ico_union_Ico {a b c : α} : 
Ico a c subseteq Ico a b union Ico b c
· 使用定理 `Finset.filter_union`：filter_union (s₁ s₂ : Finset α) : (s₁ union s₂).fil
ter p = s₁.filter p union s₂.filter p
· 使用定理 `Finset.card_union_le`：card_union_le (s t : Finset α) : #(s union t) <= #
s + #t
· 使用定理 `Nat.mul_add_one`：∀ (n m : ℕ), n * (m + 1) = n * m + n
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
-/
theorem Ico_filter_coprime_le {a : ℕ} (k n : ℕ) (a_ne_zero : a ≠ 0) :
    #{x ∈ Ico k (k + n) | a.Coprime x} ≤ totient a * (n / a + 1) := by
  conv_lhs => rw [← Nat.mod_add_div n a]
  induction n / a with
  | zero =>
    rw [← filter_coprime_Ico_eq_totient a k]
    simp only [add_zero, mul_one, mul_zero, zero_add]
    gcongr
    exact le_of_lt (mod_lt n (pos_iff_ne_zero.mpr a_ne_zero))
  | succ i ih => ?_
  simp only [mul_succ]
  simp_rw [← add_assoc] at ih ⊢
  calc
    #{x ∈ Ico k (k + n % a + a * i + a) | a.Coprime x}
      ≤ #{x ∈ Ico k (k + n % a + a * i) ∪
        Ico (k + n % a + a * i) (k + n % a + a * i + a) | a.Coprime x} := by
      gcongr
      apply Ico_subset_Ico_union_Ico
    _ ≤ #{x ∈ Ico k (k + n % a + a * i) | a.Coprime x} + a.totient := by
      rw [filter_union, ← filter_coprime_Ico_eq_totient a (k + n % a + a * i)]
      apply card_union_le
    _ ≤ a.totient * i + a.totient + a.totient := by grw [← mul_add_one, ih]

open ZMod

/-- Note this takes an explicit `Fintype ((ZMod n)ˣ)` argument to avoid trouble with instance
diamonds. -/
@[simp]
/-
**Nat._root_.ZMod.card_units_eq_totient** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note this takes an explicit `Fintype ((ZMod n)ˣ)` argument to avoid trouble with
 instance
diamonds.
-/
theorem _root_.ZMod.card_units_eq_totient (n : ℕ) [NeZero n] [Fintype (ZMod n)ˣ] :
    Fintype.card (ZMod n)ˣ = φ n :=
  calc
    Fintype.card (ZMod n)ˣ = Fintype.card { x : ZMod n // x.val.Coprime n } :=
      Fintype.card_congr ZMod.unitsEquivCoprime
    _ = φ n := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := exists_eq_succ_of_ne_zero NeZero.out
      simp only [totient, Finset.card_eq_sum_ones, Fintype.card_subtype, Finset.sum_filter, ←
        Fin.sum_univ_eq_sum_range, @Nat.coprime_comm (m + 1)]
      rfl
/-
**Nat.totient_even** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：totient_even {n : Nat} (hn : 2 < n) : Even n.totient
参数：hn : 2 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `one_lt_two`：one_lt_two [AddLeftStrictMono α] : (1 : α) < 2
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
· 使用定理 `NeZero.of_gt`：of_gt [Preorder α] [IsBotZeroClass α] (h : a < b) : NeZero
 b
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `orderOf_units`：orderOf_units {y : Gˣ} : orderOf (y : G) = orderOf y
· 使用定理 `Units.coe_neg_one`：∀ {α : Type u} [inst : Monoid α] [inst_1 : HasDistrib
Neg α], ↑(-1) = -1
· 使用定理 `orderOf_neg_one`：orderOf_neg_one {R} [Ring R] [Nontrivial R] : orderOf (
-1 : R) = if ringChar R = 2 then 1 else 2
· 使用引理 `ringChar.eq`：eq (p : Nat) [C : CharP R p] : ringChar R = p
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `ZMod.card_units_eq_totient`：∀ (n : ℕ) [NeZero n] [inst : Fintype (ZMod n
)ˣ], Fintype.card (ZMod n)ˣ = n.totient
· 使用引理 `even_iff_two_dvd`：even_iff_two_dvd : Even a ↔ 2 ∣ a
· 使用定理 `orderOf_dvd_card`：orderOf_dvd_card : orderOf x ∣ Fintype.card G
-/
theorem totient_even {n : ℕ} (hn : 2 < n) : Even n.totient := by
  have : Fact (1 < n) := ⟨one_lt_two.trans hn⟩
  have : NeZero n := NeZero.of_gt hn
  suffices 2 = orderOf (-1 : (ZMod n)ˣ) by
    rw [← ZMod.card_units_eq_totient, even_iff_two_dvd, this]
    exact orderOf_dvd_card
  rw [← orderOf_units, Units.coe_neg_one, orderOf_neg_one, ringChar.eq (ZMod n) n, if_neg hn.ne']
/-
**Nat.totient_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：totient_mul {m n : Nat} (h : m.Coprime n) : φ (m * n) = φ m * φ n
参数：h : m.Coprime n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.mul_eq_zero`：∀ {m n : ℕ}, n * m = 0 ↔ n = 0 ∨ m = 0
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `left_ne_zero_of_mul`：left_ne_zero_of_mul : a * b != 0 -> a != 0
· 使用定理 `right_ne_zero_of_mul`：right_ne_zero_of_mul : a * b != 0 -> b != 0
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
· 使用定理 `Fintype.card_prod`：Fintype.card_prod (α β : Type*) [Fintype α] [Fintype 
β] : Fintype.card (α × β) = Fintype.card α * Fintype.card β
-/
theorem totient_mul {m n : ℕ} (h : m.Coprime n) : φ (m * n) = φ m * φ n :=
  if hmn0 : m * n = 0 then by
    rcases Nat.mul_eq_zero.1 hmn0 with h | h <;>
      simp only [totient_zero, mul_zero, zero_mul, h]
  else by
    have : NeZero (m * n) := ⟨hmn0⟩
    have : NeZero m := ⟨left_ne_zero_of_mul hmn0⟩
    have : NeZero n := ⟨right_ne_zero_of_mul hmn0⟩
    simp only [← ZMod.card_units_eq_totient]
    rw [Fintype.card_congr (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).toEquiv,
      Fintype.card_congr (@MulEquiv.prodUnits (ZMod m) (ZMod n) _ _).toEquiv, Fintype.card_prod]

/-- For `d ∣ n`, the totient of `n/d` equals the number of values `k < n` such that `gcd n k = d` -/
/-
**Nat.totient_div_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：totient_div_of_dvd {n d : Nat} (hnd : d ∣ n) : φ (n / d) = #{k in range n 
| n.gcd k = d}
参数：hnd : d ∣ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_zero_of_zero_dvd`：eq_zero_of_zero_dvd (h : 0 ∣ a) : a = 0
· 使用定理 `Nat.div_zero`：∀ (n : ℕ), n / 0 = 0
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Nat.gcd_zero_left`：∀ (y : ℕ), Nat.gcd 0 y = y
· 使用定理 `Finset.range_filter_eq`：range_filter_eq {n m : Nat} : (range n).filter (
· = m) = if m < n then {m} else ∅
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.mul_div_cancel_left`：∀ (m : ℕ) {n : ℕ}, 0 < n → n * m / n = m
· 使用引理 `Finset.card_bij`：card_bij (i : forall a in s, β) (hi : forall a ha, i a 
ha in t) (i_inj : forall a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ -> a₁ = a₂) (i_surj 
: for…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `mul_lt_mul_of_pos_left`：mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc
 : b < c) (ha : 0 < a) : a * b < a * c
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Nat.gcd_mul_left`：∀ (m n k : ℕ), (m * n).gcd (m * k) = m * n.gcd k
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
For `d ∣ n`, the totient of `n/d` equals the number of values `k < n` such that 
`gcd n k = d`
-/
theorem totient_div_of_dvd {n d : ℕ} (hnd : d ∣ n) :
    φ (n / d) = #{k ∈ range n | n.gcd k = d} := by
  rcases d.eq_zero_or_pos with (rfl | hd0); · simp [eq_zero_of_zero_dvd hnd]
  rcases hnd with ⟨x, rfl⟩
  rw [Nat.mul_div_cancel_left x hd0]
  apply Finset.card_bij fun k _ => d * k
  · simp only [mem_filter, mem_range, and_imp, Coprime]
    refine fun a ha1 ha2 => ⟨by gcongr, ?_⟩
    rw [gcd_mul_left, ha2, mul_one]
  · simp [hd0.ne']
  · simp only [mem_filter, mem_range, exists_prop, and_imp]
    intro b hb1 hb2
    have : d ∣ b := by
      rw [← hb2]
      apply gcd_dvd_right
    rcases this with ⟨q, rfl⟩
    refine ⟨q, ⟨⟨(mul_lt_mul_iff_right₀ hd0).1 hb1, ?_⟩, rfl⟩⟩
    rwa [gcd_mul_left, mul_eq_left hd0.ne'] at hb2
/-
**Nat.sum_totient** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：sum_totient (n : Nat) : n.divisors.sum φ = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Nat.divisors_zero`：divisors_zero : divisors 0 = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.sum_div_divisors`：∀ {α : Type u_1} [inst : AddCommMonoid α] (n : ℕ) 
(f : ℕ → α), ∑ d ∈ n.divisors, f (n / d) = n.divisors.sum f
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `Finset.card_eq_sum_card_fiberwise`：card_eq_sum_card_fiberwise [Decidable
Eq M] {f : ι -> M} {s : Finset ι} {t : Finset M} (H : (s : Set ι).MapsTo f t) : 
#s = ∑ b in t, #{a in s…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.mem_divisors`：mem_divisors {m : Nat} : n in divisors m ↔ n ∣ m ∧ m !
= 0
· 使用定理 `Nat.gcd_dvd_left`：∀ (m n : ℕ), m.gcd n ∣ m
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.totient_div_of_dvd`：totient_div_of_dvd {n d : Nat} (hnd : d ∣ n) : φ
 (n / d) = #{k in range n | n.gcd k = d}
· 使用定理 `Nat.dvd_of_mem_divisors`：dvd_of_mem_divisors {m : Nat} (h : n in divisor
s m) : n ∣ m
-/
theorem sum_totient (n : ℕ) : n.divisors.sum φ = n := by
  rcases n.eq_zero_or_pos with (rfl | hn)
  · simp
  rw [← sum_div_divisors n φ]
  have : n = ∑ d ∈ n.divisors, #{k ∈ range n | n.gcd k = d} := by
    nth_rw 1 [← card_range n]
    refine card_eq_sum_card_fiberwise fun x _ => mem_divisors.2 ⟨?_, hn.ne'⟩
    apply gcd_dvd_left
  nth_rw 3 [this]
  exact sum_congr rfl fun x hx => totient_div_of_dvd (dvd_of_mem_divisors hx)
/-
**Nat.sum_totient'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：sum_totient' (n : Nat) : ∑ m in range n.succ with m ∣ n, φ m = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.filter.congr_simp`：∀ {α : Type u_1} (p p_1 : α → Prop),   p = p_1
 →     ∀ {inst : DecidablePred p} [inst_1 : DecidablePred p_1] (s s_1 : Finset α
),       s = s…
· 使用定理 `Finset.range_eq_Ico`：∀ (a : ℕ), Finset.range a = Finset.Ico 0 a
· 使用定理 `Finset.sum_filter`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst 
: AddCommMonoid M] (p : ι → Prop) [inst_1 : DecidablePred p]   (f : ι → M), ∑ a 
∈ s wit…
· 使用定理 `Finset.sum_eq_sum_Ico_succ_bot`：∀ {M : Type u_2} [inst : AddCommMonoid M
] {a b : ℕ},   a < b → ∀ (f : ℕ → M), ∑ k ∈ Finset.Ico a b, f k = f a + ∑ k ∈ Fi
nset.Ico (a + 1) b, …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
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
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.sum_totient`：sum_totient (n : Nat) : n.divisors.sum φ = n
-/
theorem sum_totient' (n : ℕ) : ∑ m ∈ range n.succ with m ∣ n, φ m = n := by
  convert! sum_totient _ using 1
  simp only [Nat.divisors, sum_filter, range_eq_Ico]
  rw [sum_eq_sum_Ico_succ_bot] <;> simp

/-- When `p` is prime, then the totient of `p ^ (n + 1)` is `p ^ n * (p - 1)` -/
/-
**Nat.totient_prime_pow_succ** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：totient_prime_pow_succ {p : Nat} (hp : p.Prime) (n : Nat) : φ (p ^ (n + 1)
) = p ^ n * (p - 1)
参数：hp : p.Prime；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.totient_eq_card_coprime`：totient_eq_card_coprime (n : Nat) : φ n = #
{a in range n | n.Coprime a}
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sdiff_eq_filter`：sdiff_eq_filter (s₁ s₂ : Finset α) : s₁ \ s₂ = s
₁.filter (· ∉ s₂)
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.coprime_pow_left_iff`：coprime_pow_left_iff {n : Nat} (hn : 0 < n) (a
 b : Nat) : Nat.Coprime (a ^ n) b ↔ Nat.Coprime a b
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Nat.Prime.coprime_iff_not_dvd`：∀ {p n : ℕ}, Nat.Prime p → (p.Coprime n ↔
 ¬p ∣ n)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dvd_mul_left`：dvd_mul_left (a b : α) : a ∣ b * a
· 使用定理 `lt_of_mul_lt_mul_left`：lt_of_mul_lt_mul_left [PosMulReflectLT α] (h : a 
* b < a * c) (a0 : 0 <= a) : b < c
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Nat.pow_succ'`：∀ {m n : ℕ}, m ^ n.succ = m * m ^ n
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_left_injective₀`：mul_left_injective₀ (hb : b != 0) : Function.Inject
ive fun a => a * b
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Nat.pow_succ`：∀ (n m : ℕ), n ^ m.succ = n ^ m * n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mul_lt_mul_iff_left₀`：mul_lt_mul_iff_left₀ [MulPosStrictMono α] [MulPosR
eflectLT α] (a0 : 0 < a) : b * a < c * a ↔ b < c where mp h
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
When `p` is prime, then the totient of `p ^ (n + 1)` is `p ^ n * (p - 1)`
-/
theorem totient_prime_pow_succ {p : ℕ} (hp : p.Prime) (n : ℕ) : φ (p ^ (n + 1)) = p ^ n * (p - 1) :=
  calc
    φ (p ^ (n + 1)) = #{a ∈ range (p ^ (n + 1)) | (p ^ (n + 1)).Coprime a} :=
      totient_eq_card_coprime _
    _ = #(range (p ^ (n + 1)) \ (range (p ^ n)).image (· * p)) :=
      congr_arg card
        (by
          rw [sdiff_eq_filter]
          apply filter_congr
          simp only [mem_range, coprime_pow_left_iff n.succ_pos, mem_image, not_exists,
            hp.coprime_iff_not_dvd]
          intro a ha
          constructor
          · intro hap b h; rcases h with ⟨_, rfl⟩
            exact hap (dvd_mul_left _ _)
          · rintro h ⟨b, rfl⟩
            rw [pow_succ'] at ha
            exact h b ⟨lt_of_mul_lt_mul_left ha (zero_le _), mul_comm _ _⟩)
    _ = _ := by
      have h1 : Function.Injective (· * p) := mul_left_injective₀ hp.ne_zero
      have h2 : (range (p ^ n)).image (· * p) ⊆ range (p ^ (n + 1)) := fun a => by
        simp only [mem_image, mem_range, exists_imp]
        rintro b ⟨h, rfl⟩
        rw [Nat.pow_succ]
        exact (mul_lt_mul_iff_left₀ hp.pos).2 h
      rw [card_sdiff_of_subset h2, Finset.card_image_of_injective _ h1, card_range, card_range, ←
        one_mul (p ^ n), pow_succ', ← tsub_mul, one_mul, mul_comm]

/-- When `p` is prime, then the totient of `p ^ n` is `p ^ (n - 1) * (p - 1)` -/
/-
**Nat.totient_prime_pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：totient_prime_pow {p : Nat} (hp : p.Prime) {n : Nat} (hn : 0 < n) : φ (p ^
 n) = p ^ (n - 1) * (p - 1)
参数：hp : p.Prime；hn : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_succ_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k.succ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.totient_prime_pow_succ`：totient_prime_pow_succ {p : Nat} (hp : p.Pri
me) (n : Nat) : φ (p ^ (n + 1)) = p ^ n * (p - 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
When `p` is prime, then the totient of `p ^ n` is `p ^ (n - 1) * (p - 1)`
-/
theorem totient_prime_pow {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : 0 < n) :
    φ (p ^ n) = p ^ (n - 1) * (p - 1) := by
  rcases exists_eq_succ_of_ne_zero (pos_iff_ne_zero.1 hn) with ⟨m, rfl⟩
  exact totient_prime_pow_succ hp _
/-
**Nat.totient_prime** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：totient_prime {p : Nat} (hp : p.Prime) : φ p = p - 1
参数：hp : p.Prime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Nat.totient_prime_pow`：totient_prime_pow {p : Nat} (hp : p.Prime) {n : N
at} (hn : 0 < n) : φ (p ^ n) = p ^ (n - 1) * (p - 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem totient_prime {p : ℕ} (hp : p.Prime) : φ p = p - 1 := by
  rw [← pow_one p, totient_prime_pow hp] <;> simp
/-
**Nat.totient_eq_iff_prime** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：totient_eq_iff_prime {p : Nat} (hp : 0 < p) : p.totient = p - 1 ↔ p.Prime
参数：hp : 0 < p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.succ_le_iff`：∀ {m n : ℕ}, m.succ ≤ n ↔ m < n
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `Nat.totient_one`：totient_one : φ 1 = 1
· 使用定理 `Nat.prime_of_coprime`：prime_of_coprime (n : Nat) (h1 : 1 < n) (h : foral
l m < n, m != 0 -> n.Coprime m) : Prime n
· 使用定理 `Finset.filter_card_eq`：∀ {α : Type u_1} {s : Finset α} {p : α → Prop} [i
nst : DecidablePred p],   (Finset.filter p s).card = s.card → ∀ x ∈ s, p x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_Ico`：∀ (a b : ℕ), (Finset.Ico a b).card = b - a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Nat.not_coprime_of_dvd_of_dvd`：∀ {d m n : ℕ}, 1 < d → d ∣ m → d ∣ n → ¬m
.Coprime n
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
· 使用定理 `Finset.filter_insert`：filter_insert (a : α) (s : Finset α) : (insert a s
).filter p = if p a then insert a (s.filter p) else s.filter p
· 使用引理 `Finset.insert_Ico_add_one_left_eq_Ico`：insert_Ico_add_one_left_eq_Ico (h
 : a < b) : insert a (Ico (a + 1) b) = Ico a b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Finset.range_eq_Ico`：∀ (a : ℕ), Finset.range a = Finset.Ico 0 a
· 使用定理 `Nat.totient_eq_card_coprime`：totient_eq_card_coprime (n : Nat) : φ n = #
{a in range n | n.Coprime a}
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_Ico`：mem_Ico : x in Ico a b ↔ a <= x ∧ x < b
· 使用定理 `Nat.totient_prime`：totient_prime {p : Nat} (hp : p.Prime) : φ p = p - 1
-/
theorem totient_eq_iff_prime {p : ℕ} (hp : 0 < p) : p.totient = p - 1 ↔ p.Prime := by
  refine ⟨fun h => ?_, totient_prime⟩
  replace hp : 1 < p := by
    apply lt_of_le_of_ne
    · rwa [succ_le_iff]
    · rintro rfl
      rw [totient_one, tsub_self] at h
      exact one_ne_zero h
  rw [totient_eq_card_coprime, range_eq_Ico, ← Finset.insert_Ico_add_one_left_eq_Ico hp.le,
    Finset.filter_insert, if_neg (not_coprime_of_dvd_of_dvd hp (dvd_refl p) (dvd_zero p)),
    ← Nat.card_Ico 1 p] at h
  refine
    p.prime_of_coprime hp fun n hn hnz => Finset.filter_card_eq h n <| Finset.mem_Ico.mpr ⟨?_, hn⟩
  lia
/-
**Nat.card_units_zmod_lt_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：card_units_zmod_lt_sub_one {p : Nat} (hp : 1 < p) [Fintype (ZMod p)ˣ] : Fi
ntype.card (ZMod p)ˣ <= p - 1
参数：hp : 1 < p；ZMod p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `pos_of_gt`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], a < b → 0 < b
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.card_units_eq_totient`：∀ (n : ℕ) [NeZero n] [inst : Fintype (ZMod n
)ˣ], Fintype.card (ZMod n)ˣ = n.totient
· 使用定理 `Nat.le_sub_one_of_lt`：∀ {a b : ℕ}, a < b → a ≤ b - 1
· 使用定理 `Nat.totient_lt`：totient_lt (n : Nat) (hn : 1 < n) : φ n < n
-/
theorem card_units_zmod_lt_sub_one {p : ℕ} (hp : 1 < p) [Fintype (ZMod p)ˣ] :
    Fintype.card (ZMod p)ˣ ≤ p - 1 := by
  have : NeZero p := ⟨(pos_of_gt hp).ne'⟩
  rw [ZMod.card_units_eq_totient p]
  exact Nat.le_sub_one_of_lt (Nat.totient_lt p hp)

set_option backward.isDefEq.respectTransparency false in
/-
**Nat.prime_iff_card_units** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prime_iff_card_units (p : Nat) [Fintype (ZMod p)ˣ] : p.Prime ↔ Fintype.car
d (ZMod p)ˣ = p - 1
参数：p : Nat；ZMod p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_neZero`：eq_zero_or_neZero (a : R) : a = 0 ∨ NeZero a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.card_units_eq_totient`：∀ (n : ℕ) [NeZero n] [inst : Fintype (ZMod n
)ˣ], Fintype.card (ZMod n)ˣ = n.totient
· 使用定理 `Nat.totient_eq_iff_prime`：totient_eq_iff_prime {p : Nat} (hp : 0 < p) : 
p.totient = p - 1 ↔ p.Prime
· 使用定理 `NeZero.pos`：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] :
 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem prime_iff_card_units (p : ℕ) [Fintype (ZMod p)ˣ] :
    p.Prime ↔ Fintype.card (ZMod p)ˣ = p - 1 := by
  rcases eq_zero_or_neZero p with rfl | hp
  · simp [ZMod, not_prime_zero, zero_tsub]
  rw [ZMod.card_units_eq_totient, Nat.totient_eq_iff_prime <| NeZero.pos p]

@[simp]
/-
**Nat.totient_two** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：totient_two : φ 2 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.totient_prime`：totient_prime {p : Nat} (hp : p.Prime) : φ p = p - 1
· 使用定理 `Nat.prime_two`：prime_two : Prime 2
-/
theorem totient_two : φ 2 = 1 :=
  (totient_prime prime_two).trans rfl

/-- Euler's totient function is only odd at `1` or `2`. -/
/-
**Nat.odd_totient_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：odd_totient_iff {n : Nat} : Odd (φ n) ↔ n = 1 ∨ n = 2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Nat.totient_two`：totient_two : φ 2 = 1
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Nat.Simproc.add_eq_gt`：∀ (a : ℕ) {b c : ℕ}, b > c → (a + b = c) = False
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
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
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α

--- 原说明 ---
Euler's totient function is only odd at `1` or `2`.
-/
theorem odd_totient_iff {n : ℕ} :
    Odd (φ n) ↔ n = 1 ∨ n = 2 := by
  rcases n with _ | _ | _ | _ <;> simp [Nat.totient_even]
/-
**Nat.totient_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：totient_eq_one_iff : forall {n : Nat}, n.totient = 1 ↔ n = 1 ∨ n = 2 | 0 =
> by simp | 1 => by simp | 2 => by simp | n + 3 => by have : 3 <= n + 3
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.totient_two`：totient_two : φ 2 = 1
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `le_add_self`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ b + a
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Nat.not_even_one`：¬Even 1
· 使用定理 `Nat.totient_even`：totient_even {n : Nat} (hn : 2 < n) : Even n.totient
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem totient_eq_one_iff : ∀ {n : ℕ}, n.totient = 1 ↔ n = 1 ∨ n = 2
  | 0 => by simp
  | 1 => by simp
  | 2 => by simp
  | n + 3 => by
    have : 3 ≤ n + 3 := le_add_self
    simp only [succ_succ_ne_one, false_or]
    exact ⟨fun h => not_even_one.elim <| h ▸ totient_even this, by rintro ⟨⟩⟩
/-
**Nat.dvd_two_of_totient_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：dvd_two_of_totient_le_one {a : Nat} (han : 0 < a) (ha : a.totient <= 1) : 
a ∣ 2
参数：han : 0 < a；ha : a.totient <= 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.totient_eq_one_iff`：totient_eq_one_iff : forall {n : Nat}, n.totient
 = 1 ↔ n = 1 ∨ n = 2 | 0 => by simp | 1 => by simp | 2 => by simp | n + 3 => by 
have : 3 <= …
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.totient_pos`：∀ {n : ℕ}, 0 < n.totient ↔ 0 < n
· 使用定理 `Mathlib.Meta.NormNum.isNat_dvd_true`：∀ {a b a' b' : ℕ}, Mathlib.Meta.Nor
mNum.IsNat a a' → Mathlib.Meta.NormNum.IsNat b b' → b'.mod a' = 0 → a ∣ b
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem dvd_two_of_totient_le_one {a : ℕ} (han : 0 < a) (ha : a.totient ≤ 1) : a ∣ 2 := by
  rcases totient_eq_one_iff.mp <| le_antisymm ha <| totient_pos.2 han with rfl | rfl <;> norm_num
/-
**Nat.odd_totient_iff_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：odd_totient_iff_eq_one {n : Nat} : Odd (φ n) ↔ φ n = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem odd_totient_iff_eq_one {n : ℕ} :
    Odd (φ n) ↔ φ n = 1 := by
  simp [Nat.odd_totient_iff, Nat.totient_eq_one_iff]

/-- `Nat.totient m` and `Nat.totient n` are coprime iff one of them is 1. -/
/-
**Nat.totient_coprime_totient_iff** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：totient_coprime_totient_iff (m n : Nat) : (φ m).Coprime (φ n) ↔ (m = 1 ∨ m
 = 2) ∨ (n = 1 ∨ n = 2)
参数：m n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.not_coprime_of_dvd_of_dvd`：∀ {d m n : ℕ}, 1 < d → d ∣ m → d ∣ n → ¬m
.Coprime n
· 使用引理 `one_lt_two`：one_lt_two [AddLeftStrictMono α] : (1 : α) < 2
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
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Nat.coprime_one_left`：∀ (n : ℕ), Nat.Coprime 1 n
· 使用定理 `Nat.coprime_one_right`：∀ (n : ℕ), n.Coprime 1

--- 原说明 ---
`Nat.totient m` and `Nat.totient n` are coprime iff one of them is 1.
-/
theorem totient_coprime_totient_iff (m n : ℕ) :
    (φ m).Coprime (φ n) ↔ (m = 1 ∨ m = 2) ∨ (n = 1 ∨ n = 2) := by
  constructor
  · rw [← not_imp_not]
    simp_rw [← odd_totient_iff, not_or, not_odd_iff_even, even_iff_two_dvd]
    exact fun h ↦ Nat.not_coprime_of_dvd_of_dvd one_lt_two h.1 h.2
  · simp_rw [← totient_eq_one_iff]
    rintro (h | h) <;> rw [h]
    exacts [Nat.coprime_one_left _, Nat.coprime_one_right _]

/-! ### Euler's product formula for the totient function

We prove several different statements of this formula. -/


/-- Euler's product formula for the totient function. -/
/-
**Nat.totient_eq_prod_factorization** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：totient_eq_prod_factorization {n : Nat} (hn : n != 0) : φ n = n.factorizat
ion.prod fun p k => p ^ (k - 1) * (p - 1)
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.multiplicative_factorization`：multiplicative_factorization {β : Type
*} [CommMonoid β] (f : Nat -> β) (h_mult : forall x y : Nat, Coprime x y -> f (x
 * y) = f x * f y) (hf…
· 使用定理 `Nat.totient_mul`：totient_mul {m n : Nat} (h : m.Coprime n) : φ (m * n) =
 φ m * φ n
· 使用定理 `Nat.totient_one`：totient_one : φ 1 = 1
· 使用定理 `Finsupp.prod_congr`：prod_congr {f : α ->₀ M} {g1 g2 : α -> M -> N} (h : 
forall x in f.support, g1 x (f x) = g2 x (f x)) : f.prod g1 = f.prod g2
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `zero_lt_iff`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : 
Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用定理 `Nat.totient_prime_pow`：totient_prime_pow {p : Nat} (hp : p.Prime) {n : N
at} (hn : 0 < n) : φ (p ^ n) = p ^ (n - 1) * (p - 1)
· 使用引理 `Nat.prime_of_mem_primeFactors`：prime_of_mem_primeFactors (hp : p in n.pr
imeFactors) : p.Prime

--- 原说明 ---
Euler's product formula for the totient function.
-/
theorem totient_eq_prod_factorization {n : ℕ} (hn : n ≠ 0) :
    φ n = n.factorization.prod fun p k => p ^ (k - 1) * (p - 1) := by
  rw [multiplicative_factorization φ (@totient_mul) totient_one hn]
  apply Finsupp.prod_congr _
  intro p hp
  have h := zero_lt_iff.mpr (Finsupp.mem_support_iff.mp hp)
  rw [totient_prime_pow (prime_of_mem_primeFactors hp) h]

/-- Euler's product formula for the totient function. -/
/-
**Nat.totient_mul_prod_primeFactors** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：totient_mul_prod_primeFactors (n : Nat) : (φ n * ∏ p in n.primeFactors, p)
 = n * ∏ p in n.primeFactors, (p - 1)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Nat.primeFactors_zero`：Nat.primeFactors 0 = ∅
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.totient_eq_prod_factorization`：totient_eq_prod_factorization {n : Na
t} (hn : n != 0) : φ n = n.factorization.prod fun p k => p ^ (k - 1) * (p - 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.prod_factorization_pow_eq_self`：prod_factorization_pow_eq_self {n : 
Nat} (hn : n != 0) : n.factorization.prod (· ^ ·) = n
· 使用定理 `Finsupp.prod_congr`：prod_congr {f : α ->₀ M} {g1 g2 : α -> M -> N} (h : 
forall x in f.support, g1 x (f x) = g2 x (f x)) : f.prod g1 = f.prod g2
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Nat.pow_succ'`：∀ {m n : ℕ}, m ^ n.succ = m * m ^ n
· 使用定理 `Nat.sub_one`：∀ (n : ℕ), n - 1 = n.pred
· 使用定理 `Nat.succ_pred_eq_of_pos`：∀ {n : ℕ}, 0 < n → n.pred.succ = n
· 使用定理 `zero_lt_iff`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : 
Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0

--- 原说明 ---
Euler's product formula for the totient function.
-/
theorem totient_mul_prod_primeFactors (n : ℕ) :
    (φ n * ∏ p ∈ n.primeFactors, p) = n * ∏ p ∈ n.primeFactors, (p - 1) := by
  by_cases hn : n = 0; · simp [hn]
  rw [totient_eq_prod_factorization hn]
  nth_rw 3 [← prod_factorization_pow_eq_self hn]
  simp only [prod_primeFactors_prod_factorization, ← Finsupp.prod_mul]
  refine Finsupp.prod_congr (M := ℕ) (N := ℕ) fun p hp => ?_
  rw [Finsupp.mem_support_iff, ← zero_lt_iff] at hp
  rw [mul_comm, ← mul_assoc, ← pow_succ', Nat.sub_one, Nat.succ_pred_eq_of_pos hp]

/-- Euler's product formula for the totient function. -/
/-
**Nat.totient_eq_div_primeFactors_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：totient_eq_div_primeFactors_mul (n : Nat) : φ n = (n / ∏ p in n.primeFacto
rs, p) * ∏ p in n.primeFactors, (p - 1)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.mul_div_left`：∀ (m : ℕ) {n : ℕ}, 0 < n → m * n / n = m
· 使用引理 `Finset.prod_pos`：prod_pos (h0 : forall i in s, 0 < f i) : 0 < ∏ i in s, 
f i
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用引理 `Nat.pos_of_mem_primeFactors`：pos_of_mem_primeFactors (hp : p in n.primeF
actors) : 0 < p
· 使用定理 `Nat.totient_mul_prod_primeFactors`：totient_mul_prod_primeFactors (n : Na
t) : (φ n * ∏ p in n.primeFactors, p) = n * ∏ p in n.primeFactors, (p - 1)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Nat.mul_div_assoc`：∀ {k n : ℕ} (m : ℕ), k ∣ n → m * n / k = m * (n / k)
· 使用定理 `Nat.prod_primeFactors_dvd`：prod_primeFactors_dvd (n : Nat) : ∏ p in n.pr
imeFactors, p ∣ n

--- 原说明 ---
Euler's product formula for the totient function.
-/
theorem totient_eq_div_primeFactors_mul (n : ℕ) :
    φ n = (n / ∏ p ∈ n.primeFactors, p) * ∏ p ∈ n.primeFactors, (p - 1) := by
  rw [← mul_div_left n.totient, totient_mul_prod_primeFactors, mul_comm,
    Nat.mul_div_assoc _ (prod_primeFactors_dvd n), mul_comm]
  exact prod_pos (fun p => pos_of_mem_primeFactors)

/-- Euler's product formula for the totient function. -/
/-
**Nat.totient_eq_mul_prod_factors** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：totient_eq_mul_prod_factors (n : Nat) : (φ n : Rat) = n * ∏ p in n.primeFa
ctors, (1 - (p : Rat)⁻¹)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Nat.primeFactors_zero`：Nat.primeFactors 0 = ∅
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.cast_prod`：cast_prod [CommSemiring R] (f : ι -> Nat) (s : Finset ι) 
: (↑(∏ i in s, f i) : R) = ∏ i in s, (f i : R)
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `zero_lt_iff`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : 
Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用引理 `Nat.prod_primeFactors_prod_factorization`：prod_primeFactors_prod_factori
zation {β : Type*} [CommMonoid β] (f : Nat -> β) : ∏ p in n.primeFactors, f p = 
n.factorization.prod (fun p _ …
· 使用引理 `Finset.prod_pos`：prod_pos (h0 : forall i in s, 0 < f i) : 0 < ∏ i in s, 
f i
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用引理 `Nat.pos_of_mem_primeFactors`：pos_of_mem_primeFactors (hp : p in n.primeF
actors) : 0 < p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.totient_eq_div_primeFactors_mul`：totient_eq_div_primeFactors_mul (n 
: Nat) : φ n = (n / ∏ p in n.primeFactors, p) * ∏ p in n.primeFactors, (p - 1)
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用引理 `Nat.cast_div_charZero`：cast_div_charZero (hnm : n ∣ m) : (↑(m / n) : K) 
= m / n
· 使用定理 `Nat.prod_primeFactors_dvd`：prod_primeFactors_dvd (n : Nat) : ∏ p in n.pr
imeFactors, p ∣ n
· 使用定理 `mul_comm_div`：mul_comm_div : a / b * c = a * (c / b)
· 使用引理 `mul_right_inj'`：mul_right_inj' (ha : a != 0) : a * b = a * c ↔ b = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用引理 `div_eq_iff`：div_eq_iff (hb : b != 0) : a / b = c ↔ a = c * b
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
Euler's product formula for the totient function.
-/
theorem totient_eq_mul_prod_factors (n : ℕ) :
    (φ n : ℚ) = n * ∏ p ∈ n.primeFactors, (1 - (p : ℚ)⁻¹) := by
  by_cases hn : n = 0
  · simp [hn]
  have hn' : (n : ℚ) ≠ 0 := by simp [hn]
  have hpQ : (∏ p ∈ n.primeFactors, (p : ℚ)) ≠ 0 := by
    rw [← cast_prod, cast_ne_zero, ← zero_lt_iff, prod_primeFactors_prod_factorization]
    exact prod_pos fun p hp => pos_of_mem_primeFactors hp
  simp only [totient_eq_div_primeFactors_mul n, prod_primeFactors_dvd n, cast_mul, cast_prod,
    cast_div_charZero, mul_comm_div, mul_right_inj' hn', div_eq_iff hpQ, ← prod_mul_distrib]
  refine prod_congr rfl fun p hp => ?_
  have hp := pos_of_mem_primeFactorsList (List.mem_toFinset.mp hp)
  have hp' : (p : ℚ) ≠ 0 := cast_ne_zero.mpr hp.ne.symm
  rw [sub_mul, one_mul, mul_comm, mul_inv_cancel₀ hp', cast_pred hp]
/-
**Nat.totient_gcd_mul_totient_mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：totient_gcd_mul_totient_mul (a b : Nat) : φ (a.gcd b) * φ (a * b) = φ a * 
φ b * a.gcd b
参数：a b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)
· 使用定理 `Nat.div_mul_div_comm`：∀ {a b c d : ℕ}, b ∣ a → d ∣ c → a / b * (c / d) =
 a * c / (b * d)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.totient_eq_div_primeFactors_mul`：totient_eq_div_primeFactors_mul (n 
: Nat) : φ n = (n / ∏ p in n.primeFactors, p) * ∏ p in n.primeFactors, (p - 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.prod_primeFactors_dvd`：prod_primeFactors_dvd (n : Nat) : ∏ p in n.pr
imeFactors, p ∣ n
· 使用定理 `Nat.prod_primeFactors_gcd_mul_prod_primeFactors_mul`：prod_primeFactors_g
cd_mul_prod_primeFactors_mul {β : Type*} [CommMonoid β] (m n : Nat) (f : Nat -> 
β) : (m.gcd n).primeFactors.prod f * (m *…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Nat.mul_div_assoc`：∀ {k n : ℕ} (m : ℕ), k ∣ n → m * n / k = m * (n / k)
· 使用定理 `mul_dvd_mul`：∀ {α : Type u_1} [inst : CommSemigroup α] {a b c d : α}, a 
∣ b → c ∣ d → a * c ∣ b * d
-/
theorem totient_gcd_mul_totient_mul (a b : ℕ) : φ (a.gcd b) * φ (a * b) = φ a * φ b * a.gcd b := by
  have shuffle :
    ∀ a1 a2 b1 b2 c1 c2 : ℕ,
      b1 ∣ a1 → b2 ∣ a2 → a1 / b1 * c1 * (a2 / b2 * c2) = a1 * a2 / (b1 * b2) * (c1 * c2) := by
    intro a1 a2 b1 b2 c1 c2 h1 h2
    calc
      a1 / b1 * c1 * (a2 / b2 * c2) = a1 / b1 * (a2 / b2) * (c1 * c2) := by apply mul_mul_mul_comm
      _ = a1 * a2 / (b1 * b2) * (c1 * c2) := by
        congr 1
        exact div_mul_div_comm h1 h2
  simp only [totient_eq_div_primeFactors_mul]
  rw [shuffle, shuffle]
  rotate_left
  repeat' apply prod_primeFactors_dvd
  simp only [prod_primeFactors_gcd_mul_prod_primeFactors_mul]
  rw [eq_comm, mul_comm, ← mul_assoc, ← Nat.mul_div_assoc]
  exact mul_dvd_mul (prod_primeFactors_dvd a) (prod_primeFactors_dvd b)
/-
**Nat.totient_super_multiplicative** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：totient_super_multiplicative (a b : Nat) : φ a * φ b <= φ (a * b)
参数：a b : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.gcd_pos_of_pos_left`：∀ {m : ℕ} (n : ℕ), 0 < m → 0 < m.gcd n
· 使用定理 `le_of_mul_le_mul_right`：le_of_mul_le_mul_right [MulPosReflectLE α] (bc :
 b * a <= c * a) (a0 : 0 < a) : b <= c
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Nat.totient_gcd_mul_totient_mul`：totient_gcd_mul_totient_mul (a b : Nat)
 : φ (a.gcd b) * φ (a * b) = φ a * φ b * a.gcd b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Nat.totient_le`：totient_le (n : Nat) : φ n <= n
-/
theorem totient_super_multiplicative (a b : ℕ) : φ a * φ b ≤ φ (a * b) := by
  let d := a.gcd b
  rcases eq_zero_or_pos a with (rfl | ha0)
  · simp
  have hd0 : 0 < d := Nat.gcd_pos_of_pos_left _ ha0
  apply le_of_mul_le_mul_right _ hd0
  grw [← totient_gcd_mul_totient_mul a b, mul_comm, d.totient_le]

@[gcongr]
/-
**Nat.totient_dvd_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：totient_dvd_of_dvd {a b : Nat} (h : a ∣ b) : φ a ∣ φ b
参数：h : a ∣ b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `zero_dvd_iff`：zero_dvd_iff : 0 ∣ a ↔ a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.primeFactors_mono`：primeFactors_mono (hmn : m ∣ n) (hn : n != 0) : p
rimeFactors m subseteq primeFactors n
· 使用定理 `Nat.totient_eq_prod_factorization`：totient_eq_prod_factorization {n : Na
t} (hn : n != 0) : φ n = n.factorization.prod fun p k => p ^ (k - 1) * (p - 1)
· 使用定理 `Finsupp.prod_dvd_prod_of_subset_of_dvd`：prod_dvd_prod_of_subset_of_dvd [
Zero M] [CommMonoid N] {f1 f2 : α ->₀ M} {g1 g2 : α -> M -> N} (h1 : f1.support 
subseteq f2.support) (h2 : f…
· 使用定理 `mul_dvd_mul`：∀ {α : Type u_1} [inst : CommSemigroup α] {a b c d : α}, a 
∣ b → c ∣ d → a * c ∣ b * d
· 使用引理 `pow_dvd_pow`：pow_dvd_pow (a : α) (h : m <= n) : a ^ m ∣ a ^ n
· 使用定理 `tsub_le_tsub_right`：tsub_le_tsub_right (h : a <= b) (c : α) : a - c <= b
 - c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.factorization_le_iff_dvd`：factorization_le_iff_dvd {d n : Nat} (hd :
 d != 0) (hn : n != 0) : d.factorization <= n.factorization ↔ d ∣ n
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
-/
theorem totient_dvd_of_dvd {a b : ℕ} (h : a ∣ b) : φ a ∣ φ b := by
  rcases eq_or_ne a 0 with (rfl | ha0)
  · simp [zero_dvd_iff.1 h]
  rcases eq_or_ne b 0 with (rfl | hb0)
  · simp
  have hab' := primeFactors_mono h hb0
  rw [totient_eq_prod_factorization ha0, totient_eq_prod_factorization hb0]
  refine Finsupp.prod_dvd_prod_of_subset_of_dvd hab' fun p _ => mul_dvd_mul ?_ dvd_rfl
  exact pow_dvd_pow p (tsub_le_tsub_right ((factorization_le_iff_dvd ha0 hb0).2 h p) 1)
/-
**Nat.totient_mul_of_prime_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：totient_mul_of_prime_of_dvd {p n : Nat} (hp : p.Prime) (h : p ∣ n) : (p * 
n).totient = p * n.totient
参数：hp : p.Prime；h : p ∣ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.totient_gcd_mul_totient_mul`：totient_gcd_mul_totient_mul (a b : Nat)
 : φ (a.gcd b) * φ (a * b) = φ a * φ b * a.gcd b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.totient_pos`：∀ {n : ℕ}, 0 < n.totient ↔ 0 < n
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Nat.gcd_eq_left`：∀ {m n : ℕ}, m ∣ n → m.gcd n = m
-/
theorem totient_mul_of_prime_of_dvd {p n : ℕ} (hp : p.Prime) (h : p ∣ n) :
    (p * n).totient = p * n.totient := by
  have h1 := totient_gcd_mul_totient_mul p n
  rw [gcd_eq_left h, mul_assoc] at h1
  simpa [(totient_pos.2 hp.pos).ne', mul_comm] using h1
/-
**Nat.totient_mul_of_prime_of_not_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：totient_mul_of_prime_of_not_dvd {p n : Nat} (hp : p.Prime) (h : ¬p ∣ n) : 
(p * n).totient = (p - 1) * n.totient
参数：hp : p.Prime；h : ¬p ∣ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.totient_mul`：totient_mul {m n : Nat} (h : m.Coprime n) : φ (m * n) =
 φ m * φ n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Nat.coprime_or_dvd_of_prime`：coprime_or_dvd_of_prime {p} (pp : Prime p) 
(i : Nat) : Coprime p i ∨ p ∣ i
· 使用定理 `Nat.totient_prime`：totient_prime {p : Nat} (hp : p.Prime) : φ p = p - 1
-/
theorem totient_mul_of_prime_of_not_dvd {p n : ℕ} (hp : p.Prime) (h : ¬p ∣ n) :
    (p * n).totient = (p - 1) * n.totient := by
  rw [totient_mul _, totient_prime hp]
  simpa [h] using coprime_or_dvd_of_prime hp n
/-
**Nat.totient_two_mul_of_even** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：totient_two_mul_of_even {n : Nat} (hn : Even n) : (2 * n).totient = 2 * n.
totient
参数：hn : Even n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.totient_mul_of_prime_of_dvd`：totient_mul_of_prime_of_dvd {p n : Nat}
 (hp : p.Prime) (h : p ∣ n) : (p * n).totient = p * n.totient
· 使用定理 `Nat.prime_two`：prime_two : Prime 2
· 使用定理 `Even.two_dvd`：∀ {α : Type u_2} [inst : Semiring α] {a : α}, Even a → 2 ∣
 a
-/
theorem totient_two_mul_of_even {n : ℕ} (hn : Even n) : (2 * n).totient = 2 * n.totient :=
  totient_mul_of_prime_of_dvd prime_two hn.two_dvd
/-
**Nat.totient_two_mul_of_odd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：totient_two_mul_of_odd {n : Nat} (hn : Odd n) : (2 * n).totient = n.totien
t
参数：hn : Odd n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.totient_mul_of_prime_of_not_dvd`：totient_mul_of_prime_of_not_dvd {p 
n : Nat} (hp : p.Prime) (h : ¬p ∣ n) : (p * n).totient = (p - 1) * n.totient
· 使用定理 `Nat.prime_two`：prime_two : Prime 2
· 使用定理 `Odd.not_two_dvd_nat`：∀ {n : ℕ}, Odd n → ¬2 ∣ n
· 使用定理 `Nat.add_one_sub_one`：∀ (n : ℕ), n + 1 - 1 = n
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem totient_two_mul_of_odd {n : ℕ} (hn : Odd n) : (2 * n).totient = n.totient := by
  rw [totient_mul_of_prime_of_not_dvd prime_two hn.not_two_dvd_nat, Nat.add_one_sub_one 1, one_mul]
/-
**Nat.eq_or_eq_of_totient_eq_totient** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：eq_or_eq_of_totient_eq_totient {a b : Nat} (h : a ∣ b) (h' : a.totient = b
.totient) : a = b ∨ 2 * a = b
参数：h : a ∣ b；h' : a.totient = b.totient。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.totient_eq_zero`：∀ {n : ℕ}, n.totient = 0 ↔ n = 0
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Nat.totient_zero`：totient_zero : φ 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Nat.coprime_of_dvd`：coprime_of_dvd {m n : Nat} (H : forall k, Prime k ->
 k ∣ m -> ¬k ∣ n) : Coprime m n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Nat.totient_mul_of_prime_of_dvd`：totient_mul_of_prime_of_dvd {p n : Nat}
 (hp : p.Prime) (h : p ∣ n) : (p * n).totient = p * n.totient
· 使用定理 `Nat.lt_mul_iff_one_lt_left`：∀ {b a : ℕ}, 0 < b → (b < a * b ↔ 1 < a)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.totient_pos`：∀ {n : ℕ}, 0 < n.totient ↔ 0 < n
· 使用定理 `pos_of_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1
 : Zero α] [IsBotZeroClass α], a ≠ 0 → 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Nat.zero_lt_of_ne_zero`：∀ {a : ℕ}, a ≠ 0 → 0 < a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Nat.totient_dvd_of_dvd`：totient_dvd_of_dvd {a b : Nat} (h : a ∣ b) : φ a
 ∣ φ b
· 使用定理 `Eq.not_lt`：∀ {α : Type u_2} [inst : Preorder α] {a b : α}, a = b → ¬a < 
b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.totient_eq_one_iff`：totient_eq_one_iff : forall {n : Nat}, n.totient
 = 1 ↔ n = 1 ∨ n = 2 | 0 => by simp | 1 => by simp | 2 => by simp | n + 3 => by 
have : 3 <= …
· 使用定理 `Nat.mul_eq_left`：∀ {a b : ℕ}, a ≠ 0 → (a * b = a ↔ b = 1)
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Nat.totient_mul`：totient_mul {m n : Nat} (h : m.Coprime n) : φ (m * n) =
 φ m * φ n
（共 34 条，此处仅展示前 30 条）
-/
theorem eq_or_eq_of_totient_eq_totient {a b : ℕ} (h : a ∣ b) (h' : a.totient = b.totient) :
    a = b ∨ 2 * a = b := by
  by_cases ha : a = 0
  · rw [ha, totient_zero, eq_comm, totient_eq_zero] at h'
    simp [ha, h']
  by_cases hb : b = 0
  · rw [hb, totient_zero, totient_eq_zero] at h'
    exact False.elim (ha h')
  obtain ⟨c, rfl⟩ := h
  suffices a.Coprime c by
    rw [totient_mul this, eq_comm, mul_eq_left (totient_eq_zero.not.mpr ha),
      totient_eq_one_iff] at h'
    obtain rfl | rfl := h'
    · simp
    · simp [mul_comm]
  refine coprime_of_dvd fun p hp hap ↦ ?_
  rintro ⟨d, rfl⟩
  suffices a.totient < (p * a * d).totient by
    rw [← mul_assoc, mul_comm a] at h'
    exact h'.not_lt this
  rw [mul_comm p]
  refine lt_of_lt_of_le ?_ (Nat.le_of_dvd ?_ (totient_dvd_of_dvd ⟨d, rfl⟩))
  · rw [mul_comm, totient_mul_of_prime_of_dvd hp hap, Nat.lt_mul_iff_one_lt_left]
    · exact hp.one_lt
    · exact totient_pos.mpr <| pos_of_ne_zero ha
  · exact totient_pos.mpr <| zero_lt_of_ne_zero (by rwa [mul_assoc])
/-
**Nat._root_.Even.eq_of_totient_eq_totient** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Even.eq_of_totient_eq_totient {a b : ℕ} (h : a ∣ b) (ha : Even a)
    (h' : a.totient = b.totient) : a = b := by
  by_cases ha' : a = 0
  · rw [ha', totient_zero, eq_comm, totient_eq_zero] at h'
    rw [h', ha']
  refine (eq_or_eq_of_totient_eq_totient h h').resolve_right fun h ↦ ?_
  rw [← h, totient_mul_of_prime_of_dvd (prime_two) (even_iff_two_dvd.mp ha), eq_comm,
    mul_eq_right (totient_eq_zero.not.mpr ha')] at h'
  lia
/-
**Nat.prime_pow_pow_totient_ediv_prod** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prime_pow_pow_totient_ediv_prod {p k : Nat} (hp : p.Prime) (hk : 0 < k) : 
(p ^ k : Nat) ^ φ (p ^ k) / ∏ q in (p ^ k).primeFactors, q ^ (φ (p ^ k) / (q - 1
)) = p ^ (p ^ (k - 1) * ((p - 1) * k - 1))
参数：hp : p.Prime；hk : 0 < k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `le_mul_of_one_le_right`：le_mul_of_one_le_right [PosMulMono α] (ha : 0 <=
 a) (h : 1 <= b) : a <= a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Right.one_le_mul`：Right.one_le_mul [MulRightMono α] {a b : α} (ha : 1 <=
 a) (hb : 1 <= b) : 1 <= a * b
· 使用定理 `Nat.le_sub_one_of_lt`：∀ {a b : ℕ}, a < b → a ≤ b - 1
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.totient_prime_pow`：totient_prime_pow {p : Nat} (hp : p.Prime) {n : N
at} (hn : 0 < n) : φ (p ^ n) = p ^ (n - 1) * (p - 1)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用引理 `Nat.primeFactors_prime_pow`：primeFactors_prime_pow (hk : k != 0) (hp : P
rime p) : (p ^ k).primeFactors = {p}
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `Nat.mul_div_left`：∀ (m : ℕ) {n : ℕ}, 0 < n → m * n / n = m
· 使用定理 `Nat.sub_pos_of_lt`：∀ {m n : ℕ}, m < n → 0 < n - m
· 使用定理 `Nat.pow_div`：∀ {x m n : ℕ}, n ≤ m → 0 < x → x ^ m / x ^ n = x ^ (m - n)
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `Nat.sub_mul`：∀ (n m k : ℕ), (n - m) * k = n * k - m * k
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.mul_sub`：∀ (n m k : ℕ), n * (m - k) = n * m - n * k
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf'`：∀ {R : Type u_1} [inst : CommSemiri
ng R] {a a' b : R},   a = a' → ∀ {e : ℕ}, Nat.rawCast 1 = e → a' ^ e * Nat.rawCa
st 1 = b → a = b + 0
（共 51 条，此处仅展示前 30 条）
-/
theorem prime_pow_pow_totient_ediv_prod {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
      (p ^ k : ℕ) ^ φ (p ^ k) / ∏ q ∈ (p ^ k).primeFactors, q ^ (φ (p ^ k) / (q - 1)) =
        p ^ (p ^ (k - 1) * ((p - 1) * k - 1)) := by
  have h : p ^ (k - 1) ≤ k * (p ^ (k - 1) * (p - 1)) := by
    rw [mul_left_comm]
    refine le_mul_of_one_le_right (Nat.zero_le _) ?_
    exact Right.one_le_mul hk <| Nat.le_sub_one_of_lt <| hp.one_lt
  simp_rw [Nat.totient_prime_pow hp hk, Nat.primeFactors_prime_pow hk.ne' hp, Finset.prod_singleton,
    Nat.mul_div_left _ (Nat.sub_pos_of_lt hp.one_lt), ← pow_mul]
  rw [Nat.pow_div h hp.pos]
  simp_rw [Nat.sub_mul, one_mul, Nat.mul_sub, mul_one]
  ring_nf
/-
**Nat.prod_primeFactors_pow_totient_ediv_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prod_primeFactors_pow_totient_ediv_dvd {n : Nat} (hn : 0 < n) : ∏ p in n.p
rimeFactors, p ^ (φ n / (p - 1)) ∣ n ^ φ n
参数：hn : 0 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.prod_primeFactors_dvd`：prod_primeFactors_dvd (n : Nat) : ∏ p in n.pr
imeFactors, p ∣ n
· 使用定理 `dvd_trans`：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d 
* e, h₁ ▸ h₂.trans mul_assoc a d e⟩  alias Dvd.dvd.trans
· 使用引理 `Finset.prod_dvd_prod_of_dvd`：prod_dvd_prod_of_dvd (f g : ι -> M) (h : fo
rall i in s, f i ∣ g i) : ∏ i in s, f i ∣ ∏ i in s, g i
· 使用定理 `Nat.pow_dvd_pow`：∀ {m n : ℕ} (a : ℕ), m ≤ n → a ^ m ∣ a ^ n
· 使用定理 `Nat.div_le_self`：∀ (n k : ℕ), n / k ≤ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_pow`：prod_pow (s : Finset ι) (n : Nat) (f : ι -> M) : ∏ x in
 s, f x ^ n = (∏ x in s, f x) ^ n
· 使用定理 `Nat.pow_dvd_pow_iff`：∀ {a b n : ℕ}, n ≠ 0 → (a ^ n ∣ b ^ n ↔ a ∣ b)
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.totient_pos`：∀ {n : ℕ}, 0 < n.totient ↔ 0 < n
-/
theorem prod_primeFactors_pow_totient_ediv_dvd {n : ℕ} (hn : 0 < n) :
    ∏ p ∈ n.primeFactors, p ^ (φ n / (p - 1)) ∣ n ^ φ n := by
  have := Nat.prod_primeFactors_dvd n
  rw [← Nat.pow_dvd_pow_iff (Nat.totient_pos.mpr hn).ne', ← Finset.prod_pow] at this
  refine dvd_trans (Finset.prod_dvd_prod_of_dvd _ _ fun p hp ↦ ?_) this
  exact Nat.pow_dvd_pow p <| Nat.div_le_self _ _

end Nat

namespace Mathlib.Meta.Positivity
open Lean Meta Qq

/-- Extension for `Nat.totient`. -/
@[positivity Nat.totient _]
meta def evalNatTotient : PositivityExt where eval {u α} z p e :=
  match p with | none => pure .none | some p => do
  match u, α, e with
  | 0, ~q(ℕ), ~q(Nat.totient $n) =>
    match ← core z p n with
    | .positive pa =>
      assumeInstancesCommute
      return .positive q(Nat.totient_pos.mpr $pa)
    | _ => failure
  | _, _, _ => throwError "not Nat.totient"

end Mathlib.Meta.Positivity

