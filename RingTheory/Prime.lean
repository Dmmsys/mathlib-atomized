/-
Copyright (c) 2020 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Prime.Defs
public import Mathlib.Algebra.Ring.Units
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Prime elements in rings

This file contains lemmas about prime elements of commutative rings.
-/

public section


section CancelCommMonoidWithZero

variable {R : Type*} [CommMonoidWithZero R] [IsCancelMulZero R]

open Finset

/-- If `x * y = a * ∏ i ∈ s, p i` where `p i` is always prime, then
`x` and `y` can both be written as a divisor of `a` multiplied by
a product over a subset of `s` -/
/-
**mul_eq_mul_prime_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_eq_mul_prime_prod {α : Type*} [DecidableEq α] {x y a : R} {s : Finset 
α} {p : α -> R} (hp : forall i in s, Prime (p i)) (hx : x * y = a * ∏ i in s, p 
i) : exists (t u : Finset α) (b c : R), t union u = s ∧ Disjoint t u ∧ a = b * c
 ∧ (x = b * ∏ i in t, p i) ∧ y = c * ∏ i in u, p i
参数：hp : forall i in s, Prime (p i)；hx : x * y = a * ∏ i in s, p i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.union_idempotent`：union_idempotent (s : Finset α) : s union s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `Finset.mem_union_left`：mem_union_left (t : Finset α) (h : a in s) : a in
 s union t
· 使用定理 `Finset.mem_union_right`：mem_union_right (s : Finset α) (h : a in t) : a 
in s union t
· 使用定理 `Prime.dvd_or_dvd`：dvd_or_dvd {a b : M} (h : p ∣ a * b) : p ∣ a ∨ p ∣ b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Finset.insert_union`：insert_union (a : α) (s t : Finset α) : insert a s 
union t = insert a (s union t)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_insert_left`：disjoint_insert_left : Disjoint (insert a s
) t ↔ a ∉ t ∧ Disjoint s t
· 使用引理 `mul_right_inj'`：mul_right_inj' (ha : a != 0) : a * b = a * c ↔ b = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `Prime.ne_zero`：ne_zero : p != 0
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `Finset.union_insert`：union_insert (a : α) (s t : Finset α) : s union ins
ert a t = insert a (s union t)
· 使用定理 `Finset.disjoint_insert_right`：disjoint_insert_right : Disjoint s (insert
 a t) ↔ a ∉ s ∧ Disjoint s t
· 使用引理 `mul_left_inj'`：mul_left_inj' (hc : c != 0) : a * c = b * c ↔ a = b
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
If `x * y = a * ∏ i ∈ s, p i` where `p i` is always prime, then
`x` and `y` can both be written as a divisor of `a` multiplied by
a product over a subset of `s`
-/
theorem mul_eq_mul_prime_prod {α : Type*} [DecidableEq α] {x y a : R} {s : Finset α} {p : α → R}
    (hp : ∀ i ∈ s, Prime (p i)) (hx : x * y = a * ∏ i ∈ s, p i) :
    ∃ (t u : Finset α) (b c : R),
      t ∪ u = s ∧ Disjoint t u ∧ a = b * c ∧ (x = b * ∏ i ∈ t, p i) ∧ y = c * ∏ i ∈ u, p i := by
  induction s using Finset.induction generalizing x y a with
  | empty => exact ⟨∅, ∅, x, y, by simp [hx]⟩
  | insert i s his ih =>
    rw [prod_insert his, ← mul_assoc] at hx
    have hpi : Prime (p i) := hp i (mem_insert_self _ _)
    rcases ih (fun i hi ↦ hp i (mem_insert_of_mem hi)) hx with
      ⟨t, u, b, c, htus, htu, hbc, rfl, rfl⟩
    have hit : i ∉ t := fun hit ↦ his (htus ▸ mem_union_left _ hit)
    have hiu : i ∉ u := fun hiu ↦ his (htus ▸ mem_union_right _ hiu)
    obtain ⟨d, rfl⟩ | ⟨d, rfl⟩ : p i ∣ b ∨ p i ∣ c := hpi.dvd_or_dvd ⟨a, by rw [← hbc, mul_comm]⟩
    · rw [mul_assoc, mul_comm a, mul_right_inj' hpi.ne_zero] at hbc
      exact ⟨insert i t, u, d, c, by rw [insert_union, htus], disjoint_insert_left.2 ⟨hiu, htu⟩, by
          simp [hbc, prod_insert hit, mul_comm, mul_left_comm]⟩
    · rw [← mul_assoc, mul_right_comm b, mul_left_inj' hpi.ne_zero] at hbc
      exact ⟨t, insert i u, b, d, by rw [union_insert, htus], disjoint_insert_right.2 ⟨hit, htu⟩, by
          simp [← hbc, prod_insert hiu, mul_comm, mul_left_comm]⟩

/-- If `x * y = a * p ^ n` where `p` is prime, then `x` and `y` can both be written
  as the product of a power of `p` and a divisor of `a`. -/
/-
**mul_eq_mul_prime_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_eq_mul_prime_pow {x y a p : R} {n : Nat} (hp : Prime p) (hx : x * y = 
a * p ^ n) : exists (i j : Nat) (b c : R), i + j = n ∧ a = b * c ∧ x = b * p ^ i
 ∧ y = c * p ^ j
参数：hp : Prime p；hx : x * y = a * p ^ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_eq_mul_prime_prod`：mul_eq_mul_prime_prod {α : Type*} [DecidableEq α]
 {x y a : R} {s : Finset α} {p : α -> R} (hp : forall i in s, Prime (p i)) (hx :
 x * y = a …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_union_of_disjoint`：∀ {α : Type u_1} {s t : Finset α} [inst :
 DecidableEq α], Disjoint s t → (s ∪ t).card = s.card + t.card
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
If `x * y = a * p ^ n` where `p` is prime, then `x` and `y` can both be written
  as the product of a power of `p` and a divisor of `a`.
-/
theorem mul_eq_mul_prime_pow {x y a p : R} {n : ℕ} (hp : Prime p) (hx : x * y = a * p ^ n) :
    ∃ (i j : ℕ) (b c : R), i + j = n ∧ a = b * c ∧ x = b * p ^ i ∧ y = c * p ^ j := by
  rcases mul_eq_mul_prime_prod (fun _ _ ↦ hp)
    (show x * y = a * (range n).prod fun _ ↦ p by simpa) with
      ⟨t, u, b, c, htus, htu, rfl, rfl, rfl⟩
  exact ⟨#t, #u, b, c, by rw [← card_union_of_disjoint htu, htus, card_range], by simp⟩

end CancelCommMonoidWithZero

section CommRing

variable {α : Type*} [CommRing α]

/-
**Prime.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prime.neg {p : α} (hp : Prime p) : Prime (-p)
参数：hp : Prime p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsUnit.neg_iff`：IsUnit.neg_iff [Monoid α] [HasDistribNeg α] (a : α) : Is
Unit (-a) ↔ IsUnit a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem Prime.neg {p : α} (hp : Prime p) : Prime (-p) := by
  obtain ⟨h1, h2, h3⟩ := hp
  exact ⟨neg_ne_zero.mpr h1, by rwa [IsUnit.neg_iff], by simpa [neg_dvd] using h3⟩
/-
**Prime.abs** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Prime.abs [LinearOrder α] {p : α} (hp : Prime p) : Prime (abs p)
参数：hp : Prime p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `abs_choice`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α
] (x : α), |x| = x ∨ |x| = -x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prime.neg`：Prime.neg {p : α} (hp : Prime p) : Prime (-p)
-/
theorem Prime.abs [LinearOrder α] {p : α} (hp : Prime p) : Prime (abs p) := by
  obtain h | h := abs_choice p <;> rw [h]
  · exact hp
  · exact hp.neg

end CommRing

