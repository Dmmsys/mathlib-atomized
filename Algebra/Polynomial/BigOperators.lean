/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Lemmas for the interaction between polynomials and `∑` and `∏`.

Recall that `∑` and `∏` are notation for `Finset.sum` and `Finset.prod` respectively.

## Main results

- `Polynomial.natDegree_prod_of_monic` : the degree of a product of monic polynomials is the
  product of degrees. We prove this only for `[CommSemiring R]`,
  but it ought to be true for `[Semiring R]` and `List.prod`.
- `Polynomial.natDegree_prod` : for polynomials over an integral domain,
  the degree of the product is the sum of degrees.
- `Polynomial.leadingCoeff_prod` : for polynomials over an integral domain,
  the leading coefficient is the product of leading coefficients.
- `Polynomial.prod_X_sub_C_coeff_card_pred` carries most of the content for computing
  the second coefficient of the characteristic polynomial.
-/

public section


open Finset

open Multiset

open Polynomial

universe u w

variable {R : Type u} {ι : Type w}

namespace Polynomial

variable (s : Finset ι)

section Semiring

variable {S : Type*} [Semiring S]

/-
**Polynomial.natDegree_list_sum_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_list_sum_le (l : List S[X]) : natDegree l.sum <= (l.map natDegre
e).foldr max 0
参数：l : List S[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `List.sum_le_foldr_max`：sum_le_foldr_max [AddZeroClass M] [Zero N] [Linea
rOrder N] (f : M -> N) (h0 : f 0 <= 0) (hadd : forall x y, f (x + y) <= max (f x
) (f y)) (l…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Polynomial.natDegree_add_le`：natDegree_add_le (p q : R[X]) : natDegree (
p + q) <= max (natDegree p) (natDegree q)
-/
theorem natDegree_list_sum_le (l : List S[X]) :
    natDegree l.sum ≤ (l.map natDegree).foldr max 0 := by
  apply List.sum_le_foldr_max natDegree
  · simp
  · exact natDegree_add_le
/-
**Polynomial.natDegree_multiset_sum_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_multiset_sum_le (l : Multiset S[X]) : natDegree l.sum <= (l.map 
natDegree).foldr max 0
参数：l : Multiset S[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `instLeftCommutativeOfCommutativeOfAssociative`：∀ {α : Sort u} {f : α → α
 → α} [hc : Std.Commutative f] [ha : Std.Associative f], LeftCommutative f
· 使用定理 `Nat.instCommutativeMax`：Std.Commutative max
· 使用定理 `Nat.instAssociativeMax`：Std.Associative max
· 使用定理 `Polynomial.natDegree_list_sum_le`：natDegree_list_sum_le (l : List S[X]) 
: natDegree l.sum <= (l.map natDegree).foldr max 0
-/
theorem natDegree_multiset_sum_le (l : Multiset S[X]) :
    natDegree l.sum ≤ (l.map natDegree).foldr max 0 :=
  Quotient.inductionOn l (by simpa using natDegree_list_sum_le)
/-
**Polynomial.natDegree_sum_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_sum_le (f : ι -> S[X]) : natDegree (∑ i in s, f i) <= s.fold max
 0 (natDegree ∘ f)
参数：f : ι -> S[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instCommutativeMax`：Std.Commutative max
· 使用定理 `Nat.instAssociativeMax`：Std.Associative max
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.fold_congr`：fold_congr {g : α -> β} (H : forall x in s, f x = g x
) : s.fold op b f = s.fold op b g
· 使用定理 `instLeftCommutativeOfCommutativeOfAssociative`：∀ {α : Sort u} {f : α → α
 → α} [hc : Std.Commutative f] [ha : Std.Associative f], LeftCommutative f
· 使用定理 `Multiset.foldr.congr_simp`：∀ {α : Type u_1} {β : Type v} (f f_1 : α → β 
→ β) (e_f : f = f_1) [inst : LeftCommutative f] (b b_1 : β),   b = b_1 → ∀ (s s_
1 : Multiset α)…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Polynomial.natDegree_multiset_sum_le`：natDegree_multiset_sum_le (l : Mul
tiset S[X]) : natDegree l.sum <= (l.map natDegree).foldr max 0
-/
theorem natDegree_sum_le (f : ι → S[X]) :
    natDegree (∑ i ∈ s, f i) ≤ s.fold max 0 (natDegree ∘ f) := by
  simpa using! natDegree_multiset_sum_le (s.val.map f)
/-
**Polynomial.natDegree_sum_le_of_forall_le** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial
`。
形式化陈述：natDegree_sum_le_of_forall_le {n : Nat} (f : ι -> S[X]) (h : forall i in s
, natDegree (f i) <= n) : natDegree (∑ i in s, f i) <= n
参数：f : ι -> S[X]；h : forall i in s, natDegree (f i) <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.instCommutativeMax`：Std.Commutative max
· 使用定理 `Nat.instAssociativeMax`：Std.Associative max
· 使用定理 `Polynomial.natDegree_sum_le`：natDegree_sum_le (f : ι -> S[X]) : natDegre
e (∑ i in s, f i) <= s.fold max 0 (natDegree ∘ f)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `instCommutativeMax`：∀ {α : Type u} [inst : LinearOrder α], Std.Commutati
ve max
· 使用定理 `instAssociativeMax`：∀ {α : Type u} [inst : LinearOrder α], Std.Associati
ve max
· 使用定理 `Finset.fold_max_le`：fold_max_le : s.fold max b f <= c ↔ b <= c ∧ forall 
x in s, f x <= c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
lemma natDegree_sum_le_of_forall_le {n : ℕ} (f : ι → S[X]) (h : ∀ i ∈ s, natDegree (f i) ≤ n) :
    natDegree (∑ i ∈ s, f i) ≤ n :=
  le_trans (natDegree_sum_le s f) <| (Finset.fold_max_le n).mpr <| by simpa

set_option backward.isDefEq.respectTransparency false in
/-- The leading coefficient of a sum of polynomials with the same degree is
the sum of the leading coefficients, provided that this sum is nonzero.
-/
/-
**Polynomial.leadingCoeff_sum_of_degree_eq** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
`。
形式化陈述：leadingCoeff_sum_of_degree_eq {f : ι -> S[X]} {s : Finset ι} {d} (hd : for
all k in s, (f k).degree = d) (hf : ∑ k in s, (f k).leadingCoeff != 0) : (∑ k in
 s, f k).leadingCoeff = ∑ k in s, (f k).leadingCoeff
参数：hd : forall k in s, (f k).degree = d；hf : ∑ k in s, (f k).leadingCoeff != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq_some`：natDegree_eq_of_degree_eq_som
e {p : R[X]} {n : Nat} (h : degree p = n) : natDegree p = n
· 使用定理 `Polynomial.natDegree_eq_of_le_of_coeff_ne_zero`：natDegree_eq_of_le_of_co
eff_ne_zero (pn : p.natDegree <= n) (p1 : p.coeff n != 0) : p.natDegree = n
· 使用引理 `Polynomial.natDegree_sum_le_of_forall_le`：natDegree_sum_le_of_forall_le 
{n : Nat} (f : ι -> S[X]) (h : forall i in s, natDegree (f i) <= n) : natDegree 
(∑ i in s, f i) <= n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.finsetSum_coeff`：finsetSum_coeff {ι : Type*} (s : Finset ι) (
f : ι -> R[X]) (n : Nat) : coeff (∑ b in s, f b) n = ∑ b in s, coeff (f b) n
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
The leading coefficient of a sum of polynomials with the same degree is
the sum of the leading coefficients, provided that this sum is nonzero.
-/
theorem leadingCoeff_sum_of_degree_eq {f : ι → S[X]} {s : Finset ι} {d}
    (hd : ∀ k ∈ s, (f k).degree = d) (hf : ∑ k ∈ s, (f k).leadingCoeff ≠ 0) :
    (∑ k ∈ s, f k).leadingCoeff = ∑ k ∈ s, (f k).leadingCoeff := by
  obtain _ | d := d
  · simp_all [WithBot.none_eq_bot]
  · replace hd k (hk : k ∈ s) : (f k).natDegree = d := natDegree_eq_of_degree_eq_some <| hd k hk
    suffices (∑ k ∈ s, f k).natDegree = d by simp_all [leadingCoeff]
    apply natDegree_eq_of_le_of_coeff_ne_zero
    · aesop (add safe natDegree_sum_le_of_forall_le)
    · simp_all [leadingCoeff]
/-
**Polynomial.degree_list_sum_le_of_forall_degree_le** 是 Mathlib 中的一个定理，位于命名空间 `P
olynomial`。
形式化陈述：degree_list_sum_le_of_forall_degree_le (l : List S[X]) (n : WithBot Nat) (
hl : forall p in l, degree p <= n) : degree l.sum <= n
参数：l : List S[X]；n : WithBot Nat；hl : forall p in l, degree p <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.sum_cons`：∀ {α : Type u} [inst : Add α] [inst_1 : Zero α] {a : α} {
l : List α}, (a :: l).sum = a + l.sum
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Polynomial.degree_add_le`：degree_add_le (p q : R[X]) : degree (p + q) <=
 max (degree p) (degree q)
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
-/
theorem degree_list_sum_le_of_forall_degree_le (l : List S[X])
    (n : WithBot ℕ) (hl : ∀ p ∈ l, degree p ≤ n) :
    degree l.sum ≤ n := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at hl
    rcases hl with ⟨hhd, htl⟩
    rw [List.sum_cons]
    exact le_trans (degree_add_le hd tl.sum) (max_le hhd (ih htl))
/-
**Polynomial.degree_list_sum_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_list_sum_le (l : List S[X]) : degree l.sum <= (l.map natDegree).max
imum
参数：l : List S[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.degree_list_sum_le_of_forall_degree_le`：degree_list_sum_le_of
_forall_degree_le (l : List S[X]) (n : WithBot Nat) (hl : forall p in l, degree 
p <= n) : degree l.sum <= n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `List.le_maximum_of_mem'`：le_maximum_of_mem' (ha : a in l) : (a : WithBot
 α) <= maximum l
· 使用定理 `List.mem_map`：∀ {α : Type u_1} {β : Type u_2} {b : β} {f : α → β} {l : L
ist α}, b ∈ List.map f l ↔ ∃ a ∈ l, f a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem degree_list_sum_le (l : List S[X]) : degree l.sum ≤ (l.map natDegree).maximum := by
  apply degree_list_sum_le_of_forall_degree_le
  intro p hp
  by_cases h : p = 0
  · subst h
    simp
  · rw [degree_eq_natDegree h]
    apply List.le_maximum_of_mem'
    rw [List.mem_map]
    use p
    simp [hp]
/-
**Polynomial.natDegree_list_prod_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_list_prod_le (l : List S[X]) : natDegree l.prod <= (l.map natDeg
ree).sum
参数：l : List S[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.apply_prod_le_sum_map`：apply_prod_le_sum_map (h_one : f 1 <= 0) (h_
mul : forall (a b : α), f (a * b) <= f a + f b) : f l.prod <= (l.map f).sum
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Polynomial.natDegree_one`：natDegree_one : natDegree (1 : R[X]) = 0
· 使用定理 `Polynomial.natDegree_mul_le`：natDegree_mul_le {p q : R[X]} : natDegree (
p * q) <= natDegree p + natDegree q
-/
theorem natDegree_list_prod_le (l : List S[X]) : natDegree l.prod ≤ (l.map natDegree).sum :=
  l.apply_prod_le_sum_map _ natDegree_one.le fun _ _ => natDegree_mul_le
/-
**Polynomial.degree_list_prod_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_list_prod_le (l : List S[X]) : degree l.prod <= (l.map degree).sum
参数：l : List S[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.apply_prod_le_sum_map`：apply_prod_le_sum_map (h_one : f 1 <= 0) (h_
mul : forall (a b : α), f (a * b) <= f a + f b) : f l.prod <= (l.map f).sum
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Polynomial.degree_one_le`：degree_one_le : degree (1 : R[X]) <= (0 : With
Bot Nat)
· 使用定理 `Polynomial.degree_mul_le`：degree_mul_le (p q : R[X]) : degree (p * q) <=
 degree p + degree q
-/
theorem degree_list_prod_le (l : List S[X]) : degree l.prod ≤ (l.map degree).sum :=
  l.apply_prod_le_sum_map _ degree_one_le degree_mul_le
/-
**Polynomial.coeff_list_prod_of_natDegree_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al`。
形式化陈述：coeff_list_prod_of_natDegree_le (l : List S[X]) (n : Nat) (hl : forall p i
n l, natDegree p <= n) : coeff (List.prod l) (l.length * n) = (l.map fun p => co
eff p n).prod
参数：l : List S[X]；n : Nat；hl : forall p in l, natDegree p <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Polynomial.coeff_one_zero`：coeff_one_zero : coeff (1 : R[X]) 0 = 1
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.mem_cons_of_mem`：∀ {α : Type u_1} (y : α) {a : α} {l : List α}, a ∈
 l → a ∈ y :: l
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Polynomial.natDegree_list_prod_le`：natDegree_list_prod_le (l : List S[X]
) : natDegree l.prod <= (l.map natDegree).sum
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
· 使用定理 `List.sum_le_card_nsmul`：∀ {M : Type u_3} [inst : AddMonoid M] [inst_1 : 
Preorder M] [AddRightMono M] [AddLeftMono M] (l : List M) (n : M),   (∀ x ∈ l, x
 ≤ n) → l.su…
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Polynomial.coeff_mul_add_eq_of_natDegree_le`：coeff_mul_add_eq_of_natDegr
ee_le {df dg : Nat} {f g : R[X]} (hdf : natDegree f <= df) (hdg : natDegree g <=
 dg) : (f * g).coeff (df + dg) = …
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
-/
theorem coeff_list_prod_of_natDegree_le (l : List S[X]) (n : ℕ) (hl : ∀ p ∈ l, natDegree p ≤ n) :
    coeff (List.prod l) (l.length * n) = (l.map fun p => coeff p n).prod := by
  induction l with
  | nil => simp
  | cons hd tl IH =>
    have hl' : ∀ p ∈ tl, natDegree p ≤ n := fun p hp => hl p (List.mem_cons_of_mem _ hp)
    simp only [List.prod_cons, List.map, List.length]
    rw [add_mul, one_mul, add_comm, ← IH hl', mul_comm tl.length]
    have h : natDegree tl.prod ≤ n * tl.length := by
      refine (natDegree_list_prod_le _).trans ?_
      rw [← tl.length_map natDegree, mul_comm]
      refine List.sum_le_card_nsmul _ _ ?_
      simpa using hl'
    exact coeff_mul_add_eq_of_natDegree_le (hl _ List.mem_cons_self) h

end Semiring

section CommSemiring

variable [CommSemiring R] (f : ι → R[X]) (t : Multiset R[X])

/-
**Polynomial.natDegree_multiset_prod_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_multiset_prod_le : t.prod.natDegree <= (t.map natDegree).sum
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `Polynomial.natDegree_list_prod_le`：natDegree_list_prod_le (l : List S[X]
) : natDegree l.prod <= (l.map natDegree).sum
-/
theorem natDegree_multiset_prod_le : t.prod.natDegree ≤ (t.map natDegree).sum :=
  Quotient.inductionOn t (by simpa using natDegree_list_prod_le)
/-
**Polynomial.natDegree_prod_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_prod_le : (∏ i in s, f i).natDegree <= ∑ i in s, (f i).natDegree
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Polynomial.natDegree_multiset_prod_le`：natDegree_multiset_prod_le : t.pr
od.natDegree <= (t.map natDegree).sum
-/
theorem natDegree_prod_le : (∏ i ∈ s, f i).natDegree ≤ ∑ i ∈ s, (f i).natDegree := by
  simpa using natDegree_multiset_prod_le (s.1.map f)

/-- The degree of a product of polynomials is at most the sum of the degrees,
where the degree of the zero polynomial is ⊥.
-/
/-
**Polynomial.degree_multiset_prod_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_multiset_prod_le : t.prod.degree <= (t.map Polynomial.degree).sum
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `Polynomial.degree_list_prod_le`：degree_list_prod_le (l : List S[X]) : de
gree l.prod <= (l.map degree).sum

--- 原说明 ---
The degree of a product of polynomials is at most the sum of the degrees,
where the degree of the zero polynomial is ⊥.
-/
theorem degree_multiset_prod_le : t.prod.degree ≤ (t.map Polynomial.degree).sum :=
  Quotient.inductionOn t (by simpa using degree_list_prod_le)
/-
**Polynomial.degree_prod_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_prod_le : (∏ i in s, f i).degree <= ∑ i in s, (f i).degree
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Polynomial.degree_multiset_prod_le`：degree_multiset_prod_le : t.prod.deg
ree <= (t.map Polynomial.degree).sum
-/
theorem degree_prod_le : (∏ i ∈ s, f i).degree ≤ ∑ i ∈ s, (f i).degree := by
  simpa only [Multiset.map_map] using! degree_multiset_prod_le (s.1.map f)

/-- The leading coefficient of a product of polynomials is equal to
the product of the leading coefficients, provided that this product is nonzero.

See `Polynomial.leadingCoeff_multiset_prod` (without the `'`) for a version for integral domains,
where this condition is automatically satisfied.
-/
/-
**Polynomial.leadingCoeff_multiset_prod'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeff_multiset_prod' (h : (t.map leadingCoeff).prod != 0) : t.prod.
leadingCoeff = (t.map leadingCoeff).prod
参数：h : (t.map leadingCoeff).prod != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Polynomial.leadingCoeff_mul'`：leadingCoeff_mul' (h : leadingCoeff p * le
adingCoeff q != 0) : leadingCoeff (p * q) = leadingCoeff p * leadingCoeff q
· 使用定理 `right_ne_zero_of_mul`：right_ne_zero_of_mul : a * b != 0 -> b != 0

--- 原说明 ---
The leading coefficient of a product of polynomials is equal to
the product of the leading coefficients, provided that this product is nonzero.

See `Polynomial.leadingCoeff_multiset_prod` (without the `'`) for a version for 
integral domains,
where this condition is automatically satisfied.
-/
theorem leadingCoeff_multiset_prod' (h : (t.map leadingCoeff).prod ≠ 0) :
    t.prod.leadingCoeff = (t.map leadingCoeff).prod := by
  induction t using Multiset.induction_on with | empty => simp | cons a t ih => ?_
  simp only [Multiset.map_cons, Multiset.prod_cons] at h ⊢
  rw [Polynomial.leadingCoeff_mul']
  · rw [ih]
    simp only [ne_eq]
    apply right_ne_zero_of_mul h
  · rw [ih]
    · exact h
    simp only [ne_eq]
    apply right_ne_zero_of_mul h

/-- The leading coefficient of a product of polynomials is equal to
the product of the leading coefficients, provided that this product is nonzero.

See `Polynomial.leadingCoeff_prod` (without the `'`) for a version for integral domains,
where this condition is automatically satisfied.
-/
/-
**Polynomial.leadingCoeff_prod'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeff_prod' (h : (∏ i in s, (f i).leadingCoeff) != 0) : (∏ i in s, 
f i).leadingCoeff = ∏ i in s, (f i).leadingCoeff
参数：h : (∏ i in s, (f i).leadingCoeff) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Polynomial.leadingCoeff_multiset_prod'`：leadingCoeff_multiset_prod' (h :
 (t.map leadingCoeff).prod != 0) : t.prod.leadingCoeff = (t.map leadingCoeff).pr
od
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a

--- 原说明 ---
The leading coefficient of a product of polynomials is equal to
the product of the leading coefficients, provided that this product is nonzero.

See `Polynomial.leadingCoeff_prod` (without the `'`) for a version for integral 
domains,
where this condition is automatically satisfied.
-/
theorem leadingCoeff_prod' (h : (∏ i ∈ s, (f i).leadingCoeff) ≠ 0) :
    (∏ i ∈ s, f i).leadingCoeff = ∏ i ∈ s, (f i).leadingCoeff := by
  simpa using leadingCoeff_multiset_prod' (s.1.map f) (by simpa using h)

/-- The degree of a product of polynomials is equal to
the sum of the degrees, provided that the product of leading coefficients is nonzero.

See `Polynomial.natDegree_multiset_prod` (without the `'`) for a version for integral domains,
where this condition is automatically satisfied.
-/
/-
**Polynomial.natDegree_multiset_prod'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_multiset_prod' (h : (t.map fun f => leadingCoeff f).prod != 0) :
 t.prod.natDegree = (t.map fun f => natDegree f).sum
参数：h : (t.map fun f => leadingCoeff f).prod != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_one`：natDegree_one : natDegree (1 : R[X]) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `Multiset.sum_cons`：∀ {M : Type u_3} [inst : AddCommMonoid M] (a : M) (s 
: Multiset M), (a ::ₘ s).sum = a + s.sum
· 使用定理 `Polynomial.natDegree_mul'`：natDegree_mul' (h : leadingCoeff p * leadingC
oeff q != 0) : natDegree (p * q) = natDegree p + natDegree q
· 使用定理 `Polynomial.leadingCoeff_multiset_prod'`：leadingCoeff_multiset_prod' (h :
 (t.map leadingCoeff).prod != 0) : t.prod.leadingCoeff = (t.map leadingCoeff).pr
od
· 使用定理 `right_ne_zero_of_mul`：right_ne_zero_of_mul : a * b != 0 -> b != 0

--- 原说明 ---
The degree of a product of polynomials is equal to
the sum of the degrees, provided that the product of leading coefficients is non
zero.

See `Polynomial.natDegree_multiset_prod` (without the `'`) for a version for int
egral domains,
where this condition is automatically satisfied.
-/
theorem natDegree_multiset_prod' (h : (t.map fun f => leadingCoeff f).prod ≠ 0) :
    t.prod.natDegree = (t.map fun f => natDegree f).sum := by
  revert h
  refine Multiset.induction_on t ?_ fun a t ih ht => ?_; · simp
  rw [Multiset.map_cons, Multiset.prod_cons] at ht ⊢
  rw [Multiset.sum_cons, Polynomial.natDegree_mul', ih]
  · apply right_ne_zero_of_mul ht
  · rwa [Polynomial.leadingCoeff_multiset_prod']
    apply right_ne_zero_of_mul ht

/-- The degree of a product of polynomials is equal to
the sum of the degrees, provided that the product of leading coefficients is nonzero.

See `Polynomial.natDegree_prod` (without the `'`) for a version for integral domains,
where this condition is automatically satisfied.
-/
/-
**Polynomial.natDegree_prod'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_prod' (h : (∏ i in s, (f i).leadingCoeff) != 0) : (∏ i in s, f i
).natDegree = ∑ i in s, (f i).natDegree
参数：h : (∏ i in s, (f i).leadingCoeff) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Polynomial.natDegree_multiset_prod'`：natDegree_multiset_prod' (h : (t.ma
p fun f => leadingCoeff f).prod != 0) : t.prod.natDegree = (t.map fun f => natDe
gree f).sum
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a

--- 原说明 ---
The degree of a product of polynomials is equal to
the sum of the degrees, provided that the product of leading coefficients is non
zero.

See `Polynomial.natDegree_prod` (without the `'`) for a version for integral dom
ains,
where this condition is automatically satisfied.
-/
theorem natDegree_prod' (h : (∏ i ∈ s, (f i).leadingCoeff) ≠ 0) :
    (∏ i ∈ s, f i).natDegree = ∑ i ∈ s, (f i).natDegree := by
  simpa using natDegree_multiset_prod' (s.1.map f) (by simpa using h)
/-
**Polynomial.natDegree_multiset_prod_of_monic** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial`。
形式化陈述：natDegree_multiset_prod_of_monic (h : forall f in t, Monic f) : t.prod.nat
Degree = (t.map natDegree).sum
参数：h : forall f in t, Monic f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_of_subsingleton`：natDegree_of_subsingleton [Subsing
leton R] : natDegree p = 0
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.map_const'`：∀ {α : Type u_1} {β : Type v} (s : Multiset α) (b :
 β), Multiset.map (fun x => b) s = Multiset.replicate s.card b
· 使用定理 `Multiset.sum_replicate`：∀ {M : Type u_3} [inst : AddCommMonoid M] (n : ℕ
) (a : M), (Multiset.replicate n a).sum = n • a
· 使用定理 `nsmul_zero`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ), n • 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.natDegree_multiset_prod'`：natDegree_multiset_prod' (h : (t.ma
p fun f => leadingCoeff f).prod != 0) : t.prod.natDegree = (t.map fun f => natDe
gree f).sum
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Multiset.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n
 a).prod = a ^ n
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem natDegree_multiset_prod_of_monic (h : ∀ f ∈ t, Monic f) :
    t.prod.natDegree = (t.map natDegree).sum := by
  nontriviality R
  apply natDegree_multiset_prod'
  simp_all
/-
**Polynomial.degree_multiset_prod_of_monic** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
`。
形式化陈述：degree_multiset_prod_of_monic [Nontrivial R] (h : forall f in t, Monic f) 
: t.prod.degree = (t.map degree).sum
参数：h : forall f in t, Monic f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_id'`：map_id' (s : Multiset α) : map (fun x => x) s = s
· 使用定理 `Polynomial.monic_multiset_prod_of_monic`：monic_multiset_prod_of_monic (t
 : Multiset ι) (f : ι -> R[X]) (ht : forall i in t, Monic (f i)) : Monic (t.map 
f).prod
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `Polynomial.natDegree_multiset_prod_of_monic`：natDegree_multiset_prod_of_
monic (h : forall f in t, Monic f) : t.prod.natDegree = (t.map natDegree).sum
· 使用引理 `Nat.cast_multiset_sum`：cast_multiset_sum [AddCommMonoidWithOne R] (s : M
ultiset Nat) : (↑s.sum : R) = (s.map (↑)).sum
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem degree_multiset_prod_of_monic [Nontrivial R] (h : ∀ f ∈ t, Monic f) :
    t.prod.degree = (t.map degree).sum := by
  have : t.prod ≠ 0 := Monic.ne_zero <| by simpa using monic_multiset_prod_of_monic _ _ h
  rw [degree_eq_natDegree this, natDegree_multiset_prod_of_monic _ h, Nat.cast_multiset_sum,
    Multiset.map_map, Function.comp_def,
    Multiset.map_congr rfl (fun f hf => (degree_eq_natDegree (h f hf).ne_zero).symm)]
/-
**Polynomial.natDegree_prod_of_monic** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_prod_of_monic (h : forall i in s, (f i).Monic) : (∏ i in s, f i)
.natDegree = ∑ i in s, (f i).natDegree
参数：h : forall i in s, (f i).Monic。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Polynomial.natDegree_multiset_prod_of_monic`：natDegree_multiset_prod_of_
monic (h : forall f in t, Monic f) : t.prod.natDegree = (t.map natDegree).sum
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem natDegree_prod_of_monic (h : ∀ i ∈ s, (f i).Monic) :
    (∏ i ∈ s, f i).natDegree = ∑ i ∈ s, (f i).natDegree := by
  simpa using natDegree_multiset_prod_of_monic (s.1.map f) (by simpa using h)
/-
**Polynomial.degree_prod_of_monic** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_prod_of_monic [Nontrivial R] (h : forall i in s, (f i).Monic) : (∏ 
i in s, f i).degree = ∑ i in s, (f i).degree
参数：h : forall i in s, (f i).Monic。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Polynomial.degree_multiset_prod_of_monic`：degree_multiset_prod_of_monic 
[Nontrivial R] (h : forall f in t, Monic f) : t.prod.degree = (t.map degree).sum
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem degree_prod_of_monic [Nontrivial R] (h : ∀ i ∈ s, (f i).Monic) :
    (∏ i ∈ s, f i).degree = ∑ i ∈ s, (f i).degree := by
  simpa using degree_multiset_prod_of_monic (s.1.map f) (by simpa using h)
/-
**Polynomial.coeff_multiset_prod_of_natDegree_le** 是 Mathlib 中的一个定理，位于命名空间 `Poly
nomial`。
形式化陈述：coeff_multiset_prod_of_natDegree_le (n : Nat) (hl : forall p in t, natDegr
ee p <= n) : coeff t.prod ((Multiset.card t) * n) = (t.map fun p => coeff p n).p
rod
参数：n : Nat；hl : forall p in t, natDegree p <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `Polynomial.coeff_list_prod_of_natDegree_le`：coeff_list_prod_of_natDegree
_le (l : List S[X]) (n : Nat) (hl : forall p in l, natDegree p <= n) : coeff (Li
st.prod l) (l.length * n) = (l.m…
-/
theorem coeff_multiset_prod_of_natDegree_le (n : ℕ) (hl : ∀ p ∈ t, natDegree p ≤ n) :
    coeff t.prod ((Multiset.card t) * n) = (t.map fun p => coeff p n).prod := by
  induction t using Quotient.inductionOn
  simpa using coeff_list_prod_of_natDegree_le _ _ hl
/-
**Polynomial.coeff_prod_of_natDegree_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_prod_of_natDegree_le (f : ι -> R[X]) (n : Nat) (h : forall p in s, n
atDegree (f p) <= n) : coeff (∏ i in s, f i) (#s * n) = ∏ i in s, coeff (f i) n
参数：f : ι -> R[X]；n : Nat；h : forall p in s, natDegree (f p) <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.card_map`：card_map (f : α -> β) (s) : card (map f s) = card s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Polynomial.coeff_multiset_prod_of_natDegree_le`：coeff_multiset_prod_of_n
atDegree_le (n : Nat) (hl : forall p in t, natDegree p <= n) : coeff t.prod ((Mu
ltiset.card t) * n) = (t.map fun p =…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem coeff_prod_of_natDegree_le (f : ι → R[X]) (n : ℕ) (h : ∀ p ∈ s, natDegree (f p) ≤ n) :
    coeff (∏ i ∈ s, f i) (#s * n) = ∏ i ∈ s, coeff (f i) n := by
  obtain ⟨l, hl⟩ := s
  convert! coeff_multiset_prod_of_natDegree_le (l.map f) n ?_
  · simp
  · simp
  · simpa using h
/-
**Polynomial.coeff_zero_multiset_prod** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_zero_multiset_prod : t.prod.coeff 0 = (t.map fun f => coeff f 0).pro
d
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_one_zero`：coeff_one_zero : coeff (1 : R[X]) 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Polynomial.mul_coeff_zero`：mul_coeff_zero (p q : R[X]) : coeff (p * q) 0
 = coeff p 0 * coeff q 0
-/
theorem coeff_zero_multiset_prod : t.prod.coeff 0 = (t.map fun f => coeff f 0).prod := by
  refine Multiset.induction_on t ?_ fun a t ht => ?_; · simp
  rw [Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons, Polynomial.mul_coeff_zero, ht]
/-
**Polynomial.coeff_zero_prod** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_zero_prod : (∏ i in s, f i).coeff 0 = ∏ i in s, (f i).coeff 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Polynomial.coeff_zero_multiset_prod`：coeff_zero_multiset_prod : t.prod.c
oeff 0 = (t.map fun f => coeff f 0).prod
-/
theorem coeff_zero_prod : (∏ i ∈ s, f i).coeff 0 = ∏ i ∈ s, (f i).coeff 0 := by
  simpa using coeff_zero_multiset_prod (s.1.map f)

end CommSemiring

section CommRing

variable [CommRing R]

open Monic

-- Eventually this can be generalized with Vieta's formulas
-- plus the connection between roots and factorization.
/-
**Polynomial.multiset_prod_X_sub_C_nextCoeff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al`。
形式化陈述：multiset_prod_X_sub_C_nextCoeff (t : Multiset R) : nextCoeff (t.map fun x 
=> X - C x).prod = -t.sum
参数：t : Multiset R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Monic.nextCoeff_multiset_prod`：∀ {R : Type u} {ι : Type y} [i
nst : CommSemiring R] (t : Multiset ι) (f : ι → Polynomial R),   (∀ i ∈ t, (f i)
.Monic) → (Multiset.map f t).p…
· 使用定理 `Polynomial.monic_X_sub_C`：monic_X_sub_C (x : R) : Monic (X - C x)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Polynomial.nextCoeff_X_sub_C`：nextCoeff_X_sub_C [Ring S] (c : S) : nextC
oeff (X - C c) = -c
· 使用定理 `Multiset.sum_hom`：∀ {M : Type u_5} {N : Type u_6} [inst : AddCommMonoid 
M] [inst_1 : AddCommMonoid N] (s : Multiset M) {F : Type u_8}   [inst_2 : FunLik
e F M …
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem multiset_prod_X_sub_C_nextCoeff (t : Multiset R) :
    nextCoeff (t.map fun x => X - C x).prod = -t.sum := by
  rw [nextCoeff_multiset_prod]
  · simp only [nextCoeff_X_sub_C]
    exact t.sum_hom (-AddMonoidHom.id R)
  · intros
    apply monic_X_sub_C
/-
**Polynomial.prod_X_sub_C_nextCoeff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：prod_X_sub_C_nextCoeff {s : Finset ι} (f : ι -> R) : nextCoeff (∏ i in s, 
(X - C (f i))) = -∑ i in s, f i
参数：f : ι -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Polynomial.multiset_prod_X_sub_C_nextCoeff`：multiset_prod_X_sub_C_nextCo
eff (t : Multiset R) : nextCoeff (t.map fun x => X - C x).prod = -t.sum
-/
theorem prod_X_sub_C_nextCoeff {s : Finset ι} (f : ι → R) :
    nextCoeff (∏ i ∈ s, (X - C (f i))) = -∑ i ∈ s, f i := by
  simpa using multiset_prod_X_sub_C_nextCoeff (s.1.map f)
/-
**Polynomial.multiset_prod_X_sub_C_coeff_card_pred** 是 Mathlib 中的一个定理，位于命名空间 `Po
lynomial`。
形式化陈述：multiset_prod_X_sub_C_coeff_card_pred (t : Multiset R) (ht : 0 < Multiset.
card t) : (t.map fun x => X - C x).prod.coeff ((Multiset.card t) - 1) = -t.sum
参数：t : Multiset R；ht : 0 < Multiset.card t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.nextCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polyn
omial R),   p.nextCoeff = if p.natDegree = 0 then 0 else p.coeff (p.natDegree - 
1)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Polynomial.natDegree_multiset_prod_of_monic`：natDegree_multiset_prod_of_
monic (h : forall f in t, Monic f) : t.prod.natDegree = (t.map natDegree).sum
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Polynomial.monic_X_sub_C`：monic_X_sub_C (x : R) : Monic (X - C x)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.card_pos_iff_exists_mem`：card_pos_iff_exists_mem {s : Multiset 
α} : 0 < card s ↔ exists a, a in s
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Polynomial.natDegree_X_sub_C`：natDegree_X_sub_C (x : R) : (X - C x).natD
egree = 1
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Polynomial.natDegree_sub_C`：natDegree_sub_C {a : R} : natDegree (p - C a
) = natDegree p
· 使用定理 `Polynomial.natDegree_X`：natDegree_X : (X : R[X]).natDegree = 1
· 使用定理 `Multiset.map_const'`：∀ {α : Type u_1} {β : Type v} (s : Multiset α) (b :
 β), Multiset.map (fun x => b) s = Multiset.replicate s.card b
· 使用定理 `Multiset.sum_replicate`：∀ {M : Type u_3} [inst : AddCommMonoid M] (n : ℕ
) (a : M), (Multiset.replicate n a).sum = n • a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.multiset_prod_X_sub_C_nextCoeff`：multiset_prod_X_sub_C_nextCo
eff (t : Multiset R) : nextCoeff (t.map fun x => X - C x).prod = -t.sum
-/
theorem multiset_prod_X_sub_C_coeff_card_pred (t : Multiset R) (ht : 0 < Multiset.card t) :
    (t.map fun x => X - C x).prod.coeff ((Multiset.card t) - 1) = -t.sum := by
  nontriviality R
  convert! multiset_prod_X_sub_C_nextCoeff (by assumption)
  rw [nextCoeff, if_neg]
  swap
  · rw [natDegree_multiset_prod_of_monic]
    swap
    · simp only [Multiset.mem_map]
      rintro _ ⟨_, _, rfl⟩
      apply monic_X_sub_C
    simp_rw [Multiset.sum_eq_zero_iff, Multiset.mem_map]
    obtain ⟨x, hx⟩ := card_pos_iff_exists_mem.mp ht
    exact fun h => one_ne_zero <| h 1 ⟨_, ⟨x, hx, rfl⟩, natDegree_X_sub_C _⟩
  congr; rw [natDegree_multiset_prod_of_monic] <;> · simp [monic_X_sub_C]
/-
**Polynomial.prod_X_sub_C_coeff_card_pred** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`
。
形式化陈述：prod_X_sub_C_coeff_card_pred (s : Finset ι) (f : ι -> R) (hs : 0 < #s) : (
∏ i in s, (X - C (f i))).coeff (#s - 1) = -∑ i in s, f i
参数：s : Finset ι；f : ι -> R；hs : 0 < #s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.card_map`：card_map (f : α -> β) (s) : card (map f s) = card s
· 使用定理 `Polynomial.multiset_prod_X_sub_C_coeff_card_pred`：multiset_prod_X_sub_C_
coeff_card_pred (t : Multiset R) (ht : 0 < Multiset.card t) : (t.map fun x => X 
- C x).prod.coeff ((Multiset.card t) -…
-/
theorem prod_X_sub_C_coeff_card_pred (s : Finset ι) (f : ι → R) (hs : 0 < #s) :
    (∏ i ∈ s, (X - C (f i))).coeff (#s - 1) = -∑ i ∈ s, f i := by
  simpa using multiset_prod_X_sub_C_coeff_card_pred (s.1.map f) (by simpa using hs)
/-
**Polynomial.degree_sum_eq_of_linearIndepOn** 是 Mathlib 中的一个引理，位于命名空间 `Polynomia
l`。
形式化陈述：degree_sum_eq_of_linearIndepOn {A : Type*} [CommRing A] [Algebra R A] {f :
 ι -> R[X]} {v : ι -> A} (h : LinearIndepOn R v s) : (∑ i in s, v i • (f i).map 
(algebraMap R A)).degree = s.sup (fun i => (f i).degree)
参数：h : LinearIndepOn R v s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Polynomial.degree_sum_le`：degree_sum_le (s : Finset ι) (f : ι -> R[X]) :
 degree (∑ i in s, f i) <= s.sup fun b => degree (f b)
· 使用定理 `Finset.sup_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α]
 [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   (∀ b ∈ s, f b ≤ a) 
→ s…
· 使用定理 `Polynomial.degree_smul_le`：degree_smul_le {S : Type*} [SMulZeroClass S R
] (a : S) (p : R[X]) : degree (a • p) <= degree p
· 使用引理 `Polynomial.degree_map_le`：degree_map_le : degree (p.map f) <= degree p
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `Polynomial.le_degree_of_ne_zero`：le_degree_of_ne_zero (h : coeff p n != 
0) : (n : WithBot Nat) <= degree p
· 使用定理 `Polynomial.finsetSum_coeff`：finsetSum_coeff {ι : Type*} (s : Finset ι) (
f : ι -> R[X]) (n : Nat) : coeff (∑ b in s, f b) n = ∑ b in s, coeff (f b) n
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.coeff_smul`：coeff_smul [SMulZeroClass S R] (r : S) (p : R[X])
 (n : Nat) : coeff (r • p) n = r • coeff p n
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
· 使用引理 `linearIndepOn_finset_iff`：linearIndepOn_finset_iff {s : Finset ι} : Line
arIndepOn R v s ↔ forall f : ι -> R, ∑ i in s, f i • v i = 0 -> forall i in s, f
 i = 0
-/
lemma degree_sum_eq_of_linearIndepOn {A : Type*} [CommRing A] [Algebra R A] {f : ι → R[X]}
    {v : ι → A} (h : LinearIndepOn R v s) :
    (∑ i ∈ s, v i • (f i).map (algebraMap R A)).degree = s.sup (fun i ↦ (f i).degree) := by
  apply le_antisymm
  · exact (degree_sum_le s _).trans <| Finset.sup_le fun i hi ↦ (degree_smul_le _ _).trans <|
      degree_map_le.trans <| Finset.le_sup (f := fun i ↦ (f i).degree) hi
  · apply Finset.sup_le
    intro i hi
    by_cases hf : f i = 0
    · simp [hf]
    rw [degree_eq_natDegree hf]
    apply le_degree_of_ne_zero
    rw [finsetSum_coeff]
    conv in (fun _ ↦ _) =>
      ext
      rw [coeff_smul, smul_eq_mul, coeff_map, mul_comm, ← Algebra.smul_def]
    intro H
    exact hf (leadingCoeff_eq_zero.mp (linearIndepOn_finset_iff.mp h _ H i hi))

-- Note: Proof duplicated from the `degree` version, since the statements don't
-- trivially follow from each other.
/-
**Polynomial.natDegree_sum_eq_of_linearIndepOn** 是 Mathlib 中的一个引理，位于命名空间 `Polyno
mial`。
形式化陈述：natDegree_sum_eq_of_linearIndepOn {A : Type*} [CommRing A] [Algebra R A] {
f : ι -> R[X]} {v : ι -> A} (h : LinearIndepOn R v s) : (∑ i in s, v i • (f i).m
ap (algebraMap R A)).natDegree = s.sup (fun i => (f i).natDegree)
参数：h : LinearIndepOn R v s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Polynomial.natDegree_sum_le_of_forall_le`：natDegree_sum_le_of_forall_le 
{n : Nat} (f : ι -> S[X]) (h : forall i in s, natDegree (f i) <= n) : natDegree 
(∑ i in s, f i) <= n
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Polynomial.natDegree_smul_le`：natDegree_smul_le {S : Type*} [SMulZeroCla
ss S R] (a : S) (p : R[X]) : natDegree (a • p) <= natDegree p
· 使用引理 `Polynomial.natDegree_map_le`：natDegree_map_le : natDegree (p.map f) <= n
atDegree p
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `Finset.sup_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α]
 [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   (∀ b ∈ s, f b ≤ a) 
→ s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Polynomial.le_natDegree_of_ne_zero`：le_natDegree_of_ne_zero (h : coeff p
 n != 0) : n <= natDegree p
· 使用定理 `Polynomial.finsetSum_coeff`：finsetSum_coeff {ι : Type*} (s : Finset ι) (
f : ι -> R[X]) (n : Nat) : coeff (∑ b in s, f b) n = ∑ b in s, coeff (f b) n
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.coeff_smul`：coeff_smul [SMulZeroClass S R] (r : S) (p : R[X])
 (n : Nat) : coeff (r • p) n = r • coeff p n
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
· 使用引理 `linearIndepOn_finset_iff`：linearIndepOn_finset_iff {s : Finset ι} : Line
arIndepOn R v s ↔ forall f : ι -> R, ∑ i in s, f i • v i = 0 -> forall i in s, f
 i = 0
-/
lemma natDegree_sum_eq_of_linearIndepOn {A : Type*} [CommRing A] [Algebra R A] {f : ι → R[X]}
    {v : ι → A} (h : LinearIndepOn R v s) :
    (∑ i ∈ s, v i • (f i).map (algebraMap R A)).natDegree = s.sup (fun i ↦ (f i).natDegree) := by
  apply le_antisymm
  · exact natDegree_sum_le_of_forall_le _ _ fun i hi ↦ (natDegree_smul_le _ _).trans <|
      natDegree_map_le.trans <| Finset.le_sup (f := fun i ↦ (f i).natDegree) hi
  · apply Finset.sup_le
    intro i hi
    by_cases hf : f i = 0
    · simp [hf]
    apply le_natDegree_of_ne_zero
    rw [finsetSum_coeff]
    conv in (fun _ ↦ _) =>
      ext
      rw [coeff_smul, smul_eq_mul, coeff_map, mul_comm, ← Algebra.smul_def]
    intro H
    exact hf (leadingCoeff_eq_zero.mp (linearIndepOn_finset_iff.mp h _ H i hi))

variable [Nontrivial R]

@[simp]
/-
**Polynomial.natDegree_multiset_prod_X_sub_C_eq_card** 是 Mathlib 中的一个引理，位于命名空间 `
Polynomial`。
形式化陈述：natDegree_multiset_prod_X_sub_C_eq_card (s : Multiset R) : (s.map (X - C ·
)).prod.natDegree = Multiset.card s
参数：s : Multiset R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_multiset_prod_of_monic`：natDegree_multiset_prod_of_
monic (h : forall f in t, Monic f) : t.prod.natDegree = (t.map natDegree).sum
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.forall_mem_map_iff`：forall_mem_map_iff {f : α -> β} {p : β -> P
rop} {s : Multiset α} : (forall y in s.map f, p y) ↔ forall x in s, p (f x)
· 使用定理 `Polynomial.monic_X_sub_C`：monic_X_sub_C (x : R) : Monic (X - C x)
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Polynomial.natDegree_sub_C`：natDegree_sub_C {a : R} : natDegree (p - C a
) = natDegree p
· 使用定理 `Polynomial.natDegree_X`：natDegree_X : (X : R[X]).natDegree = 1
· 使用定理 `Multiset.map_const'`：∀ {α : Type u_1} {β : Type v} (s : Multiset α) (b :
 β), Multiset.map (fun x => b) s = Multiset.replicate s.card b
· 使用定理 `Multiset.sum_replicate`：∀ {M : Type u_3} [inst : AddCommMonoid M] (n : ℕ
) (a : M), (Multiset.replicate n a).sum = n • a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma natDegree_multiset_prod_X_sub_C_eq_card (s : Multiset R) :
    (s.map (X - C ·)).prod.natDegree = Multiset.card s := by
  rw [natDegree_multiset_prod_of_monic, Multiset.map_map]
  · simp
  · exact Multiset.forall_mem_map_iff.2 fun a _ => monic_X_sub_C a
/-
**Polynomial.natDegree_finsetProd_X_sub_C_eq_card** 是 Mathlib 中的一个定理，位于命名空间 `Pol
ynomial`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] [Nontrivial R] {α : Type u_1} (s : Fins
et α) (f : α → R),   (∏ a ∈ s, (Polynomial.X - Polynomial.C (f a))).natDegree = 
s.card
参数：s : Finset α；f : α → R；∏ a ∈ s, (Polynomial.X - Polynomial.C (f a))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod.eq_1`：∀ {ι : Type u_1} {M : Type u_3} [inst : CommMonoid M] 
(s : Finset ι) (f : ι → M), s.prod f = (Multiset.map f s.val).prod
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用引理 `Polynomial.natDegree_multiset_prod_X_sub_C_eq_card`：natDegree_multiset_p
rod_X_sub_C_eq_card (s : Multiset R) : (s.map (X - C ·)).prod.natDegree = Multis
et.card s
· 使用定理 `Multiset.card_map`：card_map (f : α -> β) (s) : card (map f s) = card s
· 使用定理 `Finset.card.eq_1`：∀ {α : Type u_1} (s : Finset α), s.card = s.val.card
-/
@[simp] lemma natDegree_finsetProd_X_sub_C_eq_card {α} (s : Finset α) (f : α → R) :
    (∏ a ∈ s, (X - C (f a))).natDegree = s.card := by
  rw [Finset.prod, ← (X - C ·).comp_def f, ← Multiset.map_map,
    natDegree_multiset_prod_X_sub_C_eq_card, Multiset.card_map, Finset.card]

@[deprecated (since := "2026-04-08")]
alias natDegree_finset_prod_X_sub_C_eq_card := natDegree_finsetProd_X_sub_C_eq_card

end CommRing

section NoZeroDivisors

section Semiring

variable [Semiring R] [NoZeroDivisors R]

/-- The degree of a product of polynomials is equal to
the sum of the degrees, where the degree of the zero polynomial is ⊥.
`[Nontrivial R]` is needed, otherwise for `l = []` we have `⊥` in the LHS and `0` in the RHS.
-/
/-
**Polynomial.degree_list_prod** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_list_prod [Nontrivial R] (l : List R[X]) : l.prod.degree = (l.map d
egree).sum
参数：l : List R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_list_prod`：map_list_prod {F : Type*} [FunLike F M N] [MonoidHomClass
 F M N] (f : F) (l : List M) : f l.prod = (l.map f).prod

--- 原说明 ---
The degree of a product of polynomials is equal to
the sum of the degrees, where the degree of the zero polynomial is ⊥.
`[Nontrivial R]` is needed, otherwise for `l = []` we have `⊥` in the LHS and `0
` in the RHS.
-/
theorem degree_list_prod [Nontrivial R] (l : List R[X]) : l.prod.degree = (l.map degree).sum :=
  map_list_prod (@degreeMonoidHom R _ _ _) l

end Semiring

section CommSemiring

variable [CommSemiring R] [NoZeroDivisors R] (f : ι → R[X]) (t : Multiset R[X])

/-- The degree of a product of polynomials is equal to
the sum of the degrees.

See `Polynomial.natDegree_prod'` (with a `'`) for a version for commutative semirings,
where additionally, the product of the leading coefficients must be nonzero.
-/
/-
**Polynomial.natDegree_prod** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_prod (h : forall i in s, f i != 0) : (∏ i in s, f i).natDegree =
 ∑ i in s, (f i).natDegree
参数：h : forall i in s, f i != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_of_subsingleton`：natDegree_of_subsingleton [Subsing
leton R] : natDegree p = 0
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.natDegree_prod'`：natDegree_prod' (h : (∏ i in s, (f i).leadin
gCoeff) != 0) : (∏ i in s, f i).natDegree = ∑ i in s, (f i).natDegree
· 使用引理 `Finset.prod_ne_zero_iff`：prod_ne_zero_iff : ∏ x in s, f x != 0 ↔ forall 
a in s, f a != 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
The degree of a product of polynomials is equal to
the sum of the degrees.

See `Polynomial.natDegree_prod'` (with a `'`) for a version for commutative semi
rings,
where additionally, the product of the leading coefficients must be nonzero.
-/
theorem natDegree_prod (h : ∀ i ∈ s, f i ≠ 0) :
    (∏ i ∈ s, f i).natDegree = ∑ i ∈ s, (f i).natDegree := by
  nontriviality R
  apply natDegree_prod'
  rw [prod_ne_zero_iff]
  intro x hx; simp [h x hx]
/-
**Polynomial.natDegree_multiset_prod** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_multiset_prod (h : (0 : R[X]) ∉ t) : natDegree t.prod = (t.map n
atDegree).sum
参数：h : (0 : R[X]) ∉ t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_of_subsingleton`：natDegree_of_subsingleton [Subsing
leton R] : natDegree p = 0
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.map_const'`：∀ {α : Type u_1} {β : Type v} (s : Multiset α) (b :
 β), Multiset.map (fun x => b) s = Multiset.replicate s.card b
· 使用定理 `Multiset.sum_replicate`：∀ {M : Type u_3} [inst : AddCommMonoid M] (n : ℕ
) (a : M), (Multiset.replicate n a).sum = n • a
· 使用定理 `nsmul_zero`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ), n • 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.natDegree_multiset_prod'`：natDegree_multiset_prod' (h : (t.ma
p fun f => leadingCoeff f).prod != 0) : t.prod.natDegree = (t.map fun f => natDe
gree f).sum
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem natDegree_multiset_prod (h : (0 : R[X]) ∉ t) :
    natDegree t.prod = (t.map natDegree).sum := by
  nontriviality R
  rw [natDegree_multiset_prod']
  simp_rw [Ne, Multiset.prod_eq_zero_iff, Multiset.mem_map, leadingCoeff_eq_zero]
  rintro ⟨_, h, rfl⟩
  contradiction

/-- The degree of a product of polynomials is equal to
the sum of the degrees, where the degree of the zero polynomial is ⊥.
-/
/-
**Polynomial.degree_multiset_prod** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_multiset_prod [Nontrivial R] : t.prod.degree = (t.map fun f => degr
ee f).sum
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_multiset_prod`：∀ {F : Type u_1} {M : Type u_5} {N : Type u_6} [inst 
: CommMonoid M] [inst_1 : CommMonoid N] [inst_2 : FunLike F M N]   [MonoidHomCla
ss F M …

--- 原说明 ---
The degree of a product of polynomials is equal to
the sum of the degrees, where the degree of the zero polynomial is ⊥.
-/
theorem degree_multiset_prod [Nontrivial R] : t.prod.degree = (t.map fun f => degree f).sum :=
  map_multiset_prod (@degreeMonoidHom R _ _ _) _

/-- The degree of a product of polynomials is equal to
the sum of the degrees, where the degree of the zero polynomial is ⊥.
-/
/-
**Polynomial.degree_prod** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_prod [Nontrivial R] : (∏ i in s, f i).degree = ∑ i in s, (f i).degr
ee
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…

--- 原说明 ---
The degree of a product of polynomials is equal to
the sum of the degrees, where the degree of the zero polynomial is ⊥.
-/
theorem degree_prod [Nontrivial R] : (∏ i ∈ s, f i).degree = ∑ i ∈ s, (f i).degree :=
  map_prod (@degreeMonoidHom R _ _ _) _ _

set_option backward.isDefEq.respectTransparency false in
/-- The leading coefficient of a product of polynomials is equal to
the product of the leading coefficients.

See `Polynomial.leadingCoeff_multiset_prod'` (with a `'`) for a version for commutative semirings,
where additionally, the product of the leading coefficients must be nonzero.
-/
/-
**Polynomial.leadingCoeff_multiset_prod** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeff_multiset_prod : t.prod.leadingCoeff = (t.map fun f => leading
Coeff f).prod
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Polynomial.leadingCoeffHom_apply`：leadingCoeffHom_apply (p : R[X]) : lea
dingCoeffHom p = leadingCoeff p
· 使用定理 `MonoidHom.map_multiset_prod`：∀ {M : Type u_5} {N : Type u_6} [inst : Com
mMonoid M] [inst_1 : CommMonoid N] (f : M →* N) (s : Multiset M),   f s.prod = (
Multiset.map (⇑f)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The leading coefficient of a product of polynomials is equal to
the product of the leading coefficients.

See `Polynomial.leadingCoeff_multiset_prod'` (with a `'`) for a version for comm
utative semirings,
where additionally, the product of the leading coefficients must be nonzero.
-/
theorem leadingCoeff_multiset_prod :
    t.prod.leadingCoeff = (t.map fun f => leadingCoeff f).prod := by
  rw [← leadingCoeffHom_apply, MonoidHom.map_multiset_prod]
  simp only [leadingCoeffHom_apply]

/-- The leading coefficient of a product of polynomials is equal to
the product of the leading coefficients.

See `Polynomial.leadingCoeff_prod'` (with a `'`) for a version for commutative semirings,
where additionally, the product of the leading coefficients must be nonzero.
-/
/-
**Polynomial.leadingCoeff_prod** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeff_prod : (∏ i in s, f i).leadingCoeff = ∏ i in s, (f i).leading
Coeff
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Polynomial.leadingCoeff_multiset_prod`：leadingCoeff_multiset_prod : t.pr
od.leadingCoeff = (t.map fun f => leadingCoeff f).prod

--- 原说明 ---
The leading coefficient of a product of polynomials is equal to
the product of the leading coefficients.

See `Polynomial.leadingCoeff_prod'` (with a `'`) for a version for commutative s
emirings,
where additionally, the product of the leading coefficients must be nonzero.
-/
theorem leadingCoeff_prod : (∏ i ∈ s, f i).leadingCoeff = ∏ i ∈ s, (f i).leadingCoeff := by
  simpa using leadingCoeff_multiset_prod (s.1.map f)

end CommSemiring

end NoZeroDivisors

end Polynomial

