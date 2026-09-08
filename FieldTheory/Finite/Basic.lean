/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Joey van Langen, Casper Putz
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.Data.ZMod.ValMinAbs
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.FieldTheory.Galois.Notation
public import Mathlib.FieldTheory.Perfect

/-!
# Finite fields

This file contains basic results about finite fields.
Throughout most of this file, `K` denotes a finite field
and `q` is notation for the cardinality of `K`.

See `RingTheory.IntegralDomain` for the fact that the unit group of a finite field is a
cyclic group, as well as the fact that every finite integral domain is a field
(`Fintype.fieldOfDomain`).

## Main results

1. `Fintype.card_units`: The unit group of a finite field has cardinality `q - 1`.
2. `sum_pow_units`: The sum of `x^i`, where `x` ranges over the units of `K`, is
  - `q-1` if `q-1 ∣ i`
  - `0`   otherwise
3. `FiniteField.card`: The cardinality `q` is a power of the characteristic of `K`.
  See `FiniteField.card'` for a variant.

## Notation

Throughout most of this file, `K` denotes a finite field
and `q` is notation for the cardinality of `K`.

## Implementation notes

While `Fintype Kˣ` can be inferred from `Fintype K` in the presence of `DecidableEq K`,
in this file we take the `Fintype Kˣ` argument directly to reduce the chance of typeclass
diamonds, as `Fintype` carries data.

-/

@[expose] public section


variable {K : Type*} {R : Type*}

local notation "q" => Fintype.card K

open Finset

open scoped Polynomial

namespace FiniteField

section Polynomial

variable [CommRing R] [IsDomain R]

open Polynomial

/-- The cardinality of a field is at most `n` times the cardinality of the image of a degree `n`
  polynomial -/
/-
**FiniteField.card_image_polynomial_eval** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField`
。
形式化陈述：card_image_polynomial_eval [DecidableEq R] [Fintype R] {p : R[X]} (hp : 0 
< p.degree) : Fintype.card R <= natDegree p * #(univ.image fun x => eval x p)
参数：hp : 0 < p.degree。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_le_mul_card_image`：card_le_mul_card_image {f : α -> β} (s : 
Finset α) (n : Nat) (hn : forall b in s.image f, #{a in s | f a = b} <= n) : #s 
<= n * #(s.image f)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.mem_roots_sub_C`：mem_roots_sub_C {p : R[X]} {a x : R} (hp0 : 
0 < degree p) : x in (p - C a).roots ↔ p.eval x = a
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Multiset.toFinset_card_le`：Multiset.toFinset_card_le : #m.toFinset <= Mu
ltiset.card m
· 使用定理 `Polynomial.card_roots_sub_C'`：card_roots_sub_C' {p : R[X]} {a : R} (hp0 
: 0 < degree p) : Multiset.card (p - C a).roots <= natDegree p

--- 原说明 ---
The cardinality of a field is at most `n` times the cardinality of the image of 
a degree `n`
  polynomial
-/
theorem card_image_polynomial_eval [DecidableEq R] [Fintype R] {p : R[X]} (hp : 0 < p.degree) :
    Fintype.card R ≤ natDegree p * #(univ.image fun x => eval x p) :=
  Finset.card_le_mul_card_image _ _ (fun a _ =>
    calc
      _ = #(p - C a).roots.toFinset :=
        congr_arg card (by simp [Finset.ext_iff, ← mem_roots_sub_C hp])
      _ ≤ Multiset.card (p - C a).roots := Multiset.toFinset_card_le _
      _ ≤ _ := card_roots_sub_C' hp)

/-- If `f` and `g` are quadratic polynomials, then the `f.eval a + g.eval b = 0` has a solution. -/
/-
**FiniteField.exists_root_sum_quadratic** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField`。
形式化陈述：exists_root_sum_quadratic [Fintype R] {f g : R[X]} (hf2 : degree f = 2) (h
g2 : degree g = 2) (hR : Fintype.card R % 2 = 1) : exists a b, f.eval a + g.eval
 b = 0
参数：hf2 : degree f = 2；hg2 : degree g = 2；hR : Fintype.card R % 2 = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `Nat.mul_le_mul_left`：∀ {n m : ℕ} (k : ℕ), n ≤ m → k * n ≤ k * m
· 使用定理 `Finset.card_le_univ`：Finset.card_le_univ [Fintype α] (s : Finset α) : #s
 <= Fintype.card α
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `add_lt_add_of_lt_of_le`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preord
er α] [AddLeftMono α] [AddRightStrictMono α] {a b c d : α},   a < b → c ≤ d → a 
+ c < b + d
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
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `FiniteField.card_image_polynomial_eval`：card_image_polynomial_eval [Deci
dableEq R] [Fintype R] {p : R[X]} (hp : 0 < p.degree) : Fintype.card R <= natDeg
ree p * #(univ.image fun x =…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq_some`：natDegree_eq_of_degree_eq_som
e {p : R[X]} {n : Nat} (h : degree p = n) : natDegree p = n
· 使用定理 `Nat.mul_mod_right`：∀ (m n : ℕ), m * n % m = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Polynomial.degree_neg`：degree_neg (p : R[X]) : degree (-p) = degree p
· 使用定理 `Finset.card_union_of_disjoint`：∀ {α : Type u_1} {s t : Finset α} [inst :
 DecidableEq α], Disjoint s t → (s ∪ t).card = s.card + t.card
· 使用定理 `Polynomial.natDegree_neg`：natDegree_neg (p : R[X]) : natDegree (-p) = na
tDegree p
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` and `g` are quadratic polynomials, then the `f.eval a + g.eval b = 0` has
 a solution.
-/
theorem exists_root_sum_quadratic [Fintype R] {f g : R[X]} (hf2 : degree f = 2) (hg2 : degree g = 2)
    (hR : Fintype.card R % 2 = 1) : ∃ a b, f.eval a + g.eval b = 0 :=
  letI := Classical.decEq R
  suffices ¬Disjoint (univ.image fun x : R => eval x f)
    (univ.image fun x : R => eval x (-g)) by
    simp only [disjoint_left, mem_image] at this
    push Not at this
    rcases this with ⟨x, ⟨a, _, ha⟩, ⟨b, _, hb⟩⟩
    exact ⟨a, b, by rw [ha, ← hb, eval_neg, neg_add_cancel]⟩
  fun hd : Disjoint _ _ =>
  lt_irrefl (2 * #((univ.image fun x : R => eval x f) ∪ univ.image fun x : R => eval x (-g))) <|
    calc 2 * #((univ.image fun x : R => eval x f) ∪ univ.image fun x : R => eval x (-g))
        ≤ 2 * Fintype.card R := Nat.mul_le_mul_left _ (Finset.card_le_univ _)
      _ = Fintype.card R + Fintype.card R := two_mul _
      _ < natDegree f * #(univ.image fun x : R => eval x f) +
            natDegree (-g) * #(univ.image fun x : R => eval x (-g)) :=
        (add_lt_add_of_lt_of_le
          (lt_of_le_of_ne (card_image_polynomial_eval (by rw [hf2]; decide))
            (mt (congr_arg (· % 2)) (by simp [natDegree_eq_of_degree_eq_some hf2, hR])))
          (card_image_polynomial_eval (by rw [degree_neg, hg2]; decide)))
      _ = 2 * #((univ.image fun x : R => eval x f) ∪ univ.image fun x : R => eval x (-g)) := by
        rw [card_union_of_disjoint hd]
        simp [natDegree_eq_of_degree_eq_some hf2, natDegree_eq_of_degree_eq_some hg2, mul_add]

end Polynomial

/-
**FiniteField.prod_univ_units_id_eq_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `FiniteFie
ld`。
形式化陈述：prod_univ_units_id_eq_neg_one [CommRing K] [IsDomain K] [Fintype Kˣ] : ∏ x
 : Kˣ, x = (-1 : Kˣ)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.prod_involution`：prod_involution (g : forall a in s, ι) (hg₁ : fo
rall a ha, f a * f (g a ha) = 1) (hg₃ : forall a ha, f a != 1 -> g a ha != a) (g
_mem : foral…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `inv_eq_iff_eq_inv`：inv_eq_iff_eq_inv : a⁻¹ = b ↔ a = b⁻¹
· 使用引理 `inv_neg`：inv_neg : (-a)⁻¹ = -a⁻¹
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem prod_univ_units_id_eq_neg_one [CommRing K] [IsDomain K] [Fintype Kˣ] :
    ∏ x : Kˣ, x = (-1 : Kˣ) := by
  classical
    have : (∏ x ∈ (@univ Kˣ _).erase (-1), x) = 1 :=
      prod_involution (fun x _ => x⁻¹) (by simp)
        (fun a => by simp +contextual [Units.inv_eq_self_iff])
        (fun a => by simp [@inv_eq_iff_eq_inv _ _ a]) (by simp)
    rw [← insert_erase (mem_univ (-1 : Kˣ)), prod_insert (notMem_erase _ _), this, mul_one]
/-
**FiniteField.card_cast_subgroup_card_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `FiniteF
ield`。
形式化陈述：card_cast_subgroup_card_ne_zero [Ring K] [NoZeroDivisors K] [Nontrivial K]
 (G : Subgroup Kˣ) [Fintype G] : (Fintype.card G : K) != 0
参数：G : Subgroup Kˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CharP.exists`：∀ (R : Type u_1) [inst : NonAssocSemiring R], ∃ p, CharP R
 p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CharP.cast_eq_zero_iff`：∀ (R : Type u_2) {inst : AddMonoidWithOne R} (p 
: outParam ℕ) [self : CharP R p] (x : ℕ), ↑x = 0 ↔ p ∣ x
· 使用引理 `CharP.char_is_prime_or_zero`：char_is_prime_or_zero (p : Nat) [hc : CharP
 R p] : Nat.Prime p ∨ p = 0
· 使用定理 `exists_prime_orderOf_dvd_card`：∀ {G : Type u_3} [inst : Group G] [inst_1
 : Fintype G] (p : ℕ) [hp : Fact (Nat.Prime p)],   p ∣ Fintype.card G → ∃ x, ord
erOf x = p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `orderOf_units`：orderOf_units {y : Gˣ} : orderOf (y : G) = orderOf y
· 使用引理 `Subgroup.orderOf_coe`：orderOf_coe (a : H) : orderOf (a : G) = orderOf a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_left_inj`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, b - a = 
c - a ↔ b = c
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_zero_of_pow_eq_zero`：eq_zero_of_pow_eq_zero [Zero R] [Pow R Nat] [IsR
educed R] {n : Nat} (h : x ^ n = 0) : x = 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用引理 `sub_pow_char_of_commute`：sub_pow_char_of_commute (h : Commute x y) : (x 
- y) ^ p = x ^ p - y ^ p
· 使用定理 `Commute.one_right`：one_right (a : M) : Commute a 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `pow_orderOf_eq_one`：pow_orderOf_eq_one (x : G) : x ^ orderOf x = 1
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `orderOf_one`：orderOf_one : orderOf (1 : G) = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Fintype.card_pos`：card_pos [h : Nonempty α] : 0 < card α
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `Nat.eq_zero_of_zero_dvd`：∀ {a : ℕ}, 0 ∣ a → a = 0
-/
theorem card_cast_subgroup_card_ne_zero [Ring K] [NoZeroDivisors K] [Nontrivial K]
    (G : Subgroup Kˣ) [Fintype G] : (Fintype.card G : K) ≠ 0 := by
  let n := Fintype.card G
  intro nzero
  have ⟨p, char_p⟩ := CharP.exists K
  have hd : p ∣ n := (CharP.cast_eq_zero_iff K p n).mp nzero
  cases CharP.char_is_prime_or_zero K p with
  | inr pzero =>
    exact (Fintype.card_pos).ne' <| Nat.eq_zero_of_zero_dvd <| pzero ▸ hd
  | inl pprime =>
    have fact_pprime := Fact.mk pprime
    -- G has an element x of order p by Cauchy's theorem
    have ⟨x, hx⟩ := exists_prime_orderOf_dvd_card p hd
    -- F has an element u (= ↑↑x) of order p
    let u := ((x : Kˣ) : K)
    have hu : orderOf u = p := by rwa [orderOf_units, Subgroup.orderOf_coe]
    -- u ^ p = 1 implies (u - 1) ^ p = 0 and hence u = 1 ...
    have h : u = 1 := by
      rw [← sub_left_inj, sub_self 1]
      apply eq_zero_of_pow_eq_zero (n := p)
      rw [sub_pow_char_of_commute, one_pow, ← hu, pow_orderOf_eq_one, sub_self]
      exact Commute.one_right u
    -- ... meaning x didn't have order p after all, contradiction
    apply pprime.one_lt.ne
    rw [← hu, h, orderOf_one]

/-- The sum of a nontrivial subgroup of the units of a field is zero. -/
/-
**FiniteField.sum_subgroup_units_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField`
。
形式化陈述：sum_subgroup_units_eq_zero [Ring K] [NoZeroDivisors K] {G : Subgroup Kˣ} [
Fintype G] (hg : G != ⊥) : ∑ x : G, (x.val : K) = 0
参数：hg : G != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Subgroup.ne_bot_iff_exists_ne_one`：ne_bot_iff_exists_ne_one {H : Subgrou
p G} : H != ⊥ ↔ exists a : ↥H, a != 1
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.univ_map_embedding`：Finset.univ_map_embedding {α : Type*} [Fintyp
e α] (e : α ↪ α) : univ.map e = univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_map`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : A
ddCommMonoid M] (s : Finset ι) (e : ι ↪ κ) (f : κ → M),   ∑ x ∈ Finset.map e s, 
f x …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mulLeftEmbedding_apply`：∀ {G : Type u_1} [inst : Mul G] [inst_1 : IsLeft
CancelMul G] (g h : G), (mulLeftEmbedding g) h = g * h
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b

--- 原说明 ---
The sum of a nontrivial subgroup of the units of a field is zero.
-/
theorem sum_subgroup_units_eq_zero [Ring K] [NoZeroDivisors K]
    {G : Subgroup Kˣ} [Fintype G] (hg : G ≠ ⊥) :
    ∑ x : G, (x.val : K) = 0 := by
  rw [Subgroup.ne_bot_iff_exists_ne_one] at hg
  rcases hg with ⟨a, ha⟩
  -- The action of a on G as an embedding
  let a_mul_emb : G ↪ G := mulLeftEmbedding a
  -- ... and leaves G unchanged
  have h_unchanged : Finset.univ.map a_mul_emb = Finset.univ := by simp
  -- Therefore the sum of x over a G is the sum of a x over G
  have h_sum_map := Finset.univ.sum_map a_mul_emb fun x => ((x : Kˣ) : K)
  -- ... and the former is the sum of x over G.
  -- By algebraic manipulation, we have Σ G, x = ∑ G, a x = a ∑ G, x
  simp only [h_unchanged, mulLeftEmbedding_apply, Subgroup.coe_mul, Units.val_mul, ← mul_sum,
    a_mul_emb] at h_sum_map
  -- thus one of (a - 1) or ∑ G, x is zero
  have hzero : (((a : Kˣ) : K) - 1) = 0 ∨ ∑ x : ↥G, ((x : Kˣ) : K) = 0 := by
    rw [← mul_eq_zero, sub_mul, ← h_sum_map, one_mul, sub_self]
  apply Or.resolve_left hzero
  contrapose ha
  ext
  rwa [← sub_eq_zero]

/-- The sum of a subgroup of the units of a field is 1 if the subgroup is trivial and 1 otherwise -/
@[simp]
/-
**FiniteField.sum_subgroup_units** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField`。
形式化陈述：sum_subgroup_units [Ring K] [NoZeroDivisors K] {G : Subgroup Kˣ} [Fintype 
G] [Decidable (G = ⊥)] : ∑ x : G, (x.val : K) = if G = ⊥ then 1 else 0
参数：G = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.default_coe_singleton`：default_coe_singleton (x : α) : (default : ({
x} : Set α)) = ⟨x, rfl⟩
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `FiniteField.sum_subgroup_units_eq_zero`：sum_subgroup_units_eq_zero [Ring
 K] [NoZeroDivisors K] {G : Subgroup Kˣ} [Fintype G] (hg : G != ⊥) : ∑ x : G, (x
.val : K) = 0

--- 原说明 ---
The sum of a subgroup of the units of a field is 1 if the subgroup is trivial an
d 1 otherwise
-/
theorem sum_subgroup_units [Ring K] [NoZeroDivisors K]
    {G : Subgroup Kˣ} [Fintype G] [Decidable (G = ⊥)] :
    ∑ x : G, (x.val : K) = if G = ⊥ then 1 else 0 := by
  by_cases G_bot : G = ⊥
  · subst G_bot
    simp only [univ_unique, sum_singleton, ↓reduceIte, Units.val_eq_one, OneMemClass.coe_eq_one]
    rw [Set.default_coe_singleton]
    rfl
  · simp only [G_bot, ite_false]
    exact sum_subgroup_units_eq_zero G_bot

@[simp]
/-
**FiniteField.sum_subgroup_pow_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField`。
形式化陈述：sum_subgroup_pow_eq_zero [CommRing K] [NoZeroDivisors K] {G : Subgroup Kˣ}
 [Fintype G] {k : Nat} (k_pos : k != 0) (k_lt_card_G : k < Fintype.card G) : ∑ x
 : G, ((x : Kˣ) : K) ^ k = 0
参数：k_pos : k != 0；k_lt_card_G : k < Fintype.card G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `NoZeroDivisors.to_isDomain`：NoZeroDivisors.to_isDomain [Ring α] [h : Non
trivial α] [NoZeroDivisors α] : IsDomain α
· 使用定理 `exists_pow_ne_one_of_isCyclic`：exists_pow_ne_one_of_isCyclic [G_cyclic :
 IsCyclic G] {k : Nat} (k_pos : k != 0) (k_lt_card_G : k < Nat.card G) : exists 
a : G, a ^ k != 1
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Finset.sum_eq_multiset_sum`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddC
ommMonoid M] (s : Finset ι) (f : ι → M),   ∑ x ∈ s, f x = (Multiset.map f s.val)
.sum
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Multiset.map_univ_val_equiv`：map_univ_val_equiv (e : α ≃ β) : map e univ
.val = univ.val
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `Multiset.sum_map_mul_right`：sum_map_mul_right : sum (s.map fun i => f i 
* a) = sum (s.map f) * a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
（共 31 条，此处仅展示前 30 条）
-/
theorem sum_subgroup_pow_eq_zero [CommRing K] [NoZeroDivisors K]
    {G : Subgroup Kˣ} [Fintype G] {k : ℕ} (k_pos : k ≠ 0) (k_lt_card_G : k < Fintype.card G) :
    ∑ x : G, ((x : Kˣ) : K) ^ k = 0 := by
  rw [← Nat.card_eq_fintype_card] at k_lt_card_G
  nontriviality K
  have := NoZeroDivisors.to_isDomain K
  rcases (exists_pow_ne_one_of_isCyclic k_pos k_lt_card_G) with ⟨a, ha⟩
  rw [Finset.sum_eq_multiset_sum]
  have h_multiset_map :
    Finset.univ.val.map (fun x : G => ((x : Kˣ) : K) ^ k) =
      Finset.univ.val.map (fun x : G => ((x : Kˣ) : K) ^ k * ((a : Kˣ) : K) ^ k) := by
    simp_rw [← mul_pow]
    have as_comp :
      (fun x : ↥G => (((x : Kˣ) : K) * ((a : Kˣ) : K)) ^ k)
        = (fun x : ↥G => ((x : Kˣ) : K) ^ k) ∘ fun x : ↥G => x * a := by
      funext x
      simp only [Function.comp_apply, Subgroup.coe_mul, Units.val_mul]
    rw [as_comp, ← Multiset.map_map]
    congr
    rw [eq_comm]
    exact Multiset.map_univ_val_equiv (Equiv.mulRight a)
  have h_multiset_map_sum : (Multiset.map (fun x : G => ((x : Kˣ) : K) ^ k) Finset.univ.val).sum =
    (Multiset.map (fun x : G => ((x : Kˣ) : K) ^ k * ((a : Kˣ) : K) ^ k) Finset.univ.val).sum := by
    rw [h_multiset_map]
  rw [Multiset.sum_map_mul_right] at h_multiset_map_sum
  have hzero : (((a : Kˣ) : K) ^ k - 1 : K)
                  * (Multiset.map (fun i : G => (i.val : K) ^ k) Finset.univ.val).sum = 0 := by
    rw [sub_mul, mul_comm, ← h_multiset_map_sum, one_mul, sub_self]
  rw [mul_eq_zero] at hzero
  refine hzero.resolve_left fun h => ha ?_
  ext
  rw [← sub_eq_zero]
  simp_rw [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one, Units.val_one, h]

section

variable [GroupWithZero K] [Fintype K]

/-
**FiniteField.pow_card_sub_one_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField`。
形式化陈述：pow_card_sub_one_eq_one (a : K) (ha : a != 0) : a ^ (q - 1) = 1
参数：a : K；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Units.val_pow_eq_pow_val`：val_pow_eq_pow_val (n : Nat) : ↑(a ^ n) = (a ^
 n : α)
· 使用定理 `Units.val_mk0`：val_mk0 {a : G₀} (h : a != 0) : (mk0 a h : G₀) = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_units`：Fintype.card_units [GroupWithZero α] [Fintype α] [De
cidableEq α] : Fintype.card αˣ = Fintype.card α - 1
· 使用定理 `pow_card_eq_one`：pow_card_eq_one : x ^ Fintype.card G = 1
-/
theorem pow_card_sub_one_eq_one (a : K) (ha : a ≠ 0) : a ^ (q - 1) = 1 := by
  calc
    a ^ (Fintype.card K - 1) = (Units.mk0 a ha ^ (Fintype.card K - 1) : Kˣ).1 := by
      rw [Units.val_pow_eq_pow_val, Units.val_mk0]
    _ = 1 := by
      classical
        rw [← Fintype.card_units, pow_card_eq_one]
        rfl
/-
**FiniteField.pow_card** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField`。
形式化陈述：pow_card (a : K) : a ^ q = a
参数：a : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Fintype.card_ne_zero`：card_ne_zero [Nonempty α] : card α != 0
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.succ_pred_eq_of_pos`：∀ {n : ℕ}, 0 < n → n.pred.succ = n
· 使用定理 `Fintype.card_pos`：card_pos [h : Nonempty α] : 0 < card α
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Nat.pred_eq_sub_one`：∀ {n : ℕ}, n.pred = n - 1
· 使用定理 `FiniteField.pow_card_sub_one_eq_one`：pow_card_sub_one_eq_one (a : K) (ha
 : a != 0) : a ^ (q - 1) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem pow_card (a : K) : a ^ q = a := by
  by_cases h : a = 0; · rw [h]; apply zero_pow Fintype.card_ne_zero
  rw [← Nat.succ_pred_eq_of_pos Fintype.card_pos, pow_succ, Nat.pred_eq_sub_one,
    pow_card_sub_one_eq_one a h, one_mul]
/-
**FiniteField.pow_card_pow** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField`。
形式化陈述：pow_card_pow (n : Nat) (a : K) : a ^ q ^ n = a
参数：n : Nat；a : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `FiniteField.pow_card`：pow_card (a : K) : a ^ q = a
-/
theorem pow_card_pow (n : ℕ) (a : K) : a ^ q ^ n = a := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, pow_mul, ih, pow_card]

end

section

variable [Field K] [Fintype K]

open Lean in
/-
**FiniteField.instGrindPowIdentity** 是 Mathlib 中的一个实例，位于命名空间 `FiniteField`。
形式化陈述：instGrindPowIdentity : Grind.PowIdentity K (Fintype.card K) where pow_eq
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteField.pow_card`：pow_card (a : K) : a ^ q = a
-/
instance instGrindPowIdentity : Grind.PowIdentity K (Fintype.card K) where
  pow_eq := pow_card

end

variable (K) [Field K] [Fintype K]

/-- The cardinality `q` is a power of the characteristic of `K`. -/
@[stacks 09HY "first part"]
/-
**FiniteField.card** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField`。
形式化陈述：card (p : Nat) [CharP K p] : exists n : Nat+, Nat.Prime p ∧ q = p ^ (n : N
at)
参数：p : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CharP.char_is_prime`：char_is_prime (p : Nat) [CharP R p] : p.Prime
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `VectorSpace.card_fintype`：VectorSpace.card_fintype [Fintype K] [Fintype 
V] : exists n : Nat, card V = card K ^ n
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fintype.card_le_one_iff`：card_le_one_iff : card α <= 1 ↔ forall a b : α,
 a = b
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.card`：card (n : Nat) [Fintype (ZMod n)] : Fintype.card (ZMod n) = n
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p

--- 原说明 ---
The cardinality `q` is a power of the characteristic of `K`.
-/
theorem card (p : ℕ) [CharP K p] : ∃ n : ℕ+, Nat.Prime p ∧ q = p ^ (n : ℕ) := by
  have hp : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  let : Module (ZMod p) K := { (ZMod.castHom dvd_rfl K : ZMod p →+* _).toModule with }
  obtain ⟨n, h⟩ := VectorSpace.card_fintype (ZMod p) K
  rw [ZMod.card] at h
  refine ⟨⟨n, ?_⟩, hp.1, h⟩
  apply Or.resolve_left (Nat.eq_zero_or_pos n)
  rintro rfl
  rw [pow_zero] at h
  have : (0 : K) = 1 := by apply Fintype.card_le_one_iff.mp (le_of_eq h)
  exact absurd this zero_ne_one

-- this statement doesn't use `q` because we want `K` to be an explicit parameter
/-
**FiniteField.card'** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField`。
形式化陈述：card' : exists (p : Nat), CharP K p ∧ exists (n : Nat+), Nat.Prime p ∧ Fin
type.card K = p ^ (n : Nat)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CharP.exists`：∀ (R : Type u_1) [inst : NonAssocSemiring R], ∃ p, CharP R
 p
· 使用定理 `FiniteField.card`：card (p : Nat) [CharP K p] : exists n : Nat+, Nat.Prim
e p ∧ q = p ^ (n : Nat)
-/
theorem card' : ∃ (p : ℕ), CharP K p ∧ ∃ (n : ℕ+), Nat.Prime p ∧ Fintype.card K = p ^ (n : ℕ) :=
  let ⟨p, hc⟩ := CharP.exists K
  ⟨p, hc, @FiniteField.card K _ _ p hc⟩
/-
**FiniteField.isPrimePow_card** 是 Mathlib 中的一个引理，位于命名空间 `FiniteField`。
形式化陈述：isPrimePow_card : IsPrimePow (Fintype.card K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteField.card'`：card' : exists (p : Nat), CharP K p ∧ exists (n : Nat
+), Nat.Prime p ∧ Fintype.card K = p ^ (n : Nat)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.prime_iff`：prime_iff {p : Nat} : p.Prime ↔ _root_.Prime p
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isPrimePow_card : IsPrimePow (Fintype.card K) := by
  obtain ⟨p, _, n, hp, hn⟩ := card' K
  exact ⟨p, n, Nat.prime_iff.mp hp, n.prop, hn.symm⟩
/-
**FiniteField.cast_card_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField`。
形式化陈述：cast_card_eq_zero : (q : K) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.cast_card_eq_zero`：Nat.cast_card_eq_zero (R) [AddGroupWithOne R] [Fi
ntype R] : (Fintype.card R : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cast_card_eq_zero : (q : K) = 0 := by
  simp
/-
**FiniteField.forall_pow_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField`。
形式化陈述：forall_pow_eq_one_iff (i : Nat) : (forall x : Kˣ, x ^ i = 1) ↔ q - 1 ∣ i
参数：i : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCyclic.exists_generator`：IsCyclic.exists_generator [Group α] [IsCyclic
 α] : exists g : α, forall x, x in zpowers g
· 使用定理 `instIsCyclicUnitsOfFinite`：∀ {R : Type u_1} [inst : CommRing R] [IsDomai
n R] [Finite Rˣ], IsCyclic Rˣ
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instFiniteUnits`：∀ {α : Type u_1} [inst : Monoid α] [Finite α], Finite α
ˣ
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Nat.card_units`：Nat.card_units [GroupWithZero α] : Nat.card αˣ = Nat.car
d α - 1
· 使用定理 `orderOf_eq_card_of_forall_mem_zpowers`：orderOf_eq_card_of_forall_mem_zpo
wers {g : α} (hx : forall x, x in zpowers g) : orderOf g = Nat.card α
· 使用定理 `orderOf_dvd_iff_pow_eq_one`：orderOf_dvd_iff_pow_eq_one {n : Nat} : order
Of x ∣ n ↔ x ^ n = 1
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
-/
theorem forall_pow_eq_one_iff (i : ℕ) : (∀ x : Kˣ, x ^ i = 1) ↔ q - 1 ∣ i := by
  obtain ⟨x, hx⟩ := IsCyclic.exists_generator (α := Kˣ)
  rw [← Nat.card_eq_fintype_card, ← Nat.card_units, ← orderOf_eq_card_of_forall_mem_zpowers hx,
    orderOf_dvd_iff_pow_eq_one]
  constructor
  · intro h; apply h
  · intro h y
    simp_rw [← mem_powers_iff_mem_zpowers] at hx
    rcases hx y with ⟨j, rfl⟩
    rw [← pow_mul, mul_comm, pow_mul, h, one_pow]

/-- The sum of `x ^ i` as `x` ranges over the units of a finite field of cardinality `q`
is equal to `0` unless `(q - 1) ∣ i`, in which case the sum is `q - 1`. -/
/-
**FiniteField.sum_pow_units** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField`。
形式化陈述：sum_pow_units [DecidableEq K] (i : Nat) : (∑ x : Kˣ, (x ^ i : K)) = if q -
 1 ∣ i then -1 else 0
参数：i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `sum_hom_units`：sum_hom_units (f : G ->* R) [Decidable (f = 1)] : ∑ g : G
, f g = if f = 1 then Fintype.card G else 0
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FiniteField.forall_pow_eq_one_iff`：forall_pow_eq_one_iff (i : Nat) : (fo
rall x : Kˣ, x ^ i = 1) ↔ q - 1 ∣ i
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Fintype.card_units`：Fintype.card_units [GroupWithZero α] [Fintype α] [De
cidableEq α] : Fintype.card αˣ = Fintype.card α - 1
· 使用定理 `Nat.cast_sub`：cast_sub {m n} (h : m <= n) : ((n - m : Nat) : R) = n - m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fintype.card_pos_iff`：card_pos_iff : 0 < card α ↔ Nonempty α
· 使用定理 `FiniteField.cast_card_eq_zero`：cast_card_eq_zero : (q : K) = 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0

--- 原说明 ---
The sum of `x ^ i` as `x` ranges over the units of a finite field of cardinality
 `q`
is equal to `0` unless `(q - 1) ∣ i`, in which case the sum is `q - 1`.
-/
theorem sum_pow_units [DecidableEq K] (i : ℕ) :
    (∑ x : Kˣ, (x ^ i : K)) = if q - 1 ∣ i then -1 else 0 := by
  let φ : Kˣ →* K :=
    { toFun := fun x => x ^ i
      map_one' := by simp
      map_mul' := by simp [mul_pow] }
  have : Decidable (φ = 1) := by classical infer_instance
  calc (∑ x : Kˣ, φ x) = if φ = 1 then Fintype.card Kˣ else 0 := sum_hom_units φ
      _ = if q - 1 ∣ i then -1 else 0 := by
        suffices q - 1 ∣ i ↔ φ = 1 by
          simp only [this]
          split_ifs; swap
          · exact Nat.cast_zero
          · rw [Fintype.card_units, Nat.cast_sub,
              cast_card_eq_zero, Nat.cast_one, zero_sub]
            show 1 ≤ q; exact Fintype.card_pos_iff.mpr ⟨0⟩
        rw [← forall_pow_eq_one_iff, DFunLike.ext_iff]
        apply forall_congr'; intro x; simp [φ, Units.ext_iff]

/-- The sum of `x ^ i` as `x` ranges over a finite field of cardinality `q`
is equal to `0` if `i < q - 1`. -/
/-
**FiniteField.sum_pow_lt_card_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField`。
形式化陈述：sum_pow_lt_card_sub_one (i : Nat) (h : i < q - 1) : ∑ x : K, x ^ i = 0
参数：i : Nat；h : i < q - 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `nsmul_one`：∀ {A : Type u_2} [inst : AddMonoidWithOne A] (n : ℕ), n • 1 =
 ↑n
· 使用定理 `FiniteField.cast_card_eq_zero`：cast_card_eq_zero : (q : K) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Units.val_injective`：∀ {α : Type u} [inst : Monoid α], Function.Injectiv
e Units.val
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `isUnit_iff_ne_zero`：isUnit_iff_ne_zero : IsUnit a ↔ a != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_sdiff`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   s₁ ⊆ s₂ → ∑ x ∈ s₂
 \ s₁,…
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Finset.sum_map`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : A
ddCommMonoid M] (s : Finset ι) (e : ι ↪ κ) (f : κ → M),   ∑ x ∈ Finset.map e s, 
f x …
· 使用定理 `FiniteField.sum_pow_units`：sum_pow_units [DecidableEq K] (i : Nat) : (∑ 
x : Kˣ, (x ^ i : K)) = if q - 1 ∣ i then -1 else 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e

--- 原说明 ---
The sum of `x ^ i` as `x` ranges over a finite field of cardinality `q`
is equal to `0` if `i < q - 1`.
-/
theorem sum_pow_lt_card_sub_one (i : ℕ) (h : i < q - 1) : ∑ x : K, x ^ i = 0 := by
  by_cases hi : i = 0
  · simp only [hi, nsmul_one, sum_const, pow_zero, card_univ, cast_card_eq_zero]
  classical
    have hiq : ¬q - 1 ∣ i := by contrapose! h; exact Nat.le_of_dvd (Nat.pos_of_ne_zero hi) h
    let φ : Kˣ ↪ K := ⟨fun x ↦ x, Units.val_injective⟩
    have : univ.map φ = univ \ {0} := by
      ext x
      simpa only [mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and, mem_sdiff,
        mem_singleton, φ] using! isUnit_iff_ne_zero
    calc
      ∑ x : K, x ^ i = ∑ x ∈ univ \ {(0 : K)}, x ^ i := by
        rw [← sum_sdiff ({0} : Finset K).subset_univ, sum_singleton, zero_pow hi, add_zero]
      _ = ∑ x : Kˣ, (x ^ i : K) := by simp [φ, ← this, univ.sum_map φ]
      _ = 0 := by rw [sum_pow_units K i, if_neg]; exact hiq

section frobenius

variable (R) [CommRing R] [Algebra K R]

/-- If `R` is an algebra over a finite field `K`, the Frobenius `K`-algebra endomorphism of `R` is
  given by raising every element of `R` to its `#K`-th power. -/
/-
**FiniteField.frobeniusAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `FiniteField`。
形式化陈述：(K : Type u_1) →   (R : Type u_2) → [inst : Field K] → [Fintype K] → [inst
_2 : CommRing R] → [inst_3 : Algebra K R] → R →ₐ[K] R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `R` is an algebra over a finite field `K`, the Frobenius `K`-algebra endomorp
hism of `R` is
  given by raising every element of `R` to its `#K`-th power.
-/
@[simps!] def frobeniusAlgHom : R →ₐ[K] R where
  __ := powMonoidHom q
  map_zero' := zero_pow Fintype.card_pos.ne'
  map_add' _ _ := by
    obtain ⟨p, _, _, hp, card_eq⟩ := card' K
    nontriviality R
    have : CharP R p := charP_of_injective_algebraMap' K p
    have : ExpChar R p := .prime hp
    simp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, powMonoidHom_apply, card_eq]
    exact add_pow_expChar_pow ..
  commutes' _ := by simp [← map_pow, pow_card]
/-
**FiniteField.coe_frobeniusAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField`。
形式化陈述：coe_frobeniusAlgHom : ⇑(frobeniusAlgHom K R) = (· ^ q)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_frobeniusAlgHom : ⇑(frobeniusAlgHom K R) = (· ^ q) := rfl

/-- If `R` is a perfect ring and an algebra over a finite field `K`, the Frobenius `K`-algebra
  endomorphism of `R` is an automorphism. -/
/-
**FiniteField.frobeniusAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `FiniteField`。
形式化陈述：(K : Type u_1) →   (R : Type u_2) →     [inst : Field K] →       [Fintype 
K] →         [inst_2 : CommRing R] → [inst_3 : Algebra K R] → (p : ℕ) → [ExpChar
 R p] → [PerfectRing R p] → R ≃ₐ[K] R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `R` is a perfect ring and an algebra over a finite field `K`, the Frobenius `
K`-algebra
  endomorphism of `R` is an automorphism.
-/
@[simps!] noncomputable def frobeniusAlgEquiv (p : ℕ) [ExpChar R p] [PerfectRing R p] : R ≃ₐ[K] R :=
  .ofBijective (frobeniusAlgHom K R) <| by
    obtain ⟨p', _, n, hp, card_eq⟩ := card' K
    rw [coe_frobeniusAlgHom, card_eq]
    have : ExpChar K p' := ExpChar.prime hp
    nontriviality R
    have := ExpChar.eq ‹_› (expChar_of_injective_algebraMap (algebraMap K R).injective p')
    subst this
    apply bijective_iterateFrobenius

variable (L : Type*) [Field L] [Algebra K L]

/-- If `L/K` is an algebraic extension of a finite field, the Frobenius `K`-algebra endomorphism
  of `L` is an automorphism. -/
/-
**FiniteField.frobeniusAlgEquivOfAlgebraic** 是 Mathlib 中的一个定义，位于命名空间 `FiniteFiel
d`。
形式化陈述：(K : Type u_1) →   [inst : Field K] →     [Fintype K] → (L : Type u_3) → [
inst_2 : Field L] → [inst_3 : Algebra K L] → [Algebra.IsAlgebraic K L] → Gal(L/K
)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `L/K` is an algebraic extension of a finite field, the Frobenius `K`-algebra 
endomorphism
  of `L` is an automorphism.
-/
@[simps!] noncomputable def frobeniusAlgEquivOfAlgebraic [Algebra.IsAlgebraic K L] : Gal(L/K) :=
  (Algebra.IsAlgebraic.algEquivEquivAlgHom K L).symm (frobeniusAlgHom K L)
/-
**FiniteField.coe_frobeniusAlgEquivOfAlgebraic** 是 Mathlib 中的一个定理，位于命名空间 `Finite
Field`。
形式化陈述：coe_frobeniusAlgEquivOfAlgebraic [Algebra.IsAlgebraic K L] : ⇑(frobeniusAl
gEquivOfAlgebraic K L) = (· ^ q)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_frobeniusAlgEquivOfAlgebraic [Algebra.IsAlgebraic K L] :
    ⇑(frobeniusAlgEquivOfAlgebraic K L) = (· ^ q) := rfl
/-
**FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate** 是 Mathlib 中的一个引理，位于命名空间
 `FiniteField`。
形式化陈述：coe_frobeniusAlgEquivOfAlgebraic_iterate [Algebra.IsAlgebraic K L] (n : Na
t) : (⇑(frobeniusAlgEquivOfAlgebraic K L))^[n] = (· ^ (Fintype.card K ^ n))
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_iterate`：∀ {M : Type u_4} [inst : Monoid M] (k n : ℕ), (fun x => x ^
 k)^[n] = fun x => x ^ k ^ n
-/
lemma coe_frobeniusAlgEquivOfAlgebraic_iterate [Algebra.IsAlgebraic K L] (n : ℕ) :
    (⇑(frobeniusAlgEquivOfAlgebraic K L))^[n] = (· ^ (Fintype.card K ^ n)) :=
  pow_iterate (Fintype.card K) n

variable [Finite L]

open Polynomial in
/-
**FiniteField.orderOf_frobeniusAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField`。
形式化陈述：orderOf_frobeniusAlgHom : orderOf (frobeniusAlgHom K L) = Module.finrank K
 L
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `orderOf_eq_iff`：orderOf_eq_iff {n} (h : 0 < n) : orderOf x = n ↔ x ^ n =
 1 ∧ forall m, m < n -> 0 < m -> x ^ m != 1
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `isNoetherian_of_finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semiring
 R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] [Finite M],   IsNoet
herian R M
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `AlgHom.coe_pow`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [ins
t_1 : Semiring A] [inst_2 : Algebra R A] (φ : A →ₐ[R] A)   (n : ℕ), ⇑(φ ^ n) = (
⇑φ)^…
· 使用定理 `pow_iterate`：∀ {M : Type u_4} [inst : Monoid M] (k n : ℕ), (fun x => x ^
 k)^[n] = fun x => x ^ k ^ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FiniteField.pow_card`：pow_card (a : K) : a ^ q = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.card_le_degree_of_subset_roots`：card_le_degree_of_subset_root
s {p : R[X]} {Z : Finset R} (h : Z.val subseteq p.roots) : #Z <= p.natDegree
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_pow`：eval_pow (n : Nat) : (p ^ n).eval x = p.eval x ^ n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Polynomial.coeff_sub`：coeff_sub (p q : R[X]) (n : Nat) : coeff (p - q) n
 = coeff p n - coeff q n
· 使用定理 `Polynomial.coeff_X_pow`：coeff_X_pow (k n : Nat) : coeff (X ^ k : R[X]) n
 = if n = k then 1 else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
（共 59 条，此处仅展示前 30 条）
-/
theorem orderOf_frobeniusAlgHom : orderOf (frobeniusAlgHom K L) = Module.finrank K L :=
  (orderOf_eq_iff Module.finrank_pos).mpr <| by
    have := Fintype.ofFinite L
    refine ⟨DFunLike.ext _ _ fun x ↦ ?_, fun m lt pos eq ↦ ?_⟩
    · simp_rw [AlgHom.coe_pow, coe_frobeniusAlgHom, pow_iterate, AlgHom.one_apply,
        ← Module.card_eq_pow_finrank, pow_card]
    have := card_le_degree_of_subset_roots (R := L) (p := X ^ q ^ m - X) (Z := univ) fun x _ ↦ by
      simp_rw [mem_roots', IsRoot, eval_sub, eval_pow, eval_X]
      have := DFunLike.congr_fun eq x
      rw [AlgHom.coe_pow, coe_frobeniusAlgHom, pow_iterate, AlgHom.one_apply, ← sub_eq_zero] at this
      refine ⟨fun h ↦ ?_, this⟩
      simpa [Fintype.one_lt_card.ne, pos.ne, eqComm] using congr_arg (coeff · 1) h
    refine this.not_gt (((natDegree_sub_le ..).trans_eq ?_).trans_lt <|
      (Nat.pow_lt_pow_right Fintype.one_lt_card lt).trans_eq Module.card_eq_pow_finrank.symm)
    simp [Nat.one_le_pow _ _ Fintype.card_pos]
/-
**FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic** 是 Mathlib 中的一个定理，位于命名空间 `Fi
niteField`。
形式化陈述：orderOf_frobeniusAlgEquivOfAlgebraic : orderOf (frobeniusAlgEquivOfAlgebra
ic K L) = Module.finrank K L
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `isNoetherian_of_finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semiring
 R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] [Finite M],   IsNoet
herian R M
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `orderOf_eq_iff`：orderOf_eq_iff {n} (h : 0 < n) : orderOf x = n ↔ x ^ n =
 1 ∧ forall m, m < n -> 0 < m -> x ^ m != 1
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `AlgEquiv.coe_pow`：∀ {R : Type uR} {A₁ : Type uA₁} [inst : CommSemiring R
] [inst_1 : Semiring A₁] [inst_2 : Algebra R A₁] (e : A₁ ≃ₐ[R] A₁)   (n : ℕ), ⇑(
e ^ n)…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `AlgHom.coe_pow`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [ins
t_1 : Semiring A] [inst_2 : Algebra R A] (φ : A →ₐ[R] A)   (n : ℕ), ⇑(φ ^ n) = (
⇑φ)^…
· 使用定理 `FiniteField.orderOf_frobeniusAlgHom`：orderOf_frobeniusAlgHom : orderOf (
frobeniusAlgHom K L) = Module.finrank K L
-/
theorem orderOf_frobeniusAlgEquivOfAlgebraic :
    orderOf (frobeniusAlgEquivOfAlgebraic K L) = Module.finrank K L := by
  simpa [orderOf_eq_iff Module.finrank_pos, DFunLike.ext_iff] using! orderOf_frobeniusAlgHom K L
/-
**FiniteField.bijective_frobeniusAlgHom_pow** 是 Mathlib 中的一个定理，位于命名空间 `FiniteFie
ld`。
形式化陈述：bijective_frobeniusAlgHom_pow : Function.Bijective fun n : Fin (Module.fin
rank K L) => frobeniusAlgHom K L ^ n.1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `FiniteField.orderOf_frobeniusAlgHom`：orderOf_frobeniusAlgHom : orderOf (
frobeniusAlgHom K L) = Module.finrank K L
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `orderOf_pos_iff`：orderOf_pos_iff : 0 < orderOf x ↔ IsOfFinOrder x
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `isNoetherian_of_finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semiring
 R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] [Finite M],   IsNoet
herian R M
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.bijective_of_nat_card_le`：∀ {α : Type u_1} {β : Type 
u_2} [Finite β] {f : α → β},   Function.Injective f → Nat.card β ≤ Nat.card α → 
Function.Bijective f
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `card_algHom_le_finrank`：card_algHom_le_finrank : Nat.card (M ->ₐ[K] L) <
= finrank K M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem bijective_frobeniusAlgHom_pow :
    Function.Bijective fun n : Fin (Module.finrank K L) ↦ frobeniusAlgHom K L ^ n.1 :=
  let e := (finCongr <| orderOf_frobeniusAlgHom K L).symm.trans <|
    finEquivPowers (orderOf_pos_iff.mp <| orderOf_frobeniusAlgHom K L ▸ Module.finrank_pos)
  (Subtype.val_injective.comp e.injective).bijective_of_nat_card_le
    ((card_algHom_le_finrank K L L).trans_eq <| by simp)
/-
**FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow** 是 Mathlib 中的一个定理，位于命名
空间 `FiniteField`。
形式化陈述：bijective_frobeniusAlgEquivOfAlgebraic_pow : Function.Bijective fun n : Fi
n (Module.finrank K L) => frobeniusAlgEquivOfAlgebraic K L ^ n.1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `isNoetherian_of_finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semiring
 R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] [Finite M],   IsNoet
herian R M
· 使用定理 `Function.Bijective.of_comp_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Bijective f → ∀ (g : γ → α), Function.Bijective 
(f ∘ g) ↔ Function.Bi…
· 使用定理 `MulEquiv.bijective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [inst
_1 : Mul N] (e : M ≃* N), Function.Bijective ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `FiniteField.bijective_frobeniusAlgHom_pow`：bijective_frobeniusAlgHom_pow
 : Function.Bijective fun n : Fin (Module.finrank K L) => frobeniusAlgHom K L ^ 
n.1
-/
theorem bijective_frobeniusAlgEquivOfAlgebraic_pow :
    Function.Bijective fun n : Fin (Module.finrank K L) ↦ frobeniusAlgEquivOfAlgebraic K L ^ n.1 :=
  ((Algebra.IsAlgebraic.algEquivEquivAlgHom K L).bijective.of_comp_iff' _).mp <| by
    simpa only [Function.comp_def, map_pow] using! bijective_frobeniusAlgHom_pow K L
/-
**FiniteField.** 是 Mathlib 中的一个实例，位于命名空间 `FiniteField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (K L) [Finite L] [Field K] [Field L] [Algebra K L] : IsCyclic Gal(L/K) where
  exists_zpow_surjective :=
    have := Finite.of_injective _ (algebraMap K L).injective
    have := Fintype.ofFinite K
    ⟨frobeniusAlgEquivOfAlgebraic K L,
      fun f ↦ have ⟨n, hn⟩ := (bijective_frobeniusAlgEquivOfAlgebraic_pow K L).2 f; ⟨n, hn⟩⟩

open Polynomial in
/-
**FiniteField.minpoly_frobeniusAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField`。
形式化陈述：minpoly_frobeniusAlgHom : minpoly K (frobeniusAlgHom K L).toLinearMap = X 
^ Module.finrank K L - 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minpoly.eq_of_linearIndependent`：eq_of_linearIndependent {p : A[X]} (mon
ic : p.Monic) (hp0 : p.aeval x = 0) (n : Nat) (hpn : p.degree = n) (ind : Linear
Independent A fun i :…
· 使用定理 `Polynomial.leadingCoeff_X_pow_sub_one`：leadingCoeff_X_pow_sub_one {n : N
at} (hn : 0 < n) : (X ^ n - 1 : R[X]).leadingCoeff = 1
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `isNoetherian_of_finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semiring
 R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] [Finite M],   IsNoet
herian R M
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_sub`：aeval_sub {p q : R[X]} [Ring A] [Algebra R A] (x :
 A) : aeval x (p - q) = aeval x p - aeval x q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.End.coe_pow`：coe_pow (f : End R M) (n : Nat) : ⇑(f ^ n) = f^[n]
· 使用定理 `FiniteField.orderOf_frobeniusAlgHom`：orderOf_frobeniusAlgHom : orderOf (
frobeniusAlgHom K L) = Module.finrank K L
· 使用定理 `AlgHom.coe_pow`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [ins
t_1 : Semiring A] [inst_2 : Algebra R A] (φ : A →ₐ[R] A)   (n : ℕ), ⇑(φ ^ n) = (
⇑φ)^…
· 使用定理 `pow_orderOf_eq_one`：pow_orderOf_eq_one (x : G) : x ^ orderOf x = 1
· 使用定理 `Polynomial.degree_X_pow_sub_C`：degree_X_pow_sub_C {n : Nat} (hn : 0 < n)
 (a : R) : degree ((X : R[X]) ^ n - C a) = n
（共 41 条，此处仅展示前 30 条）
-/
theorem minpoly_frobeniusAlgHom :
    minpoly K (frobeniusAlgHom K L).toLinearMap = X ^ Module.finrank K L - 1 :=
  minpoly.eq_of_linearIndependent _ _ (leadingCoeff_X_pow_sub_one Module.finrank_pos)
    (LinearMap.ext fun x ↦ by
      simpa [sub_eq_zero, Module.End.coe_pow, orderOf_frobeniusAlgHom] using!
        congr($(pow_orderOf_eq_one (frobeniusAlgHom K L)) x)) _
    (degree_X_pow_sub_C Module.finrank_pos _) <| by
      simpa [← AlgHom.toEnd_apply, ← map_pow] using! (linearIndependent_algHom_toLinearMap K L L
        |>.restrict_scalars' K).comp _ (bijective_frobeniusAlgHom_pow K L).1

end frobenius

open Polynomial

section

variable [Fintype K] (K' : Type*) [Field K'] {p n : ℕ}

/-
**FiniteField.X_pow_card_sub_X_natDegree_eq** 是 Mathlib 中的一个定理，位于命名空间 `FiniteFie
ld`。
形式化陈述：X_pow_card_sub_X_natDegree_eq (hp : 1 < p) : (X ^ p - X : K'[X]).natDegree
 = p
参数：hp : 1 < p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_X_pow`：degree_X_pow : degree ((X : R[X]) ^ n) = n
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Polynomial.degree_X`：degree_X : degree (X : R[X]) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq`：natDegree_eq_of_degree_eq [Semirin
g S] {q : S[X]} (h : degree p = degree q) : natDegree p = natDegree q
· 使用定理 `Polynomial.degree_sub_eq_left_of_degree_lt`：degree_sub_eq_left_of_degree
_lt (h : degree q < degree p) : degree (p - q) = degree p
· 使用定理 `Polynomial.natDegree_X_pow`：natDegree_X_pow : natDegree ((X : R[X]) ^ n)
 = n
-/
theorem X_pow_card_sub_X_natDegree_eq (hp : 1 < p) : (X ^ p - X : K'[X]).natDegree = p := by
  have h1 : (X : K'[X]).degree < (X ^ p : K'[X]).degree := by
    rw [degree_X_pow, degree_X]
    exact mod_cast hp
  rw [natDegree_eq_of_degree_eq (degree_sub_eq_left_of_degree_lt h1), natDegree_X_pow]
/-
**FiniteField.X_pow_card_pow_sub_X_natDegree_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finit
eField`。
形式化陈述：X_pow_card_pow_sub_X_natDegree_eq (hn : n != 0) (hp : 1 < p) : (X ^ p ^ n 
- X : K'[X]).natDegree = p ^ n
参数：hn : n != 0；hp : 1 < p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteField.X_pow_card_sub_X_natDegree_eq`：X_pow_card_sub_X_natDegree_eq
 (hp : 1 < p) : (X ^ p - X : K'[X]).natDegree = p
· 使用定理 `Nat.one_lt_pow`：∀ {n a : ℕ}, n ≠ 0 → 1 < a → 1 < a ^ n
-/
theorem X_pow_card_pow_sub_X_natDegree_eq (hn : n ≠ 0) (hp : 1 < p) :
    (X ^ p ^ n - X : K'[X]).natDegree = p ^ n :=
  X_pow_card_sub_X_natDegree_eq K' <| Nat.one_lt_pow hn hp
/-
**FiniteField.X_pow_card_sub_X_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField`。
形式化陈述：X_pow_card_sub_X_ne_zero (hp : 1 < p) : (X ^ p - X : K'[X]) != 0
参数：hp : 1 < p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ne_zero_of_natDegree_gt`：ne_zero_of_natDegree_gt {n : Nat} (h
 : n < natDegree p) : p != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FiniteField.X_pow_card_sub_X_natDegree_eq`：X_pow_card_sub_X_natDegree_eq
 (hp : 1 < p) : (X ^ p - X : K'[X]).natDegree = p
-/
theorem X_pow_card_sub_X_ne_zero (hp : 1 < p) : (X ^ p - X : K'[X]) ≠ 0 :=
  ne_zero_of_natDegree_gt <|
    calc
      1 < _ := hp
      _ = _ := (X_pow_card_sub_X_natDegree_eq K' hp).symm
/-
**FiniteField.X_pow_card_pow_sub_X_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `FiniteFiel
d`。
形式化陈述：X_pow_card_pow_sub_X_ne_zero (hn : n != 0) (hp : 1 < p) : (X ^ p ^ n - X :
 K'[X]) != 0
参数：hn : n != 0；hp : 1 < p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteField.X_pow_card_sub_X_ne_zero`：X_pow_card_sub_X_ne_zero (hp : 1 <
 p) : (X ^ p - X : K'[X]) != 0
· 使用定理 `Nat.one_lt_pow`：∀ {n a : ℕ}, n ≠ 0 → 1 < a → 1 < a ^ n
-/
theorem X_pow_card_pow_sub_X_ne_zero (hn : n ≠ 0) (hp : 1 < p) : (X ^ p ^ n - X : K'[X]) ≠ 0 :=
  X_pow_card_sub_X_ne_zero K' <| Nat.one_lt_pow hn hp

end

/-
**FiniteField.roots_X_pow_card_sub_X** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField`。
形式化陈述：roots_X_pow_card_sub_X : roots (X ^ q - X : K[X]) = Finset.univ.val
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteField.X_pow_card_sub_X_ne_zero`：X_pow_card_sub_X_ne_zero (hp : 1 <
 p) : (X ^ p - X : K'[X]) != 0
· 使用定理 `Fintype.one_lt_card`：one_lt_card [h : Nontrivial α] : 1 < Fintype.card α
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.eq_univ_iff_forall`：eq_univ_iff_forall : s = univ ↔ forall x, x i
n s
· 使用定理 `Multiset.mem_toFinset`：mem_toFinset {a : α} {s : Multiset α} : a in s.to
Finset ↔ a in s
· 使用定理 `Polynomial.mem_roots`：mem_roots (hp : p != 0) : a in p.roots ↔ IsRoot p 
a
· 使用定理 `Polynomial.IsRoot.def`：∀ {R : Type u} {a : R} [inst : Semiring R] {p : P
olynomial R}, p.IsRoot a ↔ Polynomial.eval a p = 0
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_pow`：eval_pow (n : Nat) : (p ^ n).eval x = p.eval x ^ n
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `FiniteField.pow_card`：pow_card (a : K) : a ^ q = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.toFinset_val`：toFinset_val (s : Multiset α) : s.toFinset.1 = s.
dedup
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Multiset.dedup_eq_self`：dedup_eq_self {s : Multiset α} : dedup s = s ↔ N
odup s
· 使用定理 `Polynomial.nodup_roots`：nodup_roots {p : R[X]} (hsep : Separable p) : p.
roots.Nodup
· 使用定理 `Polynomial.separable_def`：separable_def (f : R[X]) : f.Separable ↔ IsCop
rime f (derivative f)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Polynomial.derivative_sub`：derivative_sub {f g : R[X]} : derivative (f -
 g) = derivative f - derivative g
· 使用定理 `Polynomial.derivative_X`：derivative_X : derivative (X : R[X]) = 1
· 使用定理 `Polynomial.derivative_X_pow`：derivative_X_pow (n : Nat) : derivative (X 
^ n : R[X]) = C (n : R) * X ^ (n - 1)
· 使用引理 `Nat.cast_card_eq_zero`：Nat.cast_card_eq_zero (R) [AddGroupWithOne R] [Fi
ntype R] : (Fintype.card R : R) = 0
· 使用定理 `Polynomial.C_0`：C_0 : C (0 : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `IsCoprime.neg_right`：neg_right {x y : R} (h : IsCoprime x y) : IsCoprime
 x (-y)
（共 31 条，此处仅展示前 30 条）
-/
theorem roots_X_pow_card_sub_X : roots (X ^ q - X : K[X]) = Finset.univ.val := by
  classical
    have aux : (X ^ q - X : K[X]) ≠ 0 := X_pow_card_sub_X_ne_zero K Fintype.one_lt_card
    have : (roots (X ^ q - X : K[X])).toFinset = Finset.univ := by
      rw [eq_univ_iff_forall]
      intro x
      rw [Multiset.mem_toFinset, mem_roots aux, IsRoot.def, eval_sub, eval_pow, eval_X,
        sub_eq_zero, pow_card]
    rw [← this, Multiset.toFinset_val, eq_comm, Multiset.dedup_eq_self]
    apply nodup_roots
    rw [separable_def]
    convert! isCoprime_one_right.neg_right (R := K[X]) using 1
    rw [derivative_sub, derivative_X, derivative_X_pow, Nat.cast_card_eq_zero K, C_0,
      zero_mul, zero_sub]

variable {K}
/-
**FiniteField.frobenius_pow** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField`。
形式化陈述：frobenius_pow {p : Nat} [Fact p.Prime] [CharP K p] {n : Nat} (hcard : q = 
p ^ n) : frobenius K p ^ n = 1
参数：hcard : q = p ^ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RingHom.one_def`：one_def : (1 : α ->+* α) = id α
· 使用定理 `RingHom.id_apply`：id_apply (x : α) : RingHom.id α x = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FiniteField.pow_card`：pow_card (a : K) : a ^ q = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用引理 `RingHom.mul_def`：mul_def (f g : α ->+* α) : f * g = f.comp g
· 使用定理 `RingHom.comp_apply`：comp_apply (hnp : β ->+* γ) (hmn : α ->+* β) (x : α)
 : (hnp.comp hmn : α -> γ) x = hnp (hmn x)
· 使用引理 `frobenius_def`：frobenius_def : frobenius R p x = x ^ p
-/
theorem frobenius_pow {p : ℕ} [Fact p.Prime] [CharP K p] {n : ℕ} (hcard : q = p ^ n) :
    frobenius K p ^ n = 1 := by
  ext x; conv_rhs => rw [RingHom.one_def, RingHom.id_apply, ← pow_card x, hcard]
  clear hcard
  induction n with
  | zero => simp
  | succ n hn =>
    rw [pow_succ', pow_succ, pow_mul, RingHom.mul_def, RingHom.comp_apply, frobenius_def, hn]

open Polynomial
/-
**FiniteField.expand_card** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField`。
形式化陈述：expand_card (f : K[X]) : expand K q f = f ^ q
参数：f : K[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CharP.exists`：∀ (R : Type u_1) [inst : NonAssocSemiring R], ∃ p, CharP R
 p
· 使用定理 `FiniteField.card`：card (p : Nat) [CharP K p] : exists n : Nat+, Nat.Prim
e p ∧ q = p ^ (n : Nat)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.map_iterateFrobenius_expand`：map_iterateFrobenius_expand (f :
 R[X]) (n : Nat) : map (iterateFrobenius R p n) (expand R (p ^ n) f) = f ^ p ^ n
· 使用引理 `iterateFrobenius_eq_pow`：iterateFrobenius_eq_pow : iterateFrobenius R p 
n = frobenius R p ^ n
· 使用定理 `FiniteField.frobenius_pow`：frobenius_pow {p : Nat} [Fact p.Prime] [CharP
 K p] {n : Nat} (hcard : q = p ^ n) : frobenius K p ^ n = 1
· 使用引理 `RingHom.one_def`：one_def : (1 : α ->+* α) = id α
· 使用定理 `Polynomial.map_id`：map_id : p.map (RingHom.id _) = p
-/
theorem expand_card (f : K[X]) : expand K q f = f ^ q := by
  obtain ⟨p, hp⟩ := CharP.exists K
  rcases FiniteField.card K p with ⟨⟨n, npos⟩, ⟨hp, hn⟩⟩
  have : Fact p.Prime := ⟨hp⟩
  dsimp at hn
  rw [hn, ← map_iterateFrobenius_expand, iterateFrobenius_eq_pow,
    frobenius_pow hn, RingHom.one_def, map_id]

end FiniteField

namespace ZMod

open FiniteField Polynomial

set_option backward.isDefEq.respectTransparency false in
/-
**ZMod.sq_add_sq** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：sq_add_sq (p : Nat) [hp : Fact p.Prime] (x : ZMod p) : exists a b : ZMod p
, a ^ 2 + b ^ 2 = x
参数：p : Nat；x : ZMod p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Prime.eq_two_or_odd`：∀ {p : ℕ}, Nat.Prime p → p = 2 ∨ p % 2 = 1
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `ZMod.instIsDomain`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], IsDomain (ZMod p
)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FiniteField.exists_root_sum_quadratic`：exists_root_sum_quadratic [Fintyp
e R] {f g : R[X]} (hf2 : degree f = 2) (hg2 : degree g = 2) (hR : Fintype.card R
 % 2 = 1) : exists a b, f.e…
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `Polynomial.degree_X_pow`：degree_X_pow : degree ((X : R[X]) ^ n) = n
（共 38 条，此处仅展示前 30 条）
-/
theorem sq_add_sq (p : ℕ) [hp : Fact p.Prime] (x : ZMod p) : ∃ a b : ZMod p, a ^ 2 + b ^ 2 = x := by
  rcases hp.1.eq_two_or_odd with rfl | hp_odd
  · change Fin 2 at x
    fin_cases x
    · use 0; simp
    · use 0, 1; simp
  let f : (ZMod p)[X] := X ^ 2
  let g : (ZMod p)[X] := X ^ 2 - C x
  obtain ⟨a, b, hab⟩ : ∃ a b, f.eval a + g.eval b = 0 :=
    @exists_root_sum_quadratic _ _ _ _ f g (degree_X_pow 2) (degree_X_pow_sub_C (by decide) _)
      (by rw [ZMod.card, hp_odd])
  refine ⟨a, b, ?_⟩
  rw [← sub_eq_zero]
  simpa only [f, g, eval_C, eval_X, eval_pow, eval_sub, ← add_sub_assoc] using hab

end ZMod

/-- If `p` is a prime natural number and `x` is an integer number, then there exist natural numbers
`a ≤ p / 2` and `b ≤ p / 2` such that `a ^ 2 + b ^ 2 ≡ x [ZMOD p]`. This is a version of
`ZMod.sq_add_sq` with estimates on `a` and `b`. -/
/-
**Nat.sq_add_sq_zmodEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.sq_add_sq_zmodEq (p : Nat) [Fact p.Prime] (x : Int) : exists a b : Nat
, a <= p / 2 ∧ b <= p / 2 ∧ (a : Int) ^ 2 + (b : Int) ^ 2 ≡ x [ZMOD p]
参数：p : Nat；x : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZMod.sq_add_sq`：sq_add_sq (p : Nat) [hp : Fact p.Prime] (x : ZMod p) : e
xists a b : ZMod p, a ^ 2 + b ^ 2 = x
· 使用引理 `ZMod.natAbs_valMinAbs_le`：natAbs_valMinAbs_le [NeZero n] (x : ZMod n) : 
x.valMinAbs.natAbs <= n / 2
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.natCast_natAbs`：∀ (n : ℤ), ↑n.natAbs = |n|
· 使用定理 `sq_abs`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] (a : α
), |a| ^ 2 = a ^ 2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.intCast_eq_intCast_iff`：intCast_eq_intCast_iff (a b : Int) (c : Nat
) : (a : ZMod c) = (b : ZMod c) ↔ a ≡ b [ZMOD c]
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `Int.cast_pow`：∀ {R : Type u_1} [inst : Ring R] (n : ℤ) (m : ℕ), ↑(n ^ m)
 = ↑n ^ m
· 使用定理 `ZMod.coe_valMinAbs`：∀ {n : ℕ} (x : ZMod n), ↑x.valMinAbs = x

--- 原说明 ---
If `p` is a prime natural number and `x` is an integer number, then there exist 
natural numbers
`a ≤ p / 2` and `b ≤ p / 2` such that `a ^ 2 + b ^ 2 ≡ x [ZMOD p]`. This is a ve
rsion of
`ZMod.sq_add_sq` with estimates on `a` and `b`.
-/
theorem Nat.sq_add_sq_zmodEq (p : ℕ) [Fact p.Prime] (x : ℤ) :
    ∃ a b : ℕ, a ≤ p / 2 ∧ b ≤ p / 2 ∧ (a : ℤ) ^ 2 + (b : ℤ) ^ 2 ≡ x [ZMOD p] := by
  rcases ZMod.sq_add_sq p x with ⟨a, b, hx⟩
  refine ⟨a.valMinAbs.natAbs, b.valMinAbs.natAbs, ZMod.natAbs_valMinAbs_le _,
    ZMod.natAbs_valMinAbs_le _, ?_⟩
  rw [← a.coe_valMinAbs, ← b.coe_valMinAbs] at hx
  push_cast
  rw [sq_abs, sq_abs, ← ZMod.intCast_eq_intCast_iff]
  exact mod_cast hx

/-- If `p` is a prime natural number and `x` is a natural number, then there exist natural numbers
`a ≤ p / 2` and `b ≤ p / 2` such that `a ^ 2 + b ^ 2 ≡ x [MOD p]`. This is a version of
`ZMod.sq_add_sq` with estimates on `a` and `b`. -/
/-
**Nat.sq_add_sq_modEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.sq_add_sq_modEq (p : Nat) [Fact p.Prime] (x : Nat) : exists a b : Nat,
 a <= p / 2 ∧ b <= p / 2 ∧ a ^ 2 + b ^ 2 ≡ x [MOD p]
参数：p : Nat；x : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.sq_add_sq_zmodEq`：Nat.sq_add_sq_zmodEq (p : Nat) [Fact p.Prime] (x :
 Int) : exists a b : Nat, a <= p / 2 ∧ b <= p / 2 ∧ (a : Int) ^ 2 + (b : Int) ^ 
2 ≡ x [ZMO…

--- 原说明 ---
If `p` is a prime natural number and `x` is a natural number, then there exist n
atural numbers
`a ≤ p / 2` and `b ≤ p / 2` such that `a ^ 2 + b ^ 2 ≡ x [MOD p]`. This is a ver
sion of
`ZMod.sq_add_sq` with estimates on `a` and `b`.
-/
theorem Nat.sq_add_sq_modEq (p : ℕ) [Fact p.Prime] (x : ℕ) :
    ∃ a b : ℕ, a ≤ p / 2 ∧ b ≤ p / 2 ∧ a ^ 2 + b ^ 2 ≡ x [MOD p] := by
  simpa only [← Int.natCast_modEq_iff] using! Nat.sq_add_sq_zmodEq p x

namespace CharP

/-
**CharP.sq_add_sq** 是 Mathlib 中的一个定理，位于命名空间 `CharP`。
形式化陈述：sq_add_sq (R : Type*) [Ring R] [IsDomain R] (p : Nat) [NeZero p] [CharP R 
p] (x : Int) : exists a b : Nat, ((a : R) ^ 2 + (b : R) ^ 2) = x
参数：R : Type*；p : Nat；x : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CharP.char_is_prime_of_pos`：char_is_prime_of_pos (p : Nat) [NeZero p] [C
harP R p] : Fact p.Prime
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `ZMod.sq_add_sq`：sq_add_sq (p : Nat) [hp : Fact p.Prime] (x : ZMod p) : e
xists a b : ZMod p, a ^ 2 + b ^ 2 = x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ZMod.natCast_val`：natCast_val [NeZero n] (i : ZMod n) : (i.val : R) = ca
st i
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ZMod.cast_add`：cast_add (h : m ∣ n) (a b : ZMod n) : (cast (a + b : ZMod
 n) : R) = cast a + cast b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ZMod.cast_pow`：cast_pow (h : m ∣ n) (a : ZMod n) (k : Nat) : (cast (a ^ 
k : ZMod n) : R) = (cast a) ^ k
· 使用定理 `map_intCast`：map_intCast [FunLike F α β] [RingHomClass F α β] (f : F) (n
 : Int) : f n = n
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem sq_add_sq (R : Type*) [Ring R] [IsDomain R] (p : ℕ) [NeZero p] [CharP R p] (x : ℤ) :
    ∃ a b : ℕ, ((a : R) ^ 2 + (b : R) ^ 2) = x := by
  have := char_is_prime_of_pos R p
  obtain ⟨a, b, hab⟩ := ZMod.sq_add_sq p x
  refine ⟨a.val, b.val, ?_⟩
  simpa using congr_arg (ZMod.castHom dvd_rfl R) hab

end CharP

open scoped Nat

open ZMod

/-- The **Fermat-Euler totient theorem**. `Nat.ModEq.pow_totient` is an alternative statement
  of the same theorem. -/
@[simp]
/-
**ZMod.pow_totient** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ZMod.pow_totient {n : Nat} (x : (ZMod n)ˣ) : x ^ φ n = 1
参数：x : (ZMod n)ˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.totient_zero`：totient_zero : φ 0 = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ZMod.card_units_eq_totient`：∀ (n : ℕ) [NeZero n] [inst : Fintype (ZMod n
)ˣ], Fintype.card (ZMod n)ˣ = n.totient
· 使用定理 `pow_card_eq_one`：pow_card_eq_one : x ^ Fintype.card G = 1

--- 原说明 ---
The **Fermat-Euler totient theorem**. `Nat.ModEq.pow_totient` is an alternative 
statement
  of the same theorem.
-/
theorem ZMod.pow_totient {n : ℕ} (x : (ZMod n)ˣ) : x ^ φ n = 1 := by
  cases n
  · rw [Nat.totient_zero, pow_zero]
  · rw [← card_units_eq_totient, pow_card_eq_one]

/-- The **Fermat-Euler totient theorem**. `ZMod.pow_totient` is an alternative statement
  of the same theorem. -/
/-
**Nat.ModEq.pow_totient** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.ModEq.pow_totient {x n : Nat} (h : Nat.Coprime x n) : x ^ φ n ≡ 1 [MOD
 n]
参数：h : Nat.Coprime x n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.natCast_eq_natCast_iff`：natCast_eq_natCast_iff (a b c : Nat) : (a :
 ZMod c) = (b : ZMod c) ↔ a ≡ b [MOD c]
· 使用定理 `ZMod.pow_totient`：ZMod.pow_totient {n : Nat} (x : (ZMod n)ˣ) : x ^ φ n =
 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'

--- 原说明 ---
The **Fermat-Euler totient theorem**. `ZMod.pow_totient` is an alternative state
ment
  of the same theorem.
-/
theorem Nat.ModEq.pow_totient {x n : ℕ} (h : Nat.Coprime x n) : x ^ φ n ≡ 1 [MOD n] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  let x' : Units (ZMod n) := ZMod.unitOfCoprime _ h
  have := ZMod.pow_totient x'
  apply_fun ((fun (x : Units (ZMod n)) => (x : ZMod n)) : Units (ZMod n) → ZMod n) at this
  simpa only [Nat.succ_eq_add_one, Nat.cast_pow, Units.val_one, Nat.cast_one,
    coe_unitOfCoprime, Units.val_pow_eq_pow_val]

open FiniteField

namespace ZMod

variable {p : ℕ} [Fact p.Prime]

/-
**ZMod.** 是 Mathlib 中的一个实例，位于命名空间 `ZMod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Subsingleton (Subfield (ZMod p)) :=
  subsingleton_of_bot_eq_top <| top_unique (a := ⊥) fun n _ ↦
  have := zsmul_mem (one_mem (⊥ : Subfield (ZMod p))) n.val
  by rwa [natCast_zsmul, Nat.smul_one_eq_cast, ZMod.natCast_zmod_val] at this
/-
**ZMod.fieldRange_castHom_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：fieldRange_castHom_eq_bot (p : Nat) [Fact p.Prime] [DivisionRing K] [CharP
 K p] : (ZMod.castHom (m
参数：p : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.fieldRange_eq_map`：fieldRange_eq_map : f.fieldRange = Subfield.m
ap f ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subfield.map_bot`：map_bot (f : K ->+* L) : (⊥ : Subfield K).map f = ⊥
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `ZMod.instSubsingletonSubfield`：∀ {p : ℕ} [inst : Fact (Nat.Prime p)], Su
bsingleton (Subfield (ZMod p))
-/
theorem fieldRange_castHom_eq_bot (p : ℕ) [Fact p.Prime] [DivisionRing K] [CharP K p] :
    (ZMod.castHom (m := p) dvd_rfl K).fieldRange = (⊥ : Subfield K) := by
  rw [RingHom.fieldRange_eq_map, ← Subfield.map_bot (K := ZMod p), Subsingleton.elim ⊥]

/-- A variation on Fermat's little theorem. See `ZMod.pow_card_sub_one_eq_one` -/
@[simp]
/-
**ZMod.pow_card** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：pow_card (x : ZMod p) : x ^ p = x
参数：x : ZMod p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `FiniteField.pow_card`：pow_card (a : K) : a ^ q = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.card`：card (n : Nat) [Fintype (ZMod n)] : Fintype.card (ZMod n) = n

--- 原说明 ---
A variation on Fermat's little theorem. See `ZMod.pow_card_sub_one_eq_one`
-/
theorem pow_card (x : ZMod p) : x ^ p = x := by
  have h := FiniteField.pow_card x; rwa [ZMod.card p] at h

@[simp]
/-
**ZMod.pow_card_pow** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：pow_card_pow {n : Nat} (x : ZMod p) : x ^ p ^ n = x
参数：x : ZMod p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `ZMod.pow_card`：pow_card (x : ZMod p) : x ^ p = x
-/
theorem pow_card_pow {n : ℕ} (x : ZMod p) : x ^ p ^ n = x := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, pow_mul, ih, pow_card]

@[simp]
/-
**ZMod.frobenius_zmod** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：frobenius_zmod (p : Nat) [Fact p.Prime] : frobenius (ZMod p) p = RingHom.i
d _
参数：p : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `frobenius_def`：frobenius_def : frobenius R p x = x ^ p
· 使用定理 `ZMod.pow_card`：pow_card (x : ZMod p) : x ^ p = x
· 使用定理 `RingHom.id_apply`：id_apply (x : α) : RingHom.id α x = x
-/
theorem frobenius_zmod (p : ℕ) [Fact p.Prime] : frobenius (ZMod p) p = RingHom.id _ := by
  ext a
  rw [frobenius_def, ZMod.pow_card, RingHom.id_apply]

-- This was a `simp` lemma, but now the LHS simplifies to `φ p`.
/-
**ZMod.card_units** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：card_units (p : Nat) [Fact p.Prime] : Fintype.card (ZMod p)ˣ = p - 1
参数：p : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_units`：Fintype.card_units [GroupWithZero α] [Fintype α] [De
cidableEq α] : Fintype.card αˣ = Fintype.card α - 1
· 使用定理 `ZMod.card`：card (n : Nat) [Fintype (ZMod n)] : Fintype.card (ZMod n) = n
-/
theorem card_units (p : ℕ) [Fact p.Prime] : Fintype.card (ZMod p)ˣ = p - 1 := by
  rw [Fintype.card_units, card]

/-- **Fermat's Little Theorem**: for every unit `a` of `ZMod p`, we have `a ^ (p - 1) = 1`. -/
/-
**ZMod.units_pow_card_sub_one_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：units_pow_card_sub_one_eq_one (p : Nat) [Fact p.Prime] (a : (ZMod p)ˣ) : a
 ^ (p - 1) = 1
参数：p : Nat；a : (ZMod p)ˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.card_units`：card_units (p : Nat) [Fact p.Prime] : Fintype.card (ZMo
d p)ˣ = p - 1
· 使用定理 `pow_card_eq_one`：pow_card_eq_one : x ^ Fintype.card G = 1

--- 原说明 ---
**Fermat's Little Theorem**: for every unit `a` of `ZMod p`, we have `a ^ (p - 1
) = 1`.
-/
theorem units_pow_card_sub_one_eq_one (p : ℕ) [Fact p.Prime] (a : (ZMod p)ˣ) : a ^ (p - 1) = 1 := by
  rw [← card_units p, pow_card_eq_one]

/-- **Fermat's Little Theorem**: for all nonzero `a : ZMod p`, we have `a ^ (p - 1) = 1`. -/
/-
**ZMod.pow_card_sub_one_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：pow_card_sub_one_eq_one {a : ZMod p} (ha : a != 0) : a ^ (p - 1) = 1
参数：ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `FiniteField.pow_card_sub_one_eq_one`：pow_card_sub_one_eq_one (a : K) (ha
 : a != 0) : a ^ (q - 1) = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.card`：card (n : Nat) [Fintype (ZMod n)] : Fintype.card (ZMod n) = n

--- 原说明 ---
**Fermat's Little Theorem**: for all nonzero `a : ZMod p`, we have `a ^ (p - 1) 
= 1`.
-/
theorem pow_card_sub_one_eq_one {a : ZMod p} (ha : a ≠ 0) :
    a ^ (p - 1) = 1 := by
  have h := FiniteField.pow_card_sub_one_eq_one a ha
  rwa [ZMod.card p] at h
/-
**ZMod.pow_card_sub_one** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：pow_card_sub_one (a : ZMod p) : a ^ (p - 1) = if a != 0 then 1 else 0
参数：a : ZMod p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `ZMod.pow_card_sub_one_eq_one`：pow_card_sub_one_eq_one {a : ZMod p} (ha :
 a != 0) : a ^ (p - 1) = 1
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_not_not`：of_not_not {a : Prop} : ¬¬a -> a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pow_card_sub_one (a : ZMod p) :
    a ^ (p - 1) = if a ≠ 0 then 1 else 0 := by
  split_ifs with ha
  · exact pow_card_sub_one_eq_one ha
  · simp [of_not_not ha, (Fact.out : p.Prime).one_lt, tsub_eq_zero_iff_le]
/-
**ZMod.orderOf_units_dvd_card_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：orderOf_units_dvd_card_sub_one (u : (ZMod p)ˣ) : orderOf u ∣ p - 1
参数：u : (ZMod p)ˣ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `orderOf_dvd_of_pow_eq_one`：orderOf_dvd_of_pow_eq_one (h : x ^ n = 1) : o
rderOf x ∣ n
· 使用定理 `ZMod.units_pow_card_sub_one_eq_one`：units_pow_card_sub_one_eq_one (p : N
at) [Fact p.Prime] (a : (ZMod p)ˣ) : a ^ (p - 1) = 1
-/
theorem orderOf_units_dvd_card_sub_one (u : (ZMod p)ˣ) : orderOf u ∣ p - 1 :=
  orderOf_dvd_of_pow_eq_one <| units_pow_card_sub_one_eq_one _ _
/-
**ZMod.orderOf_dvd_card_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：orderOf_dvd_card_sub_one {a : ZMod p} (ha : a != 0) : orderOf a ∣ p - 1
参数：ha : a != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `orderOf_dvd_of_pow_eq_one`：orderOf_dvd_of_pow_eq_one (h : x ^ n = 1) : o
rderOf x ∣ n
· 使用定理 `ZMod.pow_card_sub_one_eq_one`：pow_card_sub_one_eq_one {a : ZMod p} (ha :
 a != 0) : a ^ (p - 1) = 1
-/
theorem orderOf_dvd_card_sub_one {a : ZMod p} (ha : a ≠ 0) :
    orderOf a ∣ p - 1 :=
  orderOf_dvd_of_pow_eq_one <| pow_card_sub_one_eq_one ha

open Polynomial
/-
**ZMod.expand_card** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：expand_card (f : Polynomial (ZMod p)) : expand (ZMod p) p f = f ^ p
参数：f : Polynomial (ZMod p)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `FiniteField.expand_card`：expand_card (f : K[X]) : expand K q f = f ^ q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.card`：card (n : Nat) [Fintype (ZMod n)] : Fintype.card (ZMod n) = n
-/
theorem expand_card (f : Polynomial (ZMod p)) :
    expand (ZMod p) p f = f ^ p := by have h := FiniteField.expand_card f; rwa [ZMod.card p] at h

end ZMod

/-- **Fermat's Little Theorem**: for all `a : ℤ` coprime to `p`, we have
`a ^ (p - 1) ≡ 1 [ZMOD p]`. -/
/-
**Int.ModEq.pow_card_sub_one_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.ModEq.pow_card_sub_one_eq_one {p : Nat} (hp : Nat.Prime p) {n : Int} (
hpn : IsCoprime n p) : n ^ (p - 1) ≡ 1 [ZMOD p]
参数：hp : Nat.Prime p；hpn : IsCoprime n p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CharP.intCast_eq_zero_iff`：intCast_eq_zero_iff (a : Int) : (a : R) = 0 ↔
 (p : Int) ∣ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Prime.coprime_iff_not_dvd`：Prime.coprime_iff_not_dvd {p n : Nat} (pp : P
rime p) : Coprime p n ↔ ¬p ∣ n
· 使用定理 `IsBezout.of_isPrincipalIdealRing`：∀ (R : Type u) [inst : Semiring R] [Is
PrincipalIdealRing R], IsBezout R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.prime_iff_prime_int`：prime_iff_prime_int {p : Nat} : p.Prime ↔ _root
_.Prime (p : Int)
· 使用定理 `IsCoprime.symm`：IsCoprime.symm (H : IsCoprime x y) : IsCoprime y x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_pow`：∀ {R : Type u_1} [inst : Ring R] (n : ℤ) (m : ℕ), ↑(n ^ m)
 = ↑n ^ m
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `ZMod.pow_card_sub_one_eq_one`：pow_card_sub_one_eq_one {a : ZMod p} (ha :
 a != 0) : a ^ (p - 1) = 1

--- 原说明 ---
**Fermat's Little Theorem**: for all `a : ℤ` coprime to `p`, we have
`a ^ (p - 1) ≡ 1 [ZMOD p]`.
-/
theorem Int.ModEq.pow_card_sub_one_eq_one {p : ℕ} (hp : Nat.Prime p) {n : ℤ} (hpn : IsCoprime n p) :
    n ^ (p - 1) ≡ 1 [ZMOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  have : ¬(n : ZMod p) = 0 := by
    rw [CharP.intCast_eq_zero_iff _ p, ← (Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd]
    · exact hpn.symm
  simpa [← ZMod.intCast_eq_intCast_iff] using ZMod.pow_card_sub_one_eq_one this
/-
**Int.prime_dvd_pow_sub_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.prime_dvd_pow_sub_one {p : Nat} (hp : Nat.Prime p) {n : Int} (hpn : Is
Coprime n p) : (p : Int) ∣ n ^ (p - 1) - 1
参数：hp : Nat.Prime p；hpn : IsCoprime n p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ModEq.dvd`：∀ {n a b : ℤ}, a ≡ b [ZMOD n] → n ∣ b - a
· 使用定理 `Int.ModEq.symm`：∀ {n a b : ℤ}, a ≡ b [ZMOD n] → b ≡ a [ZMOD n]
· 使用定理 `Int.ModEq.pow_card_sub_one_eq_one`：Int.ModEq.pow_card_sub_one_eq_one {p 
: Nat} (hp : Nat.Prime p) {n : Int} (hpn : IsCoprime n p) : n ^ (p - 1) ≡ 1 [ZMO
D p]
-/
theorem Int.prime_dvd_pow_sub_one {p : ℕ} (hp : Nat.Prime p) {n : ℤ} (hpn : IsCoprime n p) :
    (p : ℤ) ∣ n ^ (p - 1) - 1 :=
  (ModEq.pow_card_sub_one_eq_one hp hpn).symm.dvd
/-
**Int.ModEq.pow_prime_eq_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.ModEq.pow_prime_eq_self {p : Nat} (hp : Nat.Prime p) (n : Int) : n ^ p
 ≡ n [ZMOD p]
参数：hp : Nat.Prime p；n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_pow`：∀ {R : Type u_1} [inst : Ring R] (n : ℤ) (m : ℕ), ↑(n ^ m)
 = ↑n ^ m
· 使用定理 `ZMod.pow_card`：pow_card (x : ZMod p) : x ^ p = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Int.ModEq.pow_prime_eq_self {p : ℕ} (hp : Nat.Prime p) (n : ℤ) : n ^ p ≡ n [ZMOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  simp [← ZMod.intCast_eq_intCast_iff]
/-
**Int.prime_dvd_pow_self_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.prime_dvd_pow_self_sub {p : Nat} (hp : Nat.Prime p) (n : Int) : (p : I
nt) ∣ n ^ p - n
参数：hp : Nat.Prime p；n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ModEq.dvd`：∀ {n a b : ℤ}, a ≡ b [ZMOD n] → n ∣ b - a
· 使用定理 `Int.ModEq.symm`：∀ {n a b : ℤ}, a ≡ b [ZMOD n] → b ≡ a [ZMOD n]
· 使用定理 `Int.ModEq.pow_prime_eq_self`：Int.ModEq.pow_prime_eq_self {p : Nat} (hp :
 Nat.Prime p) (n : Int) : n ^ p ≡ n [ZMOD p]
-/
theorem Int.prime_dvd_pow_self_sub {p : ℕ} (hp : Nat.Prime p) (n : ℤ) : (p : ℤ) ∣ n ^ p - n :=
  (ModEq.pow_prime_eq_self hp n).symm.dvd
/-
**Int.ModEq.pow_eq_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.ModEq.pow_eq_pow {p x y : Nat} (hp : Nat.Prime p) (h : p - 1 ∣ x - y) 
(hxy : y <= x) (hy : 0 < y) (n : Int) : n ^ x ≡ n ^ y [ZMOD p]
参数：hp : Nat.Prime p；h : p - 1 ∣ x - y；hxy : y <= x；hy : 0 < y；n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `Int.ModEq.instIsTrans`：∀ {n : ℤ}, IsTrans ℤ n.ModEq
· 使用定理 `Int.ModEq.pow`：∀ {n a b : ℤ} (m : ℕ), a ≡ b [ZMOD n] → a ^ m ≡ b ^ m [ZM
OD n]
· 使用定理 `Int.ModEq.symm`：∀ {n a b : ℤ}, a ≡ b [ZMOD n] → b ≡ a [ZMOD n]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Int.ModEq.refl`：∀ {n : ℤ} (a : ℤ), a ≡ a [ZMOD n]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_sub_mul_pow`：pow_sub_mul_pow (a : M) (h : m <= n) : a ^ (n - m) * a 
^ m = a ^ n
· 使用定理 `Nat.mul_div_eq_iff_dvd`：∀ {n d : ℕ}, d * (n / d) = n ↔ d ∣ n
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `Int.ModEq.mul`：∀ {n a b c d : ℤ}, a ≡ b [ZMOD n] → c ≡ d [ZMOD n] → a * 
c ≡ b * d [ZMOD n]
· 使用定理 `Int.ModEq.pow_card_sub_one_eq_one`：Int.ModEq.pow_card_sub_one_eq_one {p 
: Nat} (hp : Nat.Prime p) {n : Int} (hpn : IsCoprime n p) : n ^ (p - 1) ≡ 1 [ZMO
D p]
· 使用定理 `IsCoprime.symm`：IsCoprime.symm (H : IsCoprime x y) : IsCoprime y x
· 使用定理 `Prime.coprime_iff_not_dvd`：Prime.coprime_iff_not_dvd {p n : Nat} (pp : P
rime p) : Coprime p n ↔ ¬p ∣ n
· 使用定理 `IsBezout.of_isPrincipalIdealRing`：∀ (R : Type u) [inst : Semiring R] [Is
PrincipalIdealRing R], IsBezout R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.prime_iff_prime_int`：prime_iff_prime_int {p : Nat} : p.Prime ↔ _root
_.Prime (p : Int)
· 使用定理 `Int.modEq_zero_iff_dvd`：modEq_zero_iff_dvd : a ≡ 0 [ZMOD n] ↔ n ∣ a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem Int.ModEq.pow_eq_pow {p x y : ℕ} (hp : Nat.Prime p) (h : p - 1 ∣ x - y) (hxy : y ≤ x)
    (hy : 0 < y) (n : ℤ) : n ^ x ≡ n ^ y [ZMOD p] := by
  rw [← Nat.mul_div_eq_iff_dvd] at h
  by_cases hn : n ≡ 0 [ZMOD p]
  · grw [hn, zero_pow (hy.trans_le hxy).ne', zero_pow hy.ne']
  · rw [Int.modEq_zero_iff_dvd, ← (Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd] at hn
    grw [← pow_sub_mul_pow n hxy, ← h, pow_mul, Int.ModEq.pow_card_sub_one_eq_one hp hn.symm,
      one_pow, one_mul]

/-- **Fermat's Little Theorem**: for all `n : ℕ` coprime to `p`, we have
`n ^ (p - 1) ≡ 1 [MOD p]`. -/
/-
**Nat.ModEq.pow_card_sub_one_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.ModEq.pow_card_sub_one_eq_one {p : Nat} (hp : p.Prime) {n : Nat} (hpn 
: n.Coprime p) : n ^ (p - 1) ≡ 1 [MOD p]
参数：hp : p.Prime；hpn : n.Coprime p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.natCast_modEq_iff`：natCast_modEq_iff {a b n : Nat} : a ≡ b [ZMOD n] 
↔ a ≡ b [MOD n]
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Int.ModEq.pow_card_sub_one_eq_one`：Int.ModEq.pow_card_sub_one_eq_one {p 
: Nat} (hp : Nat.Prime p) {n : Int} (hpn : IsCoprime n p) : n ^ (p - 1) ≡ 1 [ZMO
D p]
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.isCoprime_iff_coprime`：Nat.isCoprime_iff_coprime {m n : Nat} : IsCop
rime (m : Int) n ↔ Nat.Coprime m n

--- 原说明 ---
**Fermat's Little Theorem**: for all `n : ℕ` coprime to `p`, we have
`n ^ (p - 1) ≡ 1 [MOD p]`.
-/
theorem Nat.ModEq.pow_card_sub_one_eq_one {p : ℕ} (hp : p.Prime) {n : ℕ} (hpn : n.Coprime p) :
    n ^ (p - 1) ≡ 1 [MOD p] := by
  rw [← Int.natCast_modEq_iff, Nat.cast_pow, Nat.cast_one]
  exact Int.ModEq.pow_card_sub_one_eq_one hp (isCoprime_iff_coprime.mpr hpn)

/-- **Fermat's Little Theorem**: for all `n : ℕ` coprime to `p`, we have
`(n ^ (p - 1) - 1) % p = 0`. -/
/-
**Nat.pow_card_sub_one_sub_one_mod_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.pow_card_sub_one_sub_one_mod_card {p : Nat} (hp : p.Prime) {n : Nat} (
hpn : n.Coprime p) : (n ^ (p - 1) - 1) % p = 0
参数：hp : p.Prime；hpn : n.Coprime p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.sub_mod_eq_zero_of_mod_eq`：∀ {m k n : ℕ}, m % k = n % k → (m - n) % 
k = 0
· 使用定理 `Nat.ModEq.pow_card_sub_one_eq_one`：Nat.ModEq.pow_card_sub_one_eq_one {p 
: Nat} (hp : p.Prime) {n : Nat} (hpn : n.Coprime p) : n ^ (p - 1) ≡ 1 [MOD p]

--- 原说明 ---
**Fermat's Little Theorem**: for all `n : ℕ` coprime to `p`, we have
`(n ^ (p - 1) - 1) % p = 0`.
-/
theorem Nat.pow_card_sub_one_sub_one_mod_card {p : ℕ} (hp : p.Prime) {n : ℕ} (hpn : n.Coprime p) :
    (n ^ (p - 1) - 1) % p = 0 :=
  Nat.sub_mod_eq_zero_of_mod_eq (Nat.ModEq.pow_card_sub_one_eq_one hp hpn)
/-
**pow_pow_modEq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_pow_modEq_one (p m a : Nat) : (1 + p * a) ^ (p ^ m) ≡ 1 [MOD p ^ m]
参数：p m a : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.modEq_one`：modEq_one : a ≡ b [MOD 1]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.modEq_iff_dvd'`：modEq_iff_dvd' (h : a <= b) : a ≡ b [MOD n] ↔ n ∣ b 
- a
· 使用引理 `Nat.one_le_pow'`：one_le_pow' (n m : Nat) : 1 <= (m + 1) ^ n
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Nat.ModEq.comm`：∀ {n a b : ℕ}, a ≡ b [MOD n] ↔ b ≡ a [MOD n]
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `tsub_eq_iff_eq_add_of_le`：tsub_eq_iff_eq_add_of_le (h : b <= a) : a - b 
= c ↔ a = c + b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `add_pow`：add_pow [CommSemiring R] (x y : R) (n : Nat) : (x + y) ^ n = ∑ 
m in range (n + 1), x ^ m * y ^ (n - m) * n.choose m
· 使用定理 `Finset.sum_range_succ'`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ
 → M) (n : ℕ),   ∑ k ∈ Finset.range (n + 1), f k = ∑ k ∈ Finset.range n, f (k + 
1) + f 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Nat.choose_zero_right`：choose_zero_right (n : Nat) : choose n 0 = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.ModEq.add_right`：∀ {n a b : ℕ} (c : ℕ), a ≡ b [MOD n] → a + c ≡ b + 
c [MOD n]
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.modEq_zero_iff_dvd`：modEq_zero_iff_dvd : a ≡ 0 [MOD n] ↔ n ∣ a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_dvd_mul_left`：mul_dvd_mul_left (a : α) (h : b ∣ c) : a * b ∣ a * c
（共 41 条，此处仅展示前 30 条）
-/
theorem pow_pow_modEq_one (p m a : ℕ) : (1 + p * a) ^ (p ^ m) ≡ 1 [MOD p ^ m] := by
  induction m with
  | zero => exact Nat.modEq_one
  | succ m hm =>
    rw [Nat.ModEq.comm, add_comm, Nat.modEq_iff_dvd' (Nat.one_le_pow' _ _)] at hm
    obtain ⟨d, hd⟩ := hm
    rw [tsub_eq_iff_eq_add_of_le (Nat.one_le_pow' _ _), add_comm] at hd
    rw [pow_succ, pow_mul, hd, add_pow, Finset.sum_range_succ', pow_zero, one_mul, one_pow,
      one_mul, Nat.choose_zero_right, Nat.cast_one]
    refine Nat.ModEq.add_right 1 (Nat.modEq_zero_iff_dvd.mpr ?_)
    simp_rw [one_pow, mul_one, pow_succ', mul_assoc, ← Finset.mul_sum]
    refine mul_dvd_mul_left (p ^ m) (dvd_mul_of_dvd_right (Finset.dvd_sum fun k hk ↦ ?_) d)
    cases m
    · rw [pow_zero, pow_one, one_mul, add_comm, add_left_inj] at hd
      cases k <;> simp [← hd, mul_assoc, pow_succ']
    · cases k <;> simp [mul_assoc, pow_succ']
/-
**ZMod.eq_one_or_isUnit_sub_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ZMod.eq_one_or_isUnit_sub_one {n p k : Nat} [Fact p.Prime] (hn : n = p ^ k
) (a : ZMod n) (ha : (orderOf a).Coprime n) : a = 1 ∨ IsUnit (a - 1)
参数：hn : n = p ^ k；a : ZMod n；ha : (orderOf a).Coprime n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `orderOf_eq_one_iff`：orderOf_eq_one_iff : orderOf x = 1 ↔ x = 1
· 使用定理 `Nat.coprime_zero_right`：∀ (n : ℕ), n.Coprime 0 ↔ n = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isUnit_neg_one`：isUnit_neg_one [Monoid α] [HasDistribNeg α] : IsUnit (-1
 : α)
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `ZMod.natCast_zmod_surjective`：natCast_zmod_surjective [NeZero n] : Funct
ion.Surjective ((↑) : Nat -> ZMod n)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.or_iff_not_imp_right`：∀ {a b : Prop}, a ∨ b ↔ ¬b → a
· 使用定理 `Nat.Coprime.eq_one_of_dvd`：∀ {k m : ℕ}, k.Coprime m → k ∣ m → k = 1
· 使用定理 `orderOf_dvd_iff_pow_eq_one`：orderOf_dvd_iff_pow_eq_one {n : Nat} : order
Of x ∣ n ↔ x ^ n = 1
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `ZMod.natCast_eq_natCast_iff`：natCast_eq_natCast_iff (a b c : Nat) : (a :
 ZMod c) = (b : ZMod c) ↔ a ≡ b [MOD c]
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.lt_one_iff`：∀ {n : ℕ}, n < 1 ↔ n = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `not_imp_comm`：not_imp_comm : ¬a -> b ↔ ¬b -> a
· 使用定理 `Nat.Prime.coprime_pow_of_not_dvd`：∀ {p m a : ℕ}, Nat.Prime p → ¬p ∣ a → 
a.Coprime (p ^ m)
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用引理 `ZMod.isUnit_iff_coprime`：isUnit_iff_coprime (m n : Nat) : IsUnit (m : ZM
od n) ↔ m.Coprime n
· 使用定理 `Nat.cast_sub`：cast_sub {m n} (h : m <= n) : ((n - m : Nat) : R) = n - m
· 使用定理 `pow_pow_modEq_one`：pow_pow_modEq_one (p m a : Nat) : (1 + p * a) ^ (p ^ 
m) ≡ 1 [MOD p ^ m]
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `tsub_eq_iff_eq_add_of_le`：tsub_eq_iff_eq_add_of_le (h : b <= a) : a - b 
= c ↔ a = c + b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
（共 31 条，此处仅展示前 30 条）
-/
theorem ZMod.eq_one_or_isUnit_sub_one {n p k : ℕ} [Fact p.Prime] (hn : n = p ^ k) (a : ZMod n)
    (ha : (orderOf a).Coprime n) : a = 1 ∨ IsUnit (a - 1) := by
  rcases eq_or_ne n 0 with rfl | hn0
  · exact Or.inl (orderOf_eq_one_iff.mp ((orderOf a).coprime_zero_right.mp ha))
  rcases eq_or_ne a 0 with rfl | ha0
  · exact Or.inr (zero_sub (1 : ZMod n) ▸ isUnit_neg_one)
  have : NeZero n := ⟨hn0⟩
  obtain ⟨a, rfl⟩ := ZMod.natCast_zmod_surjective a
  rw [← orderOf_eq_one_iff, or_iff_not_imp_right]
  refine fun h ↦ ha.eq_one_of_dvd ?_
  rw [orderOf_dvd_iff_pow_eq_one, ← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff, hn]
  replace ha0 : 1 ≤ a := by
    contrapose! ha0
    rw [Nat.lt_one_iff.mp ha0, Nat.cast_zero]
  rw [← Nat.cast_one, ← Nat.cast_sub ha0, ZMod.isUnit_iff_coprime, hn] at h
  obtain ⟨b, hb⟩ := not_imp_comm.mp (Nat.Prime.coprime_pow_of_not_dvd Fact.out) h
  rw [tsub_eq_iff_eq_add_of_le ha0, add_comm] at hb
  exact hb ▸ pow_pow_modEq_one p k b

section prime_subfield

variable {F : Type*} [Field F]

/-
**mem_bot_iff_intCast** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_bot_iff_intCast (p : Nat) [Fact p.Prime] (K) [DivisionRing K] [CharP K
 p] {x : K} : x in (⊥ : Subfield K) ↔ exists n : Int, n = x
参数：p : Nat；K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.fieldRange_castHom_eq_bot`：fieldRange_castHom_eq_bot (p : Nat) [Fac
t p.Prime] [DivisionRing K] [CharP K p] : (ZMod.castHom (m
· 使用定理 `Function.Surjective.exists`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Surjective f → ∀ {p : β → Prop}, (∃ y, p y) ↔ ∃ x, p (f x)
· 使用定理 `ZMod.intCast_surjective`：intCast_surjective : Function.Surjective ((↑) :
 Int -> ZMod n)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ZMod.cast_intCast`：cast_intCast (h : m ∣ n) (k : Int) : (cast (k : ZMod 
n) : R) = k
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_bot_iff_intCast (p : ℕ) [Fact p.Prime] (K) [DivisionRing K] [CharP K p] {x : K} :
    x ∈ (⊥ : Subfield K) ↔ ∃ n : ℤ, n = x := by
  simp [← fieldRange_castHom_eq_bot p, ZMod.intCast_surjective.exists]

variable (F) (p : ℕ) [Fact p.Prime] [CharP F p]
/-
**Subfield.card_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subfield.card_bot : Nat.card (⊥ : Subfield F) = p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.fieldRange_castHom_eq_bot`：fieldRange_castHom_eq_bot (p : Nat) [Fac
t p.Prime] [DivisionRing K] [CharP K p] : (ZMod.castHom (m
· 使用定理 `Nat.card_eq_of_bijective`：card_eq_of_bijective (f : α -> β) (hf : Functi
on.Bijective f) : Nat.card α = Nat.card β
· 使用定理 `RingHom.rangeRestrictField_bijective`：rangeRestrictField_bijective (f : 
K ->+* L) : Function.Bijective (rangeRestrictField f)
· 使用定理 `Nat.card_zmod`：card_zmod (n : Nat) : Nat.card (ZMod n) = n
-/
theorem Subfield.card_bot : Nat.card (⊥ : Subfield F) = p := by
  rw [← fieldRange_castHom_eq_bot p,
    ← Nat.card_eq_of_bijective _ (RingHom.rangeRestrictField_bijective _), Nat.card_zmod]

/-- The prime subfield is finite. -/
@[instance_reducible]
/-
**Subfield.fintypeBot** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Subfield.fintypeBot : Fintype (⊥ : Subfield F)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a

--- 原说明 ---
The prime subfield is finite.
-/
def Subfield.fintypeBot : Fintype (⊥ : Subfield F) :=
  Fintype.subtype (univ.map ⟨_, (ZMod.castHom (m := p) dvd_rfl F).injective⟩)
    fun _ ↦ by simp_rw [Finset.mem_map, mem_univ, true_and, ← fieldRange_castHom_eq_bot p]; rfl

open Polynomial
/-
**Subfield.roots_X_pow_char_sub_X_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subfield.roots_X_pow_char_sub_X_bot : letI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subfield.card_bot`：Subfield.card_bot : Nat.card (⊥ : Subfield F) = p
· 使用定理 `Fintype.card_eq_nat_card`：∀ {α : Type u_1} {x : Fintype α}, Fintype.card
 α = Nat.card α
· 使用定理 `FiniteField.roots_X_pow_card_sub_X`：roots_X_pow_card_sub_X : roots (X ^ 
q - X : K[X]) = Finset.univ.val
-/
theorem Subfield.roots_X_pow_char_sub_X_bot :
    letI := Subfield.fintypeBot F p
    (X ^ p - X : (⊥ : Subfield F)[X]).roots = Finset.univ.val := by
  let _ := Subfield.fintypeBot F p
  conv_lhs => rw [← card_bot F p, ← Fintype.card_eq_nat_card]
  exact FiniteField.roots_X_pow_card_sub_X _
/-
**Subfield.splits_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subfield.splits_bot : Splits (X ^ p - X : (⊥ : Subfield F)[X])
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.splits_iff_card_roots`：splits_iff_card_roots : Splits f ↔ f.r
oots.card = f.natDegree
· 使用定理 `Subfield.roots_X_pow_char_sub_X_bot`：Subfield.roots_X_pow_char_sub_X_bot
 : letI
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_def`：card_def (s : Finset α) : #s = Multiset.card s.1
· 使用定理 `Finset.card_univ`：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fi
ntype.card α
· 使用定理 `FiniteField.X_pow_card_sub_X_natDegree_eq`：X_pow_card_sub_X_natDegree_eq
 (hp : 1 < p) : (X ^ p - X : K'[X]).natDegree = p
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Fintype.card_eq_nat_card`：∀ {α : Type u_1} {x : Fintype α}, Fintype.card
 α = Nat.card α
· 使用定理 `Subfield.card_bot`：Subfield.card_bot : Nat.card (⊥ : Subfield F) = p
-/
theorem Subfield.splits_bot :
    Splits (X ^ p - X : (⊥ : Subfield F)[X]) := by
  let _ := Subfield.fintypeBot F p
  rw [splits_iff_card_roots, roots_X_pow_char_sub_X_bot, ← Finset.card_def, Finset.card_univ,
    FiniteField.X_pow_card_sub_X_natDegree_eq _ (Fact.out (p := p.Prime)).one_lt,
    Fintype.card_eq_nat_card, card_bot F p]
/-
**Subfield.mem_bot_iff_pow_eq_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subfield.mem_bot_iff_pow_eq_self {x : F} : x in (⊥ : Subfield F) ↔ x ^ p =
 x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.Splits.roots_map`：∀ {R : Type u_1} {S : Type u_2} [inst : Fie
ld R] [inst_1 : CommRing S] [inst_2 : IsDomain S] {f : Polynomial R},   f.Splits
 → ∀ (i : R →+* S…
· 使用定理 `Subfield.splits_bot`：Subfield.splits_bot : Splits (X ^ p - X : (⊥ : Subf
ield F)[X])
· 使用定理 `Subfield.roots_X_pow_char_sub_X_bot`：Subfield.roots_X_pow_char_sub_X_bot
 : letI
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.roots.congr_simp`：∀ {R : Type u} [inst : CommRing R] [inst_1 
: IsDomain R] (p p_1 : Polynomial R), p = p_1 → p.roots = p_1.roots
· 使用定理 `Polynomial.map_sub`：∀ {R : Type u} [inst : Ring R] {p q : Polynomial R} 
{S : Type u_1} [inst_1 : Ring S] (f : R →+* S),   Polynomial.map f (p - q) = Pol
ynomial.…
· 使用定理 `Polynomial.map_pow`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p :
 Polynomial R} [inst_1 : Semiring S] (f : R →+* S) (n : ℕ),   Polynomial.map f (
p ^ n) =…
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `FiniteField.X_pow_card_sub_X_ne_zero`：X_pow_card_sub_X_ne_zero (hp : 1 <
 p) : (X ^ p - X : K'[X]) != 0
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_pow`：eval_pow (n : Nat) : (p ^ n).eval x = p.eval x ^ n
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
-/
theorem Subfield.mem_bot_iff_pow_eq_self {x : F} : x ∈ (⊥ : Subfield F) ↔ x ^ p = x := by
  have := roots_X_pow_char_sub_X_bot F p ▸
      (splits_bot F p).roots_map (Subfield.subtype _) ▸ Multiset.mem_map (b := x)
  simpa [sub_eq_zero, iff_comm, FiniteField.X_pow_card_sub_X_ne_zero F (Fact.out : p.Prime).one_lt]

end prime_subfield

namespace FiniteField

variable {F : Type*} [Field F]

section Finite

variable [Finite F]

/-- In a finite field of characteristic `2`, all elements are squares. -/
/-
**FiniteField.isSquare_of_char_two** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField`。
形式化陈述：isSquare_of_char_two (hF : ringChar F = 2) (a : F) : IsSquare a
参数：hF : ringChar F = 2；a : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ringChar.of_eq`：of_eq {p : Nat} (h : ringChar R = p) : CharP R p
· 使用定理 `isSquare_of_charTwo'`：isSquare_of_charTwo' {R : Type*} [Finite R] [CommR
ing R] [IsReduced R] [CharP R 2] (a : R) : IsSquare a
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R

--- 原说明 ---
In a finite field of characteristic `2`, all elements are squares.
-/
theorem isSquare_of_char_two (hF : ringChar F = 2) (a : F) : IsSquare a :=
  have : CharP F 2 := ringChar.of_eq hF
  isSquare_of_charTwo' a

/-- In a finite field of odd characteristic, not every element is a square. -/
/-
**FiniteField.exists_nonsquare** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField`。
形式化陈述：exists_nonsquare (hF : ringChar F != 2) : exists a : F, ¬IsSquare a
参数：hF : ringChar F != 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用引理 `Ring.neg_one_ne_one_of_char_ne_two`：Ring.neg_one_ne_one_of_char_ne_two {
R : Type*} [NonAssocRing R] [Nontrivial R] (hR : ringChar R != 2) : (-1 : R) != 
1
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a

--- 原说明 ---
In a finite field of odd characteristic, not every element is a square.
-/
theorem exists_nonsquare (hF : ringChar F ≠ 2) : ∃ a : F, ¬IsSquare a := by
  -- Idea: the squaring map on `F` is not injective, hence not surjective
  have h : ¬Function.Injective fun x : F ↦ x * x := fun h ↦
    h.ne (Ring.neg_one_ne_one_of_char_ne_two hF) <| by simp
  simpa [Finite.injective_iff_surjective, Function.Surjective, IsSquare, eq_comm] using h

end Finite

variable [Fintype F]

/-- The finite field `F` has even cardinality iff it has characteristic `2`. -/
/-
**FiniteField.even_card_iff_char_two** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField`。
形式化陈述：even_card_iff_char_two : ringChar F = 2 ↔ Fintype.card F % 2 = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteField.card`：card (p : Nat) [CharP K p] : exists n : Nat+, Nat.Prim
e p ∧ q = p ^ (n : Nat)
· 使用定理 `ringChar.charP`：∀ (R : Type u_1) [inst : NonAssocSemiring R], CharP R (r
ingChar R)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.even_iff`：even_iff : Even n ↔ n % 2 = 0 where mp
· 使用定理 `Nat.even_pow`：∀ {m n : ℕ}, Even (m ^ n) ↔ Even m ∧ n ≠ 0
· 使用定理 `Nat.Prime.even_iff`：∀ {p : ℕ}, Nat.Prime p → (Even p ↔ p = 2)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The finite field `F` has even cardinality iff it has characteristic `2`.
-/
theorem even_card_iff_char_two : ringChar F = 2 ↔ Fintype.card F % 2 = 0 := by
  rcases FiniteField.card F (ringChar F) with ⟨n, hp, h⟩
  rw [h, ← Nat.even_iff, Nat.even_pow, hp.even_iff]
  simp
/-
**FiniteField.even_card_of_char_two** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField`。
形式化陈述：even_card_of_char_two (hF : ringChar F = 2) : Fintype.card F % 2 = 0
参数：hF : ringChar F = 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FiniteField.even_card_iff_char_two`：even_card_iff_char_two : ringChar F 
= 2 ↔ Fintype.card F % 2 = 0
-/
theorem even_card_of_char_two (hF : ringChar F = 2) : Fintype.card F % 2 = 0 :=
  even_card_iff_char_two.mp hF
/-
**FiniteField.odd_card_of_char_ne_two** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField`。
形式化陈述：odd_card_of_char_ne_two (hF : ringChar F != 2) : Fintype.card F % 2 = 1
参数：hF : ringChar F != 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.mod_two_ne_zero`：∀ {n : ℕ}, n % 2 ≠ 0 ↔ n % 2 = 1
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FiniteField.even_card_iff_char_two`：even_card_iff_char_two : ringChar F 
= 2 ↔ Fintype.card F % 2 = 0
-/
theorem odd_card_of_char_ne_two (hF : ringChar F ≠ 2) : Fintype.card F % 2 = 1 :=
  Nat.mod_two_ne_zero.mp (mt even_card_iff_char_two.mpr hF)

/-- If `F` has odd characteristic, then for nonzero `a : F`, we have that `a ^ (#F / 2) = ±1`. -/
/-
**FiniteField.pow_dichotomy** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField`。
形式化陈述：pow_dichotomy (hF : ringChar F != 2) {a : F} (ha : a != 0) : a ^ (Fintype.
card F / 2) = 1 ∨ a ^ (Fintype.card F / 2) = -1
参数：hF : ringChar F != 2；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteField.pow_card_sub_one_eq_one`：pow_card_sub_one_eq_one (a : K) (ha
 : a != 0) : a ^ (q - 1) = 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_self_eq_one_iff`：mul_self_eq_one_iff [NonAssocRing R] [NoZeroDivisor
s R] {a : R} : a * a = 1 ↔ a = 1 ∨ a = -1
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.two_mul_odd_div_two`：two_mul_odd_div_two (hn : n % 2 = 1) : 2 * (n /
 2) = n - 1
· 使用定理 `FiniteField.odd_card_of_char_ne_two`：odd_card_of_char_ne_two (hF : ringC
har F != 2) : Fintype.card F % 2 = 1

--- 原说明 ---
If `F` has odd characteristic, then for nonzero `a : F`, we have that `a ^ (#F /
 2) = ±1`.
-/
theorem pow_dichotomy (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) :
    a ^ (Fintype.card F / 2) = 1 ∨ a ^ (Fintype.card F / 2) = -1 := by
  have h₁ := FiniteField.pow_card_sub_one_eq_one a ha
  rw [← Nat.two_mul_odd_div_two (FiniteField.odd_card_of_char_ne_two hF), mul_comm, pow_mul,
    pow_two] at h₁
  exact mul_self_eq_one_iff.mp h₁

/-- A unit `a` of a finite field `F` of odd characteristic is a square
if and only if `a ^ (#F / 2) = 1`. -/
/-
**FiniteField.unit_isSquare_iff** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField`。
形式化陈述：unit_isSquare_iff (hF : ringChar F != 2) (a : Fˣ) : IsSquare a ↔ a ^ (Fint
ype.card F / 2) = 1
参数：hF : ringChar F != 2；a : Fˣ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCyclic.exists_generator`：IsCyclic.exists_generator [Group α] [IsCyclic
 α] : exists g : α, forall x, x in zpowers g
· 使用定理 `instIsCyclicUnitsOfFinite`：∀ {R : Type u_1} [inst : CommRing R] [IsDomai
n R] [Finite Rˣ], IsCyclic Rˣ
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instFiniteUnits`：∀ {α : Type u_1} [inst : Monoid α] [Finite α], Finite α
ˣ
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mem_powers_iff_mem_zpowers`：mem_powers_iff_mem_zpowers : y in powers x ↔
 y in zpowers x
· 使用引理 `Nat.two_mul_odd_div_two`：two_mul_odd_div_two (hn : n % 2 = 1) : 2 * (n /
 2) = n - 1
· 使用定理 `FiniteField.odd_card_of_char_ne_two`：odd_card_of_char_ne_two (hF : ringC
har F != 2) : Fintype.card F % 2 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `Units.val_injective`：∀ {α : Type u} [inst : Monoid α], Function.Injectiv
e Units.val
· 使用定理 `FiniteField.pow_card_sub_one_eq_one`：pow_card_sub_one_eq_one (a : K) (ha
 : a != 0) : a ^ (q - 1) = 1
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Nat.card_units`：Nat.card_units [GroupWithZero α] : Nat.card αˣ = Nat.car
d α - 1
· 使用定理 `orderOf_eq_card_of_forall_mem_zpowers`：orderOf_eq_card_of_forall_mem_zpo
wers {g : α} (hx : forall x, x in zpowers g) : orderOf g = Nat.card α
· 使用定理 `orderOf_dvd_of_pow_eq_one`：orderOf_dvd_of_pow_eq_one (h : x ^ n = 1) : o
rderOf x ∣ n
· 使用定理 `Nat.div_pos`：∀ {b a : ℕ}, b ≤ a → 0 < b → 0 < a / b
· 使用定理 `Finite.one_lt_card`：one_lt_card [Finite α] [h : Nontrivial α] : 1 < Nat.
card α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.dvd_of_mul_dvd_mul_right`：∀ {k m n : ℕ}, 0 < k → m * k ∣ n * k → m ∣
 n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a

--- 原说明 ---
A unit `a` of a finite field `F` of odd characteristic is a square
if and only if `a ^ (#F / 2) = 1`.
-/
theorem unit_isSquare_iff (hF : ringChar F ≠ 2) (a : Fˣ) :
    IsSquare a ↔ a ^ (Fintype.card F / 2) = 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  obtain ⟨n, hn⟩ : a ∈ Submonoid.powers g := by rw [mem_powers_iff_mem_zpowers]; apply hg
  have hodd := Nat.two_mul_odd_div_two (FiniteField.odd_card_of_char_ne_two hF)
  constructor
  · rintro ⟨y, rfl⟩
    rw [← pow_two, ← pow_mul, hodd]
    apply_fun Units.val using Units.val_injective
    push_cast
    exact FiniteField.pow_card_sub_one_eq_one (y : F) (Units.ne_zero y)
  · subst a; intro h
    rw [← Nat.card_eq_fintype_card] at hodd h
    have key : 2 * (Nat.card F / 2) ∣ n * (Nat.card F / 2) := by
      rw [← pow_mul] at h
      rw [hodd, ← Nat.card_units, ← orderOf_eq_card_of_forall_mem_zpowers hg]
      apply orderOf_dvd_of_pow_eq_one h
    have : 0 < Nat.card F / 2 := Nat.div_pos Finite.one_lt_card (by simp)
    obtain ⟨m, rfl⟩ := Nat.dvd_of_mul_dvd_mul_right this key
    refine ⟨g ^ m, ?_⟩
    dsimp
    rw [mul_comm, pow_mul, pow_two]

/-- A non-zero `a : F` is a square if and only if `a ^ (#F / 2) = 1`. -/
/-
**FiniteField.isSquare_iff** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField`。
形式化陈述：isSquare_iff (hF : ringChar F != 2) {a : F} (ha : a != 0) : IsSquare a ↔ a
 ^ (Fintype.card F / 2) = 1
参数：hF : ringChar F != 2；ha : a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `iff_congr`：∀ {p₁ p₂ q₁ q₂ : Prop}, (p₁ ↔ p₂) → (q₁ ↔ q₂) → ((p₁ ↔ q₁) ↔ 
(p₂ ↔ q₂))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `FiniteField.unit_isSquare_iff`：unit_isSquare_iff (hF : ringChar F != 2) 
(a : Fˣ) : IsSquare a ↔ a ^ (Fintype.card F / 2) = 1

--- 原说明 ---
A non-zero `a : F` is a square if and only if `a ^ (#F / 2) = 1`.
-/
theorem isSquare_iff (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) :
    IsSquare a ↔ a ^ (Fintype.card F / 2) = 1 := by
  apply
    (iff_congr _ (by simp [Units.ext_iff])).mp (FiniteField.unit_isSquare_iff hF (Units.mk0 a ha))
  simp only [IsSquare, Units.ext_iff, Units.val_mk0, Units.val_mul]
  constructor
  · rintro ⟨y, hy⟩; exact ⟨y, hy⟩
  · rintro ⟨y, rfl⟩
    have hy : y ≠ 0 := by rintro rfl; simp at ha
    refine ⟨Units.mk0 y hy, ?_⟩; simp

end FiniteField

