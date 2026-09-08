/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.Polynomial.Degree.CardPowDegree
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.ClassNumber.AdmissibleAbsoluteValue
public import Mathlib.RingTheory.LocalRing.Basic

/-!
# Admissible absolute values on polynomials

This file defines an admissible absolute value `Polynomial.cardPowDegreeIsAdmissible` which we
use to show the class number of the ring of integers of a function field is finite.

## Main results

* `Polynomial.cardPowDegreeIsAdmissible` shows `cardPowDegree`,
  mapping `p : Polynomial 𝔽_q` to `q ^ degree p`, is admissible
-/

@[expose] public section


namespace Polynomial

open AbsoluteValue Real

variable {Fq : Type*} [Fintype Fq]

/-- If `A` is a family of enough low-degree polynomials over a finite semiring, there is a
pair of equal elements in `A`. -/
/-
**Polynomial.exists_eq_polynomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：exists_eq_polynomial [Semiring Fq] {d : Nat} {m : Nat} (hm : Fintype.card 
Fq ^ d <= m) (b : Fq[X]) (hb : natDegree b <= d) (A : Fin m.succ -> Fq[X]) (hA :
 forall i, degree (A i) < degree b) : exists i₀ i₁, i₀ != i₁ ∧ A i₁ = A i₀
参数：hm : Fintype.card Fq ^ d <= m；b : Fq[X]；hb : natDegree b <= d；A : Fin m.succ 
-> Fq[X]；hA : forall i, degree (A i) < degree b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_pi`：∀ {ι : Type u_4} {α : ι → Type u_6} [inst : DecidableEq
 ι] [inst_1 : Fintype ι] [inst_2 : (i : ι) → Fintype (α i)],   Fintype.card ((i 
: ι) …
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `Fintype.exists_ne_map_eq_of_card_lt`：exists_ne_map_eq_of_card_lt (f : α 
-> β) (h : Fintype.card β < Fintype.card α) : exists x y, x != y ∧ f x = f y
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `Polynomial.coeff_eq_zero_of_degree_lt`：coeff_eq_zero_of_degree_lt (h : d
egree p < n) : coeff p n = 0
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.coe_lt_degree`：coe_lt_degree {p : R[X]} {n : Nat} : (n : With
Bot Nat) < degree p ↔ n < natDegree p

--- 原说明 ---
If `A` is a family of enough low-degree polynomials over a finite semiring, ther
e is a
pair of equal elements in `A`.
-/
theorem exists_eq_polynomial [Semiring Fq] {d : ℕ} {m : ℕ} (hm : Fintype.card Fq ^ d ≤ m)
    (b : Fq[X]) (hb : natDegree b ≤ d) (A : Fin m.succ → Fq[X])
    (hA : ∀ i, degree (A i) < degree b) : ∃ i₀ i₁, i₀ ≠ i₁ ∧ A i₁ = A i₀ := by
  -- Since there are > q^d elements of A, and only q^d choices for the highest `d` coefficients,
  -- there must be two elements of A with the same coefficients at
  -- `0`, ... `degree b - 1` ≤ `d - 1`.
  -- In other words, the following map is not injective:
  set f : Fin m.succ → Fin d → Fq := fun i j => (A i).coeff j
  have : Fintype.card (Fin d → Fq) < Fintype.card (Fin m.succ) := by
    simpa using lt_of_le_of_lt hm (Nat.lt_succ_self m)
  -- Therefore, the differences have all coefficients higher than `deg b - d` equal.
  obtain ⟨i₀, i₁, i_ne, i_eq⟩ := Fintype.exists_ne_map_eq_of_card_lt f this
  use i₀, i₁, i_ne
  ext j
  -- The coefficients higher than `deg b` are the same because they are equal to 0.
  by_cases! hbj : degree b ≤ j
  · rw [coeff_eq_zero_of_degree_lt (lt_of_lt_of_le (hA _) hbj),
      coeff_eq_zero_of_degree_lt (lt_of_lt_of_le (hA _) hbj)]
  -- So we only need to look for the coefficients between `0` and `deg b`.
  apply congr_fun i_eq.symm ⟨j, _⟩
  exact lt_of_lt_of_le (coe_lt_degree.mp hbj) hb

/-- If `A` is a family of enough low-degree polynomials over a finite ring,
there is a pair of elements in `A` (with different indices but not necessarily
distinct), such that their difference has small degree. -/
/-
**Polynomial.exists_approx_polynomial_aux** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`
。
形式化陈述：exists_approx_polynomial_aux [Ring Fq] {d : Nat} {m : Nat} (hm : Fintype.c
ard Fq ^ d <= m) (b : Fq[X]) (A : Fin m.succ -> Fq[X]) (hA : forall i, degree (A
 i) < degree b) : exists i₀ i₁, i₀ != i₁ ∧ degree (A i₁ - A i₀) < ↑(natDegree b 
- d)
参数：hm : Fintype.card Fq ^ d <= m；b : Fq[X]；A : Fin m.succ -> Fq[X]；hA : forall i
, degree (A i) < degree b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_lt_of_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_zero`：degree_zero : degree (0 : R[X]) = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fintype.card_pi`：∀ {ι : Type u_4} {α : ι → Type u_6} [inst : DecidableEq
 ι] [inst_1 : Fintype ι] [inst_2 : (i : ι) → Fintype (α i)],   Fintype.card ((i 
: ι) …
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `Fintype.exists_ne_map_eq_of_card_lt`：exists_ne_map_eq_of_card_lt (f : α 
-> β) (h : Fintype.card β < Fintype.card α) : exists x y, x != y ∧ f x = f y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.degree_lt_iff_coeff_zero`：degree_lt_iff_coeff_zero (f : R[X])
 (n : Nat) : degree f < n ↔ forall m : Nat, n <= m -> coeff f m = 0
· 使用定理 `Polynomial.coeff_eq_zero_of_degree_lt`：coeff_eq_zero_of_degree_lt (h : d
egree p < n) : coeff p n = 0
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Polynomial.degree_sub_le`：degree_sub_le (p q : R[X]) : degree (p - q) <=
 max (degree p) (degree q)
· 使用定理 `max_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, b < a → c <
 a → max b c < a
· 使用定理 `Polynomial.coeff_sub`：coeff_sub (p q : R[X]) (n : Nat) : coeff (p - q) n
 = coeff p n - coeff q n
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WithBot.coe_lt_coe`：coe_lt_coe : (a : WithBot α) < b ↔ a < b
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `tsub_le_self`：tsub_le_self : a - b <= a
· 使用定理 `tsub_lt_iff_tsub_lt`：tsub_lt_iff_tsub_lt (h₁ : b <= a) (h₂ : c <= a) : a
 - b < c ↔ a - c < b
· 使用定理 `StarOrderedRing.toExistsAddOfLE`：∀ {R : Type u_1} [inst : NonUnitalSemir
ing R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   Ex
istsAddOfLE R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
If `A` is a family of enough low-degree polynomials over a finite ring,
there is a pair of elements in `A` (with different indices but not necessarily
distinct), such that their difference has small degree.
-/
theorem exists_approx_polynomial_aux [Ring Fq] {d : ℕ} {m : ℕ} (hm : Fintype.card Fq ^ d ≤ m)
    (b : Fq[X]) (A : Fin m.succ → Fq[X]) (hA : ∀ i, degree (A i) < degree b) :
    ∃ i₀ i₁, i₀ ≠ i₁ ∧ degree (A i₁ - A i₀) < ↑(natDegree b - d) := by
  have hb : b ≠ 0 := by
    rintro rfl
    specialize hA 0
    rw [degree_zero] at hA
    exact not_lt_of_ge bot_le hA
  -- Since there are > q^d elements of A, and only q^d choices for the highest `d` coefficients,
  -- there must be two elements of A with the same coefficients at
  -- `degree b - 1`, ... `degree b - d`.
  -- In other words, the following map is not injective:
  set f : Fin m.succ → Fin d → Fq := fun i j => (A i).coeff (natDegree b - j.succ)
  have : Fintype.card (Fin d → Fq) < Fintype.card (Fin m.succ) := by
    simpa using lt_of_le_of_lt hm (Nat.lt_succ_self m)
  -- Therefore, the differences have all coefficients higher than `deg b - d` equal.
  obtain ⟨i₀, i₁, i_ne, i_eq⟩ := Fintype.exists_ne_map_eq_of_card_lt f this
  use i₀, i₁, i_ne
  refine (degree_lt_iff_coeff_zero _ _).mpr fun j hj => ?_
  -- The coefficients higher than `deg b` are the same because they are equal to 0.
  by_cases! hbj : degree b ≤ j
  · refine coeff_eq_zero_of_degree_lt (lt_of_lt_of_le ?_ hbj)
    exact lt_of_le_of_lt (degree_sub_le _ _) (max_lt (hA _) (hA _))
  -- So we only need to look for the coefficients between `deg b - d` and `deg b`.
  rw [coeff_sub, sub_eq_zero]
  rw [degree_eq_natDegree hb] at hbj
  have hbj : j < natDegree b := (@WithBot.coe_lt_coe _ _ _).mp hbj
  have hj : natDegree b - j.succ < d := by
    by_cases! hd : natDegree b < d
    · exact lt_of_le_of_lt tsub_le_self hd
    · have := lt_of_le_of_lt hj (Nat.lt_succ_self j)
      rwa [tsub_lt_iff_tsub_lt hd hbj] at this
  have : j = b.natDegree - (natDegree b - j.succ).succ := by
    rw [← Nat.succ_sub hbj, Nat.succ_sub_succ, tsub_tsub_cancel_of_le hbj.le]
  convert! congr_fun i_eq.symm ⟨natDegree b - j.succ, hj⟩

variable [Field Fq]

/-- If `A` is a family of enough low-degree polynomials over a finite field,
there is a pair of elements in `A` (with different indices but not necessarily
distinct), such that the difference of their remainders is close together. -/
/-
**Polynomial.exists_approx_polynomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：exists_approx_polynomial {b : Fq[X]} (hb : b != 0) {ε : Real} (hε : 0 < ε)
 (A : Fin (Fintype.card Fq ^ ⌈-log ε / log (Fintype.card Fq)⌉₊).succ -> Fq[X]) :
 exists i₀ i₁, i₀ != i₁ ∧ (cardPowDegree (A i₁ % b - A i₀ % b) : Real) < cardPow
Degree b • ε
参数：hb : b != 0；hε : 0 < ε；A : Fin (Fintype.card Fq ^ ⌈-log ε / log (Fintype.card
 Fq)⌉₊).succ -> Fq[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.cast_pos`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_1 : 
PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R] [NeZero 1]   {n : ℤ}, 0 < ↑n 
↔ …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `AbsoluteValue.pos`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring R] [
inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) {x : 
R}, x ≠…
· 使用定理 `Fintype.one_lt_card`：one_lt_card [h : Nontrivial α] : 1 < Fintype.card α
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Polynomial.exists_eq_polynomial`：exists_eq_polynomial [Semiring Fq] {d :
 Nat} {m : Nat} (hm : Fintype.card Fq ^ d <= m) (b : Fq[X]) (hb : natDegree b <=
 d) (A : Fin m.succ -…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `EuclideanDomain.mod_lt`：mod_lt : forall (a) {b : R}, b != 0 -> a % b ≺ b
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `Polynomial.exists_approx_polynomial_aux`：exists_approx_polynomial_aux [R
ing Fq] {d : Nat} {m : Nat} (hm : Fintype.card Fq ^ d <= m) (b : Fq[X]) (A : Fin
 m.succ -> Fq[X]) (hA : foral…
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
（共 61 条，此处仅展示前 30 条）

--- 原说明 ---
If `A` is a family of enough low-degree polynomials over a finite field,
there is a pair of elements in `A` (with different indices but not necessarily
distinct), such that the difference of their remainders is close together.
-/
theorem exists_approx_polynomial {b : Fq[X]} (hb : b ≠ 0) {ε : ℝ} (hε : 0 < ε)
    (A : Fin (Fintype.card Fq ^ ⌈-log ε / log (Fintype.card Fq)⌉₊).succ → Fq[X]) :
    ∃ i₀ i₁, i₀ ≠ i₁ ∧ (cardPowDegree (A i₁ % b - A i₀ % b) : ℝ) < cardPowDegree b • ε := by
  have hbε : 0 < cardPowDegree b • ε := by
    rw [Algebra.smul_def, eq_intCast]
    exact mul_pos (Int.cast_pos.mpr (AbsoluteValue.pos _ hb)) hε
  have one_lt_q : 1 < Fintype.card Fq := Fintype.one_lt_card
  have one_lt_q' : (1 : ℝ) < Fintype.card Fq := by assumption_mod_cast
  have q_pos : 0 < Fintype.card Fq := by lia
  have q_pos' : (0 : ℝ) < Fintype.card Fq := by assumption_mod_cast
  -- If `b` is already small enough, then the remainders are equal and we are done.
  by_cases! le_b : b.natDegree ≤ ⌈-log ε / log (Fintype.card Fq)⌉₊
  · obtain ⟨i₀, i₁, i_ne, mod_eq⟩ :=
      exists_eq_polynomial le_rfl b le_b (fun i => A i % b) fun i => EuclideanDomain.mod_lt (A i) hb
    refine ⟨i₀, i₁, i_ne, ?_⟩
    rwa [mod_eq, sub_self, map_zero, Int.cast_zero]
  -- Otherwise, it suffices to choose two elements whose difference is of small enough degree.
  obtain ⟨i₀, i₁, i_ne, deg_lt⟩ := exists_approx_polynomial_aux le_rfl b (fun i => A i % b) fun i =>
    EuclideanDomain.mod_lt (A i) hb
  use i₀, i₁, i_ne
  -- Again, if the remainders are equal we are done.
  by_cases h : A i₁ % b = A i₀ % b
  · rwa [h, sub_self, map_zero, Int.cast_zero]
  have h' : A i₁ % b - A i₀ % b ≠ 0 := mt sub_eq_zero.mp h
  -- If the remainders are not equal, we'll show their difference is of small degree.
  -- In particular, we'll show the degree is less than the following:
  suffices (natDegree (A i₁ % b - A i₀ % b) : ℝ) < b.natDegree + log ε / log (Fintype.card Fq) by
    rwa [← Real.log_lt_log_iff (Int.cast_pos.mpr (cardPowDegree.pos h')) hbε,
      cardPowDegree_nonzero _ h', cardPowDegree_nonzero _ hb, Algebra.smul_def, eq_intCast,
      Int.cast_pow, Int.cast_natCast, Int.cast_pow, Int.cast_natCast,
      log_mul (pow_ne_zero _ q_pos'.ne') hε.ne', ← rpow_natCast, ← rpow_natCast, log_rpow q_pos',
      log_rpow q_pos', ← lt_div_iff₀ (log_pos one_lt_q'), add_div,
      mul_div_cancel_right₀ _ (log_pos one_lt_q').ne']
  -- And that result follows from manipulating the result from `exists_approx_polynomial_aux`
  -- to turn the `-⌈-stuff⌉₊` into `+ stuff`.
  apply lt_of_lt_of_le (Nat.cast_lt.mpr (WithBot.coe_lt_coe.mp _)) _
  swap
  · convert! deg_lt
    rw [degree_eq_natDegree h']; rfl
  rw [← sub_neg_eq_add, ← neg_div, Nat.cast_sub le_b.le]
  grw [← Nat.le_ceil]

/-- If `x` is close to `y` and `y` is close to `z`, then `x` and `z` are at least as close. -/
/-
**Polynomial.cardPowDegree_anti_archimedean** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：cardPowDegree_anti_archimedean {x y z : Fq[X]} {a : Int} (hxy : cardPowDeg
ree (x - y) < a) (hyz : cardPowDegree (y - z) < a) : cardPowDegree (x - z) < a
参数：hxy : cardPowDegree (x - y) < a；hyz : cardPowDegree (y - z) < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `AbsoluteValue.nonneg`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring R
] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) (x
 : R), 0 ≤…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `Polynomial.cardPowDegree_nonzero`：cardPowDegree_nonzero (p : Fq[X]) (hp 
: p != 0) : cardPowDegree p = (Fintype.card Fq : Int) ^ p.natDegree
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Fintype.one_lt_card`：one_lt_card [h : Nontrivial α] : 1 < Fintype.card α
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用引理 `pow_le_pow_right₀`：pow_le_pow_right₀ [ZeroLEOneClass M₀] [PosMulMono M₀]
 (ha : 1 <= a) (hmn : m <= n) : a ^ m <= a ^ n
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Polynomial.natDegree_le_iff_degree_le`：natDegree_le_iff_degree_le {n : N
at} : natDegree p <= n ↔ degree p <= n
· 使用定理 `le_max_iff`：le_max_iff : a <= max b c ↔ a <= b ∨ a <= c
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `sub_add_sub_cancel`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : G), a 
- b + (b - c) = a - c
· 使用定理 `Polynomial.degree_add_le`：degree_add_le (p q : R[X]) : degree (p + q) <=
 max (degree p) (degree q)
· 使用定理 `max_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, b < a → c <
 a → max b c < a

--- 原说明 ---
If `x` is close to `y` and `y` is close to `z`, then `x` and `z` are at least as
 close.
-/
theorem cardPowDegree_anti_archimedean {x y z : Fq[X]} {a : ℤ} (hxy : cardPowDegree (x - y) < a)
    (hyz : cardPowDegree (y - z) < a) : cardPowDegree (x - z) < a := by
  have ha : 0 < a := lt_of_le_of_lt (AbsoluteValue.nonneg _ _) hxy
  by_cases hxy' : x = y
  · rwa [hxy']
  by_cases hyz' : y = z
  · rwa [← hyz']
  by_cases hxz' : x = z
  · rwa [hxz', sub_self, map_zero]
  rw [← Ne, ← sub_ne_zero] at hxy' hyz' hxz'
  refine lt_of_le_of_lt ?_ (max_lt hxy hyz)
  rw [cardPowDegree_nonzero _ hxz', cardPowDegree_nonzero _ hxy',
    cardPowDegree_nonzero _ hyz']
  have : (1 : ℤ) ≤ Fintype.card Fq := mod_cast (@Fintype.one_lt_card Fq _ _).le
  simp only [le_max_iff]
  refine Or.imp (pow_le_pow_right₀ this) (pow_le_pow_right₀ this) ?_
  rw [natDegree_le_iff_degree_le, natDegree_le_iff_degree_le, ← le_max_iff, ←
    degree_eq_natDegree hxy', ← degree_eq_natDegree hyz']
  convert! degree_add_le (x - y) (y - z) using 2
  exact (sub_add_sub_cancel _ _ _).symm

/-- A slightly stronger version of `exists_partition` on which we perform induction on `n`:
for all `ε > 0`, we can partition the remainders of any family of polynomials `A`
into equivalence classes, where the equivalence(!) relation is "closer than `ε`". -/
/-
**Polynomial.exists_partition_polynomial_aux** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al`。
形式化陈述：exists_partition_polynomial_aux (n : Nat) {ε : Real} (hε : 0 < ε) {b : Fq[
X]} (hb : b != 0) (A : Fin n -> Fq[X]) : exists t : Fin n -> Fin (Fintype.card F
q ^ ⌈-log ε / log (Fintype.card Fq)⌉₊), forall i₀ i₁ : Fin n, t i₀ = t i₁ ↔ (car
dPowDegree (A i₁ % b - A i₀ % b) : Real) < cardPowDegree b • ε
参数：n : Nat；hε : 0 < ε；hb : b != 0；A : Fin n -> Fq[X]。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.cast_pos`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_1 : 
PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R] [NeZero 1]   {n : ℤ}, 0 < ↑n 
↔ …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `AbsoluteValue.pos`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring R] [
inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) {x : 
R}, x ≠…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Polynomial.cardPowDegree_anti_archimedean`：cardPowDegree_anti_archimedea
n {x y z : Fq[X]} {a : Int} (hxy : cardPowDegree (x - y) < a) (hyz : cardPowDegr
ee (y - z) < a) : cardPowDegree…
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.exists_approx_polynomial`：exists_approx_polynomial {b : Fq[X]
} (hb : b != 0) {ε : Real} (hε : 0 < ε) (A : Fin (Fintype.card Fq ^ ⌈-log ε / lo
g (Fintype.card Fq)⌉₊).su…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `AbsoluteValue.map_sub`：∀ {R : Type u_3} {S : Type u_4} [inst : CommRing 
S] [inst_1 : PartialOrder S] [IsOrderedRing S] [inst_3 : Ring R]   (abv : Absolu
teValue R S…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Fin.succ_inj`：∀ {n : ℕ} {a b : Fin n}, a.succ = b.succ ↔ a = b
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
A slightly stronger version of `exists_partition` on which we perform induction 
on `n`:
for all `ε > 0`, we can partition the remainders of any family of polynomials `A
`
into equivalence classes, where the equivalence(!) relation is "closer than `ε`"
.
-/
theorem exists_partition_polynomial_aux (n : ℕ) {ε : ℝ} (hε : 0 < ε) {b : Fq[X]} (hb : b ≠ 0)
    (A : Fin n → Fq[X]) : ∃ t : Fin n → Fin (Fintype.card Fq ^ ⌈-log ε / log (Fintype.card Fq)⌉₊),
      ∀ i₀ i₁ : Fin n, t i₀ = t i₁ ↔
        (cardPowDegree (A i₁ % b - A i₀ % b) : ℝ) < cardPowDegree b • ε := by
  have hbε : 0 < cardPowDegree b • ε := by
    rw [Algebra.smul_def, eq_intCast]
    exact mul_pos (Int.cast_pos.mpr (AbsoluteValue.pos _ hb)) hε
  -- We go by induction on the size `A`.
  induction n with | zero => refine ⟨finZeroElim, finZeroElim⟩ | succ n ih =>
  -- Show `anti_archimedean` also holds for real distances.
  have anti_archim' : ∀ {i j k} {ε : ℝ},
    (cardPowDegree (A i % b - A j % b) : ℝ) < ε →
      (cardPowDegree (A j % b - A k % b) : ℝ) < ε →
        (cardPowDegree (A i % b - A k % b) : ℝ) < ε := by
    intro i j k ε
    simp_rw [← Int.lt_ceil]
    exact cardPowDegree_anti_archimedean
  obtain ⟨t', ht'⟩ := ih (Fin.tail A)
  -- We got rid of `A 0`, so determine the index `j` of the partition we'll re-add it to.
  rsuffices ⟨j, hj⟩ :
    ∃ j, ∀ i, t' i = j ↔ (cardPowDegree (A 0 % b - A i.succ % b) : ℝ) < cardPowDegree b • ε
  · refine ⟨Fin.cons j t', fun i₀ i₁ => ?_⟩
    refine Fin.cases ?_ (fun i₀ => ?_) i₀ <;> refine Fin.cases ?_ (fun i₁ => ?_) i₁
    · simpa using hbε
    · rw [Fin.cons_succ, Fin.cons_zero, eq_comm, AbsoluteValue.map_sub]
      exact hj i₁
    · rw [Fin.cons_succ, Fin.cons_zero]
      exact hj i₀
    · rw [Fin.cons_succ, Fin.cons_succ]
      exact ht' i₀ i₁
  -- `exists_approx_polynomial` guarantees that we can insert `A 0` into some partition `j`,
  -- but not that `j` is uniquely defined (which is needed to keep the induction going).
  obtain ⟨j, hj⟩ : ∃ j, ∀ i : Fin n,
      t' i = j → (cardPowDegree (A 0 % b - A i.succ % b) : ℝ) < cardPowDegree b • ε := by
    by_contra! hg
    obtain ⟨j₀, j₁, j_ne, approx⟩ := exists_approx_polynomial hb hε
      (Fin.cons (A 0) fun j => A (Fin.succ (Classical.choose (hg j))))
    revert j_ne approx
    refine Fin.cases ?_ (fun j₀ => ?_) j₀ <;>
      refine Fin.cases (fun j_ne approx => ?_) (fun j₁ j_ne approx => ?_) j₁
    · exact absurd rfl j_ne
    · rw [Fin.cons_succ, Fin.cons_zero, ← not_le, AbsoluteValue.map_sub] at approx
      have := (Classical.choose_spec (hg j₁)).2
      contradiction
    · rw [Fin.cons_succ, Fin.cons_zero, ← not_le] at approx
      have := (Classical.choose_spec (hg j₀)).2
      contradiction
    · rw [Fin.cons_succ, Fin.cons_succ] at approx
      rw [Ne, Fin.succ_inj] at j_ne
      have : j₀ = j₁ := (Classical.choose_spec (hg j₀)).1.symm.trans
        (((ht' (Classical.choose (hg j₀)) (Classical.choose (hg j₁))).mpr approx).trans
          (Classical.choose_spec (hg j₁)).1)
      contradiction
  -- However, if one of those partitions `j` is inhabited by some `i`, then this `j` works.
  by_cases exists_nonempty_j : ∃ j, (∃ i, t' i = j) ∧
      ∀ i, t' i = j → (cardPowDegree (A 0 % b - A i.succ % b) : ℝ) < cardPowDegree b • ε
  · obtain ⟨j, ⟨i, hi⟩, hj⟩ := exists_nonempty_j
    refine ⟨j, fun i' => ⟨hj i', fun hi' => _root_.trans ((ht' _ _).mpr ?_) hi⟩⟩
    apply anti_archim' _ hi'
    rw [AbsoluteValue.map_sub]
    exact hj _ hi
  -- And otherwise, we can just take any `j`, since those are empty.
  refine ⟨j, fun i => ⟨hj i, fun hi => ?_⟩⟩
  have := exists_nonempty_j ⟨t' i, ⟨i, rfl⟩, fun i' hi' => anti_archim' hi ((ht' _ _).mp hi')⟩
  contradiction

/-- For all `ε > 0`, we can partition the remainders of any family of polynomials `A`
into classes, where all remainders in a class are close together. -/
/-
**Polynomial.exists_partition_polynomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：exists_partition_polynomial (n : Nat) {ε : Real} (hε : 0 < ε) {b : Fq[X]} 
(hb : b != 0) (A : Fin n -> Fq[X]) : exists t : Fin n -> Fin (Fintype.card Fq ^ 
⌈-log ε / log (Fintype.card Fq)⌉₊), forall i₀ i₁ : Fin n, t i₀ = t i₁ -> (cardPo
wDegree (A i₁ % b - A i₀ % b) : Real) < cardPowDegree b • ε
参数：n : Nat；hε : 0 < ε；hb : b != 0；A : Fin n -> Fq[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.exists_partition_polynomial_aux`：exists_partition_polynomial_
aux (n : Nat) {ε : Real} (hε : 0 < ε) {b : Fq[X]} (hb : b != 0) (A : Fin n -> Fq
[X]) : exists t : Fin n -> Fin (…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b

--- 原说明 ---
For all `ε > 0`, we can partition the remainders of any family of polynomials `A
`
into classes, where all remainders in a class are close together.
-/
theorem exists_partition_polynomial (n : ℕ) {ε : ℝ} (hε : 0 < ε) {b : Fq[X]} (hb : b ≠ 0)
    (A : Fin n → Fq[X]) : ∃ t : Fin n → Fin (Fintype.card Fq ^ ⌈-log ε / log (Fintype.card Fq)⌉₊),
      ∀ i₀ i₁ : Fin n, t i₀ = t i₁ →
        (cardPowDegree (A i₁ % b - A i₀ % b) : ℝ) < cardPowDegree b • ε := by
  obtain ⟨t, ht⟩ := exists_partition_polynomial_aux n hε hb A
  exact ⟨t, fun i₀ i₁ hi => (ht i₀ i₁).mp hi⟩

/-- `fun p => Fintype.card Fq ^ degree p` is an admissible absolute value.
We set `q ^ degree 0 = 0`. -/
/-
**Polynomial.cardPowDegreeIsAdmissible** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：cardPowDegreeIsAdmissible : IsAdmissible (cardPowDegree : AbsoluteValue Fq
[X] Int)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.cardPowDegree_isEuclidean`：cardPowDegree_isEuclidean : IsEucl
idean (cardPowDegree : AbsoluteValue Fq[X] Int)
· 使用定理 `Polynomial.exists_partition_polynomial`：exists_partition_polynomial (n :
 Nat) {ε : Real} (hε : 0 < ε) {b : Fq[X]} (hb : b != 0) (A : Fin n -> Fq[X]) : e
xists t : Fin n -> Fin (Fint…

--- 原说明 ---
`fun p => Fintype.card Fq ^ degree p` is an admissible absolute value.
We set `q ^ degree 0 = 0`.
-/
noncomputable def cardPowDegreeIsAdmissible :
    IsAdmissible (cardPowDegree : AbsoluteValue Fq[X] ℤ) :=
  { @cardPowDegree_isEuclidean Fq _
      _ with
    card := fun ε => Fintype.card Fq ^ ⌈-log ε / log (Fintype.card Fq)⌉₊
    exists_partition' := fun n _ hε _ hb => exists_partition_polynomial n hε hb }

end Polynomial

