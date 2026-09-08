/-
Copyright (c) 2024 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero, Laura Capuano, Amos Turchet
-/
module

public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Data.Pi.Interval
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Qify

/-!
# Siegel's Lemma

In this file we introduce and prove Siegel's Lemma in its most basic version. This is a fundamental
tool in diophantine approximation and transcendence and says that there exists a "small" integral
non-zero solution of a non-trivial underdetermined system of linear equations with integer
coefficients.

## Main results

- `exists_ne_zero_int_vec_norm_le`: Given a non-zero `m × n` matrix `A` with `m < n` the linear
  system it determines has a non-zero integer solution `t` with
  `‖t‖ ≤ ((n * ‖A‖) ^ ((m : ℝ) / (n - m)))`

## Notation

- `‖_‖ ` : Matrix.seminormedAddCommGroup is the sup norm, the maximum of the absolute values of
  the entries of the matrix

## References

See [M. Hindry and J. Silverman, Diophantine Geometry: an Introduction][hindrysilverman00].
-/

public section

/- We set ‖⬝‖ to be Matrix.seminormedAddCommGroup  -/
attribute [local instance] Matrix.seminormedAddCommGroup

open Matrix Finset

namespace Int.Matrix

variable {α β : Type*} [Fintype α] [Fintype β] (A : Matrix α β ℤ)

-- Some definitions and relative properties

local notation3 "m" => Fintype.card α
local notation3 "n" => Fintype.card β
local notation3 "e" => m / ((n : ℝ) - m) -- exponent
local notation3 "B" => Nat.floor (((n : ℝ) * max 1 ‖A‖) ^ e)
-- B' is the vector with all components = B
local notation3 "B'" => fun _ : β => (B : ℤ)
-- T is the box [0 B]^n
local notation3 "T" => Finset.Icc 0 B'
local notation3 "P" => fun i : α => ∑ j : β, B * posPart (A i j)
local notation3 "N" => fun i : α => ∑ j : β, B * (-negPart (A i j))
-- S is the box where the image of T goes
local notation3 "S" => Finset.Icc N P

section preparation

/- In order to apply Pigeonhole we need:
# Step 1: ∀ v ∈  T, A *ᵥ v ∈  S
and
# Step 2: #S < #T
Pigeonhole will give different x and y in T with A.mulVec x = A.mulVec y in S
Their difference is the solution we are looking for
-/

-- # Step 1: ∀ v ∈ T, A *ᵥ v ∈  S

/-
**Int.Matrix.image_T_subset_S** 是 Mathlib 中的一个引理，位于命名空间 `Int.Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma image_T_subset_S [DecidableEq α] [DecidableEq β] (v) (hv : v ∈ T) : A *ᵥ v ∈ S := by
  rw [mem_Icc] at hv ⊢
  have mulVec_def : A.mulVec v =
      fun i ↦ Finset.sum univ fun j : β ↦ A i j * v j := rfl
  rw [mulVec_def]
  refine ⟨fun i ↦ ?_, fun i ↦ ?_⟩
  all_goals
    simp only [mul_neg]
    gcongr ∑ _ : β, ?_ with j _ -- Get rid of sums
    rw [← mul_comm (v j)] -- Move A i j to the right of the products
    -- We have to distinguish cases: we have now 4 goals
    rcases le_total 0 (A i j) with hsign | hsign
  · rw [negPart_eq_zero.2 hsign]
    exact mul_nonneg (hv.1 j) hsign
  · rw [negPart_eq_neg.2 hsign]
    simp only [mul_neg, neg_neg]
    exact mul_le_mul_of_nonpos_right (hv.2 j) hsign
  · rw [posPart_eq_self.2 hsign]
    gcongr
    apply hv.2
  · rw [posPart_eq_zero.2 hsign]
    exact mul_nonpos_of_nonneg_of_nonpos (hv.1 j) hsign

-- # Preparation for Step 2
/-
**Int.Matrix.card_T_eq** 是 Mathlib 中的一个引理，位于命名空间 `Int.Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma card_T_eq [DecidableEq β] : #T = (B + 1) ^ n := by
  rw [Pi.card_Icc 0 B']
  simp only [Pi.zero_apply, card_Icc, sub_zero, toNat_natCast_add_one, prod_const, card_univ]

-- This lemma is necessary to be able to apply the formula #(Icc a b) = b + 1 - a
/-
**Int.Matrix.N_le_P_add_one** 是 Mathlib 中的一个引理，位于命名空间 `Int.Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma N_le_P_add_one (i : α) : N i ≤ P i + 1 := by
  calc N i
  _ ≤ 0 := by
    apply Finset.sum_nonpos
    intro j _
    simp only [mul_neg, Left.neg_nonpos_iff]
    positivity
  _ ≤ P i + 1 := by
    apply le_trans (Finset.sum_nonneg _) (Int.le_add_one (le_refl P i))
    intro j _
    positivity
/-
**Int.Matrix.card_S_eq** 是 Mathlib 中的一个引理，位于命名空间 `Int.Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma card_S_eq [DecidableEq α] : #(Finset.Icc N P) = ∏ i : α, (P i - N i + 1) := by
  rw [Pi.card_Icc N P, Nat.cast_prod]
  congr
  ext i
  rw [Int.card_Icc_of_le (N i) (P i) (N_le_P_add_one A i)]
  exact add_sub_right_comm (P i) 1 (N i)

/-- The sup norm of a non-zero integer matrix is at least one -/
/-
**Int.Matrix.one_le_norm_A_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Int.Matrix`。
形式化陈述：one_le_norm_A_of_ne_zero (hA : A != 0) : 1 <= ‖A‖
参数：hA : A != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Int.abs_lt_one_iff`：abs_lt_one_iff {a : Int} : |a| < 1 ↔ a = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Int.norm_eq_abs`：norm_eq_abs (n : Int) : ‖n‖ = |(n : Real)|
· 使用定理 `Matrix.norm_lt_iff`：norm_lt_iff {r : Real} (hr : 0 < r) {A : Matrix m n 
α} : ‖A‖ < r ↔ forall i j, ‖A i j‖ < r
· 使用定理 `Real.zero_lt_one`：0 < 1

--- 原说明 ---
The sup norm of a non-zero integer matrix is at least one
-/
lemma one_le_norm_A_of_ne_zero (hA : A ≠ 0) : 1 ≤ ‖A‖ := by
  by_contra! h
  apply hA
  ext i j
  simp only [Matrix.zero_apply]
  rw [norm_lt_iff Real.zero_lt_one] at h
  specialize h i j
  rw [Int.norm_eq_abs] at h
  norm_cast at h
  exact Int.abs_lt_one_iff.1 h

-- # Step 2: #S < #T

open Real Nat
/-
**Int.Matrix.card_S_lt_card_T** 是 Mathlib 中的一个引理，位于命名空间 `Int.Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma card_S_lt_card_T [DecidableEq α] [DecidableEq β]
    (hn : Fintype.card α < Fintype.card β) (hm : 0 < Fintype.card α) :
    #S < #T := by
  zify -- This is necessary to use card_S_eq
  rw [card_T_eq A, card_S_eq]
  rify -- This is necessary because ‖A‖ is a real number
  calc
  ∏ x : α, (∑ x_1 : β, ↑B * ↑(A x x_1)⁺ - ∑ x_1 : β, ↑B * -↑(A x x_1)⁻ + 1)
    ≤ ∏ x : α, (n * max 1 ‖A‖ * B + 1) := by
      refine Finset.prod_le_prod (fun i _ ↦ ?_) (fun i _ ↦ ?_)
      · have h := N_le_P_add_one A i
        rify at h
        linarith only [h]
      · simp only [mul_neg, sum_neg_distrib, sub_neg_eq_add, add_le_add_iff_right]
        have h1 : n * max 1 ‖A‖ * B = ∑ _ : β, max 1 ‖A‖ * B := by
          simp
          ring
        simp_rw [h1, ← Finset.sum_add_distrib, ← mul_add, mul_comm (max 1 ‖A‖), ← Int.cast_add]
        gcongr with j _
        rw [posPart_add_negPart (A i j), Int.cast_abs]
        exact le_trans (norm_entry_le_entrywise_sup_norm A) (le_max_right ..)
  _ = (n * max 1 ‖A‖ * B + 1) ^ m := by simp
  _ ≤ (n * max 1 ‖A‖) ^ m * (B + 1) ^ m := by
        rw [← mul_pow, mul_add, mul_one]
        gcongr
        have H : 1 ≤ (n : ℝ) := mod_cast (hm.trans hn)
        exact one_le_mul_of_one_le_of_one_le H <| le_max_left ..
  _ = ((n * max 1 ‖A‖) ^ (m / ((n : ℝ) - m))) ^ ((n : ℝ) - m) * (B + 1) ^ m := by
        congr 1
        rw [← rpow_mul (mul_nonneg (Nat.cast_nonneg' n) (le_trans zero_le_one (le_max_left ..))),
          ← Real.rpow_natCast, div_mul_cancel₀]
        exact sub_ne_zero_of_ne (mod_cast hn.ne')
  _ < (B + 1) ^ ((n : ℝ) - m) * (B + 1) ^ m := by
        gcongr
        · exact sub_pos.mpr (mod_cast hn)
        · exact Nat.lt_floor_add_one ((n * max 1 ‖A‖) ^ e)
  _ = (B + 1) ^ n := by
        rw [← rpow_natCast, ← rpow_add (Nat.cast_add_one_pos B), ← rpow_natCast, sub_add_cancel]

end preparation

/-
**Int.Matrix.exists_ne_zero_int_vec_norm_le** 是 Mathlib 中的一个定理，位于命名空间 `Int.Matri
x`。
形式化陈述：exists_ne_zero_int_vec_norm_le (hn : Fintype.card α < Fintype.card β) (hm 
: 0 < Fintype.card α) : exists t : β -> Int, t != 0 ∧ A *ᵥ t = 0 ∧ ‖t‖ <= (n * m
ax 1 ‖A‖) ^ ((m : Real) / (n - m))
参数：hn : Fintype.card α < Fintype.card β；hm : 0 < Fintype.card α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.exists_ne_map_eq_of_card_lt_of_maps_to`：exists_ne_map_eq_of_card_
lt_of_maps_to (hc : #t < #s) {f : α -> β} (hf : Set.MapsTo f s t) : exists x in 
s, exists y in s, x != y ∧ f x = f …
· 使用定理 `_private.Mathlib.NumberTheory.SiegelsLemma.0.Int.Matrix.card_S_lt_card_T
`：∀ {α : Type u_1} {β : Type u_2} [inst : Fintype α] [inst_1 : Fintype β] (A : M
atrix α β ℤ) [inst_2 : DecidableEq α]   [inst_3 : DecidableEq …
· 使用定理 `_private.Mathlib.NumberTheory.SiegelsLemma.0.Int.Matrix.image_T_subset_S
`：∀ {α : Type u_1} {β : Type u_2} [inst : Fintype α] [inst_1 : Fintype β] (A : M
atrix α β ℤ) [inst_2 : DecidableEq α]   [inst_3 : DecidableEq …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.mulVec_sub`：mulVec_sub [Fintype n] (A : Matrix m n α) (x y : n ->
 α) : A *ᵥ (x - y) = A *ᵥ x - A *ᵥ y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `lt_max_of_lt_left`：lt_max_of_lt_left (h : a < b) : a < max b c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.norm_replicateCol`：norm_replicateCol (v : m -> α) : ‖replicateCol
 ι v‖ = ‖v‖
· 使用定理 `Matrix.norm_le_iff`：norm_le_iff {r : Real} (hr : 0 <= r) {A : Matrix m n
 α} : ‖A‖ <= r ↔ forall i j, ‖A i j‖ <= r
· 使用定理 `Int.norm_eq_abs`：norm_eq_abs (n : Int) : ‖n‖ = |(n : Real)|
· 使用引理 `Int.cast_abs`：cast_abs : (↑|a| : R) = |(a : R)|
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 48 条，此处仅展示前 30 条）
-/
theorem exists_ne_zero_int_vec_norm_le
    (hn : Fintype.card α < Fintype.card β) (hm : 0 < Fintype.card α) : ∃ t : β → ℤ, t ≠ 0 ∧
    A *ᵥ t = 0 ∧ ‖t‖ ≤ (n * max 1 ‖A‖) ^ ((m : ℝ) / (n - m)) := by
  classical
  -- Pigeonhole
  rcases Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (card_S_lt_card_T A hn hm) (image_T_subset_S A)
    with ⟨x, hxT, y, hyT, hneq, hfeq⟩
  -- Proofs that x - y ≠ 0 and x - y is a solution
  refine ⟨x - y, sub_ne_zero.mpr hneq, by simp only [mulVec_sub, sub_eq_zero, hfeq], ?_⟩
  -- Inequality
  have n_mul_norm_A_pow_e_nonneg : 0 ≤ (n * max 1 ‖A‖) ^ e := by positivity
  rw [← norm_replicateCol (ι := Unit), norm_le_iff n_mul_norm_A_pow_e_nonneg]
  intro i j
  simp only [replicateCol_apply, Pi.sub_apply]
  rw [Int.norm_eq_abs, ← Int.cast_abs]
  refine le_trans ?_ (Nat.floor_le n_mul_norm_A_pow_e_nonneg)
  norm_cast
  rw [abs_le]
  rw [Finset.mem_Icc] at hxT hyT
  constructor
  · simp only [neg_le_sub_iff_le_add]
    apply le_trans (hyT.2 i)
    norm_cast
    simp only [le_add_iff_nonneg_left]
    exact hxT.1 i
  · simp only [tsub_le_iff_right]
    apply le_trans (hxT.2 i)
    norm_cast
    simp only [le_add_iff_nonneg_right]
    exact hyT.1 i
/-
**Int.Matrix.exists_ne_zero_int_vec_norm_le'** 是 Mathlib 中的一个定理，位于命名空间 `Int.Matr
ix`。
形式化陈述：exists_ne_zero_int_vec_norm_le' (hn : Fintype.card α < Fintype.card β) (hm
 : 0 < Fintype.card α) (hA : A != 0) : exists t : β -> Int, t != 0 ∧ A *ᵥ t = 0 
∧ ‖t‖ <= (n * ‖A‖) ^ ((m : Real) / (n - m))
参数：hn : Fintype.card α < Fintype.card β；hm : 0 < Fintype.card α；hA : A != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.Matrix.exists_ne_zero_int_vec_norm_le`：exists_ne_zero_int_vec_norm_l
e (hn : Fintype.card α < Fintype.card β) (hm : 0 < Fintype.card α) : exists t : 
β -> Int, t != 0 ∧ A *ᵥ t = 0 ∧…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用引理 `Int.Matrix.one_le_norm_A_of_ne_zero`：one_le_norm_A_of_ne_zero (hA : A !=
 0) : 1 <= ‖A‖
-/
theorem exists_ne_zero_int_vec_norm_le'
    (hn : Fintype.card α < Fintype.card β) (hm : 0 < Fintype.card α) (hA : A ≠ 0) :
    ∃ t : β → ℤ, t ≠ 0 ∧
    A *ᵥ t = 0 ∧ ‖t‖ ≤ (n * ‖A‖) ^ ((m : ℝ) / (n - m)) := by
  have := exists_ne_zero_int_vec_norm_le A hn hm
  rwa [max_eq_right] at this
  exact Int.Matrix.one_le_norm_A_of_ne_zero _ hA

end Int.Matrix

