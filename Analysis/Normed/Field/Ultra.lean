/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Ultra
public import Mathlib.Data.Nat.Choose.Sum

/-!
## Conditions to have an ultrametric norm on a division ring

This file provides ways of constructing an instance of `IsUltrametricDist` based on
facts about the existing norm.

## Main results

* `isUltrametricDist_of_forall_norm_natCast_le_one`: a norm in a division ring is ultrametric
  if the norm of the image of a natural is less than or equal to one

* `isUltrametricDist_iff_forall_norm_natCast_le_one`: a norm in a division ring is ultrametric
  if and only if the norm of the image of a natural is less than or equal to one

## Implementation details

The proof relies on a bounded-from-above argument. The main result has a longer proof
to be able to be applied in noncommutative division rings.

## Tags

ultrametric, nonarchimedean
-/

public section
open Metric NNReal

namespace IsUltrametricDist

section sufficient

variable {R : Type*} [NormedDivisionRing R]

/-
**IsUltrametricDist.isUltrametricDist_of_forall_norm_add_one_le_max_norm_one** 是
 Mathlib 中的一个引理，位于命名空间 `IsUltrametricDist`。
形式化陈述：isUltrametricDist_of_forall_norm_add_one_le_max_norm_one (h : forall x : R
, ‖x + 1‖ <= max ‖x‖ 1) : IsUltrametricDist R
参数：h : forall x : R, ‖x + 1‖ <= max ‖x‖ 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm`：∀ {S
' : Type u_2} [inst : SeminormedAddGroup S'], (∀ (x y : S'), ‖x + y‖ ≤ max ‖x‖ ‖
y‖) → IsUltrametricDist S'
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `div_add_one`：div_add_one (h : b != 0) : a / b + 1 = (a + b) / b
· 使用定理 `norm_div`：norm_div (a b : α) : ‖a / b‖ = ‖a‖ / ‖b‖
· 使用引理 `div_le_iff₀`：div_le_iff₀ (hc : 0 < c) : b / c <= a ↔ b <= a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `max_mul_of_nonneg`：max_mul_of_nonneg [MulPosMono R] (a b : R) (hc : 0 <=
 c) : max a b * c = max (a * c) (b * c)
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma isUltrametricDist_of_forall_norm_add_one_le_max_norm_one
    (h : ∀ x : R, ‖x + 1‖ ≤ max ‖x‖ 1) : IsUltrametricDist R := by
  refine isUltrametricDist_of_forall_norm_add_le_max_norm (fun x y ↦ ?_)
  rcases eq_or_ne y 0 with rfl | hy
  · simpa only [add_zero] using le_max_left _ _
  · have p : 0 < ‖y‖ := norm_pos_iff.mpr hy
    simpa only [div_add_one hy, norm_div, div_le_iff₀ p, max_mul_of_nonneg _ _ p.le, one_mul,
      div_mul_cancel₀ _ p.ne'] using h (x / y)
/-
**IsUltrametricDist.isUltrametricDist_of_forall_norm_add_one_of_norm_le_one** 是 
Mathlib 中的一个引理，位于命名空间 `IsUltrametricDist`。
形式化陈述：isUltrametricDist_of_forall_norm_add_one_of_norm_le_one (h : forall x : R,
 ‖x‖ <= 1 -> ‖x + 1‖ <= 1) : IsUltrametricDist R
参数：h : forall x : R, ‖x‖ <= 1 -> ‖x + 1‖ <= 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUltrametricDist.isUltrametricDist_of_forall_norm_add_one_le_max_norm_o
ne`：isUltrametricDist_of_forall_norm_add_one_le_max_norm_one (h : forall x : R, 
‖x + 1‖ <= max ‖x‖ 1) : IsUltrametricDist R
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_le_one`：div_le_one (hb : 0 < b) : a / b <= 1 ↔ a <= b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `norm_div`：norm_div (a b : α) : ‖a / b‖ = ‖a‖ / ‖b‖
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `LT.lt.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b < a → 
c < b → c < a
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
（共 31 条，此处仅展示前 30 条）
-/
lemma isUltrametricDist_of_forall_norm_add_one_of_norm_le_one
    (h : ∀ x : R, ‖x‖ ≤ 1 → ‖x + 1‖ ≤ 1) : IsUltrametricDist R := by
  refine isUltrametricDist_of_forall_norm_add_one_le_max_norm_one fun x ↦ ?_
  rcases le_or_gt ‖x‖ 1 with H | H
  · exact (h _ H).trans (le_max_right _ _)
  · suffices ‖x + 1‖ ≤ ‖x‖ from this.trans (le_max_left _ _)
    rw [← div_le_one (by positivity), ← norm_div, add_div,
      div_self (by simpa using H.trans' zero_lt_one), add_comm]
    apply h
    simp [inv_le_one_iff₀, H.le]
/-
**IsUltrametricDist.isUltrametricDist_of_forall_norm_sub_one_of_norm_le_one** 是 
Mathlib 中的一个引理，位于命名空间 `IsUltrametricDist`。
形式化陈述：isUltrametricDist_of_forall_norm_sub_one_of_norm_le_one (h : forall x : R,
 ‖x‖ <= 1 -> ‖x - 1‖ <= 1) : IsUltrametricDist R
参数：h : forall x : R, ‖x‖ <= 1 -> ‖x - 1‖ <= 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsUltrametricDist.isUltrametricDist_of_forall_norm_add_one_of_norm_le_on
e`：isUltrametricDist_of_forall_norm_add_one_of_norm_le_one (h : forall x : R, ‖x
‖ <= 1 -> ‖x + 1‖ <= 1) : IsUltrametricDist R
-/
lemma isUltrametricDist_of_forall_norm_sub_one_of_norm_le_one
    (h : ∀ x : R, ‖x‖ ≤ 1 → ‖x - 1‖ ≤ 1) : IsUltrametricDist R := by
  have (x : R) (hx : ‖x‖ ≤ 1) : ‖x + 1‖ ≤ 1 := by
    simpa only [← neg_add', norm_neg] using h (-x) (norm_neg x ▸ hx)
  exact isUltrametricDist_of_forall_norm_add_one_of_norm_le_one this

/-- This technical lemma is used in the proof of
`isUltrametricDist_of_forall_norm_natCast_le_one`. -/
/-
**IsUltrametricDist.isUltrametricDist_of_forall_pow_norm_le_nsmul_pow_max_one_no
rm** 是 Mathlib 中的一个引理，位于命名空间 `IsUltrametricDist`。
形式化陈述：isUltrametricDist_of_forall_pow_norm_le_nsmul_pow_max_one_norm (h : forall
 (x : R) (m : Nat), ‖x + 1‖ ^ m <= (m + 1) • max 1 (‖x‖ ^ m)) : IsUltrametricDis
t R
参数：h : forall (x : R) (m : Nat), ‖x + 1‖ ^ m <= (m + 1) • max 1 (‖x‖ ^ m)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUltrametricDist.isUltrametricDist_of_forall_norm_add_one_le_max_norm_o
ne`：isUltrametricDist_of_forall_norm_add_one_le_max_norm_one (h : forall x : R, 
‖x + 1‖ <= max ‖x‖ 1) : IsUltrametricDist R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `max_comm`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), max a b = m
ax b a
· 使用定理 `le_of_forall_gt_imp_ge_of_dense`：le_of_forall_gt_imp_ge_of_dense (h : fo
rall a, a₂ < a -> a₁ <= a) : a₁ <= a₂
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `max_lt_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, max b c <
 a ↔ b < a ∧ c < a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Real.exists_natCast_add_one_lt_pow_of_one_lt`：exists_natCast_add_one_lt_
pow_of_one_lt (ha : 1 < a) : exists m : Nat, (m + 1 : Real) < a ^ m
· 使用定理 `one_lt_div`：one_lt_div (hb : 0 < b) : 1 < a / b ↔ b < a
· 使用定理 `lt_max_of_lt_left`：lt_max_of_lt_left (h : a < b) : a < max b c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `MonotoneOn.map_max`：MonotoneOn.map_max (hf : MonotoneOn f s) (ha : a in 
s) (hb : b in s) : f (max a b) = max (f a) (f b)
· 使用引理 `pow_left_monotoneOn`：pow_left_monotoneOn [PosMulMono M₀] [MulPosMono M₀]
 : MonotoneOn (fun a : M₀ => a ^ n) {x | 0 <= x}
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用引理 `le_of_pow_le_pow_left₀`：le_of_pow_le_pow_left₀ (hn : n != 0) (hb : 0 <= 
b) (h : a ^ n <= b ^ n) : a <= b
（共 48 条，此处仅展示前 30 条）

--- 原说明 ---
This technical lemma is used in the proof of
`isUltrametricDist_of_forall_norm_natCast_le_one`.
-/
lemma isUltrametricDist_of_forall_pow_norm_le_nsmul_pow_max_one_norm
    (h : ∀ (x : R) (m : ℕ), ‖x + 1‖ ^ m ≤ (m + 1) • max 1 (‖x‖ ^ m)) :
    IsUltrametricDist R := by
  -- it will suffice to prove that `‖x + 1‖ ≤ max 1 ‖x‖`
  refine isUltrametricDist_of_forall_norm_add_one_le_max_norm_one fun x ↦ ?_
  -- Morally, we want to deduce this from the hypothesis `h` by taking an `m`-th root and showing
  -- that `(m + 1) ^ (1 / m)` gets arbitrarily close to 1, although we will formalise this in a way
  -- that avoids explicitly mentioning `m`-th roots.
  -- First note it suffices to show that `‖x + 1‖ ≤ a` for all `a : ℝ` with `max ‖x‖ 1 < a`.
  rw [max_comm]
  refine le_of_forall_gt_imp_ge_of_dense fun a ha ↦ ?_
  have ha' : 1 < a := (max_lt_iff.mp ha).left
  -- `max 1 ‖x‖ < a`, so there must be some `m : ℕ` such that `m + 1 < (a / max 1 ‖x‖) ^ m`
  -- by the virtue of exponential growth being faster than linear growth
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ((m + 1) : ℕ) < (a / (max 1 ‖x‖)) ^ m := by
    apply_mod_cast Real.exists_natCast_add_one_lt_pow_of_one_lt
    rwa [one_lt_div (by positivity)]
  -- and we rearrange again to get `(m + 1) • max 1 ‖x‖ ^ m < a ^ m`
  rw [div_pow, lt_div_iff₀ (by positivity), ← nsmul_eq_mul] at hm
  -- which squeezes down to get our `‖x + 1‖ ≤ a` using our to-be-proven hypothesis of
  -- `‖x + 1‖ ^ m ≤ (m + 1) • max 1 ‖x‖ ^ m`, so we're done
  -- we can distribute powers into the right term of `max`
  have hp : max 1 ‖x‖ ^ m = max 1 (‖x‖ ^ m) := by
    rw [pow_left_monotoneOn.map_max (by simp [zero_le_one]) (norm_nonneg x), one_pow]
  rw [hp] at hm
  refine le_of_pow_le_pow_left₀ (fun h ↦ ?_) (zero_lt_one.trans ha').le ((h _ _).trans hm.le)
  simp only [h, zero_add, pow_zero, max_self, one_smul, lt_self_iff_false] at hm

/-- To prove that a normed division ring is nonarchimedean, it suffices to prove that the norm
of the image of any natural is less than or equal to one. -/
/-
**IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one** 是 Mathlib 
中的一个引理，位于命名空间 `IsUltrametricDist`。
形式化陈述：isUltrametricDist_of_forall_norm_natCast_le_one (h : forall n : Nat, ‖(n :
 R)‖ <= 1) : IsUltrametricDist R
参数：h : forall n : Nat, ‖(n : R)‖ <= 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUltrametricDist.isUltrametricDist_of_forall_pow_norm_le_nsmul_pow_max_
one_norm`：isUltrametricDist_of_forall_pow_norm_le_nsmul_pow_max_one_norm (h : fo
rall (x : R) (m : Nat), ‖x + 1‖ ^ m <= (m + 1) • max 1 (‖x‖ ^ m)) : Is…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `mul_le_iff_le_one_left`：mul_le_iff_le_one_left [MulPosMono α] [MulPosRef
lectLE α] (b0 : 0 < b) : a * b <= b ↔ a <= 1
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Commute.add_pow`：add_pow (h : Commute x y) (n : Nat) : (x + y) ^ n = ∑ m
 in range (n + 1), x ^ m * y ^ (n - m) * n.choose m
· 使用定理 `Commute.one_right`：one_right (a : M) : Commute a 1
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Nat.cast_comm`：cast_comm (n : Nat) (x : α) : (n : α) * x = x * n
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_sum_le`：norm_sum_le {E} [SeminormedAddCommGroup E] (s : Finset ι) (
f : ι -> E) : ‖∑ i in s, f i‖ <= ∑ i in s, ‖f i‖
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
To prove that a normed division ring is nonarchimedean, it suffices to prove tha
t the norm
of the image of any natural is less than or equal to one.
-/
lemma isUltrametricDist_of_forall_norm_natCast_le_one
    (h : ∀ n : ℕ, ‖(n : R)‖ ≤ 1) : IsUltrametricDist R := by
  -- from a previous lemma, suffices to prove that for all `m`, we have
  -- `‖x + 1‖ ^ m ≤ (m + 1) • max 1 ‖x‖ ^ m`
  refine isUltrametricDist_of_forall_pow_norm_le_nsmul_pow_max_one_norm (fun x m ↦ ?_)
  -- we first use our hypothesis about the norm of naturals to have that multiplication by
  -- naturals keeps the norm small
  replace h (x : R) (n : ℕ) : ‖n • x‖ ≤ ‖x‖ := by
    rw [nsmul_eq_mul, norm_mul]
    rcases (norm_nonneg x).eq_or_lt with hx | hx
    · simp only [← hx, mul_zero, le_refl]
    · simpa only [mul_le_iff_le_one_left hx] using h _
  -- we expand the LHS using the binomial theorem, and apply the hypothesis to bound each term by
  -- a power of ‖x‖
  transitivity ∑ k ∈ Finset.range (m + 1), ‖x‖ ^ k
  · simpa only [← norm_pow, (Commute.one_right x).add_pow, one_pow, mul_one, nsmul_eq_mul,
      Nat.cast_comm] using (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ ↦ h _ _)
  -- the nature of the norm means that one of `1` and `‖x‖ ^ m` is the largest of the two, so the
  -- other terms in the binomial expansion are bounded by the max of these, and the number of terms
  -- in the sum is precisely `m + 1`
  rw [← Finset.card_range (m + 1), ← Finset.sum_const, Finset.card_range]
  rcases max_cases 1 (‖x‖ ^ m) with (⟨hm, hx⟩ | ⟨hm, hx⟩) <;> rw [hm] <;>
  -- which we show by comparing the terms in the sum one by one
  gcongr with i hi
  · rcases eq_or_ne m 0 with rfl | hm
    · simp only [pow_zero, le_refl,
        show i = 0 by simpa only [zero_add, Finset.range_one, Finset.mem_singleton] using hi]
    · rw [pow_le_one_iff_of_nonneg (norm_nonneg _) hm] at hx
      exact pow_le_one₀ (norm_nonneg _) hx
  · contrapose! hx
    exact pow_le_one₀ (norm_nonneg _) hx.le
  · simpa [Nat.lt_succ_iff] using hi

end sufficient

end IsUltrametricDist

/-
**isUltrametricDist_iff_forall_norm_natCast_le_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isUltrametricDist_iff_forall_norm_natCast_le_one {R : Type*} [NormedDivisi
onRing R] : IsUltrametricDist R ↔ forall n : Nat, ‖(n : R)‖ <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUltrametricDist.norm_natCast_le_one`：norm_natCast_le_one (n : Nat) : ‖
(n : R)‖ <= 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用引理 `IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one`：isUlt
rametricDist_of_forall_norm_natCast_le_one (h : forall n : Nat, ‖(n : R)‖ <= 1) 
: IsUltrametricDist R
-/
theorem isUltrametricDist_iff_forall_norm_natCast_le_one {R : Type*}
    [NormedDivisionRing R] : IsUltrametricDist R ↔ ∀ n : ℕ, ‖(n : R)‖ ≤ 1 :=
  ⟨fun _ => IsUltrametricDist.norm_natCast_le_one R,
      IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one⟩
