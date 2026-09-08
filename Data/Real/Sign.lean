/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Eric Wieser
-/
module

public import Mathlib.Data.Real.Basic

/-!
# Real sign function

This file introduces and contains some results about `Real.sign` which maps negative
real numbers to -1, positive real numbers to 1, and 0 to 0.

## Main definitions

* `Real.sign r` is $\begin{cases} -1 & \text{if } r < 0, \\
                              ~~\, 0 & \text{if } r = 0, \\
                              ~~\, 1 & \text{if } r > 0. \end{cases}$

## Tags

sign function
-/

@[expose] public section


namespace Real

/-- The sign function that maps negative real numbers to -1, positive numbers to 1, and 0
otherwise. -/
/-
**Real.sign** 是 Mathlib 中的一个定义，位于命名空间 `Real`。
形式化陈述：sign (r : Real) : Real
参数：r : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sign function that maps negative real numbers to -1, positive numbers to 1, 
and 0
otherwise.
-/
noncomputable def sign (r : ℝ) : ℝ :=
  if r < 0 then -1 else if 0 < r then 1 else 0
/-
**Real.sign_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sign_of_neg {r : Real} (hr : r < 0) : sign r = -1
参数：hr : r < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sign.eq_1`：∀ (r : ℝ), r.sign = if r < 0 then -1 else if 0 < r then 
1 else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem sign_of_neg {r : ℝ} (hr : r < 0) : sign r = -1 := by rw [sign, if_pos hr]
/-
**Real.sign_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sign_of_pos {r : Real} (hr : 0 < r) : sign r = 1
参数：hr : 0 < r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sign.eq_1`：∀ (r : ℝ), r.sign = if r < 0 then -1 else if 0 < r then 
1 else 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `LT.lt.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
-/
theorem sign_of_pos {r : ℝ} (hr : 0 < r) : sign r = 1 := by rw [sign, if_pos hr, if_neg hr.not_gt]

@[simp]
/-
**Real.sign_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sign_zero : sign 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sign.eq_1`：∀ (r : ℝ), r.sign = if r < 0 then -1 else if 0 < r then 
1 else 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
-/
theorem sign_zero : sign 0 = 0 := by rw [sign, if_neg (lt_irrefl _), if_neg (lt_irrefl _)]

@[simp]
/-
**Real.sign_one** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sign_one : sign 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.sign_of_pos`：sign_of_pos {r : Real} (hr : 0 < r) : sign r = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
-/
theorem sign_one : sign 1 = 1 :=
  sign_of_pos <| by simp
/-
**Real.sign_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sign_apply_eq (r : Real) : sign r = -1 ∨ sign r = 0 ∨ sign r = 1
参数：r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `Real.sign_of_neg`：sign_of_neg {r : Real} (hr : r < 0) : sign r = -1
· 使用定理 `Real.sign_zero`：sign_zero : sign 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.sign_of_pos`：sign_of_pos {r : Real} (hr : 0 < r) : sign r = 1
-/
theorem sign_apply_eq (r : ℝ) : sign r = -1 ∨ sign r = 0 ∨ sign r = 1 := by
  obtain hn | rfl | hp := lt_trichotomy r (0 : ℝ)
  · exact Or.inl <| sign_of_neg hn
  · exact Or.inr <| Or.inl <| sign_zero
  · exact Or.inr <| Or.inr <| sign_of_pos hp

/-- This lemma is useful for working with `ℝˣ` -/
/-
**Real.sign_apply_eq_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sign_apply_eq_of_ne_zero (r : Real) (h : r != 0) : sign r = -1 ∨ sign r = 
1
参数：r : Real；h : r != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Real.sign_of_neg`：sign_of_neg {r : Real} (hr : r < 0) : sign r = -1
· 使用定理 `Real.sign_of_pos`：sign_of_pos {r : Real} (hr : 0 < r) : sign r = 1
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a

--- 原说明 ---
This lemma is useful for working with `ℝˣ`
-/
theorem sign_apply_eq_of_ne_zero (r : ℝ) (h : r ≠ 0) : sign r = -1 ∨ sign r = 1 :=
  h.lt_or_gt.imp sign_of_neg sign_of_pos

@[simp]
/-
**Real.sign_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sign_eq_zero_iff {r : Real} : sign r = 0 ↔ r = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `Real.sign_of_neg`：sign_of_neg {r : Real} (hr : r < 0) : sign r = -1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.sign_of_pos`：sign_of_pos {r : Real} (hr : 0 < r) : sign r = 1
· 使用定理 `Real.sign_zero`：sign_zero : sign 0 = 0
-/
theorem sign_eq_zero_iff {r : ℝ} : sign r = 0 ↔ r = 0 := by
  refine ⟨fun h => ?_, fun h => h.symm ▸ sign_zero⟩
  obtain hn | rfl | hp := lt_trichotomy r (0 : ℝ)
  · rw [sign_of_neg hn, neg_eq_zero] at h
    exact (one_ne_zero h).elim
  · rfl
  · rw [sign_of_pos hp] at h
    exact (one_ne_zero h).elim
/-
**Real.sign_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sign_intCast (z : Int) : sign (z : Real) = ↑(Int.sign z)
参数：z : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sign_of_neg`：sign_of_neg {r : Real} (hr : r < 0) : sign r = -1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.cast_lt_zero`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_
1 : PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R] [NeZero 1]   {n : ℤ}, ↑n 
< 0 ↔ …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Int.sign_eq_neg_one_of_neg`：∀ {a : ℤ}, a < 0 → a.sign = -1
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `Real.sign_zero`：sign_zero : sign 0 = 0
· 使用定理 `Int.sign_zero`：Int.sign 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.sign_of_pos`：sign_of_pos {r : Real} (hr : 0 < r) : sign r = 1
· 使用定理 `Int.cast_pos`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_1 : 
PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R] [NeZero 1]   {n : ℤ}, 0 < ↑n 
↔ …
· 使用定理 `Int.sign_eq_one_of_pos`：∀ {a : ℤ}, 0 < a → a.sign = 1
-/
theorem sign_intCast (z : ℤ) : sign (z : ℝ) = ↑(Int.sign z) := by
  obtain hn | rfl | hp := lt_trichotomy z (0 : ℤ)
  · rw [sign_of_neg (Int.cast_lt_zero.mpr hn), Int.sign_eq_neg_one_of_neg hn, Int.cast_neg,
      Int.cast_one]
  · rw [Int.cast_zero, sign_zero, Int.sign_zero, Int.cast_zero]
  · rw [sign_of_pos (Int.cast_pos.mpr hp), Int.sign_eq_one_of_pos hp, Int.cast_one]
/-
**Real.sign_neg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sign_neg {r : Real} : sign (-r) = -sign r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sign_of_neg`：sign_of_neg {r : Real} (hr : r < 0) : sign r = -1
· 使用定理 `Real.sign_of_pos`：sign_of_pos {r : Real} (hr : 0 < r) : sign r = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStri
ctMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Real.sign_zero`：sign_zero : sign 0 = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_lt_zero`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeft
StrictMono α] {a : α}, -a < 0 ↔ 0 < a
-/
theorem sign_neg {r : ℝ} : sign (-r) = -sign r := by
  obtain hn | rfl | hp := lt_trichotomy r (0 : ℝ)
  · rw [sign_of_neg hn, sign_of_pos (neg_pos.mpr hn), neg_neg]
  · rw [sign_zero, neg_zero, sign_zero]
  · rw [sign_of_pos hp, sign_of_neg (neg_lt_zero.mpr hp)]
/-
**Real.sign_mul_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sign_mul_nonneg (r : Real) : 0 <= sign r * r
参数：r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sign_of_neg`：sign_of_neg {r : Real} (hr : r < 0) : sign r = -1
· 使用定理 `mul_nonneg_of_nonpos_of_nonpos`：mul_nonneg_of_nonpos_of_nonpos [ExistsAd
dOfLE R] [MulPosMono R] [AddRightMono R] [AddRightReflectLE R] (ha : a <= 0) (hb
 : b <= 0) : 0 <= a …
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.sign_of_pos`：sign_of_pos {r : Real} (hr : 0 < r) : sign r = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem sign_mul_nonneg (r : ℝ) : 0 ≤ sign r * r := by
  obtain hn | rfl | hp := lt_trichotomy r (0 : ℝ)
  · rw [sign_of_neg hn]
    exact mul_nonneg_of_nonpos_of_nonpos (by simp) hn.le
  · rw [mul_zero]
  · rw [sign_of_pos hp, one_mul]
    exact hp.le
/-
**Real.sign_mul_pos_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sign_mul_pos_of_ne_zero (r : Real) (hr : r != 0) : 0 < sign r * r
参数：r : Real；hr : r != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Real.sign_mul_nonneg`：sign_mul_nonneg (r : Real) : 0 <= sign r * r
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `zero_eq_mul`：zero_eq_mul : 0 = a * b ↔ a = 0 ∨ b = 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `Real.sign_eq_zero_iff`：sign_eq_zero_iff {r : Real} : sign r = 0 ↔ r = 0
-/
theorem sign_mul_pos_of_ne_zero (r : ℝ) (hr : r ≠ 0) : 0 < sign r * r := by
  refine lt_of_le_of_ne (sign_mul_nonneg r) fun h => hr ?_
  have hs0 := (zero_eq_mul.mp h).resolve_right hr
  exact sign_eq_zero_iff.mp hs0

@[simp]
/-
**Real.inv_sign** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：inv_sign (r : Real) : (sign r)⁻¹ = sign r
参数：r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.sign_apply_eq`：sign_apply_eq (r : Real) : sign r = -1 ∨ sign r = 0 
∨ sign r = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `inv_neg`：inv_neg : (-a)⁻¹ = -a⁻¹
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
-/
theorem inv_sign (r : ℝ) : (sign r)⁻¹ = sign r := by
  obtain hn | hz | hp := sign_apply_eq r
  · rw [hn]
    simp
  · rw [hz]
    exact inv_zero
  · rw [hp]
    exact inv_one

@[simp]
/-
**Real.sign_inv** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：sign_inv (r : Real) : sign r⁻¹ = sign r
参数：r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sign_of_neg`：sign_of_neg {r : Real} (hr : r < 0) : sign r = -1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_lt_zero`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Linea
rOrder G₀] {a : G₀} [PosMulMono G₀], a⁻¹ < 0 ↔ a < 0
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Real.sign_zero`：sign_zero : sign 0 = 0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.sign_of_pos`：sign_of_pos {r : Real} (hr : 0 < r) : sign r = 1
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
-/
theorem sign_inv (r : ℝ) : sign r⁻¹ = sign r := by
  obtain hn | rfl | hp := lt_trichotomy r (0 : ℝ)
  · rw [sign_of_neg hn, sign_of_neg (inv_lt_zero.mpr hn)]
  · rw [sign_zero, inv_zero, sign_zero]
  · rw [sign_of_pos hp, sign_of_pos (inv_pos.mpr hp)]

end Real

