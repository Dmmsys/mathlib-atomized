/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import Mathlib.Data.Int.Bitwise
public import Mathlib.Data.Int.Order.Lemmas
public import Mathlib.Order.Interval.Set.Defs

/-!
# Miscellaneous lemmas about the integers

This file contains lemmas about integers, which require further imports than
`Data.Int.Basic` or `Data.Int.Order`.

-/

public section


open Nat

namespace Int

/-
**Int.le_natCast_sub** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：le_natCast_sub (m n : Nat) : (m - n : Int) <= ↑(m - n : Nat)
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem le_natCast_sub (m n : ℕ) : (m - n : ℤ) ≤ ↑(m - n : ℕ) := by
  lia

/-! ### `succ` and `pred` -/


/-
**Int.succ_natCast_pos** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：succ_natCast_pos (n : Nat) : 0 < (n : Int) + 1
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.lt_add_one_iff`：∀ {a b : ℤ}, a < b + 1 ↔ a ≤ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R

--- 原说明 ---
### `succ` and `pred`
-/
theorem succ_natCast_pos (n : ℕ) : 0 < (n : ℤ) + 1 :=
  lt_add_one_iff.mpr (by simp)

/-! ### `natAbs` -/


/-
**Int.natAbs_eq_iff_sq_eq** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：natAbs_eq_iff_sq_eq {a b : Int} : a.natAbs = b.natAbs ↔ a ^ 2 = b ^ 2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Int.natAbs_eq_iff_mul_self_eq`：natAbs_eq_iff_mul_self_eq {a b : Int} : a
.natAbs = b.natAbs ↔ a * a = b * b

--- 原说明 ---
### `natAbs`
-/
theorem natAbs_eq_iff_sq_eq {a b : ℤ} : a.natAbs = b.natAbs ↔ a ^ 2 = b ^ 2 := by
  rw [sq, sq]
  exact natAbs_eq_iff_mul_self_eq
/-
**Int.natAbs_lt_iff_sq_lt** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：natAbs_lt_iff_sq_lt {a b : Int} : a.natAbs < b.natAbs ↔ a ^ 2 < b ^ 2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Int.natAbs_lt_iff_mul_self_lt`：natAbs_lt_iff_mul_self_lt {a b : Int} : a
.natAbs < b.natAbs ↔ a * a < b * b
-/
theorem natAbs_lt_iff_sq_lt {a b : ℤ} : a.natAbs < b.natAbs ↔ a ^ 2 < b ^ 2 := by
  rw [sq, sq]
  exact natAbs_lt_iff_mul_self_lt
/-
**Int.natAbs_le_iff_sq_le** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：natAbs_le_iff_sq_le {a b : Int} : a.natAbs <= b.natAbs ↔ a ^ 2 <= b ^ 2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Int.natAbs_le_iff_mul_self_le`：natAbs_le_iff_mul_self_le {a b : Int} : a
.natAbs <= b.natAbs ↔ a * a <= b * b
-/
theorem natAbs_le_iff_sq_le {a b : ℤ} : a.natAbs ≤ b.natAbs ↔ a ^ 2 ≤ b ^ 2 := by
  rw [sq, sq]
  exact natAbs_le_iff_mul_self_le
/-
**Int.natAbs_inj_of_nonneg_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：natAbs_inj_of_nonneg_of_nonneg {a b : Int} (ha : 0 <= a) (hb : 0 <= b) : n
atAbs a = natAbs b ↔ a = b
参数：ha : 0 <= a；hb : 0 <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `sq_eq_sq₀`：sq_eq_sq₀ (ha : 0 <= a) (hb : 0 <= b) : a ^ 2 = b ^ 2 ↔ a = b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Int.natAbs_eq_iff_sq_eq`：natAbs_eq_iff_sq_eq {a b : Int} : a.natAbs = b.
natAbs ↔ a ^ 2 = b ^ 2
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem natAbs_inj_of_nonneg_of_nonneg {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    natAbs a = natAbs b ↔ a = b := by rw [← sq_eq_sq₀ ha hb, ← natAbs_eq_iff_sq_eq]
/-
**Int.natAbs_inj_of_nonpos_of_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：natAbs_inj_of_nonpos_of_nonpos {a b : Int} (ha : a <= 0) (hb : b <= 0) : n
atAbs a = natAbs b ↔ a = b
参数：ha : a <= 0；hb : b <= 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.natAbs_neg`：∀ (a : ℤ), (-a).natAbs = a.natAbs
· 使用定理 `Int.natAbs_inj_of_nonneg_of_nonneg`：natAbs_inj_of_nonneg_of_nonneg {a b 
: Int} (ha : 0 <= a) (hb : 0 <= b) : natAbs a = natAbs b ↔ a = b
· 使用定理 `neg_nonneg_of_nonpos`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : P
artialOrder α] [IsOrderedAddMonoid α] {a : α}, a ≤ 0 → 0 ≤ -a
-/
theorem natAbs_inj_of_nonpos_of_nonpos {a b : ℤ} (ha : a ≤ 0) (hb : b ≤ 0) :
    natAbs a = natAbs b ↔ a = b := by
  simpa only [Int.natAbs_neg, neg_inj] using
    natAbs_inj_of_nonneg_of_nonneg (neg_nonneg_of_nonpos ha) (neg_nonneg_of_nonpos hb)
/-
**Int.natAbs_inj_of_nonneg_of_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：natAbs_inj_of_nonneg_of_nonpos {a b : Int} (ha : 0 <= a) (hb : b <= 0) : n
atAbs a = natAbs b ↔ a = -b
参数：ha : 0 <= a；hb : b <= 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.natAbs_neg`：∀ (a : ℤ), (-a).natAbs = a.natAbs
· 使用定理 `Int.natAbs_inj_of_nonneg_of_nonneg`：natAbs_inj_of_nonneg_of_nonneg {a b 
: Int} (ha : 0 <= a) (hb : 0 <= b) : natAbs a = natAbs b ↔ a = b
· 使用定理 `neg_nonneg_of_nonpos`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : P
artialOrder α] [IsOrderedAddMonoid α] {a : α}, a ≤ 0 → 0 ≤ -a
-/
theorem natAbs_inj_of_nonneg_of_nonpos {a b : ℤ} (ha : 0 ≤ a) (hb : b ≤ 0) :
    natAbs a = natAbs b ↔ a = -b := by
  simpa only [Int.natAbs_neg] using natAbs_inj_of_nonneg_of_nonneg ha (neg_nonneg_of_nonpos hb)
/-
**Int.natAbs_inj_of_nonpos_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：natAbs_inj_of_nonpos_of_nonneg {a b : Int} (ha : a <= 0) (hb : 0 <= b) : n
atAbs a = natAbs b ↔ -a = b
参数：ha : a <= 0；hb : 0 <= b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.natAbs_neg`：∀ (a : ℤ), (-a).natAbs = a.natAbs
· 使用定理 `Int.natAbs_inj_of_nonneg_of_nonneg`：natAbs_inj_of_nonneg_of_nonneg {a b 
: Int} (ha : 0 <= a) (hb : 0 <= b) : natAbs a = natAbs b ↔ a = b
· 使用定理 `neg_nonneg_of_nonpos`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : P
artialOrder α] [IsOrderedAddMonoid α] {a : α}, a ≤ 0 → 0 ≤ -a
-/
theorem natAbs_inj_of_nonpos_of_nonneg {a b : ℤ} (ha : a ≤ 0) (hb : 0 ≤ b) :
    natAbs a = natAbs b ↔ -a = b := by
  simpa only [Int.natAbs_neg] using natAbs_inj_of_nonneg_of_nonneg (neg_nonneg_of_nonpos ha) hb

/-- A specialization of `abs_sub_le_of_nonneg_of_le` for working with the signed subtraction
  of natural numbers. -/
/-
**Int.natAbs_coe_sub_coe_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：natAbs_coe_sub_coe_le_of_le {a b n : Nat} (a_le_n : a <= n) (b_le_n : b <=
 n) : natAbs (a - b : Int) <= n
参数：a_le_n : a <= n；b_le_n : b <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `Int.natCast_natAbs`：∀ (n : ℤ), ↑n.natAbs = |n|
· 使用定理 `abs_sub_le_of_nonneg_of_le`：∀ {G : Type u_1} [inst : AddCommGroup G] [in
st_1 : LinearOrder G] [IsOrderedAddMonoid G] {a b n : G},   0 ≤ a → a ≤ n → 0 ≤ 
b → b ≤ n → |a -…
· 使用定理 `Int.natCast_nonneg`：∀ (n : ℕ), 0 ≤ ↑n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.ofNat_le`：∀ {m n : ℕ}, ↑m ≤ ↑n ↔ m ≤ n

--- 原说明 ---
A specialization of `abs_sub_le_of_nonneg_of_le` for working with the signed sub
traction
  of natural numbers.
-/
theorem natAbs_coe_sub_coe_le_of_le {a b n : ℕ} (a_le_n : a ≤ n) (b_le_n : b ≤ n) :
    natAbs (a - b : ℤ) ≤ n := by
  rw [← Nat.cast_le (α := ℤ), natCast_natAbs]
  exact abs_sub_le_of_nonneg_of_le (natCast_nonneg a) (ofNat_le.mpr a_le_n)
    (natCast_nonneg b) (ofNat_le.mpr b_le_n)

/-- A specialization of `abs_sub_lt_of_nonneg_of_lt` for working with the signed subtraction
  of natural numbers. -/
/-
**Int.natAbs_coe_sub_coe_lt_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：natAbs_coe_sub_coe_lt_of_lt {a b n : Nat} (a_lt_n : a < n) (b_lt_n : b < n
) : natAbs (a - b : Int) < n
参数：a_lt_n : a < n；b_lt_n : b < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `Int.natCast_natAbs`：∀ (n : ℤ), ↑n.natAbs = |n|
· 使用定理 `abs_sub_lt_of_nonneg_of_lt`：∀ {G : Type u_1} [inst : AddCommGroup G] [in
st_1 : LinearOrder G] [IsOrderedAddMonoid G] {a b n : G},   0 ≤ a → a < n → 0 ≤ 
b → b < n → |a -…
· 使用定理 `Int.natCast_nonneg`：∀ (n : ℕ), 0 ≤ ↑n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.ofNat_lt`：∀ {n m : ℕ}, ↑n < ↑m ↔ n < m

--- 原说明 ---
A specialization of `abs_sub_lt_of_nonneg_of_lt` for working with the signed sub
traction
  of natural numbers.
-/
theorem natAbs_coe_sub_coe_lt_of_lt {a b n : ℕ} (a_lt_n : a < n) (b_lt_n : b < n) :
    natAbs (a - b : ℤ) < n := by
  rw [← Nat.cast_lt (α := ℤ), natCast_natAbs]
  exact abs_sub_lt_of_nonneg_of_lt (natCast_nonneg a) (ofNat_lt.mpr a_lt_n)
    (natCast_nonneg b) (ofNat_lt.mpr b_lt_n)

section Intervals

open Set

/-
**Int.strictMonoOn_natAbs** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：strictMonoOn_natAbs : StrictMonoOn natAbs (Ici 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.natAbs_lt_natAbs_of_nonneg_of_lt`：∀ {a b : ℤ}, 0 ≤ a → a < b → a.nat
Abs < b.natAbs
-/
theorem strictMonoOn_natAbs : StrictMonoOn natAbs (Ici 0) := fun _ ha _ _ hab =>
  natAbs_lt_natAbs_of_nonneg_of_lt ha hab
/-
**Int.strictAntiOn_natAbs** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：strictAntiOn_natAbs : StrictAntiOn natAbs (Iic 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.natAbs_neg`：∀ (a : ℤ), (-a).natAbs = a.natAbs
· 使用定理 `Int.natAbs_lt_natAbs_of_nonneg_of_lt`：∀ {a b : ℤ}, 0 ≤ a → a < b → a.nat
Abs < b.natAbs
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Right.nonneg_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α]
 [AddRightMono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `neg_lt_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddL
eftStrictMono α] {a b : α} [AddRightStrictMono α],   -a < -b ↔ b < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
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
-/
theorem strictAntiOn_natAbs : StrictAntiOn natAbs (Iic 0) := fun a _ b hb hab => by
  simpa [Int.natAbs_neg] using
    natAbs_lt_natAbs_of_nonneg_of_lt (Right.nonneg_neg_iff.mpr hb) (neg_lt_neg_iff.mpr hab)
/-
**Int.injOn_natAbs_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：injOn_natAbs_Ici : InjOn natAbs (Ici 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictMonoOn.injOn`：StrictMonoOn.injOn (hf : StrictMonoOn f s) : s.InjOn
 f
· 使用定理 `Int.strictMonoOn_natAbs`：strictMonoOn_natAbs : StrictMonoOn natAbs (Ici 
0)
-/
theorem injOn_natAbs_Ici : InjOn natAbs (Ici 0) :=
  strictMonoOn_natAbs.injOn
/-
**Int.injOn_natAbs_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：injOn_natAbs_Iic : InjOn natAbs (Iic 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictAntiOn.injOn`：StrictAntiOn.injOn (hf : StrictAntiOn f s) : s.InjOn
 f
· 使用定理 `Int.strictAntiOn_natAbs`：strictAntiOn_natAbs : StrictAntiOn natAbs (Iic 
0)
-/
theorem injOn_natAbs_Iic : InjOn natAbs (Iic 0) :=
  strictAntiOn_natAbs.injOn

end Intervals

/-! ### bitwise ops

This lemma is orphaned from `Data.Int.Bitwise` as it also requires material from `Data.Int.Order`.
-/

@[simp]
/-
**Int.div2_bit** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：div2_bit (b n) : div2 (bit b n) = n
参数：b n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.bit_val`：bit_val (b n) : bit b n = 2 * n + cond b 1 0
· 使用定理 `Int.div2_val`：∀ (n : ℤ), n.div2 = n / 2
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Int.add_mul_ediv_left`：∀ (a : ℤ) {b : ℤ} (c : ℤ), b ≠ 0 → (a + b * c) / 
b = a / b + c
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.div_eq_of_lt`：∀ {a b : ℕ}, a < b → a / b = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a

--- 原说明 ---
### bitwise ops

This lemma is orphaned from `Data.Int.Bitwise` as it also requires material from
 `Data.Int.Order`.
-/
theorem div2_bit (b n) : div2 (bit b n) = n := by
  rw [bit_val, div2_val, add_comm, Int.add_mul_ediv_left, (_ : (_ / 2 : ℤ) = 0), zero_add]
  cases b
  · decide
  · change ofNat _ = _
    rw [Nat.div_eq_of_lt] <;> simp
  · decide

/-- Like `Int.ediv_emod_unique`, but permitting negative `b`. -/
/-
**Int.ediv_emod_unique''** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：ediv_emod_unique'' {a b r q : Int} (h : b != 0) : a / b = q ∧ a % b = r ↔ 
r + b * q = a ∧ 0 <= r ∧ r < |b|
参数：h : b != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.emod_add_mul_ediv`：∀ (a b : ℤ), a % b + b * (a / b) = a
· 使用定理 `Int.emod_nonneg`：∀ (a : ℤ) {b : ℤ}, b ≠ 0 → 0 ≤ a % b
· 使用定理 `Int.emod_lt_abs`：emod_lt_abs (a : Int) {b : Int} (H : b != 0) : a % b < 
|b|
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.add_mul_ediv_left`：∀ (a : ℤ) {b : ℤ} (c : ℤ), b ≠ 0 → (a + b * c) / 
b = a / b + c
· 使用定理 `Int.ediv_eq_zero_of_lt_abs`：ediv_eq_zero_of_lt_abs {a b : Int} (H1 : 0 <
= a) (H2 : a < |b|) : a / b = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Int.add_mul_emod_self_left`：∀ (a b c : ℤ), (a + b * c) % b = a % b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.emod_abs`：emod_abs (a b : Int) : a % |b| = a % b
· 使用定理 `Int.emod_eq_of_lt`：∀ {a b : ℤ}, 0 ≤ a → a < b → a % b = a

--- 原说明 ---
Like `Int.ediv_emod_unique`, but permitting negative `b`.
-/
theorem ediv_emod_unique'' {a b r q : Int} (h : b ≠ 0) :
    a / b = q ∧ a % b = r ↔ r + b * q = a ∧ 0 ≤ r ∧ r < |b| := by
  constructor
  · intro ⟨rfl, rfl⟩
    exact ⟨emod_add_mul_ediv a b, emod_nonneg _ h, emod_lt_abs _ h⟩
  · intro ⟨rfl, hz, hb⟩
    constructor
    · rw [Int.add_mul_ediv_left r q h, ediv_eq_zero_of_lt_abs hz hb]
      simp
    · rw [add_mul_emod_self_left, ← emod_abs, emod_eq_of_lt hz hb]

end Int

