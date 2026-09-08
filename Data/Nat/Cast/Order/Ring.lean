/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Data.Nat.Cast.Order.Basic

/-!
# Cast of natural numbers: lemmas about bundled ordered semirings

-/

public section

variable {R α : Type*}

namespace Nat

section AddMonoidWithOne
variable [AddMonoidWithOne α] [PartialOrder α]
variable [AddLeftMono α] [ZeroLEOneClass α]

/-- Specialisation of `Nat.cast_nonneg'`, which seems to be easier for Lean to use. -/
@[simp]
/-
**Nat.cast_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrderedRing α] (n : Nat) 
: 0 <= (n : α)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R

--- 原说明 ---
Specialisation of `Nat.cast_nonneg'`, which seems to be easier for Lean to use.
-/
theorem cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrderedRing α] (n : ℕ) : 0 ≤ (n : α) :=
  cast_nonneg' n

/-- Specialisation of `Nat.ofNat_nonneg'`, which seems to be easier for Lean to use. -/
@[simp]
/-
**Nat.ofNat_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ofNat_nonneg {α} [Semiring α] [PartialOrder α] [IsOrderedRing α] (n : Nat)
 [n.AtLeastTwo] : 0 <= (ofNat(n) : α)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ofNat_nonneg'`：ofNat_nonneg' (n : Nat) [n.AtLeastTwo] : 0 <= (ofNat(
n) : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R

--- 原说明 ---
Specialisation of `Nat.ofNat_nonneg'`, which seems to be easier for Lean to use.
-/
theorem ofNat_nonneg {α} [Semiring α] [PartialOrder α] [IsOrderedRing α] (n : ℕ) [n.AtLeastTwo] :
    0 ≤ (ofNat(n) : α) :=
  ofNat_nonneg' n

@[simp, norm_cast]
/-
**Nat.cast_min** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cast_min {α} [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] (m n : N
at) : (↑(min m n : Nat) : α) = min (m : α) n
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_min`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [in
st_1 : LinearOrder β] {f : α → β} {a b : α},   Monotone f → f (min a b) = min (f
 a) (f…
· 使用定理 `Nat.mono_cast`：mono_cast : Monotone (Nat.cast : Nat -> α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
-/
theorem cast_min {α} [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] (m n : ℕ) :
    (↑(min m n : ℕ) : α) = min (m : α) n :=
  (@mono_cast α _).map_min

@[simp, norm_cast]
/-
**Nat.cast_max** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cast_max {α} [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] (m n : N
at) : (↑(max m n : Nat) : α) = max (m : α) n
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)
· 使用定理 `Nat.mono_cast`：mono_cast : Monotone (Nat.cast : Nat -> α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
-/
theorem cast_max {α} [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] (m n : ℕ) :
    (↑(max m n : ℕ) : α) = max (m : α) n :=
  (@mono_cast α _).map_max

section Nontrivial

variable [NeZero (1 : α)]

/-- Specialisation of `Nat.cast_pos'`, which seems to be easier for Lean to use. -/
@[simp]
/-
**Nat.cast_pos** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing α] [Nontrivial α
] {n : Nat} : (0 : α) < n ↔ 0 < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R

--- 原说明 ---
Specialisation of `Nat.cast_pos'`, which seems to be easier for Lean to use.
-/
theorem cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing α] [Nontrivial α] {n : ℕ} :
    (0 : α) < n ↔ 0 < n := cast_pos'

/-- See also `Nat.ofNat_pos`, specialised to `IsOrderedRing`. -/
@[simp low]
/-
**Nat.ofNat_pos'** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ofNat_pos' {n : Nat} [n.AtLeastTwo] : 0 < (ofNat(n) : α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `NeZero.pos`：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] :
 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.AtLeastTwo.toNeZero`：∀ (n : ℕ) [n.AtLeastTwo], NeZero n

--- 原说明 ---
See also `Nat.ofNat_pos`, specialised to `IsOrderedRing`.
-/
theorem ofNat_pos' {n : ℕ} [n.AtLeastTwo] : 0 < (ofNat(n) : α) :=
  cast_pos'.mpr (NeZero.pos n)

/-- Specialisation of `Nat.ofNat_pos'`, which seems to be easier for Lean to use. -/
@[simp]
/-
**Nat.ofNat_pos** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：ofNat_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing α] [Nontrivial 
α] {n : Nat} [n.AtLeastTwo] : 0 < (ofNat(n) : α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ofNat_pos'`：ofNat_pos' {n : Nat} [n.AtLeastTwo] : 0 < (ofNat(n) : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R

--- 原说明 ---
Specialisation of `Nat.ofNat_pos'`, which seems to be easier for Lean to use.
-/
theorem ofNat_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing α] [Nontrivial α]
    {n : ℕ} [n.AtLeastTwo] :
    0 < (ofNat(n) : α) :=
  ofNat_pos'

end Nontrivial

end AddMonoidWithOne

/-- A version of `Nat.cast_sub` that works for `ℝ≥0` and `ℚ≥0`. Note that this proof doesn't work
for `ℕ∞` and `ℝ≥0∞`, so we use type-specific lemmas for these types. -/
@[simp, norm_cast]
/-
**Nat.cast_tsub** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：cast_tsub [CommSemiring α] [PartialOrder α] [IsOrderedRing α] [Canonically
OrderedAdd α] [Sub α] [OrderedSub α] [AddLeftReflectLE α] (m n : Nat) : ↑(m - n)
 = (m - n : α)
参数：m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `tsub_eq_zero_of_le`：∀ {α : Type u_1} [inst : AddCommMonoid α] [inst_1 : 
PartialOrder α] [CanonicallyOrderedAdd α] [inst_3 : Sub α]   [OrderedSub α] {a b
 : α}, a…
· 使用定理 `Nat.mono_cast`：mono_cast : Monotone (Nat.cast : Nat -> α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_iff_exists_add'`：∀ {α : Type u} [inst : AddCommMagma α] [inst_1 : Pre
order α] [CanonicallyOrderedAdd α] {a b : α}, a ≤ b ↔ ∃ c, b = c + a
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A version of `Nat.cast_sub` that works for `ℝ≥0` and `ℚ≥0`. Note that this proof
 doesn't work
for `ℕ∞` and `ℝ≥0∞`, so we use type-specific lemmas for these types.
-/
theorem cast_tsub [CommSemiring α] [PartialOrder α] [IsOrderedRing α] [CanonicallyOrderedAdd α]
    [Sub α] [OrderedSub α] [AddLeftReflectLE α] (m n : ℕ) : ↑(m - n) = (m - n : α) := by
  rcases le_total m n with h | h
  · rw [Nat.sub_eq_zero_of_le h, cast_zero, tsub_eq_zero_of_le]
    exact mono_cast h
  · rcases le_iff_exists_add'.mp h with ⟨m, rfl⟩
    rw [add_tsub_cancel_right, cast_add, add_tsub_cancel_right]

section Lattice
variable [Ring R] [Lattice R] [IsOrderedRing R]

@[simp, norm_cast]
/-
**Nat.abs_cast** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：abs_cast (n : Nat) : |(n : R)| = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
-/
theorem abs_cast (n : ℕ) : |(n : R)| = n := abs_of_nonneg n.cast_nonneg

@[simp]
/-
**Nat.abs_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：abs_ofNat (n : Nat) [n.AtLeastTwo] : |(ofNat(n) : R)| = ofNat(n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.abs_cast`：abs_cast (n : Nat) : |(n : R)| = n
-/
theorem abs_ofNat (n : ℕ) [n.AtLeastTwo] : |(ofNat(n) : R)| = ofNat(n) := abs_cast n

end Lattice

section PartialOrderedRing

variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R] {m n : ℕ}

/-
**Nat.neg_cast_eq_cast** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] [inst_1 : PartialOrder R] [IsStrictOrdere
dRing R] {m n : ℕ}, -↑m = ↑n ↔ m = 0 ∧ n = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp, norm_cast] lemma neg_cast_eq_cast : (-m : R) = n ↔ m = 0 ∧ n = 0 := by
  simp [neg_eq_iff_add_eq_zero, ← cast_add]
/-
**Nat.cast_eq_neg_cast** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] [inst_1 : PartialOrder R] [IsStrictOrdere
dRing R] {m n : ℕ}, ↑m = -↑n ↔ m = 0 ∧ n = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp, norm_cast] lemma cast_eq_neg_cast : (m : R) = -n ↔ m = 0 ∧ n = 0 := by
  simp [eq_neg_iff_add_eq_zero, ← cast_add]

end PartialOrderedRing

end Nat

