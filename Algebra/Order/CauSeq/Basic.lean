/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Group.MinMax
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Data.Setoid.Basic
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.Tactic.GCongr

/-!
# Cauchy sequences

A basic theory of Cauchy sequences, used in the construction of the reals and p-adic numbers. Where
applicable, lemmas that will be reused in other contexts have been stated in extra generality.
There are other "versions" of Cauchyness in the library, in particular Cauchy filters in topology.
This is a concrete implementation that is useful for simplicity and computability reasons.

## Important definitions

* `IsCauSeq`: a predicate that says `f : ℕ → β` is Cauchy.
* `CauSeq`: the type of Cauchy sequences valued in type `β` with respect to an absolute value
  function `abv`.

## Tags

sequence, cauchy, abs val, absolute value
-/

@[expose] public section

assert_not_exists Finset Module Submonoid FloorRing

variable {α β : Type*}

open IsAbsoluteValue

section

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Ring β]
  (abv : β → α) [IsAbsoluteValue abv]

/-
**rat_add_continuous_lemma** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rat_add_continuous_lemma {ε : α} (ε0 : 0 < ε) : exists δ > 0, forall {a₁ a
₂ b₁ b₂ : β}, abv (a₁ - b₁) < δ -> abv (a₂ - b₂) < δ -> abv (a₁ + a₂ - (b₁ + b₂)
) < ε
参数：ε0 : 0 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_add_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b
 c d : α), a + b - (c + d) = a - c + (b - d)
· 使用定理 `lt_imp_lt_of_le_of_le`：lt_imp_lt_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a < b -> c < d
· 使用引理 `IsAbsoluteValue.abv_add`：abv_add (x y) : abv (x + y) <= abv x + abv y
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `add_lt_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [i : Ad
dRightStrictMono α] {b c : α}, b < c → ∀ (a : α), b + a < c + a
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
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `add_halves`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2] (a :
 K), a / 2 + a / 2 = a
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
-/
theorem rat_add_continuous_lemma {ε : α} (ε0 : 0 < ε) :
    ∃ δ > 0, ∀ {a₁ a₂ b₁ b₂ : β}, abv (a₁ - b₁) < δ → abv (a₂ - b₂) < δ →
      abv (a₁ + a₂ - (b₁ + b₂)) < ε :=
  ⟨ε / 2, half_pos ε0, fun {a₁ a₂ b₁ b₂} h₁ h₂ => by
    grw [add_sub_add_comm, abv_add abv, h₁, h₂, add_halves]⟩
/-
**rat_mul_continuous_lemma** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rat_mul_continuous_lemma {ε K₁ K₂ : α} (ε0 : 0 < ε) : exists δ > 0, forall
 {a₁ a₂ b₁ b₂ : β}, abv a₁ < K₁ -> abv b₂ < K₂ -> abv (a₁ - b₁) < δ -> abv (a₂ -
 b₂) < δ -> abv (a₁ * a₂ - b₁ * b₂) < ε
参数：ε0 : 0 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `lt_imp_lt_of_le_of_le`：lt_imp_lt_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a < b -> c < d
· 使用引理 `IsAbsoluteValue.abv_add`：abv_add (x y) : abv (x + y) <= abv x + abv y
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsAbsoluteValue.abv_mul`：abv_mul (x y) : abv (x * y) = abv x * abv y
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `IsAbsoluteValue.abv_nonneg`：abv_nonneg (x) : 0 <= abv x
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
（共 54 条，此处仅展示前 30 条）
-/
theorem rat_mul_continuous_lemma {ε K₁ K₂ : α} (ε0 : 0 < ε) :
    ∃ δ > 0, ∀ {a₁ a₂ b₁ b₂ : β}, abv a₁ < K₁ → abv b₂ < K₂ → abv (a₁ - b₁) < δ →
      abv (a₂ - b₂) < δ → abv (a₁ * a₂ - b₁ * b₂) < ε := by
  have K0 : (0 : α) < max 1 (max K₁ K₂) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have εK := div_pos (half_pos ε0) K0
  refine ⟨_, εK, fun {a₁ a₂ b₁ b₂} ha₁ hb₂ h₁ h₂ => ?_⟩
  replace ha₁ := lt_of_lt_of_le ha₁ (le_trans (le_max_left _ K₂) (le_max_right 1 _))
  replace hb₂ := lt_of_lt_of_le hb₂ (le_trans (le_max_right K₁ _) (le_max_right 1 _))
  set M := max 1 (max K₁ K₂)
  suffices abv ((a₁ - b₁) * b₂ + a₁ * (a₂ - b₂)) < ε by
    simpa [sub_eq_add_neg, mul_add, add_mul, add_left_comm] using this
  grw [abv_add abv, abv_mul abv, abv_mul abv, h₁.le, h₂.le, ha₁, hb₂, mul_comm M,
    div_mul_cancel₀ _ (ne_of_gt K0), add_halves]
/-
**rat_inv_continuous_lemma** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rat_inv_continuous_lemma {β : Type*} [DivisionRing β] (abv : β -> α) [IsAb
soluteValue abv] {ε K : α} (ε0 : 0 < ε) (K0 : 0 < K) : exists δ > 0, forall {a b
 : β}, K <= abv a -> K <= abv b -> abv (a - b) < δ -> abv (a⁻¹ - b⁻¹) < ε
参数：abv : β -> α；ε0 : 0 < ε；K0 : 0 < K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_sub_inv'`：inv_sub_inv' {a b : K} (ha : a != 0) (hb : b != 0) : a⁻¹ -
 b⁻¹ = a⁻¹ * (b - a) * b⁻¹
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsAbsoluteValue.abv_pos`：abv_pos {a : R} : 0 < abv a ↔ a != 0
· 使用引理 `IsAbsoluteValue.abv_mul`：abv_mul (x y) : abv (x * y) = abv x * abv y
· 使用定理 `IsAbsoluteValue.abv_inv`：abv_inv (a : R) : abv a⁻¹ = (abv a)⁻¹
· 使用定理 `IsAbsoluteValue.abv_sub`：abv_sub (a b : R) : abv (a - b) = abv (b - a)
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Field.isDomain`：∀ {K : Type u_1} [inst : Field K], IsDomain K
· 使用定理 `lt_imp_lt_of_le_of_le`：lt_imp_lt_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a < b -> c < d
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用引理 `inv_anti₀`：inv_anti₀ (hb : 0 < b) (hba : b <= a) : a⁻¹ <= b⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用引理 `IsAbsoluteValue.abv_nonneg`：abv_nonneg (x) : 0 <= abv x
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
（共 40 条，此处仅展示前 30 条）
-/
theorem rat_inv_continuous_lemma {β : Type*} [DivisionRing β] (abv : β → α) [IsAbsoluteValue abv]
    {ε K : α} (ε0 : 0 < ε) (K0 : 0 < K) :
    ∃ δ > 0, ∀ {a b : β}, K ≤ abv a → K ≤ abv b → abv (a - b) < δ → abv (a⁻¹ - b⁻¹) < ε := by
  refine ⟨K * ε * K, mul_pos (mul_pos K0 ε0) K0, fun {a b} ha hb h => ?_⟩
  have a0 := K0.trans_le ha
  have b0 := K0.trans_le hb
  rw [inv_sub_inv' ((abv_pos abv).1 a0) ((abv_pos abv).1 b0), abv_mul abv, abv_mul abv, abv_inv abv,
    abv_inv abv, abv_sub abv]
  grw [← ha, mul_assoc, ← hb, h]
  simp [K0.ne']

end

/-- A sequence is Cauchy if the distance between its entries tends to zero. -/
@[nolint unusedArguments]
/-
**IsCauSeq** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsCauSeq {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] {β 
: Type*} [Ring β] (abv : β -> α) (f : Nat -> β) : Prop
参数：abv : β -> α；f : Nat -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sequence is Cauchy if the distance between its entries tends to zero.
-/
def IsCauSeq {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    {β : Type*} [Ring β] (abv : β → α) (f : ℕ → β) :
    Prop :=
  ∀ ε > 0, ∃ i, ∀ j ≥ i, abv (f j - f i) < ε

namespace IsCauSeq

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] [Ring β]
  {abv : β → α} [IsAbsoluteValue abv] {f g : ℕ → β}

/-
**IsCauSeq.cauchy** 是 Mathlib 中的一个定理，位于命名空间 `IsCauSeq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cauchy₂ (hf : IsCauSeq abv f) {ε : α} (ε0 : 0 < ε) :
    ∃ i, ∀ j ≥ i, ∀ k ≥ i, abv (f j - f k) < ε := by
  refine (hf _ (half_pos ε0)).imp fun i hi j ij k ik => ?_
  rw [← add_halves ε]
  refine lt_of_le_of_lt (abv_sub_le abv _ _ _) (add_lt_add (hi _ ij) ?_)
  rw [abv_sub abv]; exact hi _ ik
/-
**IsCauSeq.cauchy** 是 Mathlib 中的一个定理，位于命名空间 `IsCauSeq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cauchy₃ (hf : IsCauSeq abv f) {ε : α} (ε0 : 0 < ε) :
    ∃ i, ∀ j ≥ i, ∀ k ≥ j, abv (f k - f j) < ε :=
  let ⟨i, H⟩ := hf.cauchy₂ ε0
  ⟨i, fun _ ij _ jk => H _ (le_trans ij jk) _ ij⟩
/-
**IsCauSeq.bounded** 是 Mathlib 中的一个引理，位于命名空间 `IsCauSeq`。
形式化陈述：bounded (hf : IsCauSeq abv f) : exists r, forall i, abv (f i) < r
参数：hf : IsCauSeq abv f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用引理 `IsAbsoluteValue.abv_add`：abv_add (x y) : abv (x + y) <= abv x + abv y
· 使用定理 `add_lt_add_of_le_of_lt`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preord
er α] [AddLeftStrictMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c < d → a 
+ c < b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma bounded (hf : IsCauSeq abv f) : ∃ r, ∀ i, abv (f i) < r := by
  obtain ⟨i, h⟩ := hf _ zero_lt_one
  set R : ℕ → α := @Nat.rec (fun _ => α) (abv (f 0)) fun i c => max c (abv (f i.succ)) with hR
  have : ∀ i, ∀ j ≤ i, abv (f j) ≤ R i := by
    refine Nat.rec (by simp [hR]) ?_
    rintro i hi j (rfl | hj)
    · simp [R]
    · exact (hi j hj).trans (le_max_left _ _)
  refine ⟨R i + 1, fun j ↦ ?_⟩
  obtain hji | hij := le_total j i
  · exact (this i _ hji).trans_lt (lt_add_one _)
  · simpa using (abv_add abv _ _).trans_lt <| add_lt_add_of_le_of_lt (this i _ le_rfl) (h _ hij)
/-
**IsCauSeq.bounded'** 是 Mathlib 中的一个引理，位于命名空间 `IsCauSeq`。
形式化陈述：bounded' (hf : IsCauSeq abv f) (x : α) : exists r > x, forall i, abv (f i)
 < r
参数：hf : IsCauSeq abv f；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsCauSeq.bounded`：bounded (hf : IsCauSeq abv f) : exists r, forall i, ab
v (f i) < r
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
-/
lemma bounded' (hf : IsCauSeq abv f) (x : α) : ∃ r > x, ∀ i, abv (f i) < r :=
  let ⟨r, h⟩ := hf.bounded
  ⟨max r (x + 1), (lt_add_one x).trans_le (le_max_right _ _),
    fun i ↦ (h i).trans_le (le_max_left _ _)⟩
/-
**IsCauSeq.const** 是 Mathlib 中的一个引理，位于命名空间 `IsCauSeq`。
形式化陈述：const (x : β) : IsCauSeq abv fun _ => x
参数：x : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `IsAbsoluteValue.abv_zero`：abv_zero : abv 0 = 0
-/
lemma const (x : β) : IsCauSeq abv fun _ ↦ x :=
  fun ε ε0 ↦ ⟨0, fun j _ => by simpa [abv_zero] using ε0⟩
/-
**IsCauSeq.add** 是 Mathlib 中的一个定理，位于命名空间 `IsCauSeq`。
形式化陈述：add (hf : IsCauSeq abv f) (hg : IsCauSeq abv g) : IsCauSeq abv (f + g)
参数：hf : IsCauSeq abv f；hg : IsCauSeq abv g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `rat_add_continuous_lemma`：rat_add_continuous_lemma {ε : α} (ε0 : 0 < ε) 
: exists δ > 0, forall {a₁ a₂ b₁ b₂ : β}, abv (a₁ - b₁) < δ -> abv (a₂ - b₂) < δ
 -> abv (a₁ + …
· 使用引理 `exists_forall_ge_and`：exists_forall_ge_and {p q : α -> Prop} : (exists i
, forall j >= i, p j) -> (exists i, forall j >= i, q j) -> exists i, forall j >=
 i, p j ∧ …
· 使用定理 `IsCauSeq.cauchy₃`：cauchy₃ (hf : IsCauSeq abv f) {ε : α} (ε0 : 0 < ε) : e
xists i, forall j >= i, forall k >= j, abv (f k - f j) < ε
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem add (hf : IsCauSeq abv f) (hg : IsCauSeq abv g) : IsCauSeq abv (f + g) := fun _ ε0 =>
  let ⟨_, δ0, Hδ⟩ := rat_add_continuous_lemma abv ε0
  let ⟨i, H⟩ := exists_forall_ge_and (hf.cauchy₃ δ0) (hg.cauchy₃ δ0)
  ⟨i, fun _ ij =>
    let ⟨H₁, H₂⟩ := H _ le_rfl
    Hδ (H₁ _ ij) (H₂ _ ij)⟩
/-
**IsCauSeq.mul** 是 Mathlib 中的一个引理，位于命名空间 `IsCauSeq`。
形式化陈述：mul (hf : IsCauSeq abv f) (hg : IsCauSeq abv g) : IsCauSeq abv (f * g)
参数：hf : IsCauSeq abv f；hg : IsCauSeq abv g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsCauSeq.bounded'`：bounded' (hf : IsCauSeq abv f) (x : α) : exists r > x
, forall i, abv (f i) < r
· 使用定理 `rat_mul_continuous_lemma`：rat_mul_continuous_lemma {ε K₁ K₂ : α} (ε0 : 0
 < ε) : exists δ > 0, forall {a₁ a₂ b₁ b₂ : β}, abv a₁ < K₁ -> abv b₂ < K₂ -> ab
v (a₁ - b₁) < …
· 使用引理 `exists_forall_ge_and`：exists_forall_ge_and {p q : α -> Prop} : (exists i
, forall j >= i, p j) -> (exists i, forall j >= i, q j) -> exists i, forall j >=
 i, p j ∧ …
· 使用定理 `IsCauSeq.cauchy₃`：cauchy₃ (hf : IsCauSeq abv f) {ε : α} (ε0 : 0 < ε) : e
xists i, forall j >= i, forall k >= j, abv (f k - f j) < ε
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma mul (hf : IsCauSeq abv f) (hg : IsCauSeq abv g) : IsCauSeq abv (f * g) := fun _ ε0 =>
  let ⟨_, _, hF⟩ := hf.bounded' 0
  let ⟨_, _, hG⟩ := hg.bounded' 0
  let ⟨_, δ0, Hδ⟩ := rat_mul_continuous_lemma abv ε0
  let ⟨i, H⟩ := exists_forall_ge_and (hf.cauchy₃ δ0) (hg.cauchy₃ δ0)
  ⟨i, fun j ij =>
    let ⟨H₁, H₂⟩ := H _ le_rfl
    Hδ (hF j) (hG i) (H₁ _ ij) (H₂ _ ij)⟩
/-
**IsCauSeq._root_.isCauSeq_neg** 是 Mathlib 中的一个引理，位于命名空间 `IsCauSeq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.isCauSeq_neg : IsCauSeq abv (-f) ↔ IsCauSeq abv f := by
  simp only [IsCauSeq, Pi.neg_apply, ← neg_sub', abv_neg]

protected alias ⟨of_neg, neg⟩ := isCauSeq_neg

end IsCauSeq

/-- `CauSeq β abv` is the type of `β`-valued Cauchy sequences, with respect to the absolute value
function `abv`. -/
/-
**CauSeq** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：CauSeq {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] (β : 
Type*) [Ring β] (abv : β -> α) : Type _
参数：β : Type*；abv : β -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`CauSeq β abv` is the type of `β`-valued Cauchy sequences, with respect to the a
bsolute value
function `abv`.
-/
def CauSeq {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    (β : Type*) [Ring β] (abv : β → α) : Type _ :=
  { f : ℕ → β // IsCauSeq abv f }

namespace CauSeq

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

section Ring

variable [Ring β] {abv : β → α}

/-
**CauSeq.** 是 Mathlib 中的一个实例，位于命名空间 `CauSeq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeFun (CauSeq β abv) fun _ => ℕ → β :=
  ⟨Subtype.val⟩

@[ext]
/-
**CauSeq.ext** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：ext {f g : CauSeq β abv} (h : forall i, f i = g i) : f = g
参数：h : forall i, f i = g i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem ext {f g : CauSeq β abv} (h : ∀ i, f i = g i) : f = g := Subtype.ext (funext h)
/-
**CauSeq.isCauSeq** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：isCauSeq (f : CauSeq β abv) : IsCauSeq abv f
参数：f : CauSeq β abv。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem isCauSeq (f : CauSeq β abv) : IsCauSeq abv f :=
  f.2
/-
**CauSeq.cauchy** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：cauchy (f : CauSeq β abv) : forall {ε}, 0 < ε -> exists i, forall j >= i, 
abv (f j - f i) < ε
参数：f : CauSeq β abv。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem cauchy (f : CauSeq β abv) : ∀ {ε}, 0 < ε → ∃ i, ∀ j ≥ i, abv (f j - f i) < ε := @f.2

/-- Given a Cauchy sequence `f`, create a Cauchy sequence from a sequence `g` with
the same values as `f`. -/
/-
**CauSeq.ofEq** 是 Mathlib 中的一个定义，位于命名空间 `CauSeq`。
形式化陈述：ofEq (f : CauSeq β abv) (g : Nat -> β) (e : forall i, f i = g i) : CauSeq 
β abv
参数：f : CauSeq β abv；g : Nat -> β；e : forall i, f i = g i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a Cauchy sequence `f`, create a Cauchy sequence from a sequence `g` with
the same values as `f`.
-/
def ofEq (f : CauSeq β abv) (g : ℕ → β) (e : ∀ i, f i = g i) : CauSeq β abv :=
  ⟨g, fun ε => by rw [show g = f from (funext e).symm]; exact f.cauchy⟩

variable [IsAbsoluteValue abv]
/-
**CauSeq.cauchy** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：cauchy (f : CauSeq β abv) : forall {ε}, 0 < ε -> exists i, forall j >= i, 
abv (f j - f i) < ε
参数：f : CauSeq β abv。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem cauchy₂ (f : CauSeq β abv) {ε} :
    0 < ε → ∃ i, ∀ j ≥ i, ∀ k ≥ i, abv (f j - f k) < ε :=
  f.2.cauchy₂
/-
**CauSeq.cauchy** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：cauchy (f : CauSeq β abv) : forall {ε}, 0 < ε -> exists i, forall j >= i, 
abv (f j - f i) < ε
参数：f : CauSeq β abv。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem cauchy₃ (f : CauSeq β abv) {ε} : 0 < ε → ∃ i, ∀ j ≥ i, ∀ k ≥ j, abv (f k - f j) < ε :=
  f.2.cauchy₃
/-
**CauSeq.bounded** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：bounded (f : CauSeq β abv) : exists r, forall i, abv (f i) < r
参数：f : CauSeq β abv。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsCauSeq.bounded`：bounded (hf : IsCauSeq abv f) : exists r, forall i, ab
v (f i) < r
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem bounded (f : CauSeq β abv) : ∃ r, ∀ i, abv (f i) < r := f.2.bounded
/-
**CauSeq.bounded'** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：bounded' (f : CauSeq β abv) (x : α) : exists r > x, forall i, abv (f i) < 
r
参数：f : CauSeq β abv；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsCauSeq.bounded'`：bounded' (hf : IsCauSeq abv f) (x : α) : exists r > x
, forall i, abv (f i) < r
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem bounded' (f : CauSeq β abv) (x : α) : ∃ r > x, ∀ i, abv (f i) < r := f.2.bounded' x
/-
**CauSeq.** 是 Mathlib 中的一个实例，位于命名空间 `CauSeq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (CauSeq β abv) :=
  ⟨fun f g => ⟨f + g, f.2.add g.2⟩⟩

@[simp, norm_cast]
/-
**CauSeq.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：coe_add (f g : CauSeq β abv) : ⇑(f + g) = (f : Nat -> β) + g
参数：f g : CauSeq β abv。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_add (f g : CauSeq β abv) : ⇑(f + g) = (f : ℕ → β) + g :=
  rfl

@[simp, norm_cast]
/-
**CauSeq.add_apply** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：add_apply (f g : CauSeq β abv) (i : Nat) : (f + g) i = f i + g i
参数：f g : CauSeq β abv；i : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_apply (f g : CauSeq β abv) (i : ℕ) : (f + g) i = f i + g i :=
  rfl

variable (abv) in
/-- The constant Cauchy sequence. -/
/-
**CauSeq.const** 是 Mathlib 中的一个定义，位于命名空间 `CauSeq`。
形式化陈述：const (x : β) : CauSeq β abv
参数：x : β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `IsCauSeq.const`：const (x : β) : IsCauSeq abv fun _ => x

--- 原说明 ---
The constant Cauchy sequence.
-/
def const (x : β) : CauSeq β abv := ⟨fun _ ↦ x, IsCauSeq.const _⟩

/-- The constant Cauchy sequence -/
local notation "const" => const abv

@[simp, norm_cast]
/-
**CauSeq.coe_const** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：coe_const (x : β) : (const x : Nat -> β) = Function.const Nat x
参数：x : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_const (x : β) : (const x : ℕ → β) = Function.const ℕ x :=
  rfl

@[simp, norm_cast]
/-
**CauSeq.const_apply** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：const_apply (x : β) (i : Nat) : (const x : Nat -> β) i = x
参数：x : β；i : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_apply (x : β) (i : ℕ) : (const x : ℕ → β) i = x :=
  rfl
/-
**CauSeq.const_inj** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：const_inj {x y : β} : (const x : CauSeq β abv) = const y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem const_inj {x y : β} : (const x : CauSeq β abv) = const y ↔ x = y :=
  ⟨fun h => congr_arg (fun f : CauSeq β abv => (f : ℕ → β) 0) h, congr_arg _⟩
/-
**CauSeq.** 是 Mathlib 中的一个实例，位于命名空间 `CauSeq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (CauSeq β abv) :=
  ⟨const 0⟩
/-
**CauSeq.** 是 Mathlib 中的一个实例，位于命名空间 `CauSeq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (CauSeq β abv) :=
  ⟨const 1⟩
/-
**CauSeq.** 是 Mathlib 中的一个实例，位于命名空间 `CauSeq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (CauSeq β abv) :=
  ⟨0⟩

@[simp, norm_cast]
/-
**CauSeq.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：coe_zero : ⇑(0 : CauSeq β abv) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zero : ⇑(0 : CauSeq β abv) = 0 :=
  rfl

@[simp, norm_cast]
/-
**CauSeq.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：coe_one : ⇑(1 : CauSeq β abv) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : ⇑(1 : CauSeq β abv) = 1 :=
  rfl

@[simp, norm_cast]
/-
**CauSeq.zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：zero_apply (i) : (0 : CauSeq β abv) i = 0
参数：i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_apply (i) : (0 : CauSeq β abv) i = 0 :=
  rfl

@[simp, norm_cast]
/-
**CauSeq.one_apply** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：one_apply (i) : (1 : CauSeq β abv) i = 1
参数：i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_apply (i) : (1 : CauSeq β abv) i = 1 :=
  rfl

@[simp]
/-
**CauSeq.const_zero** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：const_zero : const 0 = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_zero : const 0 = 0 :=
  rfl

@[simp]
/-
**CauSeq.const_one** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：const_one : const 1 = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_one : const 1 = 1 :=
  rfl
/-
**CauSeq.const_add** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：const_add (x y : β) : const (x + y) = const x + const y
参数：x y : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_add (x y : β) : const (x + y) = const x + const y :=
  rfl
/-
**CauSeq.** 是 Mathlib 中的一个实例，位于命名空间 `CauSeq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul (CauSeq β abv) := ⟨fun f g ↦ ⟨f * g, f.2.mul g.2⟩⟩

@[simp, norm_cast]
/-
**CauSeq.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：coe_mul (f g : CauSeq β abv) : ⇑(f * g) = (f : Nat -> β) * g
参数：f g : CauSeq β abv。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul (f g : CauSeq β abv) : ⇑(f * g) = (f : ℕ → β) * g :=
  rfl

@[simp, norm_cast]
/-
**CauSeq.mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：mul_apply (f g : CauSeq β abv) (i : Nat) : (f * g) i = f i * g i
参数：f g : CauSeq β abv；i : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_apply (f g : CauSeq β abv) (i : ℕ) : (f * g) i = f i * g i :=
  rfl
/-
**CauSeq.const_mul** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：const_mul (x y : β) : const (x * y) = const x * const y
参数：x y : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_mul (x y : β) : const (x * y) = const x * const y :=
  rfl
/-
**CauSeq.** 是 Mathlib 中的一个实例，位于命名空间 `CauSeq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg (CauSeq β abv) := ⟨fun f ↦ ⟨-f, f.2.neg⟩⟩

@[simp, norm_cast]
/-
**CauSeq.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：coe_neg (f : CauSeq β abv) : ⇑(-f) = -f
参数：f : CauSeq β abv。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_neg (f : CauSeq β abv) : ⇑(-f) = -f :=
  rfl

@[simp, norm_cast]
/-
**CauSeq.neg_apply** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：neg_apply (f : CauSeq β abv) (i) : (-f) i = -f i
参数：f : CauSeq β abv；i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_apply (f : CauSeq β abv) (i) : (-f) i = -f i :=
  rfl
/-
**CauSeq.const_neg** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：const_neg (x : β) : const (-x) = -const x
参数：x : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_neg (x : β) : const (-x) = -const x :=
  rfl
/-
**CauSeq.** 是 Mathlib 中的一个实例，位于命名空间 `CauSeq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub (CauSeq β abv) :=
  ⟨fun f g => ofEq (f + -g) (fun x => f x - g x) fun i => by simp [sub_eq_add_neg]⟩

@[simp, norm_cast]
/-
**CauSeq.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：coe_sub (f g : CauSeq β abv) : ⇑(f - g) = (f : Nat -> β) - g
参数：f g : CauSeq β abv。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sub (f g : CauSeq β abv) : ⇑(f - g) = (f : ℕ → β) - g :=
  rfl

@[simp, norm_cast]
/-
**CauSeq.sub_apply** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：sub_apply (f g : CauSeq β abv) (i : Nat) : (f - g) i = f i - g i
参数：f g : CauSeq β abv；i : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_apply (f g : CauSeq β abv) (i : ℕ) : (f - g) i = f i - g i :=
  rfl
/-
**CauSeq.const_sub** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：const_sub (x y : β) : const (x - y) = const x - const y
参数：x y : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_sub (x y : β) : const (x - y) = const x - const y :=
  rfl

section SMul

variable {G : Type*} [SMul G β] [IsScalarTower G β β]

/-
**CauSeq.** 是 Mathlib 中的一个实例，位于命名空间 `CauSeq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul G (CauSeq β abv) :=
  ⟨fun a f => (ofEq (const (a • (1 : β)) * f) (a • (f : ℕ → β))) fun _ => smul_one_mul _ _⟩

@[simp, norm_cast]
/-
**CauSeq.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：coe_smul (a : G) (f : CauSeq β abv) : ⇑(a • f) = a • (f : Nat -> β)
参数：a : G；f : CauSeq β abv。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul (a : G) (f : CauSeq β abv) : ⇑(a • f) = a • (f : ℕ → β) :=
  rfl

@[simp, norm_cast]
/-
**CauSeq.smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：smul_apply (a : G) (f : CauSeq β abv) (i : Nat) : (a • f) i = a • f i
参数：a : G；f : CauSeq β abv；i : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_apply (a : G) (f : CauSeq β abv) (i : ℕ) : (a • f) i = a • f i :=
  rfl
/-
**CauSeq.const_smul** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：const_smul (a : G) (x : β) : const (a • x) = a • const x
参数：a : G；x : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_smul (a : G) (x : β) : const (a • x) = a • const x :=
  rfl
/-
**CauSeq.** 是 Mathlib 中的一个实例，位于命名空间 `CauSeq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsScalarTower G (CauSeq β abv) (CauSeq β abv) :=
  ⟨fun a f g => Subtype.ext <| smul_assoc a (f : ℕ → β) (g : ℕ → β)⟩

end SMul

/-
**CauSeq.addGroup** 是 Mathlib 中的一个实例，位于命名空间 `CauSeq`。
形式化陈述：addGroup : AddGroup (CauSeq β abv)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CauSeq.coe_add`：coe_add (f g : CauSeq β abv) : ⇑(f + g) = (f : Nat -> β)
 + g
· 使用定理 `CauSeq.coe_neg`：coe_neg (f : CauSeq β abv) : ⇑(-f) = -f
· 使用定理 `CauSeq.coe_sub`：coe_sub (f g : CauSeq β abv) : ⇑(f - g) = (f : Nat -> β)
 - g
-/
instance addGroup : AddGroup (CauSeq β abv) :=
  Function.Injective.addGroup Subtype.val Subtype.val_injective rfl coe_add coe_neg coe_sub
    (fun _ _ => coe_smul _ _) fun _ _ => coe_smul _ _
/-
**CauSeq.instNatCast** 是 Mathlib 中的一个实例，位于命名空间 `CauSeq`。
形式化陈述：instNatCast : NatCast (CauSeq β abv)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNatCast : NatCast (CauSeq β abv) := ⟨fun n => const n⟩
/-
**CauSeq.instIntCast** 是 Mathlib 中的一个实例，位于命名空间 `CauSeq`。
形式化陈述：instIntCast : IntCast (CauSeq β abv)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIntCast : IntCast (CauSeq β abv) := ⟨fun n => const n⟩
/-
**CauSeq.addGroupWithOne** 是 Mathlib 中的一个实例，位于命名空间 `CauSeq`。
形式化陈述：addGroupWithOne : AddGroupWithOne (CauSeq β abv)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CauSeq.coe_add`：coe_add (f g : CauSeq β abv) : ⇑(f + g) = (f : Nat -> β)
 + g
· 使用定理 `CauSeq.coe_neg`：coe_neg (f : CauSeq β abv) : ⇑(-f) = -f
· 使用定理 `CauSeq.coe_sub`：coe_sub (f g : CauSeq β abv) : ⇑(f - g) = (f : Nat -> β)
 - g
-/
instance addGroupWithOne : AddGroupWithOne (CauSeq β abv) :=
  Function.Injective.addGroupWithOne Subtype.val Subtype.val_injective rfl rfl
  coe_add coe_neg coe_sub
  (by intros; rfl)
  (by intros; rfl)
  (by intros; rfl)
  (by intros; rfl)
/-
**CauSeq.** 是 Mathlib 中的一个实例，位于命名空间 `CauSeq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Pow (CauSeq β abv) ℕ :=
  ⟨fun f n =>
    (ofEq (npowRec n f) fun i => f i ^ n) <| by induction n <;> simp [*, npowRec, pow_succ]⟩

@[simp, norm_cast]
/-
**CauSeq.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：coe_pow (f : CauSeq β abv) (n : Nat) : ⇑(f ^ n) = (f : Nat -> β) ^ n
参数：f : CauSeq β abv；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_pow (f : CauSeq β abv) (n : ℕ) : ⇑(f ^ n) = (f : ℕ → β) ^ n :=
  rfl

@[simp, norm_cast]
/-
**CauSeq.pow_apply** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：pow_apply (f : CauSeq β abv) (n i : Nat) : (f ^ n) i = f i ^ n
参数：f : CauSeq β abv；n i : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pow_apply (f : CauSeq β abv) (n i : ℕ) : (f ^ n) i = f i ^ n :=
  rfl
/-
**CauSeq.const_pow** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：const_pow (x : β) (n : Nat) : const (x ^ n) = const x ^ n
参数：x : β；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_pow (x : β) (n : ℕ) : const (x ^ n) = const x ^ n :=
  rfl
/-
**CauSeq.ring** 是 Mathlib 中的一个实例，位于命名空间 `CauSeq`。
形式化陈述：ring : Ring (CauSeq β abv)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CauSeq.coe_add`：coe_add (f g : CauSeq β abv) : ⇑(f + g) = (f : Nat -> β)
 + g
· 使用定理 `CauSeq.coe_mul`：coe_mul (f g : CauSeq β abv) : ⇑(f * g) = (f : Nat -> β)
 * g
· 使用定理 `CauSeq.coe_neg`：coe_neg (f : CauSeq β abv) : ⇑(-f) = -f
· 使用定理 `CauSeq.coe_sub`：coe_sub (f g : CauSeq β abv) : ⇑(f - g) = (f : Nat -> β)
 - g
· 使用定理 `CauSeq.coe_pow`：coe_pow (f : CauSeq β abv) (n : Nat) : ⇑(f ^ n) = (f : N
at -> β) ^ n
-/
instance ring : Ring (CauSeq β abv) :=
  Function.Injective.ring Subtype.val Subtype.val_injective rfl rfl coe_add coe_mul coe_neg coe_sub
    (fun _ _ => coe_smul _ _) (fun _ _ => coe_smul _ _) coe_pow (fun _ => rfl) fun _ => rfl
/-
**CauSeq.** 是 Mathlib 中的一个实例，位于命名空间 `CauSeq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {β : Type*} [CommRing β] {abv : β → α} [IsAbsoluteValue abv] : CommRing (CauSeq β abv) :=
  { CauSeq.ring with
    mul_comm := fun a b => ext fun n => by simp [mul_comm] }

/-- `LimZero f` holds when `f` approaches 0. -/
/-
**CauSeq.LimZero** 是 Mathlib 中的一个定义，位于命名空间 `CauSeq`。
形式化陈述：LimZero {abv : β -> α} (f : CauSeq β abv) : Prop
参数：f : CauSeq β abv。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LimZero f` holds when `f` approaches 0.
-/
def LimZero {abv : β → α} (f : CauSeq β abv) : Prop :=
  ∀ ε > 0, ∃ i, ∀ j ≥ i, abv (f j) < ε
/-
**CauSeq.add_limZero** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：add_limZero {f g : CauSeq β abv} (hf : LimZero f) (hg : LimZero g) : LimZe
ro (f + g) | ε, ε0 => (exists_forall_ge_and (hf _ <| half_pos ε0) (hg _ <| half_
pos ε0)).imp fun _ H j ij => by let ⟨H₁, H₂⟩
参数：hf : LimZero f；hg : LimZero g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_halves`：∀ {K : Type u_1} [inst : DivisionSemiring K] [NeZero 2] (a :
 K), a / 2 + a / 2 = a
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用引理 `IsAbsoluteValue.abv_add`：abv_add (x y) : abv (x + y) <= abv x + abv y
· 使用定理 `add_lt_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftStrictMono α] [AddRightStrictMono α] {a b c d : α},   a < b → c < d → a + c < 
…
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
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `exists_forall_ge_and`：exists_forall_ge_and {p q : α -> Prop} : (exists i
, forall j >= i, p j) -> (exists i, forall j >= i, q j) -> exists i, forall j >=
 i, p j ∧ …
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
-/
theorem add_limZero {f g : CauSeq β abv} (hf : LimZero f) (hg : LimZero g) : LimZero (f + g)
  | ε, ε0 =>
    (exists_forall_ge_and (hf _ <| half_pos ε0) (hg _ <| half_pos ε0)).imp fun _ H j ij => by
      let ⟨H₁, H₂⟩ := H _ ij
      simpa [add_halves ε] using lt_of_le_of_lt (abv_add abv _ _) (add_lt_add H₁ H₂)
/-
**CauSeq.mul_limZero_right** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：mul_limZero_right (f : CauSeq β abv) {g} (hg : LimZero g) : LimZero (f * g
) | ε, ε0 => let ⟨F, F0, hF⟩
参数：f : CauSeq β abv；hg : LimZero g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CauSeq.bounded'`：bounded' (f : CauSeq β abv) (x : α) : exists r > x, for
all i, abv (f i) < r
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `mul_lt_mul'`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 :
 Preorder α] {a b c d : α} [PosMulStrictMono α]   [MulPosMono α], a ≤ b → c < d 
→…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `IsAbsoluteValue.abv_nonneg`：abv_nonneg (x) : 0 <= abv x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsAbsoluteValue.abv_mul`：abv_mul (x y) : abv (x * y) = abv x * abv y
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
-/
theorem mul_limZero_right (f : CauSeq β abv) {g} (hg : LimZero g) : LimZero (f * g)
  | ε, ε0 =>
    let ⟨F, F0, hF⟩ := f.bounded' 0
    (hg _ <| div_pos ε0 F0).imp fun _ H j ij => by
      have := mul_lt_mul' (le_of_lt <| hF j) (H _ ij) (abv_nonneg abv _) F0
      rwa [mul_comm F, div_mul_cancel₀ _ (ne_of_gt F0), ← abv_mul] at this
/-
**CauSeq.mul_limZero_left** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：mul_limZero_left {f} (g : CauSeq β abv) (hg : LimZero f) : LimZero (f * g)
 | ε, ε0 => let ⟨G, G0, hG⟩
参数：g : CauSeq β abv；hg : LimZero f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CauSeq.bounded'`：bounded' (f : CauSeq β abv) (x : α) : exists r > x, for
all i, abv (f i) < r
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `mul_lt_mul''`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b c d : α} [in
st_1 : Preorder α] [PosMulStrictMono α] [MulPosMono α],   a < b → c < d → 0 ≤ a 
→ …
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用引理 `IsAbsoluteValue.abv_nonneg`：abv_nonneg (x) : 0 <= abv x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsAbsoluteValue.abv_mul`：abv_mul (x y) : abv (x * y) = abv x * abv y
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
-/
theorem mul_limZero_left {f} (g : CauSeq β abv) (hg : LimZero f) : LimZero (f * g)
  | ε, ε0 =>
    let ⟨G, G0, hG⟩ := g.bounded' 0
    (hg _ <| div_pos ε0 G0).imp fun _ H j ij => by
      have := mul_lt_mul'' (H _ ij) (hG j) (abv_nonneg abv _) (abv_nonneg abv _)
      rwa [div_mul_cancel₀ _ (ne_of_gt G0), ← abv_mul] at this
/-
**CauSeq.neg_limZero** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：neg_limZero {f : CauSeq β abv} (hf : LimZero f) : LimZero (-f)
参数：hf : LimZero f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_one_mul`：neg_one_mul (a : α) : -1 * a = -a
· 使用定理 `CauSeq.mul_limZero_right`：mul_limZero_right (f : CauSeq β abv) {g} (hg :
 LimZero g) : LimZero (f * g) | ε, ε0 => let ⟨F, F0, hF⟩
-/
theorem neg_limZero {f : CauSeq β abv} (hf : LimZero f) : LimZero (-f) := by
  rw [← neg_one_mul f]
  exact mul_limZero_right _ hf
/-
**CauSeq.sub_limZero** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：sub_limZero {f g : CauSeq β abv} (hf : LimZero f) (hg : LimZero g) : LimZe
ro (f - g)
参数：hf : LimZero f；hg : LimZero g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `CauSeq.add_limZero`：add_limZero {f g : CauSeq β abv} (hf : LimZero f) (h
g : LimZero g) : LimZero (f + g) | ε, ε0 => (exists_forall_ge_and (hf _ <| half_
pos ε0) …
· 使用定理 `CauSeq.neg_limZero`：neg_limZero {f : CauSeq β abv} (hf : LimZero f) : Li
mZero (-f)
-/
theorem sub_limZero {f g : CauSeq β abv} (hf : LimZero f) (hg : LimZero g) : LimZero (f - g) := by
  simpa only [sub_eq_add_neg] using add_limZero hf (neg_limZero hg)
/-
**CauSeq.limZero_sub_rev** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：limZero_sub_rev {f g : CauSeq β abv} (hfg : LimZero (f - g)) : LimZero (g 
- f)
参数：hfg : LimZero (f - g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `CauSeq.neg_limZero`：neg_limZero {f : CauSeq β abv} (hf : LimZero f) : Li
mZero (-f)
-/
theorem limZero_sub_rev {f g : CauSeq β abv} (hfg : LimZero (f - g)) : LimZero (g - f) := by
  simpa using neg_limZero hfg
/-
**CauSeq.zero_limZero** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Field α] [inst_1 : LinearOrder α] 
[inst_2 : IsStrictOrderedRing α]   [inst_3 : Ring β] {abv : β → α} [inst_4 : IsA
bsoluteValue abv], CauSeq.LimZero 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsAbsoluteValue.abv_zero`：abv_zero : abv 0 = 0
-/
theorem zero_limZero : LimZero (0 : CauSeq β abv)
  | ε, ε0 => ⟨0, fun j _ => by simpa [abv_zero abv] using ε0⟩
/-
**CauSeq.const_limZero** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：const_limZero {x : β} : LimZero (const x) ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `IsAbsoluteValue.abv_eq_zero`：abv_eq_zero {x} : abv x = 0 ↔ x = 0
· 使用引理 `eq_of_le_of_forall_lt_imp_le_of_dense`：eq_of_le_of_forall_lt_imp_le_of_d
ense (h₁ : a₂ <= a₁) (h₂ : forall a, a₂ < a -> a₁ <= a) : a₁ = a₂
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
· 使用引理 `IsAbsoluteValue.abv_nonneg`：abv_nonneg (x) : 0 <= abv x
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `CauSeq.zero_limZero`：∀ {α : Type u_1} {β : Type u_2} [inst : Field α] [i
nst_1 : LinearOrder α] [inst_2 : IsStrictOrderedRing α]   [inst_3 : Ring β] {abv
 : β → α}…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem const_limZero {x : β} : LimZero (const x) ↔ x = 0 :=
  ⟨fun H =>
    (abv_eq_zero abv).1 <|
      (eq_of_le_of_forall_lt_imp_le_of_dense (abv_nonneg abv _)) fun _ ε0 =>
        let ⟨_, hi⟩ := H _ ε0
        le_of_lt <| hi _ le_rfl,
    fun e => e.symm ▸ zero_limZero⟩
/-
**CauSeq.equiv** 是 Mathlib 中的一个实例，位于命名空间 `CauSeq`。
形式化陈述：equiv : Setoid (CauSeq β abv)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance equiv : Setoid (CauSeq β abv) :=
  ⟨fun f g => LimZero (f - g),
    ⟨fun f => by simp [zero_limZero],
    fun f ε hε => by simpa using neg_limZero f ε hε,
    fun fg gh => by simpa using add_limZero fg gh⟩⟩
/-
**CauSeq.add_equiv_add** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：add_equiv_add {f1 f2 g1 g2 : CauSeq β abv} (hf : f1 ≈ f2) (hg : g1 ≈ g2) :
 f1 + g1 ≈ f2 + g2
参数：hf : f1 ≈ f2；hg : g1 ≈ g2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CauSeq.add_limZero`：add_limZero {f g : CauSeq β abv} (hf : LimZero f) (h
g : LimZero g) : LimZero (f + g) | ε, ε0 => (exists_forall_ge_and (hf _ <| half_
pos ε0) …
-/
theorem add_equiv_add {f1 f2 g1 g2 : CauSeq β abv} (hf : f1 ≈ f2) (hg : g1 ≈ g2) :
    f1 + g1 ≈ f2 + g2 := by simpa only [← add_sub_add_comm] using! add_limZero hf hg
/-
**CauSeq.neg_equiv_neg** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：neg_equiv_neg {f g : CauSeq β abv} (hf : f ≈ g) : -f ≈ -g
参数：hf : f ≈ g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_sub'`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b : α), -
(a - b) = -a - -b
· 使用定理 `CauSeq.neg_limZero`：neg_limZero {f : CauSeq β abv} (hf : LimZero f) : Li
mZero (-f)
-/
theorem neg_equiv_neg {f g : CauSeq β abv} (hf : f ≈ g) : -f ≈ -g := by
  simpa only [neg_sub'] using! neg_limZero hf
/-
**CauSeq.sub_equiv_sub** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：sub_equiv_sub {f1 f2 g1 g2 : CauSeq β abv} (hf : f1 ≈ f2) (hg : g1 ≈ g2) :
 f1 - g1 ≈ f2 - g2
参数：hf : f1 ≈ f2；hg : g1 ≈ g2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `CauSeq.add_equiv_add`：add_equiv_add {f1 f2 g1 g2 : CauSeq β abv} (hf : f
1 ≈ f2) (hg : g1 ≈ g2) : f1 + g1 ≈ f2 + g2
· 使用定理 `CauSeq.neg_equiv_neg`：neg_equiv_neg {f g : CauSeq β abv} (hf : f ≈ g) : 
-f ≈ -g
-/
theorem sub_equiv_sub {f1 f2 g1 g2 : CauSeq β abv} (hf : f1 ≈ f2) (hg : g1 ≈ g2) :
    f1 - g1 ≈ f2 - g2 := by simpa only [sub_eq_add_neg] using add_equiv_add hf (neg_equiv_neg hg)
/-
**CauSeq.equiv_def** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equiv_def₃ {f g : CauSeq β abv} (h : f ≈ g) {ε : α} (ε0 : 0 < ε) :
    ∃ i, ∀ j ≥ i, ∀ k ≥ j, abv (f k - g j) < ε :=
  (exists_forall_ge_and (h _ <| half_pos ε0) (f.cauchy₃ <| half_pos ε0)).imp fun _ H j ij k jk => by
    let ⟨h₁, h₂⟩ := H _ ij
    have := lt_of_le_of_lt (abv_add abv (f j - g j) _) (add_lt_add h₁ (h₂ _ jk))
    rwa [sub_add_sub_cancel', add_halves] at this
/-
**CauSeq.limZero_congr** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：limZero_congr {f g : CauSeq β abv} (h : f ≈ g) : LimZero f ↔ LimZero g
参数：h : f ≈ g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `CauSeq.add_limZero`：add_limZero {f g : CauSeq β abv} (hf : LimZero f) (h
g : LimZero g) : LimZero (f + g) | ε, ε0 => (exists_forall_ge_and (hf _ <| half_
pos ε0) …
· 使用定理 `Setoid.symm`：∀ {α : Sort u} [inst : Setoid α] {a b : α}, a ≈ b → b ≈ a
-/
theorem limZero_congr {f g : CauSeq β abv} (h : f ≈ g) : LimZero f ↔ LimZero g :=
  ⟨fun l => by simpa using add_limZero (Setoid.symm h) l, fun l => by simpa using add_limZero h l⟩
/-
**CauSeq.abv_pos_of_not_limZero** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：abv_pos_of_not_limZero {f : CauSeq β abv} (hf : ¬LimZero f) : exists K > 0
, exists i, forall j >= i, K <= abv (f j)
参数：hf : ¬LimZero f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `CauSeq.cauchy₃`：cauchy₃ (f : CauSeq β abv) {ε} : 0 < ε -> exists i, fora
ll j >= i, forall k >= j, abv (f k - f j) < ε
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用引理 `IsAbsoluteValue.abv_add`：abv_add (x y) : abv (x + y) <= abv x + abv y
· 使用定理 `add_lt_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftStrictMono α] [AddRightStrictMono α] {a b c d : α},   a < b → c < d → a + c < 
…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
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
（共 34 条，此处仅展示前 30 条）
-/
theorem abv_pos_of_not_limZero {f : CauSeq β abv} (hf : ¬LimZero f) :
    ∃ K > 0, ∃ i, ∀ j ≥ i, K ≤ abv (f j) := by
  by_contra nk
  refine hf fun ε ε0 => ?_
  simp only [not_exists, not_and, not_forall, not_le] at nk
  obtain ⟨i, hi⟩ := f.cauchy₃ (half_pos ε0)
  rcases nk _ (half_pos ε0) i with ⟨j, ij, hj⟩
  refine ⟨j, fun k jk => ?_⟩
  have := lt_of_le_of_lt (abv_add abv _ _) (add_lt_add (hi j ij k jk) hj)
  rwa [sub_add_cancel, add_halves] at this
/-
**CauSeq.of_near** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：of_near (f : Nat -> β) (g : CauSeq β abv) (h : forall ε > 0, exists i, for
all j >= i, abv (f j - g j) < ε) : IsCauSeq abv f | ε, ε0 => let ⟨i, hi⟩
参数：f : Nat -> β；g : CauSeq β abv；h : forall ε > 0, exists i, forall j >= i, abv 
(f j - g j) < ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `exists_forall_ge_and`：exists_forall_ge_and {p q : α -> Prop} : (exists i
, forall j >= i, p j) -> (exists i, forall j >= i, q j) -> exists i, forall j >=
 i, p j ∧ …
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `CauSeq.cauchy₃`：cauchy₃ (f : CauSeq β abv) {ε} : 0 < ε -> exists i, fora
ll j >= i, forall k >= j, abv (f k - f j) < ε
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用引理 `IsAbsoluteValue.abv_add`：abv_add (x y) : abv (x + y) <= abv x + abv y
· 使用定理 `add_lt_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftStrictMono α] [AddRightStrictMono α] {a b c d : α},   a < b → c < d → a + c < 
…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
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
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsAbsoluteValue.abv_sub`：abv_sub (a b : R) : abv (a - b) = abv (b - a)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Field.isDomain`：∀ {K : Type u_1} [inst : Field K], IsDomain K
· 使用定理 `sub_add_sub_cancel`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : G), a 
- b + (b - c) = a - c
（共 34 条，此处仅展示前 30 条）
-/
theorem of_near (f : ℕ → β) (g : CauSeq β abv) (h : ∀ ε > 0, ∃ i, ∀ j ≥ i, abv (f j - g j) < ε) :
    IsCauSeq abv f
  | ε, ε0 =>
    let ⟨i, hi⟩ := exists_forall_ge_and (h _ (half_pos <| half_pos ε0)) (g.cauchy₃ <| half_pos ε0)
    ⟨i, fun j ij => by
      obtain ⟨h₁, h₂⟩ := hi _ le_rfl; rw [abv_sub abv] at h₁
      have := lt_of_le_of_lt (abv_add abv _ _) (add_lt_add (hi _ ij).1 h₁)
      have := lt_of_le_of_lt (abv_add abv _ _) (add_lt_add this (h₂ _ ij))
      rwa [add_halves, add_halves, add_right_comm, sub_add_sub_cancel, sub_add_sub_cancel] at this⟩
/-
**CauSeq.not_limZero_of_not_congr_zero** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：not_limZero_of_not_congr_zero {f : CauSeq _ abv} (hf : ¬f ≈ 0) : ¬LimZero 
f
参数：hf : ¬f ≈ 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem not_limZero_of_not_congr_zero {f : CauSeq _ abv} (hf : ¬f ≈ 0) : ¬LimZero f := by
  intro h
  have : LimZero (f - 0) := by simp [h]
  exact hf this
/-
**CauSeq.mul_equiv_zero** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：mul_equiv_zero (g : CauSeq _ abv) {f : CauSeq _ abv} (hf : f ≈ 0) : g * f 
≈ 0
参数：g : CauSeq _ abv；hf : f ≈ 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CauSeq.mul_limZero_right`：mul_limZero_right (f : CauSeq β abv) {g} (hg :
 LimZero g) : LimZero (f * g) | ε, ε0 => let ⟨F, F0, hF⟩
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
-/
theorem mul_equiv_zero (g : CauSeq _ abv) {f : CauSeq _ abv} (hf : f ≈ 0) : g * f ≈ 0 :=
  have : LimZero (f - 0) := hf
  have : LimZero (g * f) := mul_limZero_right _ <| by simpa
  show LimZero (g * f - 0) by simpa
/-
**CauSeq.mul_equiv_zero'** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：mul_equiv_zero' (g : CauSeq _ abv) {f : CauSeq _ abv} (hf : f ≈ 0) : f * g
 ≈ 0
参数：g : CauSeq _ abv；hf : f ≈ 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CauSeq.mul_limZero_left`：mul_limZero_left {f} (g : CauSeq β abv) (hg : L
imZero f) : LimZero (f * g) | ε, ε0 => let ⟨G, G0, hG⟩
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
-/
theorem mul_equiv_zero' (g : CauSeq _ abv) {f : CauSeq _ abv} (hf : f ≈ 0) : f * g ≈ 0 :=
  have : LimZero (f - 0) := hf
  have : LimZero (f * g) := mul_limZero_left _ <| by simpa
  show LimZero (f * g - 0) by simpa
/-
**CauSeq.mul_not_equiv_zero** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：mul_not_equiv_zero {f g : CauSeq _ abv} (hf : ¬f ≈ 0) (hg : ¬g ≈ 0) : ¬f *
 g ≈ 0
参数：hf : ¬f ≈ 0；hg : ¬g ≈ 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `CauSeq.abv_pos_of_not_limZero`：abv_pos_of_not_limZero {f : CauSeq β abv}
 (hf : ¬LimZero f) : exists K > 0, exists i, forall j >= i, K <= abv (f j)
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用引理 `IsAbsoluteValue.abv_mul`：abv_mul (x y) : abv (x * y) = abv x * abv y
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `IsAbsoluteValue.abv_nonneg`：abv_nonneg (x) : 0 <= abv x
-/
theorem mul_not_equiv_zero {f g : CauSeq _ abv} (hf : ¬f ≈ 0) (hg : ¬g ≈ 0) : ¬f * g ≈ 0 :=
  fun (this : LimZero (f * g - 0)) => by
  have hlz : LimZero (f * g) := by simpa
  have hf' : ¬LimZero f := by simpa using show ¬LimZero (f - 0) from hf
  have hg' : ¬LimZero g := by simpa using show ¬LimZero (g - 0) from hg
  rcases abv_pos_of_not_limZero hf' with ⟨a1, ha1, N1, hN1⟩
  rcases abv_pos_of_not_limZero hg' with ⟨a2, ha2, N2, hN2⟩
  have : 0 < a1 * a2 := mul_pos ha1 ha2
  obtain ⟨N, hN⟩ := hlz _ this
  let i := max N (max N1 N2)
  have hN' := hN i (le_max_left _ _)
  have hN1' := hN1 i (le_trans (le_max_left _ _) (le_max_right _ _))
  have hN1' := hN2 i (le_trans (le_max_right _ _) (le_max_right _ _))
  apply not_le_of_gt hN'
  change _ ≤ abv (_ * _)
  rw [abv_mul abv]
  gcongr
/-
**CauSeq.const_equiv** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：const_equiv {x y : β} : const x ≈ const y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CauSeq.const_sub`：const_sub (x y : β) : const (x - y) = const x - const 
y
· 使用定理 `CauSeq.const_limZero`：const_limZero {x : β} : LimZero (const x) ↔ x = 0
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem const_equiv {x y : β} : const x ≈ const y ↔ x = y :=
  show LimZero _ ↔ _ by rw [← const_sub, const_limZero, sub_eq_zero]
/-
**CauSeq.mul_equiv_mul** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：mul_equiv_mul {f1 f2 g1 g2 : CauSeq β abv} (hf : f1 ≈ f2) (hg : g1 ≈ g2) :
 f1 * g1 ≈ f2 * g2
参数：hf : f1 ≈ f2；hg : g1 ≈ g2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `sub_add_sub_cancel`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : G), a 
- b + (b - c) = a - c
· 使用定理 `CauSeq.add_limZero`：add_limZero {f g : CauSeq β abv} (hf : LimZero f) (h
g : LimZero g) : LimZero (f + g) | ε, ε0 => (exists_forall_ge_and (hf _ <| half_
pos ε0) …
· 使用定理 `CauSeq.mul_limZero_left`：mul_limZero_left {f} (g : CauSeq β abv) (hg : L
imZero f) : LimZero (f * g) | ε, ε0 => let ⟨G, G0, hG⟩
· 使用定理 `CauSeq.mul_limZero_right`：mul_limZero_right (f : CauSeq β abv) {g} (hg :
 LimZero g) : LimZero (f * g) | ε, ε0 => let ⟨F, F0, hF⟩
-/
theorem mul_equiv_mul {f1 f2 g1 g2 : CauSeq β abv} (hf : f1 ≈ f2) (hg : g1 ≈ g2) :
    f1 * g1 ≈ f2 * g2 := by
  simpa only [mul_sub, sub_mul, sub_add_sub_cancel]
    using! add_limZero (mul_limZero_left g1 hf) (mul_limZero_right f2 hg)
/-
**CauSeq.smul_equiv_smul** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：smul_equiv_smul {G : Type*} [SMul G β] [IsScalarTower G β β] {f1 f2 : CauS
eq β abv} (c : G) (hf : f1 ≈ f2) : c • f1 ≈ c • f2
参数：c : G；hf : f1 ≈ f2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_one_mul`：smul_one_mul {M N} [MulOneClass N] [SMul M N] [IsScalarTow
er M N N] (x : M) (y : N) : x • (1 : N) * y = x • y
· 使用定理 `CauSeq.instIsScalarTower`：∀ {α : Type u_1} {β : Type u_2} [inst : Field 
α] [inst_1 : LinearOrder α] [inst_2 : IsStrictOrderedRing α]   [inst_3 : Ring β]
 {abv : β → α}…
· 使用定理 `CauSeq.mul_equiv_mul`：mul_equiv_mul {f1 f2 g1 g2 : CauSeq β abv} (hf : f
1 ≈ f2) (hg : g1 ≈ g2) : f1 * g1 ≈ f2 * g2
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CauSeq.const_equiv`：const_equiv {x y : β} : const x ≈ const y ↔ x = y
-/
theorem smul_equiv_smul {G : Type*} [SMul G β] [IsScalarTower G β β] {f1 f2 : CauSeq β abv} (c : G)
    (hf : f1 ≈ f2) : c • f1 ≈ c • f2 := by
  simpa [const_smul, smul_one_mul _ _] using
    mul_equiv_mul (const_equiv.mpr <| Eq.refl <| c • (1 : β)) hf
/-
**CauSeq.pow_equiv_pow** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：pow_equiv_pow {f1 f2 : CauSeq β abv} (hf : f1 ≈ f2) (n : Nat) : f1 ^ n ≈ f
2 ^ n
参数：hf : f1 ≈ f2；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `CauSeq.mul_equiv_mul`：mul_equiv_mul {f1 f2 g1 g2 : CauSeq β abv} (hf : f
1 ≈ f2) (hg : g1 ≈ g2) : f1 * g1 ≈ f2 * g2
-/
theorem pow_equiv_pow {f1 f2 : CauSeq β abv} (hf : f1 ≈ f2) (n : ℕ) : f1 ^ n ≈ f2 ^ n := by
  induction n with
  | zero => simp only [pow_zero, Setoid.refl]
  | succ n ih => simpa only [pow_succ'] using mul_equiv_mul hf ih

end Ring

section IsDomain

variable [Ring β] [IsDomain β] (abv : β → α) [IsAbsoluteValue abv]

/-
**CauSeq.one_not_equiv_zero** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：one_not_equiv_zero : ¬const abv 1 ≈ const abv 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `IsAbsoluteValue.abv_nonneg`：abv_nonneg (x) : 0 <= abv x
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `IsAbsoluteValue.abv_eq_zero`：abv_eq_zero {x} : abv x = 0 ↔ x = 0
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
-/
theorem one_not_equiv_zero : ¬const abv 1 ≈ const abv 0 := fun h =>
  have : ∀ ε > 0, ∃ i, ∀ k, i ≤ k → abv (1 - 0) < ε := h
  have h1 : abv 1 ≤ 0 :=
    le_of_not_gt fun h2 : 0 < abv 1 =>
      (Exists.elim (this _ h2)) fun i hi => lt_irrefl (abv 1) <| by simpa using hi _ le_rfl
  have h2 : 0 ≤ abv 1 := abv_nonneg abv _
  have : abv 1 = 0 := le_antisymm h1 h2
  have : (1 : β) = 0 := (abv_eq_zero abv).mp this
  absurd this one_ne_zero

end IsDomain

section DivisionRing

variable [DivisionRing β] {abv : β → α} [IsAbsoluteValue abv]

/-
**CauSeq.inv_aux** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：inv_aux {f : CauSeq β abv} (hf : ¬LimZero f) : forall ε > 0, exists i, for
all j >= i, abv ((f j)⁻¹ - (f i)⁻¹) < ε | _, ε0 => let ⟨_, K0, HK⟩
参数：hf : ¬LimZero f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CauSeq.abv_pos_of_not_limZero`：abv_pos_of_not_limZero {f : CauSeq β abv}
 (hf : ¬LimZero f) : exists K > 0, exists i, forall j >= i, K <= abv (f j)
· 使用定理 `rat_inv_continuous_lemma`：rat_inv_continuous_lemma {β : Type*} [Division
Ring β] (abv : β -> α) [IsAbsoluteValue abv] {ε K : α} (ε0 : 0 < ε) (K0 : 0 < K)
 : exists δ > …
· 使用引理 `exists_forall_ge_and`：exists_forall_ge_and {p q : α -> Prop} : (exists i
, forall j >= i, p j) -> (exists i, forall j >= i, q j) -> exists i, forall j >=
 i, p j ∧ …
· 使用定理 `CauSeq.cauchy₃`：cauchy₃ (f : CauSeq β abv) {ε} : 0 < ε -> exists i, fora
ll j >= i, forall k >= j, abv (f k - f j) < ε
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem inv_aux {f : CauSeq β abv} (hf : ¬LimZero f) :
    ∀ ε > 0, ∃ i, ∀ j ≥ i, abv ((f j)⁻¹ - (f i)⁻¹) < ε
  | _, ε0 =>
    let ⟨_, K0, HK⟩ := abv_pos_of_not_limZero hf
    let ⟨_, δ0, Hδ⟩ := rat_inv_continuous_lemma abv ε0 K0
    let ⟨i, H⟩ := exists_forall_ge_and HK (f.cauchy₃ δ0)
    ⟨i, fun _ ij =>
      let ⟨iK, H'⟩ := H _ le_rfl
      Hδ (H _ ij).1 iK (H' _ ij)⟩

/-- Given a Cauchy sequence `f` with nonzero limit, create a Cauchy sequence with values equal to
the inverses of the values of `f`. -/
/-
**CauSeq.inv** 是 Mathlib 中的一个定义，位于命名空间 `CauSeq`。
形式化陈述：inv (f : CauSeq β abv) (hf : ¬LimZero f) : CauSeq β abv
参数：f : CauSeq β abv；hf : ¬LimZero f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CauSeq.inv_aux`：inv_aux {f : CauSeq β abv} (hf : ¬LimZero f) : forall ε 
> 0, exists i, forall j >= i, abv ((f j)⁻¹ - (f i)⁻¹) < ε | _, ε0 => let ⟨_, K0,
 HK⟩

--- 原说明 ---
Given a Cauchy sequence `f` with nonzero limit, create a Cauchy sequence with va
lues equal to
the inverses of the values of `f`.
-/
def inv (f : CauSeq β abv) (hf : ¬LimZero f) : CauSeq β abv :=
  ⟨_, inv_aux hf⟩

@[simp, norm_cast]
/-
**CauSeq.coe_inv** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：coe_inv {f : CauSeq β abv} (hf) : ⇑(inv f hf) = (f : Nat -> β)⁻¹
参数：hf。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inv {f : CauSeq β abv} (hf) : ⇑(inv f hf) = (f : ℕ → β)⁻¹ :=
  rfl

@[simp, norm_cast]
/-
**CauSeq.inv_apply** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：inv_apply {f : CauSeq β abv} (hf i) : inv f hf i = (f i)⁻¹
参数：hf i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_apply {f : CauSeq β abv} (hf i) : inv f hf i = (f i)⁻¹ :=
  rfl
/-
**CauSeq.inv_mul_cancel** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：inv_mul_cancel {f : CauSeq β abv} (hf) : inv f hf * f ≈ 1
参数：hf。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CauSeq.abv_pos_of_not_limZero`：abv_pos_of_not_limZero {f : CauSeq β abv}
 (hf : ¬LimZero f) : exists K > 0, exists i, forall j >= i, K <= abv (f j)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsAbsoluteValue.abv_pos`：abv_pos {a : R} : 0 < abv a ↔ a != 0
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `IsAbsoluteValue.abv_zero`：abv_zero : abv 0 = 0
-/
theorem inv_mul_cancel {f : CauSeq β abv} (hf) : inv f hf * f ≈ 1 := fun ε ε0 =>
  let ⟨K, K0, i, H⟩ := abv_pos_of_not_limZero hf
  ⟨i, fun j ij => by simpa [(abv_pos abv).1 (lt_of_lt_of_le K0 (H _ ij)), abv_zero abv] using ε0⟩
/-
**CauSeq.mul_inv_cancel** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：mul_inv_cancel {f : CauSeq β abv} (hf) : f * inv f hf ≈ 1
参数：hf。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CauSeq.abv_pos_of_not_limZero`：abv_pos_of_not_limZero {f : CauSeq β abv}
 (hf : ¬LimZero f) : exists K > 0, exists i, forall j >= i, K <= abv (f j)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsAbsoluteValue.abv_pos`：abv_pos {a : R} : 0 < abv a ↔ a != 0
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `IsAbsoluteValue.abv_zero`：abv_zero : abv 0 = 0
-/
theorem mul_inv_cancel {f : CauSeq β abv} (hf) : f * inv f hf ≈ 1 := fun ε ε0 =>
  let ⟨K, K0, i, H⟩ := abv_pos_of_not_limZero hf
  ⟨i, fun j ij => by simpa [(abv_pos abv).1 (lt_of_lt_of_le K0 (H _ ij)), abv_zero abv] using ε0⟩
/-
**CauSeq.const_inv** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：const_inv {x : β} (hx : x != 0) : const abv x⁻¹ = inv (const abv x) (by rw
a [const_limZero])
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_inv {x : β} (hx : x ≠ 0) :
    const abv x⁻¹ = inv (const abv x) (by rwa [const_limZero]) :=
  rfl

end DivisionRing

section Abs

/-- The constant Cauchy sequence -/
local notation "const" => const abs

/-- The entries of a positive Cauchy sequence eventually have a positive lower bound. -/
/-
**CauSeq.Pos** 是 Mathlib 中的一个定义，位于命名空间 `CauSeq`。
形式化陈述：Pos (f : CauSeq α abs) : Prop
参数：f : CauSeq α abs。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The entries of a positive Cauchy sequence eventually have a positive lower bound
.
-/
def Pos (f : CauSeq α abs) : Prop :=
  ∃ K > 0, ∃ i, ∀ j ≥ i, K ≤ f j
/-
**CauSeq.not_limZero_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：not_limZero_of_pos {f : CauSeq α abs} : Pos f -> ¬LimZero f | ⟨_, F0, hF⟩,
 H => let ⟨_, h⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `exists_forall_ge_and`：exists_forall_ge_and {p q : α -> Prop} : (exists i
, forall j >= i, p j) -> (exists i, forall j >= i, q j) -> exists i, forall j >=
 i, p j ∧ …
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `not_lt_of_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `abs_lt`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [A
ddLeftMono α] {a b : α} [AddRightMono α],   |a| < b ↔ -b < a ∧ a < b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem not_limZero_of_pos {f : CauSeq α abs} : Pos f → ¬LimZero f
  | ⟨_, F0, hF⟩, H =>
    let ⟨_, h⟩ := exists_forall_ge_and hF (H _ F0)
    let ⟨h₁, h₂⟩ := h _ le_rfl
    not_lt_of_ge h₁ (abs_lt.1 h₂).2
/-
**CauSeq.const_pos** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：const_pos {x : α} : Pos (const x) ↔ 0 < x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem const_pos {x : α} : Pos (const x) ↔ 0 < x :=
  ⟨fun ⟨_, K0, _, h⟩ => lt_of_lt_of_le K0 (h _ le_rfl), fun h => ⟨x, h, 0, fun _ _ => le_rfl⟩⟩
/-
**CauSeq.add_pos** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：add_pos {f g : CauSeq α abs} : Pos f -> Pos g -> Pos (f + g) | ⟨_, F0, hF⟩
, ⟨_, G0, hG⟩ => let ⟨i, h⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `exists_forall_ge_and`：exists_forall_ge_and {p q : α -> Prop} : (exists i
, forall j >= i, p j) -> (exists i, forall j >= i, q j) -> exists i, forall j >=
 i, p j ∧ …
· 使用定理 `add_pos`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder α] 
[AddLeftStrictMono α] {a b : α},   0 < a → 0 < b → 0 < a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem add_pos {f g : CauSeq α abs} : Pos f → Pos g → Pos (f + g)
  | ⟨_, F0, hF⟩, ⟨_, G0, hG⟩ =>
    let ⟨i, h⟩ := exists_forall_ge_and hF hG
    ⟨_, _root_.add_pos F0 G0, i, fun _ ij =>
      let ⟨h₁, h₂⟩ := h _ ij
      add_le_add h₁ h₂⟩
/-
**CauSeq.pos_add_limZero** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：pos_add_limZero {f g : CauSeq α abs} : Pos f -> LimZero g -> Pos (f + g) |
 ⟨F, F0, hF⟩, H => let ⟨i, h⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `exists_forall_ge_and`：exists_forall_ge_and {p q : α -> Prop} : (exists i
, forall j >= i, p j) -> (exists i, forall j >= i, q j) -> exists i, forall j >=
 i, p j ∧ …
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `abs_lt`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [A
ddLeftMono α] {a b : α} [AddRightMono α],   |a| < b ↔ -b < a ∧ a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self_div_two`：sub_self_div_two (a : α) : a - a / 2 = a / 2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
theorem pos_add_limZero {f g : CauSeq α abs} : Pos f → LimZero g → Pos (f + g)
  | ⟨F, F0, hF⟩, H =>
    let ⟨i, h⟩ := exists_forall_ge_and hF (H _ (half_pos F0))
    ⟨_, half_pos F0, i, fun j ij => by
      obtain ⟨h₁, h₂⟩ := h j ij
      have := add_le_add h₁ (le_of_lt (abs_lt.1 h₂).1)
      rwa [← sub_eq_add_neg, sub_self_div_two] at this⟩
/-
**CauSeq.mul_pos** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearOrder α] [inst_2 : IsStr
ictOrderedRing α] {f g : CauSeq α abs},   f.Pos → g.Pos → (f * g).Pos
参数：f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `exists_forall_ge_and`：exists_forall_ge_and {p q : α -> Prop} : (exists i
, forall j >= i, p j) -> (exists i, forall j >= i, q j) -> exists i, forall j >=
 i, p j ∧ …
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
protected theorem mul_pos {f g : CauSeq α abs} : Pos f → Pos g → Pos (f * g)
  | ⟨_, F0, hF⟩, ⟨_, G0, hG⟩ =>
    let ⟨i, h⟩ := exists_forall_ge_and hF hG
    ⟨_, mul_pos F0 G0, i, fun _ ij =>
      let ⟨h₁, h₂⟩ := h _ ij
      mul_le_mul h₁ h₂ (le_of_lt G0) (le_trans (le_of_lt F0) h₁)⟩
/-
**CauSeq.trichotomy** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：trichotomy (f : CauSeq α abs) : Pos f ∨ LimZero f ∨ Pos (-f)
参数：f : CauSeq α abs。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `CauSeq.abv_pos_of_not_limZero`：abv_pos_of_not_limZero {f : CauSeq β abv}
 (hf : ¬LimZero f) : exists K > 0, exists i, forall j >= i, K <= abv (f j)
· 使用引理 `exists_forall_ge_and`：exists_forall_ge_and {p q : α -> Prop} : (exists i
, forall j >= i, p j) -> (exists i, forall j >= i, q j) -> exists i, forall j >=
 i, p j ∧ …
· 使用定理 `CauSeq.cauchy₃`：cauchy₃ (f : CauSeq β abv) {ε} : 0 < ε -> exists i, fora
ll j >= i, forall k >= j, abv (f k - f j) < ε
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_add_iff_nonneg_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_
1 : LE α] [AddLeftMono α] [AddLeftReflectLE α] (a : α) {b : α},   a ≤ a + b ↔ 0 
≤ b
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `neg_le_sub_iff_le_add'`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 :
 LE α] [AddLeftMono α] {a b c : α}, -a ≤ b - c ↔ c ≤ a + b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `abs_lt`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [A
ddLeftMono α] {a b : α} [AddRightMono α],   |a| < b ↔ -b < a ∧ a < b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `abs_of_nonpos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], a ≤ 0 → |a| = -a
（共 35 条，此处仅展示前 30 条）
-/
theorem trichotomy (f : CauSeq α abs) : Pos f ∨ LimZero f ∨ Pos (-f) := by
  rcases Classical.em (LimZero f) with h | h
  · simp [*]
  simp only [false_or, h]
  rcases abv_pos_of_not_limZero h with ⟨K, K0, hK⟩
  rcases exists_forall_ge_and hK (f.cauchy₃ K0) with ⟨i, hi⟩
  refine (le_total 0 (f i)).imp ?_ ?_ <;>
    refine fun h => ⟨K, K0, i, fun j ij => ?_⟩ <;>
    have := (hi _ ij).1 <;>
    obtain ⟨h₁, h₂⟩ := hi _ le_rfl
  · rwa [abs_of_nonneg] at this
    rw [abs_of_nonneg h] at h₁
    exact
      (le_add_iff_nonneg_right _).1
        (le_trans h₁ <| neg_le_sub_iff_le_add'.1 <| le_of_lt (abs_lt.1 <| h₂ _ ij).1)
  · rwa [abs_of_nonpos] at this
    rw [abs_of_nonpos h] at h₁
    rw [← sub_le_sub_iff_right, zero_sub]
    exact le_trans (le_of_lt (abs_lt.1 <| h₂ _ ij).2) h₁
/-
**CauSeq.** 是 Mathlib 中的一个实例，位于命名空间 `CauSeq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LT (CauSeq α abs) :=
  ⟨fun f g => Pos (g - f)⟩
/-
**CauSeq.** 是 Mathlib 中的一个实例，位于命名空间 `CauSeq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LE (CauSeq α abs) :=
  ⟨fun f g => f < g ∨ f ≈ g⟩
/-
**CauSeq.lt_of_lt_of_eq** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：lt_of_lt_of_eq {f g h : CauSeq α abs} (fg : f < g) (gh : g ≈ h) : f < h
参数：fg : f < g；gh : g ≈ h。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `sub_add_sub_cancel'`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c : G
), a - b + (c - a) = c - b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CauSeq.pos_add_limZero`：pos_add_limZero {f g : CauSeq α abs} : Pos f -> 
LimZero g -> Pos (f + g) | ⟨F, F0, hF⟩, H => let ⟨i, h⟩
· 使用定理 `CauSeq.neg_limZero`：neg_limZero {f : CauSeq β abv} (hf : LimZero f) : Li
mZero (-f)
-/
theorem lt_of_lt_of_eq {f g h : CauSeq α abs} (fg : f < g) (gh : g ≈ h) : f < h :=
  show Pos (h - f) by
    convert pos_add_limZero fg (neg_limZero gh)
    simp
/-
**CauSeq.lt_of_eq_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：lt_of_eq_of_lt {f g h : CauSeq α abs} (fg : f ≈ g) (gh : g < h) : f < h
参数：fg : f ≈ g；gh : g < h。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CauSeq.pos_add_limZero`：pos_add_limZero {f g : CauSeq α abs} : Pos f -> 
LimZero g -> Pos (f + g) | ⟨F, F0, hF⟩, H => let ⟨i, h⟩
· 使用定理 `CauSeq.neg_limZero`：neg_limZero {f : CauSeq β abv} (hf : LimZero f) : Li
mZero (-f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_sub_sub_cancel_right`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : 
G), a - c - (b - c) = a - b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
-/
theorem lt_of_eq_of_lt {f g h : CauSeq α abs} (fg : f ≈ g) (gh : g < h) : f < h := by
  have := pos_add_limZero gh (neg_limZero fg)
  rwa [← sub_eq_add_neg, sub_sub_sub_cancel_right] at this
/-
**CauSeq.lt_trans** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：lt_trans {f g h : CauSeq α abs} (fg : f < g) (gh : g < h) : f < h
参数：fg : f < g；gh : g < h。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_add_sub_cancel'`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c : G
), a - b + (c - a) = c - b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CauSeq.add_pos`：add_pos {f g : CauSeq α abs} : Pos f -> Pos g -> Pos (f 
+ g) | ⟨_, F0, hF⟩, ⟨_, G0, hG⟩ => let ⟨i, h⟩
-/
theorem lt_trans {f g h : CauSeq α abs} (fg : f < g) (gh : g < h) : f < h :=
  show Pos (h - f) by
    convert add_pos fg gh
    simp
/-
**CauSeq.lt_irrefl** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearOrder α] [inst_2 : IsStr
ictOrderedRing α] {f : CauSeq α abs}, ¬f < f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CauSeq.not_limZero_of_pos`：not_limZero_of_pos {f : CauSeq α abs} : Pos f
 -> ¬LimZero f | ⟨_, F0, hF⟩, H => let ⟨_, h⟩
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
theorem lt_irrefl {f : CauSeq α abs} : ¬f < f
  | h => not_limZero_of_pos h (by simp [zero_limZero])
/-
**CauSeq.le_of_eq_of_le** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：le_of_eq_of_le {f g h : CauSeq α abs} (hfg : f ≈ g) (hgh : g <= h) : f <= 
h
参数：hfg : f ≈ g；hgh : g <= h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `CauSeq.lt_of_eq_of_lt`：lt_of_eq_of_lt {f g h : CauSeq α abs} (fg : f ≈ g
) (gh : g < h) : f < h
· 使用定理 `Setoid.trans`：∀ {α : Sort u} [inst : Setoid α] {a b c : α}, a ≈ b → b ≈ 
c → a ≈ c
-/
theorem le_of_eq_of_le {f g h : CauSeq α abs} (hfg : f ≈ g) (hgh : g ≤ h) : f ≤ h :=
  hgh.elim (Or.inl ∘ CauSeq.lt_of_eq_of_lt hfg) (Or.inr ∘ Setoid.trans hfg)
/-
**CauSeq.le_of_le_of_eq** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：le_of_le_of_eq {f g h : CauSeq α abs} (hfg : f <= g) (hgh : g ≈ h) : f <= 
h
参数：hfg : f <= g；hgh : g ≈ h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `CauSeq.lt_of_lt_of_eq`：lt_of_lt_of_eq {f g h : CauSeq α abs} (fg : f < g
) (gh : g ≈ h) : f < h
· 使用定理 `Setoid.trans`：∀ {α : Sort u} [inst : Setoid α] {a b c : α}, a ≈ b → b ≈ 
c → a ≈ c
-/
theorem le_of_le_of_eq {f g h : CauSeq α abs} (hfg : f ≤ g) (hgh : g ≈ h) : f ≤ h :=
  hfg.elim (fun h => Or.inl (CauSeq.lt_of_lt_of_eq h hgh)) fun h => Or.inr (Setoid.trans h hgh)
/-
**CauSeq.** 是 Mathlib 中的一个实例，位于命名空间 `CauSeq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Preorder (CauSeq α abs) where
  lt := (· < ·)
  le f g := f < g ∨ f ≈ g
  le_refl _ := Or.inr (Setoid.refl _)
  le_trans _ _ _ fg gh :=
    match fg, gh with
    | Or.inl fg, Or.inl gh => Or.inl <| lt_trans fg gh
    | Or.inl fg, Or.inr gh => Or.inl <| lt_of_lt_of_eq fg gh
    | Or.inr fg, Or.inl gh => Or.inl <| lt_of_eq_of_lt fg gh
    | Or.inr fg, Or.inr gh => Or.inr <| Setoid.trans fg gh
  lt_iff_le_not_ge _ _ :=
    ⟨fun h => ⟨Or.inl h, not_or_intro (mt (lt_trans h) lt_irrefl) (not_limZero_of_pos h)⟩,
      fun ⟨h₁, h₂⟩ => h₁.resolve_right (mt (fun h => Or.inr (Setoid.symm h)) h₂)⟩
/-
**CauSeq.le_antisymm** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：le_antisymm {f g : CauSeq α abs} (fg : f <= g) (gf : g <= f) : f ≈ g
参数：fg : f <= g；gf : g <= f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `not_lt_of_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
-/
theorem le_antisymm {f g : CauSeq α abs} (fg : f ≤ g) (gf : g ≤ f) : f ≈ g :=
  fg.resolve_left (not_lt_of_ge gf)
/-
**CauSeq.lt_total** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：lt_total (f g : CauSeq α abs) : f < g ∨ f ≈ g ∨ g < f
参数：f g : CauSeq α abs。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Setoid.symm`：∀ {α : Sort u} [inst : Setoid α] {a b : α}, a ≈ b → b ≈ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `CauSeq.trichotomy`：trichotomy (f : CauSeq α abs) : Pos f ∨ LimZero f ∨ P
os (-f)
-/
theorem lt_total (f g : CauSeq α abs) : f < g ∨ f ≈ g ∨ g < f :=
  (trichotomy (g - f)).imp_right fun h =>
    h.imp (fun h => Setoid.symm h) fun h => by rwa [neg_sub] at h
/-
**CauSeq.le_total** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：le_total (f g : CauSeq α abs) : f <= g ∨ g <= f
参数：f g : CauSeq α abs。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `or_assoc`：∀ {a b c : Prop}, (a ∨ b) ∨ c ↔ a ∨ b ∨ c
· 使用定理 `CauSeq.lt_total`：lt_total (f g : CauSeq α abs) : f < g ∨ f ≈ g ∨ g < f
-/
theorem le_total (f g : CauSeq α abs) : f ≤ g ∨ g ≤ f :=
  (or_assoc.2 (lt_total f g)).imp_right Or.inl
/-
**CauSeq.const_lt** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：const_lt {x y : α} : const x < const y ↔ x < y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CauSeq.const_sub`：const_sub (x y : β) : const (x - y) = const x - const 
y
· 使用定理 `CauSeq.const_pos`：const_pos {x : α} : Pos (const x) ↔ 0 < x
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
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
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem const_lt {x y : α} : const x < const y ↔ x < y :=
  show Pos _ ↔ _ by rw [← const_sub, const_pos, sub_pos]
/-
**CauSeq.const_le** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：const_le {x y : α} : const x <= const y ↔ x <= y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `le_iff_lt_or_eq`：le_iff_lt_or_eq : a <= b ↔ a < b ∨ a = b
· 使用定理 `or_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∨ b ↔ c ∨ d)
· 使用定理 `CauSeq.const_lt`：const_lt {x y : α} : const x < const y ↔ x < y
· 使用定理 `CauSeq.const_equiv`：const_equiv {x y : β} : const x ≈ const y ↔ x = y
-/
theorem const_le {x y : α} : const x ≤ const y ↔ x ≤ y := by
  rw [le_iff_lt_or_eq]; exact or_congr const_lt const_equiv
/-
**CauSeq.le_of_exists** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：le_of_exists {f g : CauSeq α abs} (h : exists i, forall j >= i, f j <= g j
) : f <= g
参数：h : exists i, forall j >= i, f j <= g j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `or_assoc`：∀ {a b c : Prop}, (a ∨ b) ∨ c ↔ a ∨ b ∨ c
· 使用定理 `CauSeq.lt_total`：lt_total (f g : CauSeq α abs) : f < g ∨ f ≈ g ∨ g < f
· 使用定理 `not_lt_of_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
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
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
-/
theorem le_of_exists {f g : CauSeq α abs} (h : ∃ i, ∀ j ≥ i, f j ≤ g j) : f ≤ g :=
  let ⟨i, hi⟩ := h
  (or_assoc.2 (CauSeq.lt_total f g)).elim id fun hgf =>
    False.elim
      (let ⟨_, hK0, j, hKj⟩ := hgf
      not_lt_of_ge (hi (max i j) (le_max_left _ _))
        (sub_pos.1 (lt_of_lt_of_le hK0 (hKj _ (le_max_right _ _)))))
/-
**CauSeq.exists_gt** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：exists_gt (f : CauSeq α abs) : exists a : α, f < const a
参数：f : CauSeq α abs。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CauSeq.bounded`：bounded (f : CauSeq β abv) : exists r, forall i, abv (f 
i) < r
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CauSeq.sub_apply`：sub_apply (f g : CauSeq β abv) (i : Nat) : (f - g) i =
 f i - g i
· 使用定理 `CauSeq.const_apply`：const_apply (x : β) (i : Nat) : (const x : Nat -> β)
 i = x
· 使用定理 `le_sub_iff_add_le'`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LE 
α] [AddLeftMono α] {a b c : α}, b ≤ c - a ↔ a + b ≤ c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `add_le_add_iff_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [A
ddRightMono α] [AddRightReflectLE α] (a : α) {b c : α},   b + a ≤ c + a ↔ b ≤ c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `abs_lt`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [A
ddLeftMono α] {a b : α} [AddRightMono α],   |a| < b ↔ -b < a ∧ a < b
-/
theorem exists_gt (f : CauSeq α abs) : ∃ a : α, f < const a :=
  let ⟨K, H⟩ := f.bounded
  ⟨K + 1, 1, zero_lt_one, 0, fun i _ => by
    rw [sub_apply, const_apply, le_sub_iff_add_le', add_le_add_iff_right]
    exact le_of_lt (abs_lt.1 (H _)).2⟩
/-
**CauSeq.exists_lt** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：exists_lt (f : CauSeq α abs) : exists a : α, const a < f
参数：f : CauSeq α abs。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CauSeq.exists_gt`：exists_gt (f : CauSeq α abs) : exists a : α, f < const
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CauSeq.const_neg`：const_neg (x : β) : const (-x) = -const x
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem exists_lt (f : CauSeq α abs) : ∃ a : α, const a < f :=
  let ⟨a, h⟩ := (-f).exists_gt
  ⟨-a, show Pos _ by rwa [const_neg, sub_neg_eq_add, add_comm, ← sub_neg_eq_add]⟩

-- so named to match `rat_add_continuous_lemma`
/-
**CauSeq.rat_sup_continuous_lemma** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：rat_sup_continuous_lemma {ε : α} {a₁ a₂ b₁ b₂ : α} : abs (a₁ - b₁) < ε -> 
abs (a₂ - b₂) < ε -> abs (a₁ ⊔ a₂ - b₁ ⊔ b₂) < ε
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `abs_max_sub_max_le_max`：abs_max_sub_max_le_max (a b c d : α) : |max a b 
- max c d| <= max |a - c| |b - d|
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `max_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, b < a → c <
 a → max b c < a
-/
theorem rat_sup_continuous_lemma {ε : α} {a₁ a₂ b₁ b₂ : α} :
    abs (a₁ - b₁) < ε → abs (a₂ - b₂) < ε → abs (a₁ ⊔ a₂ - b₁ ⊔ b₂) < ε := fun h₁ h₂ =>
  (abs_max_sub_max_le_max _ _ _ _).trans_lt (max_lt h₁ h₂)

-- so named to match `rat_add_continuous_lemma`
/-
**CauSeq.rat_inf_continuous_lemma** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：rat_inf_continuous_lemma {ε : α} {a₁ a₂ b₁ b₂ : α} : abs (a₁ - b₁) < ε -> 
abs (a₂ - b₂) < ε -> abs (a₁ ⊓ a₂ - b₁ ⊓ b₂) < ε
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `abs_min_sub_min_le_max`：abs_min_sub_min_le_max (a b c d : α) : |min a b 
- min c d| <= max |a - c| |b - d|
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `max_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, b < a → c <
 a → max b c < a
-/
theorem rat_inf_continuous_lemma {ε : α} {a₁ a₂ b₁ b₂ : α} :
    abs (a₁ - b₁) < ε → abs (a₂ - b₂) < ε → abs (a₁ ⊓ a₂ - b₁ ⊓ b₂) < ε := fun h₁ h₂ =>
  (abs_min_sub_min_le_max _ _ _ _).trans_lt (max_lt h₁ h₂)
/-
**CauSeq.** 是 Mathlib 中的一个实例，位于命名空间 `CauSeq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Max (CauSeq α abs) :=
  ⟨fun f g =>
    ⟨f ⊔ g, fun _ ε0 =>
      (exists_forall_ge_and (f.cauchy₃ ε0) (g.cauchy₃ ε0)).imp fun _ H _ ij =>
        let ⟨H₁, H₂⟩ := H _ le_rfl
        rat_sup_continuous_lemma (H₁ _ ij) (H₂ _ ij)⟩⟩
/-
**CauSeq.** 是 Mathlib 中的一个实例，位于命名空间 `CauSeq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Min (CauSeq α abs) :=
  ⟨fun f g =>
    ⟨f ⊓ g, fun _ ε0 =>
      (exists_forall_ge_and (f.cauchy₃ ε0) (g.cauchy₃ ε0)).imp fun _ H _ ij =>
        let ⟨H₁, H₂⟩ := H _ le_rfl
        rat_inf_continuous_lemma (H₁ _ ij) (H₂ _ ij)⟩⟩

@[simp, norm_cast]
/-
**CauSeq.coe_sup** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：coe_sup (f g : CauSeq α abs) : ⇑(f ⊔ g) = (f : Nat -> α) ⊔ g
参数：f g : CauSeq α abs。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sup (f g : CauSeq α abs) : ⇑(f ⊔ g) = (f : ℕ → α) ⊔ g :=
  rfl

@[simp, norm_cast]
/-
**CauSeq.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：coe_inf (f g : CauSeq α abs) : ⇑(f ⊓ g) = (f : Nat -> α) ⊓ g
参数：f g : CauSeq α abs。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inf (f g : CauSeq α abs) : ⇑(f ⊓ g) = (f : ℕ → α) ⊓ g :=
  rfl
/-
**CauSeq.sup_limZero** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：sup_limZero {f g : CauSeq α abs} (hf : LimZero f) (hg : LimZero g) : LimZe
ro (f ⊔ g) | ε, ε0 => (exists_forall_ge_and (hf _ ε0) (hg _ ε0)).imp fun _ H j i
j => by let ⟨H₁, H₂⟩
参数：hf : LimZero f；hg : LimZero g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_lt`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [A
ddLeftMono α] {a b : α} [AddRightMono α],   |a| < b ↔ -b < a ∧ a < b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_sup_iff`：lt_sup_iff : a < b ⊔ c ↔ a < b ∨ a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `sup_lt_iff`：sup_lt_iff : b ⊔ c < a ↔ b < a ∧ c < a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `exists_forall_ge_and`：exists_forall_ge_and {p q : α -> Prop} : (exists i
, forall j >= i, p j) -> (exists i, forall j >= i, q j) -> exists i, forall j >=
 i, p j ∧ …
-/
theorem sup_limZero {f g : CauSeq α abs} (hf : LimZero f) (hg : LimZero g) : LimZero (f ⊔ g)
  | ε, ε0 =>
    (exists_forall_ge_and (hf _ ε0) (hg _ ε0)).imp fun _ H j ij => by
      let ⟨H₁, H₂⟩ := H _ ij
      rw [abs_lt] at H₁ H₂ ⊢
      exact ⟨lt_sup_iff.mpr (Or.inl H₁.1), sup_lt_iff.mpr ⟨H₁.2, H₂.2⟩⟩
/-
**CauSeq.inf_limZero** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：inf_limZero {f g : CauSeq α abs} (hf : LimZero f) (hg : LimZero g) : LimZe
ro (f ⊓ g) | ε, ε0 => (exists_forall_ge_and (hf _ ε0) (hg _ ε0)).imp fun _ H j i
j => by let ⟨H₁, H₂⟩
参数：hf : LimZero f；hg : LimZero g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_lt`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [A
ddLeftMono α] {a b : α} [AddRightMono α],   |a| < b ↔ -b < a ∧ a < b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_inf_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, a < min b
 c ↔ a < b ∧ a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `inf_lt_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, min b c <
 a ↔ b < a ∨ c < a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `exists_forall_ge_and`：exists_forall_ge_and {p q : α -> Prop} : (exists i
, forall j >= i, p j) -> (exists i, forall j >= i, q j) -> exists i, forall j >=
 i, p j ∧ …
-/
theorem inf_limZero {f g : CauSeq α abs} (hf : LimZero f) (hg : LimZero g) : LimZero (f ⊓ g)
  | ε, ε0 =>
    (exists_forall_ge_and (hf _ ε0) (hg _ ε0)).imp fun _ H j ij => by
      let ⟨H₁, H₂⟩ := H _ ij
      rw [abs_lt] at H₁ H₂ ⊢
      exact ⟨lt_inf_iff.mpr ⟨H₁.1, H₂.1⟩, inf_lt_iff.mpr (Or.inl H₁.2)⟩
/-
**CauSeq.sup_equiv_sup** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：sup_equiv_sup {a₁ b₁ a₂ b₂ : CauSeq α abs} (ha : a₁ ≈ a₂) (hb : b₁ ≈ b₂) :
 a₁ ⊔ b₁ ≈ a₂ ⊔ b₂
参数：ha : a₁ ≈ a₂；hb : b₁ ≈ b₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `abs_max_sub_max_le_max`：abs_max_sub_max_le_max (a b c d : α) : |max a b 
- max c d| <= max |a - c| |b - d|
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `max_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, b < a → c <
 a → max b c < a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sup_le_iff`：sup_le_iff : a ⊔ b <= c ↔ a <= c ∧ b <= c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem sup_equiv_sup {a₁ b₁ a₂ b₂ : CauSeq α abs} (ha : a₁ ≈ a₂) (hb : b₁ ≈ b₂) :
    a₁ ⊔ b₁ ≈ a₂ ⊔ b₂ := by
  intro ε ε0
  obtain ⟨ai, hai⟩ := ha ε ε0
  obtain ⟨bi, hbi⟩ := hb ε ε0
  exact
    ⟨ai ⊔ bi, fun i hi =>
      (abs_max_sub_max_le_max (a₁ i) (b₁ i) (a₂ i) (b₂ i)).trans_lt
        (max_lt (hai i (sup_le_iff.mp hi).1) (hbi i (sup_le_iff.mp hi).2))⟩
/-
**CauSeq.inf_equiv_inf** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：inf_equiv_inf {a₁ b₁ a₂ b₂ : CauSeq α abs} (ha : a₁ ≈ a₂) (hb : b₁ ≈ b₂) :
 a₁ ⊓ b₁ ≈ a₂ ⊓ b₂
参数：ha : a₁ ≈ a₂；hb : b₁ ≈ b₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `abs_min_sub_min_le_max`：abs_min_sub_min_le_max (a b c d : α) : |min a b 
- min c d| <= max |a - c| |b - d|
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `max_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, b < a → c <
 a → max b c < a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sup_le_iff`：sup_le_iff : a ⊔ b <= c ↔ a <= c ∧ b <= c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem inf_equiv_inf {a₁ b₁ a₂ b₂ : CauSeq α abs} (ha : a₁ ≈ a₂) (hb : b₁ ≈ b₂) :
    a₁ ⊓ b₁ ≈ a₂ ⊓ b₂ := by
  intro ε ε0
  obtain ⟨ai, hai⟩ := ha ε ε0
  obtain ⟨bi, hbi⟩ := hb ε ε0
  exact
    ⟨ai ⊔ bi, fun i hi =>
      (abs_min_sub_min_le_max (a₁ i) (b₁ i) (a₂ i) (b₂ i)).trans_lt
        (max_lt (hai i (sup_le_iff.mp hi).1) (hbi i (sup_le_iff.mp hi).2))⟩
/-
**CauSeq.sup_lt** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearOrder α] [inst_2 : IsStr
ictOrderedRing α] {a b c : CauSeq α abs},   a < c → b < c → a ⊔ b < c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_inf_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, a < min b
 c ↔ a < b ∧ a < c
· 使用定理 `min_le_min`：∀ {α : Type u} [inst : LinearOrder α] {a b c d : α}, c ≤ a →
 d ≤ b → min c d ≤ min a b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sup_le_iff`：sup_le_iff : a ⊔ b <= c ↔ a <= c ∧ b <= c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `min_sub_sub_left`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : Lin
earOrder α] [IsOrderedAddMonoid α] (a b c : α),   min (a - b) (a - c) = a - max 
b c
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
protected theorem sup_lt {a b c : CauSeq α abs} (ha : a < c) (hb : b < c) : a ⊔ b < c := by
  obtain ⟨⟨εa, εa0, ia, ha⟩, ⟨εb, εb0, ib, hb⟩⟩ := ha, hb
  refine ⟨εa ⊓ εb, lt_inf_iff.mpr ⟨εa0, εb0⟩, ia ⊔ ib, fun i hi => ?_⟩
  have := min_le_min (ha _ (sup_le_iff.mp hi).1) (hb _ (sup_le_iff.mp hi).2)
  exact this.trans_eq (min_sub_sub_left _ _ _)
/-
**CauSeq.lt_inf** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearOrder α] [inst_2 : IsStr
ictOrderedRing α] {a b c : CauSeq α abs},   a < b → a < c → a < b ⊓ c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_inf_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, a < min b
 c ↔ a < b ∧ a < c
· 使用定理 `min_le_min`：∀ {α : Type u} [inst : LinearOrder α] {a b c d : α}, c ≤ a →
 d ≤ b → min c d ≤ min a b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sup_le_iff`：sup_le_iff : a ⊔ b <= c ↔ a <= c ∧ b <= c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `min_sub_sub_right`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : Li
nearOrder α] [IsOrderedAddMonoid α] (a b c : α),   min (a - c) (b - c) = min a b
 - c
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
protected theorem lt_inf {a b c : CauSeq α abs} (hb : a < b) (hc : a < c) : a < b ⊓ c := by
  obtain ⟨⟨εb, εb0, ib, hb⟩, ⟨εc, εc0, ic, hc⟩⟩ := hb, hc
  refine ⟨εb ⊓ εc, lt_inf_iff.mpr ⟨εb0, εc0⟩, ib ⊔ ic, fun i hi => ?_⟩
  have := min_le_min (hb _ (sup_le_iff.mp hi).1) (hc _ (sup_le_iff.mp hi).2)
  exact this.trans_eq (min_sub_sub_right _ _ _)

@[simp]
/-
**CauSeq.sup_idem** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearOrder α] [inst_2 : IsStr
ictOrderedRing α] (a : CauSeq α abs),   a ⊔ a = a
参数：a : CauSeq α abs。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `sup_idem`：sup_idem (a : α) : a ⊔ a = a
-/
protected theorem sup_idem (a : CauSeq α abs) : a ⊔ a = a := Subtype.ext (sup_idem _)

@[simp]
/-
**CauSeq.inf_idem** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearOrder α] [inst_2 : IsStr
ictOrderedRing α] (a : CauSeq α abs),   a ⊓ a = a
参数：a : CauSeq α abs。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `inf_idem`：∀ {α : Type u} [inst : SemilatticeInf α] (a : α), a ⊓ a = a
-/
protected theorem inf_idem (a : CauSeq α abs) : a ⊓ a = a := Subtype.ext (inf_idem _)
/-
**CauSeq.sup_comm** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearOrder α] [inst_2 : IsStr
ictOrderedRing α] (a b : CauSeq α abs),   a ⊔ b = b ⊔ a
参数：a b : CauSeq α abs。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
-/
protected theorem sup_comm (a b : CauSeq α abs) : a ⊔ b = b ⊔ a := Subtype.ext (sup_comm _ _)
/-
**CauSeq.inf_comm** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearOrder α] [inst_2 : IsStr
ictOrderedRing α] (a b : CauSeq α abs),   a ⊓ b = b ⊓ a
参数：a b : CauSeq α abs。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
-/
protected theorem inf_comm (a b : CauSeq α abs) : a ⊓ b = b ⊓ a := Subtype.ext (inf_comm _ _)
/-
**CauSeq.sup_eq_right** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearOrder α] [inst_2 : IsStr
ictOrderedRing α] {a b : CauSeq α abs},   a ≤ b → a ⊔ b ≈ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `max_sub_sub_right`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : Li
nearOrder α] [IsOrderedAddMonoid α] (a b c : α),   max (a - c) (b - c) = max a b
 - c
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用定理 `sub_nonpos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, a - b ≤ 0 ↔ a ≤ b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `Setoid.trans`：∀ {α : Sort u} [inst : Setoid α] {a b c : α}, a ≈ b → b ≈ 
c → a ≈ c
· 使用定理 `CauSeq.sup_equiv_sup`：sup_equiv_sup {a₁ b₁ a₂ b₂ : CauSeq α abs} (ha : a
₁ ≈ a₂) (hb : b₁ ≈ b₂) : a₁ ⊔ b₁ ≈ a₂ ⊔ b₂
· 使用定理 `Setoid.refl`：∀ {α : Sort u} [inst : Setoid α] (a : α), a ≈ a
· 使用定理 `CauSeq.sup_idem`：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearOrder
 α] [inst_2 : IsStrictOrderedRing α] (a : CauSeq α abs),   a ⊔ a = a
-/
protected theorem sup_eq_right {a b : CauSeq α abs} (h : a ≤ b) : a ⊔ b ≈ b := by
  obtain ⟨ε, ε0 : _ < _, i, h⟩ | h := h
  · intro _ _
    refine ⟨i, fun j hj => ?_⟩
    dsimp
    rw [← max_sub_sub_right]
    rwa [sub_self, max_eq_right, abs_zero]
    rw [sub_nonpos, ← sub_nonneg]
    exact ε0.le.trans (h _ hj)
  · refine Setoid.trans (sup_equiv_sup h (Setoid.refl _)) ?_
    rw [CauSeq.sup_idem]
/-
**CauSeq.inf_eq_right** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearOrder α] [inst_2 : IsStr
ictOrderedRing α] {a b : CauSeq α abs},   b ≤ a → a ⊓ b ≈ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `min_sub_sub_right`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : Li
nearOrder α] [IsOrderedAddMonoid α] (a b c : α),   min (a - c) (b - c) = min a b
 - c
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用引理 `min_eq_right`：min_eq_right (h : b <= a) : min a b = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Setoid.trans`：∀ {α : Sort u} [inst : Setoid α] {a b c : α}, a ≈ b → b ≈ 
c → a ≈ c
· 使用定理 `CauSeq.inf_equiv_inf`：inf_equiv_inf {a₁ b₁ a₂ b₂ : CauSeq α abs} (ha : a
₁ ≈ a₂) (hb : b₁ ≈ b₂) : a₁ ⊓ b₁ ≈ a₂ ⊓ b₂
· 使用定理 `Setoid.symm`：∀ {α : Sort u} [inst : Setoid α] {a b : α}, a ≈ b → b ≈ a
· 使用定理 `Setoid.refl`：∀ {α : Sort u} [inst : Setoid α] (a : α), a ≈ a
· 使用定理 `CauSeq.inf_idem`：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearOrder
 α] [inst_2 : IsStrictOrderedRing α] (a : CauSeq α abs),   a ⊓ a = a
-/
protected theorem inf_eq_right {a b : CauSeq α abs} (h : b ≤ a) : a ⊓ b ≈ b := by
  obtain ⟨ε, ε0 : _ < _, i, h⟩ | h := h
  · intro _ _
    refine ⟨i, fun j hj => ?_⟩
    dsimp
    rw [← min_sub_sub_right]
    rwa [sub_self, min_eq_right, abs_zero]
    exact ε0.le.trans (h _ hj)
  · refine Setoid.trans (inf_equiv_inf (Setoid.symm h) (Setoid.refl _)) ?_
    rw [CauSeq.inf_idem]
/-
**CauSeq.sup_eq_left** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearOrder α] [inst_2 : IsStr
ictOrderedRing α] {a b : CauSeq α abs},   b ≤ a → a ⊔ b ≈ a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CauSeq.sup_comm`：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearOrder
 α] [inst_2 : IsStrictOrderedRing α] (a b : CauSeq α abs),   a ⊔ b = b ⊔ a
· 使用定理 `CauSeq.sup_eq_right`：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearO
rder α] [inst_2 : IsStrictOrderedRing α] {a b : CauSeq α abs},   a ≤ b → a ⊔ b ≈
 b
-/
protected theorem sup_eq_left {a b : CauSeq α abs} (h : b ≤ a) : a ⊔ b ≈ a := by
  simpa only [CauSeq.sup_comm] using CauSeq.sup_eq_right h
/-
**CauSeq.inf_eq_left** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearOrder α] [inst_2 : IsStr
ictOrderedRing α] {a b : CauSeq α abs},   a ≤ b → a ⊓ b ≈ a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CauSeq.inf_comm`：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearOrder
 α] [inst_2 : IsStrictOrderedRing α] (a b : CauSeq α abs),   a ⊓ b = b ⊓ a
· 使用定理 `CauSeq.inf_eq_right`：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearO
rder α] [inst_2 : IsStrictOrderedRing α] {a b : CauSeq α abs},   b ≤ a → a ⊓ b ≈
 b
-/
protected theorem inf_eq_left {a b : CauSeq α abs} (h : a ≤ b) : a ⊓ b ≈ a := by
  simpa only [CauSeq.inf_comm] using CauSeq.inf_eq_right h
/-
**CauSeq.le_sup_left** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearOrder α] [inst_2 : IsStr
ictOrderedRing α] {a b : CauSeq α abs},   a ≤ a ⊔ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CauSeq.le_of_exists`：le_of_exists {f g : CauSeq α abs} (h : exists i, fo
rall j >= i, f j <= g j) : f <= g
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
protected theorem le_sup_left {a b : CauSeq α abs} : a ≤ a ⊔ b :=
  le_of_exists ⟨0, fun _ _ => le_sup_left⟩
/-
**CauSeq.inf_le_left** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearOrder α] [inst_2 : IsStr
ictOrderedRing α] {a b : CauSeq α abs},   a ⊓ b ≤ a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CauSeq.le_of_exists`：le_of_exists {f g : CauSeq α abs} (h : exists i, fo
rall j >= i, f j <= g j) : f <= g
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
protected theorem inf_le_left {a b : CauSeq α abs} : a ⊓ b ≤ a :=
  le_of_exists ⟨0, fun _ _ => inf_le_left⟩
/-
**CauSeq.le_sup_right** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearOrder α] [inst_2 : IsStr
ictOrderedRing α] {a b : CauSeq α abs},   b ≤ a ⊔ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CauSeq.le_of_exists`：le_of_exists {f g : CauSeq α abs} (h : exists i, fo
rall j >= i, f j <= g j) : f <= g
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
protected theorem le_sup_right {a b : CauSeq α abs} : b ≤ a ⊔ b :=
  le_of_exists ⟨0, fun _ _ => le_sup_right⟩
/-
**CauSeq.inf_le_right** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearOrder α] [inst_2 : IsStr
ictOrderedRing α] {a b : CauSeq α abs},   a ⊓ b ≤ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CauSeq.le_of_exists`：le_of_exists {f g : CauSeq α abs} (h : exists i, fo
rall j >= i, f j <= g j) : f <= g
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
protected theorem inf_le_right {a b : CauSeq α abs} : a ⊓ b ≤ b :=
  le_of_exists ⟨0, fun _ _ => inf_le_right⟩
/-
**CauSeq.sup_le** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearOrder α] [inst_2 : IsStr
ictOrderedRing α] {a b c : CauSeq α abs},   a ≤ c → b ≤ c → a ⊔ b ≤ c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CauSeq.sup_lt`：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearOrder α
] [inst_2 : IsStrictOrderedRing α] {a b c : CauSeq α abs},   a < c → b < c → a ⊔
 b …
· 使用定理 `CauSeq.le_of_le_of_eq`：le_of_le_of_eq {f g h : CauSeq α abs} (hfg : f <=
 g) (hgh : g ≈ h) : f <= h
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Setoid.symm`：∀ {α : Sort u} [inst : Setoid α] {a b : α}, a ≈ b → b ≈ a
· 使用定理 `CauSeq.sup_eq_right`：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearO
rder α] [inst_2 : IsStrictOrderedRing α] {a b : CauSeq α abs},   a ≤ b → a ⊔ b ≈
 b
· 使用定理 `CauSeq.sup_eq_left`：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearOr
der α] [inst_2 : IsStrictOrderedRing α] {a b : CauSeq α abs},   b ≤ a → a ⊔ b ≈ 
a
-/
protected theorem sup_le {a b c : CauSeq α abs} (ha : a ≤ c) (hb : b ≤ c) : a ⊔ b ≤ c := by
  obtain ha | ha := ha
  · obtain hb | hb := hb
    · exact Or.inl (CauSeq.sup_lt ha hb)
    · replace ha := le_of_le_of_eq ha.le (Setoid.symm hb)
      refine le_of_le_of_eq (Or.inr ?_) hb
      exact CauSeq.sup_eq_right ha
  · replace hb := le_of_le_of_eq hb (Setoid.symm ha)
    refine le_of_le_of_eq (Or.inr ?_) ha
    exact CauSeq.sup_eq_left hb
/-
**CauSeq.le_inf** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearOrder α] [inst_2 : IsStr
ictOrderedRing α] {a b c : CauSeq α abs},   a ≤ b → a ≤ c → a ≤ b ⊓ c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CauSeq.lt_inf`：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearOrder α
] [inst_2 : IsStrictOrderedRing α] {a b c : CauSeq α abs},   a < b → a < c → a <
 b …
· 使用定理 `CauSeq.le_of_eq_of_le`：le_of_eq_of_le {f g h : CauSeq α abs} (hfg : f ≈ 
g) (hgh : g <= h) : f <= h
· 使用定理 `Setoid.symm`：∀ {α : Sort u} [inst : Setoid α] {a b : α}, a ≈ b → b ≈ a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `CauSeq.inf_eq_right`：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearO
rder α] [inst_2 : IsStrictOrderedRing α] {a b : CauSeq α abs},   b ≤ a → a ⊓ b ≈
 b
· 使用定理 `CauSeq.inf_eq_left`：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearOr
der α] [inst_2 : IsStrictOrderedRing α] {a b : CauSeq α abs},   a ≤ b → a ⊓ b ≈ 
a
-/
protected theorem le_inf {a b c : CauSeq α abs} (hb : a ≤ b) (hc : a ≤ c) : a ≤ b ⊓ c := by
  obtain hb | hb := hb
  · obtain hc | hc := hc
    · exact Or.inl (CauSeq.lt_inf hb hc)
    · replace hb := le_of_eq_of_le (Setoid.symm hc) hb.le
      refine le_of_eq_of_le hc (Or.inr ?_)
      exact Setoid.symm (CauSeq.inf_eq_right hb)
  · replace hc := le_of_eq_of_le (Setoid.symm hb) hc
    refine le_of_eq_of_le hb (Or.inr ?_)
    exact Setoid.symm (CauSeq.inf_eq_left hc)

/-! Note that `DistribLattice (CauSeq α abs)` is not true because there is no `PartialOrder`. -/


/-
**CauSeq.sup_inf_distrib_left** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearOrder α] [inst_2 : IsStr
ictOrderedRing α] (a b c : CauSeq α abs),   a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c)
参数：a b c : CauSeq α abs；a ⊔ b；a ⊔ c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CauSeq.ext`：ext {f g : CauSeq β abv} (h : forall i, f i = g i) : f = g
· 使用引理 `max_min_distrib_left`：max_min_distrib_left (a b c : α) : max a (min b c)
 = min (max a b) (max a c)

--- 原说明 ---
Note that `DistribLattice (CauSeq α abs)` is not true because there is no `Parti
alOrder`.
-/
protected theorem sup_inf_distrib_left (a b c : CauSeq α abs) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) :=
  ext fun _ ↦ max_min_distrib_left _ _ _
/-
**CauSeq.sup_inf_distrib_right** 是 Mathlib 中的一个定理，位于命名空间 `CauSeq`。
形式化陈述：∀ {α : Type u_1} [inst : Field α] [inst_1 : LinearOrder α] [inst_2 : IsStr
ictOrderedRing α] (a b c : CauSeq α abs),   a ⊓ b ⊔ c = (a ⊔ c) ⊓ (b ⊔ c)
参数：a b c : CauSeq α abs；a ⊔ c；b ⊔ c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CauSeq.ext`：ext {f g : CauSeq β abv} (h : forall i, f i = g i) : f = g
· 使用引理 `max_min_distrib_right`：max_min_distrib_right (a b c : α) : max (min a b)
 c = min (max a c) (max b c)
-/
protected theorem sup_inf_distrib_right (a b c : CauSeq α abs) : a ⊓ b ⊔ c = (a ⊔ c) ⊓ (b ⊔ c) :=
  ext fun _ ↦ max_min_distrib_right _ _ _

end Abs

end CauSeq

