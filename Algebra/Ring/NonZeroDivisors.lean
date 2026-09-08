/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Regular.Basic
public import Mathlib.Algebra.Regular.Opposite
public import Mathlib.Algebra.Ring.Basic

/-!
# Non-zero divisors in a ring
-/

public section

assert_not_exists Field

open scoped nonZeroDivisors

section Monoid

variable {R : Type*} [Monoid R] {r : R}

@[to_additive]
/-
**IsLeftRegular.pow_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLeftRegular.pow_injective [IsMulTorsionFree R] (hx : IsLeftRegular r) (h
x' : r != 1) : Function.Injective (fun n => r ^ n)
参数：hx : IsLeftRegular r；hx' : r != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_add_of_le`：∀ {m n : ℕ}, m ≤ n → ∃ k, n = m + k
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_eq_one_iff_right`：pow_eq_one_iff_right (ha : a != 1) : a ^ n = 1 ↔ n
 = 0
· 使用定理 `IsLeftRegular.mul_left_eq_self_iff`：∀ {R : Type u_1} [inst : Monoid R] {
a b : R}, IsLeftRegular a → (a * b = a ↔ b = 1)
· 使用引理 `IsLeftRegular.pow`：IsLeftRegular.pow (n : Nat) (rla : IsLeftRegular a) :
 IsLeftRegular (a ^ n)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Nat.add_zero`：∀ (n : ℕ), n + 0 = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsLeftRegular.pow_injective [IsMulTorsionFree R]
    (hx : IsLeftRegular r) (hx' : r ≠ 1) : Function.Injective (fun n ↦ r ^ n) := by
  intro n m hnm
  have main {n m} (h₁ : n ≤ m) (h₂ : r ^ n = r ^ m) : n = m := by
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le h₁
    rw [pow_add, eq_comm, IsLeftRegular.mul_left_eq_self_iff (hx.pow n), pow_eq_one_iff_right hx']
      at h₂
    rw [h₂, Nat.add_zero]
  obtain h | h := Nat.le_or_le n m
  · exact main h hnm
  · exact (main h hnm.symm).symm

@[to_additive]
/-
**IsRightRegular.pow_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRightRegular.pow_injective {M : Type*} [Monoid M] [IsMulTorsionFree M] {
x : M} (hx : IsRightRegular x) (hx' : x != 1) : Function.Injective (fun n => x ^
 n)
参数：hx : IsRightRegular x；hx' : x != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `MulOpposite.unop_injective`：unop_injective : Injective (unop : αᵐᵒᵖ -> α
)
· 使用定理 `IsLeftRegular.pow_injective`：IsLeftRegular.pow_injective [IsMulTorsionFr
ee R] (hx : IsLeftRegular r) (hx' : r != 1) : Function.Injective (fun n => r ^ n
)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isLeftRegular_op`：isLeftRegular_op {a : R} : IsLeftRegular (op a) ↔ IsRi
ghtRegular a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `MulOpposite.op_eq_one_iff`：op_eq_one_iff [One α] (a : α) : op a = 1 ↔ a 
= 1
-/
theorem IsRightRegular.pow_injective {M : Type*} [Monoid M] [IsMulTorsionFree M] {x : M}
    (hx : IsRightRegular x) (hx' : x ≠ 1) : Function.Injective (fun n ↦ x ^ n) :=
  MulOpposite.unop_injective.comp <| (isLeftRegular_op.mpr hx).pow_injective <|
    (MulOpposite.op_eq_one_iff x).not.mpr hx'
/-
**IsMulTorsionFree.pow_right_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMulTorsionFree.pow_right_injective {M : Type*} [CancelMonoid M] [IsMulTo
rsionFree M] {x : M} (hx : x != 1) : Function.Injective (fun n => x ^ n)
参数：hx : x != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLeftRegular.pow_injective`：IsLeftRegular.pow_injective [IsMulTorsionFr
ee R] (hx : IsLeftRegular r) (hx' : r != 1) : Function.Injective (fun n => r ^ n
)
· 使用定理 `IsLeftRegular.all`：IsLeftRegular.all [Mul R] [IsLeftCancelMul R] (g : R)
 : IsLeftRegular g
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
-/
theorem IsMulTorsionFree.pow_right_injective {M : Type*} [CancelMonoid M] [IsMulTorsionFree M]
    {x : M} (hx : x ≠ 1) : Function.Injective (fun n ↦ x ^ n) :=
  IsLeftRegular.pow_injective (IsLeftRegular.all x) hx

@[simp]
/-
**IsMulTorsionFree.pow_right_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMulTorsionFree.pow_right_inj {M : Type*} [CancelMonoid M] [IsMulTorsionF
ree M] {x : M} (hx : x != 1) {n m : Nat} : x ^ n = x ^ m ↔ n = m
参数：hx : x != 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `IsMulTorsionFree.pow_right_injective`：IsMulTorsionFree.pow_right_injecti
ve {M : Type*} [CancelMonoid M] [IsMulTorsionFree M] {x : M} (hx : x != 1) : Fun
ction.Injective (fun n => …
-/
theorem IsMulTorsionFree.pow_right_inj {M : Type*} [CancelMonoid M] [IsMulTorsionFree M] {x : M}
    (hx : x ≠ 1) {n m : ℕ} : x ^ n = x ^ m ↔ n = m := (pow_right_injective hx).eq_iff
/-
**IsMulTorsionFree.pow_right_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMulTorsionFree.pow_right_injective {M : Type*} [CancelMonoid M] [IsMulTo
rsionFree M] {x : M} (hx : x != 1) : Function.Injective (fun n => x ^ n)
参数：hx : x != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLeftRegular.pow_injective`：IsLeftRegular.pow_injective [IsMulTorsionFr
ee R] (hx : IsLeftRegular r) (hx' : r != 1) : Function.Injective (fun n => r ^ n
)
· 使用定理 `IsLeftRegular.all`：IsLeftRegular.all [Mul R] [IsLeftCancelMul R] (g : R)
 : IsLeftRegular g
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
-/
theorem IsMulTorsionFree.pow_right_injective₀ {M : Type*} [MonoidWithZero M] [IsLeftCancelMulZero M]
    [IsMulTorsionFree M] {x : M} (hx : x ≠ 1) (hx' : x ≠ 0) : Function.Injective (fun n ↦ x ^ n) :=
  IsLeftRegular.pow_injective (IsLeftCancelMulZero.mul_left_cancel_of_ne_zero hx') hx

@[simp]
/-
**IsMulTorsionFree.pow_right_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsMulTorsionFree.pow_right_inj {M : Type*} [CancelMonoid M] [IsMulTorsionF
ree M] {x : M} (hx : x != 1) {n m : Nat} : x ^ n = x ^ m ↔ n = m
参数：hx : x != 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `IsMulTorsionFree.pow_right_injective`：IsMulTorsionFree.pow_right_injecti
ve {M : Type*} [CancelMonoid M] [IsMulTorsionFree M] {x : M} (hx : x != 1) : Fun
ction.Injective (fun n => …
-/
theorem IsMulTorsionFree.pow_right_inj₀ {M : Type*} [MonoidWithZero M] [IsLeftCancelMulZero M]
    [IsMulTorsionFree M] {x : M} (hx : x ≠ 1) (hx' : x ≠ 0) {n m : ℕ} : x ^ n = x ^ m ↔ n = m :=
  (pow_right_injective₀ hx hx').eq_iff

variable [Finite R]
/-
**IsLeftRegular.isUnit_of_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLeftRegular.isUnit_of_finite (h : IsLeftRegular r) : IsUnit r
参数：h : IsLeftRegular r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsUnit.isUnit_iff_mulLeft_bijective`：isUnit_iff_mulLeft_bijective {a : M
} : IsUnit a ↔ Function.Bijective (a * ·)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finite.injective_iff_bijective`：injective_iff_bijective {f : α -> α} : I
njective f ↔ Bijective f
-/
theorem IsLeftRegular.isUnit_of_finite (h : IsLeftRegular r) : IsUnit r := by
  rwa [IsUnit.isUnit_iff_mulLeft_bijective, ← Finite.injective_iff_bijective]
/-
**IsRightRegular.isUnit_of_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRightRegular.isUnit_of_finite (h : IsRightRegular r) : IsUnit r
参数：h : IsRightRegular r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsUnit.isUnit_iff_mulRight_bijective`：isUnit_iff_mulRight_bijective {a :
 M} : IsUnit a ↔ Function.Bijective (· * a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finite.injective_iff_bijective`：injective_iff_bijective {f : α -> α} : I
njective f ↔ Bijective f
-/
theorem IsRightRegular.isUnit_of_finite (h : IsRightRegular r) : IsUnit r := by
  rwa [IsUnit.isUnit_iff_mulRight_bijective, ← Finite.injective_iff_bijective]
/-
**isRegular_iff_isUnit_of_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isRegular_iff_isUnit_of_finite : IsRegular r ↔ IsUnit r where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLeftRegular.isUnit_of_finite`：IsLeftRegular.isUnit_of_finite (h : IsLe
ftRegular r) : IsUnit r
· 使用定理 `IsRegular.left`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → I
sLeftRegular c
· 使用定理 `IsUnit.isRegular`：IsUnit.isRegular (ua : IsUnit a) : IsRegular a
-/
theorem isRegular_iff_isUnit_of_finite : IsRegular r ↔ IsUnit r where
  mp h := h.1.isUnit_of_finite
  mpr h := h.isRegular

end Monoid

section Ring

variable {R : Type*} [Ring R] {a x y r : R}

/-
**isLeftRegular_iff_mem_nonZeroDivisorsLeft** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isLeftRegular_iff_mem_nonZeroDivisorsLeft : IsLeftRegular r ↔ r in nonZero
DivisorsLeft R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isLeftRegular_iff_right_eq_zero_of_mul`：isLeftRegular_iff_right_eq_zero_
of_mul : IsLeftRegular r ↔ forall x, r * x = 0 -> x = 0 where mp h r' eq
-/
lemma isLeftRegular_iff_mem_nonZeroDivisorsLeft : IsLeftRegular r ↔ r ∈ nonZeroDivisorsLeft R :=
  isLeftRegular_iff_right_eq_zero_of_mul
/-
**isRightRegular_iff_mem_nonZeroDivisorsRight** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isRightRegular_iff_mem_nonZeroDivisorsRight : IsRightRegular r ↔ r in nonZ
eroDivisorsRight R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isRightRegular_iff_left_eq_zero_of_mul`：isRightRegular_iff_left_eq_zero_
of_mul : IsRightRegular r ↔ forall x, x * r = 0 -> x = 0 where mp h r' eq
-/
lemma isRightRegular_iff_mem_nonZeroDivisorsRight : IsRightRegular r ↔ r ∈ nonZeroDivisorsRight R :=
  isRightRegular_iff_left_eq_zero_of_mul
/-
**isRegular_iff_mem_nonZeroDivisors** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isRegular_iff_mem_nonZeroDivisors : IsRegular r ↔ r in R⁰
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isRegular_iff_eq_zero_of_mul`：isRegular_iff_eq_zero_of_mul : IsRegular r
 ↔ (forall x, r * x = 0 -> x = 0) ∧ (forall x, x * r = 0 -> x = 0)
-/
lemma isRegular_iff_mem_nonZeroDivisors : IsRegular r ↔ r ∈ R⁰ := isRegular_iff_eq_zero_of_mul
/-
**le_nonZeroDivisorsLeft_iff_isLeftRegular** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_nonZeroDivisorsLeft_iff_isLeftRegular {S : Submonoid R} : S <= nonZeroD
ivisorsLeft R ↔ forall s : S, IsLeftRegular (s : R)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma le_nonZeroDivisorsLeft_iff_isLeftRegular {S : Submonoid R} :
    S ≤ nonZeroDivisorsLeft R ↔ ∀ s : S, IsLeftRegular (s : R) := by
  simp_rw [SetLike.le_def, isLeftRegular_iff_mem_nonZeroDivisorsLeft, Subtype.forall]
/-
**le_nonZeroDivisorsRight_iff_isRightRegular** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_nonZeroDivisorsRight_iff_isRightRegular {S : Submonoid R} : S <= nonZer
oDivisorsRight R ↔ forall s : S, IsRightRegular (s : R)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma le_nonZeroDivisorsRight_iff_isRightRegular {S : Submonoid R} :
    S ≤ nonZeroDivisorsRight R ↔ ∀ s : S, IsRightRegular (s : R) := by
  simp_rw [SetLike.le_def, isRightRegular_iff_mem_nonZeroDivisorsRight, Subtype.forall]
/-
**le_nonZeroDivisors_iff_isRegular** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_nonZeroDivisors_iff_isRegular {S : Submonoid R} : S <= R⁰ ↔ forall s : 
S, IsRegular (s : R)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma le_nonZeroDivisors_iff_isRegular {S : Submonoid R} :
    S ≤ R⁰ ↔ ∀ s : S, IsRegular (s : R) := by
  simp_rw [nonZeroDivisors, le_inf_iff, le_nonZeroDivisorsLeft_iff_isLeftRegular,
    le_nonZeroDivisorsRight_iff_isRightRegular, isRegular_iff, forall_and]
/-
**mul_cancel_left_mem_nonZeroDivisorsLeft** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_cancel_left_mem_nonZeroDivisorsLeft (hr : r in nonZeroDivisorsLeft R) 
: r * x = r * y ↔ x = y
参数：hr : r in nonZeroDivisorsLeft R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `isLeftRegular_iff_mem_nonZeroDivisorsLeft`：isLeftRegular_iff_mem_nonZero
DivisorsLeft : IsLeftRegular r ↔ r in nonZeroDivisorsLeft R
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
lemma mul_cancel_left_mem_nonZeroDivisorsLeft (hr : r ∈ nonZeroDivisorsLeft R) :
    r * x = r * y ↔ x = y :=
  ⟨(isLeftRegular_iff_mem_nonZeroDivisorsLeft.mpr hr ·), congr_arg (r * ·)⟩
/-
**mul_cancel_right_mem_nonZeroDivisorsRight** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_cancel_right_mem_nonZeroDivisorsRight (hr : r in nonZeroDivisorsRight 
R) : x * r = y * r ↔ x = y
参数：hr : r in nonZeroDivisorsRight R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `isRightRegular_iff_mem_nonZeroDivisorsRight`：isRightRegular_iff_mem_nonZ
eroDivisorsRight : IsRightRegular r ↔ r in nonZeroDivisorsRight R
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
lemma mul_cancel_right_mem_nonZeroDivisorsRight (hr : r ∈ nonZeroDivisorsRight R) :
    x * r = y * r ↔ x = y :=
  ⟨(isRightRegular_iff_mem_nonZeroDivisorsRight.mpr hr ·), congr_arg (· * r)⟩

@[simp]
/-
**mul_cancel_left_mem_nonZeroDivisors** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_cancel_left_mem_nonZeroDivisors (hr : r in R⁰) : r * x = r * y ↔ x = y
参数：hr : r in R⁰。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `mul_cancel_left_mem_nonZeroDivisorsLeft`：mul_cancel_left_mem_nonZeroDivi
sorsLeft (hr : r in nonZeroDivisorsLeft R) : r * x = r * y ↔ x = y
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma mul_cancel_left_mem_nonZeroDivisors (hr : r ∈ R⁰) : r * x = r * y ↔ x = y :=
  mul_cancel_left_mem_nonZeroDivisorsLeft hr.1
/-
**mul_cancel_left_coe_nonZeroDivisors** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_cancel_left_coe_nonZeroDivisors {c : R⁰} : (c : R) * x = c * y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `mul_cancel_left_mem_nonZeroDivisors`：mul_cancel_left_mem_nonZeroDivisors
 (hr : r in R⁰) : r * x = r * y ↔ x = y
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
lemma mul_cancel_left_coe_nonZeroDivisors {c : R⁰} : (c : R) * x = c * y ↔ x = y :=
  mul_cancel_left_mem_nonZeroDivisors c.prop
/-
**mul_cancel_right_mem_nonZeroDivisors** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_cancel_right_mem_nonZeroDivisors (hr : r in R⁰) : x * r = y * r ↔ x = 
y
参数：hr : r in R⁰。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `mul_cancel_right_mem_nonZeroDivisorsRight`：mul_cancel_right_mem_nonZeroD
ivisorsRight (hr : r in nonZeroDivisorsRight R) : x * r = y * r ↔ x = y
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma mul_cancel_right_mem_nonZeroDivisors (hr : r ∈ R⁰) : x * r = y * r ↔ x = y :=
  mul_cancel_right_mem_nonZeroDivisorsRight hr.2
/-
**mul_cancel_right_coe_nonZeroDivisors** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mul_cancel_right_coe_nonZeroDivisors {c : R⁰} : x * c = y * c ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `mul_cancel_right_mem_nonZeroDivisors`：mul_cancel_right_mem_nonZeroDiviso
rs (hr : r in R⁰) : x * r = y * r ↔ x = y
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
lemma mul_cancel_right_coe_nonZeroDivisors {c : R⁰} : x * c = y * c ↔ x = y :=
  mul_cancel_right_mem_nonZeroDivisors c.prop

/-- In a finite ring, an element is a unit iff it is a non-zero-divisor. -/
/-
**isUnit_iff_mem_nonZeroDivisors_of_finite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isUnit_iff_mem_nonZeroDivisors_of_finite [Finite R] : IsUnit a ↔ a in nonZ
eroDivisors R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `isRegular_iff_mem_nonZeroDivisors`：isRegular_iff_mem_nonZeroDivisors : I
sRegular r ↔ r in R⁰
· 使用定理 `isRegular_iff_isUnit_of_finite`：isRegular_iff_isUnit_of_finite : IsRegul
ar r ↔ IsUnit r where mp h
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
In a finite ring, an element is a unit iff it is a non-zero-divisor.
-/
lemma isUnit_iff_mem_nonZeroDivisors_of_finite [Finite R] : IsUnit a ↔ a ∈ nonZeroDivisors R := by
  rw [← isRegular_iff_mem_nonZeroDivisors, isRegular_iff_isUnit_of_finite]
/-
**dvd_cancel_left_mem_nonZeroDivisors** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dvd_cancel_left_mem_nonZeroDivisors (hr : r in R⁰) : r * x ∣ r * y ↔ x ∣ y
参数：hr : r in R⁰。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLeftRegular.dvd_cancel_left`：IsLeftRegular.dvd_cancel_left (h : IsLeft
Regular a) : a * b ∣ a * c ↔ b ∣ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `isLeftRegular_iff_mem_nonZeroDivisorsLeft`：isLeftRegular_iff_mem_nonZero
DivisorsLeft : IsLeftRegular r ↔ r in nonZeroDivisorsLeft R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma dvd_cancel_left_mem_nonZeroDivisors (hr : r ∈ R⁰) : r * x ∣ r * y ↔ x ∣ y :=
  (isLeftRegular_iff_mem_nonZeroDivisorsLeft.mpr hr.1).dvd_cancel_left
/-
**dvd_cancel_left_coe_nonZeroDivisors** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dvd_cancel_left_coe_nonZeroDivisors {c : R⁰} : c * x ∣ c * y ↔ x ∣ y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `dvd_cancel_left_mem_nonZeroDivisors`：dvd_cancel_left_mem_nonZeroDivisors
 (hr : r in R⁰) : r * x ∣ r * y ↔ x ∣ y
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
lemma dvd_cancel_left_coe_nonZeroDivisors {c : R⁰} : c * x ∣ c * y ↔ x ∣ y :=
  dvd_cancel_left_mem_nonZeroDivisors c.prop

end Ring

section CommRing
variable {R : Type*} [CommRing R] {r x y : R}

/-
**dvd_cancel_right_mem_nonZeroDivisors** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dvd_cancel_right_mem_nonZeroDivisors (hr : r in R⁰) : x * r ∣ y * r ↔ x ∣ 
y
参数：hr : r in R⁰。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `dvd_cancel_left_mem_nonZeroDivisors`：dvd_cancel_left_mem_nonZeroDivisors
 (hr : r in R⁰) : r * x ∣ r * y ↔ x ∣ y
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma dvd_cancel_right_mem_nonZeroDivisors (hr : r ∈ R⁰) : x * r ∣ y * r ↔ x ∣ y := by
  simp_rw [← mul_comm r, dvd_cancel_left_mem_nonZeroDivisors hr]
/-
**dvd_cancel_right_coe_nonZeroDivisors** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：dvd_cancel_right_coe_nonZeroDivisors {c : R⁰} : x * c ∣ y * c ↔ x ∣ y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `dvd_cancel_right_mem_nonZeroDivisors`：dvd_cancel_right_mem_nonZeroDiviso
rs (hr : r in R⁰) : x * r ∣ y * r ↔ x ∣ y
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
lemma dvd_cancel_right_coe_nonZeroDivisors {c : R⁰} : x * c ∣ y * c ↔ x ∣ y :=
  dvd_cancel_right_mem_nonZeroDivisors c.prop

end CommRing

