/-
Copyright (c) 2022 Abby J. Goldberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abby J. Goldberg, Mario Carneiro, Heather Macbeth
-/
module

public meta import Mathlib.Data.Ineq
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Data.Ineq
public meta import Mathlib.Tactic.ToAdditive

/-!
# Lemmas for the `linear_combination` tactic

These should not be used directly in user code.
-/

public meta section

open Lean

namespace Mathlib.Tactic.LinearCombination

variable {α : Type*} {a a' a₁ a₂ b b' b₁ b₂ c : α}
variable {K : Type*} {t s : K}

/-! ### Addition -/

/-
**Mathlib.Tactic.LinearCombination.add_eq_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.
Tactic.LinearCombination`。
形式化陈述：add_eq_eq [Add α] (p₁ : (a₁ : α) = b₁) (p₂ : a₂ = b₂) : a₁ + a₂ = b₁ + b₂
参数：p₁ : (a₁ : α) = b₁；p₂ : a₂ = b₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Addition
-/
theorem add_eq_eq [Add α] (p₁ : (a₁ : α) = b₁) (p₂ : a₂ = b₂) : a₁ + a₂ = b₁ + b₂ := p₁ ▸ p₂ ▸ rfl
/-
**Mathlib.Tactic.LinearCombination.add_le_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.
Tactic.LinearCombination`。
形式化陈述：add_le_eq [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α] (p₁ : 
(a₁ : α) <= b₁) (p₂ : a₂ = b₂) : a₁ + a₂ <= b₁ + b₂
参数：p₁ : (a₁ : α) <= b₁；p₂ : a₂ = b₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_le_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [i : Ad
dRightMono α] {b c : α}, b ≤ c → ∀ (a : α), b + a ≤ c + a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem add_le_eq [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α]
    (p₁ : (a₁ : α) ≤ b₁) (p₂ : a₂ = b₂) : a₁ + a₂ ≤ b₁ + b₂ :=
  p₂ ▸ add_le_add_left p₁ b₂
/-
**Mathlib.Tactic.LinearCombination.add_eq_le** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.
Tactic.LinearCombination`。
形式化陈述：add_eq_le [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α] (p₁ : 
(a₁ : α) = b₁) (p₂ : a₂ <= b₂) : a₁ + a₂ <= b₁ + b₂
参数：p₁ : (a₁ : α) = b₁；p₂ : a₂ <= b₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_le_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [AddLe
ftMono α] {b c : α}, b ≤ c → ∀ (a : α), a + b ≤ a + c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem add_eq_le [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α]
    (p₁ : (a₁ : α) = b₁) (p₂ : a₂ ≤ b₂) : a₁ + a₂ ≤ b₁ + b₂ :=
  p₁ ▸ add_le_add_right p₂ b₁
/-
**Mathlib.Tactic.LinearCombination.add_lt_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.
Tactic.LinearCombination`。
形式化陈述：add_lt_eq [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α] 
(p₁ : (a₁ : α) < b₁) (p₂ : a₂ = b₂) : a₁ + a₂ < b₁ + b₂
参数：p₁ : (a₁ : α) < b₁；p₂ : a₂ = b₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem add_lt_eq [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
    (p₁ : (a₁ : α) < b₁) (p₂ : a₂ = b₂) : a₁ + a₂ < b₁ + b₂ :=
  p₂ ▸ add_lt_add_left p₁ b₂
/-
**Mathlib.Tactic.LinearCombination.add_eq_lt** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.
Tactic.LinearCombination`。
形式化陈述：add_eq_lt [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α] 
{a₁ b₁ a₂ b₂ : α} (p₁ : a₁ = b₁) (p₂ : a₂ < b₂) : a₁ + a₂ < b₁ + b₂
参数：p₁ : a₁ = b₁；p₂ : a₂ < b₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_lt_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [AddLe
ftStrictMono α] {b c : α}, b < c → ∀ (a : α), a + b < a + c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem add_eq_lt [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α] {a₁ b₁ a₂ b₂ : α}
    (p₁ : a₁ = b₁) (p₂ : a₂ < b₂) : a₁ + a₂ < b₁ + b₂ :=
  p₁ ▸ add_lt_add_right p₂ b₁

/-! ### Multiplication -/

/-
**Mathlib.Tactic.LinearCombination.mul_eq_const** 是 Mathlib 中的一个定理，位于命名空间 `Mathl
ib.Tactic.LinearCombination`。
形式化陈述：mul_eq_const [Mul α] (p : a = b) (c : α) : a * c = b * c
参数：p : a = b；c : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Multiplication
-/
theorem mul_eq_const [Mul α] (p : a = b) (c : α) : a * c = b * c := p ▸ rfl
/-
**Mathlib.Tactic.LinearCombination.mul_le_const** 是 Mathlib 中的一个定理，位于命名空间 `Mathl
ib.Tactic.LinearCombination`。
形式化陈述：mul_le_const [Semiring α] [PartialOrder α] [IsOrderedRing α] (p : b <= c) 
{a : α} (ha : 0 <= a) : b * a <= c * a
参数：p : b <= c；ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
-/
theorem mul_le_const [Semiring α] [PartialOrder α] [IsOrderedRing α]
    (p : b ≤ c) {a : α} (ha : 0 ≤ a) :
    b * a ≤ c * a :=
  mul_le_mul_of_nonneg_right p ha
/-
**Mathlib.Tactic.LinearCombination.mul_lt_const** 是 Mathlib 中的一个定理，位于命名空间 `Mathl
ib.Tactic.LinearCombination`。
形式化陈述：mul_lt_const [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] (p : b 
< c) {a : α} (ha : 0 < a) : b * a < c * a
参数：p : b < c；ha : 0 < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul_of_pos_right`：mul_lt_mul_of_pos_right [MulPosStrictMono α] (h
bc : b < c) (ha : 0 < a) : b * a < c * a
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
-/
theorem mul_lt_const [Semiring α] [PartialOrder α] [IsStrictOrderedRing α]
    (p : b < c) {a : α} (ha : 0 < a) :
    b * a < c * a :=
  mul_lt_mul_of_pos_right p ha
/-
**Mathlib.Tactic.LinearCombination.mul_lt_const_weak** 是 Mathlib 中的一个定理，位于命名空间 `
Mathlib.Tactic.LinearCombination`。
形式化陈述：mul_lt_const_weak [Semiring α] [PartialOrder α] [IsOrderedRing α] (p : b <
 c) {a : α} (ha : 0 <= a) : b * a <= c * a
参数：p : b < c；ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem mul_lt_const_weak [Semiring α] [PartialOrder α] [IsOrderedRing α]
    (p : b < c) {a : α} (ha : 0 ≤ a) :
    b * a ≤ c * a :=
  mul_le_mul_of_nonneg_right p.le ha
/-
**Mathlib.Tactic.LinearCombination.mul_const_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mathl
ib.Tactic.LinearCombination`。
形式化陈述：mul_const_eq [Mul α] (p : b = c) (a : α) : a * b = a * c
参数：p : b = c；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_const_eq [Mul α] (p : b = c) (a : α) : a * b = a * c := p ▸ rfl
/-
**Mathlib.Tactic.LinearCombination.mul_const_le** 是 Mathlib 中的一个定理，位于命名空间 `Mathl
ib.Tactic.LinearCombination`。
形式化陈述：mul_const_le [Semiring α] [PartialOrder α] [IsOrderedRing α] (p : b <= c) 
{a : α} (ha : 0 <= a) : a * b <= a * c
参数：p : b <= c；ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
theorem mul_const_le [Semiring α] [PartialOrder α] [IsOrderedRing α]
    (p : b ≤ c) {a : α} (ha : 0 ≤ a) :
    a * b ≤ a * c :=
  mul_le_mul_of_nonneg_left p ha
/-
**Mathlib.Tactic.LinearCombination.mul_const_lt** 是 Mathlib 中的一个定理，位于命名空间 `Mathl
ib.Tactic.LinearCombination`。
形式化陈述：mul_const_lt [Semiring α] [PartialOrder α] [IsStrictOrderedRing α] (p : b 
< c) {a : α} (ha : 0 < a) : a * b < a * c
参数：p : b < c；ha : 0 < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_lt_mul_of_pos_left`：mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc
 : b < c) (ha : 0 < a) : a * b < a * c
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
-/
theorem mul_const_lt [Semiring α] [PartialOrder α] [IsStrictOrderedRing α]
    (p : b < c) {a : α} (ha : 0 < a) :
    a * b < a * c :=
  mul_lt_mul_of_pos_left p ha
/-
**Mathlib.Tactic.LinearCombination.mul_const_lt_weak** 是 Mathlib 中的一个定理，位于命名空间 `
Mathlib.Tactic.LinearCombination`。
形式化陈述：mul_const_lt_weak [Semiring α] [PartialOrder α] [IsOrderedRing α] (p : b <
 c) {a : α} (ha : 0 <= a) : a * b <= a * c
参数：p : b < c；ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem mul_const_lt_weak [Semiring α] [PartialOrder α] [IsOrderedRing α]
    (p : b < c) {a : α} (ha : 0 ≤ a) :
    a * b ≤ a * c :=
  mul_le_mul_of_nonneg_left p.le ha

/-! ### Scalar multiplication -/

/-
**Mathlib.Tactic.LinearCombination.smul_eq_const** 是 Mathlib 中的一个定理，位于命名空间 `Math
lib.Tactic.LinearCombination`。
形式化陈述：smul_eq_const [SMul K α] (p : t = s) (c : α) : t • c = s • c
参数：p : t = s；c : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Scalar multiplication
-/
theorem smul_eq_const [SMul K α] (p : t = s) (c : α) : t • c = s • c := p ▸ rfl
/-
**Mathlib.Tactic.LinearCombination.smul_le_const** 是 Mathlib 中的一个定理，位于命名空间 `Math
lib.Tactic.LinearCombination`。
形式化陈述：smul_le_const [Ring K] [PartialOrder K] [IsOrderedRing K] [AddCommGroup α]
 [PartialOrder α] [IsOrderedAddMonoid α] [Module K α] [IsOrderedModule K α] (p :
 t <= s) {a : α} (ha : 0 <= a) : t • a <= s • a
参数：p : t <= s；ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `smul_le_smul_of_nonneg_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α
} {b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_
3 : Zero β] [SMulP…
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
-/
theorem smul_le_const [Ring K] [PartialOrder K] [IsOrderedRing K]
    [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α] [Module K α]
    [IsOrderedModule K α] (p : t ≤ s) {a : α} (ha : 0 ≤ a) :
    t • a ≤ s • a :=
  smul_le_smul_of_nonneg_right p ha
/-
**Mathlib.Tactic.LinearCombination.smul_lt_const** 是 Mathlib 中的一个定理，位于命名空间 `Math
lib.Tactic.LinearCombination`。
形式化陈述：smul_lt_const [Ring K] [PartialOrder K] [IsOrderedRing K] [AddCommGroup α]
 [PartialOrder α] [IsOrderedAddMonoid α] [Module K α] [IsStrictOrderedModule K α
] (p : t < s) {a : α} (ha : 0 < a) : t • a < s • a
参数：p : t < s；ha : 0 < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `smul_lt_smul_of_pos_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α} {
b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 :
 Zero β] [SMulP…
· 使用定理 `IsStrictOrderedModule.toPosSMulStrictMono`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
α}   {inst_4 : Zero β} [self : …
-/
theorem smul_lt_const [Ring K] [PartialOrder K] [IsOrderedRing K]
    [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α] [Module K α]
    [IsStrictOrderedModule K α] (p : t < s) {a : α} (ha : 0 < a) :
    t • a < s • a :=
  smul_lt_smul_of_pos_right p ha
/-
**Mathlib.Tactic.LinearCombination.smul_lt_const_weak** 是 Mathlib 中的一个定理，位于命名空间 
`Mathlib.Tactic.LinearCombination`。
形式化陈述：smul_lt_const_weak [Ring K] [PartialOrder K] [IsOrderedRing K] [AddCommGro
up α] [PartialOrder α] [IsOrderedAddMonoid α] [Module K α] [IsStrictOrderedModul
e K α] (p : t < s) {a : α} (ha : 0 <= a) : t • a <= s • a
参数：p : t < s；ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `smul_le_smul_of_nonneg_right`：∀ {α : Type u_1} {β : Type u_2} {a₁ a₂ : α
} {b : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_
3 : Zero β] [SMulP…
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem smul_lt_const_weak [Ring K] [PartialOrder K] [IsOrderedRing K]
    [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α] [Module K α]
    [IsStrictOrderedModule K α] (p : t < s) {a : α} (ha : 0 ≤ a) :
    t • a ≤ s • a :=
  smul_le_smul_of_nonneg_right p.le ha
/-
**Mathlib.Tactic.LinearCombination.smul_const_eq** 是 Mathlib 中的一个定理，位于命名空间 `Math
lib.Tactic.LinearCombination`。
形式化陈述：smul_const_eq [SMul K α] (p : b = c) (s : K) : s • b = s • c
参数：p : b = c；s : K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_const_eq [SMul K α] (p : b = c) (s : K) : s • b = s • c := p ▸ rfl
/-
**Mathlib.Tactic.LinearCombination.smul_const_le** 是 Mathlib 中的一个定理，位于命名空间 `Math
lib.Tactic.LinearCombination`。
形式化陈述：smul_const_le [Semiring K] [PartialOrder K] [AddCommMonoid α] [PartialOrde
r α] [Module K α] [PosSMulMono K α] (p : b <= c) {s : K} (hs : 0 <= s) : s • b <
= s • c
参数：p : b <= c；hs : 0 <= s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
-/
theorem smul_const_le [Semiring K] [PartialOrder K]
    [AddCommMonoid α] [PartialOrder α] [Module K α]
    [PosSMulMono K α] (p : b ≤ c) {s : K} (hs : 0 ≤ s) :
    s • b ≤ s • c :=
  smul_le_smul_of_nonneg_left p hs
/-
**Mathlib.Tactic.LinearCombination.smul_const_lt** 是 Mathlib 中的一个定理，位于命名空间 `Math
lib.Tactic.LinearCombination`。
形式化陈述：smul_const_lt [Semiring K] [PartialOrder K] [AddCommMonoid α] [PartialOrde
r α] [Module K α] [PosSMulStrictMono K α] (p : b < c) {s : K} (hs : 0 < s) : s •
 b < s • c
参数：p : b < c；hs : 0 < s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `smul_lt_smul_of_pos_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁ b₂
 : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 : 
Zero α] [PosSM…
-/
theorem smul_const_lt [Semiring K] [PartialOrder K]
    [AddCommMonoid α] [PartialOrder α] [Module K α]
    [PosSMulStrictMono K α] (p : b < c) {s : K} (hs : 0 < s) :
    s • b < s • c :=
  smul_lt_smul_of_pos_left p hs
/-
**Mathlib.Tactic.LinearCombination.smul_const_lt_weak** 是 Mathlib 中的一个定理，位于命名空间 
`Mathlib.Tactic.LinearCombination`。
形式化陈述：smul_const_lt_weak [Semiring K] [PartialOrder K] [AddCommMonoid α] [Partia
lOrder α] [Module K α] [PosSMulMono K α] (p : b < c) {s : K} (hs : 0 <= s) : s •
 b <= s • c
参数：p : b < c；hs : 0 <= s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem smul_const_lt_weak [Semiring K] [PartialOrder K]
    [AddCommMonoid α] [PartialOrder α] [Module K α]
    [PosSMulMono K α] (p : b < c) {s : K} (hs : 0 ≤ s) :
    s • b ≤ s • c :=
  smul_le_smul_of_nonneg_left p.le hs

/-! ### Division -/

/-
**Mathlib.Tactic.LinearCombination.div_eq_const** 是 Mathlib 中的一个定理，位于命名空间 `Mathl
ib.Tactic.LinearCombination`。
形式化陈述：div_eq_const [Div α] (p : a = b) (c : α) : a / c = b / c
参数：p : a = b；c : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Division
-/
theorem div_eq_const [Div α] (p : a = b) (c : α) : a / c = b / c := p ▸ rfl
/-
**Mathlib.Tactic.LinearCombination.div_le_const** 是 Mathlib 中的一个定理，位于命名空间 `Mathl
ib.Tactic.LinearCombination`。
形式化陈述：div_le_const [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] (p : b 
<= c) {a : α} (ha : 0 <= a) : b / a <= c / a
参数：p : b <= c；ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `div_le_div_of_nonneg_right`：div_le_div_of_nonneg_right (hab : a <= b) (h
c : 0 <= c) : a / c <= b / c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
-/
theorem div_le_const [Semifield α] [LinearOrder α] [IsStrictOrderedRing α]
    (p : b ≤ c) {a : α} (ha : 0 ≤ a) : b / a ≤ c / a :=
  div_le_div_of_nonneg_right p ha
/-
**Mathlib.Tactic.LinearCombination.div_lt_const** 是 Mathlib 中的一个定理，位于命名空间 `Mathl
ib.Tactic.LinearCombination`。
形式化陈述：div_lt_const [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] (p : b 
< c) {a : α} (ha : 0 < a) : b / a < c / a
参数：p : b < c；ha : 0 < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `div_lt_div_of_pos_right`：div_lt_div_of_pos_right (h : a < b) (hc : 0 < c
) : a / c < b / c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
-/
theorem div_lt_const [Semifield α] [LinearOrder α] [IsStrictOrderedRing α]
    (p : b < c) {a : α} (ha : 0 < a) : b / a < c / a :=
  div_lt_div_of_pos_right p ha
/-
**Mathlib.Tactic.LinearCombination.div_lt_const_weak** 是 Mathlib 中的一个定理，位于命名空间 `
Mathlib.Tactic.LinearCombination`。
形式化陈述：div_lt_const_weak [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] (p
 : b < c) {a : α} (ha : 0 <= a) : b / a <= c / a
参数：p : b < c；ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `div_le_div_of_nonneg_right`：div_le_div_of_nonneg_right (hab : a <= b) (h
c : 0 <= c) : a / c <= b / c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem div_lt_const_weak [Semifield α] [LinearOrder α] [IsStrictOrderedRing α]
    (p : b < c) {a : α} (ha : 0 ≤ a) :
    b / a ≤ c / a :=
  div_le_div_of_nonneg_right p.le ha

/-! ### Lemmas constructing the reduction of a goal to a specified built-up hypothesis -/

/-
**Mathlib.Tactic.LinearCombination.eq_of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.T
actic.LinearCombination`。
形式化陈述：eq_of_eq [Add α] [IsRightCancelAdd α] (p : (a : α) = b) (H : a' + b = b' +
 a) : a' = b'
参数：p : (a : α) = b；H : a' + b = b' + a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_right_cancel`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G] {
a b c : G}, a + b = c + b → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
### Lemmas constructing the reduction of a goal to a specified built-up hypothes
is
-/
theorem eq_of_eq [Add α] [IsRightCancelAdd α] (p : (a : α) = b) (H : a' + b = b' + a) :
    a' = b' := by
  rw [p] at H
  exact add_right_cancel H
/-
**Mathlib.Tactic.LinearCombination.le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.T
actic.LinearCombination`。
形式化陈述：le_of_le [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α] (
p : (a : α) <= b) (H : a' + b <= b' + a) : a' <= b'
参数：p : (a : α) <= b；H : a' + b <= b' + a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_le_add_iff_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [A
ddRightMono α] [AddRightReflectLE α] (a : α) {b c : α},   b + a ≤ c + a ↔ b ≤ c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `IsCancelAdd.toIsRightCancelAdd`：∀ {G : Type u} {inst : Add G} [self : Is
CancelAdd G], IsRightCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
-/
theorem le_of_le [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
    (p : (a : α) ≤ b) (H : a' + b ≤ b' + a) :
    a' ≤ b' := by
  grw [← add_le_add_iff_right b, H, p]
/-
**Mathlib.Tactic.LinearCombination.le_of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.T
actic.LinearCombination`。
形式化陈述：le_of_eq [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α] (
p : (a : α) = b) (H : a' + b <= b' + a) : a' <= b'
参数：p : (a : α) = b；H : a' + b <= b' + a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_le_add_iff_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [A
ddRightMono α] [AddRightReflectLE α] (a : α) {b c : α},   b + a ≤ c + a ↔ b ≤ c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `IsCancelAdd.toIsRightCancelAdd`：∀ {G : Type u} {inst : Add G} [self : Is
CancelAdd G], IsRightCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
-/
theorem le_of_eq [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
    (p : (a : α) = b) (H : a' + b ≤ b' + a) :
    a' ≤ b' := by
  rwa [p, add_le_add_iff_right] at H
/-
**Mathlib.Tactic.LinearCombination.le_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.T
actic.LinearCombination`。
形式化陈述：le_of_lt [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α] (
p : (a : α) < b) (H : a' + b <= b' + a) : a' <= b'
参数：p : (a : α) < b；H : a' + b <= b' + a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.LinearCombination.le_of_le`：le_of_le [AddCommMonoid α] [P
artialOrder α] [IsOrderedCancelAddMonoid α] (p : (a : α) <= b) (H : a' + b <= b'
 + a) : a' <= b'
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem le_of_lt [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
    (p : (a : α) < b) (H : a' + b ≤ b' + a) :
    a' ≤ b' :=
  le_of_le p.le H
/-
**Mathlib.Tactic.LinearCombination.lt_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.T
actic.LinearCombination`。
形式化陈述：lt_of_le [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α] (
p : (a : α) <= b) (H : a' + b < b' + a) : a' < b'
参数：p : (a : α) <= b；H : a' + b < b' + a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `lt_imp_lt_of_le_of_le`：lt_imp_lt_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a < b -> c < d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
-/
theorem lt_of_le [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
    (p : (a : α) ≤ b) (H : a' + b < b' + a) :
    a' < b' := by
  grw [p] at H; simpa using H
/-
**Mathlib.Tactic.LinearCombination.lt_of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.T
actic.LinearCombination`。
形式化陈述：lt_of_eq [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α] (
p : (a : α) = b) (H : a' + b < b' + a) : a' < b'
参数：p : (a : α) = b；H : a' + b < b' + a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_lt_add_iff_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [A
ddRightStrictMono α] [AddRightReflectLT α] (a : α) {b c : α},   b + a < c + a ↔ 
b < c
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
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
-/
theorem lt_of_eq [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
    (p : (a : α) = b) (H : a' + b < b' + a) :
    a' < b' := by
  rwa [p, add_lt_add_iff_right] at H
/-
**Mathlib.Tactic.LinearCombination.lt_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.T
actic.LinearCombination`。
形式化陈述：lt_of_lt [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α] (
p : (a : α) < b) (H : a' + b <= b' + a) : a' < b'
参数：p : (a : α) < b；H : a' + b <= b' + a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_lt_add_iff_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [A
ddRightStrictMono α] [AddRightReflectLT α] (a : α) {b c : α},   b + a < c + a ↔ 
b < c
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
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `lt_imp_lt_of_le_of_le`：lt_imp_lt_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a < b -> c < d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_lt_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [AddLe
ftStrictMono α] {b c : α}, b < c → ∀ (a : α), a + b < a + c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
-/
theorem lt_of_lt [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
    (p : (a : α) < b) (H : a' + b ≤ b' + a) :
    a' < b' := by
  grw [← add_lt_add_iff_right b, H]
  gcongr

alias ⟨eq_rearrange, _⟩ := sub_eq_zero
/-
**Mathlib.Tactic.LinearCombination.le_rearrange** 是 Mathlib 中的一个定理，位于命名空间 `Mathl
ib.Tactic.LinearCombination`。
形式化陈述：le_rearrange {α : Type*} [AddCommGroup α] [PartialOrder α] [IsOrderedAddMo
noid α] {a b : α} (h : a - b <= 0) : a <= b
参数：h : a - b <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_nonpos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, a - b ≤ 0 ↔ a ≤ b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem le_rearrange {α : Type*} [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
    {a b : α} (h : a - b ≤ 0) : a ≤ b :=
  sub_nonpos.mp h
/-
**Mathlib.Tactic.LinearCombination.lt_rearrange** 是 Mathlib 中的一个定理，位于命名空间 `Mathl
ib.Tactic.LinearCombination`。
形式化陈述：lt_rearrange {α : Type*} [AddCommGroup α] [PartialOrder α] [IsOrderedAddMo
noid α] {a b : α} (h : a - b < 0) : a < b
参数：h : a - b < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_neg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, a - b < 0 ↔ a < b
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
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem lt_rearrange {α : Type*} [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
    {a b : α} (h : a - b < 0) : a < b :=
  sub_neg.mp h
/-
**Mathlib.Tactic.LinearCombination.eq_of_add_pow** 是 Mathlib 中的一个定理，位于命名空间 `Math
lib.Tactic.LinearCombination`。
形式化陈述：eq_of_add_pow [Ring α] [NoZeroDivisors α] (n : Nat) (p : (a : α) = b) (H :
 (a' - b') ^ n - (a - b) = 0) : a' = b'
参数：n : Nat；p : (a : α) = b；H : (a' - b') ^ n - (a - b) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `eq_zero_of_pow_eq_zero`：eq_zero_of_pow_eq_zero [Zero R] [Pow R Nat] [IsR
educed R] {n : Nat} (h : x ^ n = 0) : x = 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
-/
theorem eq_of_add_pow [Ring α] [NoZeroDivisors α] (n : ℕ) (p : (a : α) = b)
    (H : (a' - b') ^ n - (a - b) = 0) : a' = b' := by
  rw [← sub_eq_zero] at p ⊢; apply eq_zero_of_pow_eq_zero (n := n); rwa [sub_eq_zero, p] at H

end Tactic.LinearCombination

/-! ### Lookup functions for lemmas by operation and relation(s) -/

open Tactic.LinearCombination

namespace Ineq

/-- Given two (in)equalities, look up the lemma to add them. -/
/-
**Mathlib.Ineq.addRelRelData** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Ineq`。
形式化陈述：Mathlib.Ineq → Mathlib.Ineq → Name
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two (in)equalities, look up the lemma to add them.
-/
def addRelRelData : Ineq → Ineq → Name
  | eq, eq => ``add_eq_eq
  | eq, le => ``add_eq_le
  | eq, lt => ``add_eq_lt
  | le, eq => ``add_le_eq
  | le, le => ``add_le_add
  | le, lt => ``add_lt_add_of_le_of_lt
  | lt, eq => ``add_lt_eq
  | lt, le => ``add_lt_add_of_lt_of_le
  | lt, lt => ``add_lt_add

/-- Finite inductive type extending `Mathlib.Ineq`: a type of inequality (`eq`, `le` or `lt`),
together with, in the case of `lt`, a Boolean, typically representing the strictness (< or ≤) of
some other inequality. -/
/-
**Mathlib.Ineq.WithStrictness** 是 Mathlib 中的一个归纳类型，位于命名空间 `Mathlib.Ineq`。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Finite inductive type extending `Mathlib.Ineq`: a type of inequality (`eq`, `le`
 or `lt`),
together with, in the case of `lt`, a Boolean, typically representing the strict
ness (< or ≤) of
some other inequality.
-/
protected inductive WithStrictness : Type
  | eq : Ineq.WithStrictness
  | le : Ineq.WithStrictness
  | lt (strict : Bool) : Ineq.WithStrictness

/-- Given an (in)equality, look up the lemma to left-multiply it by a constant.  If relevant, also
take into account the degree of positivity which can be proved of the constant: strict or
non-strict. -/
/-
**Mathlib.Ineq.mulRelConstData** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Ineq`。
形式化陈述：Mathlib.Ineq.WithStrictness → Name
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an (in)equality, look up the lemma to left-multiply it by a constant.  If 
relevant, also
take into account the degree of positivity which can be proved of the constant: 
strict or
non-strict.
-/
def mulRelConstData : Ineq.WithStrictness → Name
  | .eq => ``mul_eq_const
  | .le => ``mul_le_const
  | .lt true => ``mul_lt_const
  | .lt false => ``mul_lt_const_weak

/-- Given an (in)equality, look up the lemma to right-multiply it by a constant.  If relevant, also
take into account the degree of positivity which can be proved of the constant: strict or
non-strict. -/
/-
**Mathlib.Ineq.mulConstRelData** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Ineq`。
形式化陈述：Mathlib.Ineq.WithStrictness → Name
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an (in)equality, look up the lemma to right-multiply it by a constant.  If
 relevant, also
take into account the degree of positivity which can be proved of the constant: 
strict or
non-strict.
-/
def mulConstRelData : Ineq.WithStrictness → Name
  | .eq => ``mul_const_eq
  | .le => ``mul_const_le
  | .lt true => ``mul_const_lt
  | .lt false => ``mul_const_lt_weak

/-- Given an (in)equality, look up the lemma to left-scalar-multiply it by a constant (scalar).
If relevant, also take into account the degree of positivity which can be proved of the constant:
strict or non-strict. -/
/-
**Mathlib.Ineq.smulRelConstData** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Ineq`。
形式化陈述：Mathlib.Ineq.WithStrictness → Name
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an (in)equality, look up the lemma to left-scalar-multiply it by a constan
t (scalar).
If relevant, also take into account the degree of positivity which can be proved
 of the constant:
strict or non-strict.
-/
def smulRelConstData : Ineq.WithStrictness → Name
  | .eq => ``smul_eq_const
  | .le => ``smul_le_const
  | .lt true => ``smul_lt_const
  | .lt false => ``smul_lt_const_weak

/-- Given an (in)equality, look up the lemma to right-scalar-multiply it by a constant (vector).
If relevant, also take into account the degree of positivity which can be proved of the constant:
strict or non-strict. -/
/-
**Mathlib.Ineq.smulConstRelData** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Ineq`。
形式化陈述：Mathlib.Ineq.WithStrictness → Name
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an (in)equality, look up the lemma to right-scalar-multiply it by a consta
nt (vector).
If relevant, also take into account the degree of positivity which can be proved
 of the constant:
strict or non-strict.
-/
def smulConstRelData : Ineq.WithStrictness → Name
  | .eq => ``smul_const_eq
  | .le => ``smul_const_le
  | .lt true => ``smul_const_lt
  | .lt false => ``smul_const_lt_weak

/-- Given an (in)equality, look up the lemma to divide it by a constant.  If relevant, also take
into account the degree of positivity which can be proved of the constant: strict or non-strict. -/
/-
**Mathlib.Ineq.divRelConstData** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Ineq`。
形式化陈述：Mathlib.Ineq.WithStrictness → Name
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an (in)equality, look up the lemma to divide it by a constant.  If relevan
t, also take
into account the degree of positivity which can be proved of the constant: stric
t or non-strict.
-/
def divRelConstData : Ineq.WithStrictness → Name
  | .eq => ``div_eq_const
  | .le => ``div_le_const
  | .lt true => ``div_lt_const
  | .lt false => ``div_lt_const_weak

/-- Given two (in)equalities `P` and `Q`, look up the lemma to deduce `Q` from `P`, and the relation
appearing in the side condition produced by this lemma. -/
/-
**Mathlib.Ineq.relImpRelData** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Ineq`。
形式化陈述：Mathlib.Ineq → Mathlib.Ineq → Option (Name × Mathlib.Ineq)
参数：Name × Mathlib.Ineq。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two (in)equalities `P` and `Q`, look up the lemma to deduce `Q` from `P`, 
and the relation
appearing in the side condition produced by this lemma.
-/
def relImpRelData : Ineq → Ineq → Option (Name × Ineq)
  | eq, eq => some (``eq_of_eq, eq)
  | eq, le => some (``Tactic.LinearCombination.le_of_eq, le)
  | eq, lt => some (``lt_of_eq, lt)
  | le, eq => none
  | le, le => some (``le_of_le, le)
  | le, lt => some (``lt_of_le, lt)
  | lt, eq => none
  | lt, le => some (``Tactic.LinearCombination.le_of_lt, le)
  | lt, lt => some (``lt_of_lt, le)

/-- Given an (in)equality, look up the lemma to move everything to the LHS. -/
/-
**Mathlib.Ineq.rearrangeData** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Ineq`。
形式化陈述：Mathlib.Ineq → Name
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an (in)equality, look up the lemma to move everything to the LHS.
-/
def rearrangeData : Ineq → Name
  | eq => ``eq_rearrange
  | le => ``le_rearrange
  | lt => ``lt_rearrange

end Mathlib.Ineq

