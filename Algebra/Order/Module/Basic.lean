/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Invertible
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Module.Defs

/-!
# Further lemmas about monotonicity of scalar multiplication
-/

public section

variable {𝕜 R M : Type*}

section Semiring
variable [Semiring R] [Invertible (2 : R)] [Lattice M] [AddCommGroup M] [Module R M]
  [IsOrderedAddMonoid M]

variable (R) in
/-
**inf_eq_half_smul_add_sub_abs_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inf_eq_half_smul_add_sub_abs_sub (x y : M) : x ⊓ y = (⅟2 : R) • (x + y - |
y - x|)
参数：x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_nsmul_inf_eq_add_sub_abs_sub`：∀ {α : Type u_1} [inst : Lattice α] [i
nst_1 : AddCommGroup α] [AddLeftMono α] (a b : α), 2 • (a ⊓ b) = a + b - |b - a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `two_smul`：two_smul : (2 : R) • x = x + x
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `invOf_mul_self`：invOf_mul_self [Mul α] [One α] (a : α) [Invertible a] : 
⅟a * a = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
lemma inf_eq_half_smul_add_sub_abs_sub (x y : M) : x ⊓ y = (⅟2 : R) • (x + y - |y - x|) := by
  rw [← two_nsmul_inf_eq_add_sub_abs_sub x y, two_smul, ← two_smul R,
    smul_smul, invOf_mul_self, one_smul]

variable (R) in
/-
**sup_eq_half_smul_add_add_abs_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sup_eq_half_smul_add_add_abs_sub (x y : M) : x ⊔ y = (⅟2 : R) • (x + y + |
y - x|)
参数：x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_nsmul_sup_eq_add_add_abs_sub`：∀ {α : Type u_1} [inst : Lattice α] [i
nst_1 : AddCommGroup α] [AddLeftMono α] (a b : α), 2 • (a ⊔ b) = a + b + |b - a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `two_smul`：two_smul : (2 : R) • x = x + x
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `invOf_mul_self`：invOf_mul_self [Mul α] [One α] (a : α) [Invertible a] : 
⅟a * a = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
lemma sup_eq_half_smul_add_add_abs_sub (x y : M) : x ⊔ y = (⅟2 : R) • (x + y + |y - x|) := by
  rw [← two_nsmul_sup_eq_add_add_abs_sub x y, two_smul, ← two_smul R,
    smul_smul, invOf_mul_self, one_smul]

end Semiring

section Ring
variable [Ring R] [LinearOrder R] [IsOrderedRing R] [AddCommGroup M] [LinearOrder M]
  [IsOrderedAddMonoid M] [Module R M] [PosSMulMono R M]

@[simp]
/-
**abs_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：abs_smul (a : R) (b : M) : |a • b| = |a| • |b|
参数：a : R；b : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `abs_of_nonpos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], a ≤ 0 → |a| = -a
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem abs_smul (a : R) (b : M) : |a • b| = |a| • |b| := by
  obtain ha | ha := le_total a 0 <;> obtain hb | hb := le_total b 0 <;>
    simp [*, abs_of_nonneg, abs_of_nonpos, smul_nonneg, smul_nonpos_of_nonneg_of_nonpos,
      smul_nonpos_of_nonpos_of_nonneg, smul_nonneg_of_nonpos_of_nonpos]

end Ring

section DivisionSemiring
variable [DivisionSemiring 𝕜] [NeZero (2 : 𝕜)] [Lattice M] [AddCommGroup M] [Module 𝕜 M]
  [IsOrderedAddMonoid M]

variable (𝕜) in
/-
**inf_eq_half_smul_add_sub_abs_sub'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inf_eq_half_smul_add_sub_abs_sub' (x y : M) : x ⊓ y = (2⁻¹ : 𝕜) • (x + y -
 |y - x|)
参数：x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `two_ne_zero'`：two_ne_zero' [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用引理 `inf_eq_half_smul_add_sub_abs_sub`：inf_eq_half_smul_add_sub_abs_sub (x y 
: M) : x ⊓ y = (⅟2 : R) • (x + y - |y - x|)
-/
lemma inf_eq_half_smul_add_sub_abs_sub' (x y : M) : x ⊓ y = (2⁻¹ : 𝕜) • (x + y - |y - x|) :=
  let := invertibleOfNonzero (two_ne_zero' 𝕜); inf_eq_half_smul_add_sub_abs_sub 𝕜 x y

variable (𝕜) in
/-
**sup_eq_half_smul_add_add_abs_sub'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sup_eq_half_smul_add_add_abs_sub' (x y : M) : x ⊔ y = (2⁻¹ : 𝕜) • (x + y +
 |y - x|)
参数：x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `two_ne_zero'`：two_ne_zero' [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用引理 `sup_eq_half_smul_add_add_abs_sub`：sup_eq_half_smul_add_add_abs_sub (x y 
: M) : x ⊔ y = (⅟2 : R) • (x + y + |y - x|)
-/
lemma sup_eq_half_smul_add_add_abs_sub' (x y : M) : x ⊔ y = (2⁻¹ : 𝕜) • (x + y + |y - x|) :=
  let := invertibleOfNonzero (two_ne_zero' 𝕜); sup_eq_half_smul_add_add_abs_sub 𝕜 x y

end DivisionSemiring

