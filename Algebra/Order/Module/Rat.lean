/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Module.Rat
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.Module.Defs

/-!
# Monotonicity of the action by rational numbers
-/

public section

variable {α : Type*}

/-
**PosSMulMono.nnrat_of_rat** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：PosSMulMono.nnrat_of_rat [Preorder α] [MulAction Rat α] [MulAction Rat>=0 
α] [IsScalarTower Rat>=0 Rat α] [PosSMulMono Rat α] : PosSMulMono Rat>=0 α where
 smul_le_smul_of_nonneg_left _q hq _a₁ _a₂ ha
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `NNRat.cast_smul_eq_nnqsmul`：NNRat.cast_smul_eq_nnqsmul (R : Type*) [Divi
sionSemiring R] [MulAction R M] [MulAction Rat>=0 M] [IsScalarTower Rat>=0 R M] 
(q : Rat>=0) (x …
· 使用定理 `smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁
 b₂ : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3
 : Zero α] [PosSM…
-/
instance PosSMulMono.nnrat_of_rat [Preorder α] [MulAction ℚ α] [MulAction ℚ≥0 α]
    [IsScalarTower ℚ≥0 ℚ α] [PosSMulMono ℚ α] :
    PosSMulMono ℚ≥0 α where
  smul_le_smul_of_nonneg_left _q hq _a₁ _a₂ ha := by
    rw [← NNRat.cast_smul_eq_nnqsmul ℚ, ← NNRat.cast_smul_eq_nnqsmul ℚ]
    exact smul_le_smul_of_nonneg_left (α := ℚ) ha hq
/-
**PosSMulStrictMono.nnrat_of_rat** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：PosSMulStrictMono.nnrat_of_rat [Preorder α] [MulAction Rat>=0 α] [MulActio
n Rat α] [IsScalarTower Rat>=0 Rat α] [PosSMulStrictMono Rat α] : PosSMulStrictM
ono Rat>=0 α where smul_lt_smul_of_pos_left _q hq _a₁ _a₂ ha
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `NNRat.cast_smul_eq_nnqsmul`：NNRat.cast_smul_eq_nnqsmul (R : Type*) [Divi
sionSemiring R] [MulAction R M] [MulAction Rat>=0 M] [IsScalarTower Rat>=0 R M] 
(q : Rat>=0) (x …
· 使用定理 `smul_lt_smul_of_pos_left`：∀ {α : Type u_1} {β : Type u_2} {a : α} {b₁ b₂
 : β} [inst : SMul α β] [inst_1 : Preorder α] [inst_2 : Preorder β]   [inst_3 : 
Zero α] [PosSM…
-/
instance PosSMulStrictMono.nnrat_of_rat [Preorder α] [MulAction ℚ≥0 α] [MulAction ℚ α]
    [IsScalarTower ℚ≥0 ℚ α] [PosSMulStrictMono ℚ α] :
    PosSMulStrictMono ℚ≥0 α where
  smul_lt_smul_of_pos_left _q hq _a₁ _a₂ ha := by
    rw [← NNRat.cast_smul_eq_nnqsmul ℚ, ← NNRat.cast_smul_eq_nnqsmul ℚ]
    exact smul_lt_smul_of_pos_left (α := ℚ) ha hq

section LinearOrderedAddCommGroup
variable [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]

/-
**abs_nnqsmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : LinearOrder α] [IsOrder
edAddMonoid α]   [inst_3 : DistribMulAction ℚ≥0 α] [PosSMulMono ℚ≥0 α] (q : ℚ≥0)
 (a : α), |q • a| = q • |a|
参数：q : ℚ≥0；a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_of_nonpos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], a ≤ 0 → |a| = -a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
-/
@[simp] lemma abs_nnqsmul [DistribMulAction ℚ≥0 α] [PosSMulMono ℚ≥0 α] (q : ℚ≥0) (a : α) :
    |q • a| = q • |a| := by
  obtain ha | ha := le_total a 0 <;>
    simp [*, abs_of_nonneg, abs_of_nonpos, smul_nonneg, smul_nonpos_of_nonneg_of_nonpos]

end LinearOrderedAddCommGroup

section LinearOrderedSemifield
variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α]

/-
**LinearOrderedSemifield.toPosSMulStrictMono_rat** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：LinearOrderedSemifield.toPosSMulStrictMono_rat : PosSMulStrictMono Rat>=0 
α where smul_lt_smul_of_pos_left q hq a b hab
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NNRat.smul_def`：smul_def (q : Rat>=0) (a : K) : q • a = q * a
· 使用定理 `mul_lt_mul_of_pos_left`：mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc
 : b < c) (ha : 0 < a) : a * b < a * c
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NNRat.cast_pos`：∀ {K : Type u_5} [inst : Semifield K] [inst_1 : LinearOr
der K] [IsStrictOrderedRing K] {q : ℚ≥0}, 0 < ↑q ↔ 0 < q
-/
instance LinearOrderedSemifield.toPosSMulStrictMono_rat : PosSMulStrictMono ℚ≥0 α where
  smul_lt_smul_of_pos_left q hq a b hab := by
    rw [NNRat.smul_def, NNRat.smul_def]; exact mul_lt_mul_of_pos_left hab <| NNRat.cast_pos.2 hq

end LinearOrderedSemifield

section LinearOrderedField
variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

/-
**LinearOrderedField.toPosSMulStrictMono_rat** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：LinearOrderedField.toPosSMulStrictMono_rat : PosSMulStrictMono Rat α where
 smul_lt_smul_of_pos_left q hq a b hab
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Rat.smul_def`：smul_def (a : Rat) (x : K) : a • x = ↑a * x
· 使用定理 `mul_lt_mul_of_pos_left`：mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc
 : b < c) (ha : 0 < a) : a * b < a * c
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Rat.cast_pos`：∀ {q : ℚ} {K : Type u_5} [inst : Field K] [inst_1 : Linear
Order K] [IsStrictOrderedRing K], 0 < ↑q ↔ 0 < q
-/
instance LinearOrderedField.toPosSMulStrictMono_rat : PosSMulStrictMono ℚ α where
  smul_lt_smul_of_pos_left q hq a b hab := by
    rw [Rat.smul_def, Rat.smul_def]; exact mul_lt_mul_of_pos_left hab <| Rat.cast_pos.2 hq

end LinearOrderedField

