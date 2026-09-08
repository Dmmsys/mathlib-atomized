/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Order.Group.Synonym
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Order.PiLex

/-!
# Lexicographic product of algebraic order structures

This file proves that the lexicographic order on pi types is compatible with the pointwise algebraic
operations.
-/

public section

namespace Pi.Lex
variable {ι : Type*} {α : ι → Type*} [LinearOrder ι]

@[to_additive]
/-
**Pi.Lex.isOrderedCancelMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Pi.Lex`。
形式化陈述：isOrderedCancelMonoid [forall i, CommMonoid (α i)] [forall i, PartialOrder
 (α i)] [forall i, IsOrderedCancelMonoid (α i)] : IsOrderedCancelMonoid (Lex (fo
rall i, α i)) where mul_le_mul_left _ _ hxy z
参数：α i；α i；α i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `mul_lt_mul_left`：mul_lt_mul_left [i : MulRightStrictMono α] {b c : α} (b
c : b < c) (a : α) : b * a < c * a
· 使用定理 `instIsRightCancelMulOfMulRightReflectLE`：∀ {α : Type u_1} [inst : Mul α]
 [inst_1 : PartialOrder α] [MulRightReflectLE α], IsRightCancelMul α
· 使用定理 `IsCancelMul.toIsLeftCancelMul`：∀ {G : Type u} {inst : Mul G} [self : IsC
ancelMul G], IsLeftCancelMul G
· 使用定理 `IsOrderedCancelMonoid.toIsCancelMul`：∀ {α : Type u_1} [inst : CommMonoid
 α] [inst_1 : PartialOrder α] [IsOrderedCancelMonoid α], IsCancelMul α
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLT`：∀ {α : Type u_1} [inst : CommM
onoid α] [inst_1 : PartialOrder α] [IsOrderedCancelMonoid α], MulLeftReflectLT α
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `IsOrderedCancelMonoid.toIsOrderedMonoid`：∀ {α : Type u_2} {inst : CommMo
noid α} {inst_1 : Preorder α} [self : IsOrderedCancelMonoid α], IsOrderedMonoid 
α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `mul_left_cancel`：mul_left_cancel : a * b = a * c -> b = c
· 使用定理 `Lex.instIsLeftCancelMul`：∀ {α : Type u_1} [inst : Mul α] [IsLeftCancelMu
l α], IsLeftCancelMul (Lex α)
· 使用定理 `Pi.instIsLeftCancelMul`：∀ {I : Type u} {f : I → Type v₁} [inst : (i : I)
 → Mul (f i)] [∀ (i : I), IsLeftCancelMul (f i)],   IsLeftCancelMul ((i : I) → f
 i)
· 使用定理 `instIsLeftCancelMulOfMulLeftReflectLE`：∀ {α : Type u_1} [inst : Mul α] [
inst_1 : PartialOrder α] [MulLeftReflectLE α], IsLeftCancelMul α
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLE`：∀ {α : Type u_2} [inst : CommM
onoid α] [inst_1 : Preorder α] [IsOrderedCancelMonoid α], MulLeftReflectLE α
· 使用定理 `lt_of_mul_lt_mul_left'`：lt_of_mul_lt_mul_left' [MulLeftReflectLT α] {a b
 c : α} (bc : a * b < a * c) : b < c
-/
instance isOrderedCancelMonoid [∀ i, CommMonoid (α i)] [∀ i, PartialOrder (α i)]
    [∀ i, IsOrderedCancelMonoid (α i)] :
    IsOrderedCancelMonoid (Lex (∀ i, α i)) where
  mul_le_mul_left _ _ hxy z :=
    hxy.elim (fun hxyz => hxyz ▸ le_rfl) fun ⟨i, hi⟩ =>
      Or.inr ⟨i, fun j hji => congr_arg (· * z j) (hi.1 j hji), mul_lt_mul_left hi.2 _⟩
  le_of_mul_le_mul_left _ _ _ hxyz :=
    hxyz.elim (fun h => (mul_left_cancel h).le) fun ⟨i, hi⟩ =>
      Or.inr ⟨i, fun j hj => (mul_left_cancel <| hi.1 j hj), lt_of_mul_lt_mul_left' hi.2⟩

end Pi.Lex

