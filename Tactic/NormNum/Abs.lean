/-
Copyright (c) 2025 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/
module

public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Tactic.NormNum.Basic


/-!
# `norm_num` plugin for `abs`

TODO: plugins for `mabs`, `norm`, `nnorm`, and `enorm`.
-/

public meta section

namespace Mathlib.Meta.NormNum

open Lean.Meta Qq

/-
**Mathlib.Meta.NormNum.isNat_abs_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.
NormNum`。
形式化陈述：isNat_abs_nonneg {α : Type*} [Ring α] [Lattice α] [IsOrderedRing α] {a : α
} {na : Nat} (pa : IsNat a na) : IsNat |a| na
参数：pa : IsNat a na。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsNat.out`：∀ {α : Type u} [inst : AddMonoidWithOne 
α] {a : α} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = ↑n
· 使用定理 `Nat.abs_cast`：abs_cast (n : Nat) : |(n : R)| = n
-/
theorem isNat_abs_nonneg {α : Type*} [Ring α] [Lattice α] [IsOrderedRing α]
    {a : α} {na : ℕ} (pa : IsNat a na) : IsNat |a| na := by
  rw [pa.out, Nat.abs_cast]
  constructor
  rfl
/-
**Mathlib.Meta.NormNum.isNat_abs_neg** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.Nor
mNum`。
形式化陈述：isNat_abs_neg {α : Type*} [Ring α] [Lattice α] [IsOrderedRing α] {a : α} {
na : Nat} (pa : IsInt a (.negOfNat na)) : IsNat |a| na
参数：pa : IsInt a (.negOfNat na)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.out`：∀ {α : Type u} [inst : Ring α] {a : α} {
n : ℤ}, Mathlib.Meta.NormNum.IsInt a n → a = ↑n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_negOfNat`：cast_negOfNat (n : Nat) : ((negOfNat n : Int) : R) = 
-n
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
· 使用定理 `Nat.abs_cast`：abs_cast (n : Nat) : |(n : R)| = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isNat_abs_neg {α : Type*} [Ring α] [Lattice α] [IsOrderedRing α]
    {a : α} {na : ℕ} (pa : IsInt a (.negOfNat na)) : IsNat |a| na := by
  rw [pa.out]
  constructor
  simp
/-
**Mathlib.Meta.NormNum.isNNRat_abs_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Met
a.NormNum`。
形式化陈述：isNNRat_abs_nonneg {α : Type*} [DivisionRing α] [LinearOrder α] [IsStrictO
rderedRing α] {a : α} {num den : Nat} (ra : IsNNRat a num den) : IsNNRat |a| num
 den
参数：ra : IsNNRat a num den。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isNNRat_abs_nonneg {α : Type*} [DivisionRing α] [LinearOrder α]
    [IsStrictOrderedRing α] {a : α} {num den : ℕ} (ra : IsNNRat a num den) :
    IsNNRat |a| num den := by
  obtain ⟨ha1, rfl⟩ := ra
  refine ⟨ha1, abs_of_nonneg ?_⟩
  apply mul_nonneg
  · exact Nat.cast_nonneg' num
  · simp only [invOf_eq_inv, inv_nonneg, Nat.cast_nonneg]
/-
**Mathlib.Meta.NormNum.isNNRat_abs_neg** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Meta.N
ormNum`。
形式化陈述：isNNRat_abs_neg {α : Type*} [DivisionRing α] [LinearOrder α] [IsStrictOrde
redRing α] {a : α} {num den : Nat} (ra : IsRat a (.negOfNat num) den) : IsNNRat 
|a| num den
参数：ra : IsRat a (.negOfNat num) den。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Int.cast_negOfNat`：cast_negOfNat (n : Nat) : ((negOfNat n : Int) : R) = 
-n
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isNNRat_abs_neg {α : Type*} [DivisionRing α] [LinearOrder α] [IsStrictOrderedRing α]
    {a : α} {num den : ℕ} (ra : IsRat a (.negOfNat num) den) : IsNNRat |a| num den := by
  obtain ⟨ha1, rfl⟩ := ra
  simp only [Int.cast_negOfNat, neg_mul, abs_neg]
  refine ⟨ha1, abs_of_nonneg ?_⟩
  apply mul_nonneg
  · exact Nat.cast_nonneg' num
  · simp only [invOf_eq_inv, inv_nonneg, Nat.cast_nonneg]

/-- The `norm_num` extension which identifies expressions of the form `|a|`,
such that `norm_num` successfully recognises `a`. -/
/-
**Mathlib.Meta.NormNum.evalAbs** 是 Mathlib 中的一个定义，位于命名空间 `Mathlib.Meta.NormNum`。
形式化陈述：Mathlib.Meta.NormNum.NormNumExt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `norm_num` extension which identifies expressions of the form `|a|`,
such that `norm_num` successfully recognises `a`.
-/
@[norm_num |_|] def evalAbs : NormNumExt where eval {u α}
  | ~q(@abs _ $instLattice $instAddGroup $a) => do
    match ← derive a with
    | .isBool ..  => failure
    | .isNat sα na pa =>
      let rα : Q(Ring $α) ← synthInstanceQ q(Ring $α)
      let iorα : Q(IsOrderedRing $α) ← synthInstanceQ q(IsOrderedRing $α)
      assumeInstancesCommute
      return .isNat sα na q(isNat_abs_nonneg $pa)
    | .isNegNat sα na pa =>
      let rα : Q(Ring $α) ← synthInstanceQ q(Ring $α)
      let iorα : Q(IsOrderedRing $α) ← synthInstanceQ q(IsOrderedRing $α)
      assumeInstancesCommute
      return .isNat _ _ q(isNat_abs_neg $pa)
    | .isNNRat dsα' qe' nume' dene' pe' =>
      let rα : Q(DivisionRing $α) ← synthInstanceQ q(DivisionRing $α)
      let loα : Q(LinearOrder $α) ← synthInstanceQ q(LinearOrder $α)
      let isorα : Q(IsStrictOrderedRing $α) ← synthInstanceQ q(IsStrictOrderedRing $α)
      assumeInstancesCommute
      return .isNNRat _ qe' _ _ q(isNNRat_abs_nonneg $pe')
    | .isNegNNRat dα' qe' nume' dene' pe' =>
      let loα : Q(LinearOrder $α) ← synthInstanceQ q(LinearOrder $α)
      let isorα : Q(IsStrictOrderedRing $α) ← synthInstanceQ q(IsStrictOrderedRing $α)
      assumeInstancesCommute
      return .isNNRat _ (-qe') _ _ q(isNNRat_abs_neg $pe')

end Mathlib.Meta.NormNum

