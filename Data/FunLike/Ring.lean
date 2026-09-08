/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Data.FunLike.Group
public import Mathlib.Algebra.Ring.InjSurj
public import Mathlib.Algebra.Ring.Pi

/-! # Ring instances for `FunLike` types
In this file we define various instances related to ring for `FunLike` types.

Note that currently, these are not registered as instances, but only `abbrev`s to avoid long
typeclass searches.
-/

@[expose] public section

variable {F α : Type*}

section MonoidWithZero

variable [FunLike F α α] [Zero F] [One F] [Mul F] [Zero α]
  [IsZeroApply F α α] [IsOneApplyEqSelf F α] [IsMulApplyEqComp F α]
  [ZeroHomClass F α α]

/-- A `FunLike` type with `(f + g) x = f x + g x` and `(f * g) x = f (g x)` is a `MonoidWithZero`
if `α` is a `MonoidWithZero`. -/
/-
**FunLike.monoidWithZero** 是 Mathlib 中的一个定义，位于命名空间 `FunLike`。
形式化陈述：{F : Type u_1} →   {α : Type u_2} →     [inst : FunLike F α α] →       [in
st_1 : Zero F] →         [inst_2 : One F] →           [inst_3 : Mul F] →        
     [inst_4 : Zero α] →               [IsZeroApply F α α] →                 [Is
OneApplyEqSelf F α] → [IsMulApplyEqComp F α] → [ZeroHomClass F α α] → MonoidWith
Zero F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `FunLike` type with `(f + g) x = f x + g x` and `(f * g) x = f (g x)` is a `Mo
noidWithZero`
if `α` is a `MonoidWithZero`.
-/
protected abbrev FunLike.monoidWithZero : MonoidWithZero F where
  mul_zero f := by apply DFunLike.ext; simp
  zero_mul _ := by apply DFunLike.ext; simp
  mul_one _ := by apply DFunLike.ext; simp
  one_mul _ := by apply DFunLike.ext; simp
  mul_assoc _ _ _ := by apply DFunLike.ext; simp

end MonoidWithZero

section Semiring

variable [FunLike F α α] [Zero F] [One F] [Mul F] [Add F] [AddCommMonoid α]
  [IsZeroApply F α α] [IsAddApply F α α] [IsOneApplyEqSelf F α] [IsMulApplyEqComp F α]
  [SMul ℕ F] [IsSMulApply ℕ F α α] [AddMonoidHomClass F α α] [NatCast F] [IsNatCastApply F α]

/-- A `FunLike` type with `(f + g) x = f x + g x` and `(f * g) x = f (g x)` is a `Semiring` if `α`
is a `Semiring`. -/
/-
**FunLike.semiring** 是 Mathlib 中的一个定义，位于命名空间 `FunLike`。
形式化陈述：{F : Type u_1} →   {α : Type u_2} →     [inst : FunLike F α α] →       [in
st_1 : Zero F] →         [inst_2 : One F] →           [inst_3 : Mul F] →        
     [inst_4 : Add F] →               [inst_5 : AddCommMonoid α] →              
   [IsZeroApply F α α] →                   [IsAddApply F α α] →                 
    [IsOneApplyEqSelf F α] →                       [IsMulApplyEqComp F α] →     
                    [inst_10 : SMul ℕ F] →                           [IsSMulAppl
y ℕ F α α] →                             [AddMonoidHomClass F α α] → [inst_13 : 
NatCast F] → [IsNatCastApply F α] → Semiring F
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommMonoid.add_comm`：∀ {M : Type u} [self : AddCommMonoid M] (a b : M
), a + b = b + a
· 使用定理 `MonoidWithZero.zero_mul`：∀ {M₀ : Type u} [self : MonoidWithZero M₀] (a :
 M₀), 0 * a = 0
· 使用定理 `MonoidWithZero.mul_zero`：∀ {M₀ : Type u} [self : MonoidWithZero M₀] (a :
 M₀), a * 0 = 0

--- 原说明 ---
A `FunLike` type with `(f + g) x = f x + g x` and `(f * g) x = f (g x)` is a `Se
miring` if `α`
is a `Semiring`.
-/
protected abbrev FunLike.semiring : Semiring F where
  __ := FunLike.monoidWithZero
  __ := FunLike.addCommMonoid
  left_distrib f g h := by apply DFunLike.ext; simp
  right_distrib _ _ _ := by apply DFunLike.ext; simp
  natCast_zero := by apply DFunLike.ext; simp
  natCast_succ n := by apply DFunLike.ext; simp [succ_nsmul]

end Semiring

section Ring

variable [FunLike F α α] [Zero F] [One F] [Mul F] [Add F] [Neg F] [Sub F]
  [AddCommGroup α]
  [IsZeroApply F α α] [IsAddApply F α α] [IsOneApplyEqSelf F α] [IsMulApplyEqComp F α]
  [IsNegApply F α α] [IsSubApply F α α]
  [SMul ℕ F] [IsSMulApply ℕ F α α]
  [SMul ℤ F] [IsSMulApply ℤ F α α] [AddMonoidHomClass F α α]
  [NatCast F] [IsNatCastApply F α] [IntCast F] [IsIntCastApply F α]

/-- A `FunLike` type with `(f + g) x = f x + g x` and `(f * g) x = f (g x)` is a `Ring` if `α` is a
`Ring`. -/
/-
**FunLike.ring** 是 Mathlib 中的一个定义，位于命名空间 `FunLike`。
形式化陈述：{F : Type u_1} →   {α : Type u_2} →     [inst : FunLike F α α] →       [in
st_1 : Zero F] →         [inst_2 : One F] →           [inst_3 : Mul F] →        
     [inst_4 : Add F] →               [inst_5 : Neg F] →                 [inst_6
 : Sub F] →                   [inst_7 : AddCommGroup α] →                     [I
sZeroApply F α α] →                       [IsAddApply F α α] →                  
       [IsOneApplyEqSelf F α] →                           [IsMulApplyEqComp F α]
 →                             [IsNegApply F α α] →                             
  [IsSubApply F α α] →                                 [inst_14 : SMul ℕ F] →   
                                [IsSMulApply ℕ F α α] →                         
            [inst_16 : SMul ℤ F] →                                       [IsSMul
Apply ℤ F α α] →                                         [AddMonoidHomClass F α 
α] →                                           [inst_19 : NatCast F] →          
                                   [IsNatCastApply F α] → [inst_21 : IntCast F] 
→ [IsIntCastApply F α] → Ring F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `FunLike` type with `(f + g) x = f x + g x` and `(f * g) x = f (g x)` is a `Ri
ng` if `α` is a
`Ring`.
-/
protected abbrev FunLike.ring : Ring F where
  __ := FunLike.semiring
  __ := FunLike.addCommGroup
  intCast_ofNat _ := by apply DFunLike.ext; simp
  intCast_negSucc n := by apply DFunLike.ext; simp [succ_nsmul]

end Ring

