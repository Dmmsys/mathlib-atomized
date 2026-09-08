/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Polynomial.Module.AEval
public import Mathlib.FieldTheory.Minpoly.Field

/-!
# Polynomial modules in finite dimensions

This file is a place to collect results about the `R[X]`-module structure induced on an `R`-module
by an `R`-linear endomorphism, which require the concept of finite-dimensionality.

## Main results:
* `Module.AEval.isTorsion_of_finiteDimensional`: if a vector space `M` with coefficients in a field
  `K` carries a natural `K`-linear endomorphism which belongs to a finite-dimensional algebra
  over `K`, then the induced `K[X]`-module structure on `M` is pure torsion.

-/

public section

open Polynomial

variable {R K M A : Type*} {a : A}

namespace Module.AEval

/-
**Module.AEval.isTorsion_of_aeval_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Module.AEva
l`。
形式化陈述：isTorsion_of_aeval_eq_zero [CommSemiring R] [NoZeroDivisors R] [Semiring A
] [Algebra R A] [AddCommMonoid M] [Module A M] [Module R M] [IsScalarTower R A M
] {p : R[X]} (h : aeval a p = 0) (h' : p != 0) : IsTorsion R[X] (AEval R M a)
参数：h : aeval a p = 0；h' : p != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_nonZeroDivisors_iff_right`：mem_nonZeroDivisors_iff_right : r in M₀⁰ 
↔ forall x, x * r = 0 -> x = 0
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isTorsion_of_aeval_eq_zero [CommSemiring R] [NoZeroDivisors R] [Semiring A] [Algebra R A]
    [AddCommMonoid M] [Module A M] [Module R M] [IsScalarTower R A M]
    {p : R[X]} (h : aeval a p = 0) (h' : p ≠ 0) :
    IsTorsion R[X] (AEval R M a) := by
  have hp : p ∈ nonZeroDivisors R[X] := mem_nonZeroDivisors_iff_right.mpr
    fun q hq ↦ Or.resolve_right (mul_eq_zero.mp hq) h'
  exact fun x ↦ ⟨⟨p, hp⟩, (of R M a).symm.injective <| by simp [h]⟩

variable (K M a)
/-
**Module.AEval.isTorsion_of_finiteDimensional** 是 Mathlib 中的一个定理，位于命名空间 `Module.
AEval`。
形式化陈述：isTorsion_of_finiteDimensional [Field K] [Ring A] [Algebra K A] [AddCommGr
oup M] [Module A M] [Module K M] [IsScalarTower K A M] [FiniteDimensional K A] :
 IsTorsion K[X] (AEval K M a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.AEval.isTorsion_of_aeval_eq_zero`：isTorsion_of_aeval_eq_zero [Com
mSemiring R] [NoZeroDivisors R] [Semiring A] [Algebra R A] [AddCommMonoid M] [Mo
dule A M] [Module R M] [IsSca…
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `minpoly.ne_zero_of_finite`：ne_zero_of_finite (e : B) [FiniteDimensional 
A B] : minpoly A e != 0
-/
theorem isTorsion_of_finiteDimensional [Field K] [Ring A] [Algebra K A]
    [AddCommGroup M] [Module A M] [Module K M] [IsScalarTower K A M] [FiniteDimensional K A] :
    IsTorsion K[X] (AEval K M a) :=
  isTorsion_of_aeval_eq_zero (minpoly.aeval K a) (minpoly.ne_zero_of_finite K a)

end Module.AEval

