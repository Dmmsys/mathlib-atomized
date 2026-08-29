/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Logic.Function.Iterate

/-! # Typeclasses for `FunLike` and algebraic operations
In this file we provide typeclasses for the compatibility of algebraic structures and `FunLike`
instances.

These instances encode the property that algebraic operations such as addition, subtraction, and
negation are given by the pointwise operations, and moreover we provide classes for `1` acting as
the identity and multiplication acting as composition.

The algebraic `FunLike` typeclasses provide a `simp` lemma of the form `add_apply` and a `norm_cast`
lemma `coe_add`.

The following `Is*Apply` typeclasses are available:
* `IsZeroApply`, `IsOneApply`: `0 x = 0` and `1 x = 1`, respectively
* `IsOneApplyEqSelf`: `1 x = x`
* `IsAddApply`, `IsMulApply`: `(f + g) x = f x + g x` and `(f * g) x = f x * g x`, respectively
* `IsMulApplyEqComp`: `(f * g) x = f (g x)`
* `IsSubApply`, `IsDivApply`: `(f - g) x = f x - g x` and `(f / g) x = f x / g x`, respectively
* `IsNegApply`, `IsInvApply`: `(-f) x = -(f x)` and `(f⁻¹) x = (f x)⁻¹`, respectively
* `IsVAddApply`, `IsSMulApply` `IsPowApply`: `(n +ᵥ f) x = n +ᵥ f x`, `(n • f) x = n • f x`, and
  `(f ^ n) x = (f x) ^ n`, respectively
* `IsNatCastApply`, `IsIntCastApply`: `(n : F) x = n • x` for `n : ℕ` and `n : ℤ`, respectively

For every type that declares a `FunLike` instance and an `Add` instance, there should be generally
an `IsAddApply` instance with the proof usually being `rfl`.
So for instance for the continuous linear maps equipped with the uniform convergence topology,
we have the instance
```
instance instIsAddApply [TopologicalSpace F] [IsTopologicalAddGroup F] (𝔖 : Set (Set E)) :
    IsAddApply (E →SLᵤ[σ, 𝔖] F) E F where
  add_apply _ _ _ := rfl
```


There are a few lemmas that apply to any function space as long as they have an `IsAddApply`
instance. Then it is now possible to define generic lemmas as follows:

```
section FunLike

variable {F α β : Type*} [CommMonoid β] [CommMonoid F]
  [FunLike F α β] [IsOneApply F α β] [IsMulApply F α β]

open Classical in
@[to_additive (attr := simp)]
theorem prod_apply {ι : Type*} (s : Finset ι) (f : ι → F) (x : α) :
    (∏ i ∈ s, f i) x = ∏ i ∈ s, f i x := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his h => simp [his, h]

end FunLike
```

-/


public section

section Def

section Zero

/--
Definition of `IsZeroApply` / `IsZeroApply` 的定义

English:
class IsZeroApply
  parameters: (F : Type*) (α β : outParam Type*) [FunLike F α β] [Zero β] [Zero F]
  axioms and operations (1):
    - zero_apply((x : α)) : (0 : F) x = 0

中文:
类 是ZeroApply
  参数: (F : 类型) (α β : outParam 类型) [函数状 F α β] [零 β] [零 F]
  公理与运算 (1 个):
    - zero_apply((x : α)) : (0 : F) x = 0
-/
class IsZeroApply (F : Type*) (α β : outParam Type*) [FunLike F α β] [Zero β] [Zero F] where
  zero_apply (x : α) : (0 : F) x = 0

/-- `IsOneApply F α β` states for all `x : α`, `(1 : F) x = 1`. -/
@[to_additive]
/--
Definition of `IsOneApply` / `IsOneApply` 的定义

English:
class IsOneApply
  parameters: (F : Type*) (α β : outParam Type*) [FunLike F α β] [One β] [One F]
  axioms and operations (1):
    - one_apply((x : α)) : (1 : F) x = 1

中文:
类 是OneApply
  参数: (F : 类型) (α β : outParam 类型) [函数状 F α β] [幺 β] [幺 F]
  公理与运算 (1 个):
    - one_apply((x : α)) : (1 : F) x = 1
-/
class IsOneApply (F : Type*) (α β : outParam Type*) [FunLike F α β] [One β] [One F] where
  one_apply (x : α) : (1 : F) x = 1

@[to_additive (attr := simp, grind =)] alias one_apply := IsOneApply.one_apply

/--
Definition of `IsOneApplyEqSelf` / `IsOneApplyEqSelf` 的定义

English:
class IsOneApplyEqSelf
  parameters: (F : Type*) (α : outParam Type*) [FunLike F α α] [One F]
  axioms and operations (1):
    - one_apply_eq_self((x : α)) : (1 : F) x = x

中文:
类 是OneApplyEqSelf
  参数: (F : 类型) (α : outParam 类型) [函数状 F α α] [幺 F]
  公理与运算 (1 个):
    - one_apply_eq_self((x : α)) : (1 : F) x = x
-/
class IsOneApplyEqSelf (F : Type*) (α : outParam Type*) [FunLike F α α] [One F] where
  one_apply_eq_self (x : α) : (1 : F) x = x

@[simp, grind =]
alias one_apply_eq_self := IsOneApplyEqSelf.one_apply_eq_self

end Zero

section Add

/--
Definition of `IsAddApply` / `IsAddApply` 的定义

English:
class IsAddApply
  parameters: (F : Type*) (α β : outParam Type*) [FunLike F α β] [Add β] [Add F]
  axioms and operations (1):
    - add_apply((f g : F) (x : α)) : (f + g) x = f x + g x

中文:
类 是加法Apply
  参数: (F : 类型) (α β : outParam 类型) [函数状 F α β] [加法 β] [加法 F]
  公理与运算 (1 个):
    - add_apply((f g : F) (x : α)) : (f + g) x = f x + g x
-/
class IsAddApply (F : Type*) (α β : outParam Type*) [FunLike F α β] [Add β] [Add F] where
  add_apply (f g : F) (x : α) : (f + g) x = f x + g x

/-- `IsMulApply F α β` states for all `f g : F` and `x : α`, `(f * g) x = f x * g x`. -/
@[to_additive]
/--
Definition of `IsMulApply` / `IsMulApply` 的定义

English:
class IsMulApply
  parameters: (F : Type*) (α β : outParam Type*) [FunLike F α β] [Mul β] [Mul F]
  axioms and operations (1):
    - mul_apply((f g : F) (x : α)) : (f * g) x = f x * g x

中文:
类 是MulApply
  参数: (F : 类型) (α β : outParam 类型) [函数状 F α β] [乘法 β] [乘法 F]
  公理与运算 (1 个):
    - mul_apply((f g : F) (x : α)) : (f * g) x = f x * g x
-/
class IsMulApply (F : Type*) (α β : outParam Type*) [FunLike F α β] [Mul β] [Mul F] where
  mul_apply (f g : F) (x : α) : (f * g) x = f x * g x

@[to_additive (attr := simp, grind =)] alias mul_apply := IsMulApply.mul_apply

/--
Definition of `IsMulApplyEqComp` / `IsMulApplyEqComp` 的定义

English:
class IsMulApplyEqComp
  parameters: (F : Type*) (α : outParam Type*) [FunLike F α α] [Mul F]
  axioms and operations (1):
    - mul_apply_eq_comp((f g : F) (x : α)) : (f * g) x = f (g x)

中文:
类 是MulApplyEqComp
  参数: (F : 类型) (α : outParam 类型) [函数状 F α α] [乘法 F]
  公理与运算 (1 个):
    - mul_apply_eq_comp((f g : F) (x : α)) : (f * g) x = f (g x)
-/
class IsMulApplyEqComp (F : Type*) (α : outParam Type*) [FunLike F α α] [Mul F] where
  mul_apply_eq_comp (f g : F) (x : α) : (f * g) x = f (g x)

@[simp, grind =]
alias mul_apply_eq_comp := IsMulApplyEqComp.mul_apply_eq_comp

@[simp, grind =]
/--
lemma `pow_apply_eq_iterate` / 引理 `pow_apply_eq_iterate`

English:
lemma pow_apply_eq_iterate
  statement: {F α : Type*} [FunLike F α α] [Monoid F] [IsOneApplyEqSelf F α]
  proof: by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ', ih, ← Function.iterate_succ_apply']

中文:
引理 pow_apply_eq_iterate
  结论: {F α : 类型} [函数状 F α α] [幺半群 F] [是OneApplyEqSelf F α]
  证明: by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ', ih, ← Function.iterate_succ_apply']

Depends on / 依赖: Function, Function.iterate_succ_apply, iterate_succ_apply, pow_succ
-/
lemma pow_apply_eq_iterate {F α : Type*} [FunLike F α α] [Monoid F] [IsOneApplyEqSelf F α]
    [IsMulApplyEqComp F α] (f : F) (n : Nat) (x : α) :
    (f ^ n) x = f^[n] x := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ', ih, ← Function.iterate_succ_apply']

end Add

section Sub

/--
Definition of `IsSubApply` / `IsSubApply` 的定义

English:
class IsSubApply
  parameters: (F : Type*) (α β : outParam Type*) [FunLike F α β] [Sub β] [Sub F]
  axioms and operations (1):
    - sub_apply((f g : F) (x : α)) : (f - g) x = f x - g x

中文:
类 是SubApply
  参数: (F : 类型) (α β : outParam 类型) [函数状 F α β] [减法 β] [减法 F]
  公理与运算 (1 个):
    - sub_apply((f g : F) (x : α)) : (f - g) x = f x - g x
-/
class IsSubApply (F : Type*) (α β : outParam Type*) [FunLike F α β] [Sub β] [Sub F] where
  sub_apply (f g : F) (x : α) : (f - g) x = f x - g x

/-- `IsDivApply F α β` states for all `f g : F` and `x : α`, `(f / g) x = f x / g x`. -/
@[to_additive]
/--
Definition of `IsDivApply` / `IsDivApply` 的定义

English:
class IsDivApply
  parameters: (F : Type*) (α β : outParam Type*) [FunLike F α β] [Div β] [Div F]
  axioms and operations (1):
    - div_apply((f g : F) (x : α)) : (f / g) x = f x / g x

中文:
类 是DivApply
  参数: (F : 类型) (α β : outParam 类型) [函数状 F α β] [除法 β] [除法 F]
  公理与运算 (1 个):
    - div_apply((f g : F) (x : α)) : (f / g) x = f x / g x
-/
class IsDivApply (F : Type*) (α β : outParam Type*) [FunLike F α β] [Div β] [Div F] where
  div_apply (f g : F) (x : α) : (f / g) x = f x / g x

@[to_additive (attr := simp, grind =)] alias div_apply := IsDivApply.div_apply

end Sub

section Neg

/--
Definition of `IsNegApply` / `IsNegApply` 的定义

English:
class IsNegApply
  parameters: (F : Type*) (α β : outParam Type*) [FunLike F α β] [Neg β] [Neg F]
  axioms and operations (1):
    - neg_apply((f : F) (x : α)) : (-f) x = -f x

中文:
类 是NegApply
  参数: (F : 类型) (α β : outParam 类型) [函数状 F α β] [取负 β] [取负 F]
  公理与运算 (1 个):
    - neg_apply((f : F) (x : α)) : (-f) x = -f x
-/
class IsNegApply (F : Type*) (α β : outParam Type*) [FunLike F α β] [Neg β] [Neg F] where
  neg_apply (f : F) (x : α) : (-f) x = -f x

/-- `IsInvApply F α β` states for all `f : F` and `x : α`, `f⁻¹ x = (f x)⁻¹`. -/
@[to_additive]
/--
Definition of `IsInvApply` / `IsInvApply` 的定义

English:
class IsInvApply
  parameters: (F : Type*) (α β : outParam Type*) [FunLike F α β] [Inv β] [Inv F]
  axioms and operations (1):
    - inv_apply((f : F) (x : α)) : f⁻¹ x = (f x)⁻¹

中文:
类 是InvApply
  参数: (F : 类型) (α β : outParam 类型) [函数状 F α β] [取逆 β] [取逆 F]
  公理与运算 (1 个):
    - inv_apply((f : F) (x : α)) : f⁻¹ x = (f x)⁻¹
-/
class IsInvApply (F : Type*) (α β : outParam Type*) [FunLike F α β] [Inv β] [Inv F] where
  inv_apply (f : F) (x : α) : f⁻¹ x = (f x)⁻¹

@[to_additive (attr := simp, grind =)] alias inv_apply := IsInvApply.inv_apply

end Neg

section SMul

/--
Definition of `IsVAddApply` / `IsVAddApply` 的定义

English:
class IsVAddApply
  parameters: (M F : Type*) (α β : outParam Type*) [FunLike F α β] [VAdd M β] [VAdd M F]
  axioms and operations (1):
    - vadd_apply((f : F) (n : M) (x : α)) : (n +ᵥ f) x = n +ᵥ f x

中文:
类 是VAddApply
  参数: (M F : 类型) (α β : outParam 类型) [函数状 F α β] [向量加法 M β] [向量加法 M F]
  公理与运算 (1 个):
    - vadd_apply((f : F) (n : M) (x : α)) : (n +ᵥ f) x = n +ᵥ f x
-/
class IsVAddApply (M F : Type*) (α β : outParam Type*) [FunLike F α β] [VAdd M β] [VAdd M F] where
  vadd_apply (f : F) (n : M) (x : α) : (n +ᵥ f) x = n +ᵥ f x

/-- `IsSMulApply M F α β` states for all `f : F`, `n : M` and `x : α`, `(n • f) x = n • f x`. -/
@[to_additive]
/--
Definition of `IsSMulApply` / `IsSMulApply` 的定义

English:
class IsSMulApply
  parameters: (M F : Type*) (α β : outParam Type*) [FunLike F α β] [SMul M β] [SMul M F]
  axioms and operations (1):
    - smul_apply((f : F) (r : M) (x : α)) : (r • f) x = r • f x

中文:
类 是SMulApply
  参数: (M F : 类型) (α β : outParam 类型) [函数状 F α β] [标量乘法 M β] [标量乘法 M F]
  公理与运算 (1 个):
    - smul_apply((f : F) (r : M) (x : α)) : (r • f) x = r • f x
-/
class IsSMulApply (M F : Type*) (α β : outParam Type*) [FunLike F α β] [SMul M β] [SMul M F] where
  smul_apply (f : F) (r : M) (x : α) : (r • f) x = r • f x

@[to_additive (attr := simp, grind =)] alias smul_apply := IsSMulApply.smul_apply

/-- `IsPowApply M F α β` states for all `f : F`, `n : M` and `x : α`, `(f ^ n) x = (f x) ^ n`. -/
@[to_additive IsSMulApply]
/--
Definition of `IsPowApply` / `IsPowApply` 的定义

English:
class IsPowApply
  parameters: (M F : Type*) (α β : outParam Type*) [FunLike F α β] [Pow β M] [Pow F M]
  axioms and operations (1):
    - pow_apply((f : F) (n : M) (x : α)) : (f ^ n) x = (f x) ^ n

中文:
类 是PowApply
  参数: (M F : 类型) (α β : outParam 类型) [函数状 F α β] [幂 β M] [幂 F M]
  公理与运算 (1 个):
    - pow_apply((f : F) (n : M) (x : α)) : (f ^ n) x = (f x) ^ n
-/
class IsPowApply (M F : Type*) (α β : outParam Type*) [FunLike F α β] [Pow β M] [Pow F M] where
  pow_apply (f : F) (n : M) (x : α) : (f ^ n) x = (f x) ^ n

-- Note that `smul_apply` is defined already, so we create an alias using `to_additive`,
-- but we do not declare it a `simp` lemma
@[to_additive existing smul_apply] alias pow_apply := IsPowApply.pow_apply

attribute [simp, grind =] pow_apply

end SMul

section Cast

/--
Definition of `IsNatCastApply` / `IsNatCastApply` 的定义

English:
class IsNatCastApply
  parameters: (F : Type*) (α : outParam Type*) [FunLike F α α] [NatCast F] [SMul Nat α]
  axioms and operations (1):
    - natCast_apply((n : Nat) (x : α)) : (n : F) x = n • x

中文:
类 是自然数CastApply
  参数: (F : 类型) (α : outParam 类型) [函数状 F α α] [自然数嵌入 F] [标量乘法 自然数 α]
  公理与运算 (1 个):
    - natCast_apply((n : 自然数) (x : α)) : (n : F) x = n • x
-/
class IsNatCastApply (F : Type*) (α : outParam Type*) [FunLike F α α] [NatCast F] [SMul Nat α] where
  natCast_apply (n : Nat) (x : α) : (n : F) x = n • x

@[simp, grind =]
alias natCast_apply := IsNatCastApply.natCast_apply

/--
Definition of `IsIntCastApply` / `IsIntCastApply` 的定义

English:
class IsIntCastApply
  parameters: (F : Type*) (α : outParam Type*) [FunLike F α α] [IntCast F] [SMul Int α]
  axioms and operations (1):
    - intCast_apply((n : Int) (x : α)) : (n : F) x = n • x

中文:
类 是整数CastApply
  参数: (F : 类型) (α : outParam 类型) [函数状 F α α] [整数嵌入 F] [标量乘法 整数 α]
  公理与运算 (1 个):
    - intCast_apply((n : 整数) (x : α)) : (n : F) x = n • x
-/
class IsIntCastApply (F : Type*) (α : outParam Type*) [FunLike F α α] [IntCast F] [SMul Int α] where
  intCast_apply (n : Int) (x : α) : (n : F) x = n • x

@[simp, grind =]
alias intCast_apply := IsIntCastApply.intCast_apply

end Cast

end Def

namespace FunLike

variable {M M' F F' α β : Type*} [FunLike F α β] [FunLike F' α α]

section Coercion

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  given: [One F] [One β] [IsOneApply F α β]
  statement: ↑(1 : F) = (1 : α -> β)
  proof: by ext; simp

@[to_additive (attr := simp)]

中文:
定理 coe_one
  条件: [幺 F] [幺 β] [是OneApply F α β]
  结论: ↑(1 : F) = (1 : α -> β)
  证明: by ext; simp

@[to_additive (attr := simp)]
-/
theorem coe_one [One F] [One β] [IsOneApply F α β] : ↑(1 : F) = (1 : α -> β) := by ext; simp

@[to_additive (attr := simp)]
/--
theorem `coe_one_iff` / 定理 `coe_one_iff`

English:
theorem coe_one_iff
  given: [One F] [One β] [IsOneApply F α β] (f : F)
  statement: (f : α -> β) = 1 ↔ f = 1
  proof: by
  constructor
  · intro h
    simp [DFunLike.ext_iff, h]
  · intro h
    simp [h]

@[to_additive (attr := simp, norm_cast)]

中文:
定理 coe_one_iff
  条件: [幺 F] [幺 β] [是OneApply F α β] (f : F)
  结论: (f : α -> β) = 1 ↔ f = 1
  证明: by
  constructor
  · intro h
    simp [DFunLike.ext_iff, h]
  · intro h
    simp [h]

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, ext_iff
-/
theorem coe_one_iff [One F] [One β] [IsOneApply F α β] (f : F) : (f : α -> β) = 1 ↔ f = 1 := by
  constructor
  · intro h
    simp [DFunLike.ext_iff, h]
  · intro h
    simp [h]

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: [Mul F] [Mul β] [IsMulApply F α β] (f g : F)
  statement: ↑(f * g) = (f : α -> β) * g
  proof: by
  ext; simp

@[to_additive (attr := simp, norm_cast)]

中文:
定理 coe_mul
  条件: [乘法 F] [乘法 β] [是MulApply F α β] (f g : F)
  结论: ↑(f * g) = (f : α -> β) * g
  证明: by
  ext; simp

@[to_additive (attr := simp, norm_cast)]
-/
theorem coe_mul [Mul F] [Mul β] [IsMulApply F α β] (f g : F) : ↑(f * g) = (f : α -> β) * g := by
  ext; simp

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_div` / 定理 `coe_div`

English:
theorem coe_div
  given: [Div F] [Div β] [IsDivApply F α β] (f g : F)
  statement: ↑(f / g) = (f : α -> β) / g
  proof: by
  ext; simp

@[to_additive (attr := simp, norm_cast)]

中文:
定理 coe_div
  条件: [除法 F] [除法 β] [是DivApply F α β] (f g : F)
  结论: ↑(f / g) = (f : α -> β) / g
  证明: by
  ext; simp

@[to_additive (attr := simp, norm_cast)]
-/
theorem coe_div [Div F] [Div β] [IsDivApply F α β] (f g : F) : ↑(f / g) = (f : α -> β) / g := by
  ext; simp

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_inv` / 定理 `coe_inv`

English:
theorem coe_inv
  given: [Inv F] [Inv β] [IsInvApply F α β] (f : F)
  statement: ↑(f⁻¹) = (f : α -> β)⁻¹
  proof: by
  ext; simp

@[to_additive (attr := simp, norm_cast)]

中文:
定理 coe_inv
  条件: [取逆 F] [取逆 β] [是InvApply F α β] (f : F)
  结论: ↑(f⁻¹) = (f : α -> β)⁻¹
  证明: by
  ext; simp

@[to_additive (attr := simp, norm_cast)]
-/
theorem coe_inv [Inv F] [Inv β] [IsInvApply F α β] (f : F) : ↑(f⁻¹) = (f : α -> β)⁻¹ := by
  ext; simp

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  given: [SMul M F] [SMul M β] [IsSMulApply M F α β] (n : M) (f : F)
  proof: by
  ext; simp

@[deprecated (since := "2026-07-23")] alias coe_smul' := coe_smul

@[simp, norm_cast, to_additive existing coe_smul]

中文:
定理 coe_smul
  条件: [标量乘法 M F] [标量乘法 M β] [是SMulApply M F α β] (n : M) (f : F)
  证明: by
  ext; simp

@[deprecated (since := "2026-07-23")] alias coe_smul' := coe_smul

@[simp, norm_cast, to_additive existing coe_smul]
-/
theorem coe_smul [SMul M F] [SMul M β] [IsSMulApply M F α β] (n : M) (f : F) :
    ↑(n • f) = n • (f : α -> β) := by
  ext; simp

@[deprecated (since := "2026-07-23")] alias coe_smul' := coe_smul

@[simp, norm_cast, to_additive existing coe_smul]
/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: [Pow F M] [Pow β M] [IsPowApply M F α β] (f : F) (n : M)
  proof: by
  ext; simp

@[simp, norm_cast]

中文:
定理 coe_pow
  条件: [幂 F M] [幂 β M] [是PowApply M F α β] (f : F) (n : M)
  证明: by
  ext; simp

@[simp, norm_cast]
-/
theorem coe_pow [Pow F M] [Pow β M] [IsPowApply M F α β] (f : F) (n : M) :
    ↑(f ^ n) = (f : α -> β) ^ n := by
  ext; simp

@[simp, norm_cast]
/--
theorem `coe_one_eq_id` / 定理 `coe_one_eq_id`

English:
theorem coe_one_eq_id
  given: [One F'] [IsOneApplyEqSelf F' α]
  statement: ↑(1 : F') = id
  proof: by
  ext; simp

@[simp, norm_cast]

中文:
定理 coe_one_eq_id
  条件: [幺 F'] [是OneApplyEqSelf F' α]
  结论: ↑(1 : F') = id
  证明: by
  ext; simp

@[simp, norm_cast]
-/
theorem coe_one_eq_id [One F'] [IsOneApplyEqSelf F' α] : ↑(1 : F') = id := by
  ext; simp

@[simp, norm_cast]
/--
theorem `coe_one_eq_id_iff` / 定理 `coe_one_eq_id_iff`

English:
theorem coe_one_eq_id_iff
  given: [One F'] [IsOneApplyEqSelf F' α] (f : F')
  statement: (f : α -> α) = id ↔ f = 1
  proof: by
  constructor
  · intro h
    simp [DFunLike.ext_iff, h]
  · intro h
    simp [h]

@[simp, norm_cast]

中文:
定理 coe_one_eq_id_iff
  条件: [幺 F'] [是OneApplyEqSelf F' α] (f : F')
  结论: (f : α -> α) = id ↔ f = 1
  证明: by
  constructor
  · intro h
    simp [DFunLike.ext_iff, h]
  · intro h
    simp [h]

@[simp, norm_cast]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, ext_iff
-/
theorem coe_one_eq_id_iff [One F'] [IsOneApplyEqSelf F' α] (f : F') : (f : α -> α) = id ↔ f = 1 := by
  constructor
  · intro h
    simp [DFunLike.ext_iff, h]
  · intro h
    simp [h]

@[simp, norm_cast]
/--
theorem `coe_mul_eq_comp` / 定理 `coe_mul_eq_comp`

English:
theorem coe_mul_eq_comp
  given: [Mul F'] [IsMulApplyEqComp F' α] (f g : F')
  statement: ↑(f * g) = f ∘ g
  proof: by
  ext; simp

@[simp, norm_cast]

中文:
定理 coe_mul_eq_comp
  条件: [乘法 F'] [是MulApplyEqComp F' α] (f g : F')
  结论: ↑(f * g) = f ∘ g
  证明: by
  ext; simp

@[simp, norm_cast]
-/
theorem coe_mul_eq_comp [Mul F'] [IsMulApplyEqComp F' α] (f g : F') : ↑(f * g) = f ∘ g := by
  ext; simp

@[simp, norm_cast]
/--
lemma `coe_pow_eq_iterate` / 引理 `coe_pow_eq_iterate`

English:
lemma coe_pow_eq_iterate
  statement: [Monoid F'] [IsMulApplyEqComp F' α] [IsOneApplyEqSelf F' α]
  proof: funext pow_apply_eq_iterate f n

中文:
引理 coe_pow_eq_iterate
  结论: [幺半群 F'] [是MulApplyEqComp F' α] [是OneApplyEqSelf F' α]
  证明: funext pow_apply_eq_iterate f n

Depends on / 依赖: pow_apply_eq_iterate
-/
lemma coe_pow_eq_iterate [Monoid F'] [IsMulApplyEqComp F' α] [IsOneApplyEqSelf F' α]
    (f : F') (n : Nat) : ⇑(f ^ n) = f^[n] :=
funext pow_apply_eq_iterate f n

-- this lemma cannot be `simp` since this creates loops
@[norm_cast]
/--
theorem `natCast_eq_nsmul_one` / 定理 `natCast_eq_nsmul_one`

English:
theorem natCast_eq_nsmul_one
  statement: [NatCast F'] [One F'] [SMul Nat α] [SMul Nat F']
  proof: by
  apply DFunLike.ext
  simp

@[deprecated (since := "2026-07-24")] alias coe_natCast := natCast_eq_nsmul_one

中文:
定理 natCast_eq_nsmul_one
  结论: [自然数嵌入 F'] [幺 F'] [标量乘法 自然数 α] [标量乘法 自然数 F']
  证明: by
  apply DFunLike.ext
  simp

@[deprecated (since := "2026-07-24")] alias coe_natCast := natCast_eq_nsmul_one

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem natCast_eq_nsmul_one [NatCast F'] [One F'] [SMul Nat α] [SMul Nat F']
    [IsSMulApply Nat F' α α] [IsNatCastApply F' α] [IsOneApplyEqSelf F' α] (n : Nat) :
  (n : F') = n • (1 : F') := by
  apply DFunLike.ext
  simp

@[deprecated (since := "2026-07-24")] alias coe_natCast := natCast_eq_nsmul_one

-- this lemma cannot be `simp` since this creates loops
@[norm_cast]
/--
theorem `intCast_eq_zsmul_one` / 定理 `intCast_eq_zsmul_one`

English:
theorem intCast_eq_zsmul_one
  statement: [IntCast F'] [One F'] [SMul Int α] [SMul Int F']
  proof: by
  apply DFunLike.ext
  simp

@[deprecated (since := "2026-07-24")] alias coe_intCast := intCast_eq_zsmul_one

中文:
定理 intCast_eq_zsmul_one
  结论: [整数嵌入 F'] [幺 F'] [标量乘法 整数 α] [标量乘法 整数 F']
  证明: by
  apply DFunLike.ext
  simp

@[deprecated (since := "2026-07-24")] alias coe_intCast := intCast_eq_zsmul_one

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem intCast_eq_zsmul_one [IntCast F'] [One F'] [SMul Int α] [SMul Int F']
    [IsSMulApply Int F' α α] [IsIntCastApply F' α] [IsOneApplyEqSelf F' α] (n : Int) :
  (n : F') = n • (1 : F') := by
  apply DFunLike.ext
  simp

@[deprecated (since := "2026-07-24")] alias coe_intCast := intCast_eq_zsmul_one

end Coercion

end FunLike
