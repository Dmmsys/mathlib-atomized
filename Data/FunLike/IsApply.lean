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

/-- `IsZeroApply F α β` states for all `x : α`, `(0 : F) x = 0`. -/
/-
**IsZeroApply** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_1) → (α : outParam (Type u_2)) → (β : outParam (Type u_3)) → [
FunLike F α β] → [Zero β] → [Zero F] → Prop
参数：Type u_2；Type u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsZeroApply F α β` states for all `x : α`, `(0 : F) x = 0`.
-/
class IsZeroApply (F : Type*) (α β : outParam Type*) [FunLike F α β] [Zero β] [Zero F] where
  zero_apply (x : α) : (0 : F) x = 0

/-- `IsOneApply F α β` states for all `x : α`, `(1 : F) x = 1`. -/
@[to_additive]
/-
**IsOneApply** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_1) → (α : outParam (Type u_2)) → (β : outParam (Type u_3)) → [
FunLike F α β] → [One β] → [One F] → Prop
参数：Type u_2；Type u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsOneApply F α β` states for all `x : α`, `(1 : F) x = 1`.
-/
class IsOneApply (F : Type*) (α β : outParam Type*) [FunLike F α β] [One β] [One F] where
  one_apply (x : α) : (1 : F) x = 1

@[to_additive (attr := simp, grind =)] alias one_apply := IsOneApply.one_apply

/-- `IsOneApplyEqSelf F α α` states for all `x : α`, `(1 : F) x = x`. -/
/-
**IsOneApplyEqSelf** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_1) → (α : outParam (Type u_2)) → [FunLike F α α] → [One F] → P
rop
参数：Type u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsOneApplyEqSelf F α α` states for all `x : α`, `(1 : F) x = x`.
-/
class IsOneApplyEqSelf (F : Type*) (α : outParam Type*) [FunLike F α α] [One F] where
  one_apply_eq_self (x : α) : (1 : F) x = x

@[simp, grind =]
alias one_apply_eq_self := IsOneApplyEqSelf.one_apply_eq_self

end Zero

section Add

/-- `IsAddApply F α β` states for all `f g : F` and `x : α`, `(f + g) x = f x + g x`. -/
/-
**IsAddApply** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_1) → (α : outParam (Type u_2)) → (β : outParam (Type u_3)) → [
FunLike F α β] → [Add β] → [Add F] → Prop
参数：Type u_2；Type u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsAddApply F α β` states for all `f g : F` and `x : α`, `(f + g) x = f x + g x`
.
-/
class IsAddApply (F : Type*) (α β : outParam Type*) [FunLike F α β] [Add β] [Add F] where
  add_apply (f g : F) (x : α) : (f + g) x = f x + g x

/-- `IsMulApply F α β` states for all `f g : F` and `x : α`, `(f * g) x = f x * g x`. -/
@[to_additive]
/-
**IsMulApply** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_1) → (α : outParam (Type u_2)) → (β : outParam (Type u_3)) → [
FunLike F α β] → [Mul β] → [Mul F] → Prop
参数：Type u_2；Type u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsMulApply F α β` states for all `f g : F` and `x : α`, `(f * g) x = f x * g x`
.
-/
class IsMulApply (F : Type*) (α β : outParam Type*) [FunLike F α β] [Mul β] [Mul F] where
  mul_apply (f g : F) (x : α) : (f * g) x = f x * g x

@[to_additive (attr := simp, grind =)] alias mul_apply := IsMulApply.mul_apply

/-- `IsMulApplyEqComp F α α` states for all `x : α`, `(f * g) x = f (g x)`. -/
/-
**IsMulApplyEqComp** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_1) → (α : outParam (Type u_2)) → [FunLike F α α] → [Mul F] → P
rop
参数：Type u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsMulApplyEqComp F α α` states for all `x : α`, `(f * g) x = f (g x)`.
-/
class IsMulApplyEqComp (F : Type*) (α : outParam Type*) [FunLike F α α] [Mul F] where
  mul_apply_eq_comp (f g : F) (x : α) : (f * g) x = f (g x)

@[simp, grind =]
alias mul_apply_eq_comp := IsMulApplyEqComp.mul_apply_eq_comp

@[simp, grind =]
/-
**pow_apply_eq_iterate** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_apply_eq_iterate {F α : Type*} [FunLike F α α] [Monoid F] [IsOneApplyE
qSelf F α] [IsMulApplyEqComp F α] (f : F) (n : Nat) (x : α) : (f ^ n) x = f^[n] 
x
参数：f : F；n : Nat；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_apply_eq_self`：∀ {F : Type u_1} {α : outParam (Type u_2)} {inst : Fu
nLike F α α} {inst_1 : One F} [self : IsOneApplyEqSelf F α]   (x : α), 1 x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `mul_apply_eq_comp`：∀ {F : Type u_1} {α : outParam (Type u_2)} {inst : Fu
nLike F α α} {inst_1 : Mul F} [self : IsMulApplyEqComp F α]   (f g : F) (x : α),
 (f * g…
-/
lemma pow_apply_eq_iterate {F α : Type*} [FunLike F α α] [Monoid F] [IsOneApplyEqSelf F α]
    [IsMulApplyEqComp F α] (f : F) (n : ℕ) (x : α) :
    (f ^ n) x = f^[n] x := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ', ih, ← Function.iterate_succ_apply']

end Add

section Sub

/-- `IsSubApply F α β` states for all `f g : F` and `x : α`, `(f - g) x = f x - g x`. -/
/-
**IsSubApply** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_1) → (α : outParam (Type u_2)) → (β : outParam (Type u_3)) → [
FunLike F α β] → [Sub β] → [Sub F] → Prop
参数：Type u_2；Type u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsSubApply F α β` states for all `f g : F` and `x : α`, `(f - g) x = f x - g x`
.
-/
class IsSubApply (F : Type*) (α β : outParam Type*) [FunLike F α β] [Sub β] [Sub F] where
  sub_apply (f g : F) (x : α) : (f - g) x = f x - g x

/-- `IsDivApply F α β` states for all `f g : F` and `x : α`, `(f / g) x = f x / g x`. -/
@[to_additive]
/-
**IsDivApply** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_1) → (α : outParam (Type u_2)) → (β : outParam (Type u_3)) → [
FunLike F α β] → [Div β] → [Div F] → Prop
参数：Type u_2；Type u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsDivApply F α β` states for all `f g : F` and `x : α`, `(f / g) x = f x / g x`
.
-/
class IsDivApply (F : Type*) (α β : outParam Type*) [FunLike F α β] [Div β] [Div F] where
  div_apply (f g : F) (x : α) : (f / g) x = f x / g x

@[to_additive (attr := simp, grind =)] alias div_apply := IsDivApply.div_apply

end Sub

section Neg

/-- `IsNegApply F α β` states for all `f : F` and `x : α`, `(-f) x = -f x`. -/
/-
**IsNegApply** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_1) → (α : outParam (Type u_2)) → (β : outParam (Type u_3)) → [
FunLike F α β] → [Neg β] → [Neg F] → Prop
参数：Type u_2；Type u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsNegApply F α β` states for all `f : F` and `x : α`, `(-f) x = -f x`.
-/
class IsNegApply (F : Type*) (α β : outParam Type*) [FunLike F α β] [Neg β] [Neg F] where
  neg_apply (f : F) (x : α) : (-f) x = -f x

/-- `IsInvApply F α β` states for all `f : F` and `x : α`, `f⁻¹ x = (f x)⁻¹`. -/
@[to_additive]
/-
**IsInvApply** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_1) → (α : outParam (Type u_2)) → (β : outParam (Type u_3)) → [
FunLike F α β] → [Inv β] → [Inv F] → Prop
参数：Type u_2；Type u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsInvApply F α β` states for all `f : F` and `x : α`, `f⁻¹ x = (f x)⁻¹`.
-/
class IsInvApply (F : Type*) (α β : outParam Type*) [FunLike F α β] [Inv β] [Inv F] where
  inv_apply (f : F) (x : α) : f⁻¹ x = (f x)⁻¹

@[to_additive (attr := simp, grind =)] alias inv_apply := IsInvApply.inv_apply

end Neg

section SMul

/-- `IsVAddApply M F α β` states for all `f : F`, `n : M` and `x : α`, `(n +ᵥ f) x = n +ᵥ f x`. -/
/-
**IsVAddApply** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_1) →   (F : Type u_2) →     (α : outParam (Type u_3)) → (β : o
utParam (Type u_4)) → [FunLike F α β] → [VAdd M β] → [VAdd M F] → Prop
参数：Type u_3；Type u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsVAddApply M F α β` states for all `f : F`, `n : M` and `x : α`, `(n +ᵥ f) x =
 n +ᵥ f x`.
-/
class IsVAddApply (M F : Type*) (α β : outParam Type*) [FunLike F α β] [VAdd M β] [VAdd M F] where
  vadd_apply (f : F) (n : M) (x : α) : (n +ᵥ f) x = n +ᵥ f x

/-- `IsSMulApply M F α β` states for all `f : F`, `n : M` and `x : α`, `(n • f) x = n • f x`. -/
@[to_additive]
/-
**IsSMulApply** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_1) →   (F : Type u_2) →     (α : outParam (Type u_3)) → (β : o
utParam (Type u_4)) → [FunLike F α β] → [SMul M β] → [SMul M F] → Prop
参数：Type u_3；Type u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsSMulApply M F α β` states for all `f : F`, `n : M` and `x : α`, `(n • f) x = 
n • f x`.
-/
class IsSMulApply (M F : Type*) (α β : outParam Type*) [FunLike F α β] [SMul M β] [SMul M F] where
  smul_apply (f : F) (r : M) (x : α) : (r • f) x = r • f x

@[to_additive (attr := simp, grind =)] alias smul_apply := IsSMulApply.smul_apply

/-- `IsPowApply M F α β` states for all `f : F`, `n : M` and `x : α`, `(f ^ n) x = (f x) ^ n`. -/
@[to_additive IsSMulApply]
/-
**IsPowApply** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_1) →   (F : Type u_2) →     (α : outParam (Type u_3)) → (β : o
utParam (Type u_4)) → [FunLike F α β] → [Pow β M] → [Pow F M] → Prop
参数：Type u_3；Type u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsPowApply M F α β` states for all `f : F`, `n : M` and `x : α`, `(f ^ n) x = (
f x) ^ n`.
-/
class IsPowApply (M F : Type*) (α β : outParam Type*) [FunLike F α β] [Pow β M] [Pow F M] where
  pow_apply (f : F) (n : M) (x : α) : (f ^ n) x = (f x) ^ n

-- Note that `smul_apply` is defined already, so we create an alias using `to_additive`,
-- but we do not declare it a `simp` lemma
@[to_additive existing smul_apply] alias pow_apply := IsPowApply.pow_apply

attribute [simp, grind =] pow_apply

end SMul

section Cast

/-- `IsNatCastApply F α` states for all `n : ℕ` and `x : α`, `(n : F) x = n • x`. -/
/-
**IsNatCastApply** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_1) → (α : outParam (Type u_2)) → [FunLike F α α] → [NatCast F]
 → [SMul ℕ α] → Prop
参数：Type u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsNatCastApply F α` states for all `n : ℕ` and `x : α`, `(n : F) x = n • x`.
-/
class IsNatCastApply (F : Type*) (α : outParam Type*) [FunLike F α α] [NatCast F] [SMul Nat α] where
  natCast_apply (n : Nat) (x : α) : (n : F) x = n • x

@[simp, grind =]
alias natCast_apply := IsNatCastApply.natCast_apply

/-- `IsIntCastApply F α` states for all `n : ℤ` and `x : α`, `(n : F) x = n • x`. -/
/-
**IsIntCastApply** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_1) → (α : outParam (Type u_2)) → [FunLike F α α] → [IntCast F]
 → [SMul ℤ α] → Prop
参数：Type u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsIntCastApply F α` states for all `n : ℤ` and `x : α`, `(n : F) x = n • x`.
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
/-
**FunLike.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `FunLike`。
形式化陈述：coe_one [One F] [One β] [IsOneApply F α β] : ↑(1 : F) = (1 : α -> β)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : One β}   {inst_2 : One F} [self : IsOn…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_one [One F] [One β] [IsOneApply F α β] : ↑(1 : F) = (1 : α → β) := by ext; simp

@[to_additive (attr := simp)]
/-
**FunLike.coe_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `FunLike`。
形式化陈述：coe_one_iff [One F] [One β] [IsOneApply F α β] (f : F) : (f : α -> β) = 1 
↔ f = 1
参数：f : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `one_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : One β}   {inst_2 : One F} [self : IsOn…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FunLike.coe_one`：coe_one [One F] [One β] [IsOneApply F α β] : ↑(1 : F) =
 (1 : α -> β)
-/
theorem coe_one_iff [One F] [One β] [IsOneApply F α β] (f : F) : (f : α → β) = 1 ↔ f = 1 := by
  constructor
  · intro h
    simp [DFunLike.ext_iff, h]
  · intro h
    simp [h]

@[to_additive (attr := simp, norm_cast)]
/-
**FunLike.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `FunLike`。
形式化陈述：coe_mul [Mul F] [Mul β] [IsMulApply F α β] (f g : F) : ↑(f * g) = (f : α -
> β) * g
参数：f g : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Mul β}   {inst_2 : Mul F} [self : IsMu…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_mul [Mul F] [Mul β] [IsMulApply F α β] (f g : F) : ↑(f * g) = (f : α → β) * g := by
  ext; simp

@[to_additive (attr := simp, norm_cast)]
/-
**FunLike.coe_div** 是 Mathlib 中的一个定理，位于命名空间 `FunLike`。
形式化陈述：coe_div [Div F] [Div β] [IsDivApply F α β] (f g : F) : ↑(f / g) = (f : α -
> β) / g
参数：f g : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Div β}   {inst_2 : Div F} [self : IsDi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_div [Div F] [Div β] [IsDivApply F α β] (f g : F) : ↑(f / g) = (f : α → β) / g := by
  ext; simp

@[to_additive (attr := simp, norm_cast)]
/-
**FunLike.coe_inv** 是 Mathlib 中的一个定理，位于命名空间 `FunLike`。
形式化陈述：coe_inv [Inv F] [Inv β] [IsInvApply F α β] (f : F) : ↑(f⁻¹) = (f : α -> β)
⁻¹
参数：f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Inv β}   {inst_2 : Inv F} [self : IsIn…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_inv [Inv F] [Inv β] [IsInvApply F α β] (f : F) : ↑(f⁻¹) = (f : α → β)⁻¹ := by
  ext; simp

@[to_additive (attr := simp, norm_cast)]
/-
**FunLike.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `FunLike`。
形式化陈述：coe_smul [SMul M F] [SMul M β] [IsSMulApply M F α β] (n : M) (f : F) : ↑(n
 • f) = n • (f : α -> β)
参数：n : M；f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_smul [SMul M F] [SMul M β] [IsSMulApply M F α β] (n : M) (f : F) :
    ↑(n • f) = n • (f : α → β) := by
  ext; simp

@[deprecated (since := "2026-07-23")] alias coe_smul' := coe_smul

@[simp, norm_cast, to_additive existing coe_smul]
/-
**FunLike.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `FunLike`。
形式化陈述：coe_pow [Pow F M] [Pow β M] [IsPowApply M F α β] (f : F) (n : M) : ↑(f ^ n
) = (f : α -> β) ^ n
参数：f : F；n : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β 
: outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : Pow β M} {inst_2 : Po…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_pow [Pow F M] [Pow β M] [IsPowApply M F α β] (f : F) (n : M) :
    ↑(f ^ n) = (f : α → β) ^ n := by
  ext; simp

@[simp, norm_cast]
/-
**FunLike.coe_one_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `FunLike`。
形式化陈述：coe_one_eq_id [One F'] [IsOneApplyEqSelf F' α] : ↑(1 : F') = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_apply_eq_self`：∀ {F : Type u_1} {α : outParam (Type u_2)} {inst : Fu
nLike F α α} {inst_1 : One F} [self : IsOneApplyEqSelf F α]   (x : α), 1 x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_one_eq_id [One F'] [IsOneApplyEqSelf F' α] : ↑(1 : F') = id := by
  ext; simp

@[simp, norm_cast]
/-
**FunLike.coe_one_eq_id_iff** 是 Mathlib 中的一个定理，位于命名空间 `FunLike`。
形式化陈述：coe_one_eq_id_iff [One F'] [IsOneApplyEqSelf F' α] (f : F') : (f : α -> α)
 = id ↔ f = 1
参数：f : F'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `one_apply_eq_self`：∀ {F : Type u_1} {α : outParam (Type u_2)} {inst : Fu
nLike F α α} {inst_1 : One F} [self : IsOneApplyEqSelf F α]   (x : α), 1 x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FunLike.coe_one_eq_id`：coe_one_eq_id [One F'] [IsOneApplyEqSelf F' α] : 
↑(1 : F') = id
-/
theorem coe_one_eq_id_iff [One F'] [IsOneApplyEqSelf F' α] (f : F') : (f : α → α) = id ↔ f = 1 := by
  constructor
  · intro h
    simp [DFunLike.ext_iff, h]
  · intro h
    simp [h]

@[simp, norm_cast]
/-
**FunLike.coe_mul_eq_comp** 是 Mathlib 中的一个定理，位于命名空间 `FunLike`。
形式化陈述：coe_mul_eq_comp [Mul F'] [IsMulApplyEqComp F' α] (f g : F') : ↑(f * g) = f
 ∘ g
参数：f g : F'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_apply_eq_comp`：∀ {F : Type u_1} {α : outParam (Type u_2)} {inst : Fu
nLike F α α} {inst_1 : Mul F} [self : IsMulApplyEqComp F α]   (f g : F) (x : α),
 (f * g…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_mul_eq_comp [Mul F'] [IsMulApplyEqComp F' α] (f g : F') : ↑(f * g) = f ∘ g := by
  ext; simp

@[simp, norm_cast]
/-
**FunLike.coe_pow_eq_iterate** 是 Mathlib 中的一个引理，位于命名空间 `FunLike`。
形式化陈述：coe_pow_eq_iterate [Monoid F'] [IsMulApplyEqComp F' α] [IsOneApplyEqSelf F
' α] (f : F') (n : Nat) : ⇑(f ^ n) = f^[n]
参数：f : F'；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `pow_apply_eq_iterate`：pow_apply_eq_iterate {F α : Type*} [FunLike F α α]
 [Monoid F] [IsOneApplyEqSelf F α] [IsMulApplyEqComp F α] (f : F) (n : Nat) (x :
 α) : (f ^…
-/
lemma coe_pow_eq_iterate [Monoid F'] [IsMulApplyEqComp F' α] [IsOneApplyEqSelf F' α]
    (f : F') (n : ℕ) : ⇑(f ^ n) = f^[n] :=
  funext <| pow_apply_eq_iterate f n

-- this lemma cannot be `simp` since this creates loops
@[norm_cast]
/-
**FunLike.natCast_eq_nsmul_one** 是 Mathlib 中的一个定理，位于命名空间 `FunLike`。
形式化陈述：natCast_eq_nsmul_one [NatCast F'] [One F'] [SMul Nat α] [SMul Nat F'] [IsS
MulApply Nat F' α α] [IsNatCastApply F' α] [IsOneApplyEqSelf F' α] (n : Nat) : (
n : F') = n • (1 : F')
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `natCast_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {inst : FunLik
e F α α} {inst_1 : NatCast F} {inst_2 : SMul ℕ α}   [self : IsNatCastApply F α] 
(n …
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `one_apply_eq_self`：∀ {F : Type u_1} {α : outParam (Type u_2)} {inst : Fu
nLike F α α} {inst_1 : One F} [self : IsOneApplyEqSelf F α]   (x : α), 1 x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem natCast_eq_nsmul_one [NatCast F'] [One F'] [SMul Nat α] [SMul Nat F']
    [IsSMulApply Nat F' α α] [IsNatCastApply F' α] [IsOneApplyEqSelf F' α] (n : ℕ) :
  (n : F') = n • (1 : F') := by
  apply DFunLike.ext
  simp

@[deprecated (since := "2026-07-24")] alias coe_natCast := natCast_eq_nsmul_one

-- this lemma cannot be `simp` since this creates loops
@[norm_cast]
/-
**FunLike.intCast_eq_zsmul_one** 是 Mathlib 中的一个定理，位于命名空间 `FunLike`。
形式化陈述：intCast_eq_zsmul_one [IntCast F'] [One F'] [SMul Int α] [SMul Int F'] [IsS
MulApply Int F' α α] [IsIntCastApply F' α] [IsOneApplyEqSelf F' α] (n : Int) : (
n : F') = n • (1 : F')
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intCast_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {inst : FunLik
e F α α} {inst_1 : IntCast F} {inst_2 : SMul ℤ α}   [self : IsIntCastApply F α] 
(n …
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `one_apply_eq_self`：∀ {F : Type u_1} {α : outParam (Type u_2)} {inst : Fu
nLike F α α} {inst_1 : One F} [self : IsOneApplyEqSelf F α]   (x : α), 1 x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem intCast_eq_zsmul_one [IntCast F'] [One F'] [SMul Int α] [SMul Int F']
    [IsSMulApply Int F' α α] [IsIntCastApply F' α] [IsOneApplyEqSelf F' α] (n : ℤ) :
  (n : F') = n • (1 : F') := by
  apply DFunLike.ext
  simp

@[deprecated (since := "2026-07-24")] alias coe_intCast := intCast_eq_zsmul_one

end Coercion

end FunLike

