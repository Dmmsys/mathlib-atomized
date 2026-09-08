/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Data.FunLike.IsApply
public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Pi.Basic

/-! # Group instances for `FunLike` types
In this file we define various instances related to groups for `FunLike` types.

For example given a `FunLike F α β` with `IsMulApply F α β` and `Semigroup β`, then `F` is naturally
a semigroup. Note that currently, these are not registered as instances, but only `abbrev`s to
avoid long typeclass searches.

Moreover, we define the homomorphism `FunLike.coeMulHom : F →* α → β` that acts by coercion. This
definition is mainly needed to define a module instance on `F`.

-/

@[expose] public section

namespace FunLike

variable {F α β : Type*} [FunLike F α β]

section CoercionHom

section MulHom

variable [Mul F] [Mul β] [IsMulApply F α β]

variable (F α β) in
/-- Coercion as a multiplicative homomorphism. -/
@[to_additive
/-- Coercion as an additive homomorphism. -/]
/-
**FunLike.coeMulHom** 是 Mathlib 中的一个定义，位于命名空间 `FunLike`。
形式化陈述：coeMulHom : F ->ₙ* α -> β where toFun f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `FunLike.coe_mul`：coe_mul [Mul F] [Mul β] [IsMulApply F α β] (f g : F) : 
↑(f * g) = (f : α -> β) * g
-/
def coeMulHom : F →ₙ* α → β where
  toFun f := f
  map_mul' := coe_mul

@[to_additive (attr := simp)]
/-
**FunLike.coeMulHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `FunLike`。
形式化陈述：coeMulHom_apply (f : F) : coeMulHom F α β f = f
参数：f : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeMulHom_apply (f : F) : coeMulHom F α β f = f := rfl

@[to_additive (attr := norm_cast)]
/-
**FunLike.coe_coeMulHom** 是 Mathlib 中的一个定理，位于命名空间 `FunLike`。
形式化陈述：coe_coeMulHom : (coeMulHom F α β : F -> α -> β) = DFunLike.coe
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_coeMulHom : (coeMulHom F α β : F → α → β) = DFunLike.coe := rfl

@[to_additive]
/-
**FunLike.coeMulHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `FunLike`。
形式化陈述：coeMulHom_injective : Function.Injective (coeMulHom F α β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FunLike.coe_coeMulHom`：coe_coeMulHom : (coeMulHom F α β : F -> α -> β) =
 DFunLike.coe
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem coeMulHom_injective : Function.Injective (coeMulHom F α β) := by
  rw [coe_coeMulHom]
  exact DFunLike.coe_injective

end MulHom

section MonoidHom

variable [MulOne F] [MulOneClass β] [IsOneApply F α β] [IsMulApply F α β]

variable (F α β) in
/-- Coercion as a monoid homomorphism. -/
@[to_additive
/-- Coercion as an additive monoid homomorphism. -/]
/-
**FunLike.coeMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `FunLike`。
形式化陈述：coeMonoidHom : F ->* α -> β where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def coeMonoidHom : F →* α → β where
  toFun f := f
  map_one' := coe_one
  map_mul' := coe_mul

@[to_additive (attr := simp)]
/-
**FunLike.coeMonoidHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `FunLike`。
形式化陈述：coeMonoidHom_apply (f : F) : coeMonoidHom F α β f = f
参数：f : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeMonoidHom_apply (f : F) : coeMonoidHom F α β f = f := rfl

@[to_additive (attr := norm_cast)]
/-
**FunLike.coe_coeMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `FunLike`。
形式化陈述：coe_coeMonoidHom : (coeMonoidHom F α β : F -> α -> β) = DFunLike.coe
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_coeMonoidHom : (coeMonoidHom F α β : F → α → β) = DFunLike.coe := rfl

@[to_additive (attr := norm_cast)]
/-
**FunLike.coe_coeMonoidHom'** 是 Mathlib 中的一个定理，位于命名空间 `FunLike`。
形式化陈述：coe_coeMonoidHom' : (coeMonoidHom F α β : F ->ₙ* α -> β) = coeMulHom F α β
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
theorem coe_coeMonoidHom' : (coeMonoidHom F α β : F →ₙ* α → β) = coeMulHom F α β := rfl

@[to_additive]
/-
**FunLike.coeMonoidHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `FunLike`。
形式化陈述：coeMonoidHom_injective : Function.Injective (coeMonoidHom F α β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FunLike.coe_coeMonoidHom`：coe_coeMonoidHom : (coeMonoidHom F α β : F -> 
α -> β) = DFunLike.coe
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem coeMonoidHom_injective : Function.Injective (coeMonoidHom F α β) := by
  rw [coe_coeMonoidHom]
  exact DFunLike.coe_injective

end MonoidHom

end CoercionHom

section GroupInstances

variable [Mul F]

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x` is a semigroup if `β` is a semigroup. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x` is an additive semigroup
if `β` is an additive semigroup. -/]
/-
**FunLike.semigroup** 是 Mathlib 中的一个定义，位于命名空间 `FunLike`。
形式化陈述：{F : Type u_1} →   {α : Type u_2} →     {β : Type u_3} →       [inst : Fun
Like F α β] → [inst_1 : Mul F] → [inst_2 : Semigroup β] → [IsMulApply F α β] → S
emigroup F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected abbrev semigroup [Semigroup β] [IsMulApply F α β] : Semigroup F :=
  DFunLike.coe_injective.semigroup (fun (f : F) ↦ (f : α → β)) coe_mul

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x` is a commutative semigroup if `β` is a
commutative semigroup. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x` is a commatative additive
semigroup if `β` is a commatative additive semigroup. -/]
/-
**FunLike.commSemigroup** 是 Mathlib 中的一个定义，位于命名空间 `FunLike`。
形式化陈述：{F : Type u_1} →   {α : Type u_2} →     {β : Type u_3} →       [inst : Fun
Like F α β] → [inst_1 : Mul F] → [inst_2 : CommSemigroup β] → [IsMulApply F α β]
 → CommSemigroup F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected abbrev commSemigroup [CommSemigroup β] [IsMulApply F α β] :
    CommSemigroup F :=
  DFunLike.coe_injective.commSemigroup (fun (f : F) ↦ (f : α → β)) coe_mul

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x` has left cancellative multiplication if
`β` has left cancellative multiplication. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x` has left cancellative
addition if `β` has left cancellative addition. -/]
/-
**FunLike.isLeftCancelMul** 是 Mathlib 中的一个定理，位于命名空间 `FunLike`。
形式化陈述：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} [inst : FunLike F α β] [ins
t_1 : Mul F] [inst_2 : Mul β]   [IsLeftCancelMul β] [IsMulApply F α β], IsLeftCa
ncelMul F
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isLeftCancelMul`：∀ {M₁ : Type u_1} {M₂ : Type u_2} [i
nst : Mul M₁] [inst_1 : Mul M₂] [IsLeftCancelMul M₂] (f : M₁ → M₂),   Function.I
njective f → (∀ (x y : M…
· 使用定理 `Pi.instIsLeftCancelMul`：∀ {I : Type u} {f : I → Type v₁} [inst : (i : I)
 → Mul (f i)] [∀ (i : I), IsLeftCancelMul (f i)],   IsLeftCancelMul ((i : I) → f
 i)
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `FunLike.coe_mul`：coe_mul [Mul F] [Mul β] [IsMulApply F α β] (f g : F) : 
↑(f * g) = (f : α -> β) * g
-/
protected theorem isLeftCancelMul [Mul β] [IsLeftCancelMul β] [IsMulApply F α β] :
    IsLeftCancelMul F :=
  DFunLike.coe_injective.isLeftCancelMul (fun (f : F) ↦ (f : α → β)) coe_mul

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x` has right cancellative multiplication if
`β` has right cancellative multiplication. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x` has right cancellative
addition if `β` has right cancellative addition. -/]
/-
**FunLike.isRightCancelMul** 是 Mathlib 中的一个定理，位于命名空间 `FunLike`。
形式化陈述：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} [inst : FunLike F α β] [ins
t_1 : Mul F] [inst_2 : Mul β]   [IsRightCancelMul β] [IsMulApply F α β], IsRight
CancelMul F
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isRightCancelMul`：∀ {M₁ : Type u_1} {M₂ : Type u_2} [
inst : Mul M₁] [inst_1 : Mul M₂] [IsRightCancelMul M₂] (f : M₁ → M₂),   Function
.Injective f → (∀ (x y : …
· 使用定理 `Pi.instIsRightCancelMul`：∀ {I : Type u} {f : I → Type v₁} [inst : (i : I
) → Mul (f i)] [∀ (i : I), IsRightCancelMul (f i)],   IsRightCancelMul ((i : I) 
→ f i)
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `FunLike.coe_mul`：coe_mul [Mul F] [Mul β] [IsMulApply F α β] (f g : F) : 
↑(f * g) = (f : α -> β) * g
-/
protected theorem isRightCancelMul [Mul β] [IsRightCancelMul β] [IsMulApply F α β] :
    IsRightCancelMul F :=
  DFunLike.coe_injective.isRightCancelMul (fun (f : F) ↦ (f : α → β)) coe_mul

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x` has right multiplication if
`β` has right multiplication. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x` has right
addition if `β` has cancellative addition. -/]
/-
**FunLike.isCancelMul** 是 Mathlib 中的一个定理，位于命名空间 `FunLike`。
形式化陈述：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} [inst : FunLike F α β] [ins
t_1 : Mul F] [inst_2 : Mul β] [IsCancelMul β]   [IsMulApply F α β], IsCancelMul 
F
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isCancelMul`：∀ {M₁ : Type u_1} {M₂ : Type u_2} [inst 
: Mul M₁] [inst_1 : Mul M₂] [IsCancelMul M₂] (f : M₁ → M₂),   Function.Injective
 f → (∀ (x y : M₁), …
· 使用定理 `Pi.instIsCancelMul`：∀ {I : Type u} {f : I → Type v₁} [inst : (i : I) → M
ul (f i)] [∀ (i : I), IsCancelMul (f i)],   IsCancelMul ((i : I) → f i)
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `FunLike.coe_mul`：coe_mul [Mul F] [Mul β] [IsMulApply F α β] (f g : F) : 
↑(f * g) = (f : α -> β) * g
-/
protected theorem isCancelMul [Mul β] [IsCancelMul β] [IsMulApply F α β] :
    IsCancelMul F :=
  DFunLike.coe_injective.isCancelMul (fun (f : F) ↦ (f : α → β)) coe_mul

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x` is a left cancel semigroup if `β` is a
left cancel semigroup. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x` is a left cancel additive
semigroup if `β` is a left cancel additive semigroup. -/]
/-
**FunLike.leftCancelSemigroup** 是 Mathlib 中的一个定义，位于命名空间 `FunLike`。
形式化陈述：{F : Type u_1} →   {α : Type u_2} →     {β : Type u_3} →       [inst : Fun
Like F α β] →         [inst_1 : Mul F] → [inst_2 : LeftCancelSemigroup β] → [IsM
ulApply F α β] → LeftCancelSemigroup F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected abbrev leftCancelSemigroup [LeftCancelSemigroup β] [IsMulApply F α β] :
    LeftCancelSemigroup F :=
  DFunLike.coe_injective.leftCancelSemigroup (fun (f : F) ↦ (f : α → β)) coe_mul

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x` is a right cancel semigroup if `β` is a
right cancel semigroup. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x` is a right cancel additive
semigroup if `β` is a right cancel additive semigroup. -/]
/-
**FunLike.rightCancelSemigroup** 是 Mathlib 中的一个定义，位于命名空间 `FunLike`。
形式化陈述：{F : Type u_1} →   {α : Type u_2} →     {β : Type u_3} →       [inst : Fun
Like F α β] →         [inst_1 : Mul F] → [inst_2 : RightCancelSemigroup β] → [Is
MulApply F α β] → RightCancelSemigroup F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected abbrev rightCancelSemigroup [RightCancelSemigroup β] [IsMulApply F α β] :
    RightCancelSemigroup F :=
  DFunLike.coe_injective.rightCancelSemigroup (fun (f : F) ↦ (f : α → β)) coe_mul

variable [One F]

/-- A `FunLike` type with `1` and `*` is `MulOneClass` if `β` is a `MulOneClass`. -/
@[to_additive /-- A `FunLike` type with `0` and `+` is `AddZeroClass` if `β` is a
`AddZeroClass`. -/]
/-
**FunLike.mulOneClass** 是 Mathlib 中的一个定义，位于命名空间 `FunLike`。
形式化陈述：{F : Type u_1} →   {α : Type u_2} →     {β : Type u_3} →       [inst : Fun
Like F α β] →         [inst_1 : Mul F] →           [inst_2 : One F] → [inst_3 : 
MulOneClass β] → [IsOneApply F α β] → [IsMulApply F α β] → MulOneClass F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected abbrev mulOneClass [MulOneClass β] [IsOneApply F α β] [IsMulApply F α β] :
    MulOneClass F :=
  DFunLike.coe_injective.mulOneClass (fun (f : F) ↦ (f : α → β)) coe_one coe_mul

variable [Pow F ℕ]

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x`, `1 x = 1`, and `(f ^ n) x = f x ^ n`
is a monoid if `β` is a monoid. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x`, `0 x = 0`, and
`(n • f) x = n • f x` is an additive monoid if `β` is an additive monoid. -/]
/-
**FunLike.monoid** 是 Mathlib 中的一个定义，位于命名空间 `FunLike`。
形式化陈述：{F : Type u_1} →   {α : Type u_2} →     {β : Type u_3} →       [inst : Fun
Like F α β] →         [inst_1 : Mul F] →           [inst_2 : One F] →           
  [inst_3 : Pow F ℕ] →               [inst_4 : Monoid β] → [IsOneApply F α β] → 
[IsMulApply F α β] → [IsPowApply ℕ F α β] → Monoid F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected abbrev monoid [Monoid β] [IsOneApply F α β] [IsMulApply F α β] [IsPowApply ℕ F α β] :
    Monoid F :=
  DFunLike.coe_injective.monoid (fun (f : F) ↦ (f : α → β)) coe_one coe_mul coe_pow

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x`, `1 x = 1`, and `(f ^ n) x = f x ^ n`
is a left cancel monoid if `β` is a left cancel monoid. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x`, `0 x = 0`, and
`(n • f) x = n • f x` is a left cancel additive monoid if `β` is a left cancel additive monoid. -/]
/-
**FunLike.leftCancelMonoid** 是 Mathlib 中的一个定义，位于命名空间 `FunLike`。
形式化陈述：{F : Type u_1} →   {α : Type u_2} →     {β : Type u_3} →       [inst : Fun
Like F α β] →         [inst_1 : Mul F] →           [inst_2 : One F] →           
  [inst_3 : Pow F ℕ] →               [inst_4 : LeftCancelMonoid β] →            
     [IsOneApply F α β] → [IsMulApply F α β] → [IsPowApply ℕ F α β] → LeftCancel
Monoid F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected abbrev leftCancelMonoid [LeftCancelMonoid β] [IsOneApply F α β] [IsMulApply F α β]
    [IsPowApply ℕ F α β] : LeftCancelMonoid F :=
  DFunLike.coe_injective.leftCancelMonoid (fun (f : F) ↦ (f : α → β)) coe_one coe_mul coe_pow

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x`, `1 x = 1`, and `(f ^ n) x = f x ^ n`
is a right cancel monoid if `β` is a right cancel monoid. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x`, `0 x = 0`, and
`(n • f) x = n • f x` is a right cancel additive monoid if `β` is a right cancel
additive monoid. -/]
/-
**FunLike.rightCancelMonoid** 是 Mathlib 中的一个定义，位于命名空间 `FunLike`。
形式化陈述：{F : Type u_1} →   {α : Type u_2} →     {β : Type u_3} →       [inst : Fun
Like F α β] →         [inst_1 : Mul F] →           [inst_2 : One F] →           
  [inst_3 : Pow F ℕ] →               [inst_4 : RightCancelMonoid β] →           
      [IsOneApply F α β] → [IsMulApply F α β] → [IsPowApply ℕ F α β] → RightCanc
elMonoid F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected abbrev rightCancelMonoid [RightCancelMonoid β] [IsOneApply F α β] [IsMulApply F α β]
    [IsPowApply ℕ F α β] : RightCancelMonoid F :=
  DFunLike.coe_injective.rightCancelMonoid (fun (f : F) ↦ (f : α → β)) coe_one coe_mul coe_pow

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x`, `1 x = 1`, and `(f ^ n) x = f x ^ n`
is a cancel monoid if `β` is a cancel monoid. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x`, `0 x = 0`, and
`(n • f) x = n • f x` is a cancel additive monoid if `β` is a cancel additive monoid. -/]
/-
**FunLike.cancelMonoid** 是 Mathlib 中的一个定义，位于命名空间 `FunLike`。
形式化陈述：{F : Type u_1} →   {α : Type u_2} →     {β : Type u_3} →       [inst : Fun
Like F α β] →         [inst_1 : Mul F] →           [inst_2 : One F] →           
  [inst_3 : Pow F ℕ] →               [inst_4 : CancelMonoid β] →                
 [IsOneApply F α β] → [IsMulApply F α β] → [IsPowApply ℕ F α β] → CancelMonoid F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected abbrev cancelMonoid [CancelMonoid β] [IsOneApply F α β] [IsMulApply F α β]
    [IsPowApply ℕ F α β] : CancelMonoid F :=
  DFunLike.coe_injective.cancelMonoid (fun (f : F) ↦ (f : α → β)) coe_one coe_mul coe_pow

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x`, `1 x = 1`, and `(f ^ n) x = f x ^ n`
is a commutative monoid if `β` is a commutative monoid. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x`, `0 x = 0`, and
`(n • f) x = n • f x` is a commutative additive monoid if `β` is a commutative additive monoid. -/]
/-
**FunLike.commMonoid** 是 Mathlib 中的一个定义，位于命名空间 `FunLike`。
形式化陈述：{F : Type u_1} →   {α : Type u_2} →     {β : Type u_3} →       [inst : Fun
Like F α β] →         [inst_1 : Mul F] →           [inst_2 : One F] →           
  [inst_3 : Pow F ℕ] →               [inst_4 : CommMonoid β] → [IsOneApply F α β
] → [IsMulApply F α β] → [IsPowApply ℕ F α β] → CommMonoid F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected abbrev commMonoid [CommMonoid β] [IsOneApply F α β] [IsMulApply F α β]
    [IsPowApply ℕ F α β] : CommMonoid F :=
  DFunLike.coe_injective.commMonoid (fun (f : F) ↦ (f : α → β)) coe_one coe_mul coe_pow

/-- A `FunLike` type that satisfies `(f * g) x = f x * g x`, `1 x = 1`, and `(f ^ n) x = f x ^ n`
is a cancel commutative monoid if `β` is a cancel commutative monoid. -/
@[to_additive /-- A `FunLike` type that satisfies `(f + g) x = f x + g x`, `0 x = 0`, and
`(n • f) x = n • f x` is a cancel commutative additive monoid if `β` is a cancel commutative
additive monoid. -/]
/-
**FunLike.cancelCommMonoid** 是 Mathlib 中的一个定义，位于命名空间 `FunLike`。
形式化陈述：{F : Type u_1} →   {α : Type u_2} →     {β : Type u_3} →       [inst : Fun
Like F α β] →         [inst_1 : Mul F] →           [inst_2 : One F] →           
  [inst_3 : Pow F ℕ] →               [inst_4 : CancelCommMonoid β] →            
     [IsOneApply F α β] → [IsMulApply F α β] → [IsPowApply ℕ F α β] → CancelComm
Monoid F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected abbrev cancelCommMonoid [CancelCommMonoid β] [IsOneApply F α β] [IsMulApply F α β]
    [IsPowApply ℕ F α β] : CancelCommMonoid F :=
  DFunLike.coe_injective.cancelCommMonoid (fun (f : F) ↦ (f : α → β)) coe_one coe_mul coe_pow

variable [Inv F]

/-- A `FunLike` type with inverse that satisfies `(f⁻¹) x = (f x)⁻¹` is an involutive inversion
if `β` is an involutive inversion. -/
@[to_additive /-- A `FunLike` type with negation that satisfies `(- f) x = - (f x)` is an involutive
negation if `β` is an involutive negation. -/]
/-
**FunLike.involutiveInv** 是 Mathlib 中的一个定义，位于命名空间 `FunLike`。
形式化陈述：{F : Type u_1} →   {α : Type u_2} →     {β : Type u_3} →       [inst : Fun
Like F α β] → [inst_1 : Inv F] → [inst_2 : InvolutiveInv β] → [IsInvApply F α β]
 → InvolutiveInv F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected abbrev involutiveInv [InvolutiveInv β] [IsInvApply F α β] : InvolutiveInv F :=
  DFunLike.coe_injective.involutiveInv (fun (f : F) ↦ (f : α → β)) coe_inv

/-- A `FunLike` type with `1` and inverse is an `InvOneClass` if `β` is an `InvOneClass`. -/
@[to_additive /-- A `FunLike` type with `0` and negation is a `NegZeroClass` if `β` is a
`NegZeroClass`. -/]
/-
**FunLike.invOneClass** 是 Mathlib 中的一个定义，位于命名空间 `FunLike`。
形式化陈述：{F : Type u_1} →   {α : Type u_2} →     {β : Type u_3} →       [inst : Fun
Like F α β] →         [inst_1 : One F] →           [inst_2 : Inv F] → [inst_3 : 
InvOneClass β] → [IsOneApply F α β] → [IsInvApply F α β] → InvOneClass F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected abbrev invOneClass [InvOneClass β] [IsOneApply F α β] [IsInvApply F α β] :
    InvOneClass F :=
  DFunLike.coe_injective.invOneClass (fun (f : F) ↦ (f : α → β)) coe_one coe_inv

variable [Div F] [Pow F ℤ]

/-- A `FunLike` type is a `DivInvMonoid` if `β` is a `DivInvMonoid`. -/
@[to_additive subNegMonoid /-- A `FunLike` type is a `SubNegMonoid` if `β` is a `SubNegMonoid`. -/]
/-
**FunLike.divInvMonoid** 是 Mathlib 中的一个定义，位于命名空间 `FunLike`。
形式化陈述：{F : Type u_1} →   {α : Type u_2} →     {β : Type u_3} →       [inst : Fun
Like F α β] →         [inst_1 : Mul F] →           [inst_2 : One F] →           
  [inst_3 : Pow F ℕ] →               [inst_4 : Inv F] →                 [inst_5 
: Div F] →                   [inst_6 : Pow F ℤ] →                     [inst_7 : 
DivInvMonoid β] →                       [IsOneApply F α β] →                    
     [IsMulApply F α β] →                           [IsInvApply F α β] →        
                     [IsDivApply F α β] → [IsPowApply ℕ F α β] → [IsPowApply ℤ F
 α β] → DivInvMonoid F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `FunLike` type is a `DivInvMonoid` if `β` is a `DivInvMonoid`.
-/
protected abbrev divInvMonoid [DivInvMonoid β] [IsOneApply F α β] [IsMulApply F α β]
    [IsInvApply F α β] [IsDivApply F α β] [IsPowApply ℕ F α β] [IsPowApply ℤ F α β] :
    DivInvMonoid F :=
  DFunLike.coe_injective.divInvMonoid (fun (f : F) ↦ (f : α → β)) coe_one coe_mul coe_inv coe_div
    coe_pow coe_pow

/-- A `FunLike` type is a `DivInvOneMonoid` if `β` is a `DivInvOneMonoid`. -/
@[to_additive
/-- A `FunLike` type is a `SubNegOneMonoid` if `β` is a `SubNegOneMonoid`. -/]
/-
**FunLike.divInvOneMonoid** 是 Mathlib 中的一个定义，位于命名空间 `FunLike`。
形式化陈述：{F : Type u_1} →   {α : Type u_2} →     {β : Type u_3} →       [inst : Fun
Like F α β] →         [inst_1 : Mul F] →           [inst_2 : One F] →           
  [inst_3 : Pow F ℕ] →               [inst_4 : Inv F] →                 [inst_5 
: Div F] →                   [inst_6 : Pow F ℤ] →                     [inst_7 : 
DivInvOneMonoid β] →                       [IsOneApply F α β] →                 
        [IsMulApply F α β] →                           [IsInvApply F α β] →     
                        [IsDivApply F α β] → [IsPowApply ℕ F α β] → [IsPowApply 
ℤ F α β] → DivInvOneMonoid F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected abbrev divInvOneMonoid [DivInvOneMonoid β] [IsOneApply F α β] [IsMulApply F α β]
    [IsInvApply F α β] [IsDivApply F α β] [IsPowApply ℕ F α β] [IsPowApply ℤ F α β] :
    DivInvOneMonoid F :=
  DFunLike.coe_injective.divInvOneMonoid (fun (f : F) ↦ (f : α → β)) coe_one coe_mul
    coe_inv coe_div coe_pow coe_pow

/-- A `FunLike` type is a division monoid if `β` is a division monoid. -/
@[to_additive /-- A `FunLike` type is a subtraction monoid if `β` is a subtraction monoid. -/]
/-
**FunLike.divisionMonoid** 是 Mathlib 中的一个定义，位于命名空间 `FunLike`。
形式化陈述：{F : Type u_1} →   {α : Type u_2} →     {β : Type u_3} →       [inst : Fun
Like F α β] →         [inst_1 : Mul F] →           [inst_2 : One F] →           
  [inst_3 : Pow F ℕ] →               [inst_4 : Inv F] →                 [inst_5 
: Div F] →                   [inst_6 : Pow F ℤ] →                     [inst_7 : 
DivisionMonoid β] →                       [IsOneApply F α β] →                  
       [IsMulApply F α β] →                           [IsInvApply F α β] →      
                       [IsDivApply F α β] → [IsPowApply ℕ F α β] → [IsPowApply ℤ
 F α β] → DivisionMonoid F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `FunLike` type is a division monoid if `β` is a division monoid.
-/
protected abbrev divisionMonoid [DivisionMonoid β] [IsOneApply F α β] [IsMulApply F α β]
    [IsInvApply F α β] [IsDivApply F α β] [IsPowApply ℕ F α β] [IsPowApply ℤ F α β] :
    DivisionMonoid F :=
  DFunLike.coe_injective.divisionMonoid (fun (f : F) ↦ (f : α → β)) coe_one coe_mul
    coe_inv coe_div coe_pow coe_pow

/-- A `FunLike` type is a division commutative monoid if `β` is a division commutative monoid. -/
@[to_additive subtractionCommMonoid /-- A `FunLike` type is a subtraction commutative monoid if `β`
is a subtraction commutative monoid. -/]
/-
**FunLike.divisionCommMonoid** 是 Mathlib 中的一个定义，位于命名空间 `FunLike`。
形式化陈述：{F : Type u_1} →   {α : Type u_2} →     {β : Type u_3} →       [inst : Fun
Like F α β] →         [inst_1 : Mul F] →           [inst_2 : One F] →           
  [inst_3 : Pow F ℕ] →               [inst_4 : Inv F] →                 [inst_5 
: Div F] →                   [inst_6 : Pow F ℤ] →                     [inst_7 : 
DivisionCommMonoid β] →                       [IsOneApply F α β] →              
           [IsMulApply F α β] →                           [IsInvApply F α β] →  
                           [IsDivApply F α β] → [IsPowApply ℕ F α β] → [IsPowApp
ly ℤ F α β] → DivisionCommMonoid F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected abbrev divisionCommMonoid [DivisionCommMonoid β] [IsOneApply F α β] [IsMulApply F α β]
    [IsInvApply F α β] [IsDivApply F α β] [IsPowApply ℕ F α β] [IsPowApply ℤ F α β] :
    DivisionCommMonoid F :=
  DFunLike.coe_injective.divisionCommMonoid (fun (f : F) ↦ (f : α → β)) coe_one coe_mul coe_inv
    coe_div coe_pow coe_pow

/-- A `FunLike` type is a group if `β` is a group. -/
@[to_additive /-- A `FunLike` type is an additive group if `β` is an additive group. -/]
/-
**FunLike.group** 是 Mathlib 中的一个定义，位于命名空间 `FunLike`。
形式化陈述：{F : Type u_1} →   {α : Type u_2} →     {β : Type u_3} →       [inst : Fun
Like F α β] →         [inst_1 : Mul F] →           [inst_2 : One F] →           
  [inst_3 : Pow F ℕ] →               [inst_4 : Inv F] →                 [inst_5 
: Div F] →                   [inst_6 : Pow F ℤ] →                     [inst_7 : 
Group β] →                       [IsOneApply F α β] →                         [I
sMulApply F α β] →                           [IsInvApply F α β] →               
              [IsDivApply F α β] → [IsPowApply ℕ F α β] → [IsPowApply ℤ F α β] →
 Group F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `FunLike` type is a group if `β` is a group.
-/
protected abbrev group [Group β] [IsOneApply F α β] [IsMulApply F α β] [IsInvApply F α β]
    [IsDivApply F α β] [IsPowApply ℕ F α β] [IsPowApply ℤ F α β] :
    Group F :=
  DFunLike.coe_injective.group (fun (f : F) ↦ (f : α → β)) coe_one coe_mul coe_inv coe_div coe_pow
    coe_pow

/-- A `FunLike` type is a commutative group if `β` is a commutative group. -/
@[to_additive /-- A `FunLike` type is an additive commutative group if `β` is an additive
commutative group. -/]
/-
**FunLike.commGroup** 是 Mathlib 中的一个定义，位于命名空间 `FunLike`。
形式化陈述：{F : Type u_1} →   {α : Type u_2} →     {β : Type u_3} →       [inst : Fun
Like F α β] →         [inst_1 : Mul F] →           [inst_2 : One F] →           
  [inst_3 : Pow F ℕ] →               [inst_4 : Inv F] →                 [inst_5 
: Div F] →                   [inst_6 : Pow F ℤ] →                     [inst_7 : 
CommGroup β] →                       [IsOneApply F α β] →                       
  [IsMulApply F α β] →                           [IsInvApply F α β] →           
                  [IsDivApply F α β] → [IsPowApply ℕ F α β] → [IsPowApply ℤ F α 
β] → CommGroup F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected abbrev commGroup [CommGroup β] [IsOneApply F α β] [IsMulApply F α β] [IsInvApply F α β]
    [IsDivApply F α β] [IsPowApply ℕ F α β] [IsPowApply ℤ F α β] :
    CommGroup F :=
  DFunLike.coe_injective.commGroup (fun (f : F) ↦ (f : α → β)) coe_one coe_mul coe_inv coe_div
    coe_pow coe_pow

end GroupInstances

end FunLike

