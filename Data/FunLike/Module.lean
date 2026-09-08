/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Data.FunLike.Group
public import Mathlib.Algebra.Module.Pi

/-! # Module instances for `FunLike` types
In this file we define various instances related to modules for `FunLike` types.

Note that currently, these are not registered as instances, but only `abbrev`s to avoid long
typeclass searches.

## TODO:
Add definitions and API for the coercion being a linear map, similar to `FunLike.coeMonoidHom`,
and related definitions.

-/

public section

variable {M M' F α β : Type*} [i : FunLike F α β]

namespace FunLike

section SMulInstances

variable [SMul M β] [SMul M' β] [SMul M F] [SMul M' F] [IsSMulApply M F α β] [IsSMulApply M' F α β]

include i in
/-
**FunLike.isScalarTower** 是 Mathlib 中的一个定理，位于命名空间 `FunLike`。
形式化陈述：∀ {M : Type u_1} {M' : Type u_2} {F : Type u_3} {α : Type u_4} {β : Type u
_5} [i : FunLike F α β] [inst : SMul M β]   [inst_1 : SMul M' β] [inst_2 : SMul 
M F] [inst_3 : SMul M' F] [IsSMulApply M F α β] [IsSMulApply M' F α β]   [inst_6
 : SMul M M'] [IsScalarTower M M' β], IsScalarTower M M' F
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
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
protected theorem isScalarTower [SMul M M'] [IsScalarTower M M' β] : IsScalarTower M M' F where
  smul_assoc _ _ _ := by apply DFunLike.ext; simp

include i in
/-
**FunLike.smulCommClass** 是 Mathlib 中的一个定理，位于命名空间 `FunLike`。
形式化陈述：∀ {M : Type u_1} {M' : Type u_2} {F : Type u_3} {α : Type u_4} {β : Type u
_5} [i : FunLike F α β] [inst : SMul M β]   [inst_1 : SMul M' β] [inst_2 : SMul 
M F] [inst_3 : SMul M' F] [IsSMulApply M F α β] [IsSMulApply M' F α β]   [SMulCo
mmClass M M' β], SMulCommClass M M' F
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
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
protected theorem smulCommClass [SMulCommClass M M' β] : SMulCommClass M M' F where
  smul_comm _ _ _ := by apply DFunLike.ext; simp [smul_comm]

end SMulInstances

section ModuleInstance

include i in
/-
**FunLike.isCentralScalar** 是 Mathlib 中的一个定理，位于命名空间 `FunLike`。
形式化陈述：∀ {M : Type u_1} {F : Type u_3} {α : Type u_4} {β : Type u_5} [i : FunLike
 F α β] [inst : SMul M F]   [inst_1 : SMul Mᵐᵒᵖ F] [inst_2 : SMul M β] [inst_3 :
 SMul Mᵐᵒᵖ β] [IsCentralScalar M β] [IsSMulApply M F α β]   [IsSMulApply Mᵐᵒᵖ F 
α β], IsCentralScalar M F
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
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
protected theorem isCentralScalar [SMul M F] [SMul Mᵐᵒᵖ F] [SMul M β] [SMul Mᵐᵒᵖ β]
    [IsCentralScalar M β] [IsSMulApply M F α β] [IsSMulApply Mᵐᵒᵖ F α β] :
    IsCentralScalar M F where
  op_smul_eq_smul a b := by apply DFunLike.ext; simp [op_smul_eq_smul]

/-- A `FunLike` type with scalar multiplication that satisfies `(m • f) x = m • f x` and
`0 x = 0`, `(f + g) x = f x + g x` is a `DistribSMul` if `β` is a `DistribSMul`. -/
/-
**FunLike.distribSMul** 是 Mathlib 中的一个定义，位于命名空间 `FunLike`。
形式化陈述：{M : Type u_1} →   {F : Type u_3} →     {α : Type u_4} →       {β : Type u
_5} →         [i : FunLike F α β] →           [inst : AddZeroClass β] →         
    [inst_1 : AddZeroClass F] →               [inst_2 : DistribSMul M β] →      
           [inst_3 : SMul M F] → [IsZeroApply F α β] → [IsAddApply F α β] → [IsS
MulApply M F α β] → DistribSMul M F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `FunLike` type with scalar multiplication that satisfies `(m • f) x = m • f x`
 and
`0 x = 0`, `(f + g) x = f x + g x` is a `DistribSMul` if `β` is a `DistribSMul`.
-/
protected abbrev distribSMul [AddZeroClass β] [AddZeroClass F] [DistribSMul M β]
    [SMul M F] [IsZeroApply F α β] [IsAddApply F α β] [IsSMulApply M F α β] :
    DistribSMul M F :=
  DFunLike.coe_injective.distribSMul (coeAddMonoidHom F α β) FunLike.coe_smul

/-- A `FunLike` type with scalar multiplication that satisfies `(m • f) x = m • f x`
is a `MulAction` if `β` is a `MulAction`. -/
@[to_additive /-- A `FunLike` type with scalar multiplication that satisfies `(m • f) x = m • f x`
is an `AddAction` if `β` is an `AddAction`. -/]
/-
**FunLike.mulAction** 是 Mathlib 中的一个定义，位于命名空间 `FunLike`。
形式化陈述：{M : Type u_1} →   {F : Type u_3} →     {α : Type u_4} →       {β : Type u
_5} →         [i : FunLike F α β] →           [inst : SMul M F] → [inst_1 : Mono
id M] → [inst_2 : MulAction M β] → [IsSMulApply M F α β] → MulAction M F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected abbrev mulAction [SMul M F] [Monoid M] [MulAction M β] [IsSMulApply M F α β] :
    MulAction M F :=
  DFunLike.coe_injective.mulAction _ FunLike.coe_smul

/-- A `FunLike` type with scalar multiplication that satisfies `(m • f) x = m • f x`, `0 x = 0`,
`(f + g) x = f x + g x` is a `DistribMulAction` if `β` is a `DistribMulAction`. -/
/-
**FunLike.distribMulAction** 是 Mathlib 中的一个定义，位于命名空间 `FunLike`。
形式化陈述：{M : Type u_1} →   {F : Type u_3} →     {α : Type u_4} →       {β : Type u
_5} →         [i : FunLike F α β] →           [inst : Monoid M] →             [i
nst_1 : AddMonoid β] →               [inst_2 : AddMonoid F] →                 [i
nst_3 : DistribMulAction M β] →                   [inst_4 : SMul M F] →         
            [IsZeroApply F α β] → [IsAddApply F α β] → [IsSMulApply M F α β] → D
istribMulAction M F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `FunLike` type with scalar multiplication that satisfies `(m • f) x = m • f x`
, `0 x = 0`,
`(f + g) x = f x + g x` is a `DistribMulAction` if `β` is a `DistribMulAction`.
-/
protected abbrev distribMulAction [Monoid M] [AddMonoid β] [AddMonoid F] [DistribMulAction M β]
    [SMul M F] [IsZeroApply F α β] [IsAddApply F α β] [IsSMulApply M F α β] :
    DistribMulAction M F :=
  DFunLike.coe_injective.distribMulAction (coeAddMonoidHom F α β) FunLike.coe_smul

variable [Semiring M] [AddCommMonoid β] [Module M β] [AddCommMonoid F] [SMul M F]
  [IsZeroApply F α β] [IsAddApply F α β] [IsSMulApply ℕ F α β] [IsSMulApply M F α β]

/-- A `FunLike` type is a `Module` if `β` is a `Module`. -/
/-
**FunLike.module** 是 Mathlib 中的一个定义，位于命名空间 `FunLike`。
形式化陈述：{M : Type u_1} →   {F : Type u_3} →     {α : Type u_4} →       {β : Type u
_5} →         [i : FunLike F α β] →           [inst : Semiring M] →             
[inst_1 : AddCommMonoid β] →               [inst_2 : _root_.Module M β] →       
          [inst_3 : AddCommMonoid F] →                   [inst_4 : SMul M F] →  
                   [IsZeroApply F α β] → [IsAddApply F α β] → [IsSMulApply M F α
 β] → _root_.Module M F
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `FunLike` type is a `Module` if `β` is a `Module`.
-/
protected abbrev module : Module M F :=
  coeAddHom_injective.module M (coeAddMonoidHom F α β) coe_smul

end ModuleInstance

end FunLike

