/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.Algebra.GroupWithZero.Action.Defs

/-!
# Scalar multiplication on `Finsupp`

This file defines the pointwise scalar multiplication on `Finsupp`, assuming it preserves zero.

## Main declarations

* `Finsupp.smulZeroClass`: if the action of `R` on `M` preserves `0`, then it acts on `α →₀ M`

## Implementation notes

This file is intermediate between `Finsupp.Defs` and `Finsupp.Module` in that it covers scalar
multiplication but does not rely on the definition of `Module`. Scalar multiplication is needed to
supply the `nsmul` (and `zsmul`) fields of (semi)ring structures which are fundamental for e.g.
`Polynomial`, so we want to keep the imports required for the `Finsupp.smulZeroClass` instance
reasonably light.

This file is a `noncomputable theory` and uses classical logic throughout.
-/

public section

assert_not_exists Module

noncomputable section

open Finset Function

variable {α β γ ι M M' N P G H R S : Type*}

namespace Finsupp

/-
**Finsupp.smulZeroClass** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：smulZeroClass [Zero M] [SMulZeroClass R M] : SMulZeroClass R (α ->₀ M) whe
re smul a v
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
instance smulZeroClass [Zero M] [SMulZeroClass R M] : SMulZeroClass R (α →₀ M) where
  smul a v := v.mapRange (a • ·) (smul_zero _)
  smul_zero a := by
    ext
    apply smul_zero

/-!
Throughout this section, some `Monoid` and `Semiring` arguments are specified with `{}` instead of
`[]`. See note [implicit instance arguments].
-/

@[simp, norm_cast]
/-
**Finsupp.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：coe_smul [Zero M] [SMulZeroClass R M] (b : R) (v : α ->₀ M) : ⇑(b • v) = b
 • ⇑v
参数：b : R；v : α ->₀ M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Throughout this section, some `Monoid` and `Semiring` arguments are specified wi
th `{}` instead of
`[]`. See note [implicit instance arguments].
-/
theorem coe_smul [Zero M] [SMulZeroClass R M] (b : R) (v : α →₀ M) : ⇑(b • v) = b • ⇑v :=
  rfl
/-
**Finsupp.smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：smul_apply [Zero M] [SMulZeroClass R M] (b : R) (v : α ->₀ M) (a : α) : (b
 • v) a = b • v a
参数：b : R；v : α ->₀ M；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_apply [Zero M] [SMulZeroClass R M] (b : R) (v : α →₀ M) (a : α) :
    (b • v) a = b • v a :=
  rfl
/-
**Finsupp.instSMulWithZero** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：instSMulWithZero [Zero R] [Zero M] [SMulWithZero R M] : SMulWithZero R (α 
->₀ M) where zero_smul f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMulWithZero [Zero R] [Zero M] [SMulWithZero R M] : SMulWithZero R (α →₀ M) where
  zero_smul f := by ext i; exact zero_smul _ _

variable (α M)
/-
**Finsupp.distribSMul** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：distribSMul [AddZeroClass M] [DistribSMul R M] : DistribSMul R (α ->₀ M) w
here smul_add _ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance distribSMul [AddZeroClass M] [DistribSMul R M] : DistribSMul R (α →₀ M) where
  smul_add _ _ _ := ext fun _ => smul_add _ _ _
  smul_zero _ := ext fun _ => smul_zero _
/-
**Finsupp.isScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：isScalarTower [Zero M] [SMulZeroClass R M] [SMulZeroClass S M] [SMul R S] 
[IsScalarTower R S M] : IsScalarTower R S (α ->₀ M) where smul_assoc _ _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
instance isScalarTower [Zero M] [SMulZeroClass R M] [SMulZeroClass S M] [SMul R S]
    [IsScalarTower R S M] : IsScalarTower R S (α →₀ M) where
  smul_assoc _ _ _ := ext fun _ => smul_assoc _ _ _
/-
**Finsupp.smulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：smulCommClass [Zero M] [SMulZeroClass R M] [SMulZeroClass S M] [SMulCommCl
ass R S M] : SMulCommClass R S (α ->₀ M) where smul_comm _ _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
instance smulCommClass [Zero M] [SMulZeroClass R M] [SMulZeroClass S M] [SMulCommClass R S M] :
    SMulCommClass R S (α →₀ M) where
  smul_comm _ _ _ := ext fun _ => smul_comm _ _ _
/-
**Finsupp.isCentralScalar** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：isCentralScalar [Zero M] [SMulZeroClass R M] [SMulZeroClass Rᵐᵒᵖ M] [IsCen
tralScalar R M] : IsCentralScalar R (α ->₀ M) where op_smul_eq_smul _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
-/
instance isCentralScalar [Zero M] [SMulZeroClass R M] [SMulZeroClass Rᵐᵒᵖ M] [IsCentralScalar R M] :
    IsCentralScalar R (α →₀ M) where
  op_smul_eq_smul _ _ := ext fun _ => op_smul_eq_smul _ _

variable {α M}
/-
**Finsupp.support_smul** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：support_smul [Zero M] [SMulZeroClass R M] {b : R} {g : α ->₀ M} : (b • g).
support subseteq g.support
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem support_smul [Zero M] [SMulZeroClass R M] {b : R} {g : α →₀ M} :
    (b • g).support ⊆ g.support := fun a => by
  simp only [smul_apply, mem_support_iff, Ne]
  exact mt fun h => h.symm ▸ smul_zero _

@[simp]
/-
**Finsupp.smul_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：smul_single [Zero M] [SMulZeroClass R M] (c : R) (a : α) (b : M) : c • Fin
supp.single a b = Finsupp.single a (c • b)
参数：c : R；a : α；b : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.mapRange_single`：mapRange_single {f : M -> N} {hf : f 0 = 0} {a 
: α} {b : M} : mapRange f hf (single a b) = single a (f b)
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem smul_single [Zero M] [SMulZeroClass R M] (c : R) (a : α) (b : M) :
    c • Finsupp.single a b = Finsupp.single a (c • b) :=
  mapRange_single
/-
**Finsupp.mapRange_smul'** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mapRange_smul' [Zero M] [SMulZeroClass R M] [Zero N] [SMulZeroClass S N] {
f : M -> N} {hf : f 0 = 0} (c : R) (d : S) (v : α ->₀ M) (hsmul : forall x, f (c
 • x) = d • f x) : mapRange f hf (c • v) = d • mapRange f hf v
参数：c : R；d : S；v : α ->₀ M；hsmul : forall x, f (c • x) = d • f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mapRange_smul' [Zero M] [SMulZeroClass R M] [Zero N]
    [SMulZeroClass S N] {f : M → N} {hf : f 0 = 0} (c : R) (d : S) (v : α →₀ M)
    (hsmul : ∀ x, f (c • x) = d • f x) : mapRange f hf (c • v) = d • mapRange f hf v := by
  ext
  simp [hsmul]
/-
**Finsupp.mapRange_smul** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mapRange_smul [Zero M] [SMulZeroClass R M] [Zero N] [SMulZeroClass R N] {f
 : M -> N} {hf : f 0 = 0} (c : R) (v : α ->₀ M) (hsmul : forall x, f (c • x) = c
 • f x) : mapRange f hf (c • v) = c • mapRange f hf v
参数：c : R；v : α ->₀ M；hsmul : forall x, f (c • x) = c • f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.mapRange_smul'`：mapRange_smul' [Zero M] [SMulZeroClass R M] [Zer
o N] [SMulZeroClass S N] {f : M -> N} {hf : f 0 = 0} (c : R) (d : S) (v : α ->₀ 
M) (hsmul : …
-/
theorem mapRange_smul [Zero M] [SMulZeroClass R M] [Zero N]
    [SMulZeroClass R N] {f : M → N} {hf : f 0 = 0} (c : R) (v : α →₀ M)
    (hsmul : ∀ x, f (c • x) = c • f x) : mapRange f hf (c • v) = c • mapRange f hf v :=
  mapRange_smul' c c v hsmul

end Finsupp

