/-
Copyright (c) 2023 Apurva Nakade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade
-/
module

public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Algebra.Order.Nonneg.Basic

/-!
# Modules over nonnegative elements

For an ordered ring `R`, this file proves that any (ordered) `R`-module `M` is also an (ordered)
`R≥0`-module.

Among other things, these instances are useful for working with `ConvexCone`.
-/

public section

assert_not_exists Finset

variable {R S M : Type*}

local notation3 "R≥0" => {c : R // 0 ≤ c}

namespace Nonneg
variable [Semiring R] [PartialOrder R]

section SMul

variable [SMul R S]

/-
**Nonneg.instSMul** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：instSMul : SMul R>=0 S where smul c x
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMul : SMul R≥0 S where
  smul c x := c.val • x

@[simp, norm_cast]
/-
**Nonneg.coe_smul** 是 Mathlib 中的一个引理，位于命名空间 `Nonneg`。
形式化陈述：coe_smul (a : R>=0) (x : S) : (a : R) • x = a • x
参数：a : R>=0；x : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_smul (a : R≥0) (x : S) : (a : R) • x = a • x :=
  rfl

@[simp]
/-
**Nonneg.mk_smul** 是 Mathlib 中的一个引理，位于命名空间 `Nonneg`。
形式化陈述：mk_smul (a) (ha) (x : S) : (⟨a, ha⟩ : R>=0) • x = a • x
参数：a；ha；x : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_smul (a) (ha) (x : S) : (⟨a, ha⟩ : R≥0) • x = a • x :=
  rfl

end SMul

section IsScalarTower

variable [IsOrderedRing R] [SMul R S] [SMul R M] [SMul S M] [IsScalarTower R S M]

/-
**Nonneg.instIsScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：instIsScalarTower : IsScalarTower R>=0 S M
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SMul.comp.isScalarTower`：∀ {M : Type u_1} {N : Type u_2} {α : Type u_5} 
{β : Type u_6} [inst : SMul M α] [inst_1 : SMul M β] [inst_2 : SMul α β]   [IsSc
alarTower M α…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
instance instIsScalarTower : IsScalarTower R≥0 S M :=
  SMul.comp.isScalarTower ↑Nonneg.coeRingHom

end IsScalarTower

section SMulWithZero

variable [Zero S] [SMulWithZero R S]

/-
**Nonneg.instSMulWithZero** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：instSMulWithZero : SMulWithZero R>=0 S where smul_zero _
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMulWithZero : SMulWithZero R≥0 S where
  smul_zero _ := smul_zero _
  zero_smul _ := zero_smul _ _

end SMulWithZero

section IsOrderedModule

variable [IsOrderedRing R] [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
  [SMulWithZero R M]

/-
**Nonneg.instIsOrderedModule** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：instIsOrderedModule [hM : IsOrderedModule R M] : IsOrderedModule R>=0 M wh
ere smul_le_smul_of_nonneg_left _b hb _a₁ _a₂ ha
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `PosSMulMono.smul_le_smul_of_nonneg_left`：∀ {α : Type u_1} {β : Type u_2}
 {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}
   [self : PosSMulMono α β] ⦃…
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `SMulPosMono.smul_le_smul_of_nonneg_right`：∀ {α : Type u_1} {β : Type u_2
} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero β
}   [self : SMulPosMono α β] ⦃…
· 使用定理 `IsOrderedModule.toSMulPosMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
-/
instance instIsOrderedModule [hM : IsOrderedModule R M] : IsOrderedModule R≥0 M where
  smul_le_smul_of_nonneg_left _b hb _a₁ _a₂ ha := hM.smul_le_smul_of_nonneg_left hb ha
  smul_le_smul_of_nonneg_right _b hb _a₁ _a₂ ha := hM.smul_le_smul_of_nonneg_right hb ha
/-
**Nonneg.instIsStrictOrderedModule** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：instIsStrictOrderedModule [hM : IsStrictOrderedModule R M] : IsStrictOrder
edModule R>=0 M where smul_lt_smul_of_pos_left _b hb _a₁ _a₂ ha
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `PosSMulStrictMono.smul_lt_smul_of_pos_left`：∀ {α : Type u_1} {β : Type u
_2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero
 α}   [self : PosSMulStrictMono …
· 使用定理 `IsStrictOrderedModule.toPosSMulStrictMono`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
α}   {inst_4 : Zero β} [self : …
· 使用定理 `SMulPosStrictMono.smul_lt_smul_of_pos_right`：∀ {α : Type u_1} {β : Type 
u_2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zer
o β}   [self : SMulPosStrictMono …
· 使用定理 `IsStrictOrderedModule.toSMulPosStrictMono`：∀ {α : Type u_1} {β : Type u_
2} {inst : SMul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero 
α}   {inst_4 : Zero β} [self : …
-/
instance instIsStrictOrderedModule [hM : IsStrictOrderedModule R M] :
    IsStrictOrderedModule R≥0 M where
  smul_lt_smul_of_pos_left _b hb _a₁ _a₂ ha := hM.smul_lt_smul_of_pos_left hb ha
  smul_lt_smul_of_pos_right _b hb _a₁ _a₂ ha := hM.smul_lt_smul_of_pos_right hb ha

end IsOrderedModule

section Module

variable [IsOrderedRing R] [AddCommMonoid M] [Module R M]

/-- A module over an ordered semiring is also a module over just the non-negative scalars. -/
/-
**Nonneg.instModule** 是 Mathlib 中的一个实例，位于命名空间 `Nonneg`。
形式化陈述：instModule : Module R>=0 M where smul
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R

--- 原说明 ---
A module over an ordered semiring is also a module over just the non-negative sc
alars.
-/
instance instModule : Module R≥0 M where
  smul := instSMul.smul
  __ := Module.compHom M coeRingHom

end Module
end Nonneg

