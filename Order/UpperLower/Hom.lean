/-
Copyright (c) 2022 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Hom.CompleteLattice
public import Mathlib.Order.UpperLower.Principal

/-!
# `UpperSet.Ici` etc. as `Sup`/`sSup`/`Inf`/`sInf`-homomorphisms

In this file we define `UpperSet.iciSupHom` etc. These functions are `UpperSet.Ici` and
`LowerSet.Iic` bundled as `SupHom`s, `InfHom`s, `sSupHom`s, or `sInfHom`s.
-/

@[expose] public section


variable {α : Type*}

open OrderDual

namespace UpperSet

section SemilatticeSup

variable [SemilatticeSup α]

/-- `UpperSet.Ici` as a `SupHom`. -/
/-
**UpperSet.iciSupHom** 是 Mathlib 中的一个定义，位于命名空间 `UpperSet`。
形式化陈述：iciSupHom : SupHom α (UpperSet α)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `UpperSet.Ici_sup`：Ici_sup [SemilatticeSup α] (a b : α) : Ici (a ⊔ b) = I
ci a ⊔ Ici b

--- 原说明 ---
`UpperSet.Ici` as a `SupHom`.
-/
def iciSupHom : SupHom α (UpperSet α) :=
  ⟨Ici, Ici_sup⟩

@[simp]
/-
**UpperSet.coe_iciSupHom** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：coe_iciSupHom : (iciSupHom : α -> UpperSet α) = Ici
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_iciSupHom : (iciSupHom : α → UpperSet α) = Ici :=
  rfl

@[simp]
/-
**UpperSet.iciSupHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：iciSupHom_apply (a : α) : iciSupHom a = Ici a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iciSupHom_apply (a : α) : iciSupHom a = Ici a :=
  rfl

end SemilatticeSup

variable [CompleteLattice α]

/-- `UpperSet.Ici` as a `sSupHom`. -/
/-
**UpperSet.icisSupHom** 是 Mathlib 中的一个定义，位于命名空间 `UpperSet`。
形式化陈述：icisSupHom : sSupHom α (UpperSet α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`UpperSet.Ici` as a `sSupHom`.
-/
def icisSupHom : sSupHom α (UpperSet α) :=
  ⟨Ici, fun s => (Ici_sSup s).trans sSup_image.symm⟩

@[simp]
/-
**UpperSet.coe_icisSupHom** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：coe_icisSupHom : (icisSupHom : α -> UpperSet α) = Ici
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_icisSupHom : (icisSupHom : α → UpperSet α) = Ici :=
  rfl

@[simp]
/-
**UpperSet.icisSupHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `UpperSet`。
形式化陈述：icisSupHom_apply (a : α) : icisSupHom a = Ici a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem icisSupHom_apply (a : α) : icisSupHom a = Ici a :=
  rfl

end UpperSet

namespace LowerSet

section SemilatticeInf

variable [SemilatticeInf α]

/-- `LowerSet.Iic` as an `InfHom`. -/
/-
**LowerSet.iicInfHom** 是 Mathlib 中的一个定义，位于命名空间 `LowerSet`。
形式化陈述：iicInfHom : InfHom α (LowerSet α)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LowerSet.Iic_inf`：∀ {α : Type u_1} [inst : SemilatticeInf α] (a b : α), 
LowerSet.Iic (a ⊓ b) = LowerSet.Iic a ⊓ LowerSet.Iic b

--- 原说明 ---
`LowerSet.Iic` as an `InfHom`.
-/
def iicInfHom : InfHom α (LowerSet α) :=
  ⟨Iic, Iic_inf⟩

@[simp]
/-
**LowerSet.coe_iicInfHom** 是 Mathlib 中的一个定理，位于命名空间 `LowerSet`。
形式化陈述：coe_iicInfHom : (iicInfHom : α -> LowerSet α) = Iic
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_iicInfHom : (iicInfHom : α → LowerSet α) = Iic :=
  rfl

@[simp]
/-
**LowerSet.iicInfHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `LowerSet`。
形式化陈述：iicInfHom_apply (a : α) : iicInfHom a = Iic a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iicInfHom_apply (a : α) : iicInfHom a = Iic a :=
  rfl

end SemilatticeInf

variable [CompleteLattice α]

/-- `LowerSet.Iic` as an `sInfHom`. -/
/-
**LowerSet.iicsInfHom** 是 Mathlib 中的一个定义，位于命名空间 `LowerSet`。
形式化陈述：iicsInfHom : sInfHom α (LowerSet α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LowerSet.Iic` as an `sInfHom`.
-/
def iicsInfHom : sInfHom α (LowerSet α) :=
  ⟨Iic, fun s => (Iic_sInf s).trans sInf_image.symm⟩

@[simp]
/-
**LowerSet.coe_iicsInfHom** 是 Mathlib 中的一个定理，位于命名空间 `LowerSet`。
形式化陈述：coe_iicsInfHom : (iicsInfHom : α -> LowerSet α) = Iic
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_iicsInfHom : (iicsInfHom : α → LowerSet α) = Iic :=
  rfl

@[simp]
/-
**LowerSet.iicsInfHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `LowerSet`。
形式化陈述：iicsInfHom_apply (a : α) : iicsInfHom a = Iic a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iicsInfHom_apply (a : α) : iicsInfHom a = Iic a :=
  rfl

end LowerSet

