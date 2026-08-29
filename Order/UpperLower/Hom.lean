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

/--
Definition of `iciSupHom` / `iciSupHom` 的定义

English:
definition iciSupHom
  signature: : SupHom α (UpperSet α)
  body: ⟨Ici, Ici_sup⟩

@[simp]

中文:
定义 iciSupHom
  签名: : SupHom α (UpperSet α)
  定义体: ⟨Ici, Ici_sup⟩

@[simp]

Depends on / 依赖: Ici_sup
-/
def iciSupHom : SupHom α (UpperSet α) :=
  ⟨Ici, Ici_sup⟩

@[simp]
/--
theorem `coe_iciSupHom` / 定理 `coe_iciSupHom`

English:
theorem coe_iciSupHom
  statement: (iciSupHom : α -> UpperSet α) = Ici
  proof: rfl

@[simp]

中文:
定理 coe_iciSupHom
  结论: (iciSupHom : α -> UpperSet α) = Ici
  证明: rfl

@[simp]
-/
theorem coe_iciSupHom : (iciSupHom : α -> UpperSet α) = Ici :=
  rfl

@[simp]
/--
theorem `iciSupHom_apply` / 定理 `iciSupHom_apply`

English:
theorem iciSupHom_apply
  given: (a : α)
  statement: iciSupHom a = Ici a
  proof: rfl

中文:
定理 iciSupHom_apply
  条件: (a : α)
  结论: iciSupHom a = Ici a
  证明: rfl
-/
theorem iciSupHom_apply (a : α) : iciSupHom a = Ici a :=
  rfl

end SemilatticeSup

variable [CompleteLattice α]

/--
Definition of `icisSupHom` / `icisSupHom` 的定义

English:
definition icisSupHom
  signature: : sSupHom α (UpperSet α)
  body: ⟨Ici, fun s => (Ici_sSup s).trans sSup_image.symm⟩

@[simp]

中文:
定义 icisSupHom
  签名: : sSupHom α (UpperSet α)
  定义体: ⟨Ici, fun s => (Ici_sSup s).trans sSup_image.symm⟩

@[simp]

Depends on / 依赖: Ici_sSup, sSup_image, sSup_image.symm
-/
def icisSupHom : sSupHom α (UpperSet α) :=
  ⟨Ici, fun s => (Ici_sSup s).trans sSup_image.symm⟩

@[simp]
/--
theorem `coe_icisSupHom` / 定理 `coe_icisSupHom`

English:
theorem coe_icisSupHom
  statement: (icisSupHom : α -> UpperSet α) = Ici
  proof: rfl

@[simp]

中文:
定理 coe_icisSupHom
  结论: (icisSupHom : α -> UpperSet α) = Ici
  证明: rfl

@[simp]
-/
theorem coe_icisSupHom : (icisSupHom : α -> UpperSet α) = Ici :=
  rfl

@[simp]
/--
theorem `icisSupHom_apply` / 定理 `icisSupHom_apply`

English:
theorem icisSupHom_apply
  given: (a : α)
  statement: icisSupHom a = Ici a
  proof: rfl

中文:
定理 icisSupHom_apply
  条件: (a : α)
  结论: icisSupHom a = Ici a
  证明: rfl
-/
theorem icisSupHom_apply (a : α) : icisSupHom a = Ici a :=
  rfl

end UpperSet

namespace LowerSet

section SemilatticeInf

variable [SemilatticeInf α]

/--
Definition of `iicInfHom` / `iicInfHom` 的定义

English:
definition iicInfHom
  signature: : InfHom α (LowerSet α)
  body: ⟨Iic, Iic_inf⟩

@[simp]

中文:
定义 iicInfHom
  签名: : InfHom α (LowerSet α)
  定义体: ⟨Iic, Iic_inf⟩

@[simp]

Depends on / 依赖: Iic_inf
-/
def iicInfHom : InfHom α (LowerSet α) :=
  ⟨Iic, Iic_inf⟩

@[simp]
/--
theorem `coe_iicInfHom` / 定理 `coe_iicInfHom`

English:
theorem coe_iicInfHom
  statement: (iicInfHom : α -> LowerSet α) = Iic
  proof: rfl

@[simp]

中文:
定理 coe_iicInfHom
  结论: (iicInfHom : α -> LowerSet α) = Iic
  证明: rfl

@[simp]
-/
theorem coe_iicInfHom : (iicInfHom : α -> LowerSet α) = Iic :=
  rfl

@[simp]
/--
theorem `iicInfHom_apply` / 定理 `iicInfHom_apply`

English:
theorem iicInfHom_apply
  given: (a : α)
  statement: iicInfHom a = Iic a
  proof: rfl

中文:
定理 iicInfHom_apply
  条件: (a : α)
  结论: iicInfHom a = Iic a
  证明: rfl
-/
theorem iicInfHom_apply (a : α) : iicInfHom a = Iic a :=
  rfl

end SemilatticeInf

variable [CompleteLattice α]

/--
Definition of `iicsInfHom` / `iicsInfHom` 的定义

English:
definition iicsInfHom
  signature: : sInfHom α (LowerSet α)
  body: ⟨Iic, fun s => (Iic_sInf s).trans sInf_image.symm⟩

@[simp]

中文:
定义 iicsInfHom
  签名: : sInfHom α (LowerSet α)
  定义体: ⟨Iic, fun s => (Iic_sInf s).trans sInf_image.symm⟩

@[simp]

Depends on / 依赖: Iic_sInf, sInf_image, sInf_image.symm
-/
def iicsInfHom : sInfHom α (LowerSet α) :=
  ⟨Iic, fun s => (Iic_sInf s).trans sInf_image.symm⟩

@[simp]
/--
theorem `coe_iicsInfHom` / 定理 `coe_iicsInfHom`

English:
theorem coe_iicsInfHom
  statement: (iicsInfHom : α -> LowerSet α) = Iic
  proof: rfl

@[simp]

中文:
定理 coe_iicsInfHom
  结论: (iicsInfHom : α -> LowerSet α) = Iic
  证明: rfl

@[simp]
-/
theorem coe_iicsInfHom : (iicsInfHom : α -> LowerSet α) = Iic :=
  rfl

@[simp]
/--
theorem `iicsInfHom_apply` / 定理 `iicsInfHom_apply`

English:
theorem iicsInfHom_apply
  given: (a : α)
  statement: iicsInfHom a = Iic a
  proof: rfl

中文:
定理 iicsInfHom_apply
  条件: (a : α)
  结论: iicsInfHom a = Iic a
  证明: rfl
-/
theorem iicsInfHom_apply (a : α) : iicsInfHom a = Iic a :=
  rfl

end LowerSet
