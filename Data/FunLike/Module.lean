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
/--
theorem `isScalarTower` / 定理 `isScalarTower`

English:
theorem isScalarTower
  given: [SMul M M'] [IsScalarTower M M' β]
  statement: IsScalarTower M M' F where
  proof: by apply DFunLike.ext; simp

include i in

中文:
定理 isScalarTower
  条件: [标量乘法 M M'] [标量塔 M M' β]
  结论: 标量塔 M M' F where
  证明: by apply DFunLike.ext; simp

include i in
-/
protected theorem isScalarTower [SMul M M'] [IsScalarTower M M' β] : IsScalarTower M M' F where
  smul_assoc _ _ _ := by apply DFunLike.ext; simp

include i in
/--
theorem `smulCommClass` / 定理 `smulCommClass`

English:
theorem smulCommClass
  given: [SMulCommClass M M' β]
  statement: SMulCommClass M M' F where
  proof: by apply DFunLike.ext; simp [smul_comm]

中文:
定理 smulCommClass
  条件: [标量交换类 M M' β]
  结论: 标量交换类 M M' F where
  证明: by apply DFunLike.ext; simp [smul_comm]
-/
protected theorem smulCommClass [SMulCommClass M M' β] : SMulCommClass M M' F where
  smul_comm _ _ _ := by apply DFunLike.ext; simp [smul_comm]

end SMulInstances

section ModuleInstance

include i in
/--
theorem `isCentralScalar` / 定理 `isCentralScalar`

English:
theorem isCentralScalar
  statement: [SMul M F] [SMul Mᵐᵒᵖ F] [SMul M β] [SMul Mᵐᵒᵖ β]
  proof: by apply DFunLike.ext; simp [op_smul_eq_smul]

中文:
定理 isCentralScalar
  结论: [标量乘法 M F] [标量乘法 Mᵐᵒᵖ F] [标量乘法 M β] [标量乘法 Mᵐᵒᵖ β]
  证明: by apply DFunLike.ext; simp [op_smul_eq_smul]
-/
protected theorem isCentralScalar [SMul M F] [SMul Mᵐᵒᵖ F] [SMul M β] [SMul Mᵐᵒᵖ β]
    [IsCentralScalar M β] [IsSMulApply M F α β] [IsSMulApply Mᵐᵒᵖ F α β] :
    IsCentralScalar M F where
  op_smul_eq_smul a b := by apply DFunLike.ext; simp [op_smul_eq_smul]

/--
Definition of `distribSMul` / `distribSMul` 的定义

English:
abbreviation distribSMul
  signature: [AddZeroClass β] [AddZeroClass F] [DistribSMul M β]
  body: DFunLike.coe_injective.distribSMul (coeAddMonoidHom F α β) FunLike.coe_smul

中文:
缩写 distribSMul
  签名: [加法零类 β] [加法零类 F] [分配标量乘法 M β]
  定义体: DFunLike.coe_injective.distribSMul (coeAddMonoidHom F α β) FunLike.coe_smul
-/
protected abbrev distribSMul [AddZeroClass β] [AddZeroClass F] [DistribSMul M β]
    [SMul M F] [IsZeroApply F α β] [IsAddApply F α β] [IsSMulApply M F α β] :
    DistribSMul M F :=
  DFunLike.coe_injective.distribSMul (coeAddMonoidHom F α β) FunLike.coe_smul

/-- A `FunLike` type with scalar multiplication that satisfies `(m • f) x = m • f x`
is a `MulAction` if `β` is a `MulAction`. -/
@[to_additive /-- A `FunLike` type with scalar multiplication that satisfies `(m • f) x = m • f x`
is an `AddAction` if `β` is an `AddAction`. -/]
/--
Definition of `mulAction` / `mulAction` 的定义

English:
abbreviation mulAction
  signature: [SMul M F] [Monoid M] [MulAction M β] [IsSMulApply M F α β]
  body: DFunLike.coe_injective.mulAction _ FunLike.coe_smul

中文:
缩写 mulAction
  签名: [标量乘法 M F] [幺半群 M] [乘法作用 M β] [是SMulApply M F α β]
  定义体: DFunLike.coe_injective.mulAction _ FunLike.coe_smul
-/
protected abbrev mulAction [SMul M F] [Monoid M] [MulAction M β] [IsSMulApply M F α β] :
    MulAction M F :=
  DFunLike.coe_injective.mulAction _ FunLike.coe_smul

/--
Definition of `distribMulAction` / `distribMulAction` 的定义

English:
abbreviation distribMulAction
  signature: [Monoid M] [AddMonoid β] [AddMonoid F] [DistribMulAction M β]
  body: DFunLike.coe_injective.distribMulAction (coeAddMonoidHom F α β) FunLike.coe_smul

中文:
缩写 distribMulAction
  签名: [幺半群 M] [加法幺半群 β] [加法幺半群 F] [分配乘法作用 M β]
  定义体: DFunLike.coe_injective.distribMulAction (coeAddMonoidHom F α β) FunLike.coe_smul
-/
protected abbrev distribMulAction [Monoid M] [AddMonoid β] [AddMonoid F] [DistribMulAction M β]
    [SMul M F] [IsZeroApply F α β] [IsAddApply F α β] [IsSMulApply M F α β] :
    DistribMulAction M F :=
  DFunLike.coe_injective.distribMulAction (coeAddMonoidHom F α β) FunLike.coe_smul

variable [Semiring M] [AddCommMonoid β] [Module M β] [AddCommMonoid F] [SMul M F]
  [IsZeroApply F α β] [IsAddApply F α β] [IsSMulApply Nat F α β] [IsSMulApply M F α β]

/--
Definition of `module` / `module` 的定义

English:
abbreviation module
  signature: : Module M F
  body: coeAddHom_injective.module M (coeAddMonoidHom F α β) coe_smul

中文:
缩写 module
  签名: : 模 M F
  定义体: coeAddHom_injective.module M (coeAddMonoidHom F α β) coe_smul
-/
protected abbrev module : Module M F :=
  coeAddHom_injective.module M (coeAddMonoidHom F α β) coe_smul

end ModuleInstance

end FunLike
