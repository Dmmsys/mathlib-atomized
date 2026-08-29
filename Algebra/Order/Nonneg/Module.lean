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

local notation3 "R>=0" => {c : R // 0 <= c}

namespace Nonneg
variable [Semiring R] [PartialOrder R]

section SMul

variable [SMul R S]

/--
Instance `instSMul` / 实例 `instSMul`

English:
instance instSMul
  signature: : SMul R>=0 S where
  body: c.val • x

@[simp, norm_cast]

中文:
实例 instSMul
  签名: : SMul R>=0 S where
  定义体: c.val • x

@[simp, norm_cast]

Depends on / 依赖: c.val
-/
instance instSMul : SMul R>=0 S where
  smul c x := c.val • x

@[simp, norm_cast]
/--
lemma `coe_smul` / 引理 `coe_smul`

English:
lemma coe_smul
  given: (a : R>=0) (x : S)
  statement: (a : R) • x = a • x
  proof: rfl

@[simp]

中文:
引理 coe_smul
  条件: (a : R>=0) (x : S)
  结论: (a : R) • x = a • x
  证明: rfl

@[simp]
-/
lemma coe_smul (a : R>=0) (x : S) : (a : R) • x = a • x :=
  rfl

@[simp]
/--
lemma `mk_smul` / 引理 `mk_smul`

English:
lemma mk_smul
  given: (a) (ha) (x : S)
  statement: (⟨a, ha⟩ : R>=0) • x = a • x
  proof: rfl

中文:
引理 mk_smul
  条件: (a) (ha) (x : S)
  结论: (⟨a, ha⟩ : R>=0) • x = a • x
  证明: rfl
-/
lemma mk_smul (a) (ha) (x : S) : (⟨a, ha⟩ : R>=0) • x = a • x :=
  rfl

end SMul

section IsScalarTower

variable [IsOrderedRing R] [SMul R S] [SMul R M] [SMul S M] [IsScalarTower R S M]

/--
Instance `instIsScalarTower` / 实例 `instIsScalarTower`

English:
instance instIsScalarTower
  signature: : IsScalarTower R>=0 S M
  body: SMul.comp.isScalarTower ↑Nonneg.coeRingHom

中文:
实例 instIsScalarTower
  签名: : IsScalarTower R>=0 S M
  定义体: SMul.comp.isScalarTower ↑Nonneg.coeRingHom

Depends on / 依赖: Nonneg, Nonneg.coeRingHom, SMul.comp.isScalarTower, coeRingHom, isScalarTower
-/
instance instIsScalarTower : IsScalarTower R>=0 S M :=
  SMul.comp.isScalarTower ↑Nonneg.coeRingHom

end IsScalarTower

section SMulWithZero

variable [Zero S] [SMulWithZero R S]

/--
Instance `instSMulWithZero` / 实例 `instSMulWithZero`

English:
instance instSMulWithZero
  signature: : SMulWithZero R>=0 S where
  body: smul_zero _
  zero_smul _ := zero_smul _ _

中文:
实例 instSMulWithZero
  签名: : SMulWithZero R>=0 S where
  定义体: smul_zero _
  zero_smul _ := zero_smul _ _

Depends on / 依赖: smul_zero
-/
instance instSMulWithZero : SMulWithZero R>=0 S where
  smul_zero _ := smul_zero _
  zero_smul _ := zero_smul _ _

end SMulWithZero

section IsOrderedModule

variable [IsOrderedRing R] [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
  [SMulWithZero R M]

/--
Instance `instIsOrderedModule` / 实例 `instIsOrderedModule`

English:
instance instIsOrderedModule
  signature: [hM : IsOrderedModule R M]
  body: hM.smul_le_smul_of_nonneg_left hb ha
  smul_le_smul_of_nonneg_right _b hb _a₁ _a₂ ha := hM.smul_le_smul_of_nonneg_right hb ha

中文:
实例 instIsOrderedModule
  签名: [hM : IsOrderedModule R M]
  定义体: hM.smul_le_smul_of_nonneg_left hb ha
  smul_le_smul_of_nonneg_right _b hb _a₁ _a₂ ha := hM.smul_le_smul_of_nonneg_right hb ha

Depends on / 依赖: hM.smul_le_smul_of_nonneg_left, smul_le_smul_of_nonneg_left
-/
instance instIsOrderedModule [hM : IsOrderedModule R M] : IsOrderedModule R>=0 M where
  smul_le_smul_of_nonneg_left _b hb _a₁ _a₂ ha := hM.smul_le_smul_of_nonneg_left hb ha
  smul_le_smul_of_nonneg_right _b hb _a₁ _a₂ ha := hM.smul_le_smul_of_nonneg_right hb ha

/--
Instance `instIsStrictOrderedModule` / 实例 `instIsStrictOrderedModule`

English:
instance instIsStrictOrderedModule
  signature: [hM : IsStrictOrderedModule R M]
  body: hM.smul_lt_smul_of_pos_left hb ha
  smul_lt_smul_of_pos_right _b hb _a₁ _a₂ ha := hM.smul_lt_smul_of_pos_right hb ha

中文:
实例 instIsStrictOrderedModule
  签名: [hM : IsStrictOrderedModule R M]
  定义体: hM.smul_lt_smul_of_pos_left hb ha
  smul_lt_smul_of_pos_right _b hb _a₁ _a₂ ha := hM.smul_lt_smul_of_pos_right hb ha

Depends on / 依赖: hM.smul_lt_smul_of_pos_left, smul_lt_smul_of_pos_left
-/
instance instIsStrictOrderedModule [hM : IsStrictOrderedModule R M] :
    IsStrictOrderedModule R>=0 M where
  smul_lt_smul_of_pos_left _b hb _a₁ _a₂ ha := hM.smul_lt_smul_of_pos_left hb ha
  smul_lt_smul_of_pos_right _b hb _a₁ _a₂ ha := hM.smul_lt_smul_of_pos_right hb ha

end IsOrderedModule

section Module

variable [IsOrderedRing R] [AddCommMonoid M] [Module R M]

/--
Instance `instModule` / 实例 `instModule`

English:
instance instModule
  signature: : Module R>=0 M where
  body: instSMul.smul
  __ := Module.compHom M coeRingHom

中文:
实例 instModule
  签名: : Module R>=0 M where
  定义体: instSMul.smul
  __ := Module.compHom M coeRingHom

Depends on / 依赖: instSMul, instSMul.smul
-/
instance instModule : Module R>=0 M where
  smul := instSMul.smul
  __ := Module.compHom M coeRingHom

end Module
end Nonneg
