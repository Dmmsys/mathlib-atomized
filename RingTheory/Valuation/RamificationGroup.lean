/-
Copyright (c) 2022 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Ramification groups

The decomposition subgroup and inertia subgroups.

TODO: Define higher ramification groups in lower numbering
-/

@[expose] public section


namespace ValuationSubring

open scoped Pointwise

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]

/--
Definition of `decompositionSubgroup` / `decompositionSubgroup` 的定义

English:
abbreviation decompositionSubgroup
  signature: (A : ValuationSubring L)
  body: MulAction.stabilizer (L ≃ₐ[K] L) A

中文:
缩写 decompositionSubgroup
  签名: (A : 赋值子环 L)
  定义体: MulAction.stabilizer (L ≃ₐ[K] L) A

Depends on / 依赖: MulAction, MulAction.stabilizer, stabilizer
-/
abbrev decompositionSubgroup (A : ValuationSubring L) : Subgroup (L ≃ₐ[K] L) :=
  MulAction.stabilizer (L ≃ₐ[K] L) A

/--
Definition of `subMulAction` / `subMulAction` 的定义

English:
definition subMulAction
  signature: (A : ValuationSubring L)
  body: A
  smul_mem' g _ h := Set.mem_of_mem_of_subset (Set.smul_mem_smul_set h) g.prop.le

中文:
定义 subMulAction
  签名: (A : 赋值子环 L)
  定义体: A
  smul_mem' g _ h := Set.mem_of_mem_of_subset (Set.smul_mem_smul_set h) g.prop.le
-/
def subMulAction (A : ValuationSubring L) : SubMulAction (A.decompositionSubgroup K) L where
  carrier := A
  smul_mem' g _ h := Set.mem_of_mem_of_subset (Set.smul_mem_smul_set h) g.prop.le

/--
Instance `decompositionSubgroupMulSemiringAction` / 实例 `decompositionSubgroupMulSemiringAction`

English:
instance decompositionSubgroupMulSemiringAction
  signature: (A : ValuationSubring L)
  body: { SubMulAction.mulAction (A.subMulAction K) with
smul_add := fun g k l => Subtype.ext smul_add (A := L) g k l
smul_zero := fun g => Subtype.ext smul_zero g
smul_one := fun g => Subtype.ext smul_one g
smul_mul := fun g k l => Subtype.ext smul_mul' (N := L) g k l }

中文:
实例 decompositionSubgroupMulSemiringAction
  签名: (A : 赋值子环 L)
  定义体: { SubMulAction.mulAction (A.subMulAction K) with
smul_add := fun g k l => Subtype.ext smul_add (A := L) g k l
smul_zero := fun g => Subtype.ext smul_zero g
smul_one := fun g => Subtype.ext smul_one g
smul_mul := fun g k l => Subtype.ext smul_mul' (N := L) g k l }

Depends on / 依赖: A.subMulAction, SubMulAction, SubMulAction.mulAction, Subtype, Subtype.ext, mulAction, smul_add, smul_mul, smul_one, smul_zero, subMulAction
-/
instance decompositionSubgroupMulSemiringAction (A : ValuationSubring L) :
    MulSemiringAction (A.decompositionSubgroup K) A :=
  { SubMulAction.mulAction (A.subMulAction K) with
smul_add := fun g k l => Subtype.ext smul_add (A := L) g k l
smul_zero := fun g => Subtype.ext smul_zero g
smul_one := fun g => Subtype.ext smul_one g
smul_mul := fun g k l => Subtype.ext smul_mul' (N := L) g k l }

/--
Definition of `inertiaSubgroup` / `inertiaSubgroup` 的定义

English:
definition inertiaSubgroup
  signature: (A : ValuationSubring L)
  body: MonoidHom.ker
    MulSemiringAction.toRingAut (A.decompositionSubgroup K) (IsLocalRing.ResidueField A)

中文:
定义 inertiaSubgroup
  签名: (A : 赋值子环 L)
  定义体: MonoidHom.ker
    MulSemiringAction.toRingAut (A.decompositionSubgroup K) (IsLocalRing.ResidueField A)

Depends on / 依赖: A.decompositionSubgroup, EMetricSpace, IsLocalRing, IsLocalRing.ResidueField, MonoidHom, MonoidHom.ker, MulSemiringAction, MulSemiringAction.toRingAut, Nontrivial, NontrivialTopology, ResidueField, decompositionSubgroup, toRingAut
-/
noncomputable def inertiaSubgroup (A : ValuationSubring L) : Subgroup (A.decompositionSubgroup K) :=
MonoidHom.ker
    MulSemiringAction.toRingAut (A.decompositionSubgroup K) (IsLocalRing.ResidueField A)

end ValuationSubring
