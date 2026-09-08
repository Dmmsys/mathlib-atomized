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

/-- The decomposition subgroup defined as the stabilizer of the action
on the type of all valuation subrings of the field. -/
/-
**ValuationSubring.decompositionSubgroup** 是 Mathlib 中的一个缩写定义，位于命名空间 `ValuationS
ubring`。
形式化陈述：decompositionSubgroup (A : ValuationSubring L) : Subgroup (L ≃ₐ[K] L)
参数：A : ValuationSubring L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The decomposition subgroup defined as the stabilizer of the action
on the type of all valuation subrings of the field.
-/
abbrev decompositionSubgroup (A : ValuationSubring L) : Subgroup (L ≃ₐ[K] L) :=
  MulAction.stabilizer (L ≃ₐ[K] L) A

/-- The valuation subring `A` (considered as a subset of `L`)
is stable under the action of the decomposition group. -/
/-
**ValuationSubring.subMulAction** 是 Mathlib 中的一个定义，位于命名空间 `ValuationSubring`。
形式化陈述：subMulAction (A : ValuationSubring L) : SubMulAction (A.decompositionSubgr
oup K) L where carrier
参数：A : ValuationSubring L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The valuation subring `A` (considered as a subset of `L`)
is stable under the action of the decomposition group.
-/
def subMulAction (A : ValuationSubring L) : SubMulAction (A.decompositionSubgroup K) L where
  carrier := A
  smul_mem' g _ h := Set.mem_of_mem_of_subset (Set.smul_mem_smul_set h) g.prop.le

/-- The multiplicative action of the decomposition subgroup on `A`. -/
/-
**ValuationSubring.decompositionSubgroupMulSemiringAction** 是 Mathlib 中的一个实例，位于命
名空间 `ValuationSubring`。
形式化陈述：decompositionSubgroupMulSemiringAction (A : ValuationSubring L) : MulSemir
ingAction (A.decompositionSubgroup K) A
参数：A : ValuationSubring L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplicative action of the decomposition subgroup on `A`.
-/
instance decompositionSubgroupMulSemiringAction (A : ValuationSubring L) :
    MulSemiringAction (A.decompositionSubgroup K) A :=
  { SubMulAction.mulAction (A.subMulAction K) with
    smul_add := fun g k l => Subtype.ext <| smul_add (A := L) g k l
    smul_zero := fun g => Subtype.ext <| smul_zero g
    smul_one := fun g => Subtype.ext <| smul_one g
    smul_mul := fun g k l => Subtype.ext <| smul_mul' (N := L) g k l }

/-- The inertia subgroup defined as the kernel of the group homomorphism from
the decomposition subgroup to the group of automorphisms of the residue field of `A`. -/
/-
**ValuationSubring.inertiaSubgroup** 是 Mathlib 中的一个定义，位于命名空间 `ValuationSubring`。
形式化陈述：inertiaSubgroup (A : ValuationSubring L) : Subgroup (A.decompositionSubgro
up K)
参数：A : ValuationSubring L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inertia subgroup defined as the kernel of the group homomorphism from
the decomposition subgroup to the group of automorphisms of the residue field of
 `A`.
-/
noncomputable def inertiaSubgroup (A : ValuationSubring L) : Subgroup (A.decompositionSubgroup K) :=
  MonoidHom.ker <|
    MulSemiringAction.toRingAut (A.decompositionSubgroup K) (IsLocalRing.ResidueField A)

end ValuationSubring

