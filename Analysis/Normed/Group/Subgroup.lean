/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Analysis.Normed.Group.Basic

/-!
# Subgroups of normed (semi)groups

In this file, we prove that subgroups of a normed (semi)group are also normed (semi)groups.

## Tags

normed group
-/

public section


open Filter Function Metric Bornology
open ENNReal Filter NNReal Uniformity Pointwise Topology

/-! ### Subgroups of normed groups -/

variable {E : Type*}

namespace Subgroup

section SeminormedGroup

variable [SeminormedGroup E] {s : Subgroup E}

/-- A subgroup of a seminormed group is also a seminormed group,
with the restriction of the norm. -/
@[to_additive /-- A subgroup of a seminormed group is also a seminormed group, with the restriction
of the norm. -/]
/-
**Subgroup.seminormedGroup** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：seminormedGroup : SeminormedGroup s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance seminormedGroup : SeminormedGroup s :=
  fast_instance% SeminormedGroup.induced _ _ s.subtype

/-- If `x` is an element of a subgroup `s` of a seminormed group `E`, its norm in `s` is equal to
its norm in `E`. -/
@[to_additive (attr := simp) /-- If `x` is an element of a subgroup `s` of a seminormed group `E`,
its norm in `s` is equal to its norm in `E`. -/]
/-
**Subgroup.coe_norm** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：coe_norm (x : s) : ‖x‖ = ‖(x : E)‖
参数：x : s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_norm (x : s) : ‖x‖ = ‖(x : E)‖ :=
  rfl

/-- If `x` is an element of a subgroup `s` of a seminormed group `E`, its norm in `s` is equal to
its norm in `E`.

This is a reversed version of the `simp` lemma `Subgroup.coe_norm` for use by `norm_cast`. -/
@[to_additive (attr := norm_cast) /-- If `x` is an element of a subgroup `s` of a seminormed group
`E`, its norm in `s` is equal to its norm in `E`.

This is a reversed version of the `simp` lemma `AddSubgroup.coe_norm` for use by `norm_cast`. -/]
/-
**Subgroup.norm_coe** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：norm_coe {s : Subgroup E} (x : s) : ‖(x : E)‖ = ‖x‖
参数：x : s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem norm_coe {s : Subgroup E} (x : s) : ‖(x : E)‖ = ‖x‖ :=
  rfl

end SeminormedGroup

@[to_additive]
/-
**Subgroup.seminormedCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：seminormedCommGroup [SeminormedCommGroup E] {s : Subgroup E} : SeminormedC
ommGroup s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance seminormedCommGroup [SeminormedCommGroup E] {s : Subgroup E} : SeminormedCommGroup s :=
  fast_instance% SeminormedCommGroup.induced _ _ s.subtype

@[to_additive]
/-
**Subgroup.normedGroup** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：normedGroup [NormedGroup E] {s : Subgroup E} : NormedGroup s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance normedGroup [NormedGroup E] {s : Subgroup E} : NormedGroup s :=
  fast_instance% NormedGroup.induced _ _ s.subtype Subtype.coe_injective

@[to_additive]
/-
**Subgroup.normedCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `Subgroup`。
形式化陈述：normedCommGroup [NormedCommGroup E] {s : Subgroup E} : NormedCommGroup s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance normedCommGroup [NormedCommGroup E] {s : Subgroup E} : NormedCommGroup s :=
  fast_instance% NormedCommGroup.induced _ _ s.subtype Subtype.coe_injective

end Subgroup

/-! ### Subgroup classes of normed groups -/


namespace SubgroupClass

section SeminormedGroup

variable [SeminormedGroup E] {S : Type*} [SetLike S E] [SubgroupClass S E] (s : S)

/-- A subgroup of a seminormed group is also a seminormed group,
with the restriction of the norm. -/
@[to_additive /-- A subgroup of a seminormed additive group is also a seminormed additive group,
with the restriction of the norm. -/]
/-
**SubgroupClass.** 是 Mathlib 中的一个实例，位于命名空间 `SubgroupClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 75) seminormedGroup : SeminormedGroup s :=
  fast_instance% SeminormedGroup.induced _ _ (SubgroupClass.subtype s)

/-- If `x` is an element of a subgroup `s` of a seminormed group `E`, its norm in `s` is equal to
its norm in `E`. -/
@[to_additive (attr := simp) /-- If `x` is an element of an additive subgroup `s` of a seminormed
additive group `E`, its norm in `s` is equal to its norm in `E`. -/]
/-
**SubgroupClass.coe_norm** 是 Mathlib 中的一个定理，位于命名空间 `SubgroupClass`。
形式化陈述：coe_norm (x : s) : ‖x‖ = ‖(x : E)‖
参数：x : s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_norm (x : s) : ‖x‖ = ‖(x : E)‖ :=
  rfl

end SeminormedGroup

@[to_additive]
/-
**SubgroupClass.** 是 Mathlib 中的一个实例，位于命名空间 `SubgroupClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 75) seminormedCommGroup [SeminormedCommGroup E] {S : Type*} [SetLike S E]
    [SubgroupClass S E] (s : S) : SeminormedCommGroup s :=
  fast_instance% SeminormedCommGroup.induced _ _ (SubgroupClass.subtype s)

@[to_additive]
/-
**SubgroupClass.** 是 Mathlib 中的一个实例，位于命名空间 `SubgroupClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 75) normedGroup [NormedGroup E] {S : Type*} [SetLike S E] [SubgroupClass S E]
    (s : S) : NormedGroup s :=
  fast_instance% NormedGroup.induced _ _ (SubgroupClass.subtype s) Subtype.coe_injective

@[to_additive]
/-
**SubgroupClass.** 是 Mathlib 中的一个实例，位于命名空间 `SubgroupClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 75) normedCommGroup [NormedCommGroup E] {S : Type*} [SetLike S E]
    [SubgroupClass S E] (s : S) : NormedCommGroup s :=
  fast_instance% NormedCommGroup.induced _ _ (SubgroupClass.subtype s) Subtype.coe_injective

end SubgroupClass

