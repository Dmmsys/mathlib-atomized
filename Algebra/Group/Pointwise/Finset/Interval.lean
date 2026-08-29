/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Order.Group.Pointwise.Interval
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-! # Pointwise operations on intervals

This should be kept in sync with `Mathlib/Algebra/Order/Group/Pointwise/Interval.lean`.
-/

public section

variable {α : Type*}

namespace Finset

open scoped Pointwise

/-! ### Binary pointwise operations

Note that the subset operations below only cover the cases with the largest possible intervals on
the LHS: to conclude that `Ioo a b * Ioo c d ⊆ Ioo (a * c) (c * d)`, you can use monotonicity of `*`
and `Finset.Ico_mul_Ioc_subset`.

TODO: repeat these lemmas for the generality of `mul_le_mul` (which assumes nonnegativity), which
the unprimed names have been reserved for
-/

section ContravariantLE

variable [Mul α] [Preorder α] [DecidableEq α]
variable [MulLeftMono α] [MulRightMono α]

@[to_additive Icc_add_Icc_subset]
/--
theorem `Icc_mul_Icc_subset'` / 定理 `Icc_mul_Icc_subset'`

English:
theorem Icc_mul_Icc_subset'
  given: [LocallyFiniteOrder α] (a b c d : α)
  proof: Finset.coe_subset.mp by simpa using Set.Icc_mul_Icc_subset' _ _ _ _

@[to_additive Iic_add_Iic_subset]

中文:
定理 Icc_mul_Icc_subset'
  条件: [局部有限序 α] (a b c d : α)
  证明: Finset.coe_subset.mp by simpa using Set.Icc_mul_Icc_subset' _ _ _ _

@[to_additive Iic_add_Iic_subset]

Depends on / 依赖: Finset, Finset.coe_subset.mp, Icc_mul_Icc_subset, Set.Icc_mul_Icc_subset, coe_subset
-/
theorem Icc_mul_Icc_subset' [LocallyFiniteOrder α] (a b c d : α) :
    Icc a b * Icc c d subseteq Icc (a * c) (b * d) :=
Finset.coe_subset.mp by simpa using Set.Icc_mul_Icc_subset' _ _ _ _

@[to_additive Iic_add_Iic_subset]
/--
theorem `Iic_mul_Iic_subset'` / 定理 `Iic_mul_Iic_subset'`

English:
theorem Iic_mul_Iic_subset'
  given: [LocallyFiniteOrderBot α] (a b : α)
  statement: Iic a * Iic b subseteq Iic (a * b)
  proof: Finset.coe_subset.mp by simpa using Set.Iic_mul_Iic_subset' _ _

@[to_additive Ici_add_Ici_subset]

中文:
定理 Iic_mul_Iic_subset'
  条件: [LocallyFiniteOrderBot α] (a b : α)
  结论: 左无界右闭区间 a * 左无界右闭区间 b subseteq 左无界右闭区间 (a * b)
  证明: Finset.coe_subset.mp by simpa using Set.Iic_mul_Iic_subset' _ _

@[to_additive Ici_add_Ici_subset]

Depends on / 依赖: Finset, Finset.coe_subset.mp, Iic_mul_Iic_subset, Set.Iic_mul_Iic_subset, coe_subset
-/
theorem Iic_mul_Iic_subset' [LocallyFiniteOrderBot α] (a b : α) : Iic a * Iic b subseteq Iic (a * b) :=
Finset.coe_subset.mp by simpa using Set.Iic_mul_Iic_subset' _ _

@[to_additive Ici_add_Ici_subset]
/--
theorem `Ici_mul_Ici_subset'` / 定理 `Ici_mul_Ici_subset'`

English:
theorem Ici_mul_Ici_subset'
  given: [LocallyFiniteOrderTop α] (a b : α)
  statement: Ici a * Ici b subseteq Ici (a * b)
  proof: Finset.coe_subset.mp by simpa using Set.Ici_mul_Ici_subset' _ _

中文:
定理 Ici_mul_Ici_subset'
  条件: [LocallyFiniteOrderTop α] (a b : α)
  结论: 左闭右无界区间 a * 左闭右无界区间 b subseteq 左闭右无界区间 (a * b)
  证明: Finset.coe_subset.mp by simpa using Set.Ici_mul_Ici_subset' _ _

Depends on / 依赖: Finset, Finset.coe_subset.mp, Ici_mul_Ici_subset, Set.Ici_mul_Ici_subset, coe_subset
-/
theorem Ici_mul_Ici_subset' [LocallyFiniteOrderTop α] (a b : α) : Ici a * Ici b subseteq Ici (a * b) :=
Finset.coe_subset.mp by simpa using Set.Ici_mul_Ici_subset' _ _

end ContravariantLE

section ContravariantLT

variable [Mul α] [PartialOrder α] [DecidableEq α]
variable [MulLeftStrictMono α] [MulRightStrictMono α]

@[to_additive Icc_add_Ico_subset]
/--
theorem `Icc_mul_Ico_subset'` / 定理 `Icc_mul_Ico_subset'`

English:
theorem Icc_mul_Ico_subset'
  given: [LocallyFiniteOrder α] (a b c d : α)
  proof: Finset.coe_subset.mp by simpa using Set.Icc_mul_Ico_subset' _ _ _ _

@[to_additive Ico_add_Icc_subset]

中文:
定理 Icc_mul_Ico_subset'
  条件: [局部有限序 α] (a b c d : α)
  证明: Finset.coe_subset.mp by simpa using Set.Icc_mul_Ico_subset' _ _ _ _

@[to_additive Ico_add_Icc_subset]

Depends on / 依赖: Finset, Finset.coe_subset.mp, Icc_mul_Ico_subset, Set.Icc_mul_Ico_subset, coe_subset
-/
theorem Icc_mul_Ico_subset' [LocallyFiniteOrder α] (a b c d : α) :
    Icc a b * Ico c d subseteq Ico (a * c) (b * d) :=
Finset.coe_subset.mp by simpa using Set.Icc_mul_Ico_subset' _ _ _ _

@[to_additive Ico_add_Icc_subset]
/--
theorem `Ico_mul_Icc_subset'` / 定理 `Ico_mul_Icc_subset'`

English:
theorem Ico_mul_Icc_subset'
  given: [LocallyFiniteOrder α] (a b c d : α)
  proof: Finset.coe_subset.mp by simpa using Set.Ico_mul_Icc_subset' _ _ _ _

@[to_additive Ioc_add_Ico_subset]

中文:
定理 Ico_mul_Icc_subset'
  条件: [局部有限序 α] (a b c d : α)
  证明: Finset.coe_subset.mp by simpa using Set.Ico_mul_Icc_subset' _ _ _ _

@[to_additive Ioc_add_Ico_subset]

Depends on / 依赖: Finset, Finset.coe_subset.mp, Ico_mul_Icc_subset, Set.Ico_mul_Icc_subset, coe_subset
-/
theorem Ico_mul_Icc_subset' [LocallyFiniteOrder α] (a b c d : α) :
    Ico a b * Icc c d subseteq Ico (a * c) (b * d) :=
Finset.coe_subset.mp by simpa using Set.Ico_mul_Icc_subset' _ _ _ _

@[to_additive Ioc_add_Ico_subset]
/--
theorem `Ioc_mul_Ico_subset'` / 定理 `Ioc_mul_Ico_subset'`

English:
theorem Ioc_mul_Ico_subset'
  given: [LocallyFiniteOrder α] (a b c d : α)
  proof: Finset.coe_subset.mp by simpa using Set.Ioc_mul_Ico_subset' _ _ _ _

@[to_additive Ico_add_Ioc_subset]

中文:
定理 Ioc_mul_Ico_subset'
  条件: [局部有限序 α] (a b c d : α)
  证明: Finset.coe_subset.mp by simpa using Set.Ioc_mul_Ico_subset' _ _ _ _

@[to_additive Ico_add_Ioc_subset]

Depends on / 依赖: Finset, Finset.coe_subset.mp, Ioc_mul_Ico_subset, Set.Ioc_mul_Ico_subset, coe_subset
-/
theorem Ioc_mul_Ico_subset' [LocallyFiniteOrder α] (a b c d : α) :
    Ioc a b * Ico c d subseteq Ioo (a * c) (b * d) :=
Finset.coe_subset.mp by simpa using Set.Ioc_mul_Ico_subset' _ _ _ _

@[to_additive Ico_add_Ioc_subset]
/--
theorem `Ico_mul_Ioc_subset'` / 定理 `Ico_mul_Ioc_subset'`

English:
theorem Ico_mul_Ioc_subset'
  given: [LocallyFiniteOrder α] (a b c d : α)
  proof: Finset.coe_subset.mp by simpa using Set.Ico_mul_Ioc_subset' _ _ _ _

@[to_additive Iic_add_Iio_subset]

中文:
定理 Ico_mul_Ioc_subset'
  条件: [局部有限序 α] (a b c d : α)
  证明: Finset.coe_subset.mp by simpa using Set.Ico_mul_Ioc_subset' _ _ _ _

@[to_additive Iic_add_Iio_subset]

Depends on / 依赖: Finset, Finset.coe_subset.mp, Ico_mul_Ioc_subset, Set.Ico_mul_Ioc_subset, coe_subset
-/
theorem Ico_mul_Ioc_subset' [LocallyFiniteOrder α] (a b c d : α) :
    Ico a b * Ioc c d subseteq Ioo (a * c) (b * d) :=
Finset.coe_subset.mp by simpa using Set.Ico_mul_Ioc_subset' _ _ _ _

@[to_additive Iic_add_Iio_subset]
/--
theorem `Iic_mul_Iio_subset'` / 定理 `Iic_mul_Iio_subset'`

English:
theorem Iic_mul_Iio_subset'
  given: [LocallyFiniteOrderBot α] (a b : α)
  statement: Iic a * Iio b subseteq Iio (a * b)
  proof: Finset.coe_subset.mp by simpa using Set.Iic_mul_Iio_subset' _ _

@[to_additive Iio_add_Iic_subset]

中文:
定理 Iic_mul_Iio_subset'
  条件: [LocallyFiniteOrderBot α] (a b : α)
  结论: 左无界右闭区间 a * 左无界右开区间 b subseteq 左无界右开区间 (a * b)
  证明: Finset.coe_subset.mp by simpa using Set.Iic_mul_Iio_subset' _ _

@[to_additive Iio_add_Iic_subset]

Depends on / 依赖: Finset, Finset.coe_subset.mp, Iic_mul_Iio_subset, Set.Iic_mul_Iio_subset, coe_subset
-/
theorem Iic_mul_Iio_subset' [LocallyFiniteOrderBot α] (a b : α) : Iic a * Iio b subseteq Iio (a * b) :=
Finset.coe_subset.mp by simpa using Set.Iic_mul_Iio_subset' _ _

@[to_additive Iio_add_Iic_subset]
/--
theorem `Iio_mul_Iic_subset'` / 定理 `Iio_mul_Iic_subset'`

English:
theorem Iio_mul_Iic_subset'
  given: [LocallyFiniteOrderBot α] (a b : α)
  statement: Iio a * Iic b subseteq Iio (a * b)
  proof: Finset.coe_subset.mp by simpa using Set.Iio_mul_Iic_subset' _ _

@[to_additive Ioi_add_Ici_subset]

中文:
定理 Iio_mul_Iic_subset'
  条件: [LocallyFiniteOrderBot α] (a b : α)
  结论: 左无界右开区间 a * 左无界右闭区间 b subseteq 左无界右开区间 (a * b)
  证明: Finset.coe_subset.mp by simpa using Set.Iio_mul_Iic_subset' _ _

@[to_additive Ioi_add_Ici_subset]

Depends on / 依赖: Finset, Finset.coe_subset.mp, Iio_mul_Iic_subset, Set.Iio_mul_Iic_subset, coe_subset
-/
theorem Iio_mul_Iic_subset' [LocallyFiniteOrderBot α] (a b : α) : Iio a * Iic b subseteq Iio (a * b) :=
Finset.coe_subset.mp by simpa using Set.Iio_mul_Iic_subset' _ _

@[to_additive Ioi_add_Ici_subset]
/--
theorem `Ioi_mul_Ici_subset'` / 定理 `Ioi_mul_Ici_subset'`

English:
theorem Ioi_mul_Ici_subset'
  given: [LocallyFiniteOrderTop α] (a b : α)
  statement: Ioi a * Ici b subseteq Ioi (a * b)
  proof: Finset.coe_subset.mp by simpa using Set.Ioi_mul_Ici_subset' _ _

@[to_additive Ici_add_Ioi_subset]

中文:
定理 Ioi_mul_Ici_subset'
  条件: [LocallyFiniteOrderTop α] (a b : α)
  结论: 左开右无界区间 a * 左闭右无界区间 b subseteq 左开右无界区间 (a * b)
  证明: Finset.coe_subset.mp by simpa using Set.Ioi_mul_Ici_subset' _ _

@[to_additive Ici_add_Ioi_subset]

Depends on / 依赖: Finset, Finset.coe_subset.mp, Ioi_mul_Ici_subset, Set.Ioi_mul_Ici_subset, coe_subset
-/
theorem Ioi_mul_Ici_subset' [LocallyFiniteOrderTop α] (a b : α) : Ioi a * Ici b subseteq Ioi (a * b) :=
Finset.coe_subset.mp by simpa using Set.Ioi_mul_Ici_subset' _ _

@[to_additive Ici_add_Ioi_subset]
/--
theorem `Ici_mul_Ioi_subset'` / 定理 `Ici_mul_Ioi_subset'`

English:
theorem Ici_mul_Ioi_subset'
  given: [LocallyFiniteOrderTop α] (a b : α)
  statement: Ici a * Ioi b subseteq Ioi (a * b)
  proof: Finset.coe_subset.mp by simpa using Set.Ici_mul_Ioi_subset' _ _

中文:
定理 Ici_mul_Ioi_subset'
  条件: [LocallyFiniteOrderTop α] (a b : α)
  结论: 左闭右无界区间 a * 左开右无界区间 b subseteq 左开右无界区间 (a * b)
  证明: Finset.coe_subset.mp by simpa using Set.Ici_mul_Ioi_subset' _ _

Depends on / 依赖: Finset, Finset.coe_subset.mp, Ici_mul_Ioi_subset, Set.Ici_mul_Ioi_subset, coe_subset
-/
theorem Ici_mul_Ioi_subset' [LocallyFiniteOrderTop α] (a b : α) : Ici a * Ioi b subseteq Ioi (a * b) :=
Finset.coe_subset.mp by simpa using Set.Ici_mul_Ioi_subset' _ _

end ContravariantLT

end Finset
