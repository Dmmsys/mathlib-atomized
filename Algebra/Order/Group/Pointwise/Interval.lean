/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Patrick Massot
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Group.MinMax
public import Mathlib.Algebra.Order.Interval.Set.Monoid
public import Mathlib.Order.Interval.Set.OrderIso
public import Mathlib.Order.Interval.Set.UnorderedInterval
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# (Pre)images of intervals

In this file we prove a bunch of trivial lemmas like “if we add `a` to all points of `[b, c]`,
then we get `[a + b, a + c]`”. For the functions `x ↦ x ± a`, `x ↦ a ± x`, and `x ↦ -x` we prove
lemmas about preimages and images of all intervals. We also prove a few lemmas about images under
`x ↦ a * x`, `x ↦ x * a` and `x ↦ x⁻¹`.
-/

public section


open Interval Pointwise

variable {α : Type*}

namespace Set

/-! ### Binary pointwise operations

Note that the subset operations below only cover the cases with the largest possible intervals on
the LHS: to conclude that `Ioo a b * Ioo c d ⊆ Ioo (a * c) (c * d)`, you can use monotonicity of `*`
and `Set.Ico_mul_Ioc_subset`.

TODO: repeat these lemmas for the generality of `mul_le_mul` (which assumes nonnegativity), which
the unprimed names have been reserved for
-/

section ContravariantLE

variable [Mul α] [Preorder α] [MulLeftMono α] [MulRightMono α]

@[to_additive Icc_add_Icc_subset]
/--
theorem `Icc_mul_Icc_subset'` / 定理 `Icc_mul_Icc_subset'`

English:
theorem Icc_mul_Icc_subset'
  given: (a b c d : α)
  statement: Icc a b * Icc c d subseteq Icc (a * c) (b * d)
  proof: by
  rintro x ⟨y, ⟨hya, hyb⟩, z, ⟨hzc, hzd⟩, rfl⟩
  exact ⟨mul_le_mul' hya hzc, mul_le_mul' hyb hzd⟩

@[to_additive Iic_add_Iic_subset]

中文:
定理 Icc_mul_Icc_subset'
  条件: (a b c d : α)
  结论: Icc a b * Icc c d subseteq Icc (a * c) (b * d)
  证明: by
  rintro x ⟨y, ⟨hya, hyb⟩, z, ⟨hzc, hzd⟩, rfl⟩
  exact ⟨mul_le_mul' hya hzc, mul_le_mul' hyb hzd⟩

@[to_additive Iic_add_Iic_subset]

Depends on / 依赖: mul_le_mul
-/
theorem Icc_mul_Icc_subset' (a b c d : α) : Icc a b * Icc c d subseteq Icc (a * c) (b * d) := by
  rintro x ⟨y, ⟨hya, hyb⟩, z, ⟨hzc, hzd⟩, rfl⟩
  exact ⟨mul_le_mul' hya hzc, mul_le_mul' hyb hzd⟩

@[to_additive Iic_add_Iic_subset]
/--
theorem `Iic_mul_Iic_subset'` / 定理 `Iic_mul_Iic_subset'`

English:
theorem Iic_mul_Iic_subset'
  given: (a b : α)
  statement: Iic a * Iic b subseteq Iic (a * b)
  proof: by
  rintro x ⟨y, hya, z, hzb, rfl⟩
  exact mul_le_mul' hya hzb

@[to_additive Ici_add_Ici_subset]

中文:
定理 Iic_mul_Iic_subset'
  条件: (a b : α)
  结论: Iic a * Iic b subseteq Iic (a * b)
  证明: by
  rintro x ⟨y, hya, z, hzb, rfl⟩
  exact mul_le_mul' hya hzb

@[to_additive Ici_add_Ici_subset]

Depends on / 依赖: mul_le_mul
-/
theorem Iic_mul_Iic_subset' (a b : α) : Iic a * Iic b subseteq Iic (a * b) := by
  rintro x ⟨y, hya, z, hzb, rfl⟩
  exact mul_le_mul' hya hzb

@[to_additive Ici_add_Ici_subset]
/--
theorem `Ici_mul_Ici_subset'` / 定理 `Ici_mul_Ici_subset'`

English:
theorem Ici_mul_Ici_subset'
  given: (a b : α)
  statement: Ici a * Ici b subseteq Ici (a * b)
  proof: by
  rintro x ⟨y, hya, z, hzb, rfl⟩
  exact mul_le_mul' hya hzb

中文:
定理 Ici_mul_Ici_subset'
  条件: (a b : α)
  结论: Ici a * Ici b subseteq Ici (a * b)
  证明: by
  rintro x ⟨y, hya, z, hzb, rfl⟩
  exact mul_le_mul' hya hzb

Depends on / 依赖: mul_le_mul
-/
theorem Ici_mul_Ici_subset' (a b : α) : Ici a * Ici b subseteq Ici (a * b) := by
  rintro x ⟨y, hya, z, hzb, rfl⟩
  exact mul_le_mul' hya hzb

end ContravariantLE

section ContravariantLT

variable [Mul α] [PartialOrder α] [MulLeftStrictMono α] [MulRightStrictMono α]

@[to_additive Icc_add_Ico_subset]
/--
theorem `Icc_mul_Ico_subset'` / 定理 `Icc_mul_Ico_subset'`

English:
theorem Icc_mul_Ico_subset'
  given: (a b c d : α)
  statement: Icc a b * Ico c d subseteq Ico (a * c) (b * d)
  proof: by
  have := mulLeftMono_of_mulLeftStrictMono α
  have := mulRightMono_of_mulRightStrictMono α
  rintro x ⟨y, ⟨hya, hyb⟩, z, ⟨hzc, hzd⟩, rfl⟩
  exact ⟨mul_le_mul' hya hzc, mul_lt_mul_of_le_of_lt hyb hzd⟩

@[to_additive Ico_add_Icc_subset]

中文:
定理 Icc_mul_Ico_subset'
  条件: (a b c d : α)
  结论: Icc a b * Ico c d subseteq Ico (a * c) (b * d)
  证明: by
  have := mulLeftMono_of_mulLeftStrictMono α
  have := mulRightMono_of_mulRightStrictMono α
  rintro x ⟨y, ⟨hya, hyb⟩, z, ⟨hzc, hzd⟩, rfl⟩
  exact ⟨mul_le_mul' hya hzc, mul_lt_mul_of_le_of_lt hyb hzd⟩

@[to_additive Ico_add_Icc_subset]

Depends on / 依赖: mulLeftMono_of_mulLeftStrictMono, mulRightMono_of_mulRightStrictMono, mul_le_mul, mul_lt_mul_of_le_of_lt
-/
theorem Icc_mul_Ico_subset' (a b c d : α) : Icc a b * Ico c d subseteq Ico (a * c) (b * d) := by
  have := mulLeftMono_of_mulLeftStrictMono α
  have := mulRightMono_of_mulRightStrictMono α
  rintro x ⟨y, ⟨hya, hyb⟩, z, ⟨hzc, hzd⟩, rfl⟩
  exact ⟨mul_le_mul' hya hzc, mul_lt_mul_of_le_of_lt hyb hzd⟩

@[to_additive Ico_add_Icc_subset]
/--
theorem `Ico_mul_Icc_subset'` / 定理 `Ico_mul_Icc_subset'`

English:
theorem Ico_mul_Icc_subset'
  given: (a b c d : α)
  statement: Ico a b * Icc c d subseteq Ico (a * c) (b * d)
  proof: by
  have := mulLeftMono_of_mulLeftStrictMono α
  have := mulRightMono_of_mulRightStrictMono α
  rintro x ⟨y, ⟨hya, hyb⟩, z, ⟨hzc, hzd⟩, rfl⟩
  exact ⟨mul_le_mul' hya hzc, mul_lt_mul_of_lt_of_le hyb hzd⟩

@[to_additive Ioc_add_Ico_subset]

中文:
定理 Ico_mul_Icc_subset'
  条件: (a b c d : α)
  结论: Ico a b * Icc c d subseteq Ico (a * c) (b * d)
  证明: by
  have := mulLeftMono_of_mulLeftStrictMono α
  have := mulRightMono_of_mulRightStrictMono α
  rintro x ⟨y, ⟨hya, hyb⟩, z, ⟨hzc, hzd⟩, rfl⟩
  exact ⟨mul_le_mul' hya hzc, mul_lt_mul_of_lt_of_le hyb hzd⟩

@[to_additive Ioc_add_Ico_subset]

Depends on / 依赖: PosSMulStrictMono, PosSMulStrictMono.toPosSMulMono, mulLeftMono_of_mulLeftStrictMono, mulRightMono_of_mulRightStrictMono, mul_le_mul, mul_lt_mul_of_lt_of_le, toPosSMulMono
-/
theorem Ico_mul_Icc_subset' (a b c d : α) : Ico a b * Icc c d subseteq Ico (a * c) (b * d) := by
  have := mulLeftMono_of_mulLeftStrictMono α
  have := mulRightMono_of_mulRightStrictMono α
  rintro x ⟨y, ⟨hya, hyb⟩, z, ⟨hzc, hzd⟩, rfl⟩
  exact ⟨mul_le_mul' hya hzc, mul_lt_mul_of_lt_of_le hyb hzd⟩

@[to_additive Ioc_add_Ico_subset]
/--
theorem `Ioc_mul_Ico_subset'` / 定理 `Ioc_mul_Ico_subset'`

English:
theorem Ioc_mul_Ico_subset'
  given: (a b c d : α)
  statement: Ioc a b * Ico c d subseteq Ioo (a * c) (b * d)
  proof: by
  have := mulLeftMono_of_mulLeftStrictMono α
  have := mulRightMono_of_mulRightStrictMono α
  rintro x ⟨y, ⟨hya, hyb⟩, z, ⟨hzc, hzd⟩, rfl⟩
  exact ⟨mul_lt_mul_of_lt_of_le hya hzc, mul_lt_mul_of_le_of_lt hyb hzd⟩

@[to_additive Ico_add_Ioc_subset]

中文:
定理 Ioc_mul_Ico_subset'
  条件: (a b c d : α)
  结论: Ioc a b * Ico c d subseteq Ioo (a * c) (b * d)
  证明: by
  have := mulLeftMono_of_mulLeftStrictMono α
  have := mulRightMono_of_mulRightStrictMono α
  rintro x ⟨y, ⟨hya, hyb⟩, z, ⟨hzc, hzd⟩, rfl⟩
  exact ⟨mul_lt_mul_of_lt_of_le hya hzc, mul_lt_mul_of_le_of_lt hyb hzd⟩

@[to_additive Ico_add_Ioc_subset]

Depends on / 依赖: SMulPosStrictMono, SMulPosStrictMono.toSMulPosMono, mulLeftMono_of_mulLeftStrictMono, mulRightMono_of_mulRightStrictMono, mul_lt_mul_of_le_of_lt, mul_lt_mul_of_lt_of_le, toSMulPosMono
-/
theorem Ioc_mul_Ico_subset' (a b c d : α) : Ioc a b * Ico c d subseteq Ioo (a * c) (b * d) := by
  have := mulLeftMono_of_mulLeftStrictMono α
  have := mulRightMono_of_mulRightStrictMono α
  rintro x ⟨y, ⟨hya, hyb⟩, z, ⟨hzc, hzd⟩, rfl⟩
  exact ⟨mul_lt_mul_of_lt_of_le hya hzc, mul_lt_mul_of_le_of_lt hyb hzd⟩

@[to_additive Ico_add_Ioc_subset]
/--
theorem `Ico_mul_Ioc_subset'` / 定理 `Ico_mul_Ioc_subset'`

English:
theorem Ico_mul_Ioc_subset'
  given: (a b c d : α)
  statement: Ico a b * Ioc c d subseteq Ioo (a * c) (b * d)
  proof: by
  have := mulLeftMono_of_mulLeftStrictMono α
  have := mulRightMono_of_mulRightStrictMono α
  rintro x ⟨y, ⟨hya, hyb⟩, z, ⟨hzc, hzd⟩, rfl⟩
  exact ⟨mul_lt_mul_of_le_of_lt hya hzc, mul_lt_mul_of_lt_of_le hyb hzd⟩

@[to_additive Iic_add_Iio_subset]

中文:
定理 Ico_mul_Ioc_subset'
  条件: (a b c d : α)
  结论: Ico a b * Ioc c d subseteq Ioo (a * c) (b * d)
  证明: by
  have := mulLeftMono_of_mulLeftStrictMono α
  have := mulRightMono_of_mulRightStrictMono α
  rintro x ⟨y, ⟨hya, hyb⟩, z, ⟨hzc, hzd⟩, rfl⟩
  exact ⟨mul_lt_mul_of_le_of_lt hya hzc, mul_lt_mul_of_lt_of_le hyb hzd⟩

@[to_additive Iic_add_Iio_subset]

Depends on / 依赖: PosSMulReflectLE, PosSMulReflectLE.toPosSMulReflectLT, mulLeftMono_of_mulLeftStrictMono, mulRightMono_of_mulRightStrictMono, mul_lt_mul_of_le_of_lt, mul_lt_mul_of_lt_of_le, toPosSMulReflectLT
-/
theorem Ico_mul_Ioc_subset' (a b c d : α) : Ico a b * Ioc c d subseteq Ioo (a * c) (b * d) := by
  have := mulLeftMono_of_mulLeftStrictMono α
  have := mulRightMono_of_mulRightStrictMono α
  rintro x ⟨y, ⟨hya, hyb⟩, z, ⟨hzc, hzd⟩, rfl⟩
  exact ⟨mul_lt_mul_of_le_of_lt hya hzc, mul_lt_mul_of_lt_of_le hyb hzd⟩

@[to_additive Iic_add_Iio_subset]
/--
theorem `Iic_mul_Iio_subset'` / 定理 `Iic_mul_Iio_subset'`

English:
theorem Iic_mul_Iio_subset'
  given: (a b : α)
  statement: Iic a * Iio b subseteq Iio (a * b)
  proof: by
  have := mulRightMono_of_mulRightStrictMono α
  rintro x ⟨y, hya, z, hzb, rfl⟩
  exact mul_lt_mul_of_le_of_lt hya hzb

@[to_additive Iio_add_Iic_subset]

中文:
定理 Iic_mul_Iio_subset'
  条件: (a b : α)
  结论: Iic a * Iio b subseteq Iio (a * b)
  证明: by
  have := mulRightMono_of_mulRightStrictMono α
  rintro x ⟨y, hya, z, hzb, rfl⟩
  exact mul_lt_mul_of_le_of_lt hya hzb

@[to_additive Iio_add_Iic_subset]

Depends on / 依赖: SMulPosReflectLE, SMulPosReflectLE.toSMulPosReflectLT, mulRightMono_of_mulRightStrictMono, mul_lt_mul_of_le_of_lt, toSMulPosReflectLT
-/
theorem Iic_mul_Iio_subset' (a b : α) : Iic a * Iio b subseteq Iio (a * b) := by
  have := mulRightMono_of_mulRightStrictMono α
  rintro x ⟨y, hya, z, hzb, rfl⟩
  exact mul_lt_mul_of_le_of_lt hya hzb

@[to_additive Iio_add_Iic_subset]
/--
theorem `Iio_mul_Iic_subset'` / 定理 `Iio_mul_Iic_subset'`

English:
theorem Iio_mul_Iic_subset'
  given: (a b : α)
  statement: Iio a * Iic b subseteq Iio (a * b)
  proof: by
  have := mulLeftMono_of_mulLeftStrictMono α
  rintro x ⟨y, hya, z, hzb, rfl⟩
  exact mul_lt_mul_of_lt_of_le hya hzb

@[to_additive Ioi_add_Ici_subset]

中文:
定理 Iio_mul_Iic_subset'
  条件: (a b : α)
  结论: Iio a * Iic b subseteq Iio (a * b)
  证明: by
  have := mulLeftMono_of_mulLeftStrictMono α
  rintro x ⟨y, hya, z, hzb, rfl⟩
  exact mul_lt_mul_of_lt_of_le hya hzb

@[to_additive Ioi_add_Ici_subset]

Depends on / 依赖: IsStrictOrderedModule, IsStrictOrderedModule.toIsOrderedModule, mulLeftMono_of_mulLeftStrictMono, mul_lt_mul_of_lt_of_le, toIsOrderedModule
-/
theorem Iio_mul_Iic_subset' (a b : α) : Iio a * Iic b subseteq Iio (a * b) := by
  have := mulLeftMono_of_mulLeftStrictMono α
  rintro x ⟨y, hya, z, hzb, rfl⟩
  exact mul_lt_mul_of_lt_of_le hya hzb

@[to_additive Ioi_add_Ici_subset]
/--
theorem `Ioi_mul_Ici_subset'` / 定理 `Ioi_mul_Ici_subset'`

English:
theorem Ioi_mul_Ici_subset'
  given: (a b : α)
  statement: Ioi a * Ici b subseteq Ioi (a * b)
  proof: by
  have := mulLeftMono_of_mulLeftStrictMono α
  rintro x ⟨y, hya, z, hzb, rfl⟩
  exact mul_lt_mul_of_lt_of_le hya hzb

@[to_additive Ici_add_Ioi_subset]

中文:
定理 Ioi_mul_Ici_subset'
  条件: (a b : α)
  结论: Ioi a * Ici b subseteq Ioi (a * b)
  证明: by
  have := mulLeftMono_of_mulLeftStrictMono α
  rintro x ⟨y, hya, z, hzb, rfl⟩
  exact mul_lt_mul_of_lt_of_le hya hzb

@[to_additive Ici_add_Ioi_subset]

Depends on / 依赖: mulLeftMono_of_mulLeftStrictMono, mul_lt_mul_of_lt_of_le
-/
theorem Ioi_mul_Ici_subset' (a b : α) : Ioi a * Ici b subseteq Ioi (a * b) := by
  have := mulLeftMono_of_mulLeftStrictMono α
  rintro x ⟨y, hya, z, hzb, rfl⟩
  exact mul_lt_mul_of_lt_of_le hya hzb

@[to_additive Ici_add_Ioi_subset]
/--
theorem `Ici_mul_Ioi_subset'` / 定理 `Ici_mul_Ioi_subset'`

English:
theorem Ici_mul_Ioi_subset'
  given: (a b : α)
  statement: Ici a * Ioi b subseteq Ioi (a * b)
  proof: by
  have := mulRightMono_of_mulRightStrictMono α
  rintro x ⟨y, hya, z, hzb, rfl⟩
  exact mul_lt_mul_of_le_of_lt hya hzb

中文:
定理 Ici_mul_Ioi_subset'
  条件: (a b : α)
  结论: Ici a * Ioi b subseteq Ioi (a * b)
  证明: by
  have := mulRightMono_of_mulRightStrictMono α
  rintro x ⟨y, hya, z, hzb, rfl⟩
  exact mul_lt_mul_of_le_of_lt hya hzb

Depends on / 依赖: mulRightMono_of_mulRightStrictMono, mul_lt_mul_of_le_of_lt
-/
theorem Ici_mul_Ioi_subset' (a b : α) : Ici a * Ioi b subseteq Ioi (a * b) := by
  have := mulRightMono_of_mulRightStrictMono α
  rintro x ⟨y, hya, z, hzb, rfl⟩
  exact mul_lt_mul_of_le_of_lt hya hzb

end ContravariantLT

section LinearOrderedCommMonoid
variable [CommMonoid α] [LinearOrder α] [IsOrderedMonoid α] [MulLeftReflectLE α] [ExistsMulOfLE α]
  {a b c d : α}

-- TODO: Generalise to arbitrary actions using a `smul` version of `MulLeftMono`
@[to_additive (attr := simp)]
/--
lemma `smul_Icc` / 引理 `smul_Icc`

English:
lemma smul_Icc
  given: (a b c : α)
  statement: a • Icc b c = Icc (a * b) (a * c)
  proof: by
  ext x
  constructor
  · rintro ⟨y, ⟨hby, hyc⟩, rfl⟩
    dsimp
    constructor <;> gcongr
  · rintro ⟨habx, hxac⟩
    obtain ⟨y, hy, rfl⟩ := exists_one_le_mul_of_le habx
    refine ⟨b * y, ⟨le_mul_of_one_le_right' hy, ?_⟩, (mul_assoc ..).symm⟩
    rwa [mul_assoc, mul_le_mul_iff_left] at hxac

@[

中文:
引理 smul_Icc
  条件: (a b c : α)
  结论: a • Icc b c = Icc (a * b) (a * c)
  证明: by
  ext x
  constructor
  · rintro ⟨y, ⟨hby, hyc⟩, rfl⟩
    dsimp
    constructor <;> gcongr
  · rintro ⟨habx, hxac⟩
    obtain ⟨y, hy, rfl⟩ := exists_one_le_mul_of_le habx
    refine ⟨b * y, ⟨le_mul_of_one_le_right' hy, ?_⟩, (mul_assoc ..).symm⟩
    rwa [mul_assoc, mul_le_mul_iff_left] at hxac

@[

Depends on / 依赖: exists_one_le_mul_of_le, le_mul_of_one_le_right, mul_assoc, mul_le_mul_iff_left
-/
lemma smul_Icc (a b c : α) : a • Icc b c = Icc (a * b) (a * c) := by
  ext x
  constructor
  · rintro ⟨y, ⟨hby, hyc⟩, rfl⟩
    dsimp
    constructor <;> gcongr
  · rintro ⟨habx, hxac⟩
    obtain ⟨y, hy, rfl⟩ := exists_one_le_mul_of_le habx
    refine ⟨b * y, ⟨le_mul_of_one_le_right' hy, ?_⟩, (mul_assoc ..).symm⟩
    rwa [mul_assoc, mul_le_mul_iff_left] at hxac

@[to_additive]
/--
lemma `Icc_mul_Icc` / 引理 `Icc_mul_Icc`

English:
lemma Icc_mul_Icc
  given: (hab : a <= b) (hcd : c <= d)
  statement: Icc a b * Icc c d = Icc (a * c) (b * d)
  proof: by
  refine (Icc_mul_Icc_subset' _ _ _ _).antisymm fun x ⟨hacx, hxbd⟩ => ?_
  obtain hxbc | hbcx := le_total x (b * c)
  · obtain ⟨y, hy, rfl⟩ := exists_one_le_mul_of_le hacx
    refine ⟨a * y, ⟨le_mul_of_one_le_right' hy, ?_⟩, c, left_mem_Icc.2 hcd, mul_right_comm ..⟩
    rwa [mul_right_comm, mul_l

中文:
引理 Icc_mul_Icc
  条件: (hab : a <= b) (hcd : c <= d)
  结论: Icc a b * Icc c d = Icc (a * c) (b * d)
  证明: by
  refine (Icc_mul_Icc_subset' _ _ _ _).antisymm fun x ⟨hacx, hxbd⟩ => ?_
  obtain hxbc | hbcx := le_total x (b * c)
  · obtain ⟨y, hy, rfl⟩ := exists_one_le_mul_of_le hacx
    refine ⟨a * y, ⟨le_mul_of_one_le_right' hy, ?_⟩, c, left_mem_Icc.2 hcd, mul_right_comm ..⟩
    rwa [mul_right_comm, mul_l

Depends on / 依赖: Icc_mul_Icc_subset, antisymm, exists_one_le_mul_of_le, le_mul_of_one_le_right, le_total, left_mem_Icc, mul_assoc, mul_le_mul_iff_left, mul_le_mul_iff_right, mul_right_comm, right_mem_Icc
-/
lemma Icc_mul_Icc (hab : a <= b) (hcd : c <= d) : Icc a b * Icc c d = Icc (a * c) (b * d) := by
  refine (Icc_mul_Icc_subset' _ _ _ _).antisymm fun x ⟨hacx, hxbd⟩ => ?_
  obtain hxbc | hbcx := le_total x (b * c)
  · obtain ⟨y, hy, rfl⟩ := exists_one_le_mul_of_le hacx
    refine ⟨a * y, ⟨le_mul_of_one_le_right' hy, ?_⟩, c, left_mem_Icc.2 hcd, mul_right_comm ..⟩
    rwa [mul_right_comm, mul_le_mul_iff_right] at hxbc
  · obtain ⟨y, hy, rfl⟩ := exists_one_le_mul_of_le hbcx
    refine ⟨b, right_mem_Icc.2 hab, c * y, ⟨le_mul_of_one_le_right' hy, ?_⟩, (mul_assoc ..).symm⟩
    rwa [mul_assoc, mul_le_mul_iff_left] at hxbd

end LinearOrderedCommMonoid

section OrderedCommGroup
variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

/--
lemma `inv_Ici` / 引理 `inv_Ici`

English:
lemma inv_Ici
  given: (a : α)
  statement: (Ici a)⁻¹ = Iic a⁻¹
  proof: ext fun _x => le_inv'

中文:
引理 inv_Ici
  条件: (a : α)
  结论: (Ici a)⁻¹ = Iic a⁻¹
  证明: ext fun _x => le_inv'
-/
@[to_additive (attr := simp)] lemma inv_Ici (a : α) : (Ici a)⁻¹ = Iic a⁻¹ := ext fun _x => le_inv'
/--
lemma `inv_Iic` / 引理 `inv_Iic`

English:
lemma inv_Iic
  given: (a : α)
  statement: (Iic a)⁻¹ = Ici a⁻¹
  proof: ext fun _x => inv_le'

中文:
引理 inv_Iic
  条件: (a : α)
  结论: (Iic a)⁻¹ = Ici a⁻¹
  证明: ext fun _x => inv_le'
-/
@[to_additive (attr := simp)] lemma inv_Iic (a : α) : (Iic a)⁻¹ = Ici a⁻¹ := ext fun _x => inv_le'
/--
lemma `inv_Ioi` / 引理 `inv_Ioi`

English:
lemma inv_Ioi
  given: (a : α)
  statement: (Ioi a)⁻¹ = Iio a⁻¹
  proof: ext fun _x => lt_inv'

中文:
引理 inv_Ioi
  条件: (a : α)
  结论: (Ioi a)⁻¹ = Iio a⁻¹
  证明: ext fun _x => lt_inv'
-/
@[to_additive (attr := simp)] lemma inv_Ioi (a : α) : (Ioi a)⁻¹ = Iio a⁻¹ := ext fun _x => lt_inv'
/--
lemma `inv_Iio` / 引理 `inv_Iio`

English:
lemma inv_Iio
  given: (a : α)
  statement: (Iio a)⁻¹ = Ioi a⁻¹
  proof: ext fun _x => inv_lt'

@[to_additive (attr := simp)]

中文:
引理 inv_Iio
  条件: (a : α)
  结论: (Iio a)⁻¹ = Ioi a⁻¹
  证明: ext fun _x => inv_lt'

@[to_additive (attr := simp)]
-/
@[to_additive (attr := simp)] lemma inv_Iio (a : α) : (Iio a)⁻¹ = Ioi a⁻¹ := ext fun _x => inv_lt'

@[to_additive (attr := simp)]
/--
lemma `inv_Icc` / 引理 `inv_Icc`

English:
lemma inv_Icc
  given: (a b : α)
  statement: (Icc a b)⁻¹ = Icc b⁻¹ a⁻¹
  proof: by simp [← Ici_inter_Iic, inter_comm]

@[to_additive (attr := simp)]

中文:
引理 inv_Icc
  条件: (a b : α)
  结论: (Icc a b)⁻¹ = Icc b⁻¹ a⁻¹
  证明: by simp [← Ici_inter_Iic, inter_comm]

@[to_additive (attr := simp)]

Depends on / 依赖: Ici_inter_Iic, inter_comm
-/
lemma inv_Icc (a b : α) : (Icc a b)⁻¹ = Icc b⁻¹ a⁻¹ := by simp [← Ici_inter_Iic, inter_comm]

@[to_additive (attr := simp)]
/--
lemma `inv_Ico` / 引理 `inv_Ico`

English:
lemma inv_Ico
  given: (a b : α)
  statement: (Ico a b)⁻¹ = Ioc b⁻¹ a⁻¹
  proof: by
  simp [← Ici_inter_Iio, ← Ioi_inter_Iic, inter_comm]

@[to_additive (attr := simp)]

中文:
引理 inv_Ico
  条件: (a b : α)
  结论: (Ico a b)⁻¹ = Ioc b⁻¹ a⁻¹
  证明: by
  simp [← Ici_inter_Iio, ← Ioi_inter_Iic, inter_comm]

@[to_additive (attr := simp)]

Depends on / 依赖: Ici_inter_Iio, Ioi_inter_Iic, inter_comm
-/
lemma inv_Ico (a b : α) : (Ico a b)⁻¹ = Ioc b⁻¹ a⁻¹ := by
  simp [← Ici_inter_Iio, ← Ioi_inter_Iic, inter_comm]

@[to_additive (attr := simp)]
/--
lemma `inv_Ioc` / 引理 `inv_Ioc`

English:
lemma inv_Ioc
  given: (a b : α)
  statement: (Ioc a b)⁻¹ = Ico b⁻¹ a⁻¹
  proof: by
  simp [← Ioi_inter_Iic, ← Ici_inter_Iio, inter_comm]

@[to_additive (attr := simp)]

中文:
引理 inv_Ioc
  条件: (a b : α)
  结论: (Ioc a b)⁻¹ = Ico b⁻¹ a⁻¹
  证明: by
  simp [← Ioi_inter_Iic, ← Ici_inter_Iio, inter_comm]

@[to_additive (attr := simp)]

Depends on / 依赖: Ici_inter_Iio, Ioi_inter_Iic, inter_comm
-/
lemma inv_Ioc (a b : α) : (Ioc a b)⁻¹ = Ico b⁻¹ a⁻¹ := by
  simp [← Ioi_inter_Iic, ← Ici_inter_Iio, inter_comm]

@[to_additive (attr := simp)]
/--
lemma `inv_Ioo` / 引理 `inv_Ioo`

English:
lemma inv_Ioo
  given: (a b : α)
  statement: (Ioo a b)⁻¹ = Ioo b⁻¹ a⁻¹
  proof: by simp [← Ioi_inter_Iio, inter_comm]

中文:
引理 inv_Ioo
  条件: (a b : α)
  结论: (Ioo a b)⁻¹ = Ioo b⁻¹ a⁻¹
  证明: by simp [← Ioi_inter_Iio, inter_comm]

Depends on / 依赖: Ioi_inter_Iio, inter_comm
-/
lemma inv_Ioo (a b : α) : (Ioo a b)⁻¹ = Ioo b⁻¹ a⁻¹ := by simp [← Ioi_inter_Iio, inter_comm]

/-!
### Preimages under `x ↦ a * x`
-/

@[to_additive (attr := simp)]
/--
theorem `preimage_const_mul_Ici` / 定理 `preimage_const_mul_Ici`

English:
theorem preimage_const_mul_Ici
  statement: (fun x => a * x) ⁻¹' Ici b = Ici (b / a)
  proof: ext fun _x => div_le_iff_le_mul'.symm

@[to_additive (attr := simp)]

中文:
定理 preimage_const_mul_Ici
  结论: (fun x => a * x) ⁻¹' Ici b = Ici (b / a)
  证明: ext fun _x => div_le_iff_le_mul'.symm

@[to_additive (attr := simp)]

Depends on / 依赖: div_le_iff_le_mul
-/
theorem preimage_const_mul_Ici : (fun x => a * x) ⁻¹' Ici b = Ici (b / a) :=
  ext fun _x => div_le_iff_le_mul'.symm

@[to_additive (attr := simp)]
/--
theorem `preimage_const_mul_Ioi` / 定理 `preimage_const_mul_Ioi`

English:
theorem preimage_const_mul_Ioi
  statement: (fun x => a * x) ⁻¹' Ioi b = Ioi (b / a)
  proof: ext fun _x => div_lt_iff_lt_mul'.symm

@[to_additive (attr := simp)]

中文:
定理 preimage_const_mul_Ioi
  结论: (fun x => a * x) ⁻¹' Ioi b = Ioi (b / a)
  证明: ext fun _x => div_lt_iff_lt_mul'.symm

@[to_additive (attr := simp)]

Depends on / 依赖: div_lt_iff_lt_mul
-/
theorem preimage_const_mul_Ioi : (fun x => a * x) ⁻¹' Ioi b = Ioi (b / a) :=
  ext fun _x => div_lt_iff_lt_mul'.symm

@[to_additive (attr := simp)]
/--
theorem `preimage_const_mul_Iic` / 定理 `preimage_const_mul_Iic`

English:
theorem preimage_const_mul_Iic
  statement: (fun x => a * x) ⁻¹' Iic b = Iic (b / a)
  proof: ext fun _x => le_div_iff_mul_le'.symm

@[to_additive (attr := simp)]

中文:
定理 preimage_const_mul_Iic
  结论: (fun x => a * x) ⁻¹' Iic b = Iic (b / a)
  证明: ext fun _x => le_div_iff_mul_le'.symm

@[to_additive (attr := simp)]

Depends on / 依赖: le_div_iff_mul_le
-/
theorem preimage_const_mul_Iic : (fun x => a * x) ⁻¹' Iic b = Iic (b / a) :=
  ext fun _x => le_div_iff_mul_le'.symm

@[to_additive (attr := simp)]
/--
theorem `preimage_const_mul_Iio` / 定理 `preimage_const_mul_Iio`

English:
theorem preimage_const_mul_Iio
  statement: (fun x => a * x) ⁻¹' Iio b = Iio (b / a)
  proof: ext fun _x => lt_div_iff_mul_lt'.symm

@[to_additive (attr := simp)]

中文:
定理 preimage_const_mul_Iio
  结论: (fun x => a * x) ⁻¹' Iio b = Iio (b / a)
  证明: ext fun _x => lt_div_iff_mul_lt'.symm

@[to_additive (attr := simp)]

Depends on / 依赖: lt_div_iff_mul_lt
-/
theorem preimage_const_mul_Iio : (fun x => a * x) ⁻¹' Iio b = Iio (b / a) :=
  ext fun _x => lt_div_iff_mul_lt'.symm

@[to_additive (attr := simp)]
/--
theorem `preimage_const_mul_Icc` / 定理 `preimage_const_mul_Icc`

English:
theorem preimage_const_mul_Icc
  statement: (fun x => a * x) ⁻¹' Icc b c = Icc (b / a) (c / a)
  proof: by
  simp [← Ici_inter_Iic]

@[to_additive (attr := simp)]

中文:
定理 preimage_const_mul_Icc
  结论: (fun x => a * x) ⁻¹' Icc b c = Icc (b / a) (c / a)
  证明: by
  simp [← Ici_inter_Iic]

@[to_additive (attr := simp)]

Depends on / 依赖: Ici_inter_Iic
-/
theorem preimage_const_mul_Icc : (fun x => a * x) ⁻¹' Icc b c = Icc (b / a) (c / a) := by
  simp [← Ici_inter_Iic]

@[to_additive (attr := simp)]
/--
theorem `preimage_const_mul_Ico` / 定理 `preimage_const_mul_Ico`

English:
theorem preimage_const_mul_Ico
  statement: (fun x => a * x) ⁻¹' Ico b c = Ico (b / a) (c / a)
  proof: by
  simp [← Ici_inter_Iio]

@[to_additive (attr := simp)]

中文:
定理 preimage_const_mul_Ico
  结论: (fun x => a * x) ⁻¹' Ico b c = Ico (b / a) (c / a)
  证明: by
  simp [← Ici_inter_Iio]

@[to_additive (attr := simp)]

Depends on / 依赖: Ici_inter_Iio
-/
theorem preimage_const_mul_Ico : (fun x => a * x) ⁻¹' Ico b c = Ico (b / a) (c / a) := by
  simp [← Ici_inter_Iio]

@[to_additive (attr := simp)]
/--
theorem `preimage_const_mul_Ioc` / 定理 `preimage_const_mul_Ioc`

English:
theorem preimage_const_mul_Ioc
  statement: (fun x => a * x) ⁻¹' Ioc b c = Ioc (b / a) (c / a)
  proof: by
  simp [← Ioi_inter_Iic]

@[to_additive (attr := simp)]

中文:
定理 preimage_const_mul_Ioc
  结论: (fun x => a * x) ⁻¹' Ioc b c = Ioc (b / a) (c / a)
  证明: by
  simp [← Ioi_inter_Iic]

@[to_additive (attr := simp)]

Depends on / 依赖: Ioi_inter_Iic
-/
theorem preimage_const_mul_Ioc : (fun x => a * x) ⁻¹' Ioc b c = Ioc (b / a) (c / a) := by
  simp [← Ioi_inter_Iic]

@[to_additive (attr := simp)]
/--
theorem `preimage_const_mul_Ioo` / 定理 `preimage_const_mul_Ioo`

English:
theorem preimage_const_mul_Ioo
  statement: (fun x => a * x) ⁻¹' Ioo b c = Ioo (b / a) (c / a)
  proof: by
  simp [← Ioi_inter_Iio]

中文:
定理 preimage_const_mul_Ioo
  结论: (fun x => a * x) ⁻¹' Ioo b c = Ioo (b / a) (c / a)
  证明: by
  simp [← Ioi_inter_Iio]

Depends on / 依赖: Ioi_inter_Iio
-/
theorem preimage_const_mul_Ioo : (fun x => a * x) ⁻¹' Ioo b c = Ioo (b / a) (c / a) := by
  simp [← Ioi_inter_Iio]

/-!
### Preimages under `x ↦ x * a`
-/

@[to_additive (attr := simp)]
/--
theorem `preimage_mul_const_Ici` / 定理 `preimage_mul_const_Ici`

English:
theorem preimage_mul_const_Ici
  statement: (fun x => x * a) ⁻¹' Ici b = Ici (b / a)
  proof: ext fun _x => div_le_iff_le_mul.symm

@[to_additive (attr := simp)]

中文:
定理 preimage_mul_const_Ici
  结论: (fun x => x * a) ⁻¹' Ici b = Ici (b / a)
  证明: ext fun _x => div_le_iff_le_mul.symm

@[to_additive (attr := simp)]

Depends on / 依赖: div_le_iff_le_mul, div_le_iff_le_mul.symm
-/
theorem preimage_mul_const_Ici : (fun x => x * a) ⁻¹' Ici b = Ici (b / a) :=
  ext fun _x => div_le_iff_le_mul.symm

@[to_additive (attr := simp)]
/--
theorem `preimage_mul_const_Ioi` / 定理 `preimage_mul_const_Ioi`

English:
theorem preimage_mul_const_Ioi
  statement: (fun x => x * a) ⁻¹' Ioi b = Ioi (b / a)
  proof: ext fun _x => div_lt_iff_lt_mul.symm

@[to_additive (attr := simp)]

中文:
定理 preimage_mul_const_Ioi
  结论: (fun x => x * a) ⁻¹' Ioi b = Ioi (b / a)
  证明: ext fun _x => div_lt_iff_lt_mul.symm

@[to_additive (attr := simp)]

Depends on / 依赖: div_lt_iff_lt_mul, div_lt_iff_lt_mul.symm
-/
theorem preimage_mul_const_Ioi : (fun x => x * a) ⁻¹' Ioi b = Ioi (b / a) :=
  ext fun _x => div_lt_iff_lt_mul.symm

@[to_additive (attr := simp)]
/--
theorem `preimage_mul_const_Iic` / 定理 `preimage_mul_const_Iic`

English:
theorem preimage_mul_const_Iic
  statement: (fun x => x * a) ⁻¹' Iic b = Iic (b / a)
  proof: ext fun _x => le_div_iff_mul_le.symm

@[to_additive (attr := simp)]

中文:
定理 preimage_mul_const_Iic
  结论: (fun x => x * a) ⁻¹' Iic b = Iic (b / a)
  证明: ext fun _x => le_div_iff_mul_le.symm

@[to_additive (attr := simp)]

Depends on / 依赖: le_div_iff_mul_le, le_div_iff_mul_le.symm
-/
theorem preimage_mul_const_Iic : (fun x => x * a) ⁻¹' Iic b = Iic (b / a) :=
  ext fun _x => le_div_iff_mul_le.symm

@[to_additive (attr := simp)]
/--
theorem `preimage_mul_const_Iio` / 定理 `preimage_mul_const_Iio`

English:
theorem preimage_mul_const_Iio
  statement: (fun x => x * a) ⁻¹' Iio b = Iio (b / a)
  proof: ext fun _x => lt_div_iff_mul_lt.symm

@[to_additive (attr := simp)]

中文:
定理 preimage_mul_const_Iio
  结论: (fun x => x * a) ⁻¹' Iio b = Iio (b / a)
  证明: ext fun _x => lt_div_iff_mul_lt.symm

@[to_additive (attr := simp)]

Depends on / 依赖: lt_div_iff_mul_lt, lt_div_iff_mul_lt.symm
-/
theorem preimage_mul_const_Iio : (fun x => x * a) ⁻¹' Iio b = Iio (b / a) :=
  ext fun _x => lt_div_iff_mul_lt.symm

@[to_additive (attr := simp)]
/--
theorem `preimage_mul_const_Icc` / 定理 `preimage_mul_const_Icc`

English:
theorem preimage_mul_const_Icc
  statement: (fun x => x * a) ⁻¹' Icc b c = Icc (b / a) (c / a)
  proof: by
  simp [← Ici_inter_Iic]

@[to_additive (attr := simp)]

中文:
定理 preimage_mul_const_Icc
  结论: (fun x => x * a) ⁻¹' Icc b c = Icc (b / a) (c / a)
  证明: by
  simp [← Ici_inter_Iic]

@[to_additive (attr := simp)]

Depends on / 依赖: Ici_inter_Iic
-/
theorem preimage_mul_const_Icc : (fun x => x * a) ⁻¹' Icc b c = Icc (b / a) (c / a) := by
  simp [← Ici_inter_Iic]

@[to_additive (attr := simp)]
/--
theorem `preimage_mul_const_Ico` / 定理 `preimage_mul_const_Ico`

English:
theorem preimage_mul_const_Ico
  statement: (fun x => x * a) ⁻¹' Ico b c = Ico (b / a) (c / a)
  proof: by
  simp [← Ici_inter_Iio]

@[to_additive (attr := simp)]

中文:
定理 preimage_mul_const_Ico
  结论: (fun x => x * a) ⁻¹' Ico b c = Ico (b / a) (c / a)
  证明: by
  simp [← Ici_inter_Iio]

@[to_additive (attr := simp)]

Depends on / 依赖: Ici_inter_Iio
-/
theorem preimage_mul_const_Ico : (fun x => x * a) ⁻¹' Ico b c = Ico (b / a) (c / a) := by
  simp [← Ici_inter_Iio]

@[to_additive (attr := simp)]
/--
theorem `preimage_mul_const_Ioc` / 定理 `preimage_mul_const_Ioc`

English:
theorem preimage_mul_const_Ioc
  statement: (fun x => x * a) ⁻¹' Ioc b c = Ioc (b / a) (c / a)
  proof: by
  simp [← Ioi_inter_Iic]

@[to_additive (attr := simp)]

中文:
定理 preimage_mul_const_Ioc
  结论: (fun x => x * a) ⁻¹' Ioc b c = Ioc (b / a) (c / a)
  证明: by
  simp [← Ioi_inter_Iic]

@[to_additive (attr := simp)]

Depends on / 依赖: Ioi_inter_Iic
-/
theorem preimage_mul_const_Ioc : (fun x => x * a) ⁻¹' Ioc b c = Ioc (b / a) (c / a) := by
  simp [← Ioi_inter_Iic]

@[to_additive (attr := simp)]
/--
theorem `preimage_mul_const_Ioo` / 定理 `preimage_mul_const_Ioo`

English:
theorem preimage_mul_const_Ioo
  statement: (fun x => x * a) ⁻¹' Ioo b c = Ioo (b / a) (c / a)
  proof: by
  simp [← Ioi_inter_Iio]

中文:
定理 preimage_mul_const_Ioo
  结论: (fun x => x * a) ⁻¹' Ioo b c = Ioo (b / a) (c / a)
  证明: by
  simp [← Ioi_inter_Iio]

Depends on / 依赖: Ioi_inter_Iio
-/
theorem preimage_mul_const_Ioo : (fun x => x * a) ⁻¹' Ioo b c = Ioo (b / a) (c / a) := by
  simp [← Ioi_inter_Iio]

/-!
### Preimages under `x ↦ x / a`
-/

@[to_additive (attr := simp)]
/--
theorem `preimage_div_const_Ici` / 定理 `preimage_div_const_Ici`

English:
theorem preimage_div_const_Ici
  statement: (fun x => x / a) ⁻¹' Ici b = Ici (b * a)
  proof: by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]

中文:
定理 preimage_div_const_Ici
  结论: (fun x => x / a) ⁻¹' Ici b = Ici (b * a)
  证明: by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]

Depends on / 依赖: div_eq_mul_inv
-/
theorem preimage_div_const_Ici : (fun x => x / a) ⁻¹' Ici b = Ici (b * a) := by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]
/--
theorem `preimage_div_const_Ioi` / 定理 `preimage_div_const_Ioi`

English:
theorem preimage_div_const_Ioi
  statement: (fun x => x / a) ⁻¹' Ioi b = Ioi (b * a)
  proof: by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]

中文:
定理 preimage_div_const_Ioi
  结论: (fun x => x / a) ⁻¹' Ioi b = Ioi (b * a)
  证明: by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]

Depends on / 依赖: div_eq_mul_inv
-/
theorem preimage_div_const_Ioi : (fun x => x / a) ⁻¹' Ioi b = Ioi (b * a) := by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]
/--
theorem `preimage_div_const_Iic` / 定理 `preimage_div_const_Iic`

English:
theorem preimage_div_const_Iic
  statement: (fun x => x / a) ⁻¹' Iic b = Iic (b * a)
  proof: by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]

中文:
定理 preimage_div_const_Iic
  结论: (fun x => x / a) ⁻¹' Iic b = Iic (b * a)
  证明: by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]

Depends on / 依赖: div_eq_mul_inv
-/
theorem preimage_div_const_Iic : (fun x => x / a) ⁻¹' Iic b = Iic (b * a) := by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]
/--
theorem `preimage_div_const_Iio` / 定理 `preimage_div_const_Iio`

English:
theorem preimage_div_const_Iio
  statement: (fun x => x / a) ⁻¹' Iio b = Iio (b * a)
  proof: by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]

中文:
定理 preimage_div_const_Iio
  结论: (fun x => x / a) ⁻¹' Iio b = Iio (b * a)
  证明: by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]

Depends on / 依赖: div_eq_mul_inv
-/
theorem preimage_div_const_Iio : (fun x => x / a) ⁻¹' Iio b = Iio (b * a) := by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]
/--
theorem `preimage_div_const_Icc` / 定理 `preimage_div_const_Icc`

English:
theorem preimage_div_const_Icc
  statement: (fun x => x / a) ⁻¹' Icc b c = Icc (b * a) (c * a)
  proof: by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]

中文:
定理 preimage_div_const_Icc
  结论: (fun x => x / a) ⁻¹' Icc b c = Icc (b * a) (c * a)
  证明: by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]

Depends on / 依赖: div_eq_mul_inv
-/
theorem preimage_div_const_Icc : (fun x => x / a) ⁻¹' Icc b c = Icc (b * a) (c * a) := by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]
/--
theorem `preimage_div_const_Ico` / 定理 `preimage_div_const_Ico`

English:
theorem preimage_div_const_Ico
  statement: (fun x => x / a) ⁻¹' Ico b c = Ico (b * a) (c * a)
  proof: by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]

中文:
定理 preimage_div_const_Ico
  结论: (fun x => x / a) ⁻¹' Ico b c = Ico (b * a) (c * a)
  证明: by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]

Depends on / 依赖: div_eq_mul_inv
-/
theorem preimage_div_const_Ico : (fun x => x / a) ⁻¹' Ico b c = Ico (b * a) (c * a) := by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]
/--
theorem `preimage_div_const_Ioc` / 定理 `preimage_div_const_Ioc`

English:
theorem preimage_div_const_Ioc
  statement: (fun x => x / a) ⁻¹' Ioc b c = Ioc (b * a) (c * a)
  proof: by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]

中文:
定理 preimage_div_const_Ioc
  结论: (fun x => x / a) ⁻¹' Ioc b c = Ioc (b * a) (c * a)
  证明: by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]

Depends on / 依赖: div_eq_mul_inv
-/
theorem preimage_div_const_Ioc : (fun x => x / a) ⁻¹' Ioc b c = Ioc (b * a) (c * a) := by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]
/--
theorem `preimage_div_const_Ioo` / 定理 `preimage_div_const_Ioo`

English:
theorem preimage_div_const_Ioo
  statement: (fun x => x / a) ⁻¹' Ioo b c = Ioo (b * a) (c * a)
  proof: by
  simp [div_eq_mul_inv]

中文:
定理 preimage_div_const_Ioo
  结论: (fun x => x / a) ⁻¹' Ioo b c = Ioo (b * a) (c * a)
  证明: by
  simp [div_eq_mul_inv]

Depends on / 依赖: div_eq_mul_inv
-/
theorem preimage_div_const_Ioo : (fun x => x / a) ⁻¹' Ioo b c = Ioo (b * a) (c * a) := by
  simp [div_eq_mul_inv]

/-!
### Preimages under `x ↦ a / x`
-/

@[to_additive (attr := simp)]
/--
theorem `preimage_const_div_Ici` / 定理 `preimage_const_div_Ici`

English:
theorem preimage_const_div_Ici
  statement: (fun x => a / x) ⁻¹' Ici b = Iic (a / b)
  proof: ext fun _x => le_div_comm

@[to_additive (attr := simp)]

中文:
定理 preimage_const_div_Ici
  结论: (fun x => a / x) ⁻¹' Ici b = Iic (a / b)
  证明: ext fun _x => le_div_comm

@[to_additive (attr := simp)]

Depends on / 依赖: le_div_comm
-/
theorem preimage_const_div_Ici : (fun x => a / x) ⁻¹' Ici b = Iic (a / b) :=
  ext fun _x => le_div_comm

@[to_additive (attr := simp)]
/--
theorem `preimage_const_div_Iic` / 定理 `preimage_const_div_Iic`

English:
theorem preimage_const_div_Iic
  statement: (fun x => a / x) ⁻¹' Iic b = Ici (a / b)
  proof: ext fun _x => div_le_comm

@[to_additive (attr := simp)]

中文:
定理 preimage_const_div_Iic
  结论: (fun x => a / x) ⁻¹' Iic b = Ici (a / b)
  证明: ext fun _x => div_le_comm

@[to_additive (attr := simp)]

Depends on / 依赖: div_le_comm
-/
theorem preimage_const_div_Iic : (fun x => a / x) ⁻¹' Iic b = Ici (a / b) :=
  ext fun _x => div_le_comm

@[to_additive (attr := simp)]
/--
theorem `preimage_const_div_Ioi` / 定理 `preimage_const_div_Ioi`

English:
theorem preimage_const_div_Ioi
  statement: (fun x => a / x) ⁻¹' Ioi b = Iio (a / b)
  proof: ext fun _x => lt_div_comm

@[to_additive (attr := simp)]

中文:
定理 preimage_const_div_Ioi
  结论: (fun x => a / x) ⁻¹' Ioi b = Iio (a / b)
  证明: ext fun _x => lt_div_comm

@[to_additive (attr := simp)]

Depends on / 依赖: lt_div_comm
-/
theorem preimage_const_div_Ioi : (fun x => a / x) ⁻¹' Ioi b = Iio (a / b) :=
  ext fun _x => lt_div_comm

@[to_additive (attr := simp)]
/--
theorem `preimage_const_div_Iio` / 定理 `preimage_const_div_Iio`

English:
theorem preimage_const_div_Iio
  statement: (fun x => a / x) ⁻¹' Iio b = Ioi (a / b)
  proof: ext fun _x => div_lt_comm

@[to_additive (attr := simp)]

中文:
定理 preimage_const_div_Iio
  结论: (fun x => a / x) ⁻¹' Iio b = Ioi (a / b)
  证明: ext fun _x => div_lt_comm

@[to_additive (attr := simp)]

Depends on / 依赖: div_lt_comm
-/
theorem preimage_const_div_Iio : (fun x => a / x) ⁻¹' Iio b = Ioi (a / b) :=
  ext fun _x => div_lt_comm

@[to_additive (attr := simp)]
/--
theorem `preimage_const_div_Icc` / 定理 `preimage_const_div_Icc`

English:
theorem preimage_const_div_Icc
  statement: (fun x => a / x) ⁻¹' Icc b c = Icc (a / c) (a / b)
  proof: by
  simp [← Ici_inter_Iic, inter_comm]

@[to_additive (attr := simp)]

中文:
定理 preimage_const_div_Icc
  结论: (fun x => a / x) ⁻¹' Icc b c = Icc (a / c) (a / b)
  证明: by
  simp [← Ici_inter_Iic, inter_comm]

@[to_additive (attr := simp)]

Depends on / 依赖: Ici_inter_Iic, inter_comm
-/
theorem preimage_const_div_Icc : (fun x => a / x) ⁻¹' Icc b c = Icc (a / c) (a / b) := by
  simp [← Ici_inter_Iic, inter_comm]

@[to_additive (attr := simp)]
/--
theorem `preimage_const_div_Ico` / 定理 `preimage_const_div_Ico`

English:
theorem preimage_const_div_Ico
  statement: (fun x => a / x) ⁻¹' Ico b c = Ioc (a / c) (a / b)
  proof: by
  simp [← Ioi_inter_Iic, ← Ici_inter_Iio, inter_comm]

@[to_additive (attr := simp)]

中文:
定理 preimage_const_div_Ico
  结论: (fun x => a / x) ⁻¹' Ico b c = Ioc (a / c) (a / b)
  证明: by
  simp [← Ioi_inter_Iic, ← Ici_inter_Iio, inter_comm]

@[to_additive (attr := simp)]

Depends on / 依赖: Ici_inter_Iio, Ioi_inter_Iic, inter_comm
-/
theorem preimage_const_div_Ico : (fun x => a / x) ⁻¹' Ico b c = Ioc (a / c) (a / b) := by
  simp [← Ioi_inter_Iic, ← Ici_inter_Iio, inter_comm]

@[to_additive (attr := simp)]
/--
theorem `preimage_const_div_Ioc` / 定理 `preimage_const_div_Ioc`

English:
theorem preimage_const_div_Ioc
  statement: (fun x => a / x) ⁻¹' Ioc b c = Ico (a / c) (a / b)
  proof: by
  simp [← Ioi_inter_Iic, ← Ici_inter_Iio, inter_comm]

@[to_additive (attr := simp)]

中文:
定理 preimage_const_div_Ioc
  结论: (fun x => a / x) ⁻¹' Ioc b c = Ico (a / c) (a / b)
  证明: by
  simp [← Ioi_inter_Iic, ← Ici_inter_Iio, inter_comm]

@[to_additive (attr := simp)]

Depends on / 依赖: Ici_inter_Iio, Ioi_inter_Iic, inter_comm
-/
theorem preimage_const_div_Ioc : (fun x => a / x) ⁻¹' Ioc b c = Ico (a / c) (a / b) := by
  simp [← Ioi_inter_Iic, ← Ici_inter_Iio, inter_comm]

@[to_additive (attr := simp)]
/--
theorem `preimage_const_div_Ioo` / 定理 `preimage_const_div_Ioo`

English:
theorem preimage_const_div_Ioo
  statement: (fun x => a / x) ⁻¹' Ioo b c = Ioo (a / c) (a / b)
  proof: by
  simp [← Ioi_inter_Iio, inter_comm]

中文:
定理 preimage_const_div_Ioo
  结论: (fun x => a / x) ⁻¹' Ioo b c = Ioo (a / c) (a / b)
  证明: by
  simp [← Ioi_inter_Iio, inter_comm]

Depends on / 依赖: Ioi_inter_Iio, inter_comm
-/
theorem preimage_const_div_Ioo : (fun x => a / x) ⁻¹' Ioo b c = Ioo (a / c) (a / b) := by
  simp [← Ioi_inter_Iio, inter_comm]

/-!
### Images under `x ↦ a * x`
-/

-- simp can prove this modulo `mul_comm`
@[to_additive]
/--
theorem `image_const_mul_Iic` / 定理 `image_const_mul_Iic`

English:
theorem image_const_mul_Iic
  statement: (fun x => a * x) '' Iic b = Iic (a * b)
  proof: by simp [mul_comm]

中文:
定理 image_const_mul_Iic
  结论: (fun x => a * x) '' Iic b = Iic (a * b)
  证明: by simp [mul_comm]

Depends on / 依赖: mul_comm
-/
theorem image_const_mul_Iic : (fun x => a * x) '' Iic b = Iic (a * b) := by simp [mul_comm]

-- simp can prove this modulo `mul_comm`
@[to_additive]
/--
theorem `image_const_mul_Iio` / 定理 `image_const_mul_Iio`

English:
theorem image_const_mul_Iio
  statement: (fun x => a * x) '' Iio b = Iio (a * b)
  proof: by simp [mul_comm]

中文:
定理 image_const_mul_Iio
  结论: (fun x => a * x) '' Iio b = Iio (a * b)
  证明: by simp [mul_comm]

Depends on / 依赖: mul_comm
-/
theorem image_const_mul_Iio : (fun x => a * x) '' Iio b = Iio (a * b) := by simp [mul_comm]

/-!
### Images under `x ↦ x * a`
-/

@[to_additive]
/--
theorem `image_mul_const_Iic` / 定理 `image_mul_const_Iic`

English:
theorem image_mul_const_Iic
  statement: (fun x => x * a) '' Iic b = Iic (b * a)
  proof: by simp

@[to_additive]

中文:
定理 image_mul_const_Iic
  结论: (fun x => x * a) '' Iic b = Iic (b * a)
  证明: by simp

@[to_additive]
-/
theorem image_mul_const_Iic : (fun x => x * a) '' Iic b = Iic (b * a) := by simp

@[to_additive]
/--
theorem `image_mul_const_Iio` / 定理 `image_mul_const_Iio`

English:
theorem image_mul_const_Iio
  statement: (fun x => x * a) '' Iio b = Iio (b * a)
  proof: by simp

中文:
定理 image_mul_const_Iio
  结论: (fun x => x * a) '' Iio b = Iio (b * a)
  证明: by simp
-/
theorem image_mul_const_Iio : (fun x => x * a) '' Iio b = Iio (b * a) := by simp


/-!
### Images under `x ↦ x⁻¹`
-/

@[to_additive]
/--
theorem `image_inv_Ici` / 定理 `image_inv_Ici`

English:
theorem image_inv_Ici
  statement: Inv.inv '' Ici a = Iic (a⁻¹)
  proof: by simp

@[to_additive]

中文:
定理 image_inv_Ici
  结论: Inv.inv '' Ici a = Iic (a⁻¹)
  证明: by simp

@[to_additive]
-/
theorem image_inv_Ici : Inv.inv '' Ici a = Iic (a⁻¹) := by simp

@[to_additive]
/--
theorem `image_inv_Iic` / 定理 `image_inv_Iic`

English:
theorem image_inv_Iic
  statement: Inv.inv '' Iic a = Ici (a⁻¹)
  proof: by simp

@[to_additive]

中文:
定理 image_inv_Iic
  结论: Inv.inv '' Iic a = Ici (a⁻¹)
  证明: by simp

@[to_additive]
-/
theorem image_inv_Iic : Inv.inv '' Iic a = Ici (a⁻¹) := by simp

@[to_additive]
/--
theorem `image_inv_Ioi` / 定理 `image_inv_Ioi`

English:
theorem image_inv_Ioi
  statement: Inv.inv '' Ioi a = Iio (a⁻¹)
  proof: by simp

@[to_additive]

中文:
定理 image_inv_Ioi
  结论: Inv.inv '' Ioi a = Iio (a⁻¹)
  证明: by simp

@[to_additive]
-/
theorem image_inv_Ioi : Inv.inv '' Ioi a = Iio (a⁻¹) := by simp

@[to_additive]
/--
theorem `image_inv_Iio` / 定理 `image_inv_Iio`

English:
theorem image_inv_Iio
  statement: Inv.inv '' Iio a = Ioi (a⁻¹)
  proof: by simp

@[to_additive]

中文:
定理 image_inv_Iio
  结论: Inv.inv '' Iio a = Ioi (a⁻¹)
  证明: by simp

@[to_additive]
-/
theorem image_inv_Iio : Inv.inv '' Iio a = Ioi (a⁻¹) := by simp

@[to_additive]
/--
theorem `image_inv_Icc` / 定理 `image_inv_Icc`

English:
theorem image_inv_Icc
  statement: Inv.inv '' Icc a b = Icc (b⁻¹) (a⁻¹)
  proof: by simp

@[to_additive]

中文:
定理 image_inv_Icc
  结论: Inv.inv '' Icc a b = Icc (b⁻¹) (a⁻¹)
  证明: by simp

@[to_additive]
-/
theorem image_inv_Icc : Inv.inv '' Icc a b = Icc (b⁻¹) (a⁻¹) := by simp

@[to_additive]
/--
theorem `image_inv_Ico` / 定理 `image_inv_Ico`

English:
theorem image_inv_Ico
  statement: Inv.inv '' Ico a b = Ioc (b⁻¹) (a⁻¹)
  proof: by simp

@[to_additive]

中文:
定理 image_inv_Ico
  结论: Inv.inv '' Ico a b = Ioc (b⁻¹) (a⁻¹)
  证明: by simp

@[to_additive]
-/
theorem image_inv_Ico : Inv.inv '' Ico a b = Ioc (b⁻¹) (a⁻¹) := by simp

@[to_additive]
/--
theorem `image_inv_Ioc` / 定理 `image_inv_Ioc`

English:
theorem image_inv_Ioc
  statement: Inv.inv '' Ioc a b = Ico (b⁻¹) (a⁻¹)
  proof: by simp

@[to_additive]

中文:
定理 image_inv_Ioc
  结论: Inv.inv '' Ioc a b = Ico (b⁻¹) (a⁻¹)
  证明: by simp

@[to_additive]
-/
theorem image_inv_Ioc : Inv.inv '' Ioc a b = Ico (b⁻¹) (a⁻¹) := by simp

@[to_additive]
/--
theorem `image_inv_Ioo` / 定理 `image_inv_Ioo`

English:
theorem image_inv_Ioo
  statement: Inv.inv '' Ioo a b = Ioo (b⁻¹) (a⁻¹)
  proof: by simp

中文:
定理 image_inv_Ioo
  结论: Inv.inv '' Ioo a b = Ioo (b⁻¹) (a⁻¹)
  证明: by simp
-/
theorem image_inv_Ioo : Inv.inv '' Ioo a b = Ioo (b⁻¹) (a⁻¹) := by simp



/-!
### Images under `x ↦ a / x`
-/

@[to_additive (attr := simp)]
/--
theorem `image_const_div_Ici` / 定理 `image_const_div_Ici`

English:
theorem image_const_div_Ici
  statement: (fun x => a / x) '' Ici b = Iic (a / b)
  proof: by
  have := image_comp (fun x => a * x) fun x => x⁻¹; dsimp [Function.comp_def] at this
  simp [div_eq_mul_inv, this, mul_comm]

@[to_additive (attr := simp)]

中文:
定理 image_const_div_Ici
  结论: (fun x => a / x) '' Ici b = Iic (a / b)
  证明: by
  have := image_comp (fun x => a * x) fun x => x⁻¹; dsimp [Function.comp_def] at this
  simp [div_eq_mul_inv, this, mul_comm]

@[to_additive (attr := simp)]

Depends on / 依赖: Function, Function.comp_def, comp_def, div_eq_mul_inv, image_comp, mul_comm
-/
theorem image_const_div_Ici : (fun x => a / x) '' Ici b = Iic (a / b) := by
  have := image_comp (fun x => a * x) fun x => x⁻¹; dsimp [Function.comp_def] at this
  simp [div_eq_mul_inv, this, mul_comm]

@[to_additive (attr := simp)]
/--
theorem `image_const_div_Iic` / 定理 `image_const_div_Iic`

English:
theorem image_const_div_Iic
  statement: (fun x => a / x) '' Iic b = Ici (a / b)
  proof: by
  have := image_comp (fun x => a * x) fun x => x⁻¹; dsimp [Function.comp_def] at this
  simp [div_eq_mul_inv, this, mul_comm]

@[to_additive (attr := simp)]

中文:
定理 image_const_div_Iic
  结论: (fun x => a / x) '' Iic b = Ici (a / b)
  证明: by
  have := image_comp (fun x => a * x) fun x => x⁻¹; dsimp [Function.comp_def] at this
  simp [div_eq_mul_inv, this, mul_comm]

@[to_additive (attr := simp)]

Depends on / 依赖: Function, Function.comp_def, comp_def, div_eq_mul_inv, image_comp, mul_comm
-/
theorem image_const_div_Iic : (fun x => a / x) '' Iic b = Ici (a / b) := by
  have := image_comp (fun x => a * x) fun x => x⁻¹; dsimp [Function.comp_def] at this
  simp [div_eq_mul_inv, this, mul_comm]

@[to_additive (attr := simp)]
/--
theorem `image_const_div_Ioi` / 定理 `image_const_div_Ioi`

English:
theorem image_const_div_Ioi
  statement: (fun x => a / x) '' Ioi b = Iio (a / b)
  proof: by
  have := image_comp (fun x => a * x) fun x => x⁻¹; dsimp [Function.comp_def] at this
  simp [div_eq_mul_inv, this, mul_comm]

@[to_additive (attr := simp)]

中文:
定理 image_const_div_Ioi
  结论: (fun x => a / x) '' Ioi b = Iio (a / b)
  证明: by
  have := image_comp (fun x => a * x) fun x => x⁻¹; dsimp [Function.comp_def] at this
  simp [div_eq_mul_inv, this, mul_comm]

@[to_additive (attr := simp)]

Depends on / 依赖: Function, Function.comp_def, comp_def, div_eq_mul_inv, image_comp, mul_comm
-/
theorem image_const_div_Ioi : (fun x => a / x) '' Ioi b = Iio (a / b) := by
  have := image_comp (fun x => a * x) fun x => x⁻¹; dsimp [Function.comp_def] at this
  simp [div_eq_mul_inv, this, mul_comm]

@[to_additive (attr := simp)]
/--
theorem `image_const_div_Iio` / 定理 `image_const_div_Iio`

English:
theorem image_const_div_Iio
  statement: (fun x => a / x) '' Iio b = Ioi (a / b)
  proof: by
  have := image_comp (fun x => a * x) fun x => x⁻¹; dsimp [Function.comp_def] at this
  simp [div_eq_mul_inv, this, mul_comm]

@[to_additive (attr := simp)]

中文:
定理 image_const_div_Iio
  结论: (fun x => a / x) '' Iio b = Ioi (a / b)
  证明: by
  have := image_comp (fun x => a * x) fun x => x⁻¹; dsimp [Function.comp_def] at this
  simp [div_eq_mul_inv, this, mul_comm]

@[to_additive (attr := simp)]

Depends on / 依赖: Function, Function.comp_def, comp_def, div_eq_mul_inv, image_comp, mul_comm
-/
theorem image_const_div_Iio : (fun x => a / x) '' Iio b = Ioi (a / b) := by
  have := image_comp (fun x => a * x) fun x => x⁻¹; dsimp [Function.comp_def] at this
  simp [div_eq_mul_inv, this, mul_comm]

@[to_additive (attr := simp)]
/--
theorem `image_const_div_Icc` / 定理 `image_const_div_Icc`

English:
theorem image_const_div_Icc
  statement: (fun x => a / x) '' Icc b c = Icc (a / c) (a / b)
  proof: by
  have := image_comp (fun x => a * x) fun x => x⁻¹; dsimp [Function.comp_def] at this
  simp [div_eq_mul_inv, this, mul_comm]

@[to_additive (attr := simp)]

中文:
定理 image_const_div_Icc
  结论: (fun x => a / x) '' Icc b c = Icc (a / c) (a / b)
  证明: by
  have := image_comp (fun x => a * x) fun x => x⁻¹; dsimp [Function.comp_def] at this
  simp [div_eq_mul_inv, this, mul_comm]

@[to_additive (attr := simp)]

Depends on / 依赖: Function, Function.comp_def, comp_def, div_eq_mul_inv, image_comp, mul_comm
-/
theorem image_const_div_Icc : (fun x => a / x) '' Icc b c = Icc (a / c) (a / b) := by
  have := image_comp (fun x => a * x) fun x => x⁻¹; dsimp [Function.comp_def] at this
  simp [div_eq_mul_inv, this, mul_comm]

@[to_additive (attr := simp)]
/--
theorem `image_const_div_Ico` / 定理 `image_const_div_Ico`

English:
theorem image_const_div_Ico
  statement: (fun x => a / x) '' Ico b c = Ioc (a / c) (a / b)
  proof: by
  have := image_comp (fun x => a * x) fun x => x⁻¹; dsimp [Function.comp_def] at this
  simp [div_eq_mul_inv, this, mul_comm]

@[to_additive (attr := simp)]

中文:
定理 image_const_div_Ico
  结论: (fun x => a / x) '' Ico b c = Ioc (a / c) (a / b)
  证明: by
  have := image_comp (fun x => a * x) fun x => x⁻¹; dsimp [Function.comp_def] at this
  simp [div_eq_mul_inv, this, mul_comm]

@[to_additive (attr := simp)]

Depends on / 依赖: Function, Function.comp_def, comp_def, div_eq_mul_inv, image_comp, mul_comm
-/
theorem image_const_div_Ico : (fun x => a / x) '' Ico b c = Ioc (a / c) (a / b) := by
  have := image_comp (fun x => a * x) fun x => x⁻¹; dsimp [Function.comp_def] at this
  simp [div_eq_mul_inv, this, mul_comm]

@[to_additive (attr := simp)]
/--
theorem `image_const_div_Ioc` / 定理 `image_const_div_Ioc`

English:
theorem image_const_div_Ioc
  statement: (fun x => a / x) '' Ioc b c = Ico (a / c) (a / b)
  proof: by
  have := image_comp (fun x => a * x) fun x => x⁻¹; dsimp [Function.comp_def] at this
  simp [div_eq_mul_inv, this, mul_comm]

@[to_additive (attr := simp)]

中文:
定理 image_const_div_Ioc
  结论: (fun x => a / x) '' Ioc b c = Ico (a / c) (a / b)
  证明: by
  have := image_comp (fun x => a * x) fun x => x⁻¹; dsimp [Function.comp_def] at this
  simp [div_eq_mul_inv, this, mul_comm]

@[to_additive (attr := simp)]

Depends on / 依赖: Function, Function.comp_def, comp_def, div_eq_mul_inv, image_comp, mul_comm
-/
theorem image_const_div_Ioc : (fun x => a / x) '' Ioc b c = Ico (a / c) (a / b) := by
  have := image_comp (fun x => a * x) fun x => x⁻¹; dsimp [Function.comp_def] at this
  simp [div_eq_mul_inv, this, mul_comm]

@[to_additive (attr := simp)]
/--
theorem `image_const_div_Ioo` / 定理 `image_const_div_Ioo`

English:
theorem image_const_div_Ioo
  statement: (fun x => a / x) '' Ioo b c = Ioo (a / c) (a / b)
  proof: by
  have := image_comp (fun x => a * x) fun x => x⁻¹; dsimp [Function.comp_def] at this
  simp [div_eq_mul_inv, this, mul_comm]

中文:
定理 image_const_div_Ioo
  结论: (fun x => a / x) '' Ioo b c = Ioo (a / c) (a / b)
  证明: by
  have := image_comp (fun x => a * x) fun x => x⁻¹; dsimp [Function.comp_def] at this
  simp [div_eq_mul_inv, this, mul_comm]

Depends on / 依赖: Function, Function.comp_def, comp_def, div_eq_mul_inv, image_comp, mul_comm
-/
theorem image_const_div_Ioo : (fun x => a / x) '' Ioo b c = Ioo (a / c) (a / b) := by
  have := image_comp (fun x => a * x) fun x => x⁻¹; dsimp [Function.comp_def] at this
  simp [div_eq_mul_inv, this, mul_comm]

/-!
### Images under `x ↦ x / a`
-/

@[to_additive (attr := simp)]
/--
theorem `image_div_const_Ici` / 定理 `image_div_const_Ici`

English:
theorem image_div_const_Ici
  statement: (fun x => x / a) '' Ici b = Ici (b / a)
  proof: by simp [div_eq_mul_inv]

@[to_additive (attr := simp)]

中文:
定理 image_div_const_Ici
  结论: (fun x => x / a) '' Ici b = Ici (b / a)
  证明: by simp [div_eq_mul_inv]

@[to_additive (attr := simp)]

Depends on / 依赖: div_eq_mul_inv
-/
theorem image_div_const_Ici : (fun x => x / a) '' Ici b = Ici (b / a) := by simp [div_eq_mul_inv]

@[to_additive (attr := simp)]
/--
theorem `image_div_const_Iic` / 定理 `image_div_const_Iic`

English:
theorem image_div_const_Iic
  statement: (fun x => x / a) '' Iic b = Iic (b / a)
  proof: by simp [div_eq_mul_inv]

@[to_additive (attr := simp)]

中文:
定理 image_div_const_Iic
  结论: (fun x => x / a) '' Iic b = Iic (b / a)
  证明: by simp [div_eq_mul_inv]

@[to_additive (attr := simp)]

Depends on / 依赖: div_eq_mul_inv
-/
theorem image_div_const_Iic : (fun x => x / a) '' Iic b = Iic (b / a) := by simp [div_eq_mul_inv]

@[to_additive (attr := simp)]
/--
theorem `image_div_const_Ioi` / 定理 `image_div_const_Ioi`

English:
theorem image_div_const_Ioi
  statement: (fun x => x / a) '' Ioi b = Ioi (b / a)
  proof: by simp [div_eq_mul_inv]

@[to_additive (attr := simp)]

中文:
定理 image_div_const_Ioi
  结论: (fun x => x / a) '' Ioi b = Ioi (b / a)
  证明: by simp [div_eq_mul_inv]

@[to_additive (attr := simp)]

Depends on / 依赖: div_eq_mul_inv
-/
theorem image_div_const_Ioi : (fun x => x / a) '' Ioi b = Ioi (b / a) := by simp [div_eq_mul_inv]

@[to_additive (attr := simp)]
/--
theorem `image_div_const_Iio` / 定理 `image_div_const_Iio`

English:
theorem image_div_const_Iio
  statement: (fun x => x / a) '' Iio b = Iio (b / a)
  proof: by simp [div_eq_mul_inv]

@[to_additive (attr := simp)]

中文:
定理 image_div_const_Iio
  结论: (fun x => x / a) '' Iio b = Iio (b / a)
  证明: by simp [div_eq_mul_inv]

@[to_additive (attr := simp)]

Depends on / 依赖: div_eq_mul_inv
-/
theorem image_div_const_Iio : (fun x => x / a) '' Iio b = Iio (b / a) := by simp [div_eq_mul_inv]

@[to_additive (attr := simp)]
/--
theorem `image_div_const_Icc` / 定理 `image_div_const_Icc`

English:
theorem image_div_const_Icc
  statement: (fun x => x / a) '' Icc b c = Icc (b / a) (c / a)
  proof: by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]

中文:
定理 image_div_const_Icc
  结论: (fun x => x / a) '' Icc b c = Icc (b / a) (c / a)
  证明: by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]

Depends on / 依赖: div_eq_mul_inv
-/
theorem image_div_const_Icc : (fun x => x / a) '' Icc b c = Icc (b / a) (c / a) := by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]
/--
theorem `image_div_const_Ico` / 定理 `image_div_const_Ico`

English:
theorem image_div_const_Ico
  statement: (fun x => x / a) '' Ico b c = Ico (b / a) (c / a)
  proof: by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]

中文:
定理 image_div_const_Ico
  结论: (fun x => x / a) '' Ico b c = Ico (b / a) (c / a)
  证明: by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]

Depends on / 依赖: div_eq_mul_inv
-/
theorem image_div_const_Ico : (fun x => x / a) '' Ico b c = Ico (b / a) (c / a) := by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]
/--
theorem `image_div_const_Ioc` / 定理 `image_div_const_Ioc`

English:
theorem image_div_const_Ioc
  statement: (fun x => x / a) '' Ioc b c = Ioc (b / a) (c / a)
  proof: by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]

中文:
定理 image_div_const_Ioc
  结论: (fun x => x / a) '' Ioc b c = Ioc (b / a) (c / a)
  证明: by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]

Depends on / 依赖: div_eq_mul_inv
-/
theorem image_div_const_Ioc : (fun x => x / a) '' Ioc b c = Ioc (b / a) (c / a) := by
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]
/--
theorem `image_div_const_Ioo` / 定理 `image_div_const_Ioo`

English:
theorem image_div_const_Ioo
  statement: (fun x => x / a) '' Ioo b c = Ioo (b / a) (c / a)
  proof: by
  simp [div_eq_mul_inv]

中文:
定理 image_div_const_Ioo
  结论: (fun x => x / a) '' Ioo b c = Ioo (b / a) (c / a)
  证明: by
  simp [div_eq_mul_inv]

Depends on / 依赖: div_eq_mul_inv
-/
theorem image_div_const_Ioo : (fun x => x / a) '' Ioo b c = Ioo (b / a) (c / a) := by
  simp [div_eq_mul_inv]

/-!
### Bijections
-/

@[to_additive]
/--
theorem `Iic_mul_bij` / 定理 `Iic_mul_bij`

English:
theorem Iic_mul_bij
  statement: BijOn (· * a) (Iic b) (Iic (b * a))
  proof: image_mul_const_Iic a b ▸ (mul_left_injective _).injOn.bijOn_image

@[to_additive]

中文:
定理 Iic_mul_bij
  结论: BijOn (· * a) (Iic b) (Iic (b * a))
  证明: image_mul_const_Iic a b ▸ (mul_left_injective _).injOn.bijOn_image

@[to_additive]

Depends on / 依赖: bijOn_image, image_mul_const_Iic, injOn.bijOn_image, mul_left_injective
-/
theorem Iic_mul_bij : BijOn (· * a) (Iic b) (Iic (b * a)) :=
  image_mul_const_Iic a b ▸ (mul_left_injective _).injOn.bijOn_image

@[to_additive]
/--
theorem `Iio_mul_bij` / 定理 `Iio_mul_bij`

English:
theorem Iio_mul_bij
  statement: BijOn (· * a) (Iio b) (Iio (b * a))
  proof: image_mul_const_Iio a b ▸ (mul_left_injective _).injOn.bijOn_image

中文:
定理 Iio_mul_bij
  结论: BijOn (· * a) (Iio b) (Iio (b * a))
  证明: image_mul_const_Iio a b ▸ (mul_left_injective _).injOn.bijOn_image

Depends on / 依赖: bijOn_image, image_mul_const_Iio, injOn.bijOn_image, mul_left_injective
-/
theorem Iio_mul_bij : BijOn (· * a) (Iio b) (Iio (b * a)) :=
  image_mul_const_Iio a b ▸ (mul_left_injective _).injOn.bijOn_image

end OrderedCommGroup

section LinearOrderedCommGroup
variable [CommGroup α] [LinearOrder α] [IsOrderedMonoid α]

@[to_additive (attr := simp)]
/--
lemma `inv_uIcc` / 引理 `inv_uIcc`

English:
lemma inv_uIcc
  given: (a b : α)
  statement: [[a, b]]⁻¹ = [[a⁻¹, b⁻¹]]
  proof: by
  simp only [uIcc, inv_Icc, inv_sup, inv_inf]

中文:
引理 inv_uIcc
  条件: (a b : α)
  结论: [[a, b]]⁻¹ = [[a⁻¹, b⁻¹]]
  证明: by
  simp only [uIcc, inv_Icc, inv_sup, inv_inf]

Depends on / 依赖: inv_Icc, inv_inf, inv_sup
-/
lemma inv_uIcc (a b : α) : [[a, b]]⁻¹ = [[a⁻¹, b⁻¹]] := by
  simp only [uIcc, inv_Icc, inv_sup, inv_inf]

end LinearOrderedCommGroup

section LinearOrderedAddCommGroup

variable [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α] (a b c d : α)

@[simp]
/--
theorem `preimage_const_add_uIcc` / 定理 `preimage_const_add_uIcc`

English:
theorem preimage_const_add_uIcc
  statement: (fun x => a + x) ⁻¹' [[b, c]] = [[b - a, c - a]]
  proof: by
  simp only [← Icc_min_max, preimage_const_add_Icc, min_sub_sub_right, max_sub_sub_right]

@[simp]

中文:
定理 preimage_const_add_uIcc
  结论: (fun x => a + x) ⁻¹' [[b, c]] = [[b - a, c - a]]
  证明: by
  simp only [← Icc_min_max, preimage_const_add_Icc, min_sub_sub_right, max_sub_sub_right]

@[simp]

Depends on / 依赖: Icc_min_max, max_sub_sub_right, min_sub_sub_right, preimage_const_add_Icc
-/
theorem preimage_const_add_uIcc : (fun x => a + x) ⁻¹' [[b, c]] = [[b - a, c - a]] := by
  simp only [← Icc_min_max, preimage_const_add_Icc, min_sub_sub_right, max_sub_sub_right]

@[simp]
/--
theorem `preimage_add_const_uIcc` / 定理 `preimage_add_const_uIcc`

English:
theorem preimage_add_const_uIcc
  statement: (fun x => x + a) ⁻¹' [[b, c]] = [[b - a, c - a]]
  proof: by
  simpa only [add_comm] using preimage_const_add_uIcc a b c

@[simp]

中文:
定理 preimage_add_const_uIcc
  结论: (fun x => x + a) ⁻¹' [[b, c]] = [[b - a, c - a]]
  证明: by
  simpa only [add_comm] using preimage_const_add_uIcc a b c

@[simp]

Depends on / 依赖: add_comm, preimage_const_add_uIcc
-/
theorem preimage_add_const_uIcc : (fun x => x + a) ⁻¹' [[b, c]] = [[b - a, c - a]] := by
  simpa only [add_comm] using preimage_const_add_uIcc a b c

@[simp]
/--
theorem `preimage_sub_const_uIcc` / 定理 `preimage_sub_const_uIcc`

English:
theorem preimage_sub_const_uIcc
  statement: (fun x => x - a) ⁻¹' [[b, c]] = [[b + a, c + a]]
  proof: by
  simp [sub_eq_add_neg]

@[simp]

中文:
定理 preimage_sub_const_uIcc
  结论: (fun x => x - a) ⁻¹' [[b, c]] = [[b + a, c + a]]
  证明: by
  simp [sub_eq_add_neg]

@[simp]

Depends on / 依赖: sub_eq_add_neg
-/
theorem preimage_sub_const_uIcc : (fun x => x - a) ⁻¹' [[b, c]] = [[b + a, c + a]] := by
  simp [sub_eq_add_neg]

@[simp]
/--
theorem `preimage_const_sub_uIcc` / 定理 `preimage_const_sub_uIcc`

English:
theorem preimage_const_sub_uIcc
  statement: (fun x => a - x) ⁻¹' [[b, c]] = [[a - b, a - c]]
  proof: by
  simp_rw [← Icc_min_max, preimage_const_sub_Icc]
  simp only [sub_eq_add_neg, min_add_add_left, max_add_add_left, min_neg_neg, max_neg_neg]

中文:
定理 preimage_const_sub_uIcc
  结论: (fun x => a - x) ⁻¹' [[b, c]] = [[a - b, a - c]]
  证明: by
  simp_rw [← Icc_min_max, preimage_const_sub_Icc]
  simp only [sub_eq_add_neg, min_add_add_left, max_add_add_left, min_neg_neg, max_neg_neg]

Depends on / 依赖: Icc_min_max, max_add_add_left, max_neg_neg, min_add_add_left, min_neg_neg, preimage_const_sub_Icc, simp_rw, sub_eq_add_neg
-/
theorem preimage_const_sub_uIcc : (fun x => a - x) ⁻¹' [[b, c]] = [[a - b, a - c]] := by
  simp_rw [← Icc_min_max, preimage_const_sub_Icc]
  simp only [sub_eq_add_neg, min_add_add_left, max_add_add_left, min_neg_neg, max_neg_neg]

-- simp can prove this modulo `add_comm`
/--
theorem `image_const_add_uIcc` / 定理 `image_const_add_uIcc`

English:
theorem image_const_add_uIcc
  statement: (fun x => a + x) '' [[b, c]] = [[a + b, a + c]]
  proof: by simp [add_comm]

中文:
定理 image_const_add_uIcc
  结论: (fun x => a + x) '' [[b, c]] = [[a + b, a + c]]
  证明: by simp [add_comm]

Depends on / 依赖: add_comm
-/
theorem image_const_add_uIcc : (fun x => a + x) '' [[b, c]] = [[a + b, a + c]] := by simp [add_comm]

/--
theorem `image_add_const_uIcc` / 定理 `image_add_const_uIcc`

English:
theorem image_add_const_uIcc
  statement: (fun x => x + a) '' [[b, c]] = [[b + a, c + a]]
  proof: by simp

@[simp]

中文:
定理 image_add_const_uIcc
  结论: (fun x => x + a) '' [[b, c]] = [[b + a, c + a]]
  证明: by simp

@[simp]
-/
theorem image_add_const_uIcc : (fun x => x + a) '' [[b, c]] = [[b + a, c + a]] := by simp

@[simp]
/--
theorem `image_const_sub_uIcc` / 定理 `image_const_sub_uIcc`

English:
theorem image_const_sub_uIcc
  statement: (fun x => a - x) '' [[b, c]] = [[a - b, a - c]]
  proof: by
  have := image_comp (fun x => a + x) fun x => -x; dsimp [Function.comp_def] at this
  simp [sub_eq_add_neg, this, add_comm]

@[simp]

中文:
定理 image_const_sub_uIcc
  结论: (fun x => a - x) '' [[b, c]] = [[a - b, a - c]]
  证明: by
  have := image_comp (fun x => a + x) fun x => -x; dsimp [Function.comp_def] at this
  simp [sub_eq_add_neg, this, add_comm]

@[simp]

Depends on / 依赖: Function, Function.comp_def, add_comm, comp_def, image_comp, sub_eq_add_neg
-/
theorem image_const_sub_uIcc : (fun x => a - x) '' [[b, c]] = [[a - b, a - c]] := by
  have := image_comp (fun x => a + x) fun x => -x; dsimp [Function.comp_def] at this
  simp [sub_eq_add_neg, this, add_comm]

@[simp]
/--
theorem `image_sub_const_uIcc` / 定理 `image_sub_const_uIcc`

English:
theorem image_sub_const_uIcc
  statement: (fun x => x - a) '' [[b, c]] = [[b - a, c - a]]
  proof: by
  simp [sub_eq_add_neg, add_comm]

中文:
定理 image_sub_const_uIcc
  结论: (fun x => x - a) '' [[b, c]] = [[b - a, c - a]]
  证明: by
  simp [sub_eq_add_neg, add_comm]

Depends on / 依赖: add_comm, sub_eq_add_neg
-/
theorem image_sub_const_uIcc : (fun x => x - a) '' [[b, c]] = [[b - a, c - a]] := by
  simp [sub_eq_add_neg, add_comm]

/--
theorem `image_neg_uIcc` / 定理 `image_neg_uIcc`

English:
theorem image_neg_uIcc
  statement: Neg.neg '' [[a, b]] = [[-a, -b]]
  proof: by simp

中文:
定理 image_neg_uIcc
  结论: Neg.neg '' [[a, b]] = [[-a, -b]]
  证明: by simp
-/
theorem image_neg_uIcc : Neg.neg '' [[a, b]] = [[-a, -b]] := by simp

variable {a b c d}

/--
theorem `abs_sub_le_of_uIcc_subset_uIcc` / 定理 `abs_sub_le_of_uIcc_subset_uIcc`

English:
theorem abs_sub_le_of_uIcc_subset_uIcc
  given: (h : [[c, d]] subseteq [[a, b]])
  statement: |d - c| <= |b - a|
  proof: by
  rw [← max_sub_min_eq_abs]; rw [← max_sub_min_eq_abs]
  rw [uIcc_subset_uIcc_iff_le] at h
  exact sub_le_sub h.2 h.1

中文:
定理 abs_sub_le_of_uIcc_subset_uIcc
  条件: (h : [[c, d]] subseteq [[a, b]])
  结论: |d - c| <= |b - a|
  证明: by
  rw [← max_sub_min_eq_abs]; rw [← max_sub_min_eq_abs]
  rw [uIcc_subset_uIcc_iff_le] at h
  exact sub_le_sub h.2 h.1

Depends on / 依赖: max_sub_min_eq_abs, sub_le_sub, uIcc_subset_uIcc_iff_le
-/
theorem abs_sub_le_of_uIcc_subset_uIcc (h : [[c, d]] subseteq [[a, b]]) : |d - c| <= |b - a| := by
  rw [← max_sub_min_eq_abs]; rw [← max_sub_min_eq_abs]
  rw [uIcc_subset_uIcc_iff_le] at h
  exact sub_le_sub h.2 h.1

/--
theorem `abs_sub_left_of_mem_uIcc` / 定理 `abs_sub_left_of_mem_uIcc`

English:
theorem abs_sub_left_of_mem_uIcc
  given: (h : c in [[a, b]])
  statement: |c - a| <= |b - a|
  proof: abs_sub_le_of_uIcc_subset_uIcc uIcc_subset_uIcc_left h

中文:
定理 abs_sub_left_of_mem_uIcc
  条件: (h : c in [[a, b]])
  结论: |c - a| <= |b - a|
  证明: abs_sub_le_of_uIcc_subset_uIcc uIcc_subset_uIcc_left h

Depends on / 依赖: abs_sub_le_of_uIcc_subset_uIcc, uIcc_subset_uIcc_left
-/
theorem abs_sub_left_of_mem_uIcc (h : c in [[a, b]]) : |c - a| <= |b - a| :=
abs_sub_le_of_uIcc_subset_uIcc uIcc_subset_uIcc_left h

/--
theorem `abs_sub_right_of_mem_uIcc` / 定理 `abs_sub_right_of_mem_uIcc`

English:
theorem abs_sub_right_of_mem_uIcc
  given: (h : c in [[a, b]])
  statement: |b - c| <= |b - a|
  proof: abs_sub_le_of_uIcc_subset_uIcc uIcc_subset_uIcc_right h

中文:
定理 abs_sub_right_of_mem_uIcc
  条件: (h : c in [[a, b]])
  结论: |b - c| <= |b - a|
  证明: abs_sub_le_of_uIcc_subset_uIcc uIcc_subset_uIcc_right h

Depends on / 依赖: abs_sub_le_of_uIcc_subset_uIcc, uIcc_subset_uIcc_right
-/
theorem abs_sub_right_of_mem_uIcc (h : c in [[a, b]]) : |b - c| <= |b - a| :=
abs_sub_le_of_uIcc_subset_uIcc uIcc_subset_uIcc_right h

end LinearOrderedAddCommGroup

section GroupWithZero

section MulPos

variable {G₀ : Type*} [GroupWithZero G₀] [PartialOrder G₀] [MulPosReflectLT G₀] {a b c : G₀}

@[simp]
/--
theorem `preimage_mul_const_Iic₀` / 定理 `preimage_mul_const_Iic₀`

English:
theorem preimage_mul_const_Iic₀
  given: (a : G₀) (h : 0 < c)
  statement: (· * c) ⁻¹' Iic a = Iic (a / c)
  proof: by
  simpa only [division_def] using! (OrderIso.mulRight₀ c h).preimage_Iic a

@[simp]

中文:
定理 preimage_mul_const_Iic₀
  条件: (a : G₀) (h : 0 < c)
  结论: (· * c) ⁻¹' Iic a = Iic (a / c)
  证明: by
  simpa only [division_def] using! (OrderIso.mulRight₀ c h).preimage_Iic a

@[simp]

Depends on / 依赖: OrderIso, OrderIso.mulRight, division_def, preimage_Iic
-/
theorem preimage_mul_const_Iic₀ (a : G₀) (h : 0 < c) : (· * c) ⁻¹' Iic a = Iic (a / c) := by
  simpa only [division_def] using! (OrderIso.mulRight₀ c h).preimage_Iic a

@[simp]
/--
theorem `preimage_mul_const_Ici₀` / 定理 `preimage_mul_const_Ici₀`

English:
theorem preimage_mul_const_Ici₀
  given: (a : G₀) (h : 0 < c)
  statement: (· * c) ⁻¹' Ici a = Ici (a / c)
  proof: by
  simpa only [division_def] using! (OrderIso.mulRight₀ c h).preimage_Ici a

@[simp]

中文:
定理 preimage_mul_const_Ici₀
  条件: (a : G₀) (h : 0 < c)
  结论: (· * c) ⁻¹' Ici a = Ici (a / c)
  证明: by
  simpa only [division_def] using! (OrderIso.mulRight₀ c h).preimage_Ici a

@[simp]

Depends on / 依赖: OrderIso, OrderIso.mulRight, division_def, preimage_Ici
-/
theorem preimage_mul_const_Ici₀ (a : G₀) (h : 0 < c) : (· * c) ⁻¹' Ici a = Ici (a / c) := by
  simpa only [division_def] using! (OrderIso.mulRight₀ c h).preimage_Ici a

@[simp]
/--
theorem `preimage_mul_const_Ioi₀` / 定理 `preimage_mul_const_Ioi₀`

English:
theorem preimage_mul_const_Ioi₀
  given: (a : G₀) (h : 0 < c)
  statement: (· * c) ⁻¹' Ioi a = Ioi (a / c)
  proof: by
  simpa only [division_def] using! (OrderIso.mulRight₀ c h).preimage_Ioi a

@[simp]

中文:
定理 preimage_mul_const_Ioi₀
  条件: (a : G₀) (h : 0 < c)
  结论: (· * c) ⁻¹' Ioi a = Ioi (a / c)
  证明: by
  simpa only [division_def] using! (OrderIso.mulRight₀ c h).preimage_Ioi a

@[simp]

Depends on / 依赖: OrderIso, OrderIso.mulRight, division_def, preimage_Ioi
-/
theorem preimage_mul_const_Ioi₀ (a : G₀) (h : 0 < c) : (· * c) ⁻¹' Ioi a = Ioi (a / c) := by
  simpa only [division_def] using! (OrderIso.mulRight₀ c h).preimage_Ioi a

@[simp]
/--
theorem `preimage_mul_const_Iio₀` / 定理 `preimage_mul_const_Iio₀`

English:
theorem preimage_mul_const_Iio₀
  given: (a : G₀) (h : 0 < c)
  statement: (· * c) ⁻¹' Iio a = Iio (a / c)
  proof: by
  simpa only [division_def] using! (OrderIso.mulRight₀ c h).preimage_Iio a

@[simp]

中文:
定理 preimage_mul_const_Iio₀
  条件: (a : G₀) (h : 0 < c)
  结论: (· * c) ⁻¹' Iio a = Iio (a / c)
  证明: by
  simpa only [division_def] using! (OrderIso.mulRight₀ c h).preimage_Iio a

@[simp]

Depends on / 依赖: OrderIso, OrderIso.mulRight, division_def, preimage_Iio
-/
theorem preimage_mul_const_Iio₀ (a : G₀) (h : 0 < c) : (· * c) ⁻¹' Iio a = Iio (a / c) := by
  simpa only [division_def] using! (OrderIso.mulRight₀ c h).preimage_Iio a

@[simp]
/--
theorem `preimage_mul_const_Icc₀` / 定理 `preimage_mul_const_Icc₀`

English:
theorem preimage_mul_const_Icc₀
  given: (a b : G₀) (h : 0 < c)
  proof: by simp [← Ici_inter_Iic, h]

@[simp]

中文:
定理 preimage_mul_const_Icc₀
  条件: (a b : G₀) (h : 0 < c)
  证明: by simp [← Ici_inter_Iic, h]

@[simp]

Depends on / 依赖: Ici_inter_Iic
-/
theorem preimage_mul_const_Icc₀ (a b : G₀) (h : 0 < c) :
    (· * c) ⁻¹' Icc a b = Icc (a / c) (b / c) := by simp [← Ici_inter_Iic, h]

@[simp]
/--
theorem `preimage_mul_const_Ioo₀` / 定理 `preimage_mul_const_Ioo₀`

English:
theorem preimage_mul_const_Ioo₀
  given: (a b : G₀) (h : 0 < c)
  proof: by simp [← Ioi_inter_Iio, h]

@[simp]

中文:
定理 preimage_mul_const_Ioo₀
  条件: (a b : G₀) (h : 0 < c)
  证明: by simp [← Ioi_inter_Iio, h]

@[simp]

Depends on / 依赖: Ioi_inter_Iio
-/
theorem preimage_mul_const_Ioo₀ (a b : G₀) (h : 0 < c) :
    (fun x => x * c) ⁻¹' Ioo a b = Ioo (a / c) (b / c) := by simp [← Ioi_inter_Iio, h]

@[simp]
/--
theorem `preimage_mul_const_Ioc₀` / 定理 `preimage_mul_const_Ioc₀`

English:
theorem preimage_mul_const_Ioc₀
  given: (a b : G₀) (h : 0 < c)
  proof: by simp [← Ioi_inter_Iic, h]

@[simp]

中文:
定理 preimage_mul_const_Ioc₀
  条件: (a b : G₀) (h : 0 < c)
  证明: by simp [← Ioi_inter_Iic, h]

@[simp]

Depends on / 依赖: Ioi_inter_Iic, MulAction, PosSMulMono, PosSMulMono.toPosSMulReflectLE, toPosSMulReflectLE
-/
theorem preimage_mul_const_Ioc₀ (a b : G₀) (h : 0 < c) :
    (fun x => x * c) ⁻¹' Ioc a b = Ioc (a / c) (b / c) := by simp [← Ioi_inter_Iic, h]

@[simp]
/--
theorem `preimage_mul_const_Ico₀` / 定理 `preimage_mul_const_Ico₀`

English:
theorem preimage_mul_const_Ico₀
  given: (a b : G₀) (h : 0 < c)
  proof: by simp [← Ici_inter_Iio, h]

中文:
定理 preimage_mul_const_Ico₀
  条件: (a b : G₀) (h : 0 < c)
  证明: by simp [← Ici_inter_Iio, h]

Depends on / 依赖: Ici_inter_Iio, MulActionWithZero, PosSMulStrictMono, PosSMulStrictMono.toPosSMulReflectLT, toPosSMulReflectLT
-/
theorem preimage_mul_const_Ico₀ (a b : G₀) (h : 0 < c) :
    (fun x => x * c) ⁻¹' Ico a b = Ico (a / c) (b / c) := by simp [← Ici_inter_Iio, h]

/--
theorem `image_mul_right_Icc'` / 定理 `image_mul_right_Icc'`

English:
theorem image_mul_right_Icc'
  given: (a b : G₀) (h : 0 < c)
  proof: (OrderIso.mulRight₀ c h).image_Icc a b

中文:
定理 image_mul_right_Icc'
  条件: (a b : G₀) (h : 0 < c)
  证明: (OrderIso.mulRight₀ c h).image_Icc a b

Depends on / 依赖: OrderIso, OrderIso.mulRight, image_Icc
-/
theorem image_mul_right_Icc' (a b : G₀) (h : 0 < c) :
    (· * c) '' Icc a b = Icc (a * c) (b * c) :=
  (OrderIso.mulRight₀ c h).image_Icc a b

/--
theorem `image_mul_right_Icc` / 定理 `image_mul_right_Icc`

English:
theorem image_mul_right_Icc
  given: (hab : a <= b) (hc : 0 <= c)
  proof: by
  cases eq_or_lt_of_le hc
  · subst c
    simp [(nonempty_Icc.2 hab).image_const]
  exact image_mul_right_Icc' a b ‹0 < c›

中文:
定理 image_mul_right_Icc
  条件: (hab : a <= b) (hc : 0 <= c)
  证明: by
  cases eq_or_lt_of_le hc
  · subst c
    simp [(nonempty_Icc.2 hab).image_const]
  exact image_mul_right_Icc' a b ‹0 < c›

Depends on / 依赖: eq_or_lt_of_le, image_const, image_mul_right_Icc, nonempty_Icc
-/
theorem image_mul_right_Icc (hab : a <= b) (hc : 0 <= c) :
    (· * c) '' Icc a b = Icc (a * c) (b * c) := by
  cases eq_or_lt_of_le hc
  · subst c
    simp [(nonempty_Icc.2 hab).image_const]
  exact image_mul_right_Icc' a b ‹0 < c›

/--
theorem `image_mul_right_Ioo` / 定理 `image_mul_right_Ioo`

English:
theorem image_mul_right_Ioo
  given: (a b : G₀) (h : 0 < c)
  proof: (OrderIso.mulRight₀ c h).image_Ioo a b

中文:
定理 image_mul_right_Ioo
  条件: (a b : G₀) (h : 0 < c)
  证明: (OrderIso.mulRight₀ c h).image_Ioo a b

Depends on / 依赖: OrderIso, OrderIso.mulRight, image_Ioo
-/
theorem image_mul_right_Ioo (a b : G₀) (h : 0 < c) :
    (fun x => x * c) '' Ioo a b = Ioo (a * c) (b * c) :=
  (OrderIso.mulRight₀ c h).image_Ioo a b

/--
theorem `image_mul_right_Ico` / 定理 `image_mul_right_Ico`

English:
theorem image_mul_right_Ico
  given: (a b : G₀) (h : 0 < c)
  proof: (OrderIso.mulRight₀ c h).image_Ico a b

中文:
定理 image_mul_right_Ico
  条件: (a b : G₀) (h : 0 < c)
  证明: (OrderIso.mulRight₀ c h).image_Ico a b

Depends on / 依赖: OrderIso, OrderIso.mulRight, image_Ico
-/
theorem image_mul_right_Ico (a b : G₀) (h : 0 < c) :
    (fun x => x * c) '' Ico a b = Ico (a * c) (b * c) :=
  (OrderIso.mulRight₀ c h).image_Ico a b

/--
theorem `image_mul_right_Ioc` / 定理 `image_mul_right_Ioc`

English:
theorem image_mul_right_Ioc
  given: (a b : G₀) (h : 0 < c)
  proof: (OrderIso.mulRight₀ c h).image_Ioc a b

中文:
定理 image_mul_right_Ioc
  条件: (a b : G₀) (h : 0 < c)
  证明: (OrderIso.mulRight₀ c h).image_Ioc a b

Depends on / 依赖: OrderIso, OrderIso.mulRight, image_Ioc
-/
theorem image_mul_right_Ioc (a b : G₀) (h : 0 < c) :
    (fun x => x * c) '' Ioc a b = Ioc (a * c) (b * c) :=
  (OrderIso.mulRight₀ c h).image_Ioc a b

end MulPos

section PosMul

variable {G₀ : Type*} [GroupWithZero G₀] [PartialOrder G₀] [PosMulReflectLT G₀] {a b c : G₀}

/--
theorem `image_mul_left_Ici` / 定理 `image_mul_left_Ici`

English:
theorem image_mul_left_Ici
  given: (h : 0 < a) (b : G₀)
  statement: (a * ·) '' Ici b = Ici (a * b)
  proof: (OrderIso.mulLeft₀ a h).image_Ici b

中文:
定理 image_mul_left_Ici
  条件: (h : 0 < a) (b : G₀)
  结论: (a * ·) '' Ici b = Ici (a * b)
  证明: (OrderIso.mulLeft₀ a h).image_Ici b

Depends on / 依赖: OrderIso, OrderIso.mulLeft, image_Ici
-/
theorem image_mul_left_Ici (h : 0 < a) (b : G₀) : (a * ·) '' Ici b = Ici (a * b) :=
  (OrderIso.mulLeft₀ a h).image_Ici b

/--
theorem `image_mul_left_Iic` / 定理 `image_mul_left_Iic`

English:
theorem image_mul_left_Iic
  given: (h : 0 < a) (b : G₀)
  statement: (a * ·) '' Iic b = Iic (a * b)
  proof: (OrderIso.mulLeft₀ a h).image_Iic b

中文:
定理 image_mul_left_Iic
  条件: (h : 0 < a) (b : G₀)
  结论: (a * ·) '' Iic b = Iic (a * b)
  证明: (OrderIso.mulLeft₀ a h).image_Iic b

Depends on / 依赖: OrderIso, OrderIso.mulLeft, image_Iic
-/
theorem image_mul_left_Iic (h : 0 < a) (b : G₀) : (a * ·) '' Iic b = Iic (a * b) :=
  (OrderIso.mulLeft₀ a h).image_Iic b

/--
theorem `image_mul_left_Ioi` / 定理 `image_mul_left_Ioi`

English:
theorem image_mul_left_Ioi
  given: (h : 0 < a) (b : G₀)
  statement: (a * ·) '' Ioi b = Ioi (a * b)
  proof: (OrderIso.mulLeft₀ a h).image_Ioi b

中文:
定理 image_mul_left_Ioi
  条件: (h : 0 < a) (b : G₀)
  结论: (a * ·) '' Ioi b = Ioi (a * b)
  证明: (OrderIso.mulLeft₀ a h).image_Ioi b

Depends on / 依赖: OrderIso, OrderIso.mulLeft, image_Ioi
-/
theorem image_mul_left_Ioi (h : 0 < a) (b : G₀) : (a * ·) '' Ioi b = Ioi (a * b) :=
  (OrderIso.mulLeft₀ a h).image_Ioi b

/--
theorem `image_mul_left_Iio` / 定理 `image_mul_left_Iio`

English:
theorem image_mul_left_Iio
  given: (h : 0 < a) (b : G₀)
  statement: (a * ·) '' Iio b = Iio (a * b)
  proof: (OrderIso.mulLeft₀ a h).image_Iio b

中文:
定理 image_mul_left_Iio
  条件: (h : 0 < a) (b : G₀)
  结论: (a * ·) '' Iio b = Iio (a * b)
  证明: (OrderIso.mulLeft₀ a h).image_Iio b

Depends on / 依赖: OrderIso, OrderIso.mulLeft, image_Iio
-/
theorem image_mul_left_Iio (h : 0 < a) (b : G₀) : (a * ·) '' Iio b = Iio (a * b) :=
  (OrderIso.mulLeft₀ a h).image_Iio b

/--
theorem `image_mul_left_Icc'` / 定理 `image_mul_left_Icc'`

English:
theorem image_mul_left_Icc'
  given: (h : 0 < a) (b c : G₀)
  proof: (OrderIso.mulLeft₀ a h).image_Icc b c

中文:
定理 image_mul_left_Icc'
  条件: (h : 0 < a) (b c : G₀)
  证明: (OrderIso.mulLeft₀ a h).image_Icc b c

Depends on / 依赖: OrderIso, OrderIso.mulLeft, image_Icc
-/
theorem image_mul_left_Icc' (h : 0 < a) (b c : G₀) :
    (a * ·) '' Icc b c = Icc (a * b) (a * c) :=
  (OrderIso.mulLeft₀ a h).image_Icc b c

/--
theorem `image_mul_left_Icc` / 定理 `image_mul_left_Icc`

English:
theorem image_mul_left_Icc
  given: (ha : 0 <= a) (hbc : b <= c)
  proof: by
  rcases ha.eq_or_lt with rfl | ha
  · simp [(nonempty_Icc.2 hbc).image_const]
  · exact image_mul_left_Icc' ha b c

中文:
定理 image_mul_left_Icc
  条件: (ha : 0 <= a) (hbc : b <= c)
  证明: by
  rcases ha.eq_or_lt with rfl | ha
  · simp [(nonempty_Icc.2 hbc).image_const]
  · exact image_mul_left_Icc' ha b c

Depends on / 依赖: eq_or_lt, ha.eq_or_lt, image_const, image_mul_left_Icc, nonempty_Icc
-/
theorem image_mul_left_Icc (ha : 0 <= a) (hbc : b <= c) :
    (a * ·) '' Icc b c = Icc (a * b) (a * c) := by
  rcases ha.eq_or_lt with rfl | ha
  · simp [(nonempty_Icc.2 hbc).image_const]
  · exact image_mul_left_Icc' ha b c

/--
theorem `image_mul_left_Ioo` / 定理 `image_mul_left_Ioo`

English:
theorem image_mul_left_Ioo
  given: (h : 0 < a) (b c : G₀)
  statement: (a * ·) '' Ioo b c = Ioo (a * b) (a * c)
  proof: (OrderIso.mulLeft₀ a h).image_Ioo b c

中文:
定理 image_mul_left_Ioo
  条件: (h : 0 < a) (b c : G₀)
  结论: (a * ·) '' Ioo b c = Ioo (a * b) (a * c)
  证明: (OrderIso.mulLeft₀ a h).image_Ioo b c

Depends on / 依赖: OrderIso, OrderIso.mulLeft, image_Ioo
-/
theorem image_mul_left_Ioo (h : 0 < a) (b c : G₀) : (a * ·) '' Ioo b c = Ioo (a * b) (a * c) :=
  (OrderIso.mulLeft₀ a h).image_Ioo b c

/--
theorem `image_mul_left_Ico` / 定理 `image_mul_left_Ico`

English:
theorem image_mul_left_Ico
  given: (h : 0 < a) (b c : G₀)
  proof: (OrderIso.mulLeft₀ a h).image_Ico b c

中文:
定理 image_mul_left_Ico
  条件: (h : 0 < a) (b c : G₀)
  证明: (OrderIso.mulLeft₀ a h).image_Ico b c

Depends on / 依赖: OrderIso, OrderIso.mulLeft, image_Ico
-/
theorem image_mul_left_Ico (h : 0 < a) (b c : G₀) :
    (a * ·) '' Ico b c = Ico (a * b) (a * c) :=
  (OrderIso.mulLeft₀ a h).image_Ico b c

/--
theorem `image_mul_left_Ioc` / 定理 `image_mul_left_Ioc`

English:
theorem image_mul_left_Ioc
  given: (h : 0 < a) (b c : G₀)
  proof: (OrderIso.mulLeft₀ a h).image_Ioc b c

中文:
定理 image_mul_left_Ioc
  条件: (h : 0 < a) (b c : G₀)
  证明: (OrderIso.mulLeft₀ a h).image_Ioc b c

Depends on / 依赖: OrderIso, OrderIso.mulLeft, image_Ioc
-/
theorem image_mul_left_Ioc (h : 0 < a) (b c : G₀) :
    (a * ·) '' Ioc b c = Ioc (a * b) (a * c) :=
  (OrderIso.mulLeft₀ a h).image_Ioc b c

/--
theorem `image_const_mul_Ioi_zero` / 定理 `image_const_mul_Ioi_zero`

English:
theorem image_const_mul_Ioi_zero
  given: (ha : 0 < a)
  proof: by
  rw [image_mul_left_Ioi ha]; rw [mul_zero]

中文:
定理 image_const_mul_Ioi_zero
  条件: (ha : 0 < a)
  证明: by
  rw [image_mul_left_Ioi ha]; rw [mul_zero]

Depends on / 依赖: image_mul_left_Ioi, mul_zero
-/
theorem image_const_mul_Ioi_zero (ha : 0 < a) :
    (a * ·) '' Ioi 0 = Ioi 0 := by
  rw [image_mul_left_Ioi ha]; rw [mul_zero]

end PosMul

variable {G₀ : Type*} [GroupWithZero G₀] [PartialOrder G₀] [PosMulReflectLT G₀]
  [MulPosReflectLT G₀] {a : G₀}

/--
theorem `inv_Ioo_0_left` / 定理 `inv_Ioo_0_left`

English:
theorem inv_Ioo_0_left
  given: (ha : 0 < a)
  statement: (Ioo 0 a)⁻¹ = Ioi a⁻¹
  proof: by
  ext x
  exact ⟨fun h => inv_lt_of_inv_lt₀ (inv_pos.1 h.1) h.2,
fun h => ⟨inv_pos.2 (inv_pos.2 ha).trans h, inv_lt_of_inv_lt₀ ha h⟩⟩

中文:
定理 inv_Ioo_0_left
  条件: (ha : 0 < a)
  结论: (Ioo 0 a)⁻¹ = Ioi a⁻¹
  证明: by
  ext x
  exact ⟨fun h => inv_lt_of_inv_lt₀ (inv_pos.1 h.1) h.2,
fun h => ⟨inv_pos.2 (inv_pos.2 ha).trans h, inv_lt_of_inv_lt₀ ha h⟩⟩

Depends on / 依赖: inv_pos
-/
theorem inv_Ioo_0_left (ha : 0 < a) : (Ioo 0 a)⁻¹ = Ioi a⁻¹ := by
  ext x
  exact ⟨fun h => inv_lt_of_inv_lt₀ (inv_pos.1 h.1) h.2,
fun h => ⟨inv_pos.2 (inv_pos.2 ha).trans h, inv_lt_of_inv_lt₀ ha h⟩⟩

/--
theorem `inv_Ioi₀` / 定理 `inv_Ioi₀`

English:
theorem inv_Ioi₀
  given: (ha : 0 < a)
  statement: (Ioi a)⁻¹ = Ioo 0 a⁻¹
  proof: by
  rw [inv_eq_iff_eq_inv]; rw [inv_Ioo_0_left (inv_pos.2 ha)]; rw [inv_inv]

中文:
定理 inv_Ioi₀
  条件: (ha : 0 < a)
  结论: (Ioi a)⁻¹ = Ioo 0 a⁻¹
  证明: by
  rw [inv_eq_iff_eq_inv]; rw [inv_Ioo_0_left (inv_pos.2 ha)]; rw [inv_inv]

Depends on / 依赖: inv_Ioo_0_left, inv_eq_iff_eq_inv, inv_inv, inv_pos
-/
theorem inv_Ioi₀ (ha : 0 < a) : (Ioi a)⁻¹ = Ioo 0 a⁻¹ := by
  rw [inv_eq_iff_eq_inv]; rw [inv_Ioo_0_left (inv_pos.2 ha)]; rw [inv_inv]

end GroupWithZero

/-!
### Commutative group with zero

The only reason why we need `G₀` to be commutative in this section
is that we write `a / c`, not `c⁻¹ * a`.

TODO: decide if we should reformulate the lemmas in terms of `c⁻¹ * a`
instead of depending on commutativity.
-/

section CommGroupWithZero

variable {G₀ : Type*} [CommGroupWithZero G₀] [PartialOrder G₀] [PosMulReflectLT G₀] {a b c : G₀}

@[simp]
/--
theorem `preimage_const_mul_Iic₀` / 定理 `preimage_const_mul_Iic₀`

English:
theorem preimage_const_mul_Iic₀
  given: (a : G₀) (h : 0 < c)
  statement: (c * ·) ⁻¹' Iic a = Iic (a / c)
  proof: ext fun _x => (le_div_iff₀' h).symm

@[simp]

中文:
定理 preimage_const_mul_Iic₀
  条件: (a : G₀) (h : 0 < c)
  结论: (c * ·) ⁻¹' Iic a = Iic (a / c)
  证明: ext fun _x => (le_div_iff₀' h).symm

@[simp]
-/
theorem preimage_const_mul_Iic₀ (a : G₀) (h : 0 < c) : (c * ·) ⁻¹' Iic a = Iic (a / c) :=
  ext fun _x => (le_div_iff₀' h).symm

@[simp]
/--
theorem `preimage_const_mul_Ici₀` / 定理 `preimage_const_mul_Ici₀`

English:
theorem preimage_const_mul_Ici₀
  given: (a : G₀) (h : 0 < c)
  statement: (c * ·) ⁻¹' Ici a = Ici (a / c)
  proof: ext fun _x => (div_le_iff₀' h).symm

@[simp]

中文:
定理 preimage_const_mul_Ici₀
  条件: (a : G₀) (h : 0 < c)
  结论: (c * ·) ⁻¹' Ici a = Ici (a / c)
  证明: ext fun _x => (div_le_iff₀' h).symm

@[simp]
-/
theorem preimage_const_mul_Ici₀ (a : G₀) (h : 0 < c) : (c * ·) ⁻¹' Ici a = Ici (a / c) :=
  ext fun _x => (div_le_iff₀' h).symm

@[simp]
/--
theorem `preimage_const_mul_Icc₀` / 定理 `preimage_const_mul_Icc₀`

English:
theorem preimage_const_mul_Icc₀
  given: (a b : G₀) {c : G₀} (h : 0 < c)
  proof: by simp [← Ici_inter_Iic, h]

@[simp]

中文:
定理 preimage_const_mul_Icc₀
  条件: (a b : G₀) {c : G₀} (h : 0 < c)
  证明: by simp [← Ici_inter_Iic, h]

@[simp]

Depends on / 依赖: Ici_inter_Iic
-/
theorem preimage_const_mul_Icc₀ (a b : G₀) {c : G₀} (h : 0 < c) :
    (c * ·) ⁻¹' Icc a b = Icc (a / c) (b / c) := by simp [← Ici_inter_Iic, h]

@[simp]
/--
theorem `preimage_const_mul_Iio₀` / 定理 `preimage_const_mul_Iio₀`

English:
theorem preimage_const_mul_Iio₀
  given: (a : G₀) (h : 0 < c)
  statement: (c * ·) ⁻¹' Iio a = Iio (a / c)
  proof: ext fun _x => (lt_div_iff₀' h).symm

@[simp]

中文:
定理 preimage_const_mul_Iio₀
  条件: (a : G₀) (h : 0 < c)
  结论: (c * ·) ⁻¹' Iio a = Iio (a / c)
  证明: ext fun _x => (lt_div_iff₀' h).symm

@[simp]
-/
theorem preimage_const_mul_Iio₀ (a : G₀) (h : 0 < c) : (c * ·) ⁻¹' Iio a = Iio (a / c) :=
  ext fun _x => (lt_div_iff₀' h).symm

@[simp]
/--
theorem `preimage_const_mul_Ioi₀` / 定理 `preimage_const_mul_Ioi₀`

English:
theorem preimage_const_mul_Ioi₀
  given: (a : G₀) (h : 0 < c)
  statement: (c * ·) ⁻¹' Ioi a = Ioi (a / c)
  proof: ext fun _x => (div_lt_iff₀' h).symm

@[simp]

中文:
定理 preimage_const_mul_Ioi₀
  条件: (a : G₀) (h : 0 < c)
  结论: (c * ·) ⁻¹' Ioi a = Ioi (a / c)
  证明: ext fun _x => (div_lt_iff₀' h).symm

@[simp]
-/
theorem preimage_const_mul_Ioi₀ (a : G₀) (h : 0 < c) : (c * ·) ⁻¹' Ioi a = Ioi (a / c) :=
  ext fun _x => (div_lt_iff₀' h).symm

@[simp]
/--
theorem `preimage_const_mul_Ioo₀` / 定理 `preimage_const_mul_Ioo₀`

English:
theorem preimage_const_mul_Ioo₀
  given: (a b : G₀) (h : 0 < c)
  proof: by simp [← Ioi_inter_Iio, h]

@[simp]

中文:
定理 preimage_const_mul_Ioo₀
  条件: (a b : G₀) (h : 0 < c)
  证明: by simp [← Ioi_inter_Iio, h]

@[simp]

Depends on / 依赖: Ioi_inter_Iio
-/
theorem preimage_const_mul_Ioo₀ (a b : G₀) (h : 0 < c) :
    (c * ·) ⁻¹' Ioo a b = Ioo (a / c) (b / c) := by simp [← Ioi_inter_Iio, h]

@[simp]
/--
theorem `preimage_const_mul_Ioc₀` / 定理 `preimage_const_mul_Ioc₀`

English:
theorem preimage_const_mul_Ioc₀
  given: (a b : G₀) (h : 0 < c)
  proof: by simp [← Ioi_inter_Iic, h]

@[simp]

中文:
定理 preimage_const_mul_Ioc₀
  条件: (a b : G₀) (h : 0 < c)
  证明: by simp [← Ioi_inter_Iic, h]

@[simp]

Depends on / 依赖: Ioi_inter_Iic
-/
theorem preimage_const_mul_Ioc₀ (a b : G₀) (h : 0 < c) :
    (c * ·) ⁻¹' Ioc a b = Ioc (a / c) (b / c) := by simp [← Ioi_inter_Iic, h]

@[simp]
/--
theorem `preimage_const_mul_Ico₀` / 定理 `preimage_const_mul_Ico₀`

English:
theorem preimage_const_mul_Ico₀
  given: (a b : G₀) (h : 0 < c)
  proof: by simp [← Ici_inter_Iio, h]

中文:
定理 preimage_const_mul_Ico₀
  条件: (a b : G₀) (h : 0 < c)
  证明: by simp [← Ici_inter_Iio, h]

Depends on / 依赖: Ici_inter_Iio
-/
theorem preimage_const_mul_Ico₀ (a b : G₀) (h : 0 < c) :
    (c * ·) ⁻¹' Ico a b = Ico (a / c) (b / c) := by simp [← Ici_inter_Iio, h]

end CommGroupWithZero

/-!
### Images under `x ↦ a * x + b` in a semifield
-/

section OrderedSemifield

variable {K : Type*} [DivisionSemiring K] [PartialOrder K] [PosMulReflectLT K]
  [IsOrderedCancelAddMonoid K] [ExistsAddOfLE K] {a : K}

@[simp]
/--
theorem `image_affine_Icc'` / 定理 `image_affine_Icc'`

English:
theorem image_affine_Icc'
  given: (h : 0 < a) (b c d : K)
  proof: by
  suffices (· + b) '' (a * ·) '' Icc c d = Icc (a * c + b) (a * d + b) by
    rwa [Set.image_image] at this
  rw [image_mul_left_Icc' h]; rw [image_add_const_Icc]

@[simp]

中文:
定理 image_affine_Icc'
  条件: (h : 0 < a) (b c d : K)
  证明: by
  suffices (· + b) '' (a * ·) '' Icc c d = Icc (a * c + b) (a * d + b) by
    rwa [Set.image_image] at this
  rw [image_mul_left_Icc' h]; rw [image_add_const_Icc]

@[simp]

Depends on / 依赖: Set.image_image, image_add_const_Icc, image_image, image_mul_left_Icc
-/
theorem image_affine_Icc' (h : 0 < a) (b c d : K) :
    (a * · + b) '' Icc c d = Icc (a * c + b) (a * d + b) := by
  suffices (· + b) '' (a * ·) '' Icc c d = Icc (a * c + b) (a * d + b) by
    rwa [Set.image_image] at this
  rw [image_mul_left_Icc' h]; rw [image_add_const_Icc]

@[simp]
/--
theorem `image_affine_Ico` / 定理 `image_affine_Ico`

English:
theorem image_affine_Ico
  given: (h : 0 < a) (b c d : K)
  proof: by
  suffices (· + b) '' (a * ·) '' Ico c d = Ico (a * c + b) (a * d + b) by
    rwa [Set.image_image] at this
  rw [image_mul_left_Ico h]; rw [image_add_const_Ico]

@[simp]

中文:
定理 image_affine_Ico
  条件: (h : 0 < a) (b c d : K)
  证明: by
  suffices (· + b) '' (a * ·) '' Ico c d = Ico (a * c + b) (a * d + b) by
    rwa [Set.image_image] at this
  rw [image_mul_left_Ico h]; rw [image_add_const_Ico]

@[simp]

Depends on / 依赖: Set.image_image, image_add_const_Ico, image_image, image_mul_left_Ico
-/
theorem image_affine_Ico (h : 0 < a) (b c d : K) :
    (a * · + b) '' Ico c d = Ico (a * c + b) (a * d + b) := by
  suffices (· + b) '' (a * ·) '' Ico c d = Ico (a * c + b) (a * d + b) by
    rwa [Set.image_image] at this
  rw [image_mul_left_Ico h]; rw [image_add_const_Ico]

@[simp]
/--
theorem `image_affine_Ioc` / 定理 `image_affine_Ioc`

English:
theorem image_affine_Ioc
  given: (h : 0 < a) (b c d : K)
  proof: by
  suffices (· + b) '' (a * ·) '' Ioc c d = Ioc (a * c + b) (a * d + b) by
    rwa [Set.image_image] at this
  rw [image_mul_left_Ioc h]; rw [image_add_const_Ioc]

@[simp]

中文:
定理 image_affine_Ioc
  条件: (h : 0 < a) (b c d : K)
  证明: by
  suffices (· + b) '' (a * ·) '' Ioc c d = Ioc (a * c + b) (a * d + b) by
    rwa [Set.image_image] at this
  rw [image_mul_left_Ioc h]; rw [image_add_const_Ioc]

@[simp]

Depends on / 依赖: Set.image_image, image_add_const_Ioc, image_image, image_mul_left_Ioc
-/
theorem image_affine_Ioc (h : 0 < a) (b c d : K) :
    (a * · + b) '' Ioc c d = Ioc (a * c + b) (a * d + b) := by
  suffices (· + b) '' (a * ·) '' Ioc c d = Ioc (a * c + b) (a * d + b) by
    rwa [Set.image_image] at this
  rw [image_mul_left_Ioc h]; rw [image_add_const_Ioc]

@[simp]
/--
theorem `image_affine_Ioo` / 定理 `image_affine_Ioo`

English:
theorem image_affine_Ioo
  given: (h : 0 < a) (b c d : K)
  proof: by
  suffices (· + b) '' (a * ·) '' Ioo c d = Ioo (a * c + b) (a * d + b) by
    rwa [Set.image_image] at this
  rw [image_mul_left_Ioo h]; rw [image_add_const_Ioo]

中文:
定理 image_affine_Ioo
  条件: (h : 0 < a) (b c d : K)
  证明: by
  suffices (· + b) '' (a * ·) '' Ioo c d = Ioo (a * c + b) (a * d + b) by
    rwa [Set.image_image] at this
  rw [image_mul_left_Ioo h]; rw [image_add_const_Ioo]

Depends on / 依赖: Set.image_image, image_add_const_Ioo, image_image, image_mul_left_Ioo
-/
theorem image_affine_Ioo (h : 0 < a) (b c d : K) :
    (a * · + b) '' Ioo c d = Ioo (a * c + b) (a * d + b) := by
  suffices (· + b) '' (a * ·) '' Ioo c d = Ioo (a * c + b) (a * d + b) by
    rwa [Set.image_image] at this
  rw [image_mul_left_Ioo h]; rw [image_add_const_Ioo]

end OrderedSemifield

/-!
### Multiplication and inverse in a field
-/

section LinearOrderedField

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a : α}

@[simp]
/--
theorem `preimage_mul_const_Iio_of_neg` / 定理 `preimage_mul_const_Iio_of_neg`

English:
theorem preimage_mul_const_Iio_of_neg
  given: (a : α) {c : α} (h : c < 0)
  proof: ext fun _x => (div_lt_iff_of_neg h).symm

@[simp]

中文:
定理 preimage_mul_const_Iio_of_neg
  条件: (a : α) {c : α} (h : c < 0)
  证明: ext fun _x => (div_lt_iff_of_neg h).symm

@[simp]

Depends on / 依赖: div_lt_iff_of_neg
-/
theorem preimage_mul_const_Iio_of_neg (a : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Iio a = Ioi (a / c) :=
  ext fun _x => (div_lt_iff_of_neg h).symm

@[simp]
/--
theorem `preimage_mul_const_Ioi_of_neg` / 定理 `preimage_mul_const_Ioi_of_neg`

English:
theorem preimage_mul_const_Ioi_of_neg
  given: (a : α) {c : α} (h : c < 0)
  proof: ext fun _x => (lt_div_iff_of_neg h).symm

@[simp]

中文:
定理 preimage_mul_const_Ioi_of_neg
  条件: (a : α) {c : α} (h : c < 0)
  证明: ext fun _x => (lt_div_iff_of_neg h).symm

@[simp]

Depends on / 依赖: lt_div_iff_of_neg
-/
theorem preimage_mul_const_Ioi_of_neg (a : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Ioi a = Iio (a / c) :=
  ext fun _x => (lt_div_iff_of_neg h).symm

@[simp]
/--
theorem `preimage_mul_const_Iic_of_neg` / 定理 `preimage_mul_const_Iic_of_neg`

English:
theorem preimage_mul_const_Iic_of_neg
  given: (a : α) {c : α} (h : c < 0)
  proof: ext fun _x => (div_le_iff_of_neg h).symm

@[simp]

中文:
定理 preimage_mul_const_Iic_of_neg
  条件: (a : α) {c : α} (h : c < 0)
  证明: ext fun _x => (div_le_iff_of_neg h).symm

@[simp]

Depends on / 依赖: div_le_iff_of_neg
-/
theorem preimage_mul_const_Iic_of_neg (a : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Iic a = Ici (a / c) :=
  ext fun _x => (div_le_iff_of_neg h).symm

@[simp]
/--
theorem `preimage_mul_const_Ici_of_neg` / 定理 `preimage_mul_const_Ici_of_neg`

English:
theorem preimage_mul_const_Ici_of_neg
  given: (a : α) {c : α} (h : c < 0)
  proof: ext fun _x => (le_div_iff_of_neg h).symm

@[simp]

中文:
定理 preimage_mul_const_Ici_of_neg
  条件: (a : α) {c : α} (h : c < 0)
  证明: ext fun _x => (le_div_iff_of_neg h).symm

@[simp]

Depends on / 依赖: le_div_iff_of_neg
-/
theorem preimage_mul_const_Ici_of_neg (a : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Ici a = Iic (a / c) :=
  ext fun _x => (le_div_iff_of_neg h).symm

@[simp]
/--
theorem `preimage_mul_const_Ioo_of_neg` / 定理 `preimage_mul_const_Ioo_of_neg`

English:
theorem preimage_mul_const_Ioo_of_neg
  given: (a b : α) {c : α} (h : c < 0)
  proof: by simp [← Ioi_inter_Iio, h, inter_comm]

@[simp]

中文:
定理 preimage_mul_const_Ioo_of_neg
  条件: (a b : α) {c : α} (h : c < 0)
  证明: by simp [← Ioi_inter_Iio, h, inter_comm]

@[simp]

Depends on / 依赖: Ioi_inter_Iio, inter_comm
-/
theorem preimage_mul_const_Ioo_of_neg (a b : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Ioo a b = Ioo (b / c) (a / c) := by simp [← Ioi_inter_Iio, h, inter_comm]

@[simp]
/--
theorem `preimage_mul_const_Ioc_of_neg` / 定理 `preimage_mul_const_Ioc_of_neg`

English:
theorem preimage_mul_const_Ioc_of_neg
  given: (a b : α) {c : α} (h : c < 0)
  proof: by
  simp [← Ioi_inter_Iic, ← Ici_inter_Iio, h, inter_comm]

@[simp]

中文:
定理 preimage_mul_const_Ioc_of_neg
  条件: (a b : α) {c : α} (h : c < 0)
  证明: by
  simp [← Ioi_inter_Iic, ← Ici_inter_Iio, h, inter_comm]

@[simp]

Depends on / 依赖: Ici_inter_Iio, Ioi_inter_Iic, inter_comm
-/
theorem preimage_mul_const_Ioc_of_neg (a b : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Ioc a b = Ico (b / c) (a / c) := by
  simp [← Ioi_inter_Iic, ← Ici_inter_Iio, h, inter_comm]

@[simp]
/--
theorem `preimage_mul_const_Ico_of_neg` / 定理 `preimage_mul_const_Ico_of_neg`

English:
theorem preimage_mul_const_Ico_of_neg
  given: (a b : α) {c : α} (h : c < 0)
  proof: by
  simp [← Ici_inter_Iio, ← Ioi_inter_Iic, h, inter_comm]

@[simp]

中文:
定理 preimage_mul_const_Ico_of_neg
  条件: (a b : α) {c : α} (h : c < 0)
  证明: by
  simp [← Ici_inter_Iio, ← Ioi_inter_Iic, h, inter_comm]

@[simp]

Depends on / 依赖: Ici_inter_Iio, Ioi_inter_Iic, inter_comm
-/
theorem preimage_mul_const_Ico_of_neg (a b : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Ico a b = Ioc (b / c) (a / c) := by
  simp [← Ici_inter_Iio, ← Ioi_inter_Iic, h, inter_comm]

@[simp]
/--
theorem `preimage_mul_const_Icc_of_neg` / 定理 `preimage_mul_const_Icc_of_neg`

English:
theorem preimage_mul_const_Icc_of_neg
  given: (a b : α) {c : α} (h : c < 0)
  proof: by simp [← Ici_inter_Iic, h, inter_comm]

@[simp]

中文:
定理 preimage_mul_const_Icc_of_neg
  条件: (a b : α) {c : α} (h : c < 0)
  证明: by simp [← Ici_inter_Iic, h, inter_comm]

@[simp]

Depends on / 依赖: Ici_inter_Iic, inter_comm
-/
theorem preimage_mul_const_Icc_of_neg (a b : α) {c : α} (h : c < 0) :
    (fun x => x * c) ⁻¹' Icc a b = Icc (b / c) (a / c) := by simp [← Ici_inter_Iic, h, inter_comm]

@[simp]
/--
theorem `preimage_const_mul_Iio_of_neg` / 定理 `preimage_const_mul_Iio_of_neg`

English:
theorem preimage_const_mul_Iio_of_neg
  given: (a : α) {c : α} (h : c < 0)
  proof: by
  simpa only [mul_comm] using preimage_mul_const_Iio_of_neg a h

@[simp]

中文:
定理 preimage_const_mul_Iio_of_neg
  条件: (a : α) {c : α} (h : c < 0)
  证明: by
  simpa only [mul_comm] using preimage_mul_const_Iio_of_neg a h

@[simp]

Depends on / 依赖: mul_comm, preimage_mul_const_Iio_of_neg
-/
theorem preimage_const_mul_Iio_of_neg (a : α) {c : α} (h : c < 0) :
    (c * ·) ⁻¹' Iio a = Ioi (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Iio_of_neg a h

@[simp]
/--
theorem `preimage_const_mul_Ioi_of_neg` / 定理 `preimage_const_mul_Ioi_of_neg`

English:
theorem preimage_const_mul_Ioi_of_neg
  given: (a : α) {c : α} (h : c < 0)
  proof: by
  simpa only [mul_comm] using preimage_mul_const_Ioi_of_neg a h

@[simp]

中文:
定理 preimage_const_mul_Ioi_of_neg
  条件: (a : α) {c : α} (h : c < 0)
  证明: by
  simpa only [mul_comm] using preimage_mul_const_Ioi_of_neg a h

@[simp]

Depends on / 依赖: mul_comm, preimage_mul_const_Ioi_of_neg
-/
theorem preimage_const_mul_Ioi_of_neg (a : α) {c : α} (h : c < 0) :
    (c * ·) ⁻¹' Ioi a = Iio (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Ioi_of_neg a h

@[simp]
/--
theorem `preimage_const_mul_Iic_of_neg` / 定理 `preimage_const_mul_Iic_of_neg`

English:
theorem preimage_const_mul_Iic_of_neg
  given: (a : α) {c : α} (h : c < 0)
  proof: by
  simpa only [mul_comm] using preimage_mul_const_Iic_of_neg a h

@[simp]

中文:
定理 preimage_const_mul_Iic_of_neg
  条件: (a : α) {c : α} (h : c < 0)
  证明: by
  simpa only [mul_comm] using preimage_mul_const_Iic_of_neg a h

@[simp]

Depends on / 依赖: mul_comm, preimage_mul_const_Iic_of_neg
-/
theorem preimage_const_mul_Iic_of_neg (a : α) {c : α} (h : c < 0) :
    (c * ·) ⁻¹' Iic a = Ici (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Iic_of_neg a h

@[simp]
/--
theorem `preimage_const_mul_Ici_of_neg` / 定理 `preimage_const_mul_Ici_of_neg`

English:
theorem preimage_const_mul_Ici_of_neg
  given: (a : α) {c : α} (h : c < 0)
  proof: by
  simpa only [mul_comm] using preimage_mul_const_Ici_of_neg a h

@[simp]

中文:
定理 preimage_const_mul_Ici_of_neg
  条件: (a : α) {c : α} (h : c < 0)
  证明: by
  simpa only [mul_comm] using preimage_mul_const_Ici_of_neg a h

@[simp]

Depends on / 依赖: mul_comm, preimage_mul_const_Ici_of_neg
-/
theorem preimage_const_mul_Ici_of_neg (a : α) {c : α} (h : c < 0) :
    (c * ·) ⁻¹' Ici a = Iic (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Ici_of_neg a h

@[simp]
/--
theorem `preimage_const_mul_Ioo_of_neg` / 定理 `preimage_const_mul_Ioo_of_neg`

English:
theorem preimage_const_mul_Ioo_of_neg
  given: (a b : α) {c : α} (h : c < 0)
  proof: by
  simpa only [mul_comm] using preimage_mul_const_Ioo_of_neg a b h

@[simp]

中文:
定理 preimage_const_mul_Ioo_of_neg
  条件: (a b : α) {c : α} (h : c < 0)
  证明: by
  simpa only [mul_comm] using preimage_mul_const_Ioo_of_neg a b h

@[simp]

Depends on / 依赖: mul_comm, preimage_mul_const_Ioo_of_neg
-/
theorem preimage_const_mul_Ioo_of_neg (a b : α) {c : α} (h : c < 0) :
    (c * ·) ⁻¹' Ioo a b = Ioo (b / c) (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Ioo_of_neg a b h

@[simp]
/--
theorem `preimage_const_mul_Ioc_of_neg` / 定理 `preimage_const_mul_Ioc_of_neg`

English:
theorem preimage_const_mul_Ioc_of_neg
  given: (a b : α) {c : α} (h : c < 0)
  proof: by
  simpa only [mul_comm] using preimage_mul_const_Ioc_of_neg a b h

@[simp]

中文:
定理 preimage_const_mul_Ioc_of_neg
  条件: (a b : α) {c : α} (h : c < 0)
  证明: by
  simpa only [mul_comm] using preimage_mul_const_Ioc_of_neg a b h

@[simp]

Depends on / 依赖: mul_comm, preimage_mul_const_Ioc_of_neg
-/
theorem preimage_const_mul_Ioc_of_neg (a b : α) {c : α} (h : c < 0) :
    (c * ·) ⁻¹' Ioc a b = Ico (b / c) (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Ioc_of_neg a b h

@[simp]
/--
theorem `preimage_const_mul_Ico_of_neg` / 定理 `preimage_const_mul_Ico_of_neg`

English:
theorem preimage_const_mul_Ico_of_neg
  given: (a b : α) {c : α} (h : c < 0)
  proof: by
  simpa only [mul_comm] using preimage_mul_const_Ico_of_neg a b h

@[simp]

中文:
定理 preimage_const_mul_Ico_of_neg
  条件: (a b : α) {c : α} (h : c < 0)
  证明: by
  simpa only [mul_comm] using preimage_mul_const_Ico_of_neg a b h

@[simp]

Depends on / 依赖: mul_comm, preimage_mul_const_Ico_of_neg
-/
theorem preimage_const_mul_Ico_of_neg (a b : α) {c : α} (h : c < 0) :
    (c * ·) ⁻¹' Ico a b = Ioc (b / c) (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Ico_of_neg a b h

@[simp]
/--
theorem `preimage_const_mul_Icc_of_neg` / 定理 `preimage_const_mul_Icc_of_neg`

English:
theorem preimage_const_mul_Icc_of_neg
  given: (a b : α) {c : α} (h : c < 0)
  proof: by
  simpa only [mul_comm] using preimage_mul_const_Icc_of_neg a b h

@[simp]

中文:
定理 preimage_const_mul_Icc_of_neg
  条件: (a b : α) {c : α} (h : c < 0)
  证明: by
  simpa only [mul_comm] using preimage_mul_const_Icc_of_neg a b h

@[simp]

Depends on / 依赖: mul_comm, preimage_mul_const_Icc_of_neg
-/
theorem preimage_const_mul_Icc_of_neg (a b : α) {c : α} (h : c < 0) :
    (c * ·) ⁻¹' Icc a b = Icc (b / c) (a / c) := by
  simpa only [mul_comm] using preimage_mul_const_Icc_of_neg a b h

@[simp]
/--
theorem `preimage_mul_const_uIcc` / 定理 `preimage_mul_const_uIcc`

English:
theorem preimage_mul_const_uIcc
  given: (ha : a != 0) (b c : α)
  proof: (lt_or_gt_of_ne ha).elim
    (fun h => by
      simp [← Icc_min_max, h, h.le, min_div_div_right_of_nonpos, max_div_div_right_of_nonpos])
    fun ha : 0 < a => by simp [← Icc_min_max, ha, ha.le, min_div_div_right, max_div_div_right]

@[simp]

中文:
定理 preimage_mul_const_uIcc
  条件: (ha : a != 0) (b c : α)
  证明: (lt_or_gt_of_ne ha).elim
    (fun h => by
      simp [← Icc_min_max, h, h.le, min_div_div_right_of_nonpos, max_div_div_right_of_nonpos])
    fun ha : 0 < a => by simp [← Icc_min_max, ha, ha.le, min_div_div_right, max_div_div_right]

@[simp]

Depends on / 依赖: Icc_min_max, h.le, ha.le, lt_or_gt_of_ne, max_div_div_right, max_div_div_right_of_nonpos, min_div_div_right, min_div_div_right_of_nonpos
-/
theorem preimage_mul_const_uIcc (ha : a != 0) (b c : α) :
    (· * a) ⁻¹' [[b, c]] = [[b / a, c / a]] :=
  (lt_or_gt_of_ne ha).elim
    (fun h => by
      simp [← Icc_min_max, h, h.le, min_div_div_right_of_nonpos, max_div_div_right_of_nonpos])
    fun ha : 0 < a => by simp [← Icc_min_max, ha, ha.le, min_div_div_right, max_div_div_right]

@[simp]
/--
theorem `preimage_const_mul_uIcc` / 定理 `preimage_const_mul_uIcc`

English:
theorem preimage_const_mul_uIcc
  given: (ha : a != 0) (b c : α)
  proof: by
  simp only [← preimage_mul_const_uIcc ha, mul_comm]

@[simp]

中文:
定理 preimage_const_mul_uIcc
  条件: (ha : a != 0) (b c : α)
  证明: by
  simp only [← preimage_mul_const_uIcc ha, mul_comm]

@[simp]

Depends on / 依赖: mul_comm, preimage_mul_const_uIcc
-/
theorem preimage_const_mul_uIcc (ha : a != 0) (b c : α) :
    (a * ·) ⁻¹' [[b, c]] = [[b / a, c / a]] := by
  simp only [← preimage_mul_const_uIcc ha, mul_comm]

@[simp]
/--
theorem `preimage_div_const_uIcc` / 定理 `preimage_div_const_uIcc`

English:
theorem preimage_div_const_uIcc
  given: (ha : a != 0) (b c : α)
  proof: by
  simp only [div_eq_mul_inv, preimage_mul_const_uIcc (inv_ne_zero ha), inv_inv]

中文:
定理 preimage_div_const_uIcc
  条件: (ha : a != 0) (b c : α)
  证明: by
  simp only [div_eq_mul_inv, preimage_mul_const_uIcc (inv_ne_zero ha), inv_inv]

Depends on / 依赖: div_eq_mul_inv, inv_inv, inv_ne_zero, preimage_mul_const_uIcc
-/
theorem preimage_div_const_uIcc (ha : a != 0) (b c : α) :
    (fun x => x / a) ⁻¹' [[b, c]] = [[b * a, c * a]] := by
  simp only [div_eq_mul_inv, preimage_mul_const_uIcc (inv_ne_zero ha), inv_inv]

/--
lemma `preimage_const_mul_Ioi_or_Iio` / 引理 `preimage_const_mul_Ioi_or_Iio`

English:
lemma preimage_const_mul_Ioi_or_Iio
  statement: (hb : a != 0) {U V : Set α}
  proof: by
  obtain ⟨aU, (haU | haU)⟩ := hU <;>
  simp only [hV, haU, mem_ofPred_eq] <;>
  use a⁻¹ * aU <;>
  rcases lt_or_gt_of_ne hb with (hb | hb)
  · right; rw [Set.preimage_const_mul_Ioi_of_neg _ hb, div_eq_inv_mul]
  · left; rw [Set.preimage_const_mul_Ioi₀ _ hb, div_eq_inv_mul]
  · left; rw [Set.preim

中文:
引理 preimage_const_mul_Ioi_or_Iio
  结论: (hb : a != 0) {U V : Set α}
  证明: by
  obtain ⟨aU, (haU | haU)⟩ := hU <;>
  simp only [hV, haU, mem_ofPred_eq] <;>
  use a⁻¹ * aU <;>
  rcases lt_or_gt_of_ne hb with (hb | hb)
  · right; rw [Set.preimage_const_mul_Ioi_of_neg _ hb, div_eq_inv_mul]
  · left; rw [Set.preimage_const_mul_Ioi₀ _ hb, div_eq_inv_mul]
  · left; rw [Set.preim

Depends on / 依赖: Set.preimage_const_mul_Iio, Set.preimage_const_mul_Iio_of_neg, Set.preimage_const_mul_Ioi, Set.preimage_const_mul_Ioi_of_neg, div_eq_inv_mul, lt_or_gt_of_ne, mem_ofPred_eq, preimage_const_mul_Iio_of_neg, preimage_const_mul_Ioi_of_neg
-/
lemma preimage_const_mul_Ioi_or_Iio (hb : a != 0) {U V : Set α}
    (hU : U in {s | exists a, s = Ioi a ∨ s = Iio a}) (hV : V = (a * ·) ⁻¹' U) :
    V in {s | exists a, s = Ioi a ∨ s = Iio a} := by
  obtain ⟨aU, (haU | haU)⟩ := hU <;>
  simp only [hV, haU, mem_ofPred_eq] <;>
  use a⁻¹ * aU <;>
  rcases lt_or_gt_of_ne hb with (hb | hb)
  · right; rw [Set.preimage_const_mul_Ioi_of_neg _ hb, div_eq_inv_mul]
  · left; rw [Set.preimage_const_mul_Ioi₀ _ hb, div_eq_inv_mul]
  · left; rw [Set.preimage_const_mul_Iio_of_neg _ hb, div_eq_inv_mul]
  · right; rw [Set.preimage_const_mul_Iio₀ _ hb, div_eq_inv_mul]

@[simp]
/--
theorem `image_mul_const_uIcc` / 定理 `image_mul_const_uIcc`

English:
theorem image_mul_const_uIcc
  given: (a b c : α)
  statement: (· * a) '' [[b, c]] = [[b * a, c * a]]
  proof: if ha : a = 0 then by simp [ha]
  else calc
    (fun x => x * a) '' [[b, c]] = (· * a⁻¹) ⁻¹' [[b, c]] :=
      (Units.mk0 a ha).mulRight.image_eq_preimage_symm _
    _ = (fun x => x / a) ⁻¹' [[b, c]] := by simp only [div_eq_mul_inv]
    _ = [[b * a, c * a]] := preimage_div_const_uIcc ha _ _

@[simp]

中文:
定理 image_mul_const_uIcc
  条件: (a b c : α)
  结论: (· * a) '' [[b, c]] = [[b * a, c * a]]
  证明: if ha : a = 0 then by simp [ha]
  else calc
    (fun x => x * a) '' [[b, c]] = (· * a⁻¹) ⁻¹' [[b, c]] :=
      (Units.mk0 a ha).mulRight.image_eq_preimage_symm _
    _ = (fun x => x / a) ⁻¹' [[b, c]] := by simp only [div_eq_mul_inv]
    _ = [[b * a, c * a]] := preimage_div_const_uIcc ha _ _

@[simp]

Depends on / 依赖: Units.mk0, div_eq_mul_inv, image_eq_preimage_symm, mulRight, mulRight.image_eq_preimage_symm, preimage_div_const_uIcc
-/
theorem image_mul_const_uIcc (a b c : α) : (· * a) '' [[b, c]] = [[b * a, c * a]] :=
  if ha : a = 0 then by simp [ha]
  else calc
    (fun x => x * a) '' [[b, c]] = (· * a⁻¹) ⁻¹' [[b, c]] :=
      (Units.mk0 a ha).mulRight.image_eq_preimage_symm _
    _ = (fun x => x / a) ⁻¹' [[b, c]] := by simp only [div_eq_mul_inv]
    _ = [[b * a, c * a]] := preimage_div_const_uIcc ha _ _

@[simp]
/--
theorem `image_const_mul_uIcc` / 定理 `image_const_mul_uIcc`

English:
theorem image_const_mul_uIcc
  given: (a b c : α)
  statement: (a * ·) '' [[b, c]] = [[a * b, a * c]]
  proof: by
  simpa only [mul_comm] using image_mul_const_uIcc a b c

@[simp]

中文:
定理 image_const_mul_uIcc
  条件: (a b c : α)
  结论: (a * ·) '' [[b, c]] = [[a * b, a * c]]
  证明: by
  simpa only [mul_comm] using image_mul_const_uIcc a b c

@[simp]

Depends on / 依赖: image_mul_const_uIcc, mul_comm
-/
theorem image_const_mul_uIcc (a b c : α) : (a * ·) '' [[b, c]] = [[a * b, a * c]] := by
  simpa only [mul_comm] using image_mul_const_uIcc a b c

@[simp]
/--
theorem `image_div_const_uIcc` / 定理 `image_div_const_uIcc`

English:
theorem image_div_const_uIcc
  given: (a b c : α)
  statement: (fun x => x / a) '' [[b, c]] = [[b / a, c / a]]
  proof: by
  simp only [div_eq_mul_inv, image_mul_const_uIcc]

中文:
定理 image_div_const_uIcc
  条件: (a b c : α)
  结论: (fun x => x / a) '' [[b, c]] = [[b / a, c / a]]
  证明: by
  simp only [div_eq_mul_inv, image_mul_const_uIcc]

Depends on / 依赖: div_eq_mul_inv, image_mul_const_uIcc
-/
theorem image_div_const_uIcc (a b c : α) : (fun x => x / a) '' [[b, c]] = [[b / a, c / a]] := by
  simp only [div_eq_mul_inv, image_mul_const_uIcc]

/--
theorem `inv_Ioo_0_right` / 定理 `inv_Ioo_0_right`

English:
theorem inv_Ioo_0_right
  given: {a : α} (ha : a < 0)
  statement: (Ioo a 0)⁻¹ = Iio a⁻¹
  proof: by
  ext x
  refine ⟨fun h => (lt_inv_of_neg (inv_neg''.1 h.2) ha).2 h.1, fun h => ?_⟩
  have h' := (h.trans (inv_neg''.2 ha))
  exact ⟨(lt_inv_of_neg ha h').2 h, inv_neg''.2 h'⟩

中文:
定理 inv_Ioo_0_right
  条件: {a : α} (ha : a < 0)
  结论: (Ioo a 0)⁻¹ = Iio a⁻¹
  证明: by
  ext x
  refine ⟨fun h => (lt_inv_of_neg (inv_neg''.1 h.2) ha).2 h.1, fun h => ?_⟩
  have h' := (h.trans (inv_neg''.2 ha))
  exact ⟨(lt_inv_of_neg ha h').2 h, inv_neg''.2 h'⟩

Depends on / 依赖: h.trans, inv_neg, lt_inv_of_neg
-/
theorem inv_Ioo_0_right {a : α} (ha : a < 0) : (Ioo a 0)⁻¹ = Iio a⁻¹ := by
  ext x
  refine ⟨fun h => (lt_inv_of_neg (inv_neg''.1 h.2) ha).2 h.1, fun h => ?_⟩
  have h' := (h.trans (inv_neg''.2 ha))
  exact ⟨(lt_inv_of_neg ha h').2 h, inv_neg''.2 h'⟩

/--
theorem `inv_Iio₀` / 定理 `inv_Iio₀`

English:
theorem inv_Iio₀
  given: {a : α} (ha : a < 0)
  statement: (Iio a)⁻¹ = Ioo a⁻¹ 0
  proof: by
  rw [inv_eq_iff_eq_inv]; rw [inv_Ioo_0_right (inv_neg''.2 ha)]; rw [inv_inv]

中文:
定理 inv_Iio₀
  条件: {a : α} (ha : a < 0)
  结论: (Iio a)⁻¹ = Ioo a⁻¹ 0
  证明: by
  rw [inv_eq_iff_eq_inv]; rw [inv_Ioo_0_right (inv_neg''.2 ha)]; rw [inv_inv]

Depends on / 依赖: inv_Ioo_0_right, inv_eq_iff_eq_inv, inv_inv, inv_neg
-/
theorem inv_Iio₀ {a : α} (ha : a < 0) : (Iio a)⁻¹ = Ioo a⁻¹ 0 := by
  rw [inv_eq_iff_eq_inv]; rw [inv_Ioo_0_right (inv_neg''.2 ha)]; rw [inv_inv]

end LinearOrderedField

section CanonicallyOrdered

variable {α : Type*} [Monoid α]
variable [Preorder α] [CanonicallyOrderedMul α] [MulRightMono α]

@[to_additive]
/--
theorem `Ici_mul_Ici_eq` / 定理 `Ici_mul_Ici_eq`

English:
theorem Ici_mul_Ici_eq
  given: {a b : α}
  proof: by
  refine Subset.antisymm (Ici_mul_Ici_subset' ..) (subset_def ▸ fun c c_in =>
    mem_mul.mpr ⟨a, ⟨by simp, ?_⟩⟩)
obtain ⟨d, hd⟩ := exists_mul_of_le mem_Ici.mp c_in
  exact ⟨b * d, by simp [← mul_assoc, hd]⟩

@[to_additive]

中文:
定理 Ici_mul_Ici_eq
  条件: {a b : α}
  证明: by
  refine Subset.antisymm (Ici_mul_Ici_subset' ..) (subset_def ▸ fun c c_in =>
    mem_mul.mpr ⟨a, ⟨by simp, ?_⟩⟩)
obtain ⟨d, hd⟩ := exists_mul_of_le mem_Ici.mp c_in
  exact ⟨b * d, by simp [← mul_assoc, hd]⟩

@[to_additive]

Depends on / 依赖: Ici_mul_Ici_subset, Subset, Subset.antisymm, antisymm, c_in, exists_mul_of_le, mem_Ici, mem_Ici.mp, mem_mul, mem_mul.mpr, mul_assoc, subset_def
-/
theorem Ici_mul_Ici_eq {a b : α} :
    Ici a * Ici b = Ici (a * b) := by
  refine Subset.antisymm (Ici_mul_Ici_subset' ..) (subset_def ▸ fun c c_in =>
    mem_mul.mpr ⟨a, ⟨by simp, ?_⟩⟩)
obtain ⟨d, hd⟩ := exists_mul_of_le mem_Ici.mp c_in
  exact ⟨b * d, by simp [← mul_assoc, hd]⟩

@[to_additive]
/--
theorem `Ici_pow_eq` / 定理 `Ici_pow_eq`

English:
theorem Ici_pow_eq
  given: {a : α}

中文:
定理 Ici_pow_eq
  条件: {a : α}
-/
theorem Ici_pow_eq {a : α} :
    forall n != 0, Ici a ^ n = Ici (a ^ n)
  | 1, _ => by simp
  | n + 2, _ => by simp [pow_succ _ n.succ, Ici_pow_eq, Ici_mul_Ici_eq]

end CanonicallyOrdered

end Set
