/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Group.Equiv.Opposite
public import Mathlib.Algebra.GroupWithZero.Opposite
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Data.Int.Cast.Basic

/-!
# Ring structures on the multiplicative opposite
-/

@[expose] public section

variable {R : Type*}

namespace MulOpposite

/--
Instance `instDistrib` / 实例 `instDistrib`

English:
instance instDistrib
  signature: [Distrib R]
  body: unop_injective add_mul _ _ _
right_distrib _ _ _ := unop_injective mul_add _ _ _

中文:
实例 instDistrib
  签名: [Distrib R]
  定义体: unop_injective add_mul _ _ _
right_distrib _ _ _ := unop_injective mul_add _ _ _

Depends on / 依赖: add_mul, unop_injective
-/
instance instDistrib [Distrib R] : Distrib Rᵐᵒᵖ where
left_distrib _ _ _ := unop_injective add_mul _ _ _
right_distrib _ _ _ := unop_injective mul_add _ _ _

/--
Instance `instNatCast` / 实例 `instNatCast`

English:
instance instNatCast
  signature: [NatCast R]
  body: op n

中文:
实例 inst自然数Cast
  签名: [自然数嵌入 R]
  定义体: op n
-/
@[to_additive] instance instNatCast [NatCast R] : NatCast Rᵐᵒᵖ where natCast n := op n
/--
Instance `instIntCast` / 实例 `instIntCast`

English:
instance instIntCast
  signature: [IntCast R]
  body: op n

@[to_additive (attr := simp, norm_cast)]

中文:
实例 inst整数Cast
  签名: [整数嵌入 R]
  定义体: op n

@[to_additive (attr := simp, norm_cast)]
-/
@[to_additive] instance instIntCast [IntCast R] : IntCast Rᵐᵒᵖ where intCast n := op n

@[to_additive (attr := simp, norm_cast)]
/--
theorem `op_natCast` / 定理 `op_natCast`

English:
theorem op_natCast
  given: [NatCast R] (n : Nat)
  statement: op (n : R) = n
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 op_natCast
  条件: [自然数嵌入 R] (n : 自然数)
  结论: op (n : R) = n
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem op_natCast [NatCast R] (n : Nat) : op (n : R) = n :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `op_ofNat` / 定理 `op_ofNat`

English:
theorem op_ofNat
  given: [NatCast R] (n : Nat) [n.AtLeastTwo]
  proof: rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 op_of自然数
  条件: [自然数嵌入 R] (n : 自然数) [n.AtLeastTwo]
  证明: rfl

@[to_additive (attr := simp, norm_cast)]
-/
theorem op_ofNat [NatCast R] (n : Nat) [n.AtLeastTwo] :
    op (ofNat(n) : R) = ofNat(n) :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `op_intCast` / 定理 `op_intCast`

English:
theorem op_intCast
  given: [IntCast R] (n : Int)
  statement: op (n : R) = n
  proof: rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 op_intCast
  条件: [整数嵌入 R] (n : 整数)
  结论: op (n : R) = n
  证明: rfl

@[to_additive (attr := simp, norm_cast)]
-/
theorem op_intCast [IntCast R] (n : Int) : op (n : R) = n :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `unop_natCast` / 定理 `unop_natCast`

English:
theorem unop_natCast
  given: [NatCast R] (n : Nat)
  statement: unop (n : Rᵐᵒᵖ) = n
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 unop_natCast
  条件: [自然数嵌入 R] (n : 自然数)
  结论: unop (n : Rᵐᵒᵖ) = n
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem unop_natCast [NatCast R] (n : Nat) : unop (n : Rᵐᵒᵖ) = n :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `unop_ofNat` / 定理 `unop_ofNat`

English:
theorem unop_ofNat
  given: [NatCast R] (n : Nat) [n.AtLeastTwo]
  proof: rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 unop_of自然数
  条件: [自然数嵌入 R] (n : 自然数) [n.AtLeastTwo]
  证明: rfl

@[to_additive (attr := simp, norm_cast)]
-/
theorem unop_ofNat [NatCast R] (n : Nat) [n.AtLeastTwo] :
    unop (ofNat(n) : Rᵐᵒᵖ) = ofNat(n) :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `unop_intCast` / 定理 `unop_intCast`

English:
theorem unop_intCast
  given: [IntCast R] (n : Int)
  statement: unop (n : Rᵐᵒᵖ) = n
  proof: rfl

中文:
定理 unop_intCast
  条件: [整数嵌入 R] (n : 整数)
  结论: unop (n : Rᵐᵒᵖ) = n
  证明: rfl
-/
theorem unop_intCast [IntCast R] (n : Int) : unop (n : Rᵐᵒᵖ) = n :=
  rfl

/--
Instance `instAddMonoidWithOne` / 实例 `instAddMonoidWithOne`

English:
instance instAddMonoidWithOne
  signature: [AddMonoidWithOne R]
  body: instNatCast
  toAddMonoid := instAddMonoid
  toOne := instOne
  natCast_zero := show op ((0 : Nat) : R) = 0 by rw [Nat.cast_zero, op_zero]
  natCast_succ := show forall n, op ((n + 1 : Nat) : R) = op ↑(n : Nat) + 1 by simp

中文:
实例 instAddMonoidWithOne
  签名: [加法带幺幺半群 R]
  定义体: instNatCast
  toAddMonoid := instAddMonoid
  toOne := instOne
  natCast_zero := show op ((0 : Nat) : R) = 0 by rw [Nat.cast_zero, op_zero]
  natCast_succ := show forall n, op ((n + 1 : Nat) : R) = op ↑(n : Nat) + 1 by simp

Depends on / 依赖: instNatCast
-/
instance instAddMonoidWithOne [AddMonoidWithOne R] : AddMonoidWithOne Rᵐᵒᵖ where
  toNatCast := instNatCast
  toAddMonoid := instAddMonoid
  toOne := instOne
  natCast_zero := show op ((0 : Nat) : R) = 0 by rw [Nat.cast_zero, op_zero]
  natCast_succ := show forall n, op ((n + 1 : Nat) : R) = op ↑(n : Nat) + 1 by simp

/--
Instance `instAddCommMonoidWithOne` / 实例 `instAddCommMonoidWithOne`

English:
instance instAddCommMonoidWithOne
  signature: [AddCommMonoidWithOne R]
  body: instAddMonoidWithOne
  __ := instAddCommMonoid

中文:
实例 instAddCommMonoidWithOne
  签名: [加法交换带幺幺半群 R]
  定义体: instAddMonoidWithOne
  __ := instAddCommMonoid

Depends on / 依赖: instAddMonoidWithOne
-/
instance instAddCommMonoidWithOne [AddCommMonoidWithOne R] : AddCommMonoidWithOne Rᵐᵒᵖ where
  toAddMonoidWithOne := instAddMonoidWithOne
  __ := instAddCommMonoid

/--
Instance `instAddGroupWithOne` / 实例 `instAddGroupWithOne`

English:
instance instAddGroupWithOne
  signature: [AddGroupWithOne R]
  body: instAddMonoidWithOne
  toIntCast := instIntCast
  __ := instAddGroup
  intCast_ofNat n := show op ((n : Int) : R) = op (n : R) by rw [Int.cast_natCast]
  intCast_negSucc n := show op _ = op (-unop (op ((n + 1 : Nat) : R))) by simp

中文:
实例 instAddGroupWithOne
  签名: [加法带幺群 R]
  定义体: instAddMonoidWithOne
  toIntCast := instIntCast
  __ := instAddGroup
  intCast_ofNat n := show op ((n : Int) : R) = op (n : R) by rw [Int.cast_natCast]
  intCast_negSucc n := show op _ = op (-unop (op ((n + 1 : Nat) : R))) by simp

Depends on / 依赖: instAddMonoidWithOne
-/
instance instAddGroupWithOne [AddGroupWithOne R] : AddGroupWithOne Rᵐᵒᵖ where
  toAddMonoidWithOne := instAddMonoidWithOne
  toIntCast := instIntCast
  __ := instAddGroup
  intCast_ofNat n := show op ((n : Int) : R) = op (n : R) by rw [Int.cast_natCast]
  intCast_negSucc n := show op _ = op (-unop (op ((n + 1 : Nat) : R))) by simp

/--
Instance `instAddCommGroupWithOne` / 实例 `instAddCommGroupWithOne`

English:
instance instAddCommGroupWithOne
  signature: [AddCommGroupWithOne R]
  body: instAddCommGroup
  __ := instAddGroupWithOne

中文:
实例 instAddCommGroupWithOne
  签名: [加法交换带幺群 R]
  定义体: instAddCommGroup
  __ := instAddGroupWithOne

Depends on / 依赖: instAddCommGroup
-/
instance instAddCommGroupWithOne [AddCommGroupWithOne R] : AddCommGroupWithOne Rᵐᵒᵖ where
  toAddCommGroup := instAddCommGroup
  __ := instAddGroupWithOne

/--
Instance `instNonUnitalNonAssocSemiring` / 实例 `instNonUnitalNonAssocSemiring`

English:
instance instNonUnitalNonAssocSemiring
  signature: [NonUnitalNonAssocSemiring R]
  body: instAddCommMonoid
  __ := instDistrib
  __ := instMulZeroClass

中文:
实例 instNonUnitalNonAssocSemiring
  签名: [非幺非结合半环 R]
  定义体: instAddCommMonoid
  __ := instDistrib
  __ := instMulZeroClass

Depends on / 依赖: instAddCommMonoid
-/
instance instNonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring R] :
    NonUnitalNonAssocSemiring Rᵐᵒᵖ where
  __ := instAddCommMonoid
  __ := instDistrib
  __ := instMulZeroClass

/--
Instance `instNonUnitalSemiring` / 实例 `instNonUnitalSemiring`

English:
instance instNonUnitalSemiring
  signature: [NonUnitalSemiring R]
  body: instNonUnitalNonAssocSemiring
  __ := instSemigroupWithZero

中文:
实例 instNonUnitalSemiring
  签名: [非幺半环 R]
  定义体: instNonUnitalNonAssocSemiring
  __ := instSemigroupWithZero

Depends on / 依赖: instNonUnitalNonAssocSemiring
-/
instance instNonUnitalSemiring [NonUnitalSemiring R] : NonUnitalSemiring Rᵐᵒᵖ where
  __ := instNonUnitalNonAssocSemiring
  __ := instSemigroupWithZero

/--
Instance `instNonAssocSemiring` / 实例 `instNonAssocSemiring`

English:
instance instNonAssocSemiring
  signature: [NonAssocSemiring R]
  body: instNonUnitalNonAssocSemiring
  __ := instMulZeroOneClass
  __ := instAddCommMonoidWithOne

中文:
实例 instNonAssocSemiring
  签名: [非结合半环 R]
  定义体: instNonUnitalNonAssocSemiring
  __ := instMulZeroOneClass
  __ := instAddCommMonoidWithOne

Depends on / 依赖: instNonUnitalNonAssocSemiring
-/
instance instNonAssocSemiring [NonAssocSemiring R] : NonAssocSemiring Rᵐᵒᵖ where
  __ := instNonUnitalNonAssocSemiring
  __ := instMulZeroOneClass
  __ := instAddCommMonoidWithOne

/--
Instance `instSemiring` / 实例 `instSemiring`

English:
instance instSemiring
  signature: [Semiring R]
  body: instNonUnitalSemiring
  __ := instNonAssocSemiring
  __ := instMonoidWithZero

中文:
实例 instSemiring
  签名: [半环 R]
  定义体: instNonUnitalSemiring
  __ := instNonAssocSemiring
  __ := instMonoidWithZero

Depends on / 依赖: instNonUnitalSemiring
-/
instance instSemiring [Semiring R] : Semiring Rᵐᵒᵖ where
  __ := instNonUnitalSemiring
  __ := instNonAssocSemiring
  __ := instMonoidWithZero

/--
Instance `instNonUnitalCommSemiring` / 实例 `instNonUnitalCommSemiring`

English:
instance instNonUnitalCommSemiring
  signature: [NonUnitalCommSemiring R]
  body: instNonUnitalSemiring
  __ := instCommSemigroup

中文:
实例 instNonUnitalCommSemiring
  签名: [非幺交换半环 R]
  定义体: instNonUnitalSemiring
  __ := instCommSemigroup

Depends on / 依赖: instNonUnitalSemiring
-/
instance instNonUnitalCommSemiring [NonUnitalCommSemiring R] : NonUnitalCommSemiring Rᵐᵒᵖ where
  __ := instNonUnitalSemiring
  __ := instCommSemigroup

/--
Instance `instCommSemiring` / 实例 `instCommSemiring`

English:
instance instCommSemiring
  signature: [CommSemiring R]
  body: instSemiring
  __ := instCommMonoid

中文:
实例 instCommSemiring
  签名: [交换半环 R]
  定义体: instSemiring
  __ := instCommMonoid

Depends on / 依赖: instSemiring
-/
instance instCommSemiring [CommSemiring R] : CommSemiring Rᵐᵒᵖ where
  __ := instSemiring
  __ := instCommMonoid

/--
Instance `instNonUnitalNonAssocRing` / 实例 `instNonUnitalNonAssocRing`

English:
instance instNonUnitalNonAssocRing
  signature: [NonUnitalNonAssocRing R]
  body: instAddCommGroup
  __ := instNonUnitalNonAssocSemiring

中文:
实例 instNonUnitalNonAssocRing
  签名: [非幺非结合环 R]
  定义体: instAddCommGroup
  __ := instNonUnitalNonAssocSemiring

Depends on / 依赖: instAddCommGroup
-/
instance instNonUnitalNonAssocRing [NonUnitalNonAssocRing R] : NonUnitalNonAssocRing Rᵐᵒᵖ where
  __ := instAddCommGroup
  __ := instNonUnitalNonAssocSemiring

/--
Instance `instNonUnitalRing` / 实例 `instNonUnitalRing`

English:
instance instNonUnitalRing
  signature: [NonUnitalRing R]
  body: instNonUnitalNonAssocRing
  __ := instNonUnitalSemiring

中文:
实例 instNonUnitalRing
  签名: [非幺环 R]
  定义体: instNonUnitalNonAssocRing
  __ := instNonUnitalSemiring

Depends on / 依赖: instNonUnitalNonAssocRing
-/
instance instNonUnitalRing [NonUnitalRing R] : NonUnitalRing Rᵐᵒᵖ where
  __ := instNonUnitalNonAssocRing
  __ := instNonUnitalSemiring

/--
Instance `instNonAssocRing` / 实例 `instNonAssocRing`

English:
instance instNonAssocRing
  signature: [NonAssocRing R]
  body: instNonUnitalNonAssocRing
  __ := instNonAssocSemiring
  __ := instAddCommGroupWithOne

中文:
实例 instNonAssocRing
  签名: [非结合环 R]
  定义体: instNonUnitalNonAssocRing
  __ := instNonAssocSemiring
  __ := instAddCommGroupWithOne

Depends on / 依赖: instNonUnitalNonAssocRing
-/
instance instNonAssocRing [NonAssocRing R] : NonAssocRing Rᵐᵒᵖ where
  __ := instNonUnitalNonAssocRing
  __ := instNonAssocSemiring
  __ := instAddCommGroupWithOne

/--
Instance `instRing` / 实例 `instRing`

English:
instance instRing
  signature: [Ring R]
  body: instSemiring
  __ := instAddCommGroupWithOne

中文:
实例 instRing
  签名: [环 R]
  定义体: instSemiring
  __ := instAddCommGroupWithOne

Depends on / 依赖: instSemiring
-/
instance instRing [Ring R] : Ring Rᵐᵒᵖ where
  __ := instSemiring
  __ := instAddCommGroupWithOne

/--
Instance `instNonUnitalCommRing` / 实例 `instNonUnitalCommRing`

English:
instance instNonUnitalCommRing
  signature: [NonUnitalCommRing R]
  body: instNonUnitalRing
  __ := instNonUnitalCommSemiring

中文:
实例 instNonUnitalCommRing
  签名: [非幺交换环 R]
  定义体: instNonUnitalRing
  __ := instNonUnitalCommSemiring

Depends on / 依赖: instNonUnitalRing
-/
instance instNonUnitalCommRing [NonUnitalCommRing R] : NonUnitalCommRing Rᵐᵒᵖ where
  __ := instNonUnitalRing
  __ := instNonUnitalCommSemiring

/--
Instance `instCommRing` / 实例 `instCommRing`

English:
instance instCommRing
  signature: [CommRing R]
  body: instRing
  __ := instCommMonoid

中文:
实例 instCommRing
  签名: [交换环 R]
  定义体: instRing
  __ := instCommMonoid

Depends on / 依赖: instRing
-/
instance instCommRing [CommRing R] : CommRing Rᵐᵒᵖ where
  __ := instRing
  __ := instCommMonoid

/--
Instance `instIsDomain` / 实例 `instIsDomain`

English:
instance instIsDomain
  signature: [Ring R] [IsDomain R]
  body: NoZeroDivisors.to_isDomain _

中文:
实例 instIsDomain
  签名: [环 R] [是整环 R]
  定义体: NoZeroDivisors.to_isDomain _

Depends on / 依赖: NoZeroDivisors, NoZeroDivisors.to_isDomain, to_isDomain
-/
instance instIsDomain [Ring R] [IsDomain R] : IsDomain Rᵐᵒᵖ :=
  NoZeroDivisors.to_isDomain _

end MulOpposite

namespace AddOpposite

/--
Instance `instDistrib` / 实例 `instDistrib`

English:
instance instDistrib
  signature: [Distrib R]
  body: unop_injective mul_add _ _ _
right_distrib _ _ _ := unop_injective add_mul _ _ _

中文:
实例 instDistrib
  签名: [Distrib R]
  定义体: unop_injective mul_add _ _ _
right_distrib _ _ _ := unop_injective add_mul _ _ _

Depends on / 依赖: mul_add, unop_injective
-/
instance instDistrib [Distrib R] : Distrib Rᵃᵒᵖ where
left_distrib _ _ _ := unop_injective mul_add _ _ _
right_distrib _ _ _ := unop_injective add_mul _ _ _

-- NOTE: `addMonoidWithOne R → addMonoidWithOne Rᵃᵒᵖ` does not hold
/--
Instance `instAddCommMonoidWithOne` / 实例 `instAddCommMonoidWithOne`

English:
instance instAddCommMonoidWithOne
  signature: [AddCommMonoidWithOne R]
  body: instNatCast
  toOne := instOne
  __ := instAddCommMonoid
  natCast_zero := show op ((0 : Nat) : R) = 0 by rw [Nat.cast_zero, op_zero]
  natCast_succ := show forall n, op ((n + 1 : Nat) : R) = op ↑(n : Nat) + 1 by simp [add_comm]

中文:
实例 instAddCommMonoidWithOne
  签名: [加法交换带幺幺半群 R]
  定义体: instNatCast
  toOne := instOne
  __ := instAddCommMonoid
  natCast_zero := show op ((0 : Nat) : R) = 0 by rw [Nat.cast_zero, op_zero]
  natCast_succ := show forall n, op ((n + 1 : Nat) : R) = op ↑(n : Nat) + 1 by simp [add_comm]

Depends on / 依赖: instNatCast
-/
instance instAddCommMonoidWithOne [AddCommMonoidWithOne R] : AddCommMonoidWithOne Rᵃᵒᵖ where
  toNatCast := instNatCast
  toOne := instOne
  __ := instAddCommMonoid
  natCast_zero := show op ((0 : Nat) : R) = 0 by rw [Nat.cast_zero, op_zero]
  natCast_succ := show forall n, op ((n + 1 : Nat) : R) = op ↑(n : Nat) + 1 by simp [add_comm]

/--
Instance `instAddCommGroupWithOne` / 实例 `instAddCommGroupWithOne`

English:
instance instAddCommGroupWithOne
  signature: [AddCommGroupWithOne R]
  body: instIntCast
  toAddCommGroup := instAddCommGroup
  __ := instAddCommMonoidWithOne
intCast_ofNat _ := congr_arg op Int.cast_natCast _
intCast_negSucc _ := congr_arg op Int.cast_negSucc _

中文:
实例 instAddCommGroupWithOne
  签名: [加法交换带幺群 R]
  定义体: instIntCast
  toAddCommGroup := instAddCommGroup
  __ := instAddCommMonoidWithOne
intCast_ofNat _ := congr_arg op Int.cast_natCast _
intCast_negSucc _ := congr_arg op Int.cast_negSucc _

Depends on / 依赖: instIntCast
-/
instance instAddCommGroupWithOne [AddCommGroupWithOne R] : AddCommGroupWithOne Rᵃᵒᵖ where
  toIntCast := instIntCast
  toAddCommGroup := instAddCommGroup
  __ := instAddCommMonoidWithOne
intCast_ofNat _ := congr_arg op Int.cast_natCast _
intCast_negSucc _ := congr_arg op Int.cast_negSucc _

/--
Instance `instNonUnitalNonAssocSemiring` / 实例 `instNonUnitalNonAssocSemiring`

English:
instance instNonUnitalNonAssocSemiring
  signature: [NonUnitalNonAssocSemiring R]
  body: instAddCommMonoid
  __ := instDistrib
  __ := instMulZeroClass

中文:
实例 instNonUnitalNonAssocSemiring
  签名: [非幺非结合半环 R]
  定义体: instAddCommMonoid
  __ := instDistrib
  __ := instMulZeroClass

Depends on / 依赖: instAddCommMonoid
-/
instance instNonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring R] :
    NonUnitalNonAssocSemiring Rᵃᵒᵖ where
  __ := instAddCommMonoid
  __ := instDistrib
  __ := instMulZeroClass

/--
Instance `instNonUnitalSemiring` / 实例 `instNonUnitalSemiring`

English:
instance instNonUnitalSemiring
  signature: [NonUnitalSemiring R]
  body: instNonUnitalNonAssocSemiring
  __ := instSemigroupWithZero

中文:
实例 instNonUnitalSemiring
  签名: [非幺半环 R]
  定义体: instNonUnitalNonAssocSemiring
  __ := instSemigroupWithZero

Depends on / 依赖: instNonUnitalNonAssocSemiring
-/
instance instNonUnitalSemiring [NonUnitalSemiring R] : NonUnitalSemiring Rᵃᵒᵖ where
  __ := instNonUnitalNonAssocSemiring
  __ := instSemigroupWithZero

/--
Instance `instNonAssocSemiring` / 实例 `instNonAssocSemiring`

English:
instance instNonAssocSemiring
  signature: [NonAssocSemiring R]
  body: instNonUnitalNonAssocSemiring
  __ := instMulZeroOneClass
  __ := instAddCommMonoidWithOne

中文:
实例 instNonAssocSemiring
  签名: [非结合半环 R]
  定义体: instNonUnitalNonAssocSemiring
  __ := instMulZeroOneClass
  __ := instAddCommMonoidWithOne

Depends on / 依赖: instNonUnitalNonAssocSemiring
-/
instance instNonAssocSemiring [NonAssocSemiring R] : NonAssocSemiring Rᵃᵒᵖ where
  __ := instNonUnitalNonAssocSemiring
  __ := instMulZeroOneClass
  __ := instAddCommMonoidWithOne

/--
Instance `instSemiring` / 实例 `instSemiring`

English:
instance instSemiring
  signature: [Semiring R]
  body: instNonUnitalSemiring
  __ := instNonAssocSemiring
  __ := instMonoidWithZero

中文:
实例 instSemiring
  签名: [半环 R]
  定义体: instNonUnitalSemiring
  __ := instNonAssocSemiring
  __ := instMonoidWithZero

Depends on / 依赖: instNonUnitalSemiring
-/
instance instSemiring [Semiring R] : Semiring Rᵃᵒᵖ where
  __ := instNonUnitalSemiring
  __ := instNonAssocSemiring
  __ := instMonoidWithZero

/--
Instance `instNonUnitalCommSemiring` / 实例 `instNonUnitalCommSemiring`

English:
instance instNonUnitalCommSemiring
  signature: [NonUnitalCommSemiring R]
  body: instNonUnitalSemiring
  __ := instCommSemigroup

中文:
实例 instNonUnitalCommSemiring
  签名: [非幺交换半环 R]
  定义体: instNonUnitalSemiring
  __ := instCommSemigroup

Depends on / 依赖: instNonUnitalSemiring
-/
instance instNonUnitalCommSemiring [NonUnitalCommSemiring R] : NonUnitalCommSemiring Rᵃᵒᵖ where
  __ := instNonUnitalSemiring
  __ := instCommSemigroup

/--
Instance `instCommSemiring` / 实例 `instCommSemiring`

English:
instance instCommSemiring
  signature: [CommSemiring R]
  body: instSemiring
  __ := instCommMonoid

中文:
实例 instCommSemiring
  签名: [交换半环 R]
  定义体: instSemiring
  __ := instCommMonoid

Depends on / 依赖: instSemiring
-/
instance instCommSemiring [CommSemiring R] : CommSemiring Rᵃᵒᵖ where
  __ := instSemiring
  __ := instCommMonoid

/--
Instance `instNonUnitalNonAssocRing` / 实例 `instNonUnitalNonAssocRing`

English:
instance instNonUnitalNonAssocRing
  signature: [NonUnitalNonAssocRing R]
  body: instAddCommGroup
  __ := instNonUnitalNonAssocSemiring

中文:
实例 instNonUnitalNonAssocRing
  签名: [非幺非结合环 R]
  定义体: instAddCommGroup
  __ := instNonUnitalNonAssocSemiring

Depends on / 依赖: instAddCommGroup
-/
instance instNonUnitalNonAssocRing [NonUnitalNonAssocRing R] : NonUnitalNonAssocRing Rᵃᵒᵖ where
  __ := instAddCommGroup
  __ := instNonUnitalNonAssocSemiring

/--
Instance `instNonUnitalRing` / 实例 `instNonUnitalRing`

English:
instance instNonUnitalRing
  signature: [NonUnitalRing R]
  body: instNonUnitalNonAssocRing
  __ := instNonUnitalSemiring

中文:
实例 instNonUnitalRing
  签名: [非幺环 R]
  定义体: instNonUnitalNonAssocRing
  __ := instNonUnitalSemiring

Depends on / 依赖: instNonUnitalNonAssocRing
-/
instance instNonUnitalRing [NonUnitalRing R] : NonUnitalRing Rᵃᵒᵖ where
  __ := instNonUnitalNonAssocRing
  __ := instNonUnitalSemiring

/--
Instance `instNonAssocRing` / 实例 `instNonAssocRing`

English:
instance instNonAssocRing
  signature: [NonAssocRing R]
  body: instNonUnitalNonAssocRing
  __ := instNonAssocSemiring
  __ := instAddCommGroupWithOne

中文:
实例 instNonAssocRing
  签名: [非结合环 R]
  定义体: instNonUnitalNonAssocRing
  __ := instNonAssocSemiring
  __ := instAddCommGroupWithOne

Depends on / 依赖: instNonUnitalNonAssocRing
-/
instance instNonAssocRing [NonAssocRing R] : NonAssocRing Rᵃᵒᵖ where
  __ := instNonUnitalNonAssocRing
  __ := instNonAssocSemiring
  __ := instAddCommGroupWithOne

/--
Instance `instRing` / 实例 `instRing`

English:
instance instRing
  signature: [Ring R]
  body: instSemiring
  __ := instAddCommGroupWithOne

中文:
实例 instRing
  签名: [环 R]
  定义体: instSemiring
  __ := instAddCommGroupWithOne

Depends on / 依赖: instSemiring
-/
instance instRing [Ring R] : Ring Rᵃᵒᵖ where
  __ := instSemiring
  __ := instAddCommGroupWithOne

/--
Instance `instNonUnitalCommRing` / 实例 `instNonUnitalCommRing`

English:
instance instNonUnitalCommRing
  signature: [NonUnitalCommRing R]
  body: instNonUnitalRing
  __ := instNonUnitalCommSemiring

中文:
实例 instNonUnitalCommRing
  签名: [非幺交换环 R]
  定义体: instNonUnitalRing
  __ := instNonUnitalCommSemiring

Depends on / 依赖: instNonUnitalRing
-/
instance instNonUnitalCommRing [NonUnitalCommRing R] : NonUnitalCommRing Rᵃᵒᵖ where
  __ := instNonUnitalRing
  __ := instNonUnitalCommSemiring

/--
Instance `instCommRing` / 实例 `instCommRing`

English:
instance instCommRing
  signature: [CommRing R]
  body: instRing
  __ := instCommMonoid

中文:
实例 instCommRing
  签名: [交换环 R]
  定义体: instRing
  __ := instCommMonoid

Depends on / 依赖: instRing
-/
instance instCommRing [CommRing R] : CommRing Rᵃᵒᵖ where
  __ := instRing
  __ := instCommMonoid

/--
Instance `instIsDomain` / 实例 `instIsDomain`

English:
instance instIsDomain
  signature: [Ring R] [IsDomain R]
  body: NoZeroDivisors.to_isDomain _

中文:
实例 instIsDomain
  签名: [环 R] [是整环 R]
  定义体: NoZeroDivisors.to_isDomain _

Depends on / 依赖: NoZeroDivisors, NoZeroDivisors.to_isDomain, to_isDomain
-/
instance instIsDomain [Ring R] [IsDomain R] : IsDomain Rᵃᵒᵖ :=
  NoZeroDivisors.to_isDomain _

end AddOpposite

open MulOpposite

/-- A non-unital ring homomorphism `f : R →ₙ+* S` such that `f x` commutes with `f y` for all `x, y`
defines a non-unital ring homomorphism to `Sᵐᵒᵖ`. -/
@[simps -fullyApplied]
/--
Definition of `NonUnitalRingHom.toOpposite` / `NonUnitalRingHom.toOpposite` 的定义

English:
definition NonUnitalRingHom.toOpposite
  signature: {R S : Type*} [NonUnitalNonAssocSemiring R]
  body: { ((opAddEquiv : S ≃+ Sᵐᵒᵖ).toAddMonoidHom.comp ↑f : R ->+ Sᵐᵒᵖ), f.toMulHom.toOpposite hf with
    toFun := MulOpposite.op ∘ f }

中文:
定义 非幺环态射.toOpposite
  签名: {R S : 类型} [非幺非结合半环 R]
  定义体: { ((opAddEquiv : S ≃+ Sᵐᵒᵖ).toAddMonoidHom.comp ↑f : R ->+ Sᵐᵒᵖ), f.toMulHom.toOpposite hf with
    toFun := MulOpposite.op ∘ f }

Depends on / 依赖: MulOpposite, MulOpposite.op, f.toMulHom.toOpposite, opAddEquiv, toAddMonoidHom, toAddMonoidHom.comp, toMulHom, toOpposite
-/
def NonUnitalRingHom.toOpposite {R S : Type*} [NonUnitalNonAssocSemiring R]
    [NonUnitalNonAssocSemiring S] (f : R ->ₙ+* S) (hf : forall x y, Commute (f x) (f y)) : R ->ₙ+* Sᵐᵒᵖ :=
  { ((opAddEquiv : S ≃+ Sᵐᵒᵖ).toAddMonoidHom.comp ↑f : R ->+ Sᵐᵒᵖ), f.toMulHom.toOpposite hf with
    toFun := MulOpposite.op ∘ f }

/-- A non-unital ring homomorphism `f : R →ₙ* S` such that `f x` commutes with `f y` for all `x, y`
defines a non-unital ring homomorphism from `Rᵐᵒᵖ`. -/
@[simps -fullyApplied]
/--
Definition of `NonUnitalRingHom.fromOpposite` / `NonUnitalRingHom.fromOpposite` 的定义

English:
definition NonUnitalRingHom.fromOpposite
  signature: {R S : Type*} [NonUnitalNonAssocSemiring R]
  body: { (f.toAddMonoidHom.comp (opAddEquiv : R ≃+ Rᵐᵒᵖ).symm.toAddMonoidHom : Rᵐᵒᵖ ->+ S),
    f.toMulHom.fromOpposite hf with toFun := f ∘ MulOpposite.unop }

中文:
定义 非幺环态射.fromOpposite
  签名: {R S : 类型} [非幺非结合半环 R]
  定义体: { (f.toAddMonoidHom.comp (opAddEquiv : R ≃+ Rᵐᵒᵖ).symm.toAddMonoidHom : Rᵐᵒᵖ ->+ S),
    f.toMulHom.fromOpposite hf with toFun := f ∘ MulOpposite.unop }

Depends on / 依赖: MulOpposite, MulOpposite.unop, f.toAddMonoidHom.comp, f.toMulHom.fromOpposite, fromOpposite, opAddEquiv, symm.toAddMonoidHom, toAddMonoidHom, toMulHom
-/
def NonUnitalRingHom.fromOpposite {R S : Type*} [NonUnitalNonAssocSemiring R]
    [NonUnitalNonAssocSemiring S] (f : R ->ₙ+* S) (hf : forall x y, Commute (f x) (f y)) : Rᵐᵒᵖ ->ₙ+* S :=
  { (f.toAddMonoidHom.comp (opAddEquiv : R ≃+ Rᵐᵒᵖ).symm.toAddMonoidHom : Rᵐᵒᵖ ->+ S),
    f.toMulHom.fromOpposite hf with toFun := f ∘ MulOpposite.unop }

/-- A non-unital ring hom `R →ₙ+* S` can equivalently be viewed as a non-unital ring hom
`Rᵐᵒᵖ →+* Sᵐᵒᵖ`. This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[simps]
/--
Definition of `NonUnitalRingHom.op` / `NonUnitalRingHom.op` 的定义

English:
definition NonUnitalRingHom.op
  signature: {R S} [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]
  body: { AddMonoidHom.mulOp f.toAddMonoidHom, MulHom.op f.toMulHom with }
  invFun f := { AddMonoidHom.mulUnop f.toAddMonoidHom, MulHom.unop f.toMulHom with }

中文:
定义 非幺环态射.op
  签名: {R S} [非幺非结合半环 R] [非幺非结合半环 S]
  定义体: { AddMonoidHom.mulOp f.toAddMonoidHom, MulHom.op f.toMulHom with }
  invFun f := { AddMonoidHom.mulUnop f.toAddMonoidHom, MulHom.unop f.toMulHom with }

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mulOp, MulHom, MulHom.op, f.toAddMonoidHom, f.toMulHom, toAddMonoidHom, toMulHom
-/
def NonUnitalRingHom.op {R S} [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] :
    (R ->ₙ+* S) ≃ (Rᵐᵒᵖ ->ₙ+* Sᵐᵒᵖ) where
  toFun f := { AddMonoidHom.mulOp f.toAddMonoidHom, MulHom.op f.toMulHom with }
  invFun f := { AddMonoidHom.mulUnop f.toAddMonoidHom, MulHom.unop f.toMulHom with }

/-- The 'unopposite' of a non-unital ring hom `Rᵐᵒᵖ →ₙ+* Sᵐᵒᵖ`. Inverse to
`NonUnitalRingHom.op`. -/
@[simp]
/--
Definition of `NonUnitalRingHom.unop` / `NonUnitalRingHom.unop` 的定义

English:
definition NonUnitalRingHom.unop
  signature: {R S} [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]
  body: NonUnitalRingHom.op.symm

中文:
定义 非幺环态射.unop
  签名: {R S} [非幺非结合半环 R] [非幺非结合半环 S]
  定义体: NonUnitalRingHom.op.symm

Depends on / 依赖: NonUnitalRingHom, NonUnitalRingHom.op.symm
-/
def NonUnitalRingHom.unop {R S} [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] :
    (Rᵐᵒᵖ ->ₙ+* Sᵐᵒᵖ) ≃ (R ->ₙ+* S) :=
  NonUnitalRingHom.op.symm

/-- A ring homomorphism `f : R →+* S` such that `f x` commutes with `f y` for all `x, y` defines
a ring homomorphism to `Sᵐᵒᵖ`. -/
@[simps -fullyApplied]
/--
Definition of `RingHom.toOpposite` / `RingHom.toOpposite` 的定义

English:
definition RingHom.toOpposite
  signature: {R S : Type*} [Semiring R] [Semiring S] (f : R ->+* S)
  body: { ((opAddEquiv : S ≃+ Sᵐᵒᵖ).toAddMonoidHom.comp ↑f : R ->+ Sᵐᵒᵖ), f.toMonoidHom.toOpposite hf with
    toFun := MulOpposite.op ∘ f }

中文:
定义 环态射.toOpposite
  签名: {R S : 类型} [半环 R] [半环 S] (f : R ->+* S)
  定义体: { ((opAddEquiv : S ≃+ Sᵐᵒᵖ).toAddMonoidHom.comp ↑f : R ->+ Sᵐᵒᵖ), f.toMonoidHom.toOpposite hf with
    toFun := MulOpposite.op ∘ f }

Depends on / 依赖: IsOpenImmersion, IsOpenImmersion.lift, IsOpenImmersion.of_comp, MulOpposite, MulOpposite.op, f.toMonoidHom.toOpposite, of_comp, opAddEquiv, toAddMonoidHom, toAddMonoidHom.comp, toMonoidHom, toOpposite
-/
def RingHom.toOpposite {R S : Type*} [Semiring R] [Semiring S] (f : R ->+* S)
    (hf : forall x y, Commute (f x) (f y)) : R ->+* Sᵐᵒᵖ :=
  { ((opAddEquiv : S ≃+ Sᵐᵒᵖ).toAddMonoidHom.comp ↑f : R ->+ Sᵐᵒᵖ), f.toMonoidHom.toOpposite hf with
    toFun := MulOpposite.op ∘ f }

/-- A ring homomorphism `f : R →+* S` such that `f x` commutes with `f y` for all `x, y` defines
a ring homomorphism from `Rᵐᵒᵖ`. -/
@[simps -fullyApplied]
/--
Definition of `RingHom.fromOpposite` / `RingHom.fromOpposite` 的定义

English:
definition RingHom.fromOpposite
  signature: {R S : Type*} [Semiring R] [Semiring S] (f : R ->+* S)
  body: { (f.toAddMonoidHom.comp (opAddEquiv : R ≃+ Rᵐᵒᵖ).symm.toAddMonoidHom : Rᵐᵒᵖ ->+ S),
    f.toMonoidHom.fromOpposite hf with toFun := f ∘ MulOpposite.unop }

中文:
定义 环态射.fromOpposite
  签名: {R S : 类型} [半环 R] [半环 S] (f : R ->+* S)
  定义体: { (f.toAddMonoidHom.comp (opAddEquiv : R ≃+ Rᵐᵒᵖ).symm.toAddMonoidHom : Rᵐᵒᵖ ->+ S),
    f.toMonoidHom.fromOpposite hf with toFun := f ∘ MulOpposite.unop }

Depends on / 依赖: MulOpposite, MulOpposite.unop, f.toAddMonoidHom.comp, f.toMonoidHom.fromOpposite, fromOpposite, opAddEquiv, symm.toAddMonoidHom, toAddMonoidHom, toMonoidHom
-/
def RingHom.fromOpposite {R S : Type*} [Semiring R] [Semiring S] (f : R ->+* S)
    (hf : forall x y, Commute (f x) (f y)) : Rᵐᵒᵖ ->+* S :=
  { (f.toAddMonoidHom.comp (opAddEquiv : R ≃+ Rᵐᵒᵖ).symm.toAddMonoidHom : Rᵐᵒᵖ ->+ S),
    f.toMonoidHom.fromOpposite hf with toFun := f ∘ MulOpposite.unop }

/-- A ring hom `R →+* S` can equivalently be viewed as a ring hom `Rᵐᵒᵖ →+* Sᵐᵒᵖ`. This is the
action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[simps!]
/--
Definition of `RingHom.op` / `RingHom.op` 的定义

English:
definition RingHom.op
  signature: {R S} [NonAssocSemiring R] [NonAssocSemiring S]
  body: { AddMonoidHom.mulOp f.toAddMonoidHom, MonoidHom.op f.toMonoidHom with }
  invFun f := { AddMonoidHom.mulUnop f.toAddMonoidHom, MonoidHom.unop f.toMonoidHom with }

中文:
定义 环态射.op
  签名: {R S} [非结合半环 R] [非结合半环 S]
  定义体: { AddMonoidHom.mulOp f.toAddMonoidHom, MonoidHom.op f.toMonoidHom with }
  invFun f := { AddMonoidHom.mulUnop f.toAddMonoidHom, MonoidHom.unop f.toMonoidHom with }

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mulOp, MonoidHom, MonoidHom.op, f.toAddMonoidHom, f.toMonoidHom, toAddMonoidHom, toMonoidHom
-/
def RingHom.op {R S} [NonAssocSemiring R] [NonAssocSemiring S] :
    (R ->+* S) ≃ (Rᵐᵒᵖ ->+* Sᵐᵒᵖ) where
  toFun f := { AddMonoidHom.mulOp f.toAddMonoidHom, MonoidHom.op f.toMonoidHom with }
  invFun f := { AddMonoidHom.mulUnop f.toAddMonoidHom, MonoidHom.unop f.toMonoidHom with }

/-- The 'unopposite' of a ring hom `Rᵐᵒᵖ →+* Sᵐᵒᵖ`. Inverse to `RingHom.op`. -/
@[simp]
/--
Definition of `RingHom.unop` / `RingHom.unop` 的定义

English:
definition RingHom.unop
  signature: {R S} [NonAssocSemiring R] [NonAssocSemiring S]
  body: RingHom.op.symm

中文:
定义 环态射.unop
  签名: {R S} [非结合半环 R] [非结合半环 S]
  定义体: RingHom.op.symm

Depends on / 依赖: RingHom, RingHom.op.symm
-/
def RingHom.unop {R S} [NonAssocSemiring R] [NonAssocSemiring S] : (Rᵐᵒᵖ ->+* Sᵐᵒᵖ) ≃ (R ->+* S) :=
  RingHom.op.symm
