/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
module

public import Mathlib.Algebra.Group.Commute.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.Opposites
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Tactic.TFAE

/-!
# Semirings and rings

This file gives lemmas about semirings, rings and domains.
This is analogous to `Mathlib/Algebra/Group/Basic.lean`,
the difference being that the former is about `+` and `*` separately, while
the present file is about their interaction.

For the definitions of semirings and rings see `Mathlib/Algebra/Ring/Defs.lean`.
-/

@[expose] public section

assert_not_exists Nat.cast_sub

variable {R S : Type*}

open Function

namespace AddHom

/-- Left multiplication by an element of a type with distributive multiplication is an `AddHom`. -/
@[simps -fullyApplied]
/--
Definition of `mulLeft` / `mulLeft` 的定义

English:
definition mulLeft
  signature: [Distrib R] (r : R)
  body: (r * ·)
  map_add' := mul_add r

中文:
定义 mulLeft
  签名: [Distrib R] (r : R)
  定义体: (r * ·)
  map_add' := mul_add r
-/
def mulLeft [Distrib R] (r : R) : AddHom R R where
  toFun := (r * ·)
  map_add' := mul_add r

/-- Right multiplication by an element of a type with distributive multiplication is an `AddHom`. -/
@[simps -fullyApplied]
/--
Definition of `mulRight` / `mulRight` 的定义

English:
definition mulRight
  signature: [Distrib R] (r : R)
  body: a * r
  map_add' _ _ := add_mul _ _ r

中文:
定义 mulRight
  签名: [Distrib R] (r : R)
  定义体: a * r
  map_add' _ _ := add_mul _ _ r
-/
def mulRight [Distrib R] (r : R) : AddHom R R where
  toFun a := a * r
  map_add' _ _ := add_mul _ _ r

end AddHom

namespace AddMonoidHom
variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] {a b : R}

/--
Definition of `mulLeft` / `mulLeft` 的定义

English:
definition mulLeft
  signature: (r : R)
  body: (r * ·)
  map_zero' := mul_zero r
  map_add' := mul_add r

中文:
定义 mulLeft
  签名: (r : R)
  定义体: (r * ·)
  map_zero' := mul_zero r
  map_add' := mul_add r
-/
def mulLeft (r : R) : R ->+ R where
  toFun := (r * ·)
  map_zero' := mul_zero r
  map_add' := mul_add r

/--
lemma `coe_mulLeft` / 引理 `coe_mulLeft`

English:
lemma coe_mulLeft
  given: (r : R)
  statement: (mulLeft r : R -> R) = HMul.hMul r
  proof: rfl

中文:
引理 coe_mulLeft
  条件: (r : R)
  结论: (mulLeft r : R -> R) = 异质乘法.hMul r
  证明: rfl
-/
@[simp, norm_cast] lemma coe_mulLeft (r : R) : (mulLeft r : R -> R) = HMul.hMul r := rfl

/--
Definition of `mulRight` / `mulRight` 的定义

English:
definition mulRight
  signature: (r : R)
  body: a * r
  map_zero' := zero_mul r
  map_add' _ _ := add_mul _ _ r

中文:
定义 mulRight
  签名: (r : R)
  定义体: a * r
  map_zero' := zero_mul r
  map_add' _ _ := add_mul _ _ r
-/
def mulRight (r : R) : R ->+ R where
  toFun a := a * r
  map_zero' := zero_mul r
  map_add' _ _ := add_mul _ _ r

/--
lemma `coe_mulRight` / 引理 `coe_mulRight`

English:
lemma coe_mulRight
  given: (r : R)
  statement: (mulRight r) = (· * r)
  proof: rfl

中文:
引理 coe_mulRight
  条件: (r : R)
  结论: (mulRight r) = (· * r)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_mulRight (r : R) : (mulRight r) = (· * r) := rfl

/--
lemma `mulRight_apply` / 引理 `mulRight_apply`

English:
lemma mulRight_apply
  given: (a r : R)
  statement: mulRight r a = a * r
  proof: rfl

中文:
引理 mulRight_apply
  条件: (a r : R)
  结论: mulRight r a = a * r
  证明: rfl
-/
lemma mulRight_apply (a r : R) : mulRight r a = a * r := rfl

/--
Definition of `mul` / `mul` 的定义

English:
definition mul
  signature: : R ->+ R ->+ R where
  body: mulLeft
map_zero' := ext zero_mul
map_add' a b := ext add_mul a b

中文:
定义 mul
  签名: : R ->+ R ->+ R where
  定义体: mulLeft
map_zero' := ext zero_mul
map_add' a b := ext add_mul a b

Depends on / 依赖: mulLeft
-/
def mul : R ->+ R ->+ R where
  toFun := mulLeft
map_zero' := ext zero_mul
map_add' a b := ext add_mul a b

/--
lemma `mul_apply` / 引理 `mul_apply`

English:
lemma mul_apply
  given: (x y : R)
  statement: mul x y = x * y
  proof: rfl

中文:
引理 mul_apply
  条件: (x y : R)
  结论: mul x y = x * y
  证明: rfl
-/
lemma mul_apply (x y : R) : mul x y = x * y := rfl

/--
lemma `coe_mul` / 引理 `coe_mul`

English:
lemma coe_mul
  statement: ⇑(mul : R ->+ R ->+ R) = mulLeft
  proof: rfl

中文:
引理 coe_mul
  结论: ⇑(mul : R ->+ R ->+ R) = mulLeft
  证明: rfl
-/
@[simp, norm_cast] lemma coe_mul : ⇑(mul : R ->+ R ->+ R) = mulLeft := rfl
/--
lemma `coe_flip_mul` / 引理 `coe_flip_mul`

English:
lemma coe_flip_mul
  statement: ⇑(mul : R ->+ R ->+ R).flip = mulRight
  proof: rfl

中文:
引理 coe_flip_mul
  结论: ⇑(mul : R ->+ R ->+ R).flip = mulRight
  证明: rfl
-/
@[simp, norm_cast] lemma coe_flip_mul : ⇑(mul : R ->+ R ->+ R).flip = mulRight := rfl

/--
lemma `map_mul_iff` / 引理 `map_mul_iff`

English:
lemma map_mul_iff
  given: (f : R ->+ S)
  proof: Iff.symm ext_iff₂

中文:
引理 map_mul_iff
  条件: (f : R ->+ S)
  证明: Iff.symm ext_iff₂

Depends on / 依赖: Iff.symm
-/
lemma map_mul_iff (f : R ->+ S) :
    (forall x y, f (x * y) = f x * f y) ↔ (mul : R ->+ R ->+ R).compr₂ f = (mul.comp f).compl₂ f :=
  Iff.symm ext_iff₂

/--
lemma `mulLeft_eq_mulRight_iff_forall_commute` / 引理 `mulLeft_eq_mulRight_iff_forall_commute`

English:
lemma mulLeft_eq_mulRight_iff_forall_commute
  statement: mulLeft a = mulRight a ↔ forall b, Commute a b
  proof: DFunLike.ext_iff

中文:
引理 mulLeft_eq_mulRight_iff_对任意_commute
  结论: mulLeft a = mulRight a ↔ 对任意 b, Commute a b
  证明: DFunLike.ext_iff

Depends on / 依赖: DFunLike, DFunLike.ext_iff, ext_iff
-/
lemma mulLeft_eq_mulRight_iff_forall_commute : mulLeft a = mulRight a ↔ forall b, Commute a b :=
  DFunLike.ext_iff

/--
lemma `mulRight_eq_mulLeft_iff_forall_commute` / 引理 `mulRight_eq_mulLeft_iff_forall_commute`

English:
lemma mulRight_eq_mulLeft_iff_forall_commute
  statement: mulRight b = mulLeft b ↔ forall a, Commute a b
  proof: DFunLike.ext_iff

中文:
引理 mulRight_eq_mulLeft_iff_对任意_commute
  结论: mulRight b = mulLeft b ↔ 对任意 a, Commute a b
  证明: DFunLike.ext_iff

Depends on / 依赖: DFunLike, DFunLike.ext_iff, ext_iff
-/
lemma mulRight_eq_mulLeft_iff_forall_commute : mulRight b = mulLeft b ↔ forall a, Commute a b :=
  DFunLike.ext_iff

end AddMonoidHom

namespace AddMonoid.End
section NonUnitalNonAssocSemiring
variable [NonUnitalNonAssocSemiring R]

/-- The left multiplication map: `(a, b) ↦ a * b`. See also `AddMonoidHom.mulLeft`. -/
@[simps!]
/--
Definition of `mulLeft` / `mulLeft` 的定义

English:
definition mulLeft
  signature: : R ->+ AddMonoid.End R
  body: .mul

中文:
定义 mulLeft
  签名: : R ->+ 加法幺半群.End R
  定义体: .mul
-/
def mulLeft : R ->+ AddMonoid.End R := .mul

/-- The right multiplication map: `(a, b) ↦ b * a`. See also `AddMonoidHom.mulRight`. -/
@[simps!]
/--
Definition of `mulRight` / `mulRight` 的定义

English:
definition mulRight
  signature: : R ->+ AddMonoid.End R
  body: (.mul : R ->+ AddMonoid.End R).flip

中文:
定义 mulRight
  签名: : R ->+ 加法幺半群.End R
  定义体: (.mul : R ->+ AddMonoid.End R).flip

Depends on / 依赖: AddMonoid, AddMonoid.End
-/
def mulRight : R ->+ AddMonoid.End R := (.mul : R ->+ AddMonoid.End R).flip

end NonUnitalNonAssocSemiring

section NonUnitalNonAssocCommSemiring
variable [NonUnitalNonAssocCommSemiring R]

/--
lemma `mulRight_eq_mulLeft` / 引理 `mulRight_eq_mulLeft`

English:
lemma mulRight_eq_mulLeft
  statement: mulRight = (mulLeft : R ->+ AddMonoid.End R)
  proof: AddMonoidHom.ext fun _ =>
Eq.symm AddMonoidHom.mulLeft_eq_mulRight_iff_forall_commute.2 (.all _)

中文:
引理 mulRight_eq_mulLeft
  结论: mulRight = (mulLeft : R ->+ 加法幺半群.End R)
  证明: AddMonoidHom.ext fun _ =>
Eq.symm AddMonoidHom.mulLeft_eq_mulRight_iff_forall_commute.2 (.all _)

Depends on / 依赖: AddMonoidHom, AddMonoidHom.ext, AddMonoidHom.mulLeft_eq_mulRight_iff_forall_commute, Eq.symm, mulLeft_eq_mulRight_iff_forall_commute
-/
lemma mulRight_eq_mulLeft : mulRight = (mulLeft : R ->+ AddMonoid.End R) :=
  AddMonoidHom.ext fun _ =>
Eq.symm AddMonoidHom.mulLeft_eq_mulRight_iff_forall_commute.2 (.all _)

end NonUnitalNonAssocCommSemiring
end AddMonoid.End

section HasDistribNeg

section Mul

variable {α : Type*} [Mul α] [HasDistribNeg α]

open MulOpposite

/--
Instance `MulOpposite.instHasDistribNeg` / 实例 `MulOpposite.instHasDistribNeg`

English:
instance MulOpposite.instHasDistribNeg
  signature: : HasDistribNeg αᵐᵒᵖ where
  body: unop_injective mul_neg _ _
mul_neg _ _ := unop_injective neg_mul _ _

中文:
实例 MulOpposite.instHasDistribNeg
  签名: : 有DistribNeg αᵐᵒᵖ where
  定义体: unop_injective mul_neg _ _
mul_neg _ _ := unop_injective neg_mul _ _

Depends on / 依赖: mul_neg, unop_injective
-/
instance MulOpposite.instHasDistribNeg : HasDistribNeg αᵐᵒᵖ where
neg_mul _ _ := unop_injective mul_neg _ _
mul_neg _ _ := unop_injective neg_mul _ _

end Mul

end HasDistribNeg

section NonUnitalCommRing

variable {α : Type*} [NonUnitalCommRing α]

attribute [local simp] add_assoc add_comm add_left_comm mul_comm

/--
theorem `vieta_formula_quadratic` / 定理 `vieta_formula_quadratic`

English:
theorem vieta_formula_quadratic
  given: {b c x : α} (h : x * x - b * x + c = 0)
  proof: by
  have : c = x * (b - x) := (eq_neg_of_add_eq_zero_right h).trans (by simp [mul_sub, mul_comm])
  refine ⟨b - x, ?_, by simp, by rw [this]⟩
  rw [this]; rw [sub_add]; rw [← sub_mul]; rw [sub_self]

中文:
定理 vieta_formula_quadratic
  条件: {b c x : α} (h : x * x - b * x + c = 0)
  证明: by
  have : c = x * (b - x) := (eq_neg_of_add_eq_zero_right h).trans (by simp [mul_sub, mul_comm])
  refine ⟨b - x, ?_, by simp, by rw [this]⟩
  rw [this]; rw [sub_add]; rw [← sub_mul]; rw [sub_self]

Depends on / 依赖: eq_neg_of_add_eq_zero_right, mul_comm, mul_sub, sub_add, sub_mul, sub_self
-/
theorem vieta_formula_quadratic {b c x : α} (h : x * x - b * x + c = 0) :
    exists y : α, y * y - b * y + c = 0 ∧ x + y = b ∧ x * y = c := by
  have : c = x * (b - x) := (eq_neg_of_add_eq_zero_right h).trans (by simp [mul_sub, mul_comm])
  refine ⟨b - x, ?_, by simp, by rw [this]⟩
  rw [this]; rw [sub_add]; rw [← sub_mul]; rw [sub_self]

end NonUnitalCommRing

/--
theorem `succ_ne_self` / 定理 `succ_ne_self`

English:
theorem succ_ne_self
  given: {α : Type*} [NonAssocRing α] [Nontrivial α] (a : α)
  statement: a + 1 != a
  proof: fun h =>
  one_ne_zero ((add_right_inj a).mp (by simp [h]))

中文:
定理 succ_ne_self
  条件: {α : 类型} [非结合环 α] [非平凡 α] (a : α)
  结论: a + 1 != a
  证明: fun h =>
  one_ne_zero ((add_right_inj a).mp (by simp [h]))
-/
theorem succ_ne_self {α : Type*} [NonAssocRing α] [Nontrivial α] (a : α) : a + 1 != a := fun h =>
  one_ne_zero ((add_right_inj a).mp (by simp [h]))

/--
theorem `pred_ne_self` / 定理 `pred_ne_self`

English:
theorem pred_ne_self
  given: {α : Type*} [NonAssocRing α] [Nontrivial α] (a : α)
  statement: a - 1 != a
  proof: fun h =>
  one_ne_zero (neg_injective ((add_right_inj a).mp (by simp [← sub_eq_add_neg, h])))

中文:
定理 pred_ne_self
  条件: {α : 类型} [非结合环 α] [非平凡 α] (a : α)
  结论: a - 1 != a
  证明: fun h =>
  one_ne_zero (neg_injective ((add_right_inj a).mp (by simp [← sub_eq_add_neg, h])))
-/
theorem pred_ne_self {α : Type*} [NonAssocRing α] [Nontrivial α] (a : α) : a - 1 != a := fun h =>
  one_ne_zero (neg_injective ((add_right_inj a).mp (by simp [← sub_eq_add_neg, h])))

section NoZeroDivisors

variable (α)

section NonUnitalNonAssocRing

variable {R : Type*} [NonUnitalNonAssocRing R] {r : R}

/--
lemma `isLeftRegular_iff_right_eq_zero_of_mul` / 引理 `isLeftRegular_iff_right_eq_zero_of_mul`

English:
lemma isLeftRegular_iff_right_eq_zero_of_mul
  statement: IsLeftRegular r ↔ forall x, r * x = 0 -> x = 0 where
  proof: h (by simp_rw [eq, mul_zero])
mpr h r₁ r₂ eq := sub_eq_zero.mp h _ by simp_rw [mul_sub, eq, sub_self]

中文:
引理 isLeftRegular_iff_right_eq_zero_of_mul
  结论: IsLeftRegular r ↔ 对任意 x, r * x = 0 -> x = 0 where
  证明: h (by simp_rw [eq, mul_zero])
mpr h r₁ r₂ eq := sub_eq_zero.mp h _ by simp_rw [mul_sub, eq, sub_self]

Depends on / 依赖: mul_zero, simp_rw
-/
lemma isLeftRegular_iff_right_eq_zero_of_mul : IsLeftRegular r ↔ forall x, r * x = 0 -> x = 0 where
  mp h r' eq := h (by simp_rw [eq, mul_zero])
mpr h r₁ r₂ eq := sub_eq_zero.mp h _ by simp_rw [mul_sub, eq, sub_self]

/--
lemma `isRightRegular_iff_left_eq_zero_of_mul` / 引理 `isRightRegular_iff_left_eq_zero_of_mul`

English:
lemma isRightRegular_iff_left_eq_zero_of_mul
  statement: IsRightRegular r ↔ forall x, x * r = 0 -> x = 0 where
  proof: h (by simp_rw [eq, zero_mul])
mpr h r₁ r₂ eq := sub_eq_zero.mp h _ by simp_rw [sub_mul, eq, sub_self]

中文:
引理 isRightRegular_iff_left_eq_zero_of_mul
  结论: IsRightRegular r ↔ 对任意 x, x * r = 0 -> x = 0 where
  证明: h (by simp_rw [eq, zero_mul])
mpr h r₁ r₂ eq := sub_eq_zero.mp h _ by simp_rw [sub_mul, eq, sub_self]

Depends on / 依赖: simp_rw, zero_mul
-/
lemma isRightRegular_iff_left_eq_zero_of_mul : IsRightRegular r ↔ forall x, x * r = 0 -> x = 0 where
  mp h r' eq := h (by simp_rw [eq, zero_mul])
mpr h r₁ r₂ eq := sub_eq_zero.mp h _ by simp_rw [sub_mul, eq, sub_self]

/--
lemma `isRegular_iff_eq_zero_of_mul` / 引理 `isRegular_iff_eq_zero_of_mul`

English:
lemma isRegular_iff_eq_zero_of_mul
  proof: by
  rw [isRegular_iff]; rw [isLeftRegular_iff_right_eq_zero_of_mul]; rw [isRightRegular_iff_left_eq_zero_of_mul]

中文:
引理 isRegular_iff_eq_zero_of_mul
  证明: by
  rw [isRegular_iff]; rw [isLeftRegular_iff_right_eq_zero_of_mul]; rw [isRightRegular_iff_left_eq_zero_of_mul]

Depends on / 依赖: isLeftRegular_iff_right_eq_zero_of_mul, isRegular_iff, isRightRegular_iff_left_eq_zero_of_mul
-/
lemma isRegular_iff_eq_zero_of_mul :
    IsRegular r ↔ (forall x, r * x = 0 -> x = 0) ∧ (forall x, x * r = 0 -> x = 0) := by
  rw [isRegular_iff]; rw [isLeftRegular_iff_right_eq_zero_of_mul]; rw [isRightRegular_iff_left_eq_zero_of_mul]

/--
lemma `noZeroDivisors_tfae` / 引理 `noZeroDivisors_tfae`

English:
lemma noZeroDivisors_tfae
  statement: List.TFAE
  proof: by
  simp_rw [isLeftCancelMulZero_iff, isRightCancelMulZero_iff, isCancelMulZero_iff_forall_isRegular,
    isLeftRegular_iff_right_eq_zero_of_mul, isRightRegular_iff_left_eq_zero_of_mul,
    isRegular_iff_eq_zero_of_mul]
  tfae_have 1 ↔ 2 := noZeroDivisors_iff_right_eq_zero_of_mul
  tfae_have 1 ↔ 3 

中文:
引理 noZeroDivisors_tfae
  结论: 列表.TFAE
  证明: by
  simp_rw [isLeftCancelMulZero_iff, isRightCancelMulZero_iff, isCancelMulZero_iff_forall_isRegular,
    isLeftRegular_iff_right_eq_zero_of_mul, isRightRegular_iff_left_eq_zero_of_mul,
    isRegular_iff_eq_zero_of_mul]
  tfae_have 1 ↔ 2 := noZeroDivisors_iff_right_eq_zero_of_mul
  tfae_have 1 ↔ 3 

Depends on / 依赖: isCancelMulZero_iff_forall_isRegular, isLeftCancelMulZero_iff, isLeftRegular_iff_right_eq_zero_of_mul, isRegular_iff_eq_zero_of_mul, isRightCancelMulZero_iff, isRightRegular_iff_left_eq_zero_of_mul, noZeroDivisors_iff_eq_zero_of_mul, noZeroDivisors_iff_left_eq_zero_of_mul, noZeroDivisors_iff_right_eq_zero_of_mul, simp_rw, tfae_finish, tfae_have
-/
lemma noZeroDivisors_tfae : List.TFAE
    [NoZeroDivisors R, IsLeftCancelMulZero R, IsRightCancelMulZero R, IsCancelMulZero R] := by
  simp_rw [isLeftCancelMulZero_iff, isRightCancelMulZero_iff, isCancelMulZero_iff_forall_isRegular,
    isLeftRegular_iff_right_eq_zero_of_mul, isRightRegular_iff_left_eq_zero_of_mul,
    isRegular_iff_eq_zero_of_mul]
  tfae_have 1 ↔ 2 := noZeroDivisors_iff_right_eq_zero_of_mul
  tfae_have 1 ↔ 3 := noZeroDivisors_iff_left_eq_zero_of_mul
  tfae_have 1 ↔ 4 := noZeroDivisors_iff_eq_zero_of_mul
  tfae_finish

/--
lemma `isCancelMulZero_iff_noZeroDivisors` / 引理 `isCancelMulZero_iff_noZeroDivisors`

English:
lemma isCancelMulZero_iff_noZeroDivisors
  statement: IsCancelMulZero R ↔ NoZeroDivisors R
  proof: noZeroDivisors_tfae.out 3 0

中文:
引理 isCancelMulZero_iff_noZeroDivisors
  结论: 是乘零消去 R ↔ 无零因子 R
  证明: noZeroDivisors_tfae.out 3 0

Depends on / 依赖: noZeroDivisors_tfae, noZeroDivisors_tfae.out
-/
lemma isCancelMulZero_iff_noZeroDivisors : IsCancelMulZero R ↔ NoZeroDivisors R :=
  noZeroDivisors_tfae.out 3 0

variable (R) in
instance (priority := 100) NoZeroDivisors.to_isCancelMulZero
    [NoZeroDivisors R] : IsCancelMulZero R :=
  isCancelMulZero_iff_noZeroDivisors.mpr ‹_›

end NonUnitalNonAssocRing

/--
lemma `NoZeroDivisors.to_isDomain` / 引理 `NoZeroDivisors.to_isDomain`

English:
lemma NoZeroDivisors.to_isDomain
  given: [Ring α] [h : Nontrivial α] [NoZeroDivisors α]
  proof: { NoZeroDivisors.to_isCancelMulZero α, h with .. }

中文:
引理 无零因子.to_isDomain
  条件: [环 α] [h : 非平凡 α] [无零因子 α]
  证明: { NoZeroDivisors.to_isCancelMulZero α, h with .. }

Depends on / 依赖: NoZeroDivisors, NoZeroDivisors.to_isCancelMulZero, to_isCancelMulZero
-/
lemma NoZeroDivisors.to_isDomain [Ring α] [h : Nontrivial α] [NoZeroDivisors α] :
    IsDomain α :=
  { NoZeroDivisors.to_isCancelMulZero α, h with .. }

instance (priority := 100) IsDomain.to_noZeroDivisors [Semiring α] [IsDomain α] :
    NoZeroDivisors α :=
  IsRightCancelMulZero.to_noZeroDivisors α

/--
Instance `Subsingleton.to_isCancelMulZero` / 实例 `Subsingleton.to_isCancelMulZero`

English:
instance Subsingleton.to_isCancelMulZero
  signature: [Mul α] [Zero α] [Subsingleton α]
  body: (hb <| Subsingleton.eq_zero _).elim
  mul_left_cancel_of_ne_zero hb := (hb <| Subsingleton.eq_zero _).elim

中文:
实例 子单例.to_isCancelMulZero
  签名: [乘法 α] [零 α] [子单例 α]
  定义体: (hb <| Subsingleton.eq_zero _).elim
  mul_left_cancel_of_ne_zero hb := (hb <| Subsingleton.eq_zero _).elim

Depends on / 依赖: Subsingleton, Subsingleton.eq_zero, eq_zero
-/
instance Subsingleton.to_isCancelMulZero [Mul α] [Zero α] [Subsingleton α] : IsCancelMulZero α where
  mul_right_cancel_of_ne_zero hb := (hb <| Subsingleton.eq_zero _).elim
  mul_left_cancel_of_ne_zero hb := (hb <| Subsingleton.eq_zero _).elim

-- This was previously a global instance,
-- but it has been implicated in slow typeclass resolutions,
-- so we scope it to the `Subsingleton` namespace.
/--
lemma `Subsingleton.to_noZeroDivisors` / 引理 `Subsingleton.to_noZeroDivisors`

English:
lemma Subsingleton.to_noZeroDivisors
  given: [Mul α] [Zero α] [Subsingleton α]
  statement: NoZeroDivisors α where
  proof: .inl (Subsingleton.eq_zero _)

scoped[Subsingleton] attribute [instance] Subsingleton.to_noZeroDivisors

中文:
引理 子单例.to_noZeroDivisors
  条件: [乘法 α] [零 α] [子单例 α]
  结论: 无零因子 α where
  证明: .inl (Subsingleton.eq_zero _)

scoped[Subsingleton] attribute [instance] Subsingleton.to_noZeroDivisors

Depends on / 依赖: Subsingleton, Subsingleton.eq_zero, eq_zero
-/
lemma Subsingleton.to_noZeroDivisors [Mul α] [Zero α] [Subsingleton α] : NoZeroDivisors α where
  eq_zero_or_eq_zero_of_mul_eq_zero _ := .inl (Subsingleton.eq_zero _)

scoped[Subsingleton] attribute [instance] Subsingleton.to_noZeroDivisors

/--
lemma `isDomain_iff_cancelMulZero_and_nontrivial` / 引理 `isDomain_iff_cancelMulZero_and_nontrivial`

English:
lemma isDomain_iff_cancelMulZero_and_nontrivial
  given: [Semiring α]
  proof: ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => {}⟩

中文:
引理 isDomain_iff_cancelMulZero_and_nontrivial
  条件: [半环 α]
  证明: ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => {}⟩
-/
lemma isDomain_iff_cancelMulZero_and_nontrivial [Semiring α] :
    IsDomain α ↔ IsCancelMulZero α ∧ Nontrivial α :=
  ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => {}⟩

/--
lemma `isCancelMulZero_iff_isDomain_or_subsingleton` / 引理 `isCancelMulZero_iff_isDomain_or_subsingleton`

English:
lemma isCancelMulZero_iff_isDomain_or_subsingleton
  given: [Semiring α]
  proof: by
  refine ⟨fun t => ?_, fun h => h.elim (fun _ => inferInstance) (fun _ => inferInstance)⟩
  rw [or_iff_not_imp_right]; rw [not_subsingleton_iff_nontrivial]
  exact fun _ => {}

中文:
引理 isCancelMulZero_iff_isDomain_or_subsingleton
  条件: [半环 α]
  证明: by
  refine ⟨fun t => ?_, fun h => h.elim (fun _ => inferInstance) (fun _ => inferInstance)⟩
  rw [or_iff_not_imp_right]; rw [not_subsingleton_iff_nontrivial]
  exact fun _ => {}

Depends on / 依赖: h.elim, not_subsingleton_iff_nontrivial, or_iff_not_imp_right
-/
lemma isCancelMulZero_iff_isDomain_or_subsingleton [Semiring α] :
    IsCancelMulZero α ↔ IsDomain α ∨ Subsingleton α := by
  refine ⟨fun t => ?_, fun h => h.elim (fun _ => inferInstance) (fun _ => inferInstance)⟩
  rw [or_iff_not_imp_right]; rw [not_subsingleton_iff_nontrivial]
  exact fun _ => {}

/--
lemma `isDomain_iff_noZeroDivisors_and_nontrivial` / 引理 `isDomain_iff_noZeroDivisors_and_nontrivial`

English:
lemma isDomain_iff_noZeroDivisors_and_nontrivial
  given: [Ring α]
  proof: by
  rw [← isCancelMulZero_iff_noZeroDivisors]; rw [isDomain_iff_cancelMulZero_and_nontrivial]

中文:
引理 isDomain_iff_noZeroDivisors_and_nontrivial
  条件: [环 α]
  证明: by
  rw [← isCancelMulZero_iff_noZeroDivisors]; rw [isDomain_iff_cancelMulZero_and_nontrivial]

Depends on / 依赖: isCancelMulZero_iff_noZeroDivisors, isDomain_iff_cancelMulZero_and_nontrivial
-/
lemma isDomain_iff_noZeroDivisors_and_nontrivial [Ring α] :
    IsDomain α ↔ NoZeroDivisors α ∧ Nontrivial α := by
  rw [← isCancelMulZero_iff_noZeroDivisors]; rw [isDomain_iff_cancelMulZero_and_nontrivial]

/--
lemma `noZeroDivisors_iff_isDomain_or_subsingleton` / 引理 `noZeroDivisors_iff_isDomain_or_subsingleton`

English:
lemma noZeroDivisors_iff_isDomain_or_subsingleton
  given: [Ring α]
  proof: by
  rw [← isCancelMulZero_iff_noZeroDivisors]; rw [isCancelMulZero_iff_isDomain_or_subsingleton]

中文:
引理 noZeroDivisors_iff_isDomain_or_subsingleton
  条件: [环 α]
  证明: by
  rw [← isCancelMulZero_iff_noZeroDivisors]; rw [isCancelMulZero_iff_isDomain_or_subsingleton]

Depends on / 依赖: isCancelMulZero_iff_isDomain_or_subsingleton, isCancelMulZero_iff_noZeroDivisors
-/
lemma noZeroDivisors_iff_isDomain_or_subsingleton [Ring α] :
    NoZeroDivisors α ↔ IsDomain α ∨ Subsingleton α := by
  rw [← isCancelMulZero_iff_noZeroDivisors]; rw [isCancelMulZero_iff_isDomain_or_subsingleton]

end NoZeroDivisors

section DivisionMonoid
variable [DivisionMonoid R] [HasDistribNeg R] {a b : R}

/--
lemma `one_div_neg_one_eq_neg_one` / 引理 `one_div_neg_one_eq_neg_one`

English:
lemma one_div_neg_one_eq_neg_one
  statement: (1 : R) / -1 = -1
  proof: have : -1 * -1 = (1 : R) := by rw [neg_mul_neg, one_mul]
  Eq.symm (eq_one_div_of_mul_eq_one_right this)

中文:
引理 one_div_neg_one_eq_neg_one
  结论: (1 : R) / -1 = -1
  证明: have : -1 * -1 = (1 : R) := by rw [neg_mul_neg, one_mul]
  Eq.symm (eq_one_div_of_mul_eq_one_right this)

Depends on / 依赖: Eq.symm, eq_one_div_of_mul_eq_one_right, neg_mul_neg, one_mul
-/
lemma one_div_neg_one_eq_neg_one : (1 : R) / -1 = -1 :=
  have : -1 * -1 = (1 : R) := by rw [neg_mul_neg, one_mul]
  Eq.symm (eq_one_div_of_mul_eq_one_right this)

/--
lemma `one_div_neg_eq_neg_one_div` / 引理 `one_div_neg_eq_neg_one_div`

English:
lemma one_div_neg_eq_neg_one_div
  given: (a : R)
  statement: 1 / -a = -(1 / a)
  proof: calc
    1 / -a = 1 / (-1 * a) := by rw [neg_eq_neg_one_mul]
    _ = 1 / a * (1 / -1) := by rw [one_div_mul_one_div_rev]
    _ = 1 / a * -1 := by rw [one_div_neg_one_eq_neg_one]
    _ = -(1 / a) := by rw [mul_neg, mul_one]

中文:
引理 one_div_neg_eq_neg_one_div
  条件: (a : R)
  结论: 1 / -a = -(1 / a)
  证明: calc
    1 / -a = 1 / (-1 * a) := by rw [neg_eq_neg_one_mul]
    _ = 1 / a * (1 / -1) := by rw [one_div_mul_one_div_rev]
    _ = 1 / a * -1 := by rw [one_div_neg_one_eq_neg_one]
    _ = -(1 / a) := by rw [mul_neg, mul_one]

Depends on / 依赖: mul_neg, mul_one, neg_eq_neg_one_mul, one_div_mul_one_div_rev, one_div_neg_one_eq_neg_one
-/
lemma one_div_neg_eq_neg_one_div (a : R) : 1 / -a = -(1 / a) :=
  calc
    1 / -a = 1 / (-1 * a) := by rw [neg_eq_neg_one_mul]
    _ = 1 / a * (1 / -1) := by rw [one_div_mul_one_div_rev]
    _ = 1 / a * -1 := by rw [one_div_neg_one_eq_neg_one]
    _ = -(1 / a) := by rw [mul_neg, mul_one]

/--
lemma `div_neg_eq_neg_div` / 引理 `div_neg_eq_neg_div`

English:
lemma div_neg_eq_neg_div
  given: (a b : R)
  statement: b / -a = -(b / a)
  proof: calc
    b / -a = b * (1 / -a) := by rw [← inv_eq_one_div, division_def]
    _ = b * -(1 / a) := by rw [one_div_neg_eq_neg_one_div]
    _ = -(b * (1 / a)) := by rw [neg_mul_eq_mul_neg]
    _ = -(b / a) := by rw [mul_one_div]

中文:
引理 div_neg_eq_neg_div
  条件: (a b : R)
  结论: b / -a = -(b / a)
  证明: calc
    b / -a = b * (1 / -a) := by rw [← inv_eq_one_div, division_def]
    _ = b * -(1 / a) := by rw [one_div_neg_eq_neg_one_div]
    _ = -(b * (1 / a)) := by rw [neg_mul_eq_mul_neg]
    _ = -(b / a) := by rw [mul_one_div]

Depends on / 依赖: division_def, inv_eq_one_div, mul_one_div, neg_mul_eq_mul_neg, one_div_neg_eq_neg_one_div
-/
lemma div_neg_eq_neg_div (a b : R) : b / -a = -(b / a) :=
  calc
    b / -a = b * (1 / -a) := by rw [← inv_eq_one_div, division_def]
    _ = b * -(1 / a) := by rw [one_div_neg_eq_neg_one_div]
    _ = -(b * (1 / a)) := by rw [neg_mul_eq_mul_neg]
    _ = -(b / a) := by rw [mul_one_div]

/--
lemma `neg_div` / 引理 `neg_div`

English:
lemma neg_div
  given: (a b : R)
  statement: -b / a = -(b / a)
  proof: by
  rw [neg_eq_neg_one_mul]; rw [mul_div_assoc]; rw [← neg_eq_neg_one_mul]

中文:
引理 neg_div
  条件: (a b : R)
  结论: -b / a = -(b / a)
  证明: by
  rw [neg_eq_neg_one_mul]; rw [mul_div_assoc]; rw [← neg_eq_neg_one_mul]

Depends on / 依赖: mul_div_assoc, neg_eq_neg_one_mul
-/
lemma neg_div (a b : R) : -b / a = -(b / a) := by
  rw [neg_eq_neg_one_mul]; rw [mul_div_assoc]; rw [← neg_eq_neg_one_mul]

/--
lemma `neg_div'` / 引理 `neg_div'`

English:
lemma neg_div'
  given: (a b : R)
  statement: -(b / a) = -b / a
  proof: by rw [neg_div]

@[simp]

中文:
引理 neg_div'
  条件: (a b : R)
  结论: -(b / a) = -b / a
  证明: by rw [neg_div]

@[simp]

Depends on / 依赖: neg_div
-/
lemma neg_div' (a b : R) : -(b / a) = -b / a := by rw [neg_div]

@[simp]
/--
lemma `neg_div_neg_eq` / 引理 `neg_div_neg_eq`

English:
lemma neg_div_neg_eq
  given: (a b : R)
  statement: -a / -b = a / b
  proof: by rw [div_neg_eq_neg_div, neg_div, neg_neg]

中文:
引理 neg_div_neg_eq
  条件: (a b : R)
  结论: -a / -b = a / b
  证明: by rw [div_neg_eq_neg_div, neg_div, neg_neg]

Depends on / 依赖: div_neg_eq_neg_div, neg_div, neg_neg
-/
lemma neg_div_neg_eq (a b : R) : -a / -b = a / b := by rw [div_neg_eq_neg_div, neg_div, neg_neg]

/--
lemma `neg_inv` / 引理 `neg_inv`

English:
lemma neg_inv
  statement: -a⁻¹ = (-a)⁻¹
  proof: by rw [inv_eq_one_div, inv_eq_one_div, div_neg_eq_neg_div]

中文:
引理 neg_inv
  结论: -a⁻¹ = (-a)⁻¹
  证明: by rw [inv_eq_one_div, inv_eq_one_div, div_neg_eq_neg_div]

Depends on / 依赖: div_neg_eq_neg_div, inv_eq_one_div
-/
lemma neg_inv : -a⁻¹ = (-a)⁻¹ := by rw [inv_eq_one_div, inv_eq_one_div, div_neg_eq_neg_div]

/--
lemma `div_neg` / 引理 `div_neg`

English:
lemma div_neg
  given: (a : R)
  statement: a / -b = -(a / b)
  proof: by rw [← div_neg_eq_neg_div]

中文:
引理 div_neg
  条件: (a : R)
  结论: a / -b = -(a / b)
  证明: by rw [← div_neg_eq_neg_div]

Depends on / 依赖: div_neg_eq_neg_div
-/
lemma div_neg (a : R) : a / -b = -(a / b) := by rw [← div_neg_eq_neg_div]

/--
lemma `div_neg_eq_neg_div'` / 引理 `div_neg_eq_neg_div'`

English:
lemma div_neg_eq_neg_div'
  given: (a : R)
  statement: a / -b = -a / b
  proof: neg_div b a ▸ div_neg _

@[simp]

中文:
引理 div_neg_eq_neg_div'
  条件: (a : R)
  结论: a / -b = -a / b
  证明: neg_div b a ▸ div_neg _

@[simp]

Depends on / 依赖: div_neg, neg_div
-/
lemma div_neg_eq_neg_div' (a : R) : a / -b = -a / b := neg_div b a ▸ div_neg _

@[simp]
/--
lemma `inv_neg` / 引理 `inv_neg`

English:
lemma inv_neg
  statement: (-a)⁻¹ = -a⁻¹
  proof: by rw [neg_inv]

中文:
引理 inv_neg
  结论: (-a)⁻¹ = -a⁻¹
  证明: by rw [neg_inv]

Depends on / 依赖: neg_inv
-/
lemma inv_neg : (-a)⁻¹ = -a⁻¹ := by rw [neg_inv]

/--
lemma `inv_neg_one` / 引理 `inv_neg_one`

English:
lemma inv_neg_one
  statement: (-1 : R)⁻¹ = -1
  proof: by rw [← neg_inv, inv_one]

中文:
引理 inv_neg_one
  结论: (-1 : R)⁻¹ = -1
  证明: by rw [← neg_inv, inv_one]

Depends on / 依赖: inv_one, neg_inv
-/
lemma inv_neg_one : (-1 : R)⁻¹ = -1 := by rw [← neg_inv, inv_one]

end DivisionMonoid
