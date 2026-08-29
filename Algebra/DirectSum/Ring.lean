/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.GradedMonoid
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.Ring.Associator

/-!
# Additively-graded multiplicative structures on `⨁ i, A i`

This module provides a set of heterogeneous typeclasses for defining a multiplicative structure
over `⨁ i, A i` such that `(*) : A i → A j → A (i + j)`; that is to say, `A` forms an
additively-graded ring. The five typeclasses are:

* `DirectSum.GNonUnitalNonAssocSemiring A`
* `DirectSum.GSemiring A`
* `DirectSum.GRing A`
* `DirectSum.GCommSemiring A`
* `DirectSum.GCommRing A`

Respectively, these five typeclasses imbue the external direct sum `⨁ i, A i` with:

* `DirectSum.nonUnitalNonAssocSemiring`, `DirectSum.nonUnitalNonAssocRing`
* `DirectSum.semiring`
* `DirectSum.ring`
* `DirectSum.commSemiring`
* `DirectSum.commRing`

the base ring `A 0` with instances of these types:

* `NonUnitalNonAssocSemiring (A 0)`, `NonUnitalNonAssocRing (A 0)`
* `Semiring (A 0)`
* `Ring (A 0)`
* `CommSemiring (A 0)`
* `CommRing (A 0)`

and the `i`th grade `A i` with `A 0`-actions (`•`) of these types:

* `SMulWithZero (A 0) (A i)`
* `Module (A 0) (A i)`
* (nothing)
* (nothing)
* (nothing)

Note that in the presence of these instances, `⨁ i, A i` itself inherits an `A 0`-action.

`DirectSum.ofZeroRingHom : A 0 →+* ⨁ i, A i` provides `DirectSum.of A 0` as a ring
homomorphism.

`DirectSum.toSemiring` extends `DirectSum.toAddMonoid` to produce a `RingHom`.

## Direct sums of subobjects

Additionally, this module provides helper functions to construct `GSemiring` and `GCommSemiring`
instances for:

* `A : ι → Submonoid S`:
  `DirectSum.GSemiring.ofAddSubmonoids`, `DirectSum.GCommSemiring.ofAddSubmonoids`.
* `A : ι → Subgroup S`:
  `DirectSum.GSemiring.ofAddSubgroups`, `DirectSum.GCommSemiring.ofAddSubgroups`.
* `A : ι → Submodule S`:
  `DirectSum.GSemiring.ofSubmodules`, `DirectSum.GCommSemiring.ofSubmodules`.

If `sSupIndep A`, these provide a gradation of `⨆ i, A i`, and the mapping `⨁ i, A i →+ ⨆ i, A i`
can be obtained as `DirectSum.toMonoid (fun i ↦ AddSubmonoid.inclusion <| le_iSup A i)`.

## Implementation details

The instances on `A 0` are scoped to the `DirectSum` namespace, because they have
very general discriminantion tree keys.

## Tags

graded ring, filtered ring, direct sum, additive submonoid
-/

@[expose] public section


variable {ι : Type*} [DecidableEq ι]

namespace DirectSum

open DirectSum

/-! ### Typeclasses -/


section Defs

variable (A : ι -> Type*)

/--
Definition of `GNonUnitalNonAssocSemiring` / `GNonUnitalNonAssocSemiring` 的定义

English:
class GNonUnitalNonAssocSemiring
  parameters: [Add ι] [forall i, AddCommMonoid (A i)]
  axioms and operations (4):
    - mul_zero : forall {i j} (a : A i), mul a (0 : A j) = 0
    - zero_mul : forall {i j} (b : A j), mul (0 : A i) b = 0
    - mul_add : forall {i j} (a : A i) (b c : A j), mul a (b + c) = mul a b + mul a c
    - add_mul : forall {i j} (a b : A i) (c : A j), mul (a + b) c = mul a c + mul b c

中文:
类 GNonUnitalNonAssocSemiring
  参数: [加法 ι] [对任意 i, 加法交换幺半群 (A i)]
  公理与运算 (4 个):
    - mul_zero : 对任意 {i j} (a : A i), mul a (0 : A j) = 0
    - zero_mul : 对任意 {i j} (b : A j), mul (0 : A i) b = 0
    - mul_add : 对任意 {i j} (a : A i) (b c : A j), mul a (b + c) = mul a b + mul a c
    - add_mul : 对任意 {i j} (a b : A i) (c : A j), mul (a + b) c = mul a c + mul b c
-/
class GNonUnitalNonAssocSemiring [Add ι] [forall i, AddCommMonoid (A i)] extends
  GradedMonoid.GMul A where
  /-- Multiplication from the right with any graded component's zero vanishes. -/
  mul_zero : forall {i j} (a : A i), mul a (0 : A j) = 0
  /-- Multiplication from the left with any graded component's zero vanishes. -/
  zero_mul : forall {i j} (b : A j), mul (0 : A i) b = 0
  /-- Multiplication from the right between graded components distributes with respect to
  addition. -/
  mul_add : forall {i j} (a : A i) (b c : A j), mul a (b + c) = mul a b + mul a c
  /-- Multiplication from the left between graded components distributes with respect to
  addition. -/
  add_mul : forall {i j} (a b : A i) (c : A j), mul (a + b) c = mul a c + mul b c

end Defs

section Defs

variable (A : ι -> Type*)

/--
Definition of `GSemiring` / `GSemiring` 的定义

English:
class GSemiring
  parameters: [AddMonoid ι] [forall i, AddCommMonoid (A i)]
  extends: GNonUnitalNonAssocSemiring A, 
  axioms and operations (3):
    - natCast : Nat -> A 0
    - natCast_zero : natCast 0 = 0
    - natCast_succ : forall n : Nat, natCast (n + 1) = natCast n + GradedMonoid.GOne.one

中文:
类 GSemiring
  参数: [加法幺半群 ι] [对任意 i, 加法交换幺半群 (A i)]
  继承: GNonUnitalNonAssocSemiring A, 
  公理与运算 (3 个):
    - natCast : 自然数 -> A 0
    - natCast_zero : natCast 0 = 0
    - natCast_succ : 对任意 n : 自然数, natCast (n + 1) = natCast n + 分次幺半群.GOne.one
-/
class GSemiring [AddMonoid ι] [forall i, AddCommMonoid (A i)] extends GNonUnitalNonAssocSemiring A,
  GradedMonoid.GMonoid A where
  /-- The canonical map from ℕ to the zeroth component of a graded semiring. -/
  natCast : Nat -> A 0
  /-- The canonical map from ℕ to a graded semiring respects zero. -/
  natCast_zero : natCast 0 = 0
  /-- The canonical map from ℕ to a graded semiring respects successors. -/
  natCast_succ : forall n : Nat, natCast (n + 1) = natCast n + GradedMonoid.GOne.one

/--
Definition of `GCommSemiring` / `GCommSemiring` 的定义

English:
class GCommSemiring
  parameters: [AddCommMonoid ι] [forall i, AddCommMonoid (A i)]
  extends: GSemiring A, 
  (no additional axioms)

中文:
类 GCommSemiring
  参数: [加法交换幺半群 ι] [对任意 i, 加法交换幺半群 (A i)]
  继承: GSemiring A, 
  (无附加公理)
-/
class GCommSemiring [AddCommMonoid ι] [forall i, AddCommMonoid (A i)] extends GSemiring A,
  GradedMonoid.GCommMonoid A

/--
Definition of `GRing` / `GRing` 的定义

English:
class GRing
  parameters: [AddMonoid ι] [forall i, AddCommGroup (A i)]
  extends: GSemiring A
  axioms and operations (3):
    - intCast : Int -> A 0
    - intCast_ofNat : forall n : Nat, intCast n = natCast n
    - intCast_negSucc_ofNat : forall n : Nat, intCast (Int.negSucc n) = -natCast (n + 1 : Nat)

中文:
类 G环
  参数: [加法幺半群 ι] [对任意 i, 加法交换群 (A i)]
  继承: GSemiring A
  公理与运算 (3 个):
    - intCast : 整数 -> A 0
    - intCast_ofNat : 对任意 n : 自然数, intCast n = natCast n
    - intCast_negSucc_ofNat : 对任意 n : 自然数, intCast (整数.negSucc n) = -natCast (n + 1 : 自然数)
-/
class GRing [AddMonoid ι] [forall i, AddCommGroup (A i)] extends GSemiring A where
  /-- The canonical map from ℤ to the zeroth component of a graded ring. -/
  intCast : Int -> A 0
  /-- The canonical map from ℤ to a graded ring extends the canonical map from ℕ to the underlying
  graded semiring. -/
  intCast_ofNat : forall n : Nat, intCast n = natCast n
  /-- On negative integers, the canonical map from ℤ to a graded ring is the negative extension of
  the canonical map from ℕ to the underlying graded semiring. -/
  -- Porting note: -(n + 1) -> Int.negSucc
  intCast_negSucc_ofNat : forall n : Nat, intCast (Int.negSucc n) = -natCast (n + 1 : Nat)

/--
Definition of `GCommRing` / `GCommRing` 的定义

English:
class GCommRing
  parameters: [AddCommMonoid ι] [forall i, AddCommGroup (A i)]
  extends: GRing A, GCommSemiring A
  (no additional axioms)

中文:
类 GComm环
  参数: [加法交换幺半群 ι] [对任意 i, 加法交换群 (A i)]
  继承: G环 A, GCommSemiring A
  (无附加公理)
-/
class GCommRing [AddCommMonoid ι] [forall i, AddCommGroup (A i)] extends GRing A, GCommSemiring A

end Defs

/--
theorem `of_eq_of_gradedMonoid_eq` / 定理 `of_eq_of_gradedMonoid_eq`

English:
theorem of_eq_of_gradedMonoid_eq
  statement: {A : ι -> Type*} [forall i : ι, AddCommMonoid (A i)] {i j : ι} {a : A i}
  proof: DFinsupp.single_eq_of_sigma_eq h

中文:
定理 of_eq_of_gradedMonoid_eq
  结论: {A : ι -> 类型} [对任意 i : ι, 加法交换幺半群 (A i)] {i j : ι} {a : A i}
  证明: DFinsupp.single_eq_of_sigma_eq h

Depends on / 依赖: DFinsupp, DFinsupp.single_eq_of_sigma_eq, single_eq_of_sigma_eq
-/
theorem of_eq_of_gradedMonoid_eq {A : ι -> Type*} [forall i : ι, AddCommMonoid (A i)] {i j : ι} {a : A i}
    {b : A j} (h : GradedMonoid.mk i a = GradedMonoid.mk j b) :
    DirectSum.of A i a = DirectSum.of A j b :=
  DFinsupp.single_eq_of_sigma_eq h

variable (A : ι -> Type*)

/-! ### Instances for `⨁ i, A i` -/


section One

variable [Zero ι] [GradedMonoid.GOne A] [forall i, AddCommMonoid (A i)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (⨁ i, A i)
  body: DirectSum.of A 0 GradedMonoid.GOne.one

中文:
实例 :
  签名: 幺 (⨁ i, A i)
  定义体: DirectSum.of A 0 GradedMonoid.GOne.one

Depends on / 依赖: DirectSum, DirectSum.of, GradedMonoid, GradedMonoid.GOne.one
-/
instance : One (⨁ i, A i) where one := DirectSum.of A 0 GradedMonoid.GOne.one

/--
theorem `one_def` / 定理 `one_def`

English:
theorem one_def
  statement: 1 = DirectSum.of A 0 GradedMonoid.GOne.one
  proof: rfl

中文:
定理 one_def
  结论: 1 = 直和.of A 0 分次幺半群.GOne.one
  证明: rfl
-/
theorem one_def : 1 = DirectSum.of A 0 GradedMonoid.GOne.one := rfl

end One

section Mul

variable [Add ι] [forall i, AddCommMonoid (A i)] [GNonUnitalNonAssocSemiring A]

open AddMonoidHom (flip_apply coe_comp compHom)

/-- The piecewise multiplication from the `Mul` instance, as a bundled homomorphism. -/
@[simps]
/--
Definition of `gMulHom` / `gMulHom` 的定义

English:
definition gMulHom
  signature: {i j}
  body: { toFun := fun b => GradedMonoid.GMul.mul a b
      map_zero' := GNonUnitalNonAssocSemiring.mul_zero _
      map_add' := GNonUnitalNonAssocSemiring.mul_add _ }
  map_zero' := AddMonoidHom.ext fun a => GNonUnitalNonAssocSemiring.zero_mul a
  map_add' _ _ := AddMonoidHom.ext fun _ => GNonUnitalNonAsso

中文:
定义 gMulHom
  签名: {i j}
  定义体: { toFun := fun b => GradedMonoid.GMul.mul a b
      map_zero' := GNonUnitalNonAssocSemiring.mul_zero _
      map_add' := GNonUnitalNonAssocSemiring.mul_add _ }
  map_zero' := AddMonoidHom.ext fun a => GNonUnitalNonAssocSemiring.zero_mul a
  map_add' _ _ := AddMonoidHom.ext fun _ => GNonUnitalNonAsso

Depends on / 依赖: AddMonoidHom, AddMonoidHom.ext, GNonUnitalNonAssocSemiring, GNonUnitalNonAssocSemiring.add_mul, GNonUnitalNonAssocSemiring.mul_add, GNonUnitalNonAssocSemiring.mul_zero, GNonUnitalNonAssocSemiring.zero_mul, GradedMonoid, GradedMonoid.GMul.mul, add_mul, map_add, map_zero, mul_add, mul_zero, zero_mul
-/
def gMulHom {i j} : A i ->+ A j ->+ A (i + j) where
  toFun a :=
    { toFun := fun b => GradedMonoid.GMul.mul a b
      map_zero' := GNonUnitalNonAssocSemiring.mul_zero _
      map_add' := GNonUnitalNonAssocSemiring.mul_add _ }
  map_zero' := AddMonoidHom.ext fun a => GNonUnitalNonAssocSemiring.zero_mul a
  map_add' _ _ := AddMonoidHom.ext fun _ => GNonUnitalNonAssocSemiring.add_mul _ _ _

/-- The multiplication from the `Mul` instance, as a bundled homomorphism. -/
-- See note [non-reducible instance]
@[reducible]
/--
Definition of `mulHom` / `mulHom` 的定义

English:
definition mulHom
  signature: : (⨁ i, A i) ->+ (⨁ i, A i) ->+ ⨁ i, A i
  body: DirectSum.toAddMonoid fun _ =>
AddMonoidHom.flip
      DirectSum.toAddMonoid fun _ =>
AddMonoidHom.flip (DirectSum.of A _).compHom.comp gMulHom A

中文:
定义 mulHom
  签名: : (⨁ i, A i) ->+ (⨁ i, A i) ->+ ⨁ i, A i
  定义体: DirectSum.toAddMonoid fun _ =>
AddMonoidHom.flip
      DirectSum.toAddMonoid fun _ =>
AddMonoidHom.flip (DirectSum.of A _).compHom.comp gMulHom A

Depends on / 依赖: AddMonoidHom, AddMonoidHom.flip, DirectSum, DirectSum.of, DirectSum.toAddMonoid, compHom, compHom.comp, gMulHom, toAddMonoid
-/
def mulHom : (⨁ i, A i) ->+ (⨁ i, A i) ->+ ⨁ i, A i :=
  DirectSum.toAddMonoid fun _ =>
AddMonoidHom.flip
      DirectSum.toAddMonoid fun _ =>
AddMonoidHom.flip (DirectSum.of A _).compHom.comp gMulHom A

/--
Instance `instMul` / 实例 `instMul`

English:
instance instMul
  signature: : Mul (⨁ i, A i) where
  body: fun a b => mulHom A a b

中文:
实例 instMul
  签名: : 乘法 (⨁ i, A i) where
  定义体: fun a b => mulHom A a b

Depends on / 依赖: mulHom
-/
instance instMul : Mul (⨁ i, A i) where
  mul := fun a b => mulHom A a b

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NonUnitalNonAssocSemiring (⨁ i, A i)
  body: fun _ => by simp only [Mul.mul, HMul.hMul, map_zero, AddMonoidHom.zero_apply]
  mul_zero := fun _ => by simp only [Mul.mul, HMul.hMul, map_zero]
  left_distrib := fun _ _ _ => by simp only [Mul.mul, HMul.hMul, map_add]
  right_distrib := fun _ _ _ => by
    simp only [Mul.mul, HMul.hMul, map_add, Ad

中文:
实例 :
  签名: 非幺非结合半环 (⨁ i, A i)
  定义体: fun _ => by simp only [Mul.mul, HMul.hMul, map_zero, AddMonoidHom.zero_apply]
  mul_zero := fun _ => by simp only [Mul.mul, HMul.hMul, map_zero]
  left_distrib := fun _ _ _ => by simp only [Mul.mul, HMul.hMul, map_add]
  right_distrib := fun _ _ _ => by
    simp only [Mul.mul, HMul.hMul, map_add, Ad

Depends on / 依赖: AddMonoidHom, AddMonoidHom.zero_apply, HMul.hMul, Mul.mul, map_zero, zero_apply
-/
instance : NonUnitalNonAssocSemiring (⨁ i, A i) where
  zero_mul := fun _ => by simp only [Mul.mul, HMul.hMul, map_zero, AddMonoidHom.zero_apply]
  mul_zero := fun _ => by simp only [Mul.mul, HMul.hMul, map_zero]
  left_distrib := fun _ _ _ => by simp only [Mul.mul, HMul.hMul, map_add]
  right_distrib := fun _ _ _ => by
    simp only [Mul.mul, HMul.hMul, map_add, AddMonoidHom.add_apply]

variable {A}

/--
theorem `mulHom_apply` / 定理 `mulHom_apply`

English:
theorem mulHom_apply
  given: (a b : ⨁ i, A i)
  statement: mulHom A a b = a * b
  proof: rfl

中文:
定理 mulHom_apply
  条件: (a b : ⨁ i, A i)
  结论: mulHom A a b = a * b
  证明: rfl
-/
theorem mulHom_apply (a b : ⨁ i, A i) : mulHom A a b = a * b := rfl

/--
theorem `mulHom_of_of` / 定理 `mulHom_of_of`

English:
theorem mulHom_of_of
  given: {i j} (a : A i) (b : A j)
  proof: by
  simp

中文:
定理 mulHom_of_of
  条件: {i j} (a : A i) (b : A j)
  证明: by
  simp
-/
theorem mulHom_of_of {i j} (a : A i) (b : A j) :
    mulHom A (of A i a) (of A j b) = of A (i + j) (GradedMonoid.GMul.mul a b) := by
  simp

/--
theorem `of_mul_of` / 定理 `of_mul_of`

English:
theorem of_mul_of
  given: {i j} (a : A i) (b : A j)
  proof: mulHom_of_of a b

中文:
定理 of_mul_of
  条件: {i j} (a : A i) (b : A j)
  证明: mulHom_of_of a b

Depends on / 依赖: mulHom_of_of
-/
theorem of_mul_of {i j} (a : A i) (b : A j) :
    of A i a * of A j b = of _ (i + j) (GradedMonoid.GMul.mul a b) :=
  mulHom_of_of a b

end Mul

section Semiring

variable [forall i, AddCommMonoid (A i)] [AddMonoid ι] [GSemiring A]

open AddMonoidHom (flipHom coe_comp compHom flip_apply)

private nonrec theorem one_mul (x : ⨁ i, A i) : 1 * x = x := by
  suffices mulHom A One.one = AddMonoidHom.id (⨁ i, A i) from DFunLike.congr_fun this x
  apply addHom_ext; intro i xi
  simp only [One.one]
  rw [mulHom_of_of]
  exact of_eq_of_gradedMonoid_eq (one_mul <| GradedMonoid.mk i xi)

private nonrec theorem mul_one (x : ⨁ i, A i) : x * 1 = x := by
  suffices (mulHom A).flip One.one = AddMonoidHom.id (⨁ i, A i) from DFunLike.congr_fun this x
  apply addHom_ext; intro i xi
  simp only [One.one]
  rw [flip_apply]; rw [mulHom_of_of]
  exact of_eq_of_gradedMonoid_eq (mul_one <| GradedMonoid.mk i xi)

set_option backward.defeqAttrib.useBackward true in
/--
theorem `mul_assoc` / 定理 `mul_assoc`

English:
theorem mul_assoc
  given: (a b c : ⨁ i, A i)
  statement: a * b * c = a * (b * c)
  proof: by
  -- (`fun a b c => a * b * c` as a bundled hom) = (`fun a b c => a * (b * c)` as a bundled hom)
  suffices AddMonoidHom.mulLeft₃ = AddMonoidHom.mulRight₃ by
      simpa only [AddMonoidHom.mulLeft₃_apply, AddMonoidHom.mulRight₃_apply] using
        DFunLike.congr_fun (DFunLike.congr_fun (DFunLike

中文:
定理 mul_assoc
  条件: (a b c : ⨁ i, A i)
  结论: a * b * c = a * (b * c)
  证明: by
  -- (`fun a b c => a * b * c` as a bundled hom) = (`fun a b c => a * (b * c)` as a bundled hom)
  suffices AddMonoidHom.mulLeft₃ = AddMonoidHom.mulRight₃ by
      simpa only [AddMonoidHom.mulLeft₃_apply, AddMonoidHom.mulRight₃_apply] using
        DFunLike.congr_fun (DFunLike.congr_fun (DFunLike
-/
private theorem mul_assoc (a b c : ⨁ i, A i) : a * b * c = a * (b * c) := by
  -- (`fun a b c => a * b * c` as a bundled hom) = (`fun a b c => a * (b * c)` as a bundled hom)
  suffices AddMonoidHom.mulLeft₃ = AddMonoidHom.mulRight₃ by
      simpa only [AddMonoidHom.mulLeft₃_apply, AddMonoidHom.mulRight₃_apply] using
        DFunLike.congr_fun (DFunLike.congr_fun (DFunLike.congr_fun this a) b) c
  ext ai ax bi bx ci cx : 6
  dsimp only [coe_comp, Function.comp_apply, AddMonoidHom.mulLeft₃_apply,
    AddMonoidHom.mulRight₃_apply]
  simp_rw [of_mul_of]
  exact of_eq_of_gradedMonoid_eq (_root_.mul_assoc (GradedMonoid.mk ai ax) ⟨bi, bx⟩ ⟨ci, cx⟩)

/--
Instance `instNatCast` / 实例 `instNatCast`

English:
instance instNatCast
  signature: : NatCast (⨁ i, A i) where
  body: fun n => of _ _ (GSemiring.natCast n)

中文:
实例 inst自然数Cast
  签名: : 自然数嵌入 (⨁ i, A i) where
  定义体: fun n => of _ _ (GSemiring.natCast n)

Depends on / 依赖: GSemiring, GSemiring.natCast, natCast
-/
instance instNatCast : NatCast (⨁ i, A i) where
  natCast := fun n => of _ _ (GSemiring.natCast n)

/--
Instance `semiring` / 实例 `semiring`

English:
instance semiring
  signature: : Semiring (⨁ i, A i) where
  body: private one_mul A
  mul_one := private mul_one A
  mul_assoc := private mul_assoc A
  toNatCast := instNatCast _
  natCast_zero := by simp only [NatCast.natCast, GSemiring.natCast_zero, map_zero]
  natCast_succ := fun n => by
    simp_rw [NatCast.natCast, GSemiring.natCast_succ]
    rw [map_add]
   

中文:
实例 semiring
  签名: : 半环 (⨁ i, A i) where
  定义体: private one_mul A
  mul_one := private mul_one A
  mul_assoc := private mul_assoc A
  toNatCast := instNatCast _
  natCast_zero := by simp only [NatCast.natCast, GSemiring.natCast_zero, map_zero]
  natCast_succ := fun n => by
    simp_rw [NatCast.natCast, GSemiring.natCast_succ]
    rw [map_add]
   

Depends on / 依赖: one_mul, private
-/
instance semiring : Semiring (⨁ i, A i) where
  one_mul := private one_mul A
  mul_one := private mul_one A
  mul_assoc := private mul_assoc A
  toNatCast := instNatCast _
  natCast_zero := by simp only [NatCast.natCast, GSemiring.natCast_zero, map_zero]
  natCast_succ := fun n => by
    simp_rw [NatCast.natCast, GSemiring.natCast_succ]
    rw [map_add]
    rfl

/--
theorem `ofPow` / 定理 `ofPow`

English:
theorem ofPow
  given: {i} (a : A i) (n : Nat)
  proof: by
  induction n with
  | zero => exact of_eq_of_gradedMonoid_eq (pow_zero <| GradedMonoid.mk _ a).symm
  | succ n n_ih =>
    rw [pow_succ]; rw [n_ih]; rw [of_mul_of]
    exact of_eq_of_gradedMonoid_eq (pow_succ (GradedMonoid.mk _ a) n).symm

中文:
定理 ofPow
  条件: {i} (a : A i) (n : 自然数)
  证明: by
  induction n with
  | zero => exact of_eq_of_gradedMonoid_eq (pow_zero <| GradedMonoid.mk _ a).symm
  | succ n n_ih =>
    rw [pow_succ]; rw [n_ih]; rw [of_mul_of]
    exact of_eq_of_gradedMonoid_eq (pow_succ (GradedMonoid.mk _ a) n).symm

Depends on / 依赖: GradedMonoid, GradedMonoid.mk, n_ih, of_eq_of_gradedMonoid_eq, of_mul_of, pow_succ, pow_zero
-/
theorem ofPow {i} (a : A i) (n : Nat) :
    of _ i a ^ n = of _ (n • i) (GradedMonoid.GMonoid.gnpow _ a) := by
  induction n with
  | zero => exact of_eq_of_gradedMonoid_eq (pow_zero <| GradedMonoid.mk _ a).symm
  | succ n n_ih =>
    rw [pow_succ]; rw [n_ih]; rw [of_mul_of]
    exact of_eq_of_gradedMonoid_eq (pow_succ (GradedMonoid.mk _ a) n).symm

/--
theorem `ofList_dProd` / 定理 `ofList_dProd`

English:
theorem ofList_dProd
  given: {α} (l : List α) (fι : α -> ι) (fA : forall a, A (fι a))
  proof: by
  induction l with
  | nil => simp only [List.map_nil, List.prod_nil, List.dProd_nil]; rfl
  | cons head tail =>
    rename_i ih
    simp only [List.map_cons, List.prod_cons, List.dProd_cons, ← ih]
    rw [DirectSum.of_mul_of (fA head)]
    rfl

中文:
定理 ofList_dProd
  条件: {α} (l : 列表 α) (fι : α -> ι) (fA : 对任意 a, A (fι a))
  证明: by
  induction l with
  | nil => simp only [List.map_nil, List.prod_nil, List.dProd_nil]; rfl
  | cons head tail =>
    rename_i ih
    simp only [List.map_cons, List.prod_cons, List.dProd_cons, ← ih]
    rw [DirectSum.of_mul_of (fA head)]
    rfl

Depends on / 依赖: DirectSum, DirectSum.of_mul_of, List.dProd_cons, List.dProd_nil, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, dProd_cons, dProd_nil, map_cons, map_nil, of_mul_of, prod_cons, prod_nil, rename_i
-/
theorem ofList_dProd {α} (l : List α) (fι : α -> ι) (fA : forall a, A (fι a)) :
    of A _ (l.dProd fι fA) = (l.map fun a => of A (fι a) (fA a)).prod := by
  induction l with
  | nil => simp only [List.map_nil, List.prod_nil, List.dProd_nil]; rfl
  | cons head tail =>
    rename_i ih
    simp only [List.map_cons, List.prod_cons, List.dProd_cons, ← ih]
    rw [DirectSum.of_mul_of (fA head)]
    rfl

/--
theorem `list_prod_ofFn_of_eq_dProd` / 定理 `list_prod_ofFn_of_eq_dProd`

English:
theorem list_prod_ofFn_of_eq_dProd
  given: (n : Nat) (fι : Fin n -> ι) (fA : forall a, A (fι a))
  proof: by
  rw [List.ofFn_eq_map]; rw [ofList_dProd]

中文:
定理 list_prod_ofFn_of_eq_dProd
  条件: (n : 自然数) (fι : 有限集 n -> ι) (fA : 对任意 a, A (fι a))
  证明: by
  rw [List.ofFn_eq_map]; rw [ofList_dProd]

Depends on / 依赖: List.ofFn_eq_map, ofFn_eq_map, ofList_dProd
-/
theorem list_prod_ofFn_of_eq_dProd (n : Nat) (fι : Fin n -> ι) (fA : forall a, A (fι a)) :
    (List.ofFn fun a => of A (fι a) (fA a)).prod = of A _ ((List.finRange n).dProd fι fA) := by
  rw [List.ofFn_eq_map]; rw [ofList_dProd]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mul_eq_dfinsuppSum` / 定理 `mul_eq_dfinsuppSum`

English:
theorem mul_eq_dfinsuppSum
  given: [forall (i : ι) (x : A i), Decidable (x != 0)] (a a' : ⨁ i, A i)
  proof: by
  change mulHom _ a a' = _
  -- Porting note: I have no idea how the proof from ml3 worked it used to be
  -- simpa only [mul_hom, to_add_monoid, dfinsupp.lift_add_hom_apply, dfinsupp.sum_add_hom_apply,
  -- add_monoid_hom.dfinsupp_sum_apply, flip_apply, add_monoid_hom.dfinsupp_sum_add_hom_apply]

中文:
定理 mul_eq_dfinsuppSum
  条件: [对任意 (i : ι) (x : A i), 可判定 (x != 0)] (a a' : ⨁ i, A i)
  证明: by
  change mulHom _ a a' = _
  -- Porting note: I have no idea how the proof from ml3 worked it used to be
  -- simpa only [mul_hom, to_add_monoid, dfinsupp.lift_add_hom_apply, dfinsupp.sum_add_hom_apply,
  -- add_monoid_hom.dfinsupp_sum_apply, flip_apply, add_monoid_hom.dfinsupp_sum_add_hom_apply]

Depends on / 依赖: mulHom
-/
theorem mul_eq_dfinsuppSum [forall (i : ι) (x : A i), Decidable (x != 0)] (a a' : ⨁ i, A i) :
    a * a'
= a.sum fun _ ai => a'.sum fun _ aj => DirectSum.of _ _ GradedMonoid.GMul.mul ai aj := by
  change mulHom _ a a' = _
  -- Porting note: I have no idea how the proof from ml3 worked it used to be
  -- simpa only [mul_hom, to_add_monoid, dfinsupp.lift_add_hom_apply, dfinsupp.sum_add_hom_apply,
  -- add_monoid_hom.dfinsupp_sum_apply, flip_apply, add_monoid_hom.dfinsupp_sum_add_hom_apply],
  rw [mulHom]; rw [toAddMonoid]; rw [DFinsupp.liftAddHom_apply]
  dsimp only [DirectSum]
  rw [DFinsupp.sumAddHom_apply]; rw [AddMonoidHom.dfinsuppSum_apply]
  apply congrArg _
  funext x
  simp [AddMonoidHom.dfinsuppSum_apply, DFinsupp.sumAddHom_apply, DirectSum.toAddMonoid]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mul_eq_sum_support_ghas_mul` / 定理 `mul_eq_sum_support_ghas_mul`

English:
theorem mul_eq_sum_support_ghas_mul
  given: [forall (i : ι) (x : A i), Decidable (x != 0)] (a a' : ⨁ i, A i)
  proof: by
  simp only [mul_eq_dfinsuppSum, DFinsupp.sum, Finset.sum_product]

中文:
定理 mul_eq_sum_support_ghas_mul
  条件: [对任意 (i : ι) (x : A i), 可判定 (x != 0)] (a a' : ⨁ i, A i)
  证明: by
  simp only [mul_eq_dfinsuppSum, DFinsupp.sum, Finset.sum_product]

Depends on / 依赖: DFinsupp, DFinsupp.sum, Finset, Finset.sum_product, mul_eq_dfinsuppSum, sum_product
-/
theorem mul_eq_sum_support_ghas_mul [forall (i : ι) (x : A i), Decidable (x != 0)] (a a' : ⨁ i, A i) :
    a * a' =
      ∑ ij in DFinsupp.support a ×ˢ DFinsupp.support a',
        DirectSum.of _ _ (GradedMonoid.GMul.mul (a ij.fst) (a' ij.snd)) := by
  simp only [mul_eq_dfinsuppSum, DFinsupp.sum, Finset.sum_product]

end Semiring

section CommSemiring

variable [forall i, AddCommMonoid (A i)] [AddCommMonoid ι] [GCommSemiring A]

/--
theorem `mul_comm` / 定理 `mul_comm`

English:
theorem mul_comm
  given: (a b : ⨁ i, A i)
  statement: a * b = b * a
  proof: by
  suffices mulHom A = (mulHom A).flip by
    rw [← mulHom_apply]; rw [this]; rw [AddMonoidHom.flip_apply]; rw [mulHom_apply]
  apply addHom_ext; intro ai ax; apply addHom_ext; intro bi bx
  rw [AddMonoidHom.flip_apply]; rw [mulHom_of_of]; rw [mulHom_of_of]
  exact of_eq_of_gradedMonoid_eq (GCommS

中文:
定理 mul_comm
  条件: (a b : ⨁ i, A i)
  结论: a * b = b * a
  证明: by
  suffices mulHom A = (mulHom A).flip by
    rw [← mulHom_apply]; rw [this]; rw [AddMonoidHom.flip_apply]; rw [mulHom_apply]
  apply addHom_ext; intro ai ax; apply addHom_ext; intro bi bx
  rw [AddMonoidHom.flip_apply]; rw [mulHom_of_of]; rw [mulHom_of_of]
  exact of_eq_of_gradedMonoid_eq (GCommS
-/
private theorem mul_comm (a b : ⨁ i, A i) : a * b = b * a := by
  suffices mulHom A = (mulHom A).flip by
    rw [← mulHom_apply]; rw [this]; rw [AddMonoidHom.flip_apply]; rw [mulHom_apply]
  apply addHom_ext; intro ai ax; apply addHom_ext; intro bi bx
  rw [AddMonoidHom.flip_apply]; rw [mulHom_of_of]; rw [mulHom_of_of]
  exact of_eq_of_gradedMonoid_eq (GCommSemiring.mul_comm ⟨ai, ax⟩ ⟨bi, bx⟩)

/--
Instance `commSemiring` / 实例 `commSemiring`

English:
instance commSemiring
  signature: : CommSemiring (⨁ i, A i) where
  body: private mul_comm A

中文:
实例 commSemiring
  签名: : 交换半环 (⨁ i, A i) where
  定义体: private mul_comm A

Depends on / 依赖: mul_comm, private
-/
instance commSemiring : CommSemiring (⨁ i, A i) where
  mul_comm := private mul_comm A

end CommSemiring

section NonUnitalNonAssocRing

variable [forall i, AddCommGroup (A i)] [Add ι] [GNonUnitalNonAssocSemiring A]

/--
Instance `nonAssocRing` / 实例 `nonAssocRing`

English:
instance nonAssocRing
  signature: : NonUnitalNonAssocRing (⨁ i, A i) where

中文:
实例 nonAssocRing
  签名: : 非幺非结合环 (⨁ i, A i) where
-/
instance nonAssocRing : NonUnitalNonAssocRing (⨁ i, A i) where

end NonUnitalNonAssocRing

section Ring

variable [forall i, AddCommGroup (A i)] [AddMonoid ι] [GRing A]

-- Porting note: overspecified fields in ml4
/--
Instance `ring` / 实例 `ring`

English:
instance ring
  signature: : Ring (⨁ i, A i) where
  body: of A 0 (GRing.intCast z)
intCast_ofNat _ := congrArg (of A 0) GRing.intCast_ofNat _
  intCast_negSucc _ :=
(congrArg (of A 0) <| GRing.intCast_negSucc_ofNat _).trans map_neg _ _

中文:
实例 ring
  签名: : 环 (⨁ i, A i) where
  定义体: of A 0 (GRing.intCast z)
intCast_ofNat _ := congrArg (of A 0) GRing.intCast_ofNat _
  intCast_negSucc _ :=
(congrArg (of A 0) <| GRing.intCast_negSucc_ofNat _).trans map_neg _ _

Depends on / 依赖: GRing.intCast, intCast
-/
instance ring : Ring (⨁ i, A i) where
toIntCast.intCast z := of A 0 (GRing.intCast z)
intCast_ofNat _ := congrArg (of A 0) GRing.intCast_ofNat _
  intCast_negSucc _ :=
(congrArg (of A 0) <| GRing.intCast_negSucc_ofNat _).trans map_neg _ _

end Ring

section CommRing

variable [forall i, AddCommGroup (A i)] [AddCommMonoid ι] [GCommRing A]

/--
Instance `commRing` / 实例 `commRing`

English:
instance commRing
  signature: : CommRing (⨁ i, A i) where

中文:
实例 commRing
  签名: : 交换环 (⨁ i, A i) where
-/
instance commRing : CommRing (⨁ i, A i) where

end CommRing

/-! ### Instances for `A 0`

The various `G*` instances are enough to promote the `AddCommMonoid (A 0)` structure to various
types of multiplicative structure.

Implementation detail: Note that these instances on `A 0` have very general discrimination
tree keys (e.g. `DirectSum.instRingOfNat` has discrimination tree key `Ring _` and often
sends typeclass inference on a wild goose chase with any goal of the form `Ring (F X)`),
so we scope these instances to the `DirectSum` namespace.

-/


section GradeZero

section One

variable [Zero ι] [GradedMonoid.GOne A] [forall i, AddCommMonoid (A i)]

@[simp]
/--
theorem `of_zero_one` / 定理 `of_zero_one`

English:
theorem of_zero_one
  statement: of _ 0 (1 : A 0) = 1
  proof: rfl

中文:
定理 of_zero_one
  结论: of _ 0 (1 : A 0) = 1
  证明: rfl
-/
theorem of_zero_one : of _ 0 (1 : A 0) = 1 :=
  rfl

end One

section Mul

variable [AddZeroClass ι] [forall i, AddCommMonoid (A i)] [GNonUnitalNonAssocSemiring A]

@[simp]
/--
theorem `of_zero_smul` / 定理 `of_zero_smul`

English:
theorem of_zero_smul
  given: {i} (a : A 0) (b : A i)
  statement: of _ _ (a • b) = of _ _ a * of _ _ b
  proof: (of_eq_of_gradedMonoid_eq (GradedMonoid.mk_zero_smul a b)).trans (of_mul_of _ _).symm

@[simp]

中文:
定理 of_zero_smul
  条件: {i} (a : A 0) (b : A i)
  结论: of _ _ (a • b) = of _ _ a * of _ _ b
  证明: (of_eq_of_gradedMonoid_eq (GradedMonoid.mk_zero_smul a b)).trans (of_mul_of _ _).symm

@[simp]

Depends on / 依赖: GradedMonoid, GradedMonoid.mk_zero_smul, mk_zero_smul, of_eq_of_gradedMonoid_eq, of_mul_of
-/
theorem of_zero_smul {i} (a : A 0) (b : A i) : of _ _ (a • b) = of _ _ a * of _ _ b :=
  (of_eq_of_gradedMonoid_eq (GradedMonoid.mk_zero_smul a b)).trans (of_mul_of _ _).symm

@[simp]
/--
theorem `of_zero_mul` / 定理 `of_zero_mul`

English:
theorem of_zero_mul
  given: (a b : A 0)
  statement: of _ 0 (a * b) = of _ 0 a * of _ 0 b
  proof: of_zero_smul A a b

中文:
定理 of_zero_mul
  条件: (a b : A 0)
  结论: of _ 0 (a * b) = of _ 0 a * of _ 0 b
  证明: of_zero_smul A a b

Depends on / 依赖: of_zero_smul
-/
theorem of_zero_mul (a b : A 0) : of _ 0 (a * b) = of _ 0 a * of _ 0 b :=
  of_zero_smul A a b

/-- The `NonUnitalNonAssocSemiring` structure on the grade zero part
of a `GNonUnitalNonAssocSemiring`. -/
scoped instance (priority := 900) :
    NonUnitalNonAssocSemiring (A 0) :=
  Function.Injective.nonUnitalNonAssocSemiring (of A 0) DFinsupp.single_injective (of A 0).map_zero
    (of A 0).map_add (of_zero_mul A) (map_nsmul _)

/-- The `SMulWithZero` structure on the grade zero part
of a `GNonUnitalNonAssocSemiring`. -/
scoped instance (i : ι) : SMulWithZero (A 0) (A i) := by
  letI := SMulWithZero.compHom (⨁ i, A i) (of A 0).toZeroHom
  exact Function.Injective.smulWithZero (of A i).toZeroHom DFinsupp.single_injective
    (of_zero_smul A)

end Mul

section Semiring

variable [forall i, AddCommMonoid (A i)] [AddMonoid ι] [GSemiring A]

@[simp]
/--
theorem `of_zero_pow` / 定理 `of_zero_pow`

English:
theorem of_zero_pow
  given: (a : A 0)
  statement: forall n : Nat, of A 0 (a ^ n) = of A 0 a ^ n

中文:
定理 of_zero_pow
  条件: (a : A 0)
  结论: 对任意 n : 自然数, of A 0 (a ^ n) = of A 0 a ^ n

Depends on / 依赖: NatCast
-/
theorem of_zero_pow (a : A 0) : forall n : Nat, of A 0 (a ^ n) = of A 0 a ^ n
  | 0 => by rw [pow_zero, pow_zero, DirectSum.of_zero_one]
  -- Porting note: Lean doesn't think this terminates if we only use `of_zero_pow` alone
  | n + 1 => by rw [pow_succ, pow_succ, of_zero_mul, of_zero_pow _ n]

/-- The `NatCast` instance on `A 0`, given `GSemiring A`. -/
scoped instance (priority := 900) : NatCast (A 0) :=
  ⟨GSemiring.natCast⟩


-- TODO: These could be replaced by the general lemmas for `AddMonoidHomClass` (`map_natCast'` and
-- `map_ofNat'`) if those were marked `@[simp low]`.
@[simp]
/--
theorem `of_natCast` / 定理 `of_natCast`

English:
theorem of_natCast
  given: (n : Nat)
  statement: of A 0 n = n
  proof: rfl

@[simp]

中文:
定理 of_natCast
  条件: (n : 自然数)
  结论: of A 0 n = n
  证明: rfl

@[simp]
-/
theorem of_natCast (n : Nat) : of A 0 n = n :=
  rfl

@[simp]
/--
theorem `of_zero_ofNat` / 定理 `of_zero_ofNat`

English:
theorem of_zero_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  statement: of A 0 ofNat(n) = ofNat(n)
  proof: of_natCast A n

中文:
定理 of_zero_of自然数
  条件: (n : 自然数) [n.AtLeastTwo]
  结论: of A 0 of自然数(n) = of自然数(n)
  证明: of_natCast A n

Depends on / 依赖: of_natCast
-/
theorem of_zero_ofNat (n : Nat) [n.AtLeastTwo] : of A 0 ofNat(n) = ofNat(n) :=
  of_natCast A n

/-- The `Semiring` structure derived from `GSemiring A`. -/
scoped instance (priority := 900) : Semiring (A 0) :=
  Function.Injective.semiring (of A 0) DFinsupp.single_injective (of A 0).map_zero (of_zero_one A)
    (of A 0).map_add (of_zero_mul A) (fun _ _ => (of A 0).map_nsmul _ _)
    (fun _ _ => of_zero_pow _ _ _) (of_natCast A)

/--
Definition of `ofZeroRingHom` / `ofZeroRingHom` 的定义

English:
definition ofZeroRingHom
  signature: : A 0 ->+* ⨁ i, A i
  body: { of _ 0 with
    map_one' := of_zero_one A
    map_mul' := of_zero_mul A }

中文:
定义 ofZeroRingHom
  签名: : A 0 ->+* ⨁ i, A i
  定义体: { of _ 0 with
    map_one' := of_zero_one A
    map_mul' := of_zero_mul A }

Depends on / 依赖: map_mul, map_one, of_zero_mul, of_zero_one
-/
def ofZeroRingHom : A 0 ->+* ⨁ i, A i :=
  { of _ 0 with
    map_one' := of_zero_one A
    map_mul' := of_zero_mul A }

/-- Each grade `A i` derives an `A 0`-module structure from `GSemiring A`. Note that this results
in an overall `Module (A 0) (⨁ i, A i)` structure via `DirectSum.module`.
-/
scoped instance {i} : Module (A 0) (A i) :=
  letI := Module.compHom (⨁ i, A i) (ofZeroRingHom A)
  DFinsupp.single_injective.module (A 0) (of A i) fun a => of_zero_smul A a

end Semiring

section CommSemiring

variable [forall i, AddCommMonoid (A i)] [AddCommMonoid ι] [GCommSemiring A]

/-- The `CommSemiring` structure derived from `GCommSemiring A`. -/
scoped instance (priority := 900) : CommSemiring (A 0) :=
  Function.Injective.commSemiring (of A 0) DFinsupp.single_injective (of A 0).map_zero
    (of_zero_one A) (of A 0).map_add (of_zero_mul A) (fun _ _ => map_nsmul _ _ _)
    (fun _ _ => of_zero_pow _ _ _) (of_natCast A)

end CommSemiring

section Ring

variable [forall i, AddCommGroup (A i)] [AddZeroClass ι] [GNonUnitalNonAssocSemiring A]

/-- The `NonUnitalNonAssocRing` derived from `GNonUnitalNonAssocSemiring A`. -/
scoped instance (priority := 900) : NonUnitalNonAssocRing (A 0) :=
  Function.Injective.nonUnitalNonAssocRing (of A 0) DFinsupp.single_injective (of A 0).map_zero
    (of A 0).map_add (of_zero_mul A) (of A 0).map_neg (of A 0).map_sub (fun _ _ => map_nsmul _ _ _)
    (fun _ _ => map_zsmul _ _ _)

end Ring

section Ring

variable [forall i, AddCommGroup (A i)] [AddMonoid ι] [GRing A]

/-- The `IntCast` instance on `A 0`, given `GRing A`. -/
scoped instance (priority := 900) : IntCast (A 0) :=
  ⟨GRing.intCast⟩

@[simp]
/--
theorem `of_intCast` / 定理 `of_intCast`

English:
theorem of_intCast
  given: (n : Int)
  statement: of A 0 n = n
  proof: by
  rfl

中文:
定理 of_intCast
  条件: (n : 整数)
  结论: of A 0 n = n
  证明: by
  rfl
-/
theorem of_intCast (n : Int) : of A 0 n = n := by
  rfl

/-- The `Ring` derived from `GSemiring A`. -/
scoped instance (priority := 900) : Ring (A 0) :=
  Function.Injective.ring (of A 0) DFinsupp.single_injective (of A 0).map_zero (of_zero_one A)
    (of A 0).map_add (of_zero_mul A) (of A 0).map_neg (of A 0).map_sub (fun _ _ => map_nsmul _ _ _)
    (fun _ _ => map_zsmul _ _ _) (fun _ _ => of_zero_pow _ _ _) (of_natCast A) (of_intCast A)

end Ring

section CommRing

variable [forall i, AddCommGroup (A i)] [AddCommMonoid ι] [GCommRing A]

/-- The `CommRing` derived from `GCommSemiring A`. -/
scoped instance (priority := 900) : CommRing (A 0) :=
  Function.Injective.commRing (of A 0) DFinsupp.single_injective (of A 0).map_zero (of_zero_one A)
    (of A 0).map_add (of_zero_mul A) (of A 0).map_neg (of A 0).map_sub (fun _ _ => map_nsmul _ _ _)
    (fun _ _ => map_zsmul _ _ _) (fun _ _ => of_zero_pow _ _ _) (of_natCast A) (of_intCast A)

end CommRing

end GradeZero

section ToSemiring

variable {R : Type*} [forall i, AddCommMonoid (A i)] [AddMonoid ι] [GSemiring A] [Semiring R]
variable {A}

/-- If two ring homomorphisms from `⨁ i, A i` are equal on each `of A i y`,
then they are equal.

See note [partially-applied ext lemmas]. -/
@[ext]
/--
theorem `ringHom_ext'` / 定理 `ringHom_ext'`

English:
theorem ringHom_ext'
  given: ⦃F G
  statement: (⨁ i, A i) ->+* R⦄
  proof: RingHom.coe_addMonoidHom_injective DirectSum.addHom_ext' h

中文:
定理 ringHom_ext'
  条件: ⦃F G
  结论: (⨁ i, A i) ->+* R⦄
  证明: RingHom.coe_addMonoidHom_injective DirectSum.addHom_ext' h

Depends on / 依赖: DirectSum, DirectSum.addHom_ext, RingHom, RingHom.coe_addMonoidHom_injective, addHom_ext, coe_addMonoidHom_injective
-/
theorem ringHom_ext' ⦃F G : (⨁ i, A i) ->+* R⦄
    (h : forall i, (↑F : _ ->+ R).comp (of A i) = (↑G : _ ->+ R).comp (of A i)) : F = G :=
RingHom.coe_addMonoidHom_injective DirectSum.addHom_ext' h

/--
theorem `ringHom_ext` / 定理 `ringHom_ext`

English:
theorem ringHom_ext
  given: ⦃f g
  statement: (⨁ i, A i) ->+* R⦄ (h : forall i x, f (of A i x) = g (of A i x)) : f = g
  proof: ringHom_ext' fun i => AddMonoidHom.ext h i

中文:
定理 ringHom_ext
  条件: ⦃f g
  结论: (⨁ i, A i) ->+* R⦄ (h : 对任意 i x, f (of A i x) = g (of A i x)) : f = g
  证明: ringHom_ext' fun i => AddMonoidHom.ext h i

Depends on / 依赖: AddMonoidHom, AddMonoidHom.ext, ringHom_ext
-/
theorem ringHom_ext ⦃f g : (⨁ i, A i) ->+* R⦄ (h : forall i x, f (of A i x) = g (of A i x)) : f = g :=
ringHom_ext' fun i => AddMonoidHom.ext h i

/-- A family of `AddMonoidHom`s preserving `DirectSum.One.one` and `DirectSum.Mul.mul`
describes a `RingHom`s on `⨁ i, A i`. This is a stronger version of `DirectSum.toMonoid`.

Of particular interest is the case when `A i` are bundled subobjects, `f` is the family of
coercions such as `AddSubmonoid.subtype (A i)`, and the `[GSemiring A]` structure originates from
`DirectSum.gsemiring.ofAddSubmonoids`, in which case the proofs about `GOne` and `GMul`
can be discharged by `rfl`. -/
@[simps]
/--
Definition of `toSemiring` / `toSemiring` 的定义

English:
definition toSemiring
  signature: (f : forall i, A i ->+ R) (hone : f _ GradedMonoid.GOne.one = 1)
  body: { toAddMonoid f with
    toFun := toAddMonoid f
    map_one' := by
      change (toAddMonoid f) (of _ 0 _) = 1
      rw [toAddMonoid_of]
      exact hone
    map_mul' := by
      rw [(toAddMonoid f).map_mul_iff]
      refine DirectSum.addHom_ext' (fun xi => AddMonoidHom.ext (fun xv => ?_))
      ref

中文:
定义 toSemiring
  签名: (f : 对任意 i, A i ->+ R) (hone : f _ 分次幺半群.GOne.one = 1)
  定义体: { toAddMonoid f with
    toFun := toAddMonoid f
    map_one' := by
      change (toAddMonoid f) (of _ 0 _) = 1
      rw [toAddMonoid_of]
      exact hone
    map_mul' := by
      rw [(toAddMonoid f).map_mul_iff]
      refine DirectSum.addHom_ext' (fun xi => AddMonoidHom.ext (fun xv => ?_))
      ref

Depends on / 依赖: AddMonoidHom, AddMonoidHom.ext, DirectSum, DirectSum.addHom_ext, addHom_ext, map_mul, map_mul_iff, map_one, of_mul_of, simp_rw, toAddMonoid, toAddMonoid_of
-/
def toSemiring (f : forall i, A i ->+ R) (hone : f _ GradedMonoid.GOne.one = 1)
    (hmul : forall {i j} (ai : A i) (aj : A j), f _ (GradedMonoid.GMul.mul ai aj) = f _ ai * f _ aj) :
    (⨁ i, A i) ->+* R :=
  { toAddMonoid f with
    toFun := toAddMonoid f
    map_one' := by
      change (toAddMonoid f) (of _ 0 _) = 1
      rw [toAddMonoid_of]
      exact hone
    map_mul' := by
      rw [(toAddMonoid f).map_mul_iff]
      refine DirectSum.addHom_ext' (fun xi => AddMonoidHom.ext (fun xv => ?_))
      refine DirectSum.addHom_ext' (fun yi => AddMonoidHom.ext (fun yv => ?_))
      change
        toAddMonoid f (of A xi xv * of A yi yv) =
          toAddMonoid f (of A xi xv) * toAddMonoid f (of A yi yv)
      simp_rw [of_mul_of, toAddMonoid_of]
      exact hmul _ _ }

/--
theorem `toSemiring_of` / 定理 `toSemiring_of`

English:
theorem toSemiring_of
  given: (f : forall i, A i ->+ R) (hone hmul) (i : ι) (x : A i)
  proof: toAddMonoid_of f i x

@[simp]

中文:
定理 toSemiring_of
  条件: (f : 对任意 i, A i ->+ R) (hone hmul) (i : ι) (x : A i)
  证明: toAddMonoid_of f i x

@[simp]

Depends on / 依赖: toAddMonoid_of
-/
theorem toSemiring_of (f : forall i, A i ->+ R) (hone hmul) (i : ι) (x : A i) :
    toSemiring f hone hmul (of _ i x) = f _ x :=
  toAddMonoid_of f i x

@[simp]
/--
theorem `toSemiring_coe_addMonoidHom` / 定理 `toSemiring_coe_addMonoidHom`

English:
theorem toSemiring_coe_addMonoidHom
  given: (f : forall i, A i ->+ R) (hone hmul)
  proof: rfl

中文:
定理 toSemiring_coe_addMonoidHom
  条件: (f : 对任意 i, A i ->+ R) (hone hmul)
  证明: rfl
-/
theorem toSemiring_coe_addMonoidHom (f : forall i, A i ->+ R) (hone hmul) :
    (toSemiring f hone hmul : (⨁ i, A i) ->+ R) = toAddMonoid f :=
  rfl

/-- Families of `AddMonoidHom`s preserving `DirectSum.One.one` and `DirectSum.Mul.mul`
are isomorphic to `RingHom`s on `⨁ i, A i`. This is a stronger version of `DFinsupp.liftAddHom`.
-/
@[simps]
/--
Definition of `liftRingHom` / `liftRingHom` 的定义

English:
definition liftRingHom
  signature: :
  body: toSemiring (fun _ => f.1) f.2.1 f.2.2
  invFun F :=
    ⟨by intro i; exact (F : (⨁ i, A i) ->+ R).comp (of _ i),
      by
      simp only [AddMonoidHom.comp_apply]
      rw [← F.map_one]
      rfl,
      by
      intro i j ai aj
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_coe]
      r

中文:
定义 liftRingHom
  签名: :
  定义体: toSemiring (fun _ => f.1) f.2.1 f.2.2
  invFun F :=
    ⟨by intro i; exact (F : (⨁ i, A i) ->+ R).comp (of _ i),
      by
      simp only [AddMonoidHom.comp_apply]
      rw [← F.map_one]
      rfl,
      by
      intro i j ai aj
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_coe]
      r

Depends on / 依赖: toSemiring
-/
def liftRingHom :
    { f : forall {i}, A i ->+ R //
        f GradedMonoid.GOne.one = 1 ∧
          forall {i j} (ai : A i) (aj : A j), f (GradedMonoid.GMul.mul ai aj) = f ai * f aj } ≃
      ((⨁ i, A i) ->+* R) where
  toFun f := toSemiring (fun _ => f.1) f.2.1 f.2.2
  invFun F :=
    ⟨by intro i; exact (F : (⨁ i, A i) ->+ R).comp (of _ i),
      by
      simp only [AddMonoidHom.comp_apply]
      rw [← F.map_one]
      rfl,
      by
      intro i j ai aj
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_coe]
      rw [← F.map_mul (of A i ai)]; rw [of_mul_of ai]⟩
  left_inv f := by
    ext xi xv
    exact toAddMonoid_of (fun _ => f.1) xi xv
  right_inv F := by
    apply RingHom.coe_addMonoidHom_injective
    refine DirectSum.addHom_ext' (fun xi => AddMonoidHom.ext (fun xv => ?_))
    simp only [DirectSum.toAddMonoid_of, AddMonoidHom.comp_apply, toSemiring_coe_addMonoidHom]

end ToSemiring

end DirectSum

/-! ### Concrete instances -/


section Uniform

variable (ι)

/--
Instance `NonUnitalNonAssocSemiring.directSumGNonUnitalNonAssocSemiring` / 实例 `NonUnitalNonAssocSemiring.directSumGNonUnitalNonAssocSemiring`

English:
instance NonUnitalNonAssocSemiring.directSumGNonUnitalNonAssocSemiring
  signature: {R : Type*} [AddMonoid ι]
  body: mul_zero
  zero_mul := zero_mul
  mul_add := mul_add
  add_mul := add_mul

中文:
实例 非幺非结合半环.directSumGNonUnitalNonAssocSemiring
  签名: {R : 类型} [加法幺半群 ι]
  定义体: mul_zero
  zero_mul := zero_mul
  mul_add := mul_add
  add_mul := add_mul

Depends on / 依赖: mul_zero
-/
instance NonUnitalNonAssocSemiring.directSumGNonUnitalNonAssocSemiring {R : Type*} [AddMonoid ι]
    [NonUnitalNonAssocSemiring R] : DirectSum.GNonUnitalNonAssocSemiring fun _ : ι => R where
  mul_zero := mul_zero
  zero_mul := zero_mul
  mul_add := mul_add
  add_mul := add_mul

/--
Instance `Semiring.directSumGSemiring` / 实例 `Semiring.directSumGSemiring`

English:
instance Semiring.directSumGSemiring
  signature: {R : Type*} [AddMonoid ι] [Semiring R]
  body: n
  natCast_zero := Nat.cast_zero
  natCast_succ := Nat.cast_succ

中文:
实例 半环.directSumGSemiring
  签名: {R : 类型} [加法幺半群 ι] [半环 R]
  定义体: n
  natCast_zero := Nat.cast_zero
  natCast_succ := Nat.cast_succ
-/
instance Semiring.directSumGSemiring {R : Type*} [AddMonoid ι] [Semiring R] :
    DirectSum.GSemiring fun _ : ι => R where
  natCast n := n
  natCast_zero := Nat.cast_zero
  natCast_succ := Nat.cast_succ

/--
Instance `Ring.directSumGRing` / 实例 `Ring.directSumGRing`

English:
instance Ring.directSumGRing
  signature: {R : Type*} [AddMonoid ι] [Ring R]
  body: z
  intCast_ofNat := Int.cast_natCast
  intCast_negSucc_ofNat := Int.cast_negSucc

中文:
实例 环.directSumGRing
  签名: {R : 类型} [加法幺半群 ι] [环 R]
  定义体: z
  intCast_ofNat := Int.cast_natCast
  intCast_negSucc_ofNat := Int.cast_negSucc
-/
instance Ring.directSumGRing {R : Type*} [AddMonoid ι] [Ring R] :
    DirectSum.GRing fun _ : ι => R where
  intCast z := z
  intCast_ofNat := Int.cast_natCast
  intCast_negSucc_ofNat := Int.cast_negSucc

open DirectSum

-- To check `Mul.gmul_mul` matches
example {R : Type*} [AddMonoid ι] [Semiring R] (i j : ι) (a b : R) :
    (DirectSum.of _ i a * DirectSum.of _ j b : ⨁ _, R) = DirectSum.of _ (i + j) (a * b) := by
  rw [DirectSum.of_mul_of]; rw [Mul.gMul_mul]

/--
Instance `CommSemiring.directSumGCommSemiring` / 实例 `CommSemiring.directSumGCommSemiring`

English:
instance CommSemiring.directSumGCommSemiring
  signature: {R : Type*} [AddCommMonoid ι] [CommSemiring R]

中文:
实例 交换半环.directSumGCommSemiring
  签名: {R : 类型} [加法交换幺半群 ι] [交换半环 R]
-/
instance CommSemiring.directSumGCommSemiring {R : Type*} [AddCommMonoid ι] [CommSemiring R] :
    DirectSum.GCommSemiring fun _ : ι => R where

/--
Instance `CommRing.directSumGCommRing` / 实例 `CommRing.directSumGCommRing`

English:
instance CommRing.directSumGCommRing
  signature: {R : Type*} [AddCommMonoid ι] [CommRing R]

中文:
实例 交换环.directSumGCommRing
  签名: {R : 类型} [加法交换幺半群 ι] [交换环 R]
-/
instance CommRing.directSumGCommRing {R : Type*} [AddCommMonoid ι] [CommRing R] :
    DirectSum.GCommRing fun _ : ι => R where

end Uniform
