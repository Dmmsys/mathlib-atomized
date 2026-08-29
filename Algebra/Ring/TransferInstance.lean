/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.Algebra.Ring.InjSurj

/-!
# Transfer algebraic structures across `Equiv`s

This continues the pattern set in `Mathlib/Algebra/Group/TransferInstance.lean`.
-/

@[expose] public section

assert_not_exists Field Module

namespace Equiv
variable {α β : Type*} (e : α ≃ β)

/--
Definition of `ringEquiv` / `ringEquiv` 的定义

English:
definition ringEquiv
  signature: (e : α ≃ β) [Add β] [Mul β]
  body: Equiv.add e
    let mul := Equiv.mul e
    exact α ≃+* β := by
  intros
  exact
    { e with
      map_add' := fun x y => by
        simp [add_def]
      map_mul' := fun x y => by
        simp [mul_def] }

@[simp]

中文:
定义 ringEquiv
  签名: (e : α ≃ β) [Add β] [Mul β]
  定义体: Equiv.add e
    let mul := Equiv.mul e
    exact α ≃+* β := by
  intros
  exact
    { e with
      map_add' := fun x y => by
        simp [add_def]
      map_mul' := fun x y => by
        simp [mul_def] }

@[simp]

Depends on / 依赖: Equiv.add
-/
def ringEquiv (e : α ≃ β) [Add β] [Mul β] : by
    let add := Equiv.add e
    let mul := Equiv.mul e
    exact α ≃+* β := by
  intros
  exact
    { e with
      map_add' := fun x y => by
        simp [add_def]
      map_mul' := fun x y => by
        simp [mul_def] }

@[simp]
/--
lemma `ringEquiv_apply` / 引理 `ringEquiv_apply`

English:
lemma ringEquiv_apply
  given: (e : α ≃ β) [Add β] [Mul β] (a : α)
  statement: ringEquiv e a = e a
  proof: rfl

中文:
引理 ringEquiv_apply
  条件: (e : α ≃ β) [Add β] [Mul β] (a : α)
  结论: ringEquiv e a = e a
  证明: rfl
-/
lemma ringEquiv_apply (e : α ≃ β) [Add β] [Mul β] (a : α) : ringEquiv e a = e a := rfl

/--
lemma `ringEquiv_symm_apply` / 引理 `ringEquiv_symm_apply`

English:
lemma ringEquiv_symm_apply
  given: (e : α ≃ β) [Add β] [Mul β] (b : β)
  statement: by
  proof: Equiv.add e
    letI := Equiv.mul e
    exact (ringEquiv e).symm b = e.symm b := rfl

中文:
引理 ringEquiv_symm_apply
  条件: (e : α ≃ β) [Add β] [Mul β] (b : β)
  结论: by
  证明: Equiv.add e
    letI := Equiv.mul e
    exact (ringEquiv e).symm b = e.symm b := rfl

Depends on / 依赖: Equiv.add
-/
lemma ringEquiv_symm_apply (e : α ≃ β) [Add β] [Mul β] (b : β) : by
    letI := Equiv.add e
    letI := Equiv.mul e
    exact (ringEquiv e).symm b = e.symm b := rfl

/--
Definition of `nonUnitalNonAssocSemiring` / `nonUnitalNonAssocSemiring` 的定义

English:
abbreviation nonUnitalNonAssocSemiring
  signature: [NonUnitalNonAssocSemiring β]
  body: by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let nsmul := e.smul Nat
  apply e.injective.nonUnitalNonAssocSemiring _ <;> intros <;> exact e.apply_symm_apply _

中文:
缩写 nonUnitalNonAssocSemiring
  签名: [NonUnitalNonAssocSemiring β]
  定义体: by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let nsmul := e.smul Nat
  apply e.injective.nonUnitalNonAssocSemiring _ <;> intros <;> exact e.apply_symm_apply _

Depends on / 依赖: Finite, IsCompactOpenCovered, Set.iUnion_sigma, Set.iUnion_subtype, Set.image_iUnion, Set.image_image, hU.isCompactOpenCovered, iUnion_sigma, iUnion_subtype, image_iUnion, image_image, isCompactOpenCovered, isCompactOpenCovered_of_isCompact, of_finite
-/
protected abbrev nonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring β] :
    NonUnitalNonAssocSemiring α := by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let nsmul := e.smul Nat
  apply e.injective.nonUnitalNonAssocSemiring _ <;> intros <;> exact e.apply_symm_apply _

/--
Definition of `nonUnitalSemiring` / `nonUnitalSemiring` 的定义

English:
abbreviation nonUnitalSemiring
  signature: [NonUnitalSemiring β]
  body: by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let nsmul := e.smul Nat
  apply e.injective.nonUnitalSemiring _ <;> intros <;> exact e.apply_symm_apply _

中文:
缩写 nonUnitalSemiring
  签名: [NonUnitalSemiring β]
  定义体: by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let nsmul := e.smul Nat
  apply e.injective.nonUnitalSemiring _ <;> intros <;> exact e.apply_symm_apply _
-/
protected abbrev nonUnitalSemiring [NonUnitalSemiring β] : NonUnitalSemiring α := by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let nsmul := e.smul Nat
  apply e.injective.nonUnitalSemiring _ <;> intros <;> exact e.apply_symm_apply _

-- See note [instance transfer via equivalence]
/--
Definition of `addMonoidWithOne` / `addMonoidWithOne` 的定义

English:
abbreviation addMonoidWithOne
  signature: [AddMonoidWithOne β]
  body: { e.addMonoid, e.one with
    natCast := fun n => e.invFun n
    natCast_zero := e.injective (by simp [zero_def])
    natCast_succ := fun n => e.injective (by simp [add_def, one_def]) }

中文:
缩写 addMonoidWithOne
  签名: [AddMonoidWithOne β]
  定义体: { e.addMonoid, e.one with
    natCast := fun n => e.invFun n
    natCast_zero := e.injective (by simp [zero_def])
    natCast_succ := fun n => e.injective (by simp [add_def, one_def]) }
-/
protected abbrev addMonoidWithOne [AddMonoidWithOne β] : AddMonoidWithOne α :=
  { e.addMonoid, e.one with
    natCast := fun n => e.invFun n
    natCast_zero := e.injective (by simp [zero_def])
    natCast_succ := fun n => e.injective (by simp [add_def, one_def]) }

/--
Definition of `addGroupWithOne` / `addGroupWithOne` 的定义

English:
abbreviation addGroupWithOne
  signature: [AddGroupWithOne β]
  body: { e.addMonoidWithOne,
    e.addGroup with
    intCast := fun n => e.invFun n
    intCast_ofNat := fun n => by simp only [Int.cast_natCast]; rfl
    intCast_negSucc := fun _ =>
congr_arg e.invFun (Int.cast_negSucc _).trans congr_arg _ (e.apply_symm_apply _).symm }

中文:
缩写 addGroupWithOne
  签名: [AddGroupWithOne β]
  定义体: { e.addMonoidWithOne,
    e.addGroup with
    intCast := fun n => e.invFun n
    intCast_ofNat := fun n => by simp only [Int.cast_natCast]; rfl
    intCast_negSucc := fun _ =>
congr_arg e.invFun (Int.cast_negSucc _).trans congr_arg _ (e.apply_symm_apply _).symm }
-/
protected abbrev addGroupWithOne [AddGroupWithOne β] : AddGroupWithOne α :=
  { e.addMonoidWithOne,
    e.addGroup with
    intCast := fun n => e.invFun n
    intCast_ofNat := fun n => by simp only [Int.cast_natCast]; rfl
    intCast_negSucc := fun _ =>
congr_arg e.invFun (Int.cast_negSucc _).trans congr_arg _ (e.apply_symm_apply _).symm }

/--
Definition of `nonAssocSemiring` / `nonAssocSemiring` 的定义

English:
abbreviation nonAssocSemiring
  signature: [NonAssocSemiring β]
  body: by
  let mul := e.mul
  let add_monoid_with_one := e.addMonoidWithOne
  apply e.injective.nonAssocSemiring _ <;> intros <;> exact e.apply_symm_apply _

中文:
缩写 nonAssocSemiring
  签名: [NonAssocSemiring β]
  定义体: by
  let mul := e.mul
  let add_monoid_with_one := e.addMonoidWithOne
  apply e.injective.nonAssocSemiring _ <;> intros <;> exact e.apply_symm_apply _
-/
protected abbrev nonAssocSemiring [NonAssocSemiring β] : NonAssocSemiring α := by
  let mul := e.mul
  let add_monoid_with_one := e.addMonoidWithOne
  apply e.injective.nonAssocSemiring _ <;> intros <;> exact e.apply_symm_apply _

/--
Definition of `semiring` / `semiring` 的定义

English:
abbreviation semiring
  signature: [Semiring β]
  body: by
  let mul := e.mul
  let add_monoid_with_one := e.addMonoidWithOne
  let npow := e.pow Nat
  apply e.injective.semiring _ <;> intros <;> exact e.apply_symm_apply _

中文:
缩写 semiring
  签名: [Semiring β]
  定义体: by
  let mul := e.mul
  let add_monoid_with_one := e.addMonoidWithOne
  let npow := e.pow Nat
  apply e.injective.semiring _ <;> intros <;> exact e.apply_symm_apply _
-/
protected abbrev semiring [Semiring β] : Semiring α := by
  let mul := e.mul
  let add_monoid_with_one := e.addMonoidWithOne
  let npow := e.pow Nat
  apply e.injective.semiring _ <;> intros <;> exact e.apply_symm_apply _

/--
Definition of `nonUnitalCommSemiring` / `nonUnitalCommSemiring` 的定义

English:
abbreviation nonUnitalCommSemiring
  signature: [NonUnitalCommSemiring β]
  body: by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let nsmul := e.smul Nat
  apply e.injective.nonUnitalCommSemiring _ <;> intros <;> exact e.apply_symm_apply _

中文:
缩写 nonUnitalCommSemiring
  签名: [NonUnitalCommSemiring β]
  定义体: by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let nsmul := e.smul Nat
  apply e.injective.nonUnitalCommSemiring _ <;> intros <;> exact e.apply_symm_apply _

Depends on / 依赖: toPreZeroHypercover
-/
protected abbrev nonUnitalCommSemiring [NonUnitalCommSemiring β] : NonUnitalCommSemiring α := by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let nsmul := e.smul Nat
  apply e.injective.nonUnitalCommSemiring _ <;> intros <;> exact e.apply_symm_apply _

/--
Definition of `commSemiring` / `commSemiring` 的定义

English:
abbreviation commSemiring
  signature: [CommSemiring β]
  body: by
  let mul := e.mul
  let add_monoid_with_one := e.addMonoidWithOne
  let npow := e.pow Nat
  apply e.injective.commSemiring _ <;> intros <;> exact e.apply_symm_apply _

中文:
缩写 commSemiring
  签名: [CommSemiring β]
  定义体: by
  let mul := e.mul
  let add_monoid_with_one := e.addMonoidWithOne
  let npow := e.pow Nat
  apply e.injective.commSemiring _ <;> intros <;> exact e.apply_symm_apply _

Depends on / 依赖: PreZeroHypercover, PreZeroHypercover.sumInl, of_hom, sumInl
-/
protected abbrev commSemiring [CommSemiring β] : CommSemiring α := by
  let mul := e.mul
  let add_monoid_with_one := e.addMonoidWithOne
  let npow := e.pow Nat
  apply e.injective.commSemiring _ <;> intros <;> exact e.apply_symm_apply _

/--
Definition of `nonUnitalNonAssocRing` / `nonUnitalNonAssocRing` 的定义

English:
abbreviation nonUnitalNonAssocRing
  signature: [NonUnitalNonAssocRing β]
  body: by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let neg := e.Neg
  let sub := e.sub
  let nsmul := e.smul Nat
  let zsmul := e.smul Int
  apply e.injective.nonUnitalNonAssocRing _ <;> intros <;> exact e.apply_symm_apply _

中文:
缩写 nonUnitalNonAssocRing
  签名: [NonUnitalNonAssocRing β]
  定义体: by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let neg := e.Neg
  let sub := e.sub
  let nsmul := e.smul Nat
  let zsmul := e.smul Int
  apply e.injective.nonUnitalNonAssocRing _ <;> intros <;> exact e.apply_symm_apply _

Depends on / 依赖: PreZeroHypercover, PreZeroHypercover.sumInr, of_hom, sumInr
-/
protected abbrev nonUnitalNonAssocRing [NonUnitalNonAssocRing β] : NonUnitalNonAssocRing α := by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let neg := e.Neg
  let sub := e.sub
  let nsmul := e.smul Nat
  let zsmul := e.smul Int
  apply e.injective.nonUnitalNonAssocRing _ <;> intros <;> exact e.apply_symm_apply _

/--
Definition of `nonUnitalRing` / `nonUnitalRing` 的定义

English:
abbreviation nonUnitalRing
  signature: [NonUnitalRing β]
  body: by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let neg := e.Neg
  let sub := e.sub
  let nsmul := e.smul Nat
  let zsmul := e.smul Int
  apply e.injective.nonUnitalRing _ <;> intros <;> exact e.apply_symm_apply _

中文:
缩写 nonUnitalRing
  签名: [NonUnitalRing β]
  定义体: by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let neg := e.Neg
  let sub := e.sub
  let nsmul := e.smul Nat
  let zsmul := e.smul Int
  apply e.injective.nonUnitalRing _ <;> intros <;> exact e.apply_symm_apply _
-/
protected abbrev nonUnitalRing [NonUnitalRing β] : NonUnitalRing α := by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let neg := e.Neg
  let sub := e.sub
  let nsmul := e.smul Nat
  let zsmul := e.smul Int
  apply e.injective.nonUnitalRing _ <;> intros <;> exact e.apply_symm_apply _

/--
Definition of `nonAssocRing` / `nonAssocRing` 的定义

English:
abbreviation nonAssocRing
  signature: [NonAssocRing β]
  body: by
  let add_group_with_one := e.addGroupWithOne
  let mul := e.mul
  apply e.injective.nonAssocRing _ <;> intros <;> exact e.apply_symm_apply _

中文:
缩写 nonAssocRing
  签名: [NonAssocRing β]
  定义体: by
  let add_group_with_one := e.addGroupWithOne
  let mul := e.mul
  apply e.injective.nonAssocRing _ <;> intros <;> exact e.apply_symm_apply _
-/
protected abbrev nonAssocRing [NonAssocRing β] : NonAssocRing α := by
  let add_group_with_one := e.addGroupWithOne
  let mul := e.mul
  apply e.injective.nonAssocRing _ <;> intros <;> exact e.apply_symm_apply _

/--
Definition of `ring` / `ring` 的定义

English:
abbreviation ring
  signature: [Ring β]
  body: by
  let mul := e.mul
  let add_group_with_one := e.addGroupWithOne
  let npow := e.pow Nat
  apply e.injective.ring _ <;> intros <;> exact e.apply_symm_apply _

中文:
缩写 ring
  签名: [Ring β]
  定义体: by
  let mul := e.mul
  let add_group_with_one := e.addGroupWithOne
  let npow := e.pow Nat
  apply e.injective.ring _ <;> intros <;> exact e.apply_symm_apply _
-/
protected abbrev ring [Ring β] : Ring α := by
  let mul := e.mul
  let add_group_with_one := e.addGroupWithOne
  let npow := e.pow Nat
  apply e.injective.ring _ <;> intros <;> exact e.apply_symm_apply _

/--
Definition of `nonUnitalCommRing` / `nonUnitalCommRing` 的定义

English:
abbreviation nonUnitalCommRing
  signature: [NonUnitalCommRing β]
  body: by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let neg := e.Neg
  let sub := e.sub
  let nsmul := e.smul Nat
  let zsmul := e.smul Int
  apply e.injective.nonUnitalCommRing _ <;> intros <;> exact e.apply_symm_apply _

中文:
缩写 nonUnitalCommRing
  签名: [NonUnitalCommRing β]
  定义体: by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let neg := e.Neg
  let sub := e.sub
  let nsmul := e.smul Nat
  let zsmul := e.smul Int
  apply e.injective.nonUnitalCommRing _ <;> intros <;> exact e.apply_symm_apply _

Depends on / 依赖: H.choose, H.choose_spec.choose_spec.choose, H.choose_spec.choose_spec.choose_spec.left, H.choose_spec.choose_spec.choose_spec.right, choose_spec, exists_isAffineOpen_of_isCompact, hU.isCompact, isCompact, of_finite
-/
protected abbrev nonUnitalCommRing [NonUnitalCommRing β] : NonUnitalCommRing α := by
  let zero := e.zero
  let add := e.add
  let mul := e.mul
  let neg := e.Neg
  let sub := e.sub
  let nsmul := e.smul Nat
  let zsmul := e.smul Int
  apply e.injective.nonUnitalCommRing _ <;> intros <;> exact e.apply_symm_apply _

/--
Definition of `commRing` / `commRing` 的定义

English:
abbreviation commRing
  signature: [CommRing β]
  body: by
  let mul := e.mul
  let add_group_with_one := e.addGroupWithOne
  let npow := e.pow Nat
  apply e.injective.commRing _ <;> intros <;> exact e.apply_symm_apply _

中文:
缩写 commRing
  签名: [CommRing β]
  定义体: by
  let mul := e.mul
  let add_group_with_one := e.addGroupWithOne
  let npow := e.pow Nat
  apply e.injective.commRing _ <;> intros <;> exact e.apply_symm_apply _
-/
protected abbrev commRing [CommRing β] : CommRing α := by
  let mul := e.mul
  let add_group_with_one := e.addGroupWithOne
  let npow := e.pow Nat
  apply e.injective.commRing _ <;> intros <;> exact e.apply_symm_apply _

/--
lemma `isDomain` / 引理 `isDomain`

English:
lemma isDomain
  given: [Semiring β] [IsDomain β] (e : α ≃ β)
  proof: e.semiring
    IsDomain α :=
  letI := e.semiring; e.injective.isDomain e.ringEquiv

中文:
引理 isDomain
  条件: [Semiring β] [IsDomain β] (e : α ≃ β)
  证明: e.semiring
    IsDomain α :=
  letI := e.semiring; e.injective.isDomain e.ringEquiv
-/
protected lemma isDomain [Semiring β] [IsDomain β] (e : α ≃ β) :
    letI := e.semiring
    IsDomain α :=
  letI := e.semiring; e.injective.isDomain e.ringEquiv

end Equiv
