/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Data.Rat.Cast.CharZero

/-!
# Further basic results about `Algebra`'s over `ℚ`.

This file could usefully be split further.
-/

public section

assert_not_exists Subgroup

variable {F R S : Type*}

namespace RingHom

@[simp]
/--
theorem `map_rat_algebraMap` / 定理 `map_rat_algebraMap`

English:
theorem map_rat_algebraMap
  statement: [Semiring R] [Semiring S] [Algebra Rat R] [Algebra Rat S] (f : R ->+* S)
  proof: RingHom.ext_iff.1 (Subsingleton.elim (f.comp (algebraMap Rat R)) (algebraMap Rat S)) r

中文:
定理 map_rat_algebraMap
  结论: [半环 R] [半环 S] [代数 有理数 R] [代数 有理数 S] (f : R ->+* S)
  证明: RingHom.ext_iff.1 (Subsingleton.elim (f.comp (algebraMap Rat R)) (algebraMap Rat S)) r

Depends on / 依赖: IsCancelMul, IsMulTorsionFree, Monoid, Monoid.FG, RingHom, RingHom.ext_iff, Subsingleton, Subsingleton.elim, algebraMap, ext_iff, f.comp
-/
theorem map_rat_algebraMap [Semiring R] [Semiring S] [Algebra Rat R] [Algebra Rat S] (f : R ->+* S)
    (r : Rat) : f (algebraMap Rat R r) = algebraMap Rat S r :=
  RingHom.ext_iff.1 (Subsingleton.elim (f.comp (algebraMap Rat R)) (algebraMap Rat S)) r

end RingHom

namespace NNRat
variable [DivisionSemiring R] [CharZero R] [DivisionSemiring S] [CharZero S]

/--
Instance `_root_.DivisionSemiring.toNNRatAlgebra` / 实例 `_root_.DivisionSemiring.toNNRatAlgebra`

English:
instance _root_.DivisionSemiring.toNNRatAlgebra
  signature: : Algebra Rat>=0 R where
  body: smul_def
  algebraMap := castHom _
  commutes' := cast_commute

中文:
实例 _root_.除半环.toNNRatAlgebra
  签名: : 代数 有理数>=0 R where
  定义体: smul_def
  algebraMap := castHom _
  commutes' := cast_commute

Depends on / 依赖: smul_def
-/
instance _root_.DivisionSemiring.toNNRatAlgebra : Algebra Rat>=0 R where
  smul_def' := smul_def
  algebraMap := castHom _
  commutes' := cast_commute

/--
Instance `_root_.RingHomClass.toLinearMapClassNNRat` / 实例 `_root_.RingHomClass.toLinearMapClassNNRat`

English:
instance _root_.RingHomClass.toLinearMapClassNNRat
  signature: [FunLike F R S] [RingHomClass F R S]
  body: by simp [smul_def, cast_id]

中文:
实例 _root_.环态射类.toLinearMapClassNNRat
  签名: [函数状 F R S] [环态射类 F R S]
  定义体: by simp [smul_def, cast_id]

Depends on / 依赖: cast_id, smul_def
-/
instance _root_.RingHomClass.toLinearMapClassNNRat [FunLike F R S] [RingHomClass F R S] :
    LinearMapClass F Rat>=0 R S where
  map_smulₛₗ f q a := by simp [smul_def, cast_id]

variable [SMul R S]

/--
Instance `instSMulCommClass` / 实例 `instSMulCommClass`

English:
instance instSMulCommClass
  signature: [SMulCommClass R S S]
  body: by simp [smul_def, mul_smul_comm]

中文:
实例 instSMulCommClass
  签名: [标量交换类 R S S]
  定义体: by simp [smul_def, mul_smul_comm]

Depends on / 依赖: mul_smul_comm, smul_def
-/
instance instSMulCommClass [SMulCommClass R S S] : SMulCommClass Rat>=0 R S where
  smul_comm q a b := by simp [smul_def, mul_smul_comm]

/--
Instance `instSMulCommClass'` / 实例 `instSMulCommClass'`

English:
instance instSMulCommClass'
  signature: [SMulCommClass S R S]
  body: have := SMulCommClass.symm S R S; SMulCommClass.symm _ _ _

中文:
实例 instSMulCommClass'
  签名: [标量交换类 S R S]
  定义体: have := SMulCommClass.symm S R S; SMulCommClass.symm _ _ _

Depends on / 依赖: SMulCommClass, SMulCommClass.symm
-/
instance instSMulCommClass' [SMulCommClass S R S] : SMulCommClass R Rat>=0 S :=
  have := SMulCommClass.symm S R S; SMulCommClass.symm _ _ _

end NNRat

namespace Rat
variable [DivisionRing R] [CharZero R] [DivisionRing S] [CharZero S]

/--
Instance `_root_.DivisionRing.toRatAlgebra` / 实例 `_root_.DivisionRing.toRatAlgebra`

English:
instance _root_.DivisionRing.toRatAlgebra
  signature: : Algebra Rat R where
  body: smul_def
  algebraMap := castHom _
  commutes' := cast_commute

中文:
实例 _root_.除环.toRatAlgebra
  签名: : 代数 有理数 R where
  定义体: smul_def
  algebraMap := castHom _
  commutes' := cast_commute

Depends on / 依赖: smul_def
-/
instance _root_.DivisionRing.toRatAlgebra : Algebra Rat R where
  smul_def' := smul_def
  algebraMap := castHom _
  commutes' := cast_commute

/--
Instance `_root_.RingHomClass.toLinearMapClassRat` / 实例 `_root_.RingHomClass.toLinearMapClassRat`

English:
instance _root_.RingHomClass.toLinearMapClassRat
  signature: [FunLike F R S] [RingHomClass F R S]
  body: by simp [smul_def, cast_id]

中文:
实例 _root_.环态射类.toLinearMapClassRat
  签名: [函数状 F R S] [环态射类 F R S]
  定义体: by simp [smul_def, cast_id]

Depends on / 依赖: cast_id, smul_def
-/
instance _root_.RingHomClass.toLinearMapClassRat [FunLike F R S] [RingHomClass F R S] :
    LinearMapClass F Rat R S where
  map_smulₛₗ f q a := by simp [smul_def, cast_id]

/--
Instance `_root_.RingEquivClass.toLinearEquivClassRat` / 实例 `_root_.RingEquivClass.toLinearEquivClassRat`

English:
instance _root_.RingEquivClass.toLinearEquivClassRat
  signature: [EquivLike F R S] [RingEquivClass F R S]
  body: by simp [Algebra.smul_def]

中文:
实例 _root_.环等价类.toLinearEquivClassRat
  签名: [等价状 F R S] [环等价类 F R S]
  定义体: by simp [Algebra.smul_def]

Depends on / 依赖: Algebra, Algebra.smul_def, smul_def
-/
instance _root_.RingEquivClass.toLinearEquivClassRat [EquivLike F R S] [RingEquivClass F R S] :
    LinearEquivClass F Rat R S where
  map_smulₛₗ f c x := by simp [Algebra.smul_def]

variable [SMul R S]

/--
Instance `instSMulCommClass` / 实例 `instSMulCommClass`

English:
instance instSMulCommClass
  signature: [SMulCommClass R S S]
  body: by simp [smul_def, mul_smul_comm]

中文:
实例 instSMulCommClass
  签名: [标量交换类 R S S]
  定义体: by simp [smul_def, mul_smul_comm]

Depends on / 依赖: mul_smul_comm, smul_def
-/
instance instSMulCommClass [SMulCommClass R S S] : SMulCommClass Rat R S where
  smul_comm q a b := by simp [smul_def, mul_smul_comm]

/--
Instance `instSMulCommClass'` / 实例 `instSMulCommClass'`

English:
instance instSMulCommClass'
  signature: [SMulCommClass S R S]
  body: have := SMulCommClass.symm S R S; SMulCommClass.symm _ _ _

中文:
实例 instSMulCommClass'
  签名: [标量交换类 S R S]
  定义体: have := SMulCommClass.symm S R S; SMulCommClass.symm _ _ _

Depends on / 依赖: AddCancelCommMonoid, AddMonoid, AddMonoid.FG, AffineAddMonoid, AffineAddMonoid.to_twoUniqueSums, SMulCommClass, SMulCommClass.symm, to_twoUniqueSums
-/
instance instSMulCommClass' [SMulCommClass S R S] : SMulCommClass R Rat S :=
  have := SMulCommClass.symm S R S; SMulCommClass.symm _ _ _

/--
Instance `algebra_rat_subsingleton` / 实例 `algebra_rat_subsingleton`

English:
instance algebra_rat_subsingleton
  signature: {R} [Semiring R]
  body: ⟨fun x y => Algebra.algebra_ext x y RingHom.congr_fun Subsingleton.elim _ _⟩

中文:
实例 algebra_rat_subsingleton
  签名: {R} [半环 R]
  定义体: ⟨fun x y => Algebra.algebra_ext x y RingHom.congr_fun Subsingleton.elim _ _⟩

Depends on / 依赖: AffineMonoid, AffineMonoid.to_twoUniqueProds, Algebra, Algebra.algebra_ext, CancelCommMonoid, Monoid, Monoid.FG, RingHom, RingHom.congr_fun, Subsingleton, Subsingleton.elim, algebra_ext, congr_fun, to_twoUniqueProds
-/
instance algebra_rat_subsingleton {R} [Semiring R] : Subsingleton (Algebra Rat R) :=
⟨fun x y => Algebra.algebra_ext x y RingHom.congr_fun Subsingleton.elim _ _⟩

end Rat
