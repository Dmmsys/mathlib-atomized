/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.NonUnitalStarAlgebra
public import Mathlib.Topology.Algebra.StarSubalgebra

/-! # Classes of C⋆-algebras

This file defines classes for complex C⋆-algebras. These are (unital or non-unital, commutative or
noncommutative) Banach algebra over `ℂ` with an antimultiplicative conjugate-linear involution
(`star`) satisfying the C⋆-identity `∥star x * x∥ = ∥x∥ ^ 2`.

## Notes

These classes are not defined in `Mathlib/Analysis/CStarAlgebra/Basic.lean` because they require
heavier imports.

-/

public section

noncomputable section

/--
Definition of `NonUnitalCStarAlgebra` / `NonUnitalCStarAlgebra` 的定义

English:
class NonUnitalCStarAlgebra
  parameters: (A : Type*)
  extends: NonUnitalNormedRing A, StarRing A, CompleteSpace A, 
  (no additional axioms)

中文:
类 NonUnitalCStarAlgebra
  参数: (A : 类型)
  继承: NonUnitalNormedRing A, StarRing A, CompleteSpace A, 
  (无附加公理)
-/
class NonUnitalCStarAlgebra (A : Type*) extends NonUnitalNormedRing A, StarRing A, CompleteSpace A,
    CStarRing A, NormedSpace Complex A, IsScalarTower Complex A A, SMulCommClass Complex A A, StarModule Complex A where

/--
Definition of `NonUnitalCommCStarAlgebra` / `NonUnitalCommCStarAlgebra` 的定义

English:
class NonUnitalCommCStarAlgebra
  parameters: (A : Type*)
  (no additional axioms)

中文:
类 NonUnitalCommCStarAlgebra
  参数: (A : 类型)
  (无附加公理)
-/
class NonUnitalCommCStarAlgebra (A : Type*) extends
    NonUnitalNormedCommRing A, NonUnitalCStarAlgebra A

/--
Definition of `CStarAlgebra` / `CStarAlgebra` 的定义

English:
class CStarAlgebra
  parameters: (A : Type*)
  extends: NormedRing A, StarRing A, CompleteSpace A, CStarRing A, 
  (no additional axioms)

中文:
类 CStarAlgebra
  参数: (A : 类型)
  继承: NormedRing A, StarRing A, CompleteSpace A, CStarRing A, 
  (无附加公理)
-/
class CStarAlgebra (A : Type*) extends NormedRing A, StarRing A, CompleteSpace A, CStarRing A,
    NormedAlgebra Complex A, StarModule Complex A where

/--
Definition of `CommCStarAlgebra` / `CommCStarAlgebra` 的定义

English:
class CommCStarAlgebra
  parameters: (A : Type*)
  extends: NormedCommRing A, CStarAlgebra A
  (no additional axioms)

中文:
类 CommCStarAlgebra
  参数: (A : 类型)
  继承: NormedCommRing A, CStarAlgebra A
  (无附加公理)
-/
class CommCStarAlgebra (A : Type*) extends NormedCommRing A, CStarAlgebra A

noncomputable instance (priority := 100) CStarAlgebra.toNonUnitalCStarAlgebra (A : Type*)
    [CStarAlgebra A] : NonUnitalCStarAlgebra A where

noncomputable instance (priority := 100) CommCStarAlgebra.toNonUnitalCommCStarAlgebra (A : Type*)
    [CommCStarAlgebra A] : NonUnitalCommCStarAlgebra A where

/--
Instance `StarSubalgebra.cstarAlgebra` / 实例 `StarSubalgebra.cstarAlgebra`

English:
instance StarSubalgebra.cstarAlgebra
  signature: {S A : Type*} [CStarAlgebra A]
  body: h_closed.completeSpace_coe
.symm.le norm_mul_self_le x := CStarRing.norm_star_mul_self (x := (x : A))

中文:
实例 StarSubalgebra.cstarAlgebra
  签名: {S A : 类型} [CStarAlgebra A]
  定义体: h_closed.completeSpace_coe
.symm.le norm_mul_self_le x := CStarRing.norm_star_mul_self (x := (x : A))

Depends on / 依赖: completeSpace_coe, h_closed, h_closed.completeSpace_coe
-/
noncomputable instance StarSubalgebra.cstarAlgebra {S A : Type*} [CStarAlgebra A]
    [SetLike S A] [SubringClass S A] [SMulMemClass S Complex A] [StarMemClass S A]
    (s : S) [h_closed : IsClosed (s : Set A)] : CStarAlgebra s where
  toCompleteSpace := h_closed.completeSpace_coe
.symm.le norm_mul_self_le x := CStarRing.norm_star_mul_self (x := (x : A))

/--
Instance `StarSubalgebra.commCStarAlgebra` / 实例 `StarSubalgebra.commCStarAlgebra`

English:
instance StarSubalgebra.commCStarAlgebra
  signature: {S A : Type*} [CommCStarAlgebra A]
  body: h_closed.completeSpace_coe
.symm.le norm_mul_self_le x := CStarRing.norm_star_mul_self (x := (x : A))
mul_comm _ _ := Subtype.ext mul_comm _ _

中文:
实例 StarSubalgebra.commCStarAlgebra
  签名: {S A : 类型} [CommCStarAlgebra A]
  定义体: h_closed.completeSpace_coe
.symm.le norm_mul_self_le x := CStarRing.norm_star_mul_self (x := (x : A))
mul_comm _ _ := Subtype.ext mul_comm _ _

Depends on / 依赖: completeSpace_coe, h_closed, h_closed.completeSpace_coe
-/
noncomputable instance StarSubalgebra.commCStarAlgebra {S A : Type*} [CommCStarAlgebra A]
    [SetLike S A] [SubringClass S A] [SMulMemClass S Complex A] [StarMemClass S A]
    (s : S) [h_closed : IsClosed (s : Set A)] : CommCStarAlgebra s where
  toCompleteSpace := h_closed.completeSpace_coe
.symm.le norm_mul_self_le x := CStarRing.norm_star_mul_self (x := (x : A))
mul_comm _ _ := Subtype.ext mul_comm _ _

/--
Instance `NonUnitalStarSubalgebra.nonUnitalCStarAlgebra` / 实例 `NonUnitalStarSubalgebra.nonUnitalCStarAlgebra`

English:
instance NonUnitalStarSubalgebra.nonUnitalCStarAlgebra
  signature: {S A : Type*}
  body: h_closed.completeSpace_coe
.symm.le norm_mul_self_le x := CStarRing.norm_star_mul_self (x := (x : A))

中文:
实例 NonUnitalStarSubalgebra.nonUnitalCStarAlgebra
  签名: {S A : 类型}
  定义体: h_closed.completeSpace_coe
.symm.le norm_mul_self_le x := CStarRing.norm_star_mul_self (x := (x : A))

Depends on / 依赖: completeSpace_coe, h_closed, h_closed.completeSpace_coe
-/
noncomputable instance NonUnitalStarSubalgebra.nonUnitalCStarAlgebra {S A : Type*}
    [NonUnitalCStarAlgebra A] [SetLike S A] [NonUnitalSubringClass S A] [SMulMemClass S Complex A]
    [StarMemClass S A] (s : S) [h_closed : IsClosed (s : Set A)] : NonUnitalCStarAlgebra s where
  toCompleteSpace := h_closed.completeSpace_coe
.symm.le norm_mul_self_le x := CStarRing.norm_star_mul_self (x := (x : A))

/--
Instance `NonUnitalStarSubalgebra.nonUnitalCommCStarAlgebra` / 实例 `NonUnitalStarSubalgebra.nonUnitalCommCStarAlgebra`

English:
instance NonUnitalStarSubalgebra.nonUnitalCommCStarAlgebra
  signature: {S A : Type*}
  body: h_closed.completeSpace_coe
.symm.le norm_mul_self_le x := CStarRing.norm_star_mul_self (x := (x : A))
mul_comm _ _ := Subtype.ext mul_comm _ _

中文:
实例 NonUnitalStarSubalgebra.nonUnitalCommCStarAlgebra
  签名: {S A : 类型}
  定义体: h_closed.completeSpace_coe
.symm.le norm_mul_self_le x := CStarRing.norm_star_mul_self (x := (x : A))
mul_comm _ _ := Subtype.ext mul_comm _ _

Depends on / 依赖: completeSpace_coe, h_closed, h_closed.completeSpace_coe
-/
noncomputable instance NonUnitalStarSubalgebra.nonUnitalCommCStarAlgebra {S A : Type*}
    [NonUnitalCommCStarAlgebra A] [SetLike S A] [NonUnitalSubringClass S A] [SMulMemClass S Complex A]
    [StarMemClass S A] (s : S) [h_closed : IsClosed (s : Set A)] : NonUnitalCommCStarAlgebra s where
  toCompleteSpace := h_closed.completeSpace_coe
.symm.le norm_mul_self_le x := CStarRing.norm_star_mul_self (x := (x : A))
mul_comm _ _ := Subtype.ext mul_comm _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommCStarAlgebra Complex

中文:
实例 :
  签名: CommCStarAlgebra Complex
-/
noncomputable instance : CommCStarAlgebra Complex where

section Elemental

variable {A : Type*}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CStarAlgebra
  signature: A] (x
  body: StarSubalgebra.cstarAlgebra _ (h_closed := StarAlgebra.elemental.isClosed Complex x)

中文:
实例 [CStarAlgebra
  签名: A] (x
  定义体: StarSubalgebra.cstarAlgebra _ (h_closed := StarAlgebra.elemental.isClosed Complex x)

Depends on / 依赖: StarAlgebra, StarAlgebra.elemental.isClosed, StarSubalgebra, StarSubalgebra.cstarAlgebra, cstarAlgebra, elemental, h_closed, isClosed
-/
noncomputable instance [CStarAlgebra A] (x : A) :
    CStarAlgebra (StarAlgebra.elemental Complex x) :=
  StarSubalgebra.cstarAlgebra _ (h_closed := StarAlgebra.elemental.isClosed Complex x)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalCStarAlgebra
  signature: A] (x
  body: NonUnitalStarSubalgebra.nonUnitalCStarAlgebra _
    (h_closed := NonUnitalStarAlgebra.elemental.isClosed Complex x)

中文:
实例 [NonUnitalCStarAlgebra
  签名: A] (x
  定义体: NonUnitalStarSubalgebra.nonUnitalCStarAlgebra _
    (h_closed := NonUnitalStarAlgebra.elemental.isClosed Complex x)

Depends on / 依赖: NonUnitalStarAlgebra, NonUnitalStarAlgebra.elemental.isClosed, NonUnitalStarSubalgebra, NonUnitalStarSubalgebra.nonUnitalCStarAlgebra, elemental, h_closed, isClosed, nonUnitalCStarAlgebra
-/
noncomputable instance [NonUnitalCStarAlgebra A] (x : A) :
    NonUnitalCStarAlgebra (NonUnitalStarAlgebra.elemental Complex x) :=
  NonUnitalStarSubalgebra.nonUnitalCStarAlgebra _
    (h_closed := NonUnitalStarAlgebra.elemental.isClosed Complex x)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CStarAlgebra
  signature: A] (x

中文:
实例 [CStarAlgebra
  签名: A] (x
-/
noncomputable instance [CStarAlgebra A] (x : A) [IsStarNormal x] :
    CommCStarAlgebra (StarAlgebra.elemental Complex x) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalCStarAlgebra
  signature: A] (x

中文:
实例 [NonUnitalCStarAlgebra
  签名: A] (x
-/
noncomputable instance [NonUnitalCStarAlgebra A] (x : A) [IsStarNormal x] :
    NonUnitalCommCStarAlgebra (NonUnitalStarAlgebra.elemental Complex x) where

end Elemental

section Pi

variable {ι : Type*} {A : ι -> Type*} [Fintype ι]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [(i
  signature: : ι) -> NonUnitalCStarAlgebra (A i)] :

中文:
实例 [(i
  签名: : ι) -> NonUnitalCStarAlgebra (A i)] :
-/
noncomputable instance [(i : ι) -> NonUnitalCStarAlgebra (A i)] :
    NonUnitalCStarAlgebra (Π i, A i) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [(i
  signature: : ι) -> NonUnitalCommCStarAlgebra (A i)] :

中文:
实例 [(i
  签名: : ι) -> NonUnitalCommCStarAlgebra (A i)] :
-/
noncomputable instance [(i : ι) -> NonUnitalCommCStarAlgebra (A i)] :
    NonUnitalCommCStarAlgebra (Π i, A i) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [(i
  signature: : ι) -> CStarAlgebra (A i)] : CStarAlgebra (Π i, A i) where

中文:
实例 [(i
  签名: : ι) -> CStarAlgebra (A i)] : CStarAlgebra (Π i, A i) where
-/
noncomputable instance [(i : ι) -> CStarAlgebra (A i)] : CStarAlgebra (Π i, A i) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [(i
  signature: : ι) -> CommCStarAlgebra (A i)] : CommCStarAlgebra (Π i, A i) where

中文:
实例 [(i
  签名: : ι) -> CommCStarAlgebra (A i)] : CommCStarAlgebra (Π i, A i) where
-/
noncomputable instance [(i : ι) -> CommCStarAlgebra (A i)] : CommCStarAlgebra (Π i, A i) where

end Pi

section Prod

variable {A B : Type*}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalCStarAlgebra
  signature: A] [NonUnitalCStarAlgebra B] :

中文:
实例 [NonUnitalCStarAlgebra
  签名: A] [NonUnitalCStarAlgebra B] :
-/
noncomputable instance [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] :
    NonUnitalCStarAlgebra (A × B) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalCommCStarAlgebra
  signature: A] [NonUnitalCommCStarAlgebra B] :

中文:
实例 [NonUnitalCommCStarAlgebra
  签名: A] [NonUnitalCommCStarAlgebra B] :
-/
noncomputable instance [NonUnitalCommCStarAlgebra A] [NonUnitalCommCStarAlgebra B] :
    NonUnitalCommCStarAlgebra (A × B) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CStarAlgebra
  signature: A] [CStarAlgebra B] : CStarAlgebra (A × B) where

中文:
实例 [CStarAlgebra
  签名: A] [CStarAlgebra B] : CStarAlgebra (A × B) where
-/
noncomputable instance [CStarAlgebra A] [CStarAlgebra B] : CStarAlgebra (A × B) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommCStarAlgebra
  signature: A] [CommCStarAlgebra B] : CommCStarAlgebra (A × B) where

中文:
实例 [CommCStarAlgebra
  签名: A] [CommCStarAlgebra B] : CommCStarAlgebra (A × B) where
-/
noncomputable instance [CommCStarAlgebra A] [CommCStarAlgebra B] : CommCStarAlgebra (A × B) where

end Prod

namespace MulOpposite

variable {A : Type*}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalCStarAlgebra
  signature: A] : NonUnitalCStarAlgebra Aᵐᵒᵖ where

中文:
实例 [NonUnitalCStarAlgebra
  签名: A] : NonUnitalCStarAlgebra Aᵐᵒᵖ where
-/
noncomputable instance [NonUnitalCStarAlgebra A] : NonUnitalCStarAlgebra Aᵐᵒᵖ where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalCommCStarAlgebra
  signature: A] : NonUnitalCommCStarAlgebra Aᵐᵒᵖ where

中文:
实例 [NonUnitalCommCStarAlgebra
  签名: A] : NonUnitalCommCStarAlgebra Aᵐᵒᵖ where
-/
noncomputable instance [NonUnitalCommCStarAlgebra A] : NonUnitalCommCStarAlgebra Aᵐᵒᵖ where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CStarAlgebra
  signature: A] : CStarAlgebra Aᵐᵒᵖ where

中文:
实例 [CStarAlgebra
  签名: A] : CStarAlgebra Aᵐᵒᵖ where
-/
noncomputable instance [CStarAlgebra A] : CStarAlgebra Aᵐᵒᵖ where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommCStarAlgebra
  signature: A] : CommCStarAlgebra Aᵐᵒᵖ where

中文:
实例 [CommCStarAlgebra
  签名: A] : CommCStarAlgebra Aᵐᵒᵖ where
-/
noncomputable instance [CommCStarAlgebra A] : CommCStarAlgebra Aᵐᵒᵖ where

end MulOpposite
