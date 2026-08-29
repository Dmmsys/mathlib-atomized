/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Lp.lpSpace

/-! # `lp ∞ A` as a C⋆-algebra

We place these here because, for reasons related to the import hierarchy, they should not be placed
in earlier files.
-/

public section
open scoped ENNReal

noncomputable section

variable {I : Type*} {A : I -> Type*}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, NonUnitalCStarAlgebra (A i)] : NonUnitalCStarAlgebra (lp A ∞) where

中文:
实例 [对任意
  签名: i, 非幺CStar代数 (A i)] : 非幺CStar代数 (lp A ∞) where
-/
instance [forall i, NonUnitalCStarAlgebra (A i)] : NonUnitalCStarAlgebra (lp A ∞) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, NonUnitalCommCStarAlgebra (A i)] : NonUnitalCommCStarAlgebra (lp A ∞) where

中文:
实例 [对任意
  签名: i, 非幺交换CStar代数 (A i)] : 非幺交换CStar代数 (lp A ∞) where

Depends on / 依赖: NormedDivisionRing, NormedDivisionRing.toNormedRing, toNormedRing
-/
instance [forall i, NonUnitalCommCStarAlgebra (A i)] : NonUnitalCommCStarAlgebra (lp A ∞) where

-- it's slightly weird that we need the `Nontrivial` instance here
-- it's because we have no way to say that `‖(1 : A i)‖` is uniformly bounded as a type class
-- aside from `∀ i, NormOneClass (A i)`, this holds automatically for C⋆-algebras though.
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, Nontrivial (A i)] [forall i, CStarAlgebra (A i)] : NormedRing (lp A ∞) where
  body: dist_eq_norm_neg_add
  norm_mul_le := norm_mul_le

中文:
实例 [对任意
  签名: i, 非平凡 (A i)] [对任意 i, CStar代数 (A i)] : 赋范环 (lp A ∞) where
  定义体: dist_eq_norm_neg_add
  norm_mul_le := norm_mul_le

Depends on / 依赖: NormedDivisionRing, NormedDivisionRing.toNormMulClass, dist_eq_norm_neg_add, toNormMulClass
-/
instance [forall i, Nontrivial (A i)] [forall i, CStarAlgebra (A i)] : NormedRing (lp A ∞) where
  dist_eq := dist_eq_norm_neg_add
  norm_mul_le := norm_mul_le

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, Nontrivial (A i)] [forall i, CommCStarAlgebra (A i)] : CommCStarAlgebra (lp A ∞) where

中文:
实例 [对任意
  签名: i, 非平凡 (A i)] [对任意 i, 交换CStar代数 (A i)] : 交换CStar代数 (lp A ∞) where

Depends on / 依赖: NormOneClass, NormedDivisionRing, NormedDivisionRing.to_normOneClass, to_normOneClass
-/
instance [forall i, Nontrivial (A i)] [forall i, CommCStarAlgebra (A i)] : CommCStarAlgebra (lp A ∞) where

end
