/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.LinearAlgebra.Matrix.Ideal
public import Mathlib.RingTheory.SimpleRing.Basic

/-!
The matrix ring over a simple ring is simple
-/

public section

namespace IsSimpleRing

variable (ι A : Type*) [Ring A] [Fintype ι] [Nonempty ι]

/--
Instance `matrix` / 实例 `matrix`

English:
instance matrix
  signature: [IsSimpleRing A]
  body: letI := Classical.decEq ι; TwoSidedIdeal.orderIsoMatrix

中文:
实例 matrix
  签名: [IsSimpleRing A]
  定义体: letI := Classical.decEq ι; TwoSidedIdeal.orderIsoMatrix

Depends on / 依赖: Classical, Classical.decEq, TwoSidedIdeal, TwoSidedIdeal.orderIsoMatrix, orderIsoMatrix
-/
instance matrix [IsSimpleRing A] : IsSimpleRing (Matrix ι ι A) where
.symm.isSimpleOrder simple := letI := Classical.decEq ι; TwoSidedIdeal.orderIsoMatrix

end IsSimpleRing
