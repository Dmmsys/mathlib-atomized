/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Yunzhou Xie
-/
module

public import Mathlib.Algebra.Central.Defs
public import Mathlib.Data.Matrix.Basis

/-!
# The matrix algebra is a central algebra
-/

public section

namespace Matrix
variable {n R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Fintype n] [DecidableEq n]

/--
theorem `subalgebraCenter_eq_scalarAlgHom_map` / 定理 `subalgebraCenter_eq_scalarAlgHom_map`

English:
theorem subalgebraCenter_eq_scalarAlgHom_map
  proof: SetLike.coe_injective center_eq_scalar_image

中文:
定理 subalgebraCenter_eq_scalarAlgHom_map
  证明: SetLike.coe_injective center_eq_scalar_image

Depends on / 依赖: SetLike, SetLike.coe_injective, center_eq_scalar_image, coe_injective
-/
theorem subalgebraCenter_eq_scalarAlgHom_map :
    Subalgebra.center R (Matrix n n A) = (Subalgebra.center R A).map (scalarAlgHom n R) :=
  SetLike.coe_injective center_eq_scalar_image

end Matrix

namespace Algebra.IsCentral
variable (K D : Type*) [CommSemiring K] [Semiring D] [Algebra K D] [IsCentral K D]

open Matrix in
/--
Instance `matrix` / 实例 `matrix`

English:
instance matrix
  signature: (ι : Type*) [Fintype ι] [DecidableEq ι]
  body: subalgebraCenter_eq_scalarAlgHom_map.trans_le
.trans_eq map_bot _ Subalgebra.map_mono out

中文:
实例 matrix
  签名: (ι : 类型) [Fintype ι] [DecidableEq ι]
  定义体: subalgebraCenter_eq_scalarAlgHom_map.trans_le
.trans_eq map_bot _ Subalgebra.map_mono out

Depends on / 依赖: subalgebraCenter_eq_scalarAlgHom_map, subalgebraCenter_eq_scalarAlgHom_map.trans_le, trans_le
-/
instance matrix (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Algebra.IsCentral K (Matrix ι ι D) where
out := subalgebraCenter_eq_scalarAlgHom_map.trans_le
.trans_eq map_bot _ Subalgebra.map_mono out

end Algebra.IsCentral
