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

/-
**Matrix.subalgebraCenter_eq_scalarAlgHom_map** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`
。
形式化陈述：subalgebraCenter_eq_scalarAlgHom_map : Subalgebra.center R (Matrix n n A) 
= (Subalgebra.center R A).map (scalarAlgHom n R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Matrix.center_eq_scalar_image`：center_eq_scalar_image : Set.center (Matr
ix n n α) = scalar n '' Set.center α
-/
theorem subalgebraCenter_eq_scalarAlgHom_map :
    Subalgebra.center R (Matrix n n A) = (Subalgebra.center R A).map (scalarAlgHom n R) :=
  SetLike.coe_injective center_eq_scalar_image

end Matrix

namespace Algebra.IsCentral
variable (K D : Type*) [CommSemiring K] [Semiring D] [Algebra K D] [IsCentral K D]

open Matrix in
/-
**Algebra.IsCentral.matrix** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.IsCentral`。
形式化陈述：matrix (ι : Type*) [Fintype ι] [DecidableEq ι] : Algebra.IsCentral K (Matr
ix ι ι D) where out
参数：ι : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Matrix.subalgebraCenter_eq_scalarAlgHom_map`：subalgebraCenter_eq_scalarA
lgHom_map : Subalgebra.center R (Matrix n n A) = (Subalgebra.center R A).map (sc
alarAlgHom n R)
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Subalgebra.map_mono`：map_mono {S₁ S₂ : Subalgebra R A} {f : A ->ₐ[R] B} 
: S₁ <= S₂ -> S₁.map f <= S₂.map f
· 使用定理 `Algebra.IsCentral.out`：∀ {K : Type u} {inst : CommSemiring K} {D : Type 
v} {inst_1 : Semiring D} {inst_2 : Algebra K D}   [self : Algebra.IsCentral K D]
, Subalgebr…
· 使用定理 `Algebra.map_bot`：map_bot (f : A ->ₐ[R] B) : (⊥ : Subalgebra R A).map f =
 ⊥
-/
instance matrix (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Algebra.IsCentral K (Matrix ι ι D) where
  out := subalgebraCenter_eq_scalarAlgHom_map.trans_le <|
    Subalgebra.map_mono out |>.trans_eq <| map_bot _

end Algebra.IsCentral

