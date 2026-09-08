/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Ring.Opposite

/-!
# Actions by matrices on vectors through `*ᵥ` and `ᵥ*`, cast as `Module`s

This file provides the left- and right- module structures of square matrices on vectors, via
`Matrix.mulVec` and `Matrix.vecMul`.
-/

public section

variable {n R S : Type*}

namespace Matrix

variable [Fintype n] [DecidableEq n] [Semiring R]

/-! ## `*ᵥ` as a left-module -/

section mulVec

/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module (Matrix n n R) (n → R) where
  smul := mulVec
  one_smul := one_mulVec
  mul_smul _ _ _ := (mulVec_mulVec _ _ _).symm
  zero_smul := zero_mulVec
  add_smul := add_mulVec
  smul_zero := mulVec_zero
  smul_add := mulVec_add
/-
**Matrix.smul_eq_mulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n : Type u_1} {R : Type u_2} [inst : Fintype n] [inst_1 : DecidableEq n
] [inst_2 : Semiring R] (A : Matrix n n R)   (v : n → R), A • v = A.mulVec v
参数：A : Matrix n n R；v : n → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma smul_eq_mulVec (A : Matrix n n R) (v : n → R) : A • v = A *ᵥ v := rfl
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DistribSMul S R] [SMulCommClass R S R] : SMulCommClass (Matrix n n R) S (n → R) where
  smul_comm := letI := SMulCommClass.symm; mulVec_smul
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DistribSMul S R] [SMulCommClass S R R] : SMulCommClass S (Matrix n n R) (n → R) where
  smul_comm s A v := (mulVec_smul A s v).symm
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DistribSMul S R] [IsScalarTower S R R] : IsScalarTower S (Matrix n n R) (n → R) where
  smul_assoc := smul_mulVec
/-
**Matrix.ext_iff_smul** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：ext_iff_smul {A B : Matrix n n R} : A = B ↔ forall v : n -> R, A • v = B •
 v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext_iff_mulVec`：ext_iff_mulVec [Fintype n] {A B : Matrix m n α} :
 A = B ↔ forall v, A *ᵥ v = B *ᵥ v
-/
lemma ext_iff_smul {A B : Matrix n n R} :
    A = B ↔ ∀ v : n → R, A • v = B • v := Matrix.ext_iff_mulVec

end mulVec

/-! ## `*ᵥ` as a right-module -/

section vecMul

/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module (Matrix n n R)ᵐᵒᵖ (n → R) where
  smul A v := v ᵥ* A.unop
  one_smul := Matrix.vecMul_one
  mul_smul _ _ _ := (vecMul_vecMul _ _ _).symm
  zero_smul := vecMul_zero
  add_smul _ _ := vecMul_add _ _
  smul_zero _ := zero_vecMul _
  smul_add _ := add_vecMul _
/-
**Matrix.op_smul_eq_vecMul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n : Type u_1} {R : Type u_2} [inst : Fintype n] [inst_1 : DecidableEq n
] [inst_2 : Semiring R]   (A : (Matrix n n R)ᵐᵒᵖ) (v : n → R), A • v = Matrix.ve
cMul v (MulOpposite.unop A)
参数：A : (Matrix n n R)ᵐᵒᵖ；v : n → R；MulOpposite.unop A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma op_smul_eq_vecMul (A : (Matrix n n R)ᵐᵒᵖ) (v : n → R) : A • v = v ᵥ* A.unop := rfl
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DistribSMul S R] [IsScalarTower S R R] : SMulCommClass (Matrix n n R)ᵐᵒᵖ S (n → R) where
  smul_comm A s v := smul_vecMul s v A.unop
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DistribSMul S R] [IsScalarTower S R R] : SMulCommClass S (Matrix n n R)ᵐᵒᵖ (n → R) where
  smul_comm s A v := (smul_vecMul s v A.unop).symm
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DistribSMul S R] [SMulCommClass S R R] : IsScalarTower S (Matrix n n R)ᵐᵒᵖ (n → R) where
  smul_assoc s A v := vecMul_smul v s A.unop

end vecMul

end Matrix

