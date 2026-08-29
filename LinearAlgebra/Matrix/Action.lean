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

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module (Matrix n n R) (n -> R)
  body: mulVec
  one_smul := one_mulVec
  mul_smul _ _ _ := (mulVec_mulVec _ _ _).symm
  zero_smul := zero_mulVec
  add_smul := add_mulVec
  smul_zero := mulVec_zero
  smul_add := mulVec_add

中文:
实例 :
  签名: Module (Matrix n n R) (n -> R)
  定义体: mulVec
  one_smul := one_mulVec
  mul_smul _ _ _ := (mulVec_mulVec _ _ _).symm
  zero_smul := zero_mulVec
  add_smul := add_mulVec
  smul_zero := mulVec_zero
  smul_add := mulVec_add

Depends on / 依赖: mulVec
-/
instance : Module (Matrix n n R) (n -> R) where
  smul := mulVec
  one_smul := one_mulVec
  mul_smul _ _ _ := (mulVec_mulVec _ _ _).symm
  zero_smul := zero_mulVec
  add_smul := add_mulVec
  smul_zero := mulVec_zero
  smul_add := mulVec_add

/--
lemma `smul_eq_mulVec` / 引理 `smul_eq_mulVec`

English:
lemma smul_eq_mulVec
  given: (A : Matrix n n R) (v : n -> R)
  statement: A • v = A *ᵥ v
  proof: rfl

中文:
引理 smul_eq_mulVec
  条件: (A : Matrix n n R) (v : n -> R)
  结论: A • v = A *ᵥ v
  证明: rfl
-/
@[simp] lemma smul_eq_mulVec (A : Matrix n n R) (v : n -> R) : A • v = A *ᵥ v := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DistribSMul
  signature: S R] [SMulCommClass R S R] : SMulCommClass (Matrix n n R) S (n -> R) where
  body: letI := SMulCommClass.symm; mulVec_smul

中文:
实例 [DistribSMul
  签名: S R] [SMulCommClass R S R] : SMulCommClass (Matrix n n R) S (n -> R) where
  定义体: letI := SMulCommClass.symm; mulVec_smul

Depends on / 依赖: SMulCommClass, SMulCommClass.symm, mulVec_smul
-/
instance [DistribSMul S R] [SMulCommClass R S R] : SMulCommClass (Matrix n n R) S (n -> R) where
  smul_comm := letI := SMulCommClass.symm; mulVec_smul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DistribSMul
  signature: S R] [SMulCommClass S R R] : SMulCommClass S (Matrix n n R) (n -> R) where
  body: (mulVec_smul A s v).symm

中文:
实例 [DistribSMul
  签名: S R] [SMulCommClass S R R] : SMulCommClass S (Matrix n n R) (n -> R) where
  定义体: (mulVec_smul A s v).symm

Depends on / 依赖: mulVec_smul
-/
instance [DistribSMul S R] [SMulCommClass S R R] : SMulCommClass S (Matrix n n R) (n -> R) where
  smul_comm s A v := (mulVec_smul A s v).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DistribSMul
  signature: S R] [IsScalarTower S R R] : IsScalarTower S (Matrix n n R) (n -> R) where
  body: smul_mulVec

中文:
实例 [DistribSMul
  签名: S R] [IsScalarTower S R R] : IsScalarTower S (Matrix n n R) (n -> R) where
  定义体: smul_mulVec

Depends on / 依赖: smul_mulVec
-/
instance [DistribSMul S R] [IsScalarTower S R R] : IsScalarTower S (Matrix n n R) (n -> R) where
  smul_assoc := smul_mulVec

/--
lemma `ext_iff_smul` / 引理 `ext_iff_smul`

English:
lemma ext_iff_smul
  given: {A B : Matrix n n R}
  proof: Matrix.ext_iff_mulVec

中文:
引理 ext_iff_smul
  条件: {A B : Matrix n n R}
  证明: Matrix.ext_iff_mulVec

Depends on / 依赖: Matrix, Matrix.ext_iff_mulVec, ext_iff_mulVec
-/
lemma ext_iff_smul {A B : Matrix n n R} :
    A = B ↔ forall v : n -> R, A • v = B • v := Matrix.ext_iff_mulVec

end mulVec

/-! ## `*ᵥ` as a right-module -/

section vecMul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module (Matrix n n R)ᵐᵒᵖ (n -> R)
  body: v ᵥ* A.unop
  one_smul := Matrix.vecMul_one
  mul_smul _ _ _ := (vecMul_vecMul _ _ _).symm
  zero_smul := vecMul_zero
  add_smul _ _ := vecMul_add _ _
  smul_zero _ := zero_vecMul _
  smul_add _ := add_vecMul _

中文:
实例 :
  签名: Module (Matrix n n R)ᵐᵒᵖ (n -> R)
  定义体: v ᵥ* A.unop
  one_smul := Matrix.vecMul_one
  mul_smul _ _ _ := (vecMul_vecMul _ _ _).symm
  zero_smul := vecMul_zero
  add_smul _ _ := vecMul_add _ _
  smul_zero _ := zero_vecMul _
  smul_add _ := add_vecMul _

Depends on / 依赖: A.unop
-/
instance : Module (Matrix n n R)ᵐᵒᵖ (n -> R) where
  smul A v := v ᵥ* A.unop
  one_smul := Matrix.vecMul_one
  mul_smul _ _ _ := (vecMul_vecMul _ _ _).symm
  zero_smul := vecMul_zero
  add_smul _ _ := vecMul_add _ _
  smul_zero _ := zero_vecMul _
  smul_add _ := add_vecMul _

/--
lemma `op_smul_eq_vecMul` / 引理 `op_smul_eq_vecMul`

English:
lemma op_smul_eq_vecMul
  given: (A : (Matrix n n R)ᵐᵒᵖ) (v : n -> R)
  statement: A • v = v ᵥ* A.unop
  proof: rfl

中文:
引理 op_smul_eq_vecMul
  条件: (A : (Matrix n n R)ᵐᵒᵖ) (v : n -> R)
  结论: A • v = v ᵥ* A.unop
  证明: rfl
-/
@[simp] lemma op_smul_eq_vecMul (A : (Matrix n n R)ᵐᵒᵖ) (v : n -> R) : A • v = v ᵥ* A.unop := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DistribSMul
  signature: S R] [IsScalarTower S R R] : SMulCommClass (Matrix n n R)ᵐᵒᵖ S (n -> R) where
  body: smul_vecMul s v A.unop

中文:
实例 [DistribSMul
  签名: S R] [IsScalarTower S R R] : SMulCommClass (Matrix n n R)ᵐᵒᵖ S (n -> R) where
  定义体: smul_vecMul s v A.unop

Depends on / 依赖: A.unop, smul_vecMul
-/
instance [DistribSMul S R] [IsScalarTower S R R] : SMulCommClass (Matrix n n R)ᵐᵒᵖ S (n -> R) where
  smul_comm A s v := smul_vecMul s v A.unop

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DistribSMul
  signature: S R] [IsScalarTower S R R] : SMulCommClass S (Matrix n n R)ᵐᵒᵖ (n -> R) where
  body: (smul_vecMul s v A.unop).symm

中文:
实例 [DistribSMul
  签名: S R] [IsScalarTower S R R] : SMulCommClass S (Matrix n n R)ᵐᵒᵖ (n -> R) where
  定义体: (smul_vecMul s v A.unop).symm

Depends on / 依赖: A.unop, smul_vecMul
-/
instance [DistribSMul S R] [IsScalarTower S R R] : SMulCommClass S (Matrix n n R)ᵐᵒᵖ (n -> R) where
  smul_comm s A v := (smul_vecMul s v A.unop).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DistribSMul
  signature: S R] [SMulCommClass S R R] : IsScalarTower S (Matrix n n R)ᵐᵒᵖ (n -> R) where
  body: vecMul_smul v s A.unop

中文:
实例 [DistribSMul
  签名: S R] [SMulCommClass S R R] : IsScalarTower S (Matrix n n R)ᵐᵒᵖ (n -> R) where
  定义体: vecMul_smul v s A.unop

Depends on / 依赖: A.unop, vecMul_smul
-/
instance [DistribSMul S R] [SMulCommClass S R R] : IsScalarTower S (Matrix n n R)ᵐᵒᵖ (n -> R) where
  smul_assoc s A v := vecMul_smul v s A.unop

end vecMul

end Matrix
