/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Opposite

/-!
# Module operations on `Mᵐᵒᵖ`

This file contains definitions that build on top of the group action definitions in
`Mathlib/Algebra/GroupWithZero/Action/Opposite.lean`.
-/

@[expose] public section

section

variable {R S M : Type*} [Semiring R] [Semiring S] [AddCommMonoid M] [Module S M]

@[ext high]
/--
theorem `LinearMap.ext_ring_op` / 定理 `LinearMap.ext_ring_op`

English:
theorem LinearMap.ext_ring_op
  proof: ext fun x => by
    rw [← one_mul x]; rw [← op_smul_eq_mul]; rw [f.map_smulₛₗ]; rw [h]; rw [g.map_smulₛₗ]

中文:
定理 LinearMap.ext_ring_op
  证明: ext fun x => by
    rw [← one_mul x]; rw [← op_smul_eq_mul]; rw [f.map_smulₛₗ]; rw [h]; rw [g.map_smulₛₗ]

Depends on / 依赖: f.map_smul, g.map_smul, one_mul, op_smul_eq_mul
-/
theorem LinearMap.ext_ring_op
    {σ : Rᵐᵒᵖ ->+* S} {f g : R ->ₛₗ[σ] M} (h : f (1 : R) = g (1 : R)) :
    f = g :=
  ext fun x => by
    rw [← one_mul x]; rw [← op_smul_eq_mul]; rw [f.map_smulₛₗ]; rw [h]; rw [g.map_smulₛₗ]

end

namespace MulOpposite

universe u v

variable (R : Type u) {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]

/--
Definition of `opLinearEquiv` / `opLinearEquiv` 的定义

English:
definition opLinearEquiv
  signature: : M ≃ₗ[R] Mᵐᵒᵖ
  body: { opAddEquiv with map_smul' := MulOpposite.op_smul }

@[simp]

中文:
定义 opLinearEquiv
  签名: : M ≃ₗ[R] Mᵐᵒᵖ
  定义体: { opAddEquiv with map_smul' := MulOpposite.op_smul }

@[simp]

Depends on / 依赖: MulOpposite, MulOpposite.op_smul, map_smul, opAddEquiv, op_smul
-/
def opLinearEquiv : M ≃ₗ[R] Mᵐᵒᵖ :=
  { opAddEquiv with map_smul' := MulOpposite.op_smul }

@[simp]
/--
theorem `coe_opLinearEquiv` / 定理 `coe_opLinearEquiv`

English:
theorem coe_opLinearEquiv
  statement: (opLinearEquiv R : M -> Mᵐᵒᵖ) = op
  proof: rfl

@[simp]

中文:
定理 coe_opLinearEquiv
  结论: (opLinearEquiv R : M -> Mᵐᵒᵖ) = op
  证明: rfl

@[simp]
-/
theorem coe_opLinearEquiv : (opLinearEquiv R : M -> Mᵐᵒᵖ) = op :=
  rfl

@[simp]
/--
theorem `coe_opLinearEquiv_symm` / 定理 `coe_opLinearEquiv_symm`

English:
theorem coe_opLinearEquiv_symm
  statement: ((opLinearEquiv R).symm : Mᵐᵒᵖ -> M) = unop
  proof: rfl

@[simp]

中文:
定理 coe_opLinearEquiv_symm
  结论: ((opLinearEquiv R).symm : Mᵐᵒᵖ -> M) = unop
  证明: rfl

@[simp]
-/
theorem coe_opLinearEquiv_symm : ((opLinearEquiv R).symm : Mᵐᵒᵖ -> M) = unop :=
  rfl

@[simp]
/--
theorem `coe_opLinearEquiv_toLinearMap` / 定理 `coe_opLinearEquiv_toLinearMap`

English:
theorem coe_opLinearEquiv_toLinearMap
  statement: ((opLinearEquiv R).toLinearMap : M -> Mᵐᵒᵖ) = op
  proof: rfl

@[simp]

中文:
定理 coe_opLinearEquiv_toLinearMap
  结论: ((opLinearEquiv R).toLinearMap : M -> Mᵐᵒᵖ) = op
  证明: rfl

@[simp]
-/
theorem coe_opLinearEquiv_toLinearMap : ((opLinearEquiv R).toLinearMap : M -> Mᵐᵒᵖ) = op :=
  rfl

@[simp]
/--
theorem `coe_opLinearEquiv_symm_toLinearMap` / 定理 `coe_opLinearEquiv_symm_toLinearMap`

English:
theorem coe_opLinearEquiv_symm_toLinearMap
  proof: rfl

中文:
定理 coe_opLinearEquiv_symm_toLinearMap
  证明: rfl
-/
theorem coe_opLinearEquiv_symm_toLinearMap :
    ((opLinearEquiv R).symm.toLinearMap : Mᵐᵒᵖ -> M) = unop :=
  rfl

/--
theorem `opLinearEquiv_toAddEquiv` / 定理 `opLinearEquiv_toAddEquiv`

English:
theorem opLinearEquiv_toAddEquiv
  statement: (opLinearEquiv R : M ≃ₗ[R] Mᵐᵒᵖ).toAddEquiv = opAddEquiv
  proof: rfl

@[simp]

中文:
定理 opLinearEquiv_toAddEquiv
  结论: (opLinearEquiv R : M ≃ₗ[R] Mᵐᵒᵖ).toAddEquiv = opAddEquiv
  证明: rfl

@[simp]
-/
theorem opLinearEquiv_toAddEquiv : (opLinearEquiv R : M ≃ₗ[R] Mᵐᵒᵖ).toAddEquiv = opAddEquiv :=
  rfl

@[simp]
/--
theorem `coe_opLinearEquiv_addEquiv` / 定理 `coe_opLinearEquiv_addEquiv`

English:
theorem coe_opLinearEquiv_addEquiv
  statement: ((opLinearEquiv R : M ≃ₗ[R] Mᵐᵒᵖ) : M ≃+ Mᵐᵒᵖ) = opAddEquiv
  proof: rfl

中文:
定理 coe_opLinearEquiv_addEquiv
  结论: ((opLinearEquiv R : M ≃ₗ[R] Mᵐᵒᵖ) : M ≃+ Mᵐᵒᵖ) = opAddEquiv
  证明: rfl
-/
theorem coe_opLinearEquiv_addEquiv : ((opLinearEquiv R : M ≃ₗ[R] Mᵐᵒᵖ) : M ≃+ Mᵐᵒᵖ) = opAddEquiv :=
  rfl

/--
theorem `opLinearEquiv_symm_toAddEquiv` / 定理 `opLinearEquiv_symm_toAddEquiv`

English:
theorem opLinearEquiv_symm_toAddEquiv
  proof: rfl

@[simp]

中文:
定理 opLinearEquiv_symm_toAddEquiv
  证明: rfl

@[simp]
-/
theorem opLinearEquiv_symm_toAddEquiv :
    (opLinearEquiv R : M ≃ₗ[R] Mᵐᵒᵖ).symm.toAddEquiv = opAddEquiv.symm :=
  rfl

@[simp]
/--
theorem `coe_opLinearEquiv_symm_addEquiv` / 定理 `coe_opLinearEquiv_symm_addEquiv`

English:
theorem coe_opLinearEquiv_symm_addEquiv
  proof: rfl

中文:
定理 coe_opLinearEquiv_symm_addEquiv
  证明: rfl
-/
theorem coe_opLinearEquiv_symm_addEquiv :
    ((opLinearEquiv R : M ≃ₗ[R] Mᵐᵒᵖ).symm : Mᵐᵒᵖ ≃+ M) = opAddEquiv.symm :=
  rfl

end MulOpposite
