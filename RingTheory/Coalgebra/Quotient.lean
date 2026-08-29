/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Coalgebra.CoassocSimps
public import Mathlib.RingTheory.Coalgebra.Hom

/-!
# Coalgebra structure on the quotient by a coideal

## Main definitions

* `Submodule.IsCoideal I` : the submodule `I : Submodule R C` is a coideal.
* `Coalgebra.Quotient.mkQCoalgHom` : `Submodule.mkQ` as a coalgebra homomorphism.

## Main results

* `Coalgebra` instance on `C ⧸ I` when `[I.IsCoideal]`.
-/

public section

open Coalgebra LinearMap TensorProduct

variable {R C : Type*} [CommRing R] [AddCommGroup C] [Module R C]

section CoalgebraStruct

variable [CoalgebraStruct R C]

/-- An `R`-submodule `I` of an `R`-coalgebra `C` is a *coideal* if the counit vanishes on
`I` and the comultiplication descends through the module quotient `C ⧸ I`. -/
@[mk_iff]
/--
Definition of `Submodule.IsCoideal` / `Submodule.IsCoideal` 的定义

English:
class Submodule.IsCoideal
  parameters: (I : Submodule R C)
  axioms and operations (2):
    - counit_eq_zero : forall ⦃x : C⦄, x in I -> counit (R := R) x = 0
    - map_mkQ_comul_eq_zero : forall ⦃x : C⦄, x in I -> TensorProduct.map I.mkQ I.mkQ (comul x) = 0

中文:
类 子模.是余ideal
  参数: (I : 子模 R C)
  公理与运算 (2 个):
    - counit_eq_zero : 对任意 ⦃x : C⦄, x in I -> counit (R := R) x = 0
    - map_mkQ_comul_eq_zero : 对任意 ⦃x : C⦄, x in I -> 张量积.map I.mkQ I.mkQ (comul x) = 0
-/
class Submodule.IsCoideal (I : Submodule R C) : Prop where
  counit_eq_zero : forall ⦃x : C⦄, x in I -> counit (R := R) x = 0
  map_mkQ_comul_eq_zero : forall ⦃x : C⦄, x in I -> TensorProduct.map I.mkQ I.mkQ (comul x) = 0

/--
lemma `Submodule.isCoideal_iff_comul_mem` / 引理 `Submodule.isCoideal_iff_comul_mem`

English:
lemma Submodule.isCoideal_iff_comul_mem
  given: (I : Submodule R C)
  proof: by
  simp_rw [isCoideal_iff, ← LinearMap.mem_ker,
    TensorProduct.map_ker (LinearMap.exact_subtype_mkQ I) I.mkQ_surjective
      (LinearMap.exact_subtype_mkQ I) I.mkQ_surjective]

中文:
引理 子模.isCoideal_iff_comul_mem
  条件: (I : 子模 R C)
  证明: by
  simp_rw [isCoideal_iff, ← LinearMap.mem_ker,
    TensorProduct.map_ker (LinearMap.exact_subtype_mkQ I) I.mkQ_surjective
      (LinearMap.exact_subtype_mkQ I) I.mkQ_surjective]
-/
lemma Submodule.isCoideal_iff_comul_mem (I : Submodule R C) :
    I.IsCoideal ↔ (forall x in I, counit (R := R) x = 0) ∧
      forall x in I, comul x in
        LinearMap.range (lTensor C I.subtype) ⊔ LinearMap.range (rTensor C I.subtype) := by
  simp_rw [isCoideal_iff, ← LinearMap.mem_ker,
    TensorProduct.map_ker (LinearMap.exact_subtype_mkQ I) I.mkQ_surjective
      (LinearMap.exact_subtype_mkQ I) I.mkQ_surjective]

end CoalgebraStruct

namespace Coalgebra.Quotient

section CoalgebraStruct

variable [CoalgebraStruct R C] (I : Submodule R C) [I.IsCoideal]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoalgebraStruct R (C ⧸ I)
  body: I.liftQ (map I.mkQ I.mkQ ∘ₗ comul) Submodule.IsCoideal.map_mkQ_comul_eq_zero
  counit := I.liftQ counit Submodule.IsCoideal.counit_eq_zero

中文:
实例 :
  签名: 余algebraStruct R (C ⧸ I)
  定义体: I.liftQ (map I.mkQ I.mkQ ∘ₗ comul) Submodule.IsCoideal.map_mkQ_comul_eq_zero
  counit := I.liftQ counit Submodule.IsCoideal.counit_eq_zero

Depends on / 依赖: I.liftQ, I.mkQ, IsCoideal, Submodule, Submodule.IsCoideal.map_mkQ_comul_eq_zero, map_mkQ_comul_eq_zero
-/
instance : CoalgebraStruct R (C ⧸ I) where
  comul := I.liftQ (map I.mkQ I.mkQ ∘ₗ comul) Submodule.IsCoideal.map_mkQ_comul_eq_zero
  counit := I.liftQ counit Submodule.IsCoideal.counit_eq_zero

/--
lemma `comul_comp_mkQ` / 引理 `comul_comp_mkQ`

English:
lemma comul_comp_mkQ
  statement: comul ∘ₗ I.mkQ = map I.mkQ I.mkQ ∘ₗ (comul : C ->ₗ[R] _)
  proof: rfl

中文:
引理 comul_comp_mkQ
  结论: comul ∘ₗ I.mkQ = map I.mkQ I.mkQ ∘ₗ (comul : C ->ₗ[R] _)
  证明: rfl
-/
lemma comul_comp_mkQ : comul ∘ₗ I.mkQ = map I.mkQ I.mkQ ∘ₗ (comul : C ->ₗ[R] _) := rfl

/--
lemma `counit_comp_mkQ` / 引理 `counit_comp_mkQ`

English:
lemma counit_comp_mkQ
  statement: counit ∘ₗ I.mkQ = (counit : C ->ₗ[R] R)
  proof: rfl

@[simp]

中文:
引理 counit_comp_mkQ
  结论: counit ∘ₗ I.mkQ = (counit : C ->ₗ[R] R)
  证明: rfl

@[simp]
-/
lemma counit_comp_mkQ : counit ∘ₗ I.mkQ = (counit : C ->ₗ[R] R) := rfl

@[simp]
/--
lemma `counit_mk` / 引理 `counit_mk`

English:
lemma counit_mk
  given: (x : C)
  statement: counit (R := R) (Submodule.Quotient.mk (p := I) x) = counit x
  proof: rfl

@[simp]

中文:
引理 counit_mk
  条件: (x : C)
  结论: counit (R := R) (子模.商.mk (p := I) x) = counit x
  证明: rfl

@[simp]

Depends on / 依赖: Quotient, Submodule, Submodule.Quotient.mk, counit
-/
lemma counit_mk (x : C) : counit (R := R) (Submodule.Quotient.mk (p := I) x) = counit x := rfl

@[simp]
/--
lemma `comul_mk` / 引理 `comul_mk`

English:
lemma comul_mk
  given: (x : C)
  proof: rfl

中文:
引理 comul_mk
  条件: (x : C)
  证明: rfl

Depends on / 依赖: I.mkQ, Quotient, Submodule, Submodule.Quotient.mk
-/
lemma comul_mk (x : C) :
    comul (R := R) (Submodule.Quotient.mk (p := I) x) = map I.mkQ I.mkQ (comul x) := rfl

/--
Definition of `mkQCoalgHom` / `mkQCoalgHom` 的定义

English:
definition mkQCoalgHom
  signature: : C ->ₗc[R] C ⧸ I
  body: ⟨I.mkQ, rfl, rfl⟩

中文:
定义 mkQCoalgHom
  签名: : C ->ₗc[R] C ⧸ I
  定义体: ⟨I.mkQ, rfl, rfl⟩
-/
@[expose] def mkQCoalgHom : C ->ₗc[R] C ⧸ I := ⟨I.mkQ, rfl, rfl⟩

/--
lemma `mkQCoalgHom_apply` / 引理 `mkQCoalgHom_apply`

English:
lemma mkQCoalgHom_apply
  given: (x : C)
  proof: rfl

中文:
引理 mkQCoalgHom_apply
  条件: (x : C)
  证明: rfl
-/
@[simp] lemma mkQCoalgHom_apply (x : C) :
    mkQCoalgHom (R := R) I x = Submodule.Quotient.mk x := rfl

end CoalgebraStruct

variable [Coalgebra R C] (I : Submodule R C) [I.IsCoideal]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coalgebra R (C ⧸ I)
  body: by
  constructor <;> ext : 1 <;>
    simp only [coassoc_simps, comul_comp_mkQ, counit_comp_mkQ]
  · rw [CoassocSimps.map_counit_comp_comul_left]; rfl
  · rw [CoassocSimps.map_counit_comp_comul_right]; rfl

中文:
实例 :
  签名: 余algebra R (C ⧸ I)
  定义体: by
  constructor <;> ext : 1 <;>
    simp only [coassoc_simps, comul_comp_mkQ, counit_comp_mkQ]
  · rw [CoassocSimps.map_counit_comp_comul_left]; rfl
  · rw [CoassocSimps.map_counit_comp_comul_right]; rfl

Depends on / 依赖: CoassocSimps, CoassocSimps.map_counit_comp_comul_left, CoassocSimps.map_counit_comp_comul_right, coassoc_simps, comul_comp_mkQ, counit_comp_mkQ, map_counit_comp_comul_left, map_counit_comp_comul_right
-/
instance : Coalgebra R (C ⧸ I) := by
  constructor <;> ext : 1 <;>
    simp only [coassoc_simps, comul_comp_mkQ, counit_comp_mkQ]
  · rw [CoassocSimps.map_counit_comp_comul_left]; rfl
  · rw [CoassocSimps.map_counit_comp_comul_right]; rfl

end Coalgebra.Quotient
