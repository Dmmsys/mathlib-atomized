/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.RingTheory.Bialgebra.Hom
public import Mathlib.RingTheory.Coalgebra.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Bialgebra structure on quotients

If `I` is a two-sided ideal of an `R`-bialgebra `A` whose underlying `R`-submodule is a
coideal, then the quotient `A ⧸ I` inherits a bialgebra structure.

## Main definitions

* `Bialgebra.Quotient.counitAlgHom` : the counit on `A ⧸ I`, as an `R`-algebra homomorphism.
* `Bialgebra.Quotient.comulAlgHom` : comultiplication on `A ⧸ I` as an `R`-algebra homomorphism.
* `Bialgebra.Quotient.mkBialgHom` : `Ideal.Quotient.mkₐ` as a bialgebra homomorphism.

## Main results

* `Bialgebra R (A ⧸ I)` instance when `[I.IsTwoSided]` and `[(I.restrictScalars R).IsCoideal]`.
-/

@[expose] public section

open Bialgebra Coalgebra LinearMap TensorProduct

variable {R A : Type*} [CommRing R] [Ring A] [Bialgebra R A]
variable (I : Ideal A) [I.IsTwoSided] [(I.restrictScalars R).IsCoideal]

namespace Bialgebra.Quotient

/--
Definition of `counitAlgHom` / `counitAlgHom` 的定义

English:
definition counitAlgHom
  signature: : (A ⧸ I) ->ₐ[R] R
  body: Ideal.Quotient.liftₐ I (Bialgebra.counitAlgHom R A)
    (Submodule.IsCoideal.counit_eq_zero (I := I.restrictScalars R))

中文:
定义 counitAlgHom
  签名: : (A ⧸ I) ->ₐ[R] R
  定义体: Ideal.Quotient.liftₐ I (Bialgebra.counitAlgHom R A)
    (Submodule.IsCoideal.counit_eq_zero (I := I.restrictScalars R))

Depends on / 依赖: Bialgebra, Bialgebra.counitAlgHom, I.restrictScalars, Ideal.Quotient.lift, IsCoideal, Quotient, Submodule, Submodule.IsCoideal.counit_eq_zero, counitAlgHom, counit_eq_zero, restrictScalars
-/
def counitAlgHom : (A ⧸ I) ->ₐ[R] R :=
  Ideal.Quotient.liftₐ I (Bialgebra.counitAlgHom R A)
    (Submodule.IsCoideal.counit_eq_zero (I := I.restrictScalars R))

/--
Definition of `comulAlgHom` / `comulAlgHom` 的定义

English:
definition comulAlgHom
  signature: : (A ⧸ I) ->ₐ[R] (A ⧸ I) otimes[R] (A ⧸ I)
  body: Ideal.Quotient.liftₐ I
    ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)).comp
      (Bialgebra.comulAlgHom R A))
    (Submodule.IsCoideal.map_mkQ_comul_eq_zero (I := I.restrictScalars R))

中文:
定义 comulAlgHom
  签名: : (A ⧸ I) ->ₐ[R] (A ⧸ I) otimes[R] (A ⧸ I)
  定义体: Ideal.Quotient.liftₐ I
    ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)).comp
      (Bialgebra.comulAlgHom R A))
    (Submodule.IsCoideal.map_mkQ_comul_eq_zero (I := I.restrictScalars R))

Depends on / 依赖: Algebra, Algebra.TensorProduct.map, Bialgebra, Bialgebra.comulAlgHom, I.restrictScalars, Ideal.Quotient.lift, Ideal.Quotient.mk, IsCoideal, Quotient, Submodule, Submodule.IsCoideal.map_mkQ_comul_eq_zero, TensorProduct, comulAlgHom, map_mkQ_comul_eq_zero, restrictScalars
-/
def comulAlgHom : (A ⧸ I) ->ₐ[R] (A ⧸ I) otimes[R] (A ⧸ I) :=
  Ideal.Quotient.liftₐ I
    ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)).comp
      (Bialgebra.comulAlgHom R A))
    (Submodule.IsCoideal.map_mkQ_comul_eq_zero (I := I.restrictScalars R))

/--
lemma `counit_comp_mkₐ` / 引理 `counit_comp_mkₐ`

English:
lemma counit_comp_mkₐ
  proof: rfl

中文:
引理 counit_comp_mkₐ
  证明: rfl
-/
lemma counit_comp_mkₐ :
    (counitAlgHom I).toLinearMap ∘ₗ (Ideal.Quotient.mkₐ R I).toLinearMap = counit := rfl

/--
lemma `comul_comp_mkₐ` / 引理 `comul_comp_mkₐ`

English:
lemma comul_comp_mkₐ
  proof: rfl

中文:
引理 comul_comp_mkₐ
  证明: rfl

Depends on / 依赖: Ideal.Quotient.mk, Quotient, toLinearMap
-/
lemma comul_comp_mkₐ :
    (comulAlgHom (R := R) I).toLinearMap ∘ₗ (Ideal.Quotient.mkₐ R I).toLinearMap =
      map (Ideal.Quotient.mkₐ R I).toLinearMap (Ideal.Quotient.mkₐ R I).toLinearMap ∘ₗ comul := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bialgebra R (A ⧸ I)
  body: by
  refine .ofAlgHom (comulAlgHom I) (counitAlgHom I) ?_ ?_ ?_ <;>
    refine Ideal.Quotient.algHom_ext R (AlgHom.toLinearMap_injective ?_) <;>
    simp only [coassoc_simps, AlgHom.comp_toLinearMap, Algebra.TensorProduct.toLinearMap_map,
      comul_comp_mkₐ, counit_comp_mkₐ]
  · simp [coassoc_simp

中文:
实例 :
  签名: 双代数 R (A ⧸ I)
  定义体: by
  refine .ofAlgHom (comulAlgHom I) (counitAlgHom I) ?_ ?_ ?_ <;>
    refine Ideal.Quotient.algHom_ext R (AlgHom.toLinearMap_injective ?_) <;>
    simp only [coassoc_simps, AlgHom.comp_toLinearMap, Algebra.TensorProduct.toLinearMap_map,
      comul_comp_mkₐ, counit_comp_mkₐ]
  · simp [coassoc_simp

Depends on / 依赖: AlgHom, AlgHom.comp_toLinearMap, AlgHom.toLinearMap_injective, Algebra, Algebra.TensorProduct.toLinearMap_map, CoassocSimps, CoassocSimps.map_counit_comp_comul_left, CoassocSimps.map_counit_comp_comul_right, Ideal.Quotient.algHom_ext, Quotient, TensorProduct, algHom_ext, coassoc_simps, comp_toLinearMap, comulAlgHom, counitAlgHom, map_counit_comp_comul_left, map_counit_comp_comul_right, ofAlgHom, toLinearMap_injective
-/
instance : Bialgebra R (A ⧸ I) := by
  refine .ofAlgHom (comulAlgHom I) (counitAlgHom I) ?_ ?_ ?_ <;>
    refine Ideal.Quotient.algHom_ext R (AlgHom.toLinearMap_injective ?_) <;>
    simp only [coassoc_simps, AlgHom.comp_toLinearMap, Algebra.TensorProduct.toLinearMap_map,
      comul_comp_mkₐ, counit_comp_mkₐ]
  · simp [coassoc_simps]
  · rw [CoassocSimps.map_counit_comp_comul_left]; rfl
  · rw [CoassocSimps.map_counit_comp_comul_right]; rfl

/--
lemma `counit_mk` / 引理 `counit_mk`

English:
lemma counit_mk
  given: (a : A)
  proof: rfl

中文:
引理 counit_mk
  条件: (a : A)
  证明: rfl
-/
@[simp] lemma counit_mk (a : A) :
    counit (R := R) (Ideal.Quotient.mk I a) = counit a := rfl

/--
lemma `comul_mk` / 引理 `comul_mk`

English:
lemma comul_mk
  given: (a : A)
  proof: rfl

中文:
引理 comul_mk
  条件: (a : A)
  证明: rfl
-/
@[simp] lemma comul_mk (a : A) :
    comul (R := R) (Ideal.Quotient.mk I a) =
      map (Ideal.Quotient.mkₐ R I).toLinearMap (Ideal.Quotient.mkₐ R I).toLinearMap (comul a) :=
  rfl

/--
Definition of `mkBialgHom` / `mkBialgHom` 的定义

English:
definition mkBialgHom
  signature: : A ->ₐc[R] A ⧸ I
  body: .ofAlgHom (Ideal.Quotient.mkₐ R I) rfl rfl

中文:
定义 mkBialgHom
  签名: : A ->ₐc[R] A ⧸ I
  定义体: .ofAlgHom (Ideal.Quotient.mkₐ R I) rfl rfl

Depends on / 依赖: Ideal.Quotient.mk, Quotient, ofAlgHom
-/
def mkBialgHom : A ->ₐc[R] A ⧸ I := .ofAlgHom (Ideal.Quotient.mkₐ R I) rfl rfl

/--
lemma `mkBialgHom_apply` / 引理 `mkBialgHom_apply`

English:
lemma mkBialgHom_apply
  given: (a : A)
  proof: rfl

中文:
引理 mkBialgHom_apply
  条件: (a : A)
  证明: rfl
-/
@[simp] lemma mkBialgHom_apply (a : A) :
    mkBialgHom (R := R) I a = Ideal.Quotient.mk I a := rfl

end Bialgebra.Quotient
