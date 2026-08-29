/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Flat.Localization

/-!
# Flat modules in domains

We show that the tensor product of two injective linear maps is injective if the sources are flat
and the ring is an integral domain.
-/

public section

universe u

variable {R M N : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]

open TensorProduct Function

attribute [local instance 1100] Module.Free.of_divisionRing Module.Flat.of_free in
/--
lemma `TensorProduct.map_injective_of_flat_flat_of_isDomain` / 引理 `TensorProduct.map_injective_of_flat_flat_of_isDomain`

English:
lemma TensorProduct.map_injective_of_flat_flat_of_isDomain
  proof: by
  let K := FractionRing R
  refine .of_comp (f := TensorProduct.mk R K _ 1) ?_
  have H₁ := TensorProduct.map_injective_of_flat_flat (f.baseChange K) (g.baseChange K)
    (Module.Flat.lTensor_preserves_injective_linearMap f hf)
    (Module.Flat.lTensor_preserves_injective_linearMap g hg)
  have H

中文:
引理 TensorProduct.map_injective_of_flat_flat_of_isDomain
  证明: by
  let K := FractionRing R
  refine .of_comp (f := TensorProduct.mk R K _ 1) ?_
  have H₁ := TensorProduct.map_injective_of_flat_flat (f.baseChange K) (g.baseChange K)
    (Module.Flat.lTensor_preserves_injective_linearMap f hf)
    (Module.Flat.lTensor_preserves_injective_linearMap g hg)
  have H

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.assoc, AlgebraTensorModule.cancelBaseChange, FractionRing, Module, Module.Flat.lTensor_preserves_injective_linearMap, TensorProduct, TensorProduct.map_injective_of_flat_flat, TensorProduct.mk, baseChange, cancelBaseChange, f.baseChange, g.baseChange, injective, lTensor_preserves_injective_linearMap, map_injective_of_flat_flat, of_comp, otimes, symm.injective
-/
lemma TensorProduct.map_injective_of_flat_flat_of_isDomain
    (f : P ->ₗ[R] M) (g : Q ->ₗ[R] N) [H : Module.Flat R P] [Module.Flat R Q]
    (hf : Injective f) (hg : Injective g) : Injective (TensorProduct.map f g) := by
  let K := FractionRing R
  refine .of_comp (f := TensorProduct.mk R K _ 1) ?_
  have H₁ := TensorProduct.map_injective_of_flat_flat (f.baseChange K) (g.baseChange K)
    (Module.Flat.lTensor_preserves_injective_linearMap f hf)
    (Module.Flat.lTensor_preserves_injective_linearMap g hg)
  have H₂ := (AlgebraTensorModule.cancelBaseChange R K K (K otimes[R] P) Q).symm.injective
  have H₃ := (AlgebraTensorModule.cancelBaseChange R K K (K otimes[R] M) N).injective
  have H₄ := (AlgebraTensorModule.assoc R R K K P Q).symm.injective
  have H₅ := (AlgebraTensorModule.assoc R R K K M N).injective
  have H₆ := Module.Flat.rTensor_preserves_injective_linearMap (M := P otimes[R] Q)
    (Algebra.linearMap R K) (FaithfulSMul.algebraMap_injective R K)
  have H₇ := (TensorProduct.lid R (P otimes[R] Q)).symm.injective
convert! H₅.comp H₃.comp H₁.comp H₂.comp H₄.comp H₆.comp H₇
  dsimp only [← LinearMap.coe_comp, ← LinearEquiv.coe_toLinearMap,
    ← @LinearMap.coe_restrictScalars R K]
  congr! 1
  ext p q
  -- `simp` solves the goal but it times out
  change (1 : K) otimesₜ[R] (f p otimesₜ[R] g q) = (AlgebraTensorModule.assoc R R K K M N)
    (((1 : K) • (algebraMap R K) 1 otimesₜ[R] f p) otimesₜ[R] g q)
  simp only [map_one, one_smul, AlgebraTensorModule.assoc_tmul]

variable {ι κ : Type*} {v : ι -> M} {w : κ -> N} {s : Set ι} {t : Set κ}

/--
lemma `LinearIndependent.tmul_of_isDomain` / 引理 `LinearIndependent.tmul_of_isDomain`

English:
lemma LinearIndependent.tmul_of_isDomain
  given: (hv : LinearIndependent R v) (hw : LinearIndependent R w)
  proof: by
  rw [LinearIndependent]
  convert!
    (TensorProduct.map_injective_of_flat_flat_of_isDomain _ _ hv hw).comp
      (finsuppTensorFinsupp' _ _ _).symm.injective
  rw [← LinearEquiv.coe_toLinearMap]; rw [← LinearMap.coe_comp]
  congr!
  ext i
  simp [finsuppTensorFinsupp'_symm_single_eq_single_one

中文:
引理 LinearIndependent.tmul_of_isDomain
  条件: (hv : LinearIndependent R v) (hw : LinearIndependent R w)
  证明: by
  rw [LinearIndependent]
  convert!
    (TensorProduct.map_injective_of_flat_flat_of_isDomain _ _ hv hw).comp
      (finsuppTensorFinsupp' _ _ _).symm.injective
  rw [← LinearEquiv.coe_toLinearMap]; rw [← LinearMap.coe_comp]
  congr!
  ext i
  simp [finsuppTensorFinsupp'_symm_single_eq_single_one

Depends on / 依赖: LinearEquiv, LinearEquiv.coe_toLinearMap, LinearIndependent, LinearMap, LinearMap.coe_comp, TensorProduct, TensorProduct.map_injective_of_flat_flat_of_isDomain, _symm_single_eq_single_one_tmul, coe_comp, coe_toLinearMap, convert, finsuppTensorFinsupp, injective, map_injective_of_flat_flat_of_isDomain, symm.injective
-/
lemma LinearIndependent.tmul_of_isDomain (hv : LinearIndependent R v) (hw : LinearIndependent R w) :
    LinearIndependent R fun i : ι × κ => v i.1 otimesₜ[R] w i.2 := by
  rw [LinearIndependent]
  convert!
    (TensorProduct.map_injective_of_flat_flat_of_isDomain _ _ hv hw).comp
      (finsuppTensorFinsupp' _ _ _).symm.injective
  rw [← LinearEquiv.coe_toLinearMap]; rw [← LinearMap.coe_comp]
  congr!
  ext i
  simp [finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]

/-- Tensor product of linearly independent families is linearly independent over domains.
This is true over non-domains if one of the modules is flat.
See `LinearIndepOn.tmul_of_flat_left`. -/
nonrec lemma LinearIndepOn.tmul_of_isDomain (hv : LinearIndepOn R v s) (hw : LinearIndepOn R w t) :
    LinearIndepOn R (fun i : ι × κ => v i.1 otimesₜ[R] w i.2) (s ×ˢ t) :=
  ((hv.tmul_of_isDomain hw).comp _ (Equiv.Set.prod _ _).injective :)
