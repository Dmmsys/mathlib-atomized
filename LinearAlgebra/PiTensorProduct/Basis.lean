/-
Copyright (c) 2025 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison, Sophie Morel
-/
module

public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.PiTensorProduct.Finsupp

/-!
# Basis for `PiTensorProduct`

This file constructs a basis for `PiTensorProduct` given bases on the component spaces.
-/

@[expose] public section

section PiTensorProduct

attribute [local ext] PiTensorProduct.ext

open LinearMap PiTensorProduct Module TensorProduct

variable {ι R : Type*} {M : ι -> Type*} {κ : ι -> Type*} [CommSemiring R] [forall i, AddCommMonoid (M i)]
  [forall i, Module R (M i)]

open scoped Classical in
/--
Definition of `Basis.piTensorProduct` / `Basis.piTensorProduct` 的定义

English:
definition Basis.piTensorProduct
  signature: [Finite ι] (b : Π i, Basis (κ i) R (M i))
  body: haveI := Fintype.ofFinite ι
  Finsupp.basisSingleOne.map
    ((PiTensorProduct.congr (fun i => (b i).repr)) ≪≫ₗ
      ofFinsuppEquiv ≪≫ₗ
      Finsupp.lcongr (Equiv.refl _) (constantBaseRingEquiv _ R).toLinearEquiv).symm

@[simp]

中文:
定义 Basis.piTensorProduct
  签名: [Finite ι] (b : Π i, Basis (κ i) R (M i))
  定义体: haveI := Fintype.ofFinite ι
  Finsupp.basisSingleOne.map
    ((PiTensorProduct.congr (fun i => (b i).repr)) ≪≫ₗ
      ofFinsuppEquiv ≪≫ₗ
      Finsupp.lcongr (Equiv.refl _) (constantBaseRingEquiv _ R).toLinearEquiv).symm

@[simp]

Depends on / 依赖: Equiv.refl, Finsupp, Finsupp.basisSingleOne.map, Finsupp.lcongr, Fintype, Fintype.ofFinite, PiTensorProduct, PiTensorProduct.congr, basisSingleOne, constantBaseRingEquiv, lcongr, ofFinite, ofFinsuppEquiv, toLinearEquiv
-/
noncomputable def Basis.piTensorProduct [Finite ι] (b : Π i, Basis (κ i) R (M i)) :
    Basis (Π i, κ i) R (⨂[R] i, M i) :=
  haveI := Fintype.ofFinite ι
  Finsupp.basisSingleOne.map
    ((PiTensorProduct.congr (fun i => (b i).repr)) ≪≫ₗ
      ofFinsuppEquiv ≪≫ₗ
      Finsupp.lcongr (Equiv.refl _) (constantBaseRingEquiv _ R).toLinearEquiv).symm

@[simp]
/--
theorem `Basis.piTensorProduct_repr_tprod_apply` / 定理 `Basis.piTensorProduct_repr_tprod_apply`

English:
theorem Basis.piTensorProduct_repr_tprod_apply
  statement: [Fintype ι] (b : Π i, Basis (κ i) R (M i))
  proof: by
  rw [piTensorProduct]; rw [Subsingleton.elim (Fintype.ofFinite ι) ‹_›]
  simp

@[simp]

中文:
定理 Basis.piTensorProduct_repr_tprod_apply
  结论: [Fintype ι] (b : Π i, Basis (κ i) R (M i))
  证明: by
  rw [piTensorProduct]; rw [Subsingleton.elim (Fintype.ofFinite ι) ‹_›]
  simp

@[simp]

Depends on / 依赖: Fintype, Fintype.ofFinite, Subsingleton, Subsingleton.elim, ofFinite, piTensorProduct
-/
theorem Basis.piTensorProduct_repr_tprod_apply [Fintype ι] (b : Π i, Basis (κ i) R (M i))
    (x : Π i, M i) (p : Π i, κ i) :
    (Basis.piTensorProduct b).repr (tprod R x) p = ∏ i : ι, (b i).repr (x i) (p i) := by
  rw [piTensorProduct]; rw [Subsingleton.elim (Fintype.ofFinite ι) ‹_›]
  simp

@[simp]
/--
theorem `Basis.piTensorProduct_apply` / 定理 `Basis.piTensorProduct_apply`

English:
theorem Basis.piTensorProduct_apply
  given: [Finite ι] (b : Π i, Basis (κ i) R (M i)) (p : Π i, κ i)
  proof: by
  have := Fintype.ofFinite ι
  classical
  refine (Basis.piTensorProduct b).ext_elem (fun q => ?_)
  simp [Finsupp.single_apply, Fintype.prod_ite_zero, ← funext_iff]

中文:
定理 Basis.piTensorProduct_apply
  条件: [Finite ι] (b : Π i, Basis (κ i) R (M i)) (p : Π i, κ i)
  证明: by
  have := Fintype.ofFinite ι
  classical
  refine (Basis.piTensorProduct b).ext_elem (fun q => ?_)
  simp [Finsupp.single_apply, Fintype.prod_ite_zero, ← funext_iff]

Depends on / 依赖: Basis.piTensorProduct, Finsupp, Finsupp.single_apply, Fintype, Fintype.ofFinite, Fintype.prod_ite_zero, classical, ext_elem, funext_iff, ofFinite, piTensorProduct, prod_ite_zero, single_apply
-/
theorem Basis.piTensorProduct_apply [Finite ι] (b : Π i, Basis (κ i) R (M i)) (p : Π i, κ i) :
    Basis.piTensorProduct b p = ⨂ₜ[R] i, (b i) (p i) := by
  have := Fintype.ofFinite ι
  classical
  refine (Basis.piTensorProduct b).ext_elem (fun q => ?_)
  simp [Finsupp.single_apply, Fintype.prod_ite_zero, ← funext_iff]

end PiTensorProduct
