/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Johan Commelin
-/
module

public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.Finsupp.Pi
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Results on bases of tensor products

In the file we construct a basis for the base change of a module to an algebra,
and deduce that `Module.Free` is stable under base change.

## Main declarations

- `Algebra.TensorProduct.basis`: given a basis of a module `M` over a commutative semiring `R`,
  and an `R`-algebra `A`, this provides a basis for `A ⊗[R] M` over `A`.
- `Algebra.TensorProduct.instFree`: if `M` is free, then so is `A ⊗[R] M`.

-/

@[expose] public section

assert_not_exists Cardinal

open Module
open scoped TensorProduct

namespace Algebra

namespace TensorProduct

variable {R A : Type*}

section Basis

universe uM uι
variable {M : Type uM} {ι : Type uι}
variable [CommSemiring R] [Semiring A] [Algebra R A]
variable [AddCommMonoid M] [Module R M] (b : Basis ι R M)

variable (A) in
/--
Definition of `basisAux` / `basisAux` 的定义

English:
definition basisAux
  signature: : A otimes[R] M ≃ₗ[R] ι ->₀ A
  body: _root_.TensorProduct.congr (Finsupp.uniqueLinearEquiv R A ()).symm b.repr ≪≫ₗ
    (finsuppTensorFinsupp R R A R PUnit ι).trans
      (Finsupp.lcongr (Equiv.uniqueProd ι PUnit) (_root_.TensorProduct.rid R A))

中文:
定义 basisAux
  签名: : A otimes[R] M ≃ₗ[R] ι ->₀ A
  定义体: _root_.TensorProduct.congr (Finsupp.uniqueLinearEquiv R A ()).symm b.repr ≪≫ₗ
    (finsuppTensorFinsupp R R A R PUnit ι).trans
      (Finsupp.lcongr (Equiv.uniqueProd ι PUnit) (_root_.TensorProduct.rid R A))

Depends on / 依赖: Equiv.uniqueProd, Finsupp, Finsupp.lcongr, Finsupp.uniqueLinearEquiv, TensorProduct, _root_, _root_.TensorProduct.congr, _root_.TensorProduct.rid, b.repr, finsuppTensorFinsupp, lcongr, uniqueLinearEquiv, uniqueProd
-/
noncomputable def basisAux : A otimes[R] M ≃ₗ[R] ι ->₀ A :=
  _root_.TensorProduct.congr (Finsupp.uniqueLinearEquiv R A ()).symm b.repr ≪≫ₗ
    (finsuppTensorFinsupp R R A R PUnit ι).trans
      (Finsupp.lcongr (Equiv.uniqueProd ι PUnit) (_root_.TensorProduct.rid R A))

/--
theorem `basisAux_tmul` / 定理 `basisAux_tmul`

English:
theorem basisAux_tmul
  given: (a : A) (m : M)
  proof: by
  ext
  simp [basisAux, ← Algebra.commutes, Algebra.smul_def]

中文:
定理 basisAux_tmul
  条件: (a : A) (m : M)
  证明: by
  ext
  simp [basisAux, ← Algebra.commutes, Algebra.smul_def]

Depends on / 依赖: Algebra, Algebra.commutes, Algebra.smul_def, basisAux, commutes, smul_def
-/
theorem basisAux_tmul (a : A) (m : M) :
    basisAux A b (a otimesₜ m) = a • Finsupp.mapRange (algebraMap R A) (map_zero _) (b.repr m) := by
  ext
  simp [basisAux, ← Algebra.commutes, Algebra.smul_def]

/--
theorem `basisAux_map_smul` / 定理 `basisAux_map_smul`

English:
theorem basisAux_map_smul
  given: (a : A) (x : A otimes[R] M)
  statement: basisAux A b (a • x) = a • basisAux A b x
  proof: TensorProduct.induction_on x (by simp)
    (fun x y => by simp only [TensorProduct.smul_tmul', basisAux_tmul, smul_assoc])
    fun x y hx hy => by simp [hx, hy]

中文:
定理 basisAux_map_smul
  条件: (a : A) (x : A otimes[R] M)
  结论: basisAux A b (a • x) = a • basisAux A b x
  证明: TensorProduct.induction_on x (by simp)
    (fun x y => by simp only [TensorProduct.smul_tmul', basisAux_tmul, smul_assoc])
    fun x y hx hy => by simp [hx, hy]

Depends on / 依赖: TensorProduct, TensorProduct.induction_on, TensorProduct.smul_tmul, basisAux_tmul, induction_on, smul_assoc, smul_tmul
-/
theorem basisAux_map_smul (a : A) (x : A otimes[R] M) : basisAux A b (a • x) = a • basisAux A b x :=
  TensorProduct.induction_on x (by simp)
    (fun x y => by simp only [TensorProduct.smul_tmul', basisAux_tmul, smul_assoc])
    fun x y hx hy => by simp [hx, hy]

variable (A) in
/--
Definition of `basis` / `basis` 的定义

English:
definition basis
  signature: : Basis ι A (A otimes[R] M) where
  body: { basisAux A b with map_smul' := basisAux_map_smul b }

@[simp]

中文:
定义 basis
  签名: : Basis ι A (A otimes[R] M) where
  定义体: { basisAux A b with map_smul' := basisAux_map_smul b }

@[simp]

Depends on / 依赖: basisAux, basisAux_map_smul, map_smul
-/
noncomputable def basis : Basis ι A (A otimes[R] M) where
  repr := { basisAux A b with map_smul' := basisAux_map_smul b }

@[simp]
/--
theorem `basis_repr_tmul` / 定理 `basis_repr_tmul`

English:
theorem basis_repr_tmul
  given: (a : A) (m : M)
  proof: basisAux_tmul b _ _

中文:
定理 basis_repr_tmul
  条件: (a : A) (m : M)
  证明: basisAux_tmul b _ _

Depends on / 依赖: basisAux_tmul
-/
theorem basis_repr_tmul (a : A) (m : M) :
    (basis A b).repr (a otimesₜ m) = a • Finsupp.mapRange (algebraMap R A) (map_zero _) (b.repr m) :=
  basisAux_tmul b _ _

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `basis_repr_symm_apply` / 定理 `basis_repr_symm_apply`

English:
theorem basis_repr_symm_apply
  given: (a : A) (i : ι)
  proof: by
  simp [basis, Equiv.uniqueProd_symm_apply, basisAux]

@[simp]

中文:
定理 basis_repr_symm_apply
  条件: (a : A) (i : ι)
  证明: by
  simp [basis, Equiv.uniqueProd_symm_apply, basisAux]

@[simp]

Depends on / 依赖: Equiv.uniqueProd_symm_apply, basisAux, uniqueProd_symm_apply
-/
theorem basis_repr_symm_apply (a : A) (i : ι) :
    (basis A b).repr.symm (Finsupp.single i a) = a otimesₜ b.repr.symm (Finsupp.single i 1) := by
  simp [basis, Equiv.uniqueProd_symm_apply, basisAux]

@[simp]
/--
theorem `basis_apply` / 定理 `basis_apply`

English:
theorem basis_apply
  given: (i : ι)
  statement: basis A b i = 1 otimesₜ b i
  proof: basis_repr_symm_apply b 1 i

中文:
定理 basis_apply
  条件: (i : ι)
  结论: basis A b i = 1 otimesₜ b i
  证明: basis_repr_symm_apply b 1 i

Depends on / 依赖: basis_repr_symm_apply
-/
theorem basis_apply (i : ι) : basis A b i = 1 otimesₜ b i := basis_repr_symm_apply b 1 i

/--
theorem `basis_repr_symm_apply'` / 定理 `basis_repr_symm_apply'`

English:
theorem basis_repr_symm_apply'
  given: (a : A) (i : ι)
  statement: a • basis A b i = a otimesₜ b i
  proof: by
  simpa using basis_repr_symm_apply b a i

中文:
定理 basis_repr_symm_apply'
  条件: (a : A) (i : ι)
  结论: a • basis A b i = a otimesₜ b i
  证明: by
  simpa using basis_repr_symm_apply b a i

Depends on / 依赖: basis_repr_symm_apply
-/
theorem basis_repr_symm_apply' (a : A) (i : ι) : a • basis A b i = a otimesₜ b i := by
  simpa using basis_repr_symm_apply b a i

section baseChange

open LinearMap

variable [Fintype ι]
variable {ι' N : Type*} [Fintype ι'] [DecidableEq ι'] [AddCommMonoid N] [Module R N]
variable (A : Type*) [CommSemiring A] [Algebra R A]

/--
lemma `_root_.Module.Basis.baseChange_linearMap` / 引理 `_root_.Module.Basis.baseChange_linearMap`

English:
lemma _root_.Module.Basis.baseChange_linearMap
  given: (b : Basis ι R M) (b' : Basis ι' R N) (ij : ι × ι')
  proof: by
  apply (basis A b').ext
  intro k
  conv_lhs => simp only [basis_apply, baseChange_tmul]
  simp_rw [Basis.linearMap_apply_apply, basis_apply]
  split <;> simp only [TensorProduct.tmul_zero]

中文:
引理 _root_.Module.Basis.baseChange_linearMap
  条件: (b : Basis ι R M) (b' : Basis ι' R N) (ij : ι × ι')
  证明: by
  apply (basis A b').ext
  intro k
  conv_lhs => simp only [basis_apply, baseChange_tmul]
  simp_rw [Basis.linearMap_apply_apply, basis_apply]
  split <;> simp only [TensorProduct.tmul_zero]

Depends on / 依赖: Basis.linearMap_apply_apply, TensorProduct, TensorProduct.tmul_zero, baseChange_tmul, basis_apply, conv_lhs, linearMap_apply_apply, simp_rw, tmul_zero
-/
lemma _root_.Module.Basis.baseChange_linearMap (b : Basis ι R M) (b' : Basis ι' R N) (ij : ι × ι') :
    baseChange A (b'.linearMap b ij) = (basis A b').linearMap (basis A b) ij := by
  apply (basis A b').ext
  intro k
  conv_lhs => simp only [basis_apply, baseChange_tmul]
  simp_rw [Basis.linearMap_apply_apply, basis_apply]
  split <;> simp only [TensorProduct.tmul_zero]

variable [DecidableEq ι]

/--
lemma `_root_.Module.Basis.baseChange_end` / 引理 `_root_.Module.Basis.baseChange_end`

English:
lemma _root_.Module.Basis.baseChange_end
  given: (b : Basis ι R M) (ij : ι × ι)
  proof: b.baseChange_linearMap A b ij

中文:
引理 _root_.Module.Basis.baseChange_end
  条件: (b : Basis ι R M) (ij : ι × ι)
  证明: b.baseChange_linearMap A b ij

Depends on / 依赖: b.baseChange_linearMap, baseChange_linearMap
-/
lemma _root_.Module.Basis.baseChange_end (b : Basis ι R M) (ij : ι × ι) :
    baseChange A (b.end ij) = (basis A b).end ij :=
  b.baseChange_linearMap A b ij

end baseChange

end Basis

/--
Instance `instFree` / 实例 `instFree`

English:
instance instFree
  signature: (R A M : Type*)
  body: Module.Free.of_basis Algebra.TensorProduct.basis A (Module.Free.chooseBasis R M)

中文:
实例 instFree
  签名: (R A M : 类型)
  定义体: Module.Free.of_basis Algebra.TensorProduct.basis A (Module.Free.chooseBasis R M)

Depends on / 依赖: Algebra, Algebra.TensorProduct.basis, Module, Module.Free.chooseBasis, Module.Free.of_basis, TensorProduct, chooseBasis, of_basis
-/
instance instFree (R A M : Type*)
    [CommSemiring R] [AddCommMonoid M] [Module R M] [Module.Free R M]
    [CommSemiring A] [Algebra R A] :
    Module.Free A (A otimes[R] M) :=
Module.Free.of_basis Algebra.TensorProduct.basis A (Module.Free.chooseBasis R M)

end TensorProduct

end Algebra

namespace LinearMap

open Algebra.TensorProduct

variable {R M₁ M₂ ι ι₂ : Type*} (A : Type*)
  [Fintype ι] [Finite ι₂] [DecidableEq ι]
  [CommSemiring R] [CommSemiring A] [Algebra R A]
  [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]

@[simp]
/--
lemma `toMatrix_baseChange` / 引理 `toMatrix_baseChange`

English:
lemma toMatrix_baseChange
  given: (f : M₁ ->ₗ[R] M₂) (b₁ : Basis ι R M₁) (b₂ : Basis ι₂ R M₂)
  proof: by
  ext; simp [toMatrix_apply]

中文:
引理 toMatrix_baseChange
  条件: (f : M₁ ->ₗ[R] M₂) (b₁ : Basis ι R M₁) (b₂ : Basis ι₂ R M₂)
  证明: by
  ext; simp [toMatrix_apply]

Depends on / 依赖: toMatrix_apply
-/
lemma toMatrix_baseChange (f : M₁ ->ₗ[R] M₂) (b₁ : Basis ι R M₁) (b₂ : Basis ι₂ R M₂) :
    toMatrix (basis A b₁) (basis A b₂) (f.baseChange A) =
    (toMatrix b₁ b₂ f).map (algebraMap R A) := by
  ext; simp [toMatrix_apply]

end LinearMap
