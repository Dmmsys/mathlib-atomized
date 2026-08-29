/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Bases and dimensionality of tensor products of modules

This file defines various bases on the tensor product of modules,
and shows that the tensor product of free modules is again free.
-/

@[expose] public section


noncomputable section

open LinearMap Module Set Submodule

open scoped TensorProduct

section CommSemiring

variable {R : Type*} {S : Type*} {M : Type*} {N : Type*} {ι : Type*} {κ : Type*}
  [CommSemiring R] [Semiring S] [Algebra R S] [AddCommMonoid M] [Module R M] [Module S M]
  [IsScalarTower R S M] [AddCommMonoid N] [Module R N]

namespace Module.Basis

/--
Definition of `tensorProduct` / `tensorProduct` 的定义

English:
definition tensorProduct
  signature: (b : Basis ι S M) (c : Basis κ R N)
  body: Finsupp.basisSingleOne.map
    ((TensorProduct.AlgebraTensorModule.congr b.repr c.repr).trans <|
(finsuppTensorFinsupp R S _ _ _ _).trans
          Finsupp.lcongr (Equiv.refl _) (TensorProduct.AlgebraTensorModule.rid R S S)).symm

@[simp]

中文:
定义 tensorProduct
  签名: (b : 基 ι S M) (c : 基 κ R N)
  定义体: Finsupp.basisSingleOne.map
    ((TensorProduct.AlgebraTensorModule.congr b.repr c.repr).trans <|
(finsuppTensorFinsupp R S _ _ _ _).trans
          Finsupp.lcongr (Equiv.refl _) (TensorProduct.AlgebraTensorModule.rid R S S)).symm

@[simp]

Depends on / 依赖: AlgebraTensorModule, Equiv.refl, Finsupp, Finsupp.basisSingleOne.map, Finsupp.lcongr, TensorProduct, TensorProduct.AlgebraTensorModule.congr, TensorProduct.AlgebraTensorModule.rid, b.repr, basisSingleOne, c.repr, finsuppTensorFinsupp, lcongr
-/
def tensorProduct (b : Basis ι S M) (c : Basis κ R N) :
    Basis (ι × κ) S (M otimes[R] N) :=
  Finsupp.basisSingleOne.map
    ((TensorProduct.AlgebraTensorModule.congr b.repr c.repr).trans <|
(finsuppTensorFinsupp R S _ _ _ _).trans
          Finsupp.lcongr (Equiv.refl _) (TensorProduct.AlgebraTensorModule.rid R S S)).symm

@[simp]
/--
theorem `tensorProduct_apply` / 定理 `tensorProduct_apply`

English:
theorem tensorProduct_apply
  given: (b : Basis ι S M) (c : Basis κ R N) (i : ι) (j : κ)
  proof: by
  simp [tensorProduct]

中文:
定理 tensorProduct_apply
  条件: (b : 基 ι S M) (c : 基 κ R N) (i : ι) (j : κ)
  证明: by
  simp [tensorProduct]

Depends on / 依赖: tensorProduct
-/
theorem tensorProduct_apply (b : Basis ι S M) (c : Basis κ R N) (i : ι) (j : κ) :
    tensorProduct b c (i, j) = b i otimesₜ c j := by
  simp [tensorProduct]

/--
theorem `tensorProduct_apply'` / 定理 `tensorProduct_apply'`

English:
theorem tensorProduct_apply'
  given: (b : Basis ι S M) (c : Basis κ R N) (i : ι × κ)
  proof: by
  simp [tensorProduct]

@[simp]

中文:
定理 tensorProduct_apply'
  条件: (b : 基 ι S M) (c : 基 κ R N) (i : ι × κ)
  证明: by
  simp [tensorProduct]

@[simp]

Depends on / 依赖: tensorProduct
-/
theorem tensorProduct_apply' (b : Basis ι S M) (c : Basis κ R N) (i : ι × κ) :
    tensorProduct b c i = b i.1 otimesₜ c i.2 := by
  simp [tensorProduct]

@[simp]
/--
theorem `tensorProduct_repr_tmul_apply` / 定理 `tensorProduct_repr_tmul_apply`

English:
theorem tensorProduct_repr_tmul_apply
  statement: (b : Basis ι S M) (c : Basis κ R N) (m : M) (n : N)
  proof: by
  simp [tensorProduct]

中文:
定理 tensorProduct_repr_tmul_apply
  结论: (b : 基 ι S M) (c : 基 κ R N) (m : M) (n : N)
  证明: by
  simp [tensorProduct]

Depends on / 依赖: tensorProduct
-/
theorem tensorProduct_repr_tmul_apply (b : Basis ι S M) (c : Basis κ R N) (m : M) (n : N)
    (i : ι) (j : κ) :
    (tensorProduct b c).repr (m otimesₜ n) (i, j) = c.repr n j • b.repr m i := by
  simp [tensorProduct]

variable (S : Type*) [Semiring S] [Algebra R S]

/-- The lift of an `R`-basis of `M` to an `S`-basis of the base change `S ⊗[R] M`. -/
noncomputable
/--
Definition of `baseChange` / `baseChange` 的定义

English:
definition baseChange
  signature: (b : Basis ι R M)
  body: (tensorProduct (.singleton Unit S) b).reindex (Equiv.punitProd ι)

@[simp]

中文:
定义 baseChange
  签名: (b : 基 ι R M)
  定义体: (tensorProduct (.singleton Unit S) b).reindex (Equiv.punitProd ι)

@[simp]

Depends on / 依赖: Equiv.punitProd, punitProd, reindex, singleton, tensorProduct
-/
def baseChange (b : Basis ι R M) : Basis ι S (S otimes[R] M) :=
  (tensorProduct (.singleton Unit S) b).reindex (Equiv.punitProd ι)

@[simp]
/--
lemma `baseChange_repr_tmul` / 引理 `baseChange_repr_tmul`

English:
lemma baseChange_repr_tmul
  given: (b : Basis ι R M) (x y i)
  proof: by
  simp [baseChange, tensorProduct]

@[simp]

中文:
引理 baseChange_repr_tmul
  条件: (b : 基 ι R M) (x y i)
  证明: by
  simp [baseChange, tensorProduct]

@[simp]

Depends on / 依赖: baseChange, tensorProduct
-/
lemma baseChange_repr_tmul (b : Basis ι R M) (x y i) :
    (b.baseChange S).repr (x otimesₜ y) i = b.repr y i • x := by
  simp [baseChange, tensorProduct]

@[simp]
/--
lemma `baseChange_apply` / 引理 `baseChange_apply`

English:
lemma baseChange_apply
  given: (b : Basis ι R M) (i)
  proof: by
  simp [baseChange, tensorProduct]

中文:
引理 baseChange_apply
  条件: (b : 基 ι R M) (i)
  证明: by
  simp [baseChange, tensorProduct]

Depends on / 依赖: baseChange, tensorProduct
-/
lemma baseChange_apply (b : Basis ι R M) (i) :
    b.baseChange S i = 1 otimesₜ b i := by
  simp [baseChange, tensorProduct]

end Module.Basis

section

variable [DecidableEq ι] [DecidableEq κ]
variable (ℬ : Basis ι R M) (𝒞 : Basis κ R N) (x : M otimes[R] N)

/--
Definition of `TensorProduct.equivFinsuppOfBasisRight` / `TensorProduct.equivFinsuppOfBasisRight` 的定义

English:
definition TensorProduct.equivFinsuppOfBasisRight
  signature: : M otimes[R] N ≃ₗ[R] κ ->₀ M
  body: LinearEquiv.lTensor M 𝒞.repr ≪≫ₗ TensorProduct.finsuppScalarRight R R M κ

@[simp]

中文:
定义 张量积.equivFinsuppOfBasisRight
  签名: : M otimes[R] N ≃ₗ[R] κ ->₀ M
  定义体: LinearEquiv.lTensor M 𝒞.repr ≪≫ₗ TensorProduct.finsuppScalarRight R R M κ

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.lTensor, TensorProduct, TensorProduct.finsuppScalarRight, finsuppScalarRight, lTensor
-/
def TensorProduct.equivFinsuppOfBasisRight : M otimes[R] N ≃ₗ[R] κ ->₀ M :=
  LinearEquiv.lTensor M 𝒞.repr ≪≫ₗ TensorProduct.finsuppScalarRight R R M κ

@[simp]
/--
lemma `TensorProduct.equivFinsuppOfBasisRight_apply_tmul` / 引理 `TensorProduct.equivFinsuppOfBasisRight_apply_tmul`

English:
lemma TensorProduct.equivFinsuppOfBasisRight_apply_tmul
  given: (m : M) (n : N)
  proof: by
  ext; simp [equivFinsuppOfBasisRight]

中文:
引理 张量积.equivFinsuppOfBasisRight_apply_tmul
  条件: (m : M) (n : N)
  证明: by
  ext; simp [equivFinsuppOfBasisRight]

Depends on / 依赖: equivFinsuppOfBasisRight
-/
lemma TensorProduct.equivFinsuppOfBasisRight_apply_tmul (m : M) (n : N) :
    (TensorProduct.equivFinsuppOfBasisRight 𝒞) (m otimesₜ n) =
    (𝒞.repr n).mapRange (· • m) (zero_smul _ _) := by
  ext; simp [equivFinsuppOfBasisRight]

/--
lemma `TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply` / 引理 `TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply`

English:
lemma TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply
  proof: by
  simp only [equivFinsuppOfBasisRight_apply_tmul, Finsupp.mapRange_apply]

中文:
引理 张量积.equivFinsuppOfBasisRight_apply_tmul_apply
  证明: by
  simp only [equivFinsuppOfBasisRight_apply_tmul, Finsupp.mapRange_apply]

Depends on / 依赖: Finsupp, Finsupp.mapRange_apply, equivFinsuppOfBasisRight_apply_tmul, mapRange_apply
-/
lemma TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply
    (m : M) (n : N) (i : κ) :
    (TensorProduct.equivFinsuppOfBasisRight 𝒞) (m otimesₜ n) i =
    𝒞.repr n i • m := by
  simp only [equivFinsuppOfBasisRight_apply_tmul, Finsupp.mapRange_apply]

/--
lemma `TensorProduct.equivFinsuppOfBasisRight_symm` / 引理 `TensorProduct.equivFinsuppOfBasisRight_symm`

English:
lemma TensorProduct.equivFinsuppOfBasisRight_symm
  proof: by
  ext; simp [equivFinsuppOfBasisRight]

@[simp]

中文:
引理 张量积.equivFinsuppOfBasisRight_symm
  证明: by
  ext; simp [equivFinsuppOfBasisRight]

@[simp]

Depends on / 依赖: equivFinsuppOfBasisRight
-/
lemma TensorProduct.equivFinsuppOfBasisRight_symm :
    (TensorProduct.equivFinsuppOfBasisRight 𝒞).symm.toLinearMap =
    Finsupp.lsum R fun i => (TensorProduct.mk R M N).flip (𝒞 i) := by
  ext; simp [equivFinsuppOfBasisRight]

@[simp]
/--
lemma `TensorProduct.equivFinsuppOfBasisRight_symm_apply` / 引理 `TensorProduct.equivFinsuppOfBasisRight_symm_apply`

English:
lemma TensorProduct.equivFinsuppOfBasisRight_symm_apply
  given: (b : κ ->₀ M)
  proof: congr($(TensorProduct.equivFinsuppOfBasisRight_symm 𝒞) b)

omit [DecidableEq κ] in

中文:
引理 张量积.equivFinsuppOfBasisRight_symm_apply
  条件: (b : κ ->₀ M)
  证明: congr($(TensorProduct.equivFinsuppOfBasisRight_symm 𝒞) b)

omit [DecidableEq κ] in

Depends on / 依赖: TensorProduct, TensorProduct.equivFinsuppOfBasisRight_symm, equivFinsuppOfBasisRight_symm
-/
lemma TensorProduct.equivFinsuppOfBasisRight_symm_apply (b : κ ->₀ M) :
    (TensorProduct.equivFinsuppOfBasisRight 𝒞).symm b = b.sum fun i m => m otimesₜ 𝒞 i :=
  congr($(TensorProduct.equivFinsuppOfBasisRight_symm 𝒞) b)

omit [DecidableEq κ] in
/--
lemma `TensorProduct.sum_tmul_basis_right_injective` / 引理 `TensorProduct.sum_tmul_basis_right_injective`

English:
lemma TensorProduct.sum_tmul_basis_right_injective
  proof: have := Classical.decEq κ
  (equivFinsuppOfBasisRight_symm (M := M) 𝒞).symm ▸
    (TensorProduct.equivFinsuppOfBasisRight 𝒞).symm.injective

omit [DecidableEq κ] in

中文:
引理 张量积.sum_tmul_basis_right_injective
  证明: have := Classical.decEq κ
  (equivFinsuppOfBasisRight_symm (M := M) 𝒞).symm ▸
    (TensorProduct.equivFinsuppOfBasisRight 𝒞).symm.injective

omit [DecidableEq κ] in

Depends on / 依赖: Classical, Classical.decEq, TensorProduct, TensorProduct.equivFinsuppOfBasisRight, equivFinsuppOfBasisRight, equivFinsuppOfBasisRight_symm, injective, symm.injective
-/
lemma TensorProduct.sum_tmul_basis_right_injective :
    Function.Injective (Finsupp.lsum R fun i => (TensorProduct.mk R M N).flip (𝒞 i)) :=
  have := Classical.decEq κ
  (equivFinsuppOfBasisRight_symm (M := M) 𝒞).symm ▸
    (TensorProduct.equivFinsuppOfBasisRight 𝒞).symm.injective

omit [DecidableEq κ] in
/--
lemma `TensorProduct.sum_tmul_basis_right_eq_zero` / 引理 `TensorProduct.sum_tmul_basis_right_eq_zero`

English:
lemma TensorProduct.sum_tmul_basis_right_eq_zero
  proof: have := Classical.decEq κ
(TensorProduct.equivFinsuppOfBasisRight 𝒞).symm.injective (a₂ := 0) by simpa

中文:
引理 张量积.sum_tmul_basis_right_eq_zero
  证明: have := Classical.decEq κ
(TensorProduct.equivFinsuppOfBasisRight 𝒞).symm.injective (a₂ := 0) by simpa

Depends on / 依赖: Classical, Classical.decEq, TensorProduct, TensorProduct.equivFinsuppOfBasisRight, equivFinsuppOfBasisRight, injective, symm.injective
-/
lemma TensorProduct.sum_tmul_basis_right_eq_zero
    (b : κ ->₀ M) (h : (b.sum fun i m => m otimesₜ[R] 𝒞 i) = 0) : b = 0 :=
  have := Classical.decEq κ
(TensorProduct.equivFinsuppOfBasisRight 𝒞).symm.injective (a₂ := 0) by simpa

/--
Definition of `TensorProduct.equivFinsuppOfBasisLeft` / `TensorProduct.equivFinsuppOfBasisLeft` 的定义

English:
definition TensorProduct.equivFinsuppOfBasisLeft
  signature: : M otimes[R] N ≃ₗ[R] ι ->₀ N
  body: TensorProduct.comm R M N ≪≫ₗ TensorProduct.equivFinsuppOfBasisRight ℬ

@[simp]

中文:
定义 张量积.equivFinsuppOfBasisLeft
  签名: : M otimes[R] N ≃ₗ[R] ι ->₀ N
  定义体: TensorProduct.comm R M N ≪≫ₗ TensorProduct.equivFinsuppOfBasisRight ℬ

@[simp]

Depends on / 依赖: TensorProduct, TensorProduct.comm, TensorProduct.equivFinsuppOfBasisRight, equivFinsuppOfBasisRight
-/
def TensorProduct.equivFinsuppOfBasisLeft : M otimes[R] N ≃ₗ[R] ι ->₀ N :=
  TensorProduct.comm R M N ≪≫ₗ TensorProduct.equivFinsuppOfBasisRight ℬ

@[simp]
/--
lemma `TensorProduct.equivFinsuppOfBasisLeft_apply_tmul` / 引理 `TensorProduct.equivFinsuppOfBasisLeft_apply_tmul`

English:
lemma TensorProduct.equivFinsuppOfBasisLeft_apply_tmul
  given: (m : M) (n : N)
  proof: by
  simp [equivFinsuppOfBasisLeft]

中文:
引理 张量积.equivFinsuppOfBasisLeft_apply_tmul
  条件: (m : M) (n : N)
  证明: by
  simp [equivFinsuppOfBasisLeft]

Depends on / 依赖: equivFinsuppOfBasisLeft
-/
lemma TensorProduct.equivFinsuppOfBasisLeft_apply_tmul (m : M) (n : N) :
    (TensorProduct.equivFinsuppOfBasisLeft ℬ) (m otimesₜ n) =
    (ℬ.repr m).mapRange (· • n) (zero_smul _ _) := by
  simp [equivFinsuppOfBasisLeft]

/--
lemma `TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply` / 引理 `TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply`

English:
lemma TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply
  proof: by
  simp only [equivFinsuppOfBasisLeft_apply_tmul, Finsupp.mapRange_apply]

中文:
引理 张量积.equivFinsuppOfBasisLeft_apply_tmul_apply
  证明: by
  simp only [equivFinsuppOfBasisLeft_apply_tmul, Finsupp.mapRange_apply]

Depends on / 依赖: Finsupp, Finsupp.mapRange_apply, equivFinsuppOfBasisLeft_apply_tmul, mapRange_apply
-/
lemma TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply
    (m : M) (n : N) (i : ι) :
    (TensorProduct.equivFinsuppOfBasisLeft ℬ) (m otimesₜ n) i =
    ℬ.repr m i • n := by
  simp only [equivFinsuppOfBasisLeft_apply_tmul, Finsupp.mapRange_apply]

/--
lemma `TensorProduct.equivFinsuppOfBasisRight_apply` / 引理 `TensorProduct.equivFinsuppOfBasisRight_apply`

English:
lemma TensorProduct.equivFinsuppOfBasisRight_apply
  given: (x : M otimes[R] N) (i : κ)
  proof: by
  induction x <;> simp_all

中文:
引理 张量积.equivFinsuppOfBasisRight_apply
  条件: (x : M otimes[R] N) (i : κ)
  证明: by
  induction x <;> simp_all
-/
lemma TensorProduct.equivFinsuppOfBasisRight_apply (x : M otimes[R] N) (i : κ) :
    equivFinsuppOfBasisRight 𝒞 x i = TensorProduct.rid R M ((𝒞.coord i).lTensor _ x) := by
  induction x <;> simp_all

/--
lemma `TensorProduct.equivFinsuppOfBasisLeft_apply` / 引理 `TensorProduct.equivFinsuppOfBasisLeft_apply`

English:
lemma TensorProduct.equivFinsuppOfBasisLeft_apply
  given: (x : M otimes[R] N) (i : ι)
  proof: by
  induction x <;> simp_all

中文:
引理 张量积.equivFinsuppOfBasisLeft_apply
  条件: (x : M otimes[R] N) (i : ι)
  证明: by
  induction x <;> simp_all
-/
lemma TensorProduct.equivFinsuppOfBasisLeft_apply (x : M otimes[R] N) (i : ι) :
    equivFinsuppOfBasisLeft ℬ x i = TensorProduct.lid R N ((ℬ.coord i).rTensor _ x) := by
  induction x <;> simp_all

/--
lemma `TensorProduct.equivFinsuppOfBasisLeft_symm` / 引理 `TensorProduct.equivFinsuppOfBasisLeft_symm`

English:
lemma TensorProduct.equivFinsuppOfBasisLeft_symm
  proof: by
  ext; simp [equivFinsuppOfBasisLeft]

@[simp]

中文:
引理 张量积.equivFinsuppOfBasisLeft_symm
  证明: by
  ext; simp [equivFinsuppOfBasisLeft]

@[simp]

Depends on / 依赖: equivFinsuppOfBasisLeft
-/
lemma TensorProduct.equivFinsuppOfBasisLeft_symm :
    (TensorProduct.equivFinsuppOfBasisLeft ℬ).symm.toLinearMap =
    Finsupp.lsum R fun i => (TensorProduct.mk R M N) (ℬ i) := by
  ext; simp [equivFinsuppOfBasisLeft]

@[simp]
/--
lemma `TensorProduct.equivFinsuppOfBasisLeft_symm_apply` / 引理 `TensorProduct.equivFinsuppOfBasisLeft_symm_apply`

English:
lemma TensorProduct.equivFinsuppOfBasisLeft_symm_apply
  given: (b : ι ->₀ N)
  proof: congr($(TensorProduct.equivFinsuppOfBasisLeft_symm ℬ) b)

omit [DecidableEq κ] in

中文:
引理 张量积.equivFinsuppOfBasisLeft_symm_apply
  条件: (b : ι ->₀ N)
  证明: congr($(TensorProduct.equivFinsuppOfBasisLeft_symm ℬ) b)

omit [DecidableEq κ] in

Depends on / 依赖: TensorProduct, TensorProduct.equivFinsuppOfBasisLeft_symm, equivFinsuppOfBasisLeft_symm
-/
lemma TensorProduct.equivFinsuppOfBasisLeft_symm_apply (b : ι ->₀ N) :
    (TensorProduct.equivFinsuppOfBasisLeft ℬ).symm b = b.sum fun i n => ℬ i otimesₜ n :=
  congr($(TensorProduct.equivFinsuppOfBasisLeft_symm ℬ) b)

omit [DecidableEq κ] in
/--
lemma `TensorProduct.eq_repr_basis_right` / 引理 `TensorProduct.eq_repr_basis_right`

English:
lemma TensorProduct.eq_repr_basis_right
  proof: by
  classical simpa using (TensorProduct.equivFinsuppOfBasisRight 𝒞).symm.surjective x

omit [DecidableEq ι] in

中文:
引理 张量积.eq_repr_basis_right
  证明: by
  classical simpa using (TensorProduct.equivFinsuppOfBasisRight 𝒞).symm.surjective x

omit [DecidableEq ι] in

Depends on / 依赖: TensorProduct, TensorProduct.equivFinsuppOfBasisRight, classical, equivFinsuppOfBasisRight, surjective, symm.surjective
-/
lemma TensorProduct.eq_repr_basis_right :
    exists b : κ ->₀ M, b.sum (fun i m => m otimesₜ 𝒞 i) = x := by
  classical simpa using (TensorProduct.equivFinsuppOfBasisRight 𝒞).symm.surjective x

omit [DecidableEq ι] in
/--
lemma `TensorProduct.eq_repr_basis_left` / 引理 `TensorProduct.eq_repr_basis_left`

English:
lemma TensorProduct.eq_repr_basis_left
  proof: by
  classical obtain ⟨c, rfl⟩ := (TensorProduct.equivFinsuppOfBasisLeft ℬ).symm.surjective x
exact ⟨c, (TensorProduct.comm R M N).injective by simp [Finsupp.sum]⟩

omit [DecidableEq ι] in

中文:
引理 张量积.eq_repr_basis_left
  证明: by
  classical obtain ⟨c, rfl⟩ := (TensorProduct.equivFinsuppOfBasisLeft ℬ).symm.surjective x
exact ⟨c, (TensorProduct.comm R M N).injective by simp [Finsupp.sum]⟩

omit [DecidableEq ι] in

Depends on / 依赖: Finsupp, Finsupp.sum, TensorProduct, TensorProduct.comm, TensorProduct.equivFinsuppOfBasisLeft, classical, equivFinsuppOfBasisLeft, injective, surjective, symm.surjective
-/
lemma TensorProduct.eq_repr_basis_left :
    exists (c : ι ->₀ N), (c.sum fun i n => ℬ i otimesₜ n) = x := by
  classical obtain ⟨c, rfl⟩ := (TensorProduct.equivFinsuppOfBasisLeft ℬ).symm.surjective x
exact ⟨c, (TensorProduct.comm R M N).injective by simp [Finsupp.sum]⟩

omit [DecidableEq ι] in
/--
lemma `TensorProduct.sum_tmul_basis_left_injective` / 引理 `TensorProduct.sum_tmul_basis_left_injective`

English:
lemma TensorProduct.sum_tmul_basis_left_injective
  proof: have := Classical.decEq ι
  (equivFinsuppOfBasisLeft_symm (N := N) ℬ).symm ▸
    (TensorProduct.equivFinsuppOfBasisLeft ℬ).symm.injective

omit [DecidableEq ι] in

中文:
引理 张量积.sum_tmul_basis_left_injective
  证明: have := Classical.decEq ι
  (equivFinsuppOfBasisLeft_symm (N := N) ℬ).symm ▸
    (TensorProduct.equivFinsuppOfBasisLeft ℬ).symm.injective

omit [DecidableEq ι] in

Depends on / 依赖: Classical, Classical.decEq, TensorProduct, TensorProduct.equivFinsuppOfBasisLeft, equivFinsuppOfBasisLeft, equivFinsuppOfBasisLeft_symm, injective, symm.injective
-/
lemma TensorProduct.sum_tmul_basis_left_injective :
    Function.Injective (Finsupp.lsum R fun i => (TensorProduct.mk R M N) (ℬ i)) :=
  have := Classical.decEq ι
  (equivFinsuppOfBasisLeft_symm (N := N) ℬ).symm ▸
    (TensorProduct.equivFinsuppOfBasisLeft ℬ).symm.injective

omit [DecidableEq ι] in
/--
lemma `TensorProduct.sum_tmul_basis_left_eq_zero` / 引理 `TensorProduct.sum_tmul_basis_left_eq_zero`

English:
lemma TensorProduct.sum_tmul_basis_left_eq_zero
  proof: have := Classical.decEq ι
(TensorProduct.equivFinsuppOfBasisLeft ℬ).symm.injective (a₂ := 0) by simpa

中文:
引理 张量积.sum_tmul_basis_left_eq_zero
  证明: have := Classical.decEq ι
(TensorProduct.equivFinsuppOfBasisLeft ℬ).symm.injective (a₂ := 0) by simpa

Depends on / 依赖: Classical, Classical.decEq, TensorProduct, TensorProduct.equivFinsuppOfBasisLeft, equivFinsuppOfBasisLeft, injective, symm.injective
-/
lemma TensorProduct.sum_tmul_basis_left_eq_zero
    (b : ι ->₀ N) (h : (b.sum fun i n => ℬ i otimesₜ[R] n) = 0) : b = 0 :=
  have := Classical.decEq ι
(TensorProduct.equivFinsuppOfBasisLeft ℬ).symm.injective (a₂ := 0) by simpa

end

/--
Instance `Module.Free.tensor` / 实例 `Module.Free.tensor`

English:
instance Module.Free.tensor
  signature: [Module.Free S M] [Module.Free R N]
  body: let ⟨bM⟩ := exists_basis (R := S) (M := M)
  let ⟨bN⟩ := exists_basis (R := R) (M := N)
  of_basis (bM.2.tensorProduct bN.2)

中文:
实例 模.自由.tensor
  签名: [模.自由 S M] [模.自由 R N]
  定义体: let ⟨bM⟩ := exists_basis (R := S) (M := M)
  let ⟨bN⟩ := exists_basis (R := R) (M := N)
  of_basis (bM.2.tensorProduct bN.2)

Depends on / 依赖: exists_basis, of_basis, tensorProduct
-/
instance Module.Free.tensor [Module.Free S M] [Module.Free R N] : Module.Free S (M otimes[R] N) :=
  let ⟨bM⟩ := exists_basis (R := S) (M := M)
  let ⟨bN⟩ := exists_basis (R := R) (M := N)
  of_basis (bM.2.tensorProduct bN.2)

end CommSemiring

end
