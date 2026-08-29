/-
Copyright (c) 2025 Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Mrugała
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.RingTheory.IsTensorProduct

/-!
# Monoid algebras commute with base change

In this file we show that monoid algebras are stable under pushout.
-/

@[expose] public noncomputable section

open Algebra TensorProduct

namespace MonoidAlgebra
variable {R M N S A B : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring A] [CommSemiring B]
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra S A] [IsScalarTower R S A]
  [CommMonoid M] [CommMonoid N]

-- Note: Cannot be additivised automatically because of the use of `Multiplicative`
-- in `AddMonoidAlgebra.liftNCAlgHom` and `of`
/--
Definition of `_root_.AddMonoidAlgebra.rTensorEquivAlgEquiv.invFun` / `_root_.AddMonoidAlgebra.rTensorEquivAlgEquiv.invFun` 的定义

English:
definition _root_.AddMonoidAlgebra.rTensorEquivAlgEquiv.invFun
  signature: [AddCommMonoid M]
  body: AddMonoidAlgebra.liftNCAlgHom
    (Algebra.TensorProduct.map (.id _ _) AddMonoidAlgebra.singleZeroAlgHom)
    (Algebra.TensorProduct.includeRight.toMonoidHom.comp <| AddMonoidAlgebra.of B M)
      fun _ _ => .all ..

中文:
定义 _root_.AddMonoidAlgebra.rTensorEquivAlgEquiv.invFun
  签名: [AddCommMonoid M]
  定义体: AddMonoidAlgebra.liftNCAlgHom
    (Algebra.TensorProduct.map (.id _ _) AddMonoidAlgebra.singleZeroAlgHom)
    (Algebra.TensorProduct.includeRight.toMonoidHom.comp <| AddMonoidAlgebra.of B M)
      fun _ _ => .all ..

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.liftNCAlgHom, AddMonoidAlgebra.of, AddMonoidAlgebra.singleZeroAlgHom, Algebra, Algebra.TensorProduct.includeRight.toMonoidHom.comp, Algebra.TensorProduct.map, TensorProduct, includeRight, liftNCAlgHom, singleZeroAlgHom, toMonoidHom
-/
noncomputable def _root_.AddMonoidAlgebra.rTensorEquivAlgEquiv.invFun [AddCommMonoid M] :
    AddMonoidAlgebra (A otimes[R] B) M ->ₐ[S] A otimes[R] AddMonoidAlgebra B M :=
  AddMonoidAlgebra.liftNCAlgHom
    (Algebra.TensorProduct.map (.id _ _) AddMonoidAlgebra.singleZeroAlgHom)
    (Algebra.TensorProduct.includeRight.toMonoidHom.comp <| AddMonoidAlgebra.of B M)
      fun _ _ => .all ..

/-- Implementation detail. -/
@[to_additive existing (dont_translate := R)]
/--
Definition of `rTensorEquivAlgEquiv.invFun` / `rTensorEquivAlgEquiv.invFun` 的定义

English:
definition rTensorEquivAlgEquiv.invFun
  signature: : (A otimes[R] B)[M] ->ₐ[S] A otimes[R] B[M]
  body: MonoidAlgebra.liftNCAlgHom (Algebra.TensorProduct.map (.id _ _) singleOneAlgHom)
    (Algebra.TensorProduct.includeRight.toMonoidHom.comp (of B M)) fun _ _ => .all ..

omit [CommMonoid M] in

中文:
定义 rTensorEquivAlgEquiv.invFun
  签名: : (A otimes[R] B)[M] ->ₐ[S] A otimes[R] B[M]
  定义体: MonoidAlgebra.liftNCAlgHom (Algebra.TensorProduct.map (.id _ _) singleOneAlgHom)
    (Algebra.TensorProduct.includeRight.toMonoidHom.comp (of B M)) fun _ _ => .all ..

omit [CommMonoid M] in

Depends on / 依赖: Algebra, Algebra.TensorProduct.includeRight.toMonoidHom.comp, Algebra.TensorProduct.map, MonoidAlgebra, MonoidAlgebra.liftNCAlgHom, TensorProduct, includeRight, liftNCAlgHom, singleOneAlgHom, toMonoidHom
-/
def rTensorEquivAlgEquiv.invFun : (A otimes[R] B)[M] ->ₐ[S] A otimes[R] B[M] :=
  MonoidAlgebra.liftNCAlgHom (Algebra.TensorProduct.map (.id _ _) singleOneAlgHom)
    (Algebra.TensorProduct.includeRight.toMonoidHom.comp (of B M)) fun _ _ => .all ..

omit [CommMonoid M] in
variable (R A B) [AddCommMonoid M] in
/--
lemma `_root_.AddMonoidAlgebra.rTensorEquivAlgEquiv.invFun_tmul` / 引理 `_root_.AddMonoidAlgebra.rTensorEquivAlgEquiv.invFun_tmul`

English:
lemma _root_.AddMonoidAlgebra.rTensorEquivAlgEquiv.invFun_tmul
  given: (a : A) (m : M) (b : B)
  proof: by
  simp [AddMonoidAlgebra.rTensorEquivAlgEquiv.invFun]

@[to_additive existing (dont_translate := R) (attr := simp)]

中文:
引理 _root_.AddMonoidAlgebra.rTensorEquivAlgEquiv.invFun_tmul
  条件: (a : A) (m : M) (b : B)
  证明: by
  simp [AddMonoidAlgebra.rTensorEquivAlgEquiv.invFun]

@[to_additive existing (dont_translate := R) (attr := simp)]

Depends on / 依赖: single
-/
lemma _root_.AddMonoidAlgebra.rTensorEquivAlgEquiv.invFun_tmul (a : A) (m : M) (b : B) :
    AddMonoidAlgebra.rTensorEquivAlgEquiv.invFun (S := S) (.single m (a otimesₜ[R] b)) =
       a otimesₜ .single m b := by
  simp [AddMonoidAlgebra.rTensorEquivAlgEquiv.invFun]

@[to_additive existing (dont_translate := R) (attr := simp)]
/--
lemma `rTensorEquivAlgEquiv.invFun_tmul` / 引理 `rTensorEquivAlgEquiv.invFun_tmul`

English:
lemma rTensorEquivAlgEquiv.invFun_tmul
  given: (a : A) (m : M) (b : B)
  proof: by
  simp [rTensorEquivAlgEquiv.invFun]

中文:
引理 rTensorEquivAlgEquiv.invFun_tmul
  条件: (a : A) (m : M) (b : B)
  证明: by
  simp [rTensorEquivAlgEquiv.invFun]

Depends on / 依赖: invFun, rTensorEquivAlgEquiv, rTensorEquivAlgEquiv.invFun, single
-/
lemma rTensorEquivAlgEquiv.invFun_tmul (a : A) (m : M) (b : B) :
    rTensorEquivAlgEquiv.invFun (S := S) (single m (a otimesₜ[R] b)) = a otimesₜ single m b := by
  simp [rTensorEquivAlgEquiv.invFun]

variable (R S A B) in
/-- The base change of `B[M]` to an `R`-algebra `A` is isomorphic to `(A ⊗[R] B)[M]`
as an `A`-algebra. -/
@[to_additive (dont_translate := R S A B)
/-- The base change of `B[M]` to an `R`-algebra `A` is isomorphic to `(A ⊗[R] B)[M]`
as an `A`-algebra. -/]
/--
Definition of `rTensorEquivAlgEquiv` / `rTensorEquivAlgEquiv` 的定义

English:
definition rTensorEquivAlgEquiv
  signature: : A otimes[R] B[M] ≃ₐ[S] (A otimes[R] B)[M]
  body: by
refine .restrictScalars S .ofAlgHom
    (Algebra.TensorProduct.lift
      ((IsScalarTower.toAlgHom A (A otimes[R] B) _).comp Algebra.TensorProduct.includeLeft)
      (mapAlgHom _ Algebra.TensorProduct.includeRight) fun p n => .all ..)
      rTensorEquivAlgEquiv.invFun ?_ ?_
  · apply AlgHom.toLin

中文:
定义 rTensorEquivAlgEquiv
  签名: : A otimes[R] B[M] ≃ₐ[S] (A otimes[R] B)[M]
  定义体: by
refine .restrictScalars S .ofAlgHom
    (Algebra.TensorProduct.lift
      ((IsScalarTower.toAlgHom A (A otimes[R] B) _).comp Algebra.TensorProduct.includeLeft)
      (mapAlgHom _ Algebra.TensorProduct.includeRight) fun p n => .all ..)
      rTensorEquivAlgEquiv.invFun ?_ ?_
  · apply AlgHom.toLin

Depends on / 依赖: AlgHom, AlgHom.toLinearMap_injective, Algebra, Algebra.TensorProduct.includeLeft, Algebra.TensorProduct.includeRight, Algebra.TensorProduct.lift, IsScalarTower, IsScalarTower.toAlgHom, TensorProduct, includeLeft, includeRight, invFun, mapAlgHom, ofAlgHom, otimes, rTensorEquivAlgEquiv, rTensorEquivAlgEquiv.invFun, restrictScalars, toAlgHom, toLinearMap_injective
-/
noncomputable def rTensorEquivAlgEquiv : A otimes[R] B[M] ≃ₐ[S] (A otimes[R] B)[M] := by
refine .restrictScalars S .ofAlgHom
    (Algebra.TensorProduct.lift
      ((IsScalarTower.toAlgHom A (A otimes[R] B) _).comp Algebra.TensorProduct.includeLeft)
      (mapAlgHom _ Algebra.TensorProduct.includeRight) fun p n => .all ..)
      rTensorEquivAlgEquiv.invFun ?_ ?_
  · apply AlgHom.toLinearMap_injective
    ext
    simp
  · ext : 1
    apply AlgHom.toLinearMap_injective
    ext
    simp

@[to_additive (dont_translate := R A B) (attr := simp)]
/--
lemma `rTensorEquiv_tmulAlgEquiv` / 引理 `rTensorEquiv_tmulAlgEquiv`

English:
lemma rTensorEquiv_tmulAlgEquiv
  given: (a : A) (p : B[M])
  proof: by
  simp [rTensorEquivAlgEquiv, Algebra.smul_def]

@[to_additive (dont_translate := R A B) (attr := simp)]

中文:
引理 rTensorEquiv_tmulAlgEquiv
  条件: (a : A) (p : B[M])
  证明: by
  simp [rTensorEquivAlgEquiv, Algebra.smul_def]

@[to_additive (dont_translate := R A B) (attr := simp)]

Depends on / 依赖: Algebra, Algebra.smul_def, rTensorEquivAlgEquiv, smul_def
-/
lemma rTensorEquiv_tmulAlgEquiv (a : A) (p : B[M]) :
    rTensorEquivAlgEquiv R S A B (a otimesₜ p) =
      a • mapAlgHom M Algebra.TensorProduct.includeRight p := by
  simp [rTensorEquivAlgEquiv, Algebra.smul_def]

@[to_additive (dont_translate := R A B) (attr := simp)]
/--
lemma `rTensorEquiv_symm_singleAlgEquiv` / 引理 `rTensorEquiv_symm_singleAlgEquiv`

English:
lemma rTensorEquiv_symm_singleAlgEquiv
  given: (m : M) (a : A) (b : B)
  proof: rTensorEquivAlgEquiv.invFun_tmul ..

中文:
引理 rTensorEquiv_symm_singleAlgEquiv
  条件: (m : M) (a : A) (b : B)
  证明: rTensorEquivAlgEquiv.invFun_tmul ..

Depends on / 依赖: invFun_tmul, rTensorEquivAlgEquiv, rTensorEquivAlgEquiv.invFun_tmul
-/
lemma rTensorEquiv_symm_singleAlgEquiv (m : M) (a : A) (b : B) :
    (rTensorEquivAlgEquiv R S A B).symm (single m (a otimesₜ b)) = a otimesₜ single m b :=
  rTensorEquivAlgEquiv.invFun_tmul ..

variable (R A B) in
/-- The base change of `B[M]` to an `R`-algebra `A` is isomorphic to `(A ⊗[R] B)[M]`
as an `A`-algebra. -/
@[to_additive (dont_translate := R A B)
/-- The base change of `B[M]` to an `R`-algebra `A` is isomorphic to `(A ⊗[R] B)[M]`
as an `A`-algebra. -/]
/--
Definition of `lTensorAlgEquiv` / `lTensorAlgEquiv` 的定义

English:
definition lTensorAlgEquiv
  signature: : A[M] otimes[R] B ≃ₐ[R] (A otimes[R] B)[M]
  body: (Algebra.TensorProduct.comm ..).trans (rTensorEquivAlgEquiv _ _ _ _).trans
mapAlgEquiv _ _ Algebra.TensorProduct.comm ..

@[to_additive (dont_translate := R A B) (attr := simp)]

中文:
定义 lTensorAlgEquiv
  签名: : A[M] otimes[R] B ≃ₐ[R] (A otimes[R] B)[M]
  定义体: (Algebra.TensorProduct.comm ..).trans (rTensorEquivAlgEquiv _ _ _ _).trans
mapAlgEquiv _ _ Algebra.TensorProduct.comm ..

@[to_additive (dont_translate := R A B) (attr := simp)]

Depends on / 依赖: Algebra, Algebra.TensorProduct.comm, TensorProduct, mapAlgEquiv, rTensorEquivAlgEquiv
-/
noncomputable def lTensorAlgEquiv : A[M] otimes[R] B ≃ₐ[R] (A otimes[R] B)[M] :=
(Algebra.TensorProduct.comm ..).trans (rTensorEquivAlgEquiv _ _ _ _).trans
mapAlgEquiv _ _ Algebra.TensorProduct.comm ..

@[to_additive (dont_translate := R A B) (attr := simp)]
/--
lemma `lTensorAlgEquiv_symm_single` / 引理 `lTensorAlgEquiv_symm_single`

English:
lemma lTensorAlgEquiv_symm_single
  given: (m : M) (a : A) (b : B)
  proof: by
  simp [lTensorAlgEquiv]

中文:
引理 lTensorAlgEquiv_symm_single
  条件: (m : M) (a : A) (b : B)
  证明: by
  simp [lTensorAlgEquiv]

Depends on / 依赖: lTensorAlgEquiv
-/
lemma lTensorAlgEquiv_symm_single (m : M) (a : A) (b : B) :
    (lTensorAlgEquiv R A B).symm (single m (a otimesₜ b)) = single m a otimesₜ b := by
  simp [lTensorAlgEquiv]

variable (R A) in
/-- The base change of `R[M]` to an `R`-algebra `A` is isomorphic to `A[M]` as an `A`-algebra. -/
@[to_additive (dont_translate := R A)
/-- The base change of `R[M]` to an `R`-algebra `A` is isomorphic to `A[M]` as an `A`-algebra. -/]
/--
Definition of `scalarTensorEquiv` / `scalarTensorEquiv` 的定义

English:
definition scalarTensorEquiv
  signature: : A otimes[R] R[M] ≃ₐ[A] A[M]
  body: (rTensorEquivAlgEquiv ..).trans mapAlgEquiv A M Algebra.TensorProduct.rid R A A

@[to_additive (dont_translate := R A) (attr := simp)]

中文:
定义 scalarTensorEquiv
  签名: : A otimes[R] R[M] ≃ₐ[A] A[M]
  定义体: (rTensorEquivAlgEquiv ..).trans mapAlgEquiv A M Algebra.TensorProduct.rid R A A

@[to_additive (dont_translate := R A) (attr := simp)]

Depends on / 依赖: Algebra, Algebra.TensorProduct.rid, TensorProduct, mapAlgEquiv, rTensorEquivAlgEquiv
-/
noncomputable def scalarTensorEquiv : A otimes[R] R[M] ≃ₐ[A] A[M] :=
(rTensorEquivAlgEquiv ..).trans mapAlgEquiv A M Algebra.TensorProduct.rid R A A

@[to_additive (dont_translate := R A) (attr := simp)]
/--
lemma `scalarTensorEquiv_tmul` / 引理 `scalarTensorEquiv_tmul`

English:
lemma scalarTensorEquiv_tmul
  given: (a : A) (p : R[M])
  proof: by
  ext; simp [scalarTensorEquiv]; simp [Algebra.smul_def, Algebra.commutes]

@[to_additive (dont_translate := R A) (attr := simp)]

中文:
引理 scalarTensorEquiv_tmul
  条件: (a : A) (p : R[M])
  证明: by
  ext; simp [scalarTensorEquiv]; simp [Algebra.smul_def, Algebra.commutes]

@[to_additive (dont_translate := R A) (attr := simp)]

Depends on / 依赖: Algebra, Algebra.commutes, Algebra.smul_def, commutes, scalarTensorEquiv, smul_def
-/
lemma scalarTensorEquiv_tmul (a : A) (p : R[M]) :
    scalarTensorEquiv R A (a otimesₜ p) = a • mapAlgHom M (Algebra.ofId ..) p := by
  ext; simp [scalarTensorEquiv]; simp [Algebra.smul_def, Algebra.commutes]

@[to_additive (dont_translate := R A) (attr := simp)]
/--
lemma `scalarTensorEquiv_symm_single` / 引理 `scalarTensorEquiv_symm_single`

English:
lemma scalarTensorEquiv_symm_single
  given: (m : M) (a : A)
  proof: by simp [scalarTensorEquiv]

中文:
引理 scalarTensorEquiv_symm_single
  条件: (m : M) (a : A)
  证明: by simp [scalarTensorEquiv]

Depends on / 依赖: scalarTensorEquiv
-/
lemma scalarTensorEquiv_symm_single (m : M) (a : A) :
    (scalarTensorEquiv R A).symm (single m a) = a otimesₜ single m 1 := by simp [scalarTensorEquiv]

open scoped AlgebraMonoidAlgebra

variable [Algebra S B] [Algebra A B] [IsScalarTower R A B] [IsScalarTower R S B]

@[to_additive (dont_translate := R S B)]
/--
Instance `instIsPushout` / 实例 `instIsPushout`

English:
instance instIsPushout
  signature: [IsPushout R S A B]
  body: .of_equiv ((rTensorEquivAlgEquiv R S S A (M := M)).trans <|
mapAlgEquiv S M IsPushout.equiv R S A B).toLinearEquiv fun x => by
    induction x using induction_linear <;> simp_all [IsPushout.equiv_tmul]

@[to_additive (dont_translate := R)]

中文:
实例 instIsPushout
  签名: [IsPushout R S A B]
  定义体: .of_equiv ((rTensorEquivAlgEquiv R S S A (M := M)).trans <|
mapAlgEquiv S M IsPushout.equiv R S A B).toLinearEquiv fun x => by
    induction x using induction_linear <;> simp_all [IsPushout.equiv_tmul]

@[to_additive (dont_translate := R)]

Depends on / 依赖: of_equiv, rTensorEquivAlgEquiv
-/
instance instIsPushout [IsPushout R S A B] : IsPushout R S A[M] B[M] where
  out := .of_equiv ((rTensorEquivAlgEquiv R S S A (M := M)).trans <|
mapAlgEquiv S M IsPushout.equiv R S A B).toLinearEquiv fun x => by
    induction x using induction_linear <;> simp_all [IsPushout.equiv_tmul]

@[to_additive (dont_translate := R)]
/--
Instance `instIsPushout'` / 实例 `instIsPushout'`

English:
instance instIsPushout'
  signature: [IsPushout R A S B]
  body: have : IsPushout R S A B := .symm ‹_›; .symm inferInstance

omit [CommMonoid M] [CommMonoid N]

中文:
实例 instIsPushout'
  签名: [IsPushout R A S B]
  定义体: have : IsPushout R S A B := .symm ‹_›; .symm inferInstance

omit [CommMonoid M] [CommMonoid N]

Depends on / 依赖: IsPushout
-/
instance instIsPushout' [IsPushout R A S B] : IsPushout R A[M] S B[M] :=
  have : IsPushout R S A B := .symm ‹_›; .symm inferInstance

omit [CommMonoid M] [CommMonoid N]

-- TODO: Generalise to different base rings, strengthen to an `AlgEquiv`
variable (R) in
/-- The tensor product of two monoid algebras is the monoid algebra of their product. -/
@[to_additive (dont_translate := R) (attr := simps! apply_coeff)
/-- The tensor product of two monoid algebras is the monoid algebra of their product. -/]
/--
Definition of `tensorEquiv` / `tensorEquiv` 的定义

English:
definition tensorEquiv
  signature: : R[M] otimes[R] R[N] ≃ₗ[R] R[M × N]
  body: TensorProduct.congr (coeffLinearEquiv _) (coeffLinearEquiv _) ≪≫ₗ
    finsuppTensorFinsupp' .. ≪≫ₗ (coeffLinearEquiv _).symm

@[to_additive (dont_translate := R) (attr := simp)]

中文:
定义 tensorEquiv
  签名: : R[M] otimes[R] R[N] ≃ₗ[R] R[M × N]
  定义体: TensorProduct.congr (coeffLinearEquiv _) (coeffLinearEquiv _) ≪≫ₗ
    finsuppTensorFinsupp' .. ≪≫ₗ (coeffLinearEquiv _).symm

@[to_additive (dont_translate := R) (attr := simp)]

Depends on / 依赖: TensorProduct, TensorProduct.congr, coeffLinearEquiv, finsuppTensorFinsupp
-/
noncomputable def tensorEquiv : R[M] otimes[R] R[N] ≃ₗ[R] R[M × N] :=
  TensorProduct.congr (coeffLinearEquiv _) (coeffLinearEquiv _) ≪≫ₗ
    finsuppTensorFinsupp' .. ≪≫ₗ (coeffLinearEquiv _).symm

@[to_additive (dont_translate := R) (attr := simp)]
/--
lemma `tensorEquiv_single_tmul_single` / 引理 `tensorEquiv_single_tmul_single`

English:
lemma tensorEquiv_single_tmul_single
  given: (m : M) (r₁ : R) (n : N) (r₂ : R)
  proof: by ext; simp

@[to_additive (dont_translate := R)]

中文:
引理 tensorEquiv_single_tmul_single
  条件: (m : M) (r₁ : R) (n : N) (r₂ : R)
  证明: by ext; simp

@[to_additive (dont_translate := R)]
-/
lemma tensorEquiv_single_tmul_single (m : M) (r₁ : R) (n : N) (r₂ : R) :
    tensorEquiv R (single m r₁ otimesₜ single n r₂) = single (m, n) (r₁ * r₂) := by ext; simp

@[to_additive (dont_translate := R)]
/--
lemma `tensorEquiv_symm_single_eq_single_one_tmul` / 引理 `tensorEquiv_symm_single_eq_single_one_tmul`

English:
lemma tensorEquiv_symm_single_eq_single_one_tmul
  given: (mn : M × N) (r : R)
  proof: by
  simp [tensorEquiv, finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]

@[to_additive (dont_translate := R)]

中文:
引理 tensorEquiv_symm_single_eq_single_one_tmul
  条件: (mn : M × N) (r : R)
  证明: by
  simp [tensorEquiv, finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]

@[to_additive (dont_translate := R)]

Depends on / 依赖: _symm_single_eq_single_one_tmul, finsuppTensorFinsupp, tensorEquiv
-/
lemma tensorEquiv_symm_single_eq_single_one_tmul (mn : M × N) (r : R) :
    (tensorEquiv R).symm (single mn r) = single mn.1 1 otimesₜ single mn.2 r := by
  simp [tensorEquiv, finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]

@[to_additive (dont_translate := R)]
/--
lemma `tensorEquiv_symm_single_eq_tmul_single_one` / 引理 `tensorEquiv_symm_single_eq_tmul_single_one`

English:
lemma tensorEquiv_symm_single_eq_tmul_single_one
  given: (mn : M × N) (r : R)
  proof: by
  simp [tensorEquiv, finsuppTensorFinsupp'_symm_single_eq_tmul_single_one]

中文:
引理 tensorEquiv_symm_single_eq_tmul_single_one
  条件: (mn : M × N) (r : R)
  证明: by
  simp [tensorEquiv, finsuppTensorFinsupp'_symm_single_eq_tmul_single_one]

Depends on / 依赖: _symm_single_eq_tmul_single_one, finsuppTensorFinsupp, tensorEquiv
-/
lemma tensorEquiv_symm_single_eq_tmul_single_one (mn : M × N) (r : R) :
    (tensorEquiv R).symm (single mn r) = single mn.1 r otimesₜ single mn.2 1 := by
  simp [tensorEquiv, finsuppTensorFinsupp'_symm_single_eq_tmul_single_one]

end MonoidAlgebra

end
