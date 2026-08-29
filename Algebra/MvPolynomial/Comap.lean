/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.MvPolynomial.Rename

/-!
# `comap` operation on `MvPolynomial`

This file defines the `comap` function on `MvPolynomial`.

`MvPolynomial.comap` is a low-tech example of a map of "algebraic varieties," modulo the fact that
`mathlib` does not yet define varieties.

## Notation

As in other polynomial files, we typically use the notation:

+ `σ : Type*` (indexing the variables)

+ `R : Type*` `[CommSemiring R]` (the coefficients)

-/

@[expose] public section


namespace MvPolynomial

variable {σ : Type*} {τ : Type*} {υ : Type*} {R : Type*} [CommSemiring R]

/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (f : MvPolynomial σ R ->ₐ[R] MvPolynomial τ R)
  body: fun x i => aeval x (f (X i))

@[simp]

中文:
定义 comap
  签名: (f : 多元多项式 σ R ->ₐ[R] 多元多项式 τ R)
  定义体: fun x i => aeval x (f (X i))

@[simp]
-/
noncomputable def comap (f : MvPolynomial σ R ->ₐ[R] MvPolynomial τ R) : (τ -> R) -> σ -> R :=
  fun x i => aeval x (f (X i))

@[simp]
/--
theorem `comap_apply` / 定理 `comap_apply`

English:
theorem comap_apply
  given: (f : MvPolynomial σ R ->ₐ[R] MvPolynomial τ R) (x : τ -> R) (i : σ)
  proof: rfl

@[simp]

中文:
定理 comap_apply
  条件: (f : 多元多项式 σ R ->ₐ[R] 多元多项式 τ R) (x : τ -> R) (i : σ)
  证明: rfl

@[simp]
-/
theorem comap_apply (f : MvPolynomial σ R ->ₐ[R] MvPolynomial τ R) (x : τ -> R) (i : σ) :
    comap f x i = aeval x (f (X i)) :=
  rfl

@[simp]
/--
theorem `comap_id_apply` / 定理 `comap_id_apply`

English:
theorem comap_id_apply
  given: (x : σ -> R)
  statement: comap (AlgHom.id R (MvPolynomial σ R)) x = x
  proof: by
  funext i
  simp only [comap, AlgHom.id_apply, aeval_X]

中文:
定理 comap_id_apply
  条件: (x : σ -> R)
  结论: comap (代数态射.id R (多元多项式 σ R)) x = x
  证明: by
  funext i
  simp only [comap, AlgHom.id_apply, aeval_X]

Depends on / 依赖: AlgHom, AlgHom.id_apply, aeval_X, id_apply
-/
theorem comap_id_apply (x : σ -> R) : comap (AlgHom.id R (MvPolynomial σ R)) x = x := by
  funext i
  simp only [comap, AlgHom.id_apply, aeval_X]

variable (σ R)

/--
theorem `comap_id` / 定理 `comap_id`

English:
theorem comap_id
  statement: comap (AlgHom.id R (MvPolynomial σ R)) = id
  proof: by
  funext x
  exact comap_id_apply x

中文:
定理 comap_id
  结论: comap (代数态射.id R (多元多项式 σ R)) = id
  证明: by
  funext x
  exact comap_id_apply x

Depends on / 依赖: comap_id_apply
-/
theorem comap_id : comap (AlgHom.id R (MvPolynomial σ R)) = id := by
  funext x
  exact comap_id_apply x

variable {σ R}

/--
theorem `comap_comp_apply` / 定理 `comap_comp_apply`

English:
theorem comap_comp_apply
  statement: (f : MvPolynomial σ R ->ₐ[R] MvPolynomial τ R)
  proof: by
  funext i
  trans aeval x (aeval (fun i => g (X i)) (f (X i)))
  · apply eval₂Hom_congr rfl rfl
    rw [AlgHom.comp_apply]
    suffices g = aeval fun i => g (X i) by rw [← this]
    exact aeval_unique g
  · simp only [comap, aeval_eq_eval₂Hom, map_eval₂Hom]
    refine eval₂Hom_congr ?_ rfl rfl
 

中文:
定理 comap_comp_apply
  结论: (f : 多元多项式 σ R ->ₐ[R] 多元多项式 τ R)
  证明: by
  funext i
  trans aeval x (aeval (fun i => g (X i)) (f (X i)))
  · apply eval₂Hom_congr rfl rfl
    rw [AlgHom.comp_apply]
    suffices g = aeval fun i => g (X i) by rw [← this]
    exact aeval_unique g
  · simp only [comap, aeval_eq_eval₂Hom, map_eval₂Hom]
    refine eval₂Hom_congr ?_ rfl rfl
 

Depends on / 依赖: AlgHom, AlgHom.comp_apply, aeval_C, aeval_unique, comp_apply
-/
theorem comap_comp_apply (f : MvPolynomial σ R ->ₐ[R] MvPolynomial τ R)
    (g : MvPolynomial τ R ->ₐ[R] MvPolynomial υ R) (x : υ -> R) :
    comap (g.comp f) x = comap f (comap g x) := by
  funext i
  trans aeval x (aeval (fun i => g (X i)) (f (X i)))
  · apply eval₂Hom_congr rfl rfl
    rw [AlgHom.comp_apply]
    suffices g = aeval fun i => g (X i) by rw [← this]
    exact aeval_unique g
  · simp only [comap, aeval_eq_eval₂Hom, map_eval₂Hom]
    refine eval₂Hom_congr ?_ rfl rfl
    ext r
    apply aeval_C

/--
theorem `comap_comp` / 定理 `comap_comp`

English:
theorem comap_comp
  statement: (f : MvPolynomial σ R ->ₐ[R] MvPolynomial τ R)
  proof: by
  funext x
  exact comap_comp_apply _ _ _

中文:
定理 comap_comp
  结论: (f : 多元多项式 σ R ->ₐ[R] 多元多项式 τ R)
  证明: by
  funext x
  exact comap_comp_apply _ _ _

Depends on / 依赖: comap_comp_apply
-/
theorem comap_comp (f : MvPolynomial σ R ->ₐ[R] MvPolynomial τ R)
    (g : MvPolynomial τ R ->ₐ[R] MvPolynomial υ R) : comap (g.comp f) = comap f ∘ comap g := by
  funext x
  exact comap_comp_apply _ _ _

/--
theorem `comap_eq_id_of_eq_id` / 定理 `comap_eq_id_of_eq_id`

English:
theorem comap_eq_id_of_eq_id
  statement: (f : MvPolynomial σ R ->ₐ[R] MvPolynomial σ R) (hf : forall φ, f φ = φ)
  proof: by
  convert! comap_id_apply x
  ext1 φ
  simp [hf, AlgHom.id_apply]

中文:
定理 comap_eq_id_of_eq_id
  结论: (f : 多元多项式 σ R ->ₐ[R] 多元多项式 σ R) (hf : 对任意 φ, f φ = φ)
  证明: by
  convert! comap_id_apply x
  ext1 φ
  simp [hf, AlgHom.id_apply]

Depends on / 依赖: AlgHom, AlgHom.id_apply, comap_id_apply, convert, id_apply
-/
theorem comap_eq_id_of_eq_id (f : MvPolynomial σ R ->ₐ[R] MvPolynomial σ R) (hf : forall φ, f φ = φ)
    (x : σ -> R) : comap f x = x := by
  convert! comap_id_apply x
  ext1 φ
  simp [hf, AlgHom.id_apply]

/--
theorem `comap_rename` / 定理 `comap_rename`

English:
theorem comap_rename
  given: (f : σ -> τ) (x : τ -> R)
  statement: comap (rename f) x = x ∘ f
  proof: by
  funext
  simp [rename_X, comap_apply, aeval_X]

中文:
定理 comap_rename
  条件: (f : σ -> τ) (x : τ -> R)
  结论: comap (rename f) x = x ∘ f
  证明: by
  funext
  simp [rename_X, comap_apply, aeval_X]

Depends on / 依赖: aeval_X, comap_apply, rename_X
-/
theorem comap_rename (f : σ -> τ) (x : τ -> R) : comap (rename f) x = x ∘ f := by
  funext
  simp [rename_X, comap_apply, aeval_X]

/--
Definition of `comapEquiv` / `comapEquiv` 的定义

English:
definition comapEquiv
  signature: (f : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R)
  body: comap f
  invFun := comap f.symm
  left_inv := by
    intro x
    rw [← comap_comp_apply]
    apply comap_eq_id_of_eq_id
    intro
    simp only [AlgHom.id_apply, AlgEquiv.comp_symm]
  right_inv := by
    intro x
    rw [← comap_comp_apply]
    apply comap_eq_id_of_eq_id
    intro
    simp only [Alg

中文:
定义 comapEquiv
  签名: (f : 多元多项式 σ R ≃ₐ[R] 多元多项式 τ R)
  定义体: comap f
  invFun := comap f.symm
  left_inv := by
    intro x
    rw [← comap_comp_apply]
    apply comap_eq_id_of_eq_id
    intro
    simp only [AlgHom.id_apply, AlgEquiv.comp_symm]
  right_inv := by
    intro x
    rw [← comap_comp_apply]
    apply comap_eq_id_of_eq_id
    intro
    simp only [Alg
-/
noncomputable def comapEquiv (f : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R) : (τ -> R) ≃ (σ -> R) where
  toFun := comap f
  invFun := comap f.symm
  left_inv := by
    intro x
    rw [← comap_comp_apply]
    apply comap_eq_id_of_eq_id
    intro
    simp only [AlgHom.id_apply, AlgEquiv.comp_symm]
  right_inv := by
    intro x
    rw [← comap_comp_apply]
    apply comap_eq_id_of_eq_id
    intro
    simp only [AlgHom.id_apply, AlgEquiv.symm_comp]

@[simp]
/--
theorem `comapEquiv_coe` / 定理 `comapEquiv_coe`

English:
theorem comapEquiv_coe
  given: (f : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R)
  proof: rfl

@[simp]

中文:
定理 comapEquiv_coe
  条件: (f : 多元多项式 σ R ≃ₐ[R] 多元多项式 τ R)
  证明: rfl

@[simp]
-/
theorem comapEquiv_coe (f : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R) :
    (comapEquiv f : (τ -> R) -> σ -> R) = comap f :=
  rfl

@[simp]
/--
theorem `comapEquiv_symm_coe` / 定理 `comapEquiv_symm_coe`

English:
theorem comapEquiv_symm_coe
  given: (f : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R)
  proof: rfl

中文:
定理 comapEquiv_symm_coe
  条件: (f : 多元多项式 σ R ≃ₐ[R] 多元多项式 τ R)
  证明: rfl
-/
theorem comapEquiv_symm_coe (f : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R) :
    ((comapEquiv f).symm : (σ -> R) -> τ -> R) = comap f.symm :=
  rfl

end MvPolynomial
