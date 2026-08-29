/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Andrew Yang
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Coalgebra.Equiv

import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.Algebra.Algebra.Bilinear

/-!
# Tensor products of coalgebras

Suppose `S` is an `R`-algebra. Given an `S`-coalgebra `A` and `R`-coalgebra `B`, we can define
a natural comultiplication map `Δ : A ⊗[R] B → (A ⊗[R] B) ⊗[S] (A ⊗[R] B)`
and counit map `ε : A ⊗[R] B → S` induced by the comultiplication and counit maps of `A` and `B`.

In this file we show that `Δ, ε` satisfy the axioms of a coalgebra, and also define other data
in the monoidal structure on `R`-coalgebras, like the tensor product of two coalgebra morphisms
as a coalgebra morphism.

In particular, when `R = S` we get tensor products of coalgebras, and when `A = S` we get
the base change `S ⊗[R] B` as an `S`-coalgebra.

-/

@[expose] public section

open TensorProduct

variable {R S A B : Type*} [CommSemiring R] [CommSemiring S] [AddCommMonoid A] [AddCommMonoid B]
    [Algebra R S] [Module R A] [Module S A] [Module R B] [IsScalarTower R S A]

namespace TensorProduct

open Coalgebra

section CoalgebraStruct
variable [CoalgebraStruct R B] [CoalgebraStruct S A]

noncomputable
/--
Instance `instCoalgebraStruct` / 实例 `instCoalgebraStruct`

English:
instance instCoalgebraStruct
  signature: : CoalgebraStruct S (A otimes[R] B) where
  body: AlgebraTensorModule.tensorTensorTensorComm R S R S A A B B ∘ₗ
      AlgebraTensorModule.map comul comul
  counit := AlgebraTensorModule.rid R S S ∘ₗ AlgebraTensorModule.map counit counit

中文:
实例 instCoalgebraStruct
  签名: : 余algebraStruct S (A otimes[R] B) where
  定义体: AlgebraTensorModule.tensorTensorTensorComm R S R S A A B B ∘ₗ
      AlgebraTensorModule.map comul comul
  counit := AlgebraTensorModule.rid R S S ∘ₗ AlgebraTensorModule.map counit counit

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.map, AlgebraTensorModule.rid, AlgebraTensorModule.tensorTensorTensorComm, counit, tensorTensorTensorComm
-/
instance instCoalgebraStruct : CoalgebraStruct S (A otimes[R] B) where
  comul :=
    AlgebraTensorModule.tensorTensorTensorComm R S R S A A B B ∘ₗ
      AlgebraTensorModule.map comul comul
  counit := AlgebraTensorModule.rid R S S ∘ₗ AlgebraTensorModule.map counit counit

/--
lemma `comul_def` / 引理 `comul_def`

English:
lemma comul_def
  proof: rfl

中文:
引理 comul_def
  证明: rfl

Depends on / 依赖: otimes
-/
lemma comul_def :
    Coalgebra.comul (R := S) (A := A otimes[R] B) =
      AlgebraTensorModule.tensorTensorTensorComm R S R S A A B B ∘ₗ
        AlgebraTensorModule.map Coalgebra.comul Coalgebra.comul :=
  rfl

/--
lemma `counit_def` / 引理 `counit_def`

English:
lemma counit_def
  proof: rfl

@[simp]

中文:
引理 counit_def
  证明: rfl

@[simp]

Depends on / 依赖: otimes
-/
lemma counit_def :
    Coalgebra.counit (R := S) (A := A otimes[R] B) =
      AlgebraTensorModule.rid R S S ∘ₗ AlgebraTensorModule.map counit counit :=
  rfl

@[simp]
/--
lemma `comul_tmul` / 引理 `comul_tmul`

English:
lemma comul_tmul
  given: (x : A) (y : B)
  proof: rfl

@[simp]

中文:
引理 comul_tmul
  条件: (x : A) (y : B)
  证明: rfl

@[simp]
-/
lemma comul_tmul (x : A) (y : B) :
    comul (x otimesₜ y) =
      AlgebraTensorModule.tensorTensorTensorComm R S R S A A B B (comul x otimesₜ comul y) := rfl

@[simp]
/--
lemma `counit_tmul` / 引理 `counit_tmul`

English:
lemma counit_tmul
  given: (x : A) (y : B)
  proof: rfl

中文:
引理 counit_tmul
  条件: (x : A) (y : B)
  证明: rfl

Depends on / 依赖: counit
-/
lemma counit_tmul (x : A) (y : B) :
    counit (R := S) (x otimesₜ[R] y) = counit (R := R) y • counit (R := S) x := rfl

end CoalgebraStruct

variable [Coalgebra R B] [Coalgebra S A]

open Lean.Parser.Tactic in
/-- `hopf_tensor_induction x with x₁ x₂` attempts to replace `x` by
`x₁ ⊗ₜ x₂` via linearity. This is an implementation detail that is used to set up tensor products
of coalgebras, bialgebras, and hopf algebras, and shouldn't be relied on downstream. -/
scoped macro "hopf_tensor_induction " var:elimTarget "with " var₁:ident var₂:ident : tactic =>
  `(tactic|
    (induction $var with
      | zero =>
        -- avoid the more general `map_zero` for performance reasons
        simp only [tmul_zero, LinearEquiv.map_zero, LinearMap.map_zero,
          zero_tmul, zero_mul, mul_zero]
      | add _ _ h₁ h₂ =>
        -- avoid the more general `map_add` for performance reasons
        simp only [LinearEquiv.map_add, LinearMap.map_add,
          tmul_add, add_tmul, add_mul, mul_add, h₁, h₂]
| tmul var₁ var₂ => ?_))

set_option backward.defeqAttrib.useBackward true in
set_option backward.privateInPublic true in
/--
lemma `coassoc` / 引理 `coassoc`

English:
lemma coassoc
  proof: by
  ext x y
  let F : A otimes[S] (A otimes[S] A) otimes[R] (B otimes[R] (B otimes[R] B)) ≃ₗ[S]
    A otimes[R] B otimes[S] (A otimes[R] B otimes[S] (A otimes[R] B)) :=
    AlgebraTensorModule.tensorTensorTensorComm _ _ _ _ _ _ _ _ ≪≫ₗ
      AlgebraTensorModule.congr (.refl _ _)
        (AlgebraTensorModule.tensorTensorTensorComm _ _ _ _ _ _ _ _)
  let F' : A otimes[S] (A otimes[S] A) otimes[R] (B otimes[R] (B otimes[R] B)) ->ₗ[S]
      A otimes[R] B otimes[S] (A otimes[R] B otimes[S] (A otimes[R] B)) :=
    TensorProduct.mapOfCompatibleSMul .. ∘ₗ
        TensorProduct.map .id (TensorProduct.mapOfCompatibleSMul ..) ∘ₗ F.toLinearMap
  convert! congr(F ($(Coalgebra.coassoc_apply x) otimesₜ[R] $(Coalgebra.coassoc_apply y))) using 1
  · dsimp
    hopf_tensor_induction comul (R := S) x with x₁ x₂
    hopf_tensor_induction comul (R := R) y with y₁ y₂
    dsimp
    hopf_tensor_induction comul (R := S) x₁ with x₁₁ x₁₂
    hopf_tensor_induction comul (R := R) y₁ with y₁₁ y₁₂
    rfl
  · dsimp
    hopf_tensor_induction comul (R := S) x with x₁ x₂
    hopf_tensor_induction comul (R := R) y with y₁ y₂
    dsimp
    hopf_tensor_induction comul (R := S) x₂ with x₂₁ x₂₂
    hopf_tensor_induction comul (R := R) y₂ with y₂₁ y₂₂
    rfl

中文:
引理 coassoc
  证明: by
  ext x y
  let F : A otimes[S] (A otimes[S] A) otimes[R] (B otimes[R] (B otimes[R] B)) ≃ₗ[S]
    A otimes[R] B otimes[S] (A otimes[R] B otimes[S] (A otimes[R] B)) :=
    AlgebraTensorModule.tensorTensorTensorComm _ _ _ _ _ _ _ _ ≪≫ₗ
      AlgebraTensorModule.congr (.refl _ _)
        (AlgebraTensorModule.tensorTensorTensorComm _ _ _ _ _ _ _ _)
  let F' : A otimes[S] (A otimes[S] A) otimes[R] (B otimes[R] (B otimes[R] B)) ->ₗ[S]
      A otimes[R] B otimes[S] (A otimes[R] B otimes[S] (A otimes[R] B)) :=
    TensorProduct.mapOfCompatibleSMul .. ∘ₗ
        TensorProduct.map .id (TensorProduct.mapOfCompatibleSMul ..) ∘ₗ F.toLinearMap
  convert! congr(F ($(Coalgebra.coassoc_apply x) otimesₜ[R] $(Coalgebra.coassoc_apply y))) using 1
  · dsimp
    hopf_tensor_induction comul (R := S) x with x₁ x₂
    hopf_tensor_induction comul (R := R) y with y₁ y₂
    dsimp
    hopf_tensor_induction comul (R := S) x₁ with x₁₁ x₁₂
    hopf_tensor_induction comul (R := R) y₁ with y₁₁ y₁₂
    rfl
  · dsimp
    hopf_tensor_induction comul (R := S) x with x₁ x₂
    hopf_tensor_induction comul (R := R) y with y₁ y₂
    dsimp
    hopf_tensor_induction comul (R := S) x₂ with x₂₁ x₂₂
    hopf_tensor_induction comul (R := R) y₂ with y₂₁ y₂₂
    rfl
-/
private lemma coassoc :
    TensorProduct.assoc S (A otimes[R] B) (A otimes[R] B) (A otimes[R] B) ∘ₗ
      (comul (R := S) (A := (A otimes[R] B))).rTensor (A otimes[R] B) ∘ₗ
        (comul (R := S) (A := (A otimes[R] B))) =
    (comul (R := S) (A := (A otimes[R] B))).lTensor (A otimes[R] B) ∘ₗ
      (comul (R := S) (A := (A otimes[R] B))) := by
  ext x y
  let F : A otimes[S] (A otimes[S] A) otimes[R] (B otimes[R] (B otimes[R] B)) ≃ₗ[S]
    A otimes[R] B otimes[S] (A otimes[R] B otimes[S] (A otimes[R] B)) :=
    AlgebraTensorModule.tensorTensorTensorComm _ _ _ _ _ _ _ _ ≪≫ₗ
      AlgebraTensorModule.congr (.refl _ _)
        (AlgebraTensorModule.tensorTensorTensorComm _ _ _ _ _ _ _ _)
  let F' : A otimes[S] (A otimes[S] A) otimes[R] (B otimes[R] (B otimes[R] B)) ->ₗ[S]
      A otimes[R] B otimes[S] (A otimes[R] B otimes[S] (A otimes[R] B)) :=
    TensorProduct.mapOfCompatibleSMul .. ∘ₗ
        TensorProduct.map .id (TensorProduct.mapOfCompatibleSMul ..) ∘ₗ F.toLinearMap
  convert! congr(F ($(Coalgebra.coassoc_apply x) otimesₜ[R] $(Coalgebra.coassoc_apply y))) using 1
  · dsimp
    hopf_tensor_induction comul (R := S) x with x₁ x₂
    hopf_tensor_induction comul (R := R) y with y₁ y₂
    dsimp
    hopf_tensor_induction comul (R := S) x₁ with x₁₁ x₁₂
    hopf_tensor_induction comul (R := R) y₁ with y₁₁ y₁₂
    rfl
  · dsimp
    hopf_tensor_induction comul (R := S) x with x₁ x₂
    hopf_tensor_induction comul (R := R) y with y₁ y₂
    dsimp
    hopf_tensor_induction comul (R := S) x₂ with x₂₁ x₂₂
    hopf_tensor_induction comul (R := R) y₂ with y₂₁ y₂₂
    rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
noncomputable
/--
Instance `instCoalgebra` / 实例 `instCoalgebra`

English:
instance instCoalgebra
  signature: : Coalgebra S (A otimes[R] B) where
  body: coassoc (R := R)
  rTensor_counit_comp_comul := by
    ext x y
    convert!
      congr((TensorProduct.lid S _).symm
        (TensorProduct.lid _ _ $(rTensor_counit_comul (R := S) x) otimesₜ[R]
TensorProduct.lid _ _ (rTensor_counit_comul (R := R) y)))
    · dsimp
      hopf_tensor_induction comul (R := S) x with x₁ x₂
      hopf_tensor_induction comul (R := R) y with y₁ y₂
      apply (TensorProduct.lid S _).injective
      dsimp
      rw [tmul_smul]; rw [smul_assoc]; rw [one_smul]; rw [smul_tmul']
    · dsimp
      simp only [one_smul]
  lTensor_counit_comp_comul := by
    ext x y
    convert!
      congr((TensorProduct.rid S _).symm
        (TensorProduct.rid _ _ $(lTensor_counit_comul (R := S) x) otimesₜ[R]
TensorProduct.rid _ _ (lTensor_counit_comul (R := R) y)))
    · dsimp
      hopf_tensor_induction comul (R := S) x with x₁ x₂
      hopf_tensor_induction comul (R := R) y with y₁ y₂
      apply (TensorProduct.rid S _).injective
      dsimp
      rw [tmul_smul]; rw [smul_assoc]; rw [one_smul]; rw [smul_tmul']
    · dsimp
      simp only [one_smul]

中文:
实例 instCoalgebra
  签名: : 余algebra S (A otimes[R] B) where
  定义体: coassoc (R := R)
  rTensor_counit_comp_comul := by
    ext x y
    convert!
      congr((TensorProduct.lid S _).symm
        (TensorProduct.lid _ _ $(rTensor_counit_comul (R := S) x) otimesₜ[R]
TensorProduct.lid _ _ (rTensor_counit_comul (R := R) y)))
    · dsimp
      hopf_tensor_induction comul (R := S) x with x₁ x₂
      hopf_tensor_induction comul (R := R) y with y₁ y₂
      apply (TensorProduct.lid S _).injective
      dsimp
      rw [tmul_smul]; rw [smul_assoc]; rw [one_smul]; rw [smul_tmul']
    · dsimp
      simp only [one_smul]
  lTensor_counit_comp_comul := by
    ext x y
    convert!
      congr((TensorProduct.rid S _).symm
        (TensorProduct.rid _ _ $(lTensor_counit_comul (R := S) x) otimesₜ[R]
TensorProduct.rid _ _ (lTensor_counit_comul (R := R) y)))
    · dsimp
      hopf_tensor_induction comul (R := S) x with x₁ x₂
      hopf_tensor_induction comul (R := R) y with y₁ y₂
      apply (TensorProduct.rid S _).injective
      dsimp
      rw [tmul_smul]; rw [smul_assoc]; rw [one_smul]; rw [smul_tmul']
    · dsimp
      simp only [one_smul]

Depends on / 依赖: coassoc
-/
instance instCoalgebra : Coalgebra S (A otimes[R] B) where
  coassoc := coassoc (R := R)
  rTensor_counit_comp_comul := by
    ext x y
    convert!
      congr((TensorProduct.lid S _).symm
        (TensorProduct.lid _ _ $(rTensor_counit_comul (R := S) x) otimesₜ[R]
TensorProduct.lid _ _ (rTensor_counit_comul (R := R) y)))
    · dsimp
      hopf_tensor_induction comul (R := S) x with x₁ x₂
      hopf_tensor_induction comul (R := R) y with y₁ y₂
      apply (TensorProduct.lid S _).injective
      dsimp
      rw [tmul_smul]; rw [smul_assoc]; rw [one_smul]; rw [smul_tmul']
    · dsimp
      simp only [one_smul]
  lTensor_counit_comp_comul := by
    ext x y
    convert!
      congr((TensorProduct.rid S _).symm
        (TensorProduct.rid _ _ $(lTensor_counit_comul (R := S) x) otimesₜ[R]
TensorProduct.rid _ _ (lTensor_counit_comul (R := R) y)))
    · dsimp
      hopf_tensor_induction comul (R := S) x with x₁ x₂
      hopf_tensor_induction comul (R := R) y with y₁ y₂
      apply (TensorProduct.rid S _).injective
      dsimp
      rw [tmul_smul]; rw [smul_assoc]; rw [one_smul]; rw [smul_tmul']
    · dsimp
      simp only [one_smul]

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsCocomm
  signature: S A] [IsCocomm R B] : IsCocomm S (A otimes[R] B) where
  body: by
    ext x y
    dsimp
    conv_rhs => rw [← comm_comul _ x, ← comm_comul _ y]
    hopf_tensor_induction comul (R := S) x with x₁ x₂
    hopf_tensor_induction comul (R := R) y with y₁ y₂
    simp

中文:
实例 [是余comm
  签名: S A] [是余comm R B] : 是余comm S (A otimes[R] B) where
  定义体: by
    ext x y
    dsimp
    conv_rhs => rw [← comm_comul _ x, ← comm_comul _ y]
    hopf_tensor_induction comul (R := S) x with x₁ x₂
    hopf_tensor_induction comul (R := R) y with y₁ y₂
    simp

Depends on / 依赖: comm_comul, conv_rhs, hopf_tensor_induction
-/
instance [IsCocomm S A] [IsCocomm R B] : IsCocomm S (A otimes[R] B) where
  comm_comp_comul := by
    ext x y
    dsimp
    conv_rhs => rw [← comm_comul _ x, ← comm_comul _ y]
    hopf_tensor_induction comul (R := S) x with x₁ x₂
    hopf_tensor_induction comul (R := R) y with y₁ y₂
    simp

end TensorProduct

namespace Coalgebra
namespace TensorProduct

variable {R S M N P Q : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q] [Module R M] [Module R N]
  [Module R P] [Module R Q] [Module S M] [IsScalarTower R S M] [Coalgebra S M] [Module S N]
  [IsScalarTower R S N] [Coalgebra S N] [Coalgebra R P] [Coalgebra R Q]

section

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : M ->ₗc[S] N) (g : P ->ₗc[R] Q)
  body: AlgebraTensorModule.map f.toLinearMap g.toLinearMap
  counit_comp := by ext; simp
  map_comp_comul := by
    ext x y
    dsimp
    simp only [← CoalgHomClass.map_comp_comul_apply]
    hopf_tensor_induction comul (R := S) x with x₁ x₂
    hopf_tensor_induction comul (R := R) y with y₁ y₂
    simp

@[simp]

中文:
定义 map
  签名: (f : M ->ₗc[S] N) (g : P ->ₗc[R] Q)
  定义体: AlgebraTensorModule.map f.toLinearMap g.toLinearMap
  counit_comp := by ext; simp
  map_comp_comul := by
    ext x y
    dsimp
    simp only [← CoalgHomClass.map_comp_comul_apply]
    hopf_tensor_induction comul (R := S) x with x₁ x₂
    hopf_tensor_induction comul (R := R) y with y₁ y₂
    simp

@[simp]

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.map, f.toLinearMap, g.toLinearMap, toLinearMap
-/
noncomputable def map (f : M ->ₗc[S] N) (g : P ->ₗc[R] Q) :
    M otimes[R] P ->ₗc[S] N otimes[R] Q where
  toLinearMap := AlgebraTensorModule.map f.toLinearMap g.toLinearMap
  counit_comp := by ext; simp
  map_comp_comul := by
    ext x y
    dsimp
    simp only [← CoalgHomClass.map_comp_comul_apply]
    hopf_tensor_induction comul (R := S) x with x₁ x₂
    hopf_tensor_induction comul (R := R) y with y₁ y₂
    simp

@[simp]
/--
theorem `map_tmul` / 定理 `map_tmul`

English:
theorem map_tmul
  given: (f : M ->ₗc[S] N) (g : P ->ₗc[R] Q) (x : M) (y : P)
  proof: rfl

@[simp]

中文:
定理 map_tmul
  条件: (f : M ->ₗc[S] N) (g : P ->ₗc[R] Q) (x : M) (y : P)
  证明: rfl

@[simp]
-/
theorem map_tmul (f : M ->ₗc[S] N) (g : P ->ₗc[R] Q) (x : M) (y : P) :
    map f g (x otimesₜ y) = f x otimesₜ g y :=
  rfl

@[simp]
/--
theorem `map_toLinearMap` / 定理 `map_toLinearMap`

English:
theorem map_toLinearMap
  given: (f : M ->ₗc[S] N) (g : P ->ₗc[R] Q)
  proof: rfl

中文:
定理 map_toLinearMap
  条件: (f : M ->ₗc[S] N) (g : P ->ₗc[R] Q)
  证明: rfl
-/
theorem map_toLinearMap (f : M ->ₗc[S] N) (g : P ->ₗc[R] Q) :
    map f g = AlgebraTensorModule.map (f : M ->ₗ[S] N) (g : P ->ₗ[R] Q) := rfl

variable (R S M N P)

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def assoc
  body: { AlgebraTensorModule.assoc R S S M N P with
    counit_comp := by ext; simp
    map_comp_comul := by
      ext x y z
      dsimp
      hopf_tensor_induction comul (R := S) x with x₁ x₂
      hopf_tensor_induction comul (R := S) y with y₁ y₂
      hopf_tensor_induction comul (R := R) z with z₁ z₂
      simp }

中文:
定义 noncomputable
  签名: def assoc
  定义体: { AlgebraTensorModule.assoc R S S M N P with
    counit_comp := by ext; simp
    map_comp_comul := by
      ext x y z
      dsimp
      hopf_tensor_induction comul (R := S) x with x₁ x₂
      hopf_tensor_induction comul (R := S) y with y₁ y₂
      hopf_tensor_induction comul (R := R) z with z₁ z₂
      simp }
-/
protected noncomputable def assoc :
    (M otimes[S] N) otimes[R] P ≃ₗc[S] M otimes[S] (N otimes[R] P) :=
  { AlgebraTensorModule.assoc R S S M N P with
    counit_comp := by ext; simp
    map_comp_comul := by
      ext x y z
      dsimp
      hopf_tensor_induction comul (R := S) x with x₁ x₂
      hopf_tensor_induction comul (R := S) y with y₁ y₂
      hopf_tensor_induction comul (R := R) z with z₁ z₂
      simp }

variable {R S M N P}

@[simp]
/--
theorem `assoc_tmul` / 定理 `assoc_tmul`

English:
theorem assoc_tmul
  given: (x : M) (y : N) (z : P)
  proof: rfl

@[simp]

中文:
定理 assoc_tmul
  条件: (x : M) (y : N) (z : P)
  证明: rfl

@[simp]
-/
theorem assoc_tmul (x : M) (y : N) (z : P) :
    Coalgebra.TensorProduct.assoc R S M N P ((x otimesₜ y) otimesₜ z) = x otimesₜ (y otimesₜ z) :=
  rfl

@[simp]
/--
theorem `assoc_symm_tmul` / 定理 `assoc_symm_tmul`

English:
theorem assoc_symm_tmul
  given: (x : M) (y : N) (z : P)
  proof: rfl

@[simp]

中文:
定理 assoc_symm_tmul
  条件: (x : M) (y : N) (z : P)
  证明: rfl

@[simp]
-/
theorem assoc_symm_tmul (x : M) (y : N) (z : P) :
    (Coalgebra.TensorProduct.assoc R S M N P).symm (x otimesₜ (y otimesₜ z)) = (x otimesₜ y) otimesₜ z :=
  rfl

@[simp]
/--
theorem `assoc_toLinearEquiv` / 定理 `assoc_toLinearEquiv`

English:
theorem assoc_toLinearEquiv
  proof: rfl

中文:
定理 assoc_toLinearEquiv
  证明: rfl
-/
theorem assoc_toLinearEquiv :
    Coalgebra.TensorProduct.assoc R S M N P = AlgebraTensorModule.assoc R S S M N P := rfl

variable (R P)

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def lid
  body: { _root_.TensorProduct.lid R P with
    counit_comp := by ext; simp
    map_comp_comul := by
      ext x
      dsimp
      simp only [one_smul]
      hopf_tensor_induction comul (R := R) x with x₁ x₂
      simp }

中文:
定义 noncomputable
  签名: def lid
  定义体: { _root_.TensorProduct.lid R P with
    counit_comp := by ext; simp
    map_comp_comul := by
      ext x
      dsimp
      simp only [one_smul]
      hopf_tensor_induction comul (R := R) x with x₁ x₂
      simp }
-/
protected noncomputable def lid : R otimes[R] P ≃ₗc[R] P :=
  { _root_.TensorProduct.lid R P with
    counit_comp := by ext; simp
    map_comp_comul := by
      ext x
      dsimp
      simp only [one_smul]
      hopf_tensor_induction comul (R := R) x with x₁ x₂
      simp }

variable {R P}

@[simp]
/--
theorem `lid_toLinearEquiv` / 定理 `lid_toLinearEquiv`

English:
theorem lid_toLinearEquiv
  proof: rfl

@[simp]

中文:
定理 lid_toLinearEquiv
  证明: rfl

@[simp]
-/
theorem lid_toLinearEquiv :
    (Coalgebra.TensorProduct.lid R P) = _root_.TensorProduct.lid R P := rfl

@[simp]
/--
theorem `lid_tmul` / 定理 `lid_tmul`

English:
theorem lid_tmul
  given: (r : R) (a : P)
  statement: Coalgebra.TensorProduct.lid R P (r otimesₜ a) = r • a
  proof: rfl

@[simp]

中文:
定理 lid_tmul
  条件: (r : R) (a : P)
  结论: 余algebra.张量积.lid R P (r otimesₜ a) = r • a
  证明: rfl

@[simp]
-/
theorem lid_tmul (r : R) (a : P) : Coalgebra.TensorProduct.lid R P (r otimesₜ a) = r • a := rfl

@[simp]
/--
theorem `lid_symm_apply` / 定理 `lid_symm_apply`

English:
theorem lid_symm_apply
  given: (a : P)
  statement: (Coalgebra.TensorProduct.lid R P).symm a = 1 otimesₜ a
  proof: rfl

中文:
定理 lid_symm_apply
  条件: (a : P)
  结论: (余algebra.张量积.lid R P).symm a = 1 otimesₜ a
  证明: rfl
-/
theorem lid_symm_apply (a : P) : (Coalgebra.TensorProduct.lid R P).symm a = 1 otimesₜ a := rfl

set_option backward.defeqAttrib.useBackward true in
variable (R S M) in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def rid
  body: { AlgebraTensorModule.rid R S M with
    counit_comp := by ext; simp
    map_comp_comul := by
      ext x
      dsimp
      simp only [one_smul]
      hopf_tensor_induction comul (R := S) x with x₁ x₂
      simp }

@[simp]

中文:
定义 noncomputable
  签名: def rid
  定义体: { AlgebraTensorModule.rid R S M with
    counit_comp := by ext; simp
    map_comp_comul := by
      ext x
      dsimp
      simp only [one_smul]
      hopf_tensor_induction comul (R := S) x with x₁ x₂
      simp }

@[simp]
-/
protected noncomputable def rid : M otimes[R] R ≃ₗc[S] M :=
  { AlgebraTensorModule.rid R S M with
    counit_comp := by ext; simp
    map_comp_comul := by
      ext x
      dsimp
      simp only [one_smul]
      hopf_tensor_induction comul (R := S) x with x₁ x₂
      simp }

@[simp]
/--
theorem `rid_toLinearEquiv` / 定理 `rid_toLinearEquiv`

English:
theorem rid_toLinearEquiv
  proof: rfl

@[simp]

中文:
定理 rid_toLinearEquiv
  证明: rfl

@[simp]
-/
theorem rid_toLinearEquiv :
    (Coalgebra.TensorProduct.rid R S M) = AlgebraTensorModule.rid R S M := rfl

@[simp]
/--
theorem `rid_tmul` / 定理 `rid_tmul`

English:
theorem rid_tmul
  given: (r : R) (a : M)
  statement: Coalgebra.TensorProduct.rid R S M (a otimesₜ r) = r • a
  proof: rfl

@[simp]

中文:
定理 rid_tmul
  条件: (r : R) (a : M)
  结论: 余algebra.张量积.rid R S M (a otimesₜ r) = r • a
  证明: rfl

@[simp]
-/
theorem rid_tmul (r : R) (a : M) : Coalgebra.TensorProduct.rid R S M (a otimesₜ r) = r • a := rfl

@[simp]
/--
theorem `rid_symm_apply` / 定理 `rid_symm_apply`

English:
theorem rid_symm_apply
  given: (a : M)
  statement: (Coalgebra.TensorProduct.rid R S M).symm a = a otimesₜ 1
  proof: rfl

中文:
定理 rid_symm_apply
  条件: (a : M)
  结论: (余algebra.张量积.rid R S M).symm a = a otimesₜ 1
  证明: rfl
-/
theorem rid_symm_apply (a : M) : (Coalgebra.TensorProduct.rid R S M).symm a = a otimesₜ 1 := rfl

end

end TensorProduct
end Coalgebra
namespace CoalgHom

variable {R M N P : Type*} [CommRing R]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N]
  [Module R P] [Coalgebra R M] [Coalgebra R N] [Coalgebra R P]

variable (M)

/--
Definition of `lTensor` / `lTensor` 的定义

English:
abbreviation lTensor
  signature: (f : N ->ₗc[R] P)
  body: Coalgebra.TensorProduct.map (CoalgHom.id R M) f

中文:
缩写 lTensor
  签名: (f : N ->ₗc[R] P)
  定义体: Coalgebra.TensorProduct.map (CoalgHom.id R M) f

Depends on / 依赖: CoalgHom, CoalgHom.id, Coalgebra, Coalgebra.TensorProduct.map, TensorProduct
-/
noncomputable abbrev lTensor (f : N ->ₗc[R] P) : M otimes[R] N ->ₗc[R] M otimes[R] P :=
  Coalgebra.TensorProduct.map (CoalgHom.id R M) f

/--
Definition of `rTensor` / `rTensor` 的定义

English:
abbreviation rTensor
  signature: (f : N ->ₗc[R] P)
  body: Coalgebra.TensorProduct.map f (CoalgHom.id R M)

中文:
缩写 rTensor
  签名: (f : N ->ₗc[R] P)
  定义体: Coalgebra.TensorProduct.map f (CoalgHom.id R M)

Depends on / 依赖: CoalgHom, CoalgHom.id, Coalgebra, Coalgebra.TensorProduct.map, TensorProduct
-/
noncomputable abbrev rTensor (f : N ->ₗc[R] P) : N otimes[R] M ->ₗc[R] P otimes[R] M :=
  Coalgebra.TensorProduct.map f (CoalgHom.id R M)

end CoalgHom

namespace Coalgebra
variable {R C : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]
  [IsCocomm R C]

local notation3 "ε" => counit (R := R) (A := C)
local notation3 "μ" => LinearMap.mul' R R
local notation3 "δ" => comul (R := R)
local infix:90 " ◁ " => LinearMap.lTensor
local notation3:90 f:90 " ▷ " X:90 => LinearMap.rTensor X f
local infix:70 " otimesₘ " => _root_.TensorProduct.map

variable (R C) in
/--
Definition of `comulCoalgHom` / `comulCoalgHom` 的定义

English:
definition comulCoalgHom
  signature: : C ->ₗc[R] C otimes[R] C where
  body: δ
  counit_comp := by
    simp only [counit_def, AlgebraTensorModule.rid_eq_rid, ← lid_eq_rid]
    calc
        (μ ∘ₗ (ε otimesₘ ε)) ∘ₗ δ
    _ = (μ ∘ₗ ε ▷ R) ∘ₗ (C ◁ ε ∘ₗ δ) := by simp [coassoc_simps]
    _ = ε := by ext; simp
  map_comp_comul := by simp [comul_def, coassoc_simps]

中文:
定义 comulCoalgHom
  签名: : C ->ₗc[R] C otimes[R] C where
  定义体: δ
  counit_comp := by
    simp only [counit_def, AlgebraTensorModule.rid_eq_rid, ← lid_eq_rid]
    calc
        (μ ∘ₗ (ε otimesₘ ε)) ∘ₗ δ
    _ = (μ ∘ₗ ε ▷ R) ∘ₗ (C ◁ ε ∘ₗ δ) := by simp [coassoc_simps]
    _ = ε := by ext; simp
  map_comp_comul := by simp [comul_def, coassoc_simps]
-/
noncomputable def comulCoalgHom : C ->ₗc[R] C otimes[R] C where
  __ := δ
  counit_comp := by
    simp only [counit_def, AlgebraTensorModule.rid_eq_rid, ← lid_eq_rid]
    calc
        (μ ∘ₗ (ε otimesₘ ε)) ∘ₗ δ
    _ = (μ ∘ₗ ε ▷ R) ∘ₗ (C ◁ ε ∘ₗ δ) := by simp [coassoc_simps]
    _ = ε := by ext; simp
  map_comp_comul := by simp [comul_def, coassoc_simps]

end Coalgebra
