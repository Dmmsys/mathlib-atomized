/-
Copyright (c) 2024 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.Pi

/-!

# Tensor product and products

In this file we examine the behaviour of the tensor product with arbitrary and finite products.

Let `S` be an `R`-algebra, `N` an `S`-module, `ι` an index type and `Mᵢ` a family of `R`-modules.
We then have a natural map

`TensorProduct.piRightHom`: `N ⊗[R] (∀ i, M i) →ₗ[S] ∀ i, N ⊗[R] M i`

In general, this is not an isomorphism, but if `ι` is finite, then it is
and it is packaged as `TensorProduct.piRight`. Also a special case for when `Mᵢ = R` is given.

## Notes

See `Mathlib/LinearAlgebra/TensorProduct/Prod.lean` for binary products.

-/

@[expose] public section

variable (R : Type*) [CommSemiring R]
variable (S : Type*) [CommSemiring S] [Algebra R S]
variable (N : Type*) [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]
variable (ι : Type*)

open LinearMap

namespace TensorProduct

section

variable {ι} (M : ι -> Type*) [forall i, AddCommMonoid (M i)] [forall i, Module R (M i)]

/--
Definition of `piRightHomBil` / `piRightHomBil` 的定义

English:
definition piRightHomBil
  signature: : N ->ₗ[S] (forall i, M i) ->ₗ[R] forall i, N otimes[R] M i where
  body: LinearMap.pi (fun i => mk R N (M i) n ∘ₗ LinearMap.proj i)
  map_add' _ _ := by
    ext
    simp
  map_smul' _ _ := rfl

中文:
定义 piRightHomBil
  签名: : N ->ₗ[S] (对任意 i, M i) ->ₗ[R] 对任意 i, N otimes[R] M i where
  定义体: LinearMap.pi (fun i => mk R N (M i) n ∘ₗ LinearMap.proj i)
  map_add' _ _ := by
    ext
    simp
  map_smul' _ _ := rfl

Depends on / 依赖: LinearMap, LinearMap.pi, LinearMap.proj
-/
def piRightHomBil : N ->ₗ[S] (forall i, M i) ->ₗ[R] forall i, N otimes[R] M i where
  toFun n := LinearMap.pi (fun i => mk R N (M i) n ∘ₗ LinearMap.proj i)
  map_add' _ _ := by
    ext
    simp
  map_smul' _ _ := rfl

/--
Definition of `piRightHom` / `piRightHom` 的定义

English:
definition piRightHom
  signature: : N otimes[R] (forall i, M i) ->ₗ[S] forall i, N otimes[R] M i
  body: AlgebraTensorModule.lift piRightHomBil R S N M

@[simp]

中文:
定义 piRightHom
  签名: : N otimes[R] (对任意 i, M i) ->ₗ[S] 对任意 i, N otimes[R] M i
  定义体: AlgebraTensorModule.lift piRightHomBil R S N M

@[simp]

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.lift, piRightHomBil
-/
def piRightHom : N otimes[R] (forall i, M i) ->ₗ[S] forall i, N otimes[R] M i :=
AlgebraTensorModule.lift piRightHomBil R S N M

@[simp]
/--
lemma `piRightHom_tmul` / 引理 `piRightHom_tmul`

English:
lemma piRightHom_tmul
  given: (x : N) (f : forall i, M i)
  proof: rfl

中文:
引理 piRightHom_tmul
  条件: (x : N) (f : 对任意 i, M i)
  证明: rfl
-/
lemma piRightHom_tmul (x : N) (f : forall i, M i) :
    piRightHom R S N M (x otimesₜ f) = (fun j => x otimesₜ f j) :=
  rfl

variable [Fintype ι] [DecidableEq ι]

/--
Definition of `piRightInv` / `piRightInv` 的定义

English:
definition piRightInv
  signature: : (forall i, N otimes[R] M i) ->ₗ[S] N otimes[R] forall i, M i
  body: LinearMap.lsum S (fun i => N otimes[R] M i) S fun i =>
    AlgebraTensorModule.map LinearMap.id (single R M i)

@[simp]

中文:
定义 piRightInv
  签名: : (对任意 i, N otimes[R] M i) ->ₗ[S] N otimes[R] 对任意 i, M i
  定义体: LinearMap.lsum S (fun i => N otimes[R] M i) S fun i =>
    AlgebraTensorModule.map LinearMap.id (single R M i)

@[simp]

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.map, LinearMap, LinearMap.id, LinearMap.lsum, otimes, single
-/
def piRightInv : (forall i, N otimes[R] M i) ->ₗ[S] N otimes[R] forall i, M i :=
LinearMap.lsum S (fun i => N otimes[R] M i) S fun i =>
    AlgebraTensorModule.map LinearMap.id (single R M i)

@[simp]
/--
lemma `piRightInv_apply` / 引理 `piRightInv_apply`

English:
lemma piRightInv_apply
  given: (x : N) (m : forall i, M i)
  proof: by
  simp only [piRightInv, lsum_apply, coe_sum, coe_comp, coe_proj, Finset.sum_apply,
    Function.comp_apply, Function.eval, AlgebraTensorModule.map_tmul, id_coe, id_eq, coe_single]
  rw [← tmul_sum]
  congr
  ext j
  simp

@[simp]

中文:
引理 piRightInv_apply
  条件: (x : N) (m : 对任意 i, M i)
  证明: by
  simp only [piRightInv, lsum_apply, coe_sum, coe_comp, coe_proj, Finset.sum_apply,
    Function.comp_apply, Function.eval, AlgebraTensorModule.map_tmul, id_coe, id_eq, coe_single]
  rw [← tmul_sum]
  congr
  ext j
  simp

@[simp]
-/
private lemma piRightInv_apply (x : N) (m : forall i, M i) :
    piRightInv R S N M (fun i => x otimesₜ m i) = x otimesₜ m := by
  simp only [piRightInv, lsum_apply, coe_sum, coe_comp, coe_proj, Finset.sum_apply,
    Function.comp_apply, Function.eval, AlgebraTensorModule.map_tmul, id_coe, id_eq, coe_single]
  rw [← tmul_sum]
  congr
  ext j
  simp

@[simp]
/--
lemma `piRightInv_single` / 引理 `piRightInv_single`

English:
lemma piRightInv_single
  given: (x : N) (i : ι) (m : M i)
  proof: by
  have : Pi.single i (x otimesₜ m) = fun j => x otimesₜ[R] (Pi.single i m j) := by
    ext j
    rw [← tmul_single]
  rw [this]
  simp

中文:
引理 piRightInv_single
  条件: (x : N) (i : ι) (m : M i)
  证明: by
  have : Pi.single i (x otimesₜ m) = fun j => x otimesₜ[R] (Pi.single i m j) := by
    ext j
    rw [← tmul_single]
  rw [this]
  simp
-/
private lemma piRightInv_single (x : N) (i : ι) (m : M i) :
    piRightInv R S N M (Pi.single i (x otimesₜ m)) = x otimesₜ Pi.single i m := by
  have : Pi.single i (x otimesₜ m) = fun j => x otimesₜ[R] (Pi.single i m j) := by
    ext j
    rw [← tmul_single]
  rw [this]
  simp

/--
Definition of `piRight` / `piRight` 的定义

English:
definition piRight
  signature: : N otimes[R] (forall i, M i) ≃ₗ[S] forall i, N otimes[R] M i
  body: LinearEquiv.ofLinearMap
    (piRightHom R S N M)
    (piRightInv R S N M)
    (by ext i x m j; simp [tmul_single])
    (by ext x j m; simp)

@[simp]

中文:
定义 piRight
  签名: : N otimes[R] (对任意 i, M i) ≃ₗ[S] 对任意 i, N otimes[R] M i
  定义体: LinearEquiv.ofLinearMap
    (piRightHom R S N M)
    (piRightInv R S N M)
    (by ext i x m j; simp [tmul_single])
    (by ext x j m; simp)

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.ofLinearMap, ofLinearMap, piRightHom, piRightInv, tmul_single
-/
def piRight : N otimes[R] (forall i, M i) ≃ₗ[S] forall i, N otimes[R] M i :=
  LinearEquiv.ofLinearMap
    (piRightHom R S N M)
    (piRightInv R S N M)
    (by ext i x m j; simp [tmul_single])
    (by ext x j m; simp)

@[simp]
/--
lemma `piRight_apply` / 引理 `piRight_apply`

English:
lemma piRight_apply
  given: (x : N otimes[R] (forall i, M i))
  proof: by
  rfl

@[simp]

中文:
引理 piRight_apply
  条件: (x : N otimes[R] (对任意 i, M i))
  证明: by
  rfl

@[simp]
-/
lemma piRight_apply (x : N otimes[R] (forall i, M i)) :
    piRight R S N M x = piRightHom R S N M x := by
  rfl

@[simp]
/--
lemma `piRight_symm_apply` / 引理 `piRight_symm_apply`

English:
lemma piRight_symm_apply
  given: (x : N) (m : forall i, M i)
  proof: by
  simp [piRight]

@[simp]

中文:
引理 piRight_symm_apply
  条件: (x : N) (m : 对任意 i, M i)
  证明: by
  simp [piRight]

@[simp]

Depends on / 依赖: piRight
-/
lemma piRight_symm_apply (x : N) (m : forall i, M i) :
    (piRight R S N M).symm (fun i => x otimesₜ m i) = x otimesₜ m := by
  simp [piRight]

@[simp]
/--
lemma `piRight_symm_single` / 引理 `piRight_symm_single`

English:
lemma piRight_symm_single
  given: (x : N) (i : ι) (m : M i)
  proof: by
  simp [piRight]

中文:
引理 piRight_symm_single
  条件: (x : N) (i : ι) (m : M i)
  证明: by
  simp [piRight]

Depends on / 依赖: piRight
-/
lemma piRight_symm_single (x : N) (i : ι) (m : M i) :
    (piRight R S N M).symm (Pi.single i (x otimesₜ m)) = x otimesₜ Pi.single i m := by
  simp [piRight]

/--
Definition of `piLeft` / `piLeft` 的定义

English:
definition piLeft
  signature: : (forall i, M i) otimes[R] N ≃ₗ[R] forall i, M i otimes[R] N
  body: TensorProduct.comm .. ≪≫ₗ piRight .. ≪≫ₗ .piCongrRight fun _ => TensorProduct.comm ..

中文:
定义 piLeft
  签名: : (对任意 i, M i) otimes[R] N ≃ₗ[R] 对任意 i, M i otimes[R] N
  定义体: TensorProduct.comm .. ≪≫ₗ piRight .. ≪≫ₗ .piCongrRight fun _ => TensorProduct.comm ..
-/
@[simp] def piLeft : (forall i, M i) otimes[R] N ≃ₗ[R] forall i, M i otimes[R] N :=
  TensorProduct.comm .. ≪≫ₗ piRight .. ≪≫ₗ .piCongrRight fun _ => TensorProduct.comm ..

end

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `piScalarRightHomBil` / `piScalarRightHomBil` 的定义

English:
definition piScalarRightHomBil
  signature: : N ->ₗ[S] (ι -> R) ->ₗ[R] (ι -> N) where
  body: LinearMap.compLeft (toSpanSingleton R N n) ι
  map_add' x y := by
    ext i j
    simp
  map_smul' s x := by
    ext i j
    dsimp only [coe_comp, coe_single, Function.comp_apply, compLeft_apply, toSpanSingleton_apply,
      RingHom.id_apply, smul_apply, Pi.smul_apply]
    rw [← IsScalarTower.smul_assoc]; rw [_root_.Algebra.smul_def]; rw [mul_comm]; rw [mul_smul]
    simp

中文:
定义 piScalarRightHomBil
  签名: : N ->ₗ[S] (ι -> R) ->ₗ[R] (ι -> N) where
  定义体: LinearMap.compLeft (toSpanSingleton R N n) ι
  map_add' x y := by
    ext i j
    simp
  map_smul' s x := by
    ext i j
    dsimp only [coe_comp, coe_single, Function.comp_apply, compLeft_apply, toSpanSingleton_apply,
      RingHom.id_apply, smul_apply, Pi.smul_apply]
    rw [← IsScalarTower.smul_assoc]; rw [_root_.Algebra.smul_def]; rw [mul_comm]; rw [mul_smul]
    simp

Depends on / 依赖: LinearMap, LinearMap.compLeft, compLeft, toSpanSingleton
-/
def piScalarRightHomBil : N ->ₗ[S] (ι -> R) ->ₗ[R] (ι -> N) where
  toFun n := LinearMap.compLeft (toSpanSingleton R N n) ι
  map_add' x y := by
    ext i j
    simp
  map_smul' s x := by
    ext i j
    dsimp only [coe_comp, coe_single, Function.comp_apply, compLeft_apply, toSpanSingleton_apply,
      RingHom.id_apply, smul_apply, Pi.smul_apply]
    rw [← IsScalarTower.smul_assoc]; rw [_root_.Algebra.smul_def]; rw [mul_comm]; rw [mul_smul]
    simp

/--
Definition of `piScalarRightHom` / `piScalarRightHom` 的定义

English:
definition piScalarRightHom
  signature: : N otimes[R] (ι -> R) ->ₗ[S] (ι -> N)
  body: AlgebraTensorModule.lift piScalarRightHomBil R S N ι

@[simp]

中文:
定义 piScalarRightHom
  签名: : N otimes[R] (ι -> R) ->ₗ[S] (ι -> N)
  定义体: AlgebraTensorModule.lift piScalarRightHomBil R S N ι

@[simp]

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.lift, piScalarRightHomBil
-/
def piScalarRightHom : N otimes[R] (ι -> R) ->ₗ[S] (ι -> N) :=
AlgebraTensorModule.lift piScalarRightHomBil R S N ι

@[simp]
/--
lemma `piScalarRightHom_tmul` / 引理 `piScalarRightHom_tmul`

English:
lemma piScalarRightHom_tmul
  given: (x : N) (f : ι -> R)
  proof: by
  ext j
  simp [piScalarRightHom, piScalarRightHomBil]

中文:
引理 piScalarRightHom_tmul
  条件: (x : N) (f : ι -> R)
  证明: by
  ext j
  simp [piScalarRightHom, piScalarRightHomBil]

Depends on / 依赖: piScalarRightHom, piScalarRightHomBil
-/
lemma piScalarRightHom_tmul (x : N) (f : ι -> R) :
    piScalarRightHom R S N ι (x otimesₜ f) = (fun j => f j • x) := by
  ext j
  simp [piScalarRightHom, piScalarRightHomBil]

variable [Fintype ι] [DecidableEq ι]

/--
Definition of `piScalarRightInv` / `piScalarRightInv` 的定义

English:
definition piScalarRightInv
  signature: : (ι -> N) ->ₗ[S] N otimes[R] (ι -> R)
  body: LinearMap.lsum S (fun _ => N) S fun i => {
    toFun := fun n => n otimesₜ Pi.single i 1
    map_add' := fun x y => by simp [add_tmul]
    map_smul' := fun _ _ => rfl
  }

中文:
定义 piScalarRightInv
  签名: : (ι -> N) ->ₗ[S] N otimes[R] (ι -> R)
  定义体: LinearMap.lsum S (fun _ => N) S fun i => {
    toFun := fun n => n otimesₜ Pi.single i 1
    map_add' := fun x y => by simp [add_tmul]
    map_smul' := fun _ _ => rfl
  }

Depends on / 依赖: LinearMap, LinearMap.lsum, Pi.single, add_tmul, map_add, map_smul, single
-/
def piScalarRightInv : (ι -> N) ->ₗ[S] N otimes[R] (ι -> R) :=
LinearMap.lsum S (fun _ => N) S fun i => {
    toFun := fun n => n otimesₜ Pi.single i 1
    map_add' := fun x y => by simp [add_tmul]
    map_smul' := fun _ _ => rfl
  }

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `piScalarRightInv_single` / 引理 `piScalarRightInv_single`

English:
lemma piScalarRightInv_single
  given: (x : N) (i : ι)
  proof: by
  simp [piScalarRightInv, Pi.single_apply, TensorProduct.ite_tmul]

中文:
引理 piScalarRightInv_single
  条件: (x : N) (i : ι)
  证明: by
  simp [piScalarRightInv, Pi.single_apply, TensorProduct.ite_tmul]
-/
private lemma piScalarRightInv_single (x : N) (i : ι) :
    piScalarRightInv R S N ι (Pi.single i x) = x otimesₜ Pi.single i 1 := by
  simp [piScalarRightInv, Pi.single_apply, TensorProduct.ite_tmul]

/--
Definition of `piScalarRight` / `piScalarRight` 的定义

English:
definition piScalarRight
  signature: : N otimes[R] (ι -> R) ≃ₗ[S] (ι -> N)
  body: LinearEquiv.ofLinearMap
    (piScalarRightHom R S N ι)
    (piScalarRightInv R S N ι)
    (by ext i x j; simp [Pi.single_apply])
    (by ext x i; simp [Pi.single_apply_smul])

@[simp]

中文:
定义 piScalarRight
  签名: : N otimes[R] (ι -> R) ≃ₗ[S] (ι -> N)
  定义体: LinearEquiv.ofLinearMap
    (piScalarRightHom R S N ι)
    (piScalarRightInv R S N ι)
    (by ext i x j; simp [Pi.single_apply])
    (by ext x i; simp [Pi.single_apply_smul])

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.ofLinearMap, Pi.single_apply, Pi.single_apply_smul, ofLinearMap, piScalarRightHom, piScalarRightInv, single_apply, single_apply_smul
-/
def piScalarRight : N otimes[R] (ι -> R) ≃ₗ[S] (ι -> N) :=
  LinearEquiv.ofLinearMap
    (piScalarRightHom R S N ι)
    (piScalarRightInv R S N ι)
    (by ext i x j; simp [Pi.single_apply])
    (by ext x i; simp [Pi.single_apply_smul])

@[simp]
/--
lemma `piScalarRight_apply` / 引理 `piScalarRight_apply`

English:
lemma piScalarRight_apply
  given: (x : N otimes[R] (ι -> R))
  proof: by
  rfl

@[simp]

中文:
引理 piScalarRight_apply
  条件: (x : N otimes[R] (ι -> R))
  证明: by
  rfl

@[simp]
-/
lemma piScalarRight_apply (x : N otimes[R] (ι -> R)) :
    piScalarRight R S N ι x = piScalarRightHom R S N ι x := by
  rfl

@[simp]
/--
lemma `piScalarRight_symm_single` / 引理 `piScalarRight_symm_single`

English:
lemma piScalarRight_symm_single
  given: (x : N) (i : ι)
  proof: by
  simp [piScalarRight]

中文:
引理 piScalarRight_symm_single
  条件: (x : N) (i : ι)
  证明: by
  simp [piScalarRight]

Depends on / 依赖: piScalarRight
-/
lemma piScalarRight_symm_single (x : N) (i : ι) :
    (piScalarRight R S N ι).symm (Pi.single i x) = x otimesₜ Pi.single i 1 := by
  simp [piScalarRight]

-- See also `TensorProduct.piScalarRight_symm_algebraMap` in
-- `Mathlib/RingTheory/TensorProduct/Pi.lean`.

end TensorProduct
