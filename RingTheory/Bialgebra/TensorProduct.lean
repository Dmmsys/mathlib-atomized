/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Andrew Yang
-/
module

public import Mathlib.RingTheory.Bialgebra.Equiv
public import Mathlib.RingTheory.Coalgebra.TensorProduct
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Tensor products of bialgebras

We define the data in the monoidal structure on the category of bialgebras - e.g. the bialgebra
instance on a tensor product of bialgebras, and the tensor product of two `BialgHom`s as a
`BialgHom`. This is done by combining the corresponding API for coalgebras and algebras.

-/

public noncomputable section

open Coalgebra
open scoped TensorProduct

namespace Bialgebra.TensorProduct

open Coalgebra.TensorProduct

variable {R S A B C D : Type*} [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

section Heterogeneous
variable (R S A B) [Bialgebra S A] [Bialgebra R B] [Algebra R A] [Algebra R S] [IsScalarTower R S A]

/--
lemma `counit_eq_algHom_toLinearMap` / 引理 `counit_eq_algHom_toLinearMap`

English:
lemma counit_eq_algHom_toLinearMap
  proof: rfl

中文:
引理 counit_eq_algHom_toLinearMap
  证明: rfl

Depends on / 依赖: otimes
-/
lemma counit_eq_algHom_toLinearMap :
    Coalgebra.counit (R := S) (A := A otimes[R] B) =
      ((Algebra.TensorProduct.rid _ _ _).toAlgHom.comp (Algebra.TensorProduct.map
      (Bialgebra.counitAlgHom S A) (Bialgebra.counitAlgHom R B))).toLinearMap :=
  rfl

/--
lemma `comul_eq_algHom_toLinearMap` / 引理 `comul_eq_algHom_toLinearMap`

English:
lemma comul_eq_algHom_toLinearMap
  proof: rfl

中文:
引理 comul_eq_algHom_toLinearMap
  证明: rfl

Depends on / 依赖: otimes
-/
lemma comul_eq_algHom_toLinearMap :
    Coalgebra.comul (R := S) (A := A otimes[R] B) =
      ((Algebra.TensorProduct.tensorTensorTensorComm R S R S A A B B).toAlgHom.comp
      (Algebra.TensorProduct.map (Bialgebra.comulAlgHom S A)
      (Bialgebra.comulAlgHom R B))).toLinearMap :=
  rfl

/--
Instance `_root_.TensorProduct.instBialgebra` / 实例 `_root_.TensorProduct.instBialgebra`

English:
instance _root_.TensorProduct.instBialgebra
  signature: : Bialgebra S (A otimes[R] B)
  body: by
  have hcounit := congr(DFunLike.coe $(counit_eq_algHom_toLinearMap R S A B))
  have hcomul := congr(DFunLike.coe $(comul_eq_algHom_toLinearMap R S A B))
  refine Bialgebra.mk' S (A otimes[R] B) ?_ (fun {x y} => ?_) ?_ (fun {x y} => ?_) <;>
  simp_all only [AlgHom.toLinearMap_apply] <;>
  simp on

中文:
实例 _root_.张量积.instBialgebra
  签名: : 双代数 S (A otimes[R] B)
  定义体: by
  have hcounit := congr(DFunLike.coe $(counit_eq_algHom_toLinearMap R S A B))
  have hcomul := congr(DFunLike.coe $(comul_eq_algHom_toLinearMap R S A B))
  refine Bialgebra.mk' S (A otimes[R] B) ?_ (fun {x y} => ?_) ?_ (fun {x y} => ?_) <;>
  simp_all only [AlgHom.toLinearMap_apply] <;>
  simp on

Depends on / 依赖: AlgHom, AlgHom.toLinearMap_apply, Bialgebra, Bialgebra.mk, DFunLike, DFunLike.coe, comul_eq_algHom_toLinearMap, counit_eq_algHom_toLinearMap, hcomul, hcounit, map_mul, map_one, otimes, toLinearMap_apply
-/
noncomputable instance _root_.TensorProduct.instBialgebra : Bialgebra S (A otimes[R] B) := by
  have hcounit := congr(DFunLike.coe $(counit_eq_algHom_toLinearMap R S A B))
  have hcomul := congr(DFunLike.coe $(comul_eq_algHom_toLinearMap R S A B))
  refine Bialgebra.mk' S (A otimes[R] B) ?_ (fun {x y} => ?_) ?_ (fun {x y} => ?_) <;>
  simp_all only [AlgHom.toLinearMap_apply] <;>
  simp only [map_one, map_mul]

/--
lemma `counitAlgHom_def` / 引理 `counitAlgHom_def`

English:
lemma counitAlgHom_def
  proof: rfl

中文:
引理 counitAlgHom_def
  证明: rfl

Depends on / 依赖: otimes
-/
lemma counitAlgHom_def :
    counitAlgHom (R := S) (A := A otimes[R] B) =
      (Algebra.TensorProduct.rid _ _ _).toAlgHom.comp (Algebra.TensorProduct.map
      (Bialgebra.counitAlgHom S A) (Bialgebra.counitAlgHom R B)) := rfl

/--
lemma `comulAlgHom_def` / 引理 `comulAlgHom_def`

English:
lemma comulAlgHom_def
  proof: rfl

中文:
引理 comulAlgHom_def
  证明: rfl

Depends on / 依赖: otimes
-/
lemma comulAlgHom_def :
    comulAlgHom (R := S) (A := A otimes[R] B) =
      (Algebra.TensorProduct.tensorTensorTensorComm R S R S A A B B).toAlgHom.comp
        (Algebra.TensorProduct.map (Bialgebra.comulAlgHom S A)
        (Bialgebra.comulAlgHom R B)) := rfl

variable {R S A B}

variable [Semiring C] [Semiring D] [Bialgebra S C]
  [Bialgebra R D] [Algebra R C] [IsScalarTower R S C]

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : A ->ₐc[S] C) (g : B ->ₐc[R] D)
  body: { Coalgebra.TensorProduct.map (f : A ->ₗc[S] C) (g : B ->ₗc[R] D),
    Algebra.TensorProduct.map (f : A ->ₐ[S] C) (g : B ->ₐ[R] D) with }

@[simp]

中文:
定义 map
  签名: (f : A ->ₐc[S] C) (g : B ->ₐc[R] D)
  定义体: { Coalgebra.TensorProduct.map (f : A ->ₗc[S] C) (g : B ->ₗc[R] D),
    Algebra.TensorProduct.map (f : A ->ₐ[S] C) (g : B ->ₐ[R] D) with }

@[simp]
-/
@[expose] def map (f : A ->ₐc[S] C) (g : B ->ₐc[R] D) : A otimes[R] B ->ₐc[S] C otimes[R] D :=
  { Coalgebra.TensorProduct.map (f : A ->ₗc[S] C) (g : B ->ₗc[R] D),
    Algebra.TensorProduct.map (f : A ->ₐ[S] C) (g : B ->ₐ[R] D) with }

@[simp]
/--
theorem `map_tmul` / 定理 `map_tmul`

English:
theorem map_tmul
  given: (f : A ->ₐc[S] C) (g : B ->ₐc[R] D) (x : A) (y : B)
  proof: rfl

@[simp]

中文:
定理 map_tmul
  条件: (f : A ->ₐc[S] C) (g : B ->ₐc[R] D) (x : A) (y : B)
  证明: rfl

@[simp]
-/
theorem map_tmul (f : A ->ₐc[S] C) (g : B ->ₐc[R] D) (x : A) (y : B) :
    map f g (x otimesₜ y) = f x otimesₜ g y :=
  rfl

@[simp]
/--
theorem `map_toCoalgHom` / 定理 `map_toCoalgHom`

English:
theorem map_toCoalgHom
  given: (f : A ->ₐc[S] C) (g : B ->ₐc[R] D)
  proof: rfl

@[simp]

中文:
定理 map_toCoalgHom
  条件: (f : A ->ₐc[S] C) (g : B ->ₐc[R] D)
  证明: rfl

@[simp]
-/
theorem map_toCoalgHom (f : A ->ₐc[S] C) (g : B ->ₐc[R] D) :
    map f g = Coalgebra.TensorProduct.map (f : A ->ₗc[S] C) (g : B ->ₗc[R] D) := rfl

@[simp]
/--
theorem `map_toAlgHom` / 定理 `map_toAlgHom`

English:
theorem map_toAlgHom
  given: (f : A ->ₐc[S] C) (g : B ->ₐc[R] D)
  proof: rfl

中文:
定理 map_toAlgHom
  条件: (f : A ->ₐc[S] C) (g : B ->ₐc[R] D)
  证明: rfl
-/
theorem map_toAlgHom (f : A ->ₐc[S] C) (g : B ->ₐc[R] D) :
    (map f g : A otimes[R] B ->ₐ[S] C otimes[R] D) =
      Algebra.TensorProduct.map (f : A ->ₐ[S] C) (g : B ->ₐ[R] D) :=
  rfl

variable (R S A C D) in
/--
Definition of `assoc` / `assoc` 的定义

English:
definition assoc
  signature: : (A otimes[S] C) otimes[R] D ≃ₐc[S] A otimes[S] (C otimes[R] D)
  body: { Coalgebra.TensorProduct.assoc R S A C D, Algebra.TensorProduct.assoc R S S A C D with }

@[simp]

中文:
定义 assoc
  签名: : (A otimes[S] C) otimes[R] D ≃ₐc[S] A otimes[S] (C otimes[R] D)
  定义体: { Coalgebra.TensorProduct.assoc R S A C D, Algebra.TensorProduct.assoc R S S A C D with }

@[simp]
-/
@[expose] protected def assoc : (A otimes[S] C) otimes[R] D ≃ₐc[S] A otimes[S] (C otimes[R] D) :=
  { Coalgebra.TensorProduct.assoc R S A C D, Algebra.TensorProduct.assoc R S S A C D with }

@[simp]
/--
theorem `assoc_tmul` / 定理 `assoc_tmul`

English:
theorem assoc_tmul
  given: (x : A) (y : C) (z : D)
  proof: rfl

@[simp]

中文:
定理 assoc_tmul
  条件: (x : A) (y : C) (z : D)
  证明: rfl

@[simp]
-/
theorem assoc_tmul (x : A) (y : C) (z : D) :
    Bialgebra.TensorProduct.assoc R S A C D ((x otimesₜ y) otimesₜ z) = x otimesₜ (y otimesₜ z) :=
  rfl

@[simp]
/--
theorem `assoc_symm_tmul` / 定理 `assoc_symm_tmul`

English:
theorem assoc_symm_tmul
  given: (x : A) (y : C) (z : D)
  proof: rfl

@[simp]

中文:
定理 assoc_symm_tmul
  条件: (x : A) (y : C) (z : D)
  证明: rfl

@[simp]
-/
theorem assoc_symm_tmul (x : A) (y : C) (z : D) :
    (Bialgebra.TensorProduct.assoc R S A C D).symm (x otimesₜ (y otimesₜ z)) = (x otimesₜ y) otimesₜ z :=
  rfl

@[simp]
/--
theorem `assoc_toCoalgEquiv` / 定理 `assoc_toCoalgEquiv`

English:
theorem assoc_toCoalgEquiv
  proof: rfl

@[simp]

中文:
定理 assoc_toCoalgEquiv
  证明: rfl

@[simp]
-/
theorem assoc_toCoalgEquiv :
    (Bialgebra.TensorProduct.assoc R S A C D : _ ≃ₗc[S] _) =
    Coalgebra.TensorProduct.assoc R S A C D := rfl

@[simp]
/--
theorem `assoc_toAlgEquiv` / 定理 `assoc_toAlgEquiv`

English:
theorem assoc_toAlgEquiv
  proof: rfl

中文:
定理 assoc_toAlgEquiv
  证明: rfl
-/
theorem assoc_toAlgEquiv :
    (Bialgebra.TensorProduct.assoc R S A C D : _ ≃ₐ[S] _) =
    Algebra.TensorProduct.assoc R S S A C D := rfl

variable (R B) in
/--
Definition of `lid` / `lid` 的定义

English:
definition lid
  signature: : R otimes[R] B ≃ₐc[R] B
  body: { Coalgebra.TensorProduct.lid R B, Algebra.TensorProduct.lid R B with }

@[simp]

中文:
定义 lid
  签名: : R otimes[R] B ≃ₐc[R] B
  定义体: { Coalgebra.TensorProduct.lid R B, Algebra.TensorProduct.lid R B with }

@[simp]
-/
@[expose] protected def lid : R otimes[R] B ≃ₐc[R] B :=
  { Coalgebra.TensorProduct.lid R B, Algebra.TensorProduct.lid R B with }

@[simp]
/--
theorem `lid_toCoalgEquiv` / 定理 `lid_toCoalgEquiv`

English:
theorem lid_toCoalgEquiv
  proof: rfl

@[simp]

中文:
定理 lid_toCoalgEquiv
  证明: rfl

@[simp]
-/
theorem lid_toCoalgEquiv :
    (Bialgebra.TensorProduct.lid R B : R otimes[R] B ≃ₗc[R] B) = Coalgebra.TensorProduct.lid R B := rfl

@[simp]
/--
theorem `lid_toAlgEquiv` / 定理 `lid_toAlgEquiv`

English:
theorem lid_toAlgEquiv
  proof: rfl

@[simp]

中文:
定理 lid_toAlgEquiv
  证明: rfl

@[simp]
-/
theorem lid_toAlgEquiv :
    (Bialgebra.TensorProduct.lid R B : R otimes[R] B ≃ₐ[R] B) = Algebra.TensorProduct.lid R B := rfl

@[simp]
/--
theorem `lid_tmul` / 定理 `lid_tmul`

English:
theorem lid_tmul
  given: (r : R) (a : B)
  statement: Bialgebra.TensorProduct.lid R B (r otimesₜ a) = r • a
  proof: rfl

@[simp]

中文:
定理 lid_tmul
  条件: (r : R) (a : B)
  结论: 双代数.张量积.lid R B (r otimesₜ a) = r • a
  证明: rfl

@[simp]
-/
theorem lid_tmul (r : R) (a : B) : Bialgebra.TensorProduct.lid R B (r otimesₜ a) = r • a := rfl

@[simp]
/--
theorem `lid_symm_apply` / 定理 `lid_symm_apply`

English:
theorem lid_symm_apply
  given: (a : B)
  statement: (Bialgebra.TensorProduct.lid R B).symm a = 1 otimesₜ a
  proof: rfl

中文:
定理 lid_symm_apply
  条件: (a : B)
  结论: (双代数.张量积.lid R B).symm a = 1 otimesₜ a
  证明: rfl
-/
theorem lid_symm_apply (a : B) : (Bialgebra.TensorProduct.lid R B).symm a = 1 otimesₜ a := rfl

/--
theorem `coalgebra_rid_eq_algebra_rid_apply` / 定理 `coalgebra_rid_eq_algebra_rid_apply`

English:
theorem coalgebra_rid_eq_algebra_rid_apply
  given: (x : A otimes[R] R)
  proof: rfl

中文:
定理 coalgebra_rid_eq_algebra_rid_apply
  条件: (x : A otimes[R] R)
  证明: rfl
-/
theorem coalgebra_rid_eq_algebra_rid_apply (x : A otimes[R] R) :
    Coalgebra.TensorProduct.rid R S A x = Algebra.TensorProduct.rid R R A x := rfl

variable (R S A) in
/--
Definition of `rid` / `rid` 的定义

English:
definition rid
  signature: : A otimes[R] R ≃ₐc[S] A where
  body: Coalgebra.TensorProduct.rid R S A
  map_mul' x y := by
    simp only [CoalgEquiv.toCoalgHom_eq_coe, CoalgHom.toLinearMap_eq_coe, AddHom.toFun_eq_coe,
      LinearMap.coe_toAddHom, CoalgHom.coe_toLinearMap, CoalgHom.coe_coe,
      coalgebra_rid_eq_algebra_rid_apply, map_mul]

@[simp]

中文:
定义 rid
  签名: : A otimes[R] R ≃ₐc[S] A where
  定义体: Coalgebra.TensorProduct.rid R S A
  map_mul' x y := by
    simp only [CoalgEquiv.toCoalgHom_eq_coe, CoalgHom.toLinearMap_eq_coe, AddHom.toFun_eq_coe,
      LinearMap.coe_toAddHom, CoalgHom.coe_toLinearMap, CoalgHom.coe_coe,
      coalgebra_rid_eq_algebra_rid_apply, map_mul]

@[simp]
-/
@[expose] protected def rid : A otimes[R] R ≃ₐc[S] A where
  toCoalgEquiv := Coalgebra.TensorProduct.rid R S A
  map_mul' x y := by
    simp only [CoalgEquiv.toCoalgHom_eq_coe, CoalgHom.toLinearMap_eq_coe, AddHom.toFun_eq_coe,
      LinearMap.coe_toAddHom, CoalgHom.coe_toLinearMap, CoalgHom.coe_coe,
      coalgebra_rid_eq_algebra_rid_apply, map_mul]

@[simp]
/--
theorem `rid_toCoalgEquiv` / 定理 `rid_toCoalgEquiv`

English:
theorem rid_toCoalgEquiv
  proof: rfl

@[simp]

中文:
定理 rid_toCoalgEquiv
  证明: rfl

@[simp]
-/
theorem rid_toCoalgEquiv :
    (TensorProduct.rid R S A : A otimes[R] R ≃ₗc[S] A) = Coalgebra.TensorProduct.rid R S A := rfl

@[simp]
/--
theorem `rid_toAlgEquiv` / 定理 `rid_toAlgEquiv`

English:
theorem rid_toAlgEquiv
  proof: by
  ext x
  exact coalgebra_rid_eq_algebra_rid_apply x

@[simp]

中文:
定理 rid_toAlgEquiv
  证明: by
  ext x
  exact coalgebra_rid_eq_algebra_rid_apply x

@[simp]

Depends on / 依赖: coalgebra_rid_eq_algebra_rid_apply
-/
theorem rid_toAlgEquiv :
    (Bialgebra.TensorProduct.rid R S A : A otimes[R] R ≃ₐ[S] A) = Algebra.TensorProduct.rid R S A := by
  ext x
  exact coalgebra_rid_eq_algebra_rid_apply x

@[simp]
/--
theorem `rid_tmul` / 定理 `rid_tmul`

English:
theorem rid_tmul
  given: (r : R) (a : A)
  statement: Bialgebra.TensorProduct.rid R S A (a otimesₜ r) = r • a
  proof: rfl

@[simp]

中文:
定理 rid_tmul
  条件: (r : R) (a : A)
  结论: 双代数.张量积.rid R S A (a otimesₜ r) = r • a
  证明: rfl

@[simp]
-/
theorem rid_tmul (r : R) (a : A) : Bialgebra.TensorProduct.rid R S A (a otimesₜ r) = r • a := rfl

@[simp]
/--
theorem `rid_symm_apply` / 定理 `rid_symm_apply`

English:
theorem rid_symm_apply
  given: (a : A)
  statement: (Bialgebra.TensorProduct.rid R S A).symm a = a otimesₜ 1
  proof: rfl

中文:
定理 rid_symm_apply
  条件: (a : A)
  结论: (双代数.张量积.rid R S A).symm a = a otimesₜ 1
  证明: rfl
-/
theorem rid_symm_apply (a : A) : (Bialgebra.TensorProduct.rid R S A).symm a = a otimesₜ 1 := rfl

end Heterogeneous

section Homogeneous
variable (R S A B) [Bialgebra R A] [Bialgebra R B]

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `comm` / `comm` 的定义

English:
definition comm
  signature: : A otimes[R] B ≃ₐc[R] B otimes[R] A
  body: .ofAlgEquiv (Algebra.TensorProduct.comm R A B) (by ext <;> simp) by
    ext a <;>
    · dsimp
      rw [← (ℛ R a).eq]
      simp [TensorProduct.tmul_sum, TensorProduct.sum_tmul, Algebra.TensorProduct.one_def]

中文:
定义 comm
  签名: : A otimes[R] B ≃ₐc[R] B otimes[R] A
  定义体: .ofAlgEquiv (Algebra.TensorProduct.comm R A B) (by ext <;> simp) by
    ext a <;>
    · dsimp
      rw [← (ℛ R a).eq]
      simp [TensorProduct.tmul_sum, TensorProduct.sum_tmul, Algebra.TensorProduct.one_def]
-/
@[expose] def comm : A otimes[R] B ≃ₐc[R] B otimes[R] A :=
.ofAlgEquiv (Algebra.TensorProduct.comm R A B) (by ext <;> simp) by
    ext a <;>
    · dsimp
      rw [← (ℛ R a).eq]
      simp [TensorProduct.tmul_sum, TensorProduct.sum_tmul, Algebra.TensorProduct.one_def]

end Homogeneous
end Bialgebra.TensorProduct

namespace BialgHom

variable {R A B C : Type*} [CommRing R] [Ring A] [Ring B] [Ring C]
    [Bialgebra R A] [Bialgebra R B] [Bialgebra R C]

variable (A)

/--
Definition of `lTensor` / `lTensor` 的定义

English:
abbreviation lTensor
  signature: (f : B ->ₐc[R] C)
  body: Bialgebra.TensorProduct.map (BialgHom.id R A) f

中文:
缩写 lTensor
  签名: (f : B ->ₐc[R] C)
  定义体: Bialgebra.TensorProduct.map (BialgHom.id R A) f

Depends on / 依赖: BialgHom, BialgHom.id, Bialgebra, Bialgebra.TensorProduct.map, TensorProduct
-/
abbrev lTensor (f : B ->ₐc[R] C) : A otimes[R] B ->ₐc[R] A otimes[R] C :=
  Bialgebra.TensorProduct.map (BialgHom.id R A) f

/--
Definition of `rTensor` / `rTensor` 的定义

English:
abbreviation rTensor
  signature: (f : B ->ₐc[R] C)
  body: Bialgebra.TensorProduct.map f (BialgHom.id R A)

中文:
缩写 rTensor
  签名: (f : B ->ₐc[R] C)
  定义体: Bialgebra.TensorProduct.map f (BialgHom.id R A)

Depends on / 依赖: BialgHom, BialgHom.id, Bialgebra, Bialgebra.TensorProduct.map, TensorProduct
-/
abbrev rTensor (f : B ->ₐc[R] C) : B otimes[R] A ->ₐc[R] C otimes[R] A :=
  Bialgebra.TensorProduct.map f (BialgHom.id R A)

end BialgHom

namespace Bialgebra
variable {R A B ι κ : Type*} [CommSemiring R]

section Semiring
variable [Semiring A] [Bialgebra R A] [Semiring B] [Bialgebra R B] {a : A} {b : B}

variable (R A) in
/--
Definition of `comulBialgHom` / `comulBialgHom` 的定义

English:
definition comulBialgHom
  signature: [IsCocomm R A]
  body: comulAlgHom R A
  __ := comulCoalgHom R A

中文:
定义 comulBialgHom
  签名: [是余comm R A]
  定义体: comulAlgHom R A
  __ := comulCoalgHom R A
-/
@[expose] def comulBialgHom [IsCocomm R A] : A ->ₐc[R] A otimes[R] A where
  __ := comulAlgHom R A
  __ := comulCoalgHom R A

/--
lemma `comm_comp_comulBialgHom` / 引理 `comm_comp_comulBialgHom`

English:
lemma comm_comp_comulBialgHom
  given: [IsCocomm R A]
  proof: by
  ext; exact comm_comul _ _

中文:
引理 comm_comp_comulBialgHom
  条件: [是余comm R A]
  证明: by
  ext; exact comm_comul _ _

Depends on / 依赖: comm_comul
-/
lemma comm_comp_comulBialgHom [IsCocomm R A] :
    (TensorProduct.comm R A A).toBialgHom.comp (comulBialgHom R A) = comulBialgHom R A := by
  ext; exact comm_comul _ _

variable (R A) in
/-- Multiplication on a bialgebra as a coalgebra hom. -/
@[expose]
/--
Definition of `mulCoalgHom` / `mulCoalgHom` 的定义

English:
definition mulCoalgHom
  signature: : A otimes[R] A ->ₗc[R] A where
  body: .mul' R A
  counit_comp := by ext; simp [mul_comm]
  map_comp_comul := by
    ext a b
    simp [← (ℛ R a).eq, ← (ℛ R b).eq, TensorProduct.sum_tmul]
    simp [TensorProduct.tmul_sum, Finset.sum_mul_sum]

中文:
定义 mulCoalgHom
  签名: : A otimes[R] A ->ₗc[R] A where
  定义体: .mul' R A
  counit_comp := by ext; simp [mul_comm]
  map_comp_comul := by
    ext a b
    simp [← (ℛ R a).eq, ← (ℛ R b).eq, TensorProduct.sum_tmul]
    simp [TensorProduct.tmul_sum, Finset.sum_mul_sum]
-/
def mulCoalgHom : A otimes[R] A ->ₗc[R] A where
  toLinearMap := .mul' R A
  counit_comp := by ext; simp [mul_comm]
  map_comp_comul := by
    ext a b
    simp [← (ℛ R a).eq, ← (ℛ R b).eq, TensorProduct.sum_tmul]
    simp [TensorProduct.tmul_sum, Finset.sum_mul_sum]

-- TODO: Generate this using `simps` once the coercion from `LinearMapClass` is gone.
@[simp]
/--
lemma `toLinearMap_mulCoalgHom` / 引理 `toLinearMap_mulCoalgHom`

English:
lemma toLinearMap_mulCoalgHom
  statement: mulCoalgHom R A = LinearMap.mul' R A
  proof: rfl

中文:
引理 toLinearMap_mulCoalgHom
  结论: mulCoalgHom R A = 线性映射.mul' R A
  证明: rfl
-/
lemma toLinearMap_mulCoalgHom : mulCoalgHom R A = LinearMap.mul' R A := rfl

/--
lemma `coe_mulCoalgHom` / 引理 `coe_mulCoalgHom`

English:
lemma coe_mulCoalgHom
  statement: ⇑(mulCoalgHom R A) = LinearMap.mul' R A
  proof: rfl

中文:
引理 coe_mulCoalgHom
  结论: ⇑(mulCoalgHom R A) = 线性映射.mul' R A
  证明: rfl
-/
@[simp] lemma coe_mulCoalgHom : ⇑(mulCoalgHom R A) = LinearMap.mul' R A := rfl

/-- Representations of `a` and `b` yield a representation of `a ⊗ b`. -/
@[expose, simps]
/--
Definition of `_root_.Coalgebra.Repr.tmul` / `_root_.Coalgebra.Repr.tmul` 的定义

English:
definition _root_.Coalgebra.Repr.tmul
  signature: (ℛa : Coalgebra.Repr R a ι) (ℛb : Coalgebra.Repr R b κ)
  body: ℛa.index ×ˢ ℛb.index
  left i := ℛa.left i.1 otimesₜ ℛb.left i.2
  right i := ℛa.right i.1 otimesₜ ℛb.right i.2
  eq := by
    simp [← ℛa.eq, ← ℛb.eq, TensorProduct.sum_tmul ℛa.index, TensorProduct.tmul_sum,
      ← Finset.sum_product']

中文:
定义 _root_.余algebra.Repr.tmul
  签名: (ℛa : 余algebra.Repr R a ι) (ℛb : 余algebra.Repr R b κ)
  定义体: ℛa.index ×ˢ ℛb.index
  left i := ℛa.left i.1 otimesₜ ℛb.left i.2
  right i := ℛa.right i.1 otimesₜ ℛb.right i.2
  eq := by
    simp [← ℛa.eq, ← ℛb.eq, TensorProduct.sum_tmul ℛa.index, TensorProduct.tmul_sum,
      ← Finset.sum_product']
-/
protected def _root_.Coalgebra.Repr.tmul (ℛa : Coalgebra.Repr R a ι) (ℛb : Coalgebra.Repr R b κ) :
    Coalgebra.Repr R (a otimesₜ[R] b) (ι × κ) where
  index := ℛa.index ×ˢ ℛb.index
  left i := ℛa.left i.1 otimesₜ ℛb.left i.2
  right i := ℛa.right i.1 otimesₜ ℛb.right i.2
  eq := by
    simp [← ℛa.eq, ← ℛb.eq, TensorProduct.sum_tmul ℛa.index, TensorProduct.tmul_sum,
      ← Finset.sum_product']

/-- Representations of `a` and `b` yield a representation of `a * b`. -/
@[expose, simps! left right index] protected
/--
Definition of `_root_.Coalgebra.Repr.mul` / `_root_.Coalgebra.Repr.mul` 的定义

English:
definition _root_.Coalgebra.Repr.mul
  signature: {b : A} (ℛ₁ : Coalgebra.Repr R a ι) (ℛ₂ : Coalgebra.Repr R b κ)
  body: (ℛ₁.tmul ℛ₂).induced (R := R) (mulCoalgHom R A)

中文:
定义 _root_.余algebra.Repr.mul
  签名: {b : A} (ℛ₁ : 余algebra.Repr R a ι) (ℛ₂ : 余algebra.Repr R b κ)
  定义体: (ℛ₁.tmul ℛ₂).induced (R := R) (mulCoalgHom R A)

Depends on / 依赖: induced, mulCoalgHom
-/
def _root_.Coalgebra.Repr.mul {b : A} (ℛ₁ : Coalgebra.Repr R a ι) (ℛ₂ : Coalgebra.Repr R b κ) :
    Coalgebra.Repr R (a * b) (ι × κ) := (ℛ₁.tmul ℛ₂).induced (R := R) (mulCoalgHom R A)

end Semiring

@[simp]
/--
lemma `counitAlgHom_comp_includeRight` / 引理 `counitAlgHom_comp_includeRight`

English:
lemma counitAlgHom_comp_includeRight
  given: [CommSemiring A] [Semiring B] [Algebra R A] [Bialgebra R B]
  proof: by
  ext; simp [Algebra.algebraMap_eq_smul_one]

中文:
引理 counitAlgHom_comp_includeRight
  条件: [交换半环 A] [半环 B] [代数 R A] [双代数 R B]
  证明: by
  ext; simp [Algebra.algebraMap_eq_smul_one]

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, algebraMap_eq_smul_one
-/
lemma counitAlgHom_comp_includeRight [CommSemiring A] [Semiring B] [Algebra R A] [Bialgebra R B] :
    ((counitAlgHom A (A otimes[R] B)).restrictScalars R).comp Algebra.TensorProduct.includeRight =
      (Algebra.ofId R A).comp (counitAlgHom R B) := by
  ext; simp [Algebra.algebraMap_eq_smul_one]

/--
lemma `comul_includeRight` / 引理 `comul_includeRight`

English:
lemma comul_includeRight
  given: [CommSemiring A] [CommSemiring B] [Bialgebra R B] [Algebra R A]
  proof: by
  ext x; simp [← (ℛ R x).eq, TensorProduct.tmul_sum]

中文:
引理 comul_includeRight
  条件: [交换半环 A] [交换半环 B] [双代数 R B] [代数 R A]
  证明: by
  ext x; simp [← (ℛ R x).eq, TensorProduct.tmul_sum]
-/
lemma comul_includeRight [CommSemiring A] [CommSemiring B] [Bialgebra R B] [Algebra R A] :
    (RingHomClass.toRingHom (Bialgebra.comulAlgHom A (A otimes[R] B))).comp
      (RingHomClass.toRingHom Algebra.TensorProduct.includeRight) =
      (Algebra.TensorProduct.mapRingHom (algebraMap R A)
        (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight (A := A)))
        (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight (A := A)))
        (by simp [← IsScalarTower.algebraMap_eq])
        (by simp [← IsScalarTower.algebraMap_eq])).comp
        (RingHomClass.toRingHom (Bialgebra.comulAlgHom R B)) := by
  ext x; simp [← (ℛ R x).eq, TensorProduct.tmul_sum]

section CommSemiring
variable [CommSemiring A] [Bialgebra R A]

variable (R A) in
/-- Multiplication on a commutative bialgebra as a bialgebra hom. -/
@[expose, simps toCoalgHom]
/--
Definition of `mulBialgHom` / `mulBialgHom` 的定义

English:
definition mulBialgHom
  signature: : A otimes[R] A ->ₐc[R] A where
  body: mulCoalgHom R A
  __ := Algebra.TensorProduct.lmul' R

@[simp]

中文:
定义 mulBialgHom
  签名: : A otimes[R] A ->ₐc[R] A where
  定义体: mulCoalgHom R A
  __ := Algebra.TensorProduct.lmul' R

@[simp]

Depends on / 依赖: mulCoalgHom
-/
def mulBialgHom : A otimes[R] A ->ₐc[R] A where
  toCoalgHom := mulCoalgHom R A
  __ := Algebra.TensorProduct.lmul' R

@[simp]
/--
lemma `mulBialgHom_toAlgHom` / 引理 `mulBialgHom_toAlgHom`

English:
lemma mulBialgHom_toAlgHom
  statement: (mulBialgHom R A).toAlgHom = Algebra.TensorProduct.lmul' R
  proof: rfl

中文:
引理 mulBialgHom_toAlgHom
  结论: (mulBialgHom R A).toAlgHom = 代数.张量积.lmul' R
  证明: rfl
-/
lemma mulBialgHom_toAlgHom : (mulBialgHom R A).toAlgHom = Algebra.TensorProduct.lmul' R := rfl

/--
lemma `coe_mulBialgHom` / 引理 `coe_mulBialgHom`

English:
lemma coe_mulBialgHom
  statement: ⇑(mulBialgHom R A) = LinearMap.mul' R A
  proof: rfl

中文:
引理 coe_mulBialgHom
  结论: ⇑(mulBialgHom R A) = 线性映射.mul' R A
  证明: rfl
-/
@[simp] lemma coe_mulBialgHom : ⇑(mulBialgHom R A) = LinearMap.mul' R A := rfl

end CommSemiring
end Bialgebra
