/-
Copyright (c) 2025 Antoine Chambert-Loir and María-Inés de Frutos Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María-Inés de Frutos Fernández
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Adjoin.FG

/-! # Tensor products and finitely generated submodules

Various results about how tensor products of arbitrary modules are direct limits of
tensor products of finitely-generated modules.

## Main definitions

* `Submodule.FG.directedSystem`, the directed system of finitely generated submodules of a module.

* `Submodule.FG.directLimit` proves that a module is the direct limit
  of its finitely generated submodules, with respect to the inclusion maps

* `DirectedSystem.rTensor`, the directed system deduced from a directed system of modules
  by applying `rTensor`.

* `Submodule.FG.rTensor.directSystem`, the directed system of
  modules `P ⊗[R] N`, for all finitely generated
  submodules `P`, with respect to the maps deduced from the inclusions

* `Submodule.FG.rTensor.directLimit` : a tensor product `M ⊗[R] N` is the direct limit
  of the modules `P ⊗[R] N`, where `P` ranges over all finitely generated submodules of `M`,
  as a linear equivalence.

* `DirectedSystem.lTensor`, the directed system deduced from a directed system of modules
  by applying `lTensor`.

* `Submodule.FG.lTensor.directSystem`, the directed system of
  modules `M ⊗[R] Q`, for all finitely generated
  submodules `Q`, with respect to the maps deduced from the inclusions

* `Submodule.FG.lTensor.directLimit` : a tensor product `M ⊗[R] N` is the direct limit
  of the modules `M ⊗[R] Q`, where `Q` ranges over all finitely generated submodules of `N`,
  as a linear equivalence.
-/

@[expose] public section

open Submodule LinearMap

section Semiring

universe u v
variable {R : Type u} [Semiring R] {M : Type*} [AddCommMonoid M] [Module R M]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
Instance `Submodule.FG.directedSystem` / 实例 `Submodule.FG.directedSystem`

English:
instance Submodule.FG.directedSystem
  signature: :
  body: fun _ _ => rfl
  map_map := fun _ _ _ _ _ _ => rfl

中文:
实例 子模.FG.directedSystem
  签名: :
  定义体: fun _ _ => rfl
  map_map := fun _ _ _ _ _ _ => rfl

Depends on / 依赖: P.FG, P.val, Submodule
-/
instance Submodule.FG.directedSystem :
    DirectedSystem (ι := {P : Submodule R M // P.FG}) (F := fun P => P.val)
    (f := fun ⦃P Q⦄ (h : P <= Q) => Submodule.inclusion h) where
  map_self := fun _ _ => rfl
  map_map := fun _ _ _ _ _ _ => rfl

set_option backward.isDefEq.respectTransparency.types false in
variable (R M) in
/--
Definition of `Submodule.FG.directLimit` / `Submodule.FG.directLimit` 的定义

English:
definition Submodule.FG.directLimit
  signature: [DecidableEq {P : Submodule R M // P.FG}]
  body: LinearEquiv.ofBijective
    (Module.DirectLimit.lift _ _ _ _ (fun P => P.val.subtype) (fun _ _ _ _ => rfl))
    ⟨Module.DirectLimit.lift_injective _ _ (fun P => Submodule.injective_subtype P.val),
      fun x => ⟨Module.DirectLimit.of _ {P : Submodule R M // P.FG} _ _
          ⟨Submodule.span R {x}

中文:
定义 子模.FG.directLimit
  签名: [DecidableEq {P : 子模 R M // P.FG}]
  定义体: LinearEquiv.ofBijective
    (Module.DirectLimit.lift _ _ _ _ (fun P => P.val.subtype) (fun _ _ _ _ => rfl))
    ⟨Module.DirectLimit.lift_injective _ _ (fun P => Submodule.injective_subtype P.val),
      fun x => ⟨Module.DirectLimit.of _ {P : Submodule R M // P.FG} _ _
          ⟨Submodule.span R {x}

Depends on / 依赖: P.FG, P.val, Submodule
-/
noncomputable def Submodule.FG.directLimit [DecidableEq {P : Submodule R M // P.FG}] :
    Module.DirectLimit (ι := {P : Submodule R M // P.FG}) (G := fun P => P.val)
      (fun ⦃P Q⦄ (h : P <= Q) => Submodule.inclusion h) ≃ₗ[R] M :=
  LinearEquiv.ofBijective
    (Module.DirectLimit.lift _ _ _ _ (fun P => P.val.subtype) (fun _ _ _ _ => rfl))
    ⟨Module.DirectLimit.lift_injective _ _ (fun P => Submodule.injective_subtype P.val),
      fun x => ⟨Module.DirectLimit.of _ {P : Submodule R M // P.FG} _ _
          ⟨Submodule.span R {x}, Submodule.fg_span_singleton x⟩
          ⟨x, Submodule.mem_span_singleton_self x⟩,
         by simp⟩⟩

end Semiring

section TensorProducts

open TensorProduct

universe u v

variable (R : Type u) (M N : Type*)
  [CommSemiring R]
  [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]

/--
theorem `DirectedSystem.rTensor` / 定理 `DirectedSystem.rTensor`

English:
theorem DirectedSystem.rTensor
  statement: {ι : Type*} [Preorder ι] {F : ι -> Type*}
  proof: by
    rw [← id_apply (R := R) t]
    apply DFunLike.congr_fun
    ext m n
    simp [D.map_self]
  map_map {i j k} h h' t := by
    rw [← comp_apply]; rw [← rTensor_comp]
    apply DFunLike.congr_fun
    ext p n
    simp [D.map_map]

中文:
定理 DirectedSystem.rTensor
  结论: {ι : 类型} [预序 ι] {F : ι -> 类型}
  证明: by
    rw [← id_apply (R := R) t]
    apply DFunLike.congr_fun
    ext m n
    simp [D.map_self]
  map_map {i j k} h h' t := by
    rw [← comp_apply]; rw [← rTensor_comp]
    apply DFunLike.congr_fun
    ext p n
    simp [D.map_map]

Depends on / 依赖: D.map_map, D.map_self, DFunLike, DFunLike.congr_fun, comp_apply, congr_fun, id_apply, map_map, map_self, rTensor_comp
-/
theorem DirectedSystem.rTensor {ι : Type*} [Preorder ι] {F : ι -> Type*}
    [forall i, AddCommMonoid (F i)] [forall i, Module R (F i)] {f : ⦃i j : ι⦄ -> i <= j -> F i ->ₗ[R] F j}
    (D : DirectedSystem F (fun _ _ h => f h)) :
    DirectedSystem (fun i => (F i) otimes[R] N) (fun _ _ h => rTensor N (f h)) where
  map_self i t := by
    rw [← id_apply (R := R) t]
    apply DFunLike.congr_fun
    ext m n
    simp [D.map_self]
  map_map {i j k} h h' t := by
    rw [← comp_apply]; rw [← rTensor_comp]
    apply DFunLike.congr_fun
    ext p n
    simp [D.map_map]

/--
theorem `Submodule.FG.rTensor.directedSystem` / 定理 `Submodule.FG.rTensor.directedSystem`

English:
theorem Submodule.FG.rTensor.directedSystem
  proof: Submodule.FG.directedSystem.rTensor R N

中文:
定理 子模.FG.rTensor.directedSystem
  证明: Submodule.FG.directedSystem.rTensor R N

Depends on / 依赖: P.FG, P.val, Submodule, otimes
-/
theorem Submodule.FG.rTensor.directedSystem :
    DirectedSystem (ι := {P : Submodule R M // P.FG}) (fun P => P.val otimes[R] N)
    (fun ⦃_ _⦄ h => rTensor N (Submodule.inclusion h)) :=
  Submodule.FG.directedSystem.rTensor R N

/--
Definition of `Submodule.FG.rTensor.directLimit` / `Submodule.FG.rTensor.directLimit` 的定义

English:
definition Submodule.FG.rTensor.directLimit
  signature: [DecidableEq {P : Submodule R M // P.FG}]
  body: (TensorProduct.directLimitLeft _ N).symm.trans ((Submodule.FG.directLimit R M).rTensor N)

中文:
定义 子模.FG.rTensor.directLimit
  签名: [DecidableEq {P : 子模 R M // P.FG}]
  定义体: (TensorProduct.directLimitLeft _ N).symm.trans ((Submodule.FG.directLimit R M).rTensor N)

Depends on / 依赖: P.FG, P.val, Submodule, otimes
-/
noncomputable def Submodule.FG.rTensor.directLimit [DecidableEq {P : Submodule R M // P.FG}] :
    Module.DirectLimit (R := R) (ι := {P : Submodule R M // P.FG}) (fun P => P.val otimes[R] N)
      (fun ⦃P Q⦄ (h : P <= Q) => (Submodule.inclusion h).rTensor N) ≃ₗ[R] M otimes[R] N :=
  (TensorProduct.directLimitLeft _ N).symm.trans ((Submodule.FG.directLimit R M).rTensor N)

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `Submodule.FG.rTensor.directLimit_apply` / 定理 `Submodule.FG.rTensor.directLimit_apply`

English:
theorem Submodule.FG.rTensor.directLimit_apply
  statement: [DecidableEq {P : Submodule R M // P.FG}]
  proof: by
  suffices (Submodule.FG.rTensor.directLimit R M N).toLinearMap.comp
      (Module.DirectLimit.of R {P : Submodule R M // P.FG} (fun P => P.val otimes[R] N)
        (fun _ _ hPQ => rTensor N (Submodule.inclusion hPQ)) P)
      = rTensor N (Submodule.subtype P.val) by
    exact DFunLike.congr_fun 

中文:
定理 子模.FG.rTensor.directLimit_apply
  结论: [DecidableEq {P : 子模 R M // P.FG}]
  证明: by
  suffices (Submodule.FG.rTensor.directLimit R M N).toLinearMap.comp
      (Module.DirectLimit.of R {P : Submodule R M // P.FG} (fun P => P.val otimes[R] N)
        (fun _ _ hPQ => rTensor N (Submodule.inclusion hPQ)) P)
      = rTensor N (Submodule.subtype P.val) by
    exact DFunLike.congr_fun 

Depends on / 依赖: DFunLike, DFunLike.congr_fun, DirectLimit, Module, Module.DirectLimit.of, P.FG, P.val, Submodule, Submodule.FG.directLimit, Submodule.FG.rTensor.directLimit, Submodule.inclusion, Submodule.subtype, congr_fun, directLimit, inclusion, otimes, rTensor, subtype, toLinearMap, toLinearMap.comp
-/
theorem Submodule.FG.rTensor.directLimit_apply [DecidableEq {P : Submodule R M // P.FG}]
    {P : {P : Submodule R M // P.FG}} (u : P otimes[R] N) :
    (Submodule.FG.rTensor.directLimit R M N)
      ((Module.DirectLimit.of R {P : Submodule R M // P.FG} (fun P => P.val otimes[R] N)
        (fun ⦃_ _⦄ h => (Submodule.inclusion h).rTensor N) P) u)
      = (rTensor N (Submodule.subtype P)) u := by
  suffices (Submodule.FG.rTensor.directLimit R M N).toLinearMap.comp
      (Module.DirectLimit.of R {P : Submodule R M // P.FG} (fun P => P.val otimes[R] N)
        (fun _ _ hPQ => rTensor N (Submodule.inclusion hPQ)) P)
      = rTensor N (Submodule.subtype P.val) by
    exact DFunLike.congr_fun this u
  ext p n
  simp [Submodule.FG.rTensor.directLimit, Submodule.FG.directLimit]

/--
theorem `Submodule.FG.rTensor.directLimit_apply'` / 定理 `Submodule.FG.rTensor.directLimit_apply'`

English:
theorem Submodule.FG.rTensor.directLimit_apply'
  statement: [DecidableEq {P : Submodule R M // P.FG}]
  proof: by
  apply Submodule.FG.rTensor.directLimit_apply

中文:
定理 子模.FG.rTensor.directLimit_apply'
  结论: [DecidableEq {P : 子模 R M // P.FG}]
  证明: by
  apply Submodule.FG.rTensor.directLimit_apply

Depends on / 依赖: Submodule, Submodule.FG.rTensor.directLimit_apply, directLimit_apply, rTensor
-/
theorem Submodule.FG.rTensor.directLimit_apply' [DecidableEq {P : Submodule R M // P.FG}]
    {P : Submodule R M} (hP : Submodule.FG P) (u : P otimes[R] N) :
    (Submodule.FG.rTensor.directLimit R M N)
      ((Module.DirectLimit.of R {P : Submodule R M // P.FG} (fun P => P.val otimes[R] N)
        (fun ⦃_ _⦄ h => rTensor N (Submodule.inclusion h)) ⟨P, hP⟩) u)
      = (rTensor N (Submodule.subtype P)) u := by
  apply Submodule.FG.rTensor.directLimit_apply

/--
theorem `DirectedSystem.lTensor` / 定理 `DirectedSystem.lTensor`

English:
theorem DirectedSystem.lTensor
  statement: {ι : Type*} [Preorder ι] {F : ι -> Type*}
  proof: by
    rw [← id_apply (R := R) t]
    apply DFunLike.congr_fun
    ext m n
    simp [D.map_self]
  map_map {i j k} h h' t := by
    rw [← comp_apply]; rw [← lTensor_comp]
    apply DFunLike.congr_fun
    ext p n
    simp [D.map_map]

中文:
定理 DirectedSystem.lTensor
  结论: {ι : 类型} [预序 ι] {F : ι -> 类型}
  证明: by
    rw [← id_apply (R := R) t]
    apply DFunLike.congr_fun
    ext m n
    simp [D.map_self]
  map_map {i j k} h h' t := by
    rw [← comp_apply]; rw [← lTensor_comp]
    apply DFunLike.congr_fun
    ext p n
    simp [D.map_map]

Depends on / 依赖: D.map_map, D.map_self, DFunLike, DFunLike.congr_fun, comp_apply, congr_fun, id_apply, lTensor_comp, map_map, map_self
-/
theorem DirectedSystem.lTensor {ι : Type*} [Preorder ι] {F : ι -> Type*}
    [forall i, AddCommMonoid (F i)] [forall i, Module R (F i)] {f : ⦃i j : ι⦄ -> i <= j -> F i ->ₗ[R] F j}
    (D : DirectedSystem F (fun _ _ h => f h)) :
    DirectedSystem (fun i => M otimes[R] (F i)) (fun _ _ h => lTensor M (f h)) where
  map_self i t := by
    rw [← id_apply (R := R) t]
    apply DFunLike.congr_fun
    ext m n
    simp [D.map_self]
  map_map {i j k} h h' t := by
    rw [← comp_apply]; rw [← lTensor_comp]
    apply DFunLike.congr_fun
    ext p n
    simp [D.map_map]

/--
theorem `Submodule.FG.lTensor.directedSystem` / 定理 `Submodule.FG.lTensor.directedSystem`

English:
theorem Submodule.FG.lTensor.directedSystem
  proof: Submodule.FG.directedSystem.lTensor R M

中文:
定理 子模.FG.lTensor.directedSystem
  证明: Submodule.FG.directedSystem.lTensor R M

Depends on / 依赖: Q.FG, Q.val, Submodule, otimes
-/
theorem Submodule.FG.lTensor.directedSystem :
    DirectedSystem (ι := {Q : Submodule R N // Q.FG}) (fun Q => M otimes[R] Q.val)
      (fun _ _ hPQ => lTensor M (Submodule.inclusion hPQ)) :=
  Submodule.FG.directedSystem.lTensor R M

/--
Definition of `Submodule.FG.lTensor.directLimit` / `Submodule.FG.lTensor.directLimit` 的定义

English:
definition Submodule.FG.lTensor.directLimit
  signature: [DecidableEq {Q : Submodule R N // Q.FG}]
  body: (TensorProduct.directLimitRight _ M).symm.trans ((Submodule.FG.directLimit R N).lTensor M)

中文:
定义 子模.FG.lTensor.directLimit
  签名: [DecidableEq {Q : 子模 R N // Q.FG}]
  定义体: (TensorProduct.directLimitRight _ M).symm.trans ((Submodule.FG.directLimit R N).lTensor M)

Depends on / 依赖: Q.FG, Q.val, Submodule, otimes
-/
noncomputable def Submodule.FG.lTensor.directLimit [DecidableEq {Q : Submodule R N // Q.FG}] :
    Module.DirectLimit (R := R) (ι := {Q : Submodule R N // Q.FG}) (fun Q => M otimes[R] Q.val)
      (fun _ _ hPQ => (inclusion hPQ).lTensor M) ≃ₗ[R] M otimes[R] N :=
  (TensorProduct.directLimitRight _ M).symm.trans ((Submodule.FG.directLimit R N).lTensor M)

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `Submodule.FG.lTensor.directLimit_apply` / 定理 `Submodule.FG.lTensor.directLimit_apply`

English:
theorem Submodule.FG.lTensor.directLimit_apply
  statement: [DecidableEq {P : Submodule R N // P.FG}]
  proof: by
  suffices (Submodule.FG.lTensor.directLimit R M N).toLinearMap.comp
      (Module.DirectLimit.of R {Q : Submodule R N // Q.FG} (fun Q => M otimes[R] Q.val)
        (fun _ _ hPQ => lTensor M (inclusion hPQ)) Q)
      = lTensor M (Submodule.subtype Q.val) by
    exact DFunLike.congr_fun this u
  e

中文:
定理 子模.FG.lTensor.directLimit_apply
  结论: [DecidableEq {P : 子模 R N // P.FG}]
  证明: by
  suffices (Submodule.FG.lTensor.directLimit R M N).toLinearMap.comp
      (Module.DirectLimit.of R {Q : Submodule R N // Q.FG} (fun Q => M otimes[R] Q.val)
        (fun _ _ hPQ => lTensor M (inclusion hPQ)) Q)
      = lTensor M (Submodule.subtype Q.val) by
    exact DFunLike.congr_fun this u
  e

Depends on / 依赖: DFunLike, DFunLike.congr_fun, DirectLimit, Module, Module.DirectLimit.of, Q.FG, Q.val, Submodule, Submodule.FG.directLimit, Submodule.FG.lTensor.directLimit, Submodule.subtype, congr_fun, directLimit, inclusion, lTensor, otimes, subtype, toLinearMap, toLinearMap.comp
-/
theorem Submodule.FG.lTensor.directLimit_apply [DecidableEq {P : Submodule R N // P.FG}]
    (Q : {Q : Submodule R N // Q.FG}) (u : M otimes[R] Q.val) :
    (Submodule.FG.lTensor.directLimit R M N)
      ((Module.DirectLimit.of R {Q : Submodule R N // Q.FG} (fun Q => M otimes[R] Q.val)
        (fun _ _ hPQ => (inclusion hPQ).lTensor M) Q) u)
      = (lTensor M (Submodule.subtype Q.val)) u := by
  suffices (Submodule.FG.lTensor.directLimit R M N).toLinearMap.comp
      (Module.DirectLimit.of R {Q : Submodule R N // Q.FG} (fun Q => M otimes[R] Q.val)
        (fun _ _ hPQ => lTensor M (inclusion hPQ)) Q)
      = lTensor M (Submodule.subtype Q.val) by
    exact DFunLike.congr_fun this u
  ext p n
  simp [Submodule.FG.lTensor.directLimit, Submodule.FG.directLimit]

/--
theorem `Submodule.FG.lTensor.directLimit_apply'` / 定理 `Submodule.FG.lTensor.directLimit_apply'`

English:
theorem Submodule.FG.lTensor.directLimit_apply'
  statement: [DecidableEq {Q : Submodule R N // Q.FG}]
  proof: Submodule.FG.lTensor.directLimit_apply R M N ⟨Q, hQ⟩ u

中文:
定理 子模.FG.lTensor.directLimit_apply'
  结论: [DecidableEq {Q : 子模 R N // Q.FG}]
  证明: Submodule.FG.lTensor.directLimit_apply R M N ⟨Q, hQ⟩ u

Depends on / 依赖: Submodule, Submodule.FG.lTensor.directLimit_apply, directLimit_apply, lTensor
-/
theorem Submodule.FG.lTensor.directLimit_apply' [DecidableEq {Q : Submodule R N // Q.FG}]
    (Q : Submodule R N) (hQ : Q.FG) (u : M otimes[R] Q) :
    (Submodule.FG.lTensor.directLimit R M N)
      ((Module.DirectLimit.of R {Q : Submodule R N // Q.FG} (fun Q => M otimes[R] Q.val)
        (fun _ _ hPQ => lTensor M (inclusion hPQ)) ⟨Q, hQ⟩) u)
      = (lTensor M (Submodule.subtype Q)) u :=
  Submodule.FG.lTensor.directLimit_apply R M N ⟨Q, hQ⟩ u

variable {R M N} (u : M otimes[R] N)
    {P : Submodule R M} (hP : Submodule.FG P) {t : P otimes[R] N}
    {P' : Submodule R M} (hP' : Submodule.FG P') {t' : P' otimes[R] N}

/--
theorem `TensorProduct.exists_of_fg` / 定理 `TensorProduct.exists_of_fg`

English:
theorem TensorProduct.exists_of_fg
  proof: by
  let ⟨P, t, ht⟩ := Module.DirectLimit.exists_of ((Submodule.FG.rTensor.directLimit R M N).symm u)
  use P.val, P.property, t
  rw [← Submodule.FG.rTensor.directLimit_apply]; rw [ht]; rw [LinearEquiv.apply_symm_apply]

include hP in

中文:
定理 张量积.存在_of_fg
  证明: by
  let ⟨P, t, ht⟩ := Module.DirectLimit.exists_of ((Submodule.FG.rTensor.directLimit R M N).symm u)
  use P.val, P.property, t
  rw [← Submodule.FG.rTensor.directLimit_apply]; rw [ht]; rw [LinearEquiv.apply_symm_apply]

include hP in

Depends on / 依赖: DirectLimit, LinearEquiv, LinearEquiv.apply_symm_apply, Module, Module.DirectLimit.exists_of, P.property, P.val, Submodule, Submodule.FG.rTensor.directLimit, Submodule.FG.rTensor.directLimit_apply, apply_symm_apply, directLimit, directLimit_apply, exists_of, property, rTensor
-/
theorem TensorProduct.exists_of_fg :
    exists (P : Submodule R M), P.FG ∧ u in range (rTensor N P.subtype) := by
  let ⟨P, t, ht⟩ := Module.DirectLimit.exists_of ((Submodule.FG.rTensor.directLimit R M N).symm u)
  use P.val, P.property, t
  rw [← Submodule.FG.rTensor.directLimit_apply]; rw [ht]; rw [LinearEquiv.apply_symm_apply]

include hP in
/--
theorem `TensorProduct.eq_of_fg_of_subtype_eq` / 定理 `TensorProduct.eq_of_fg_of_subtype_eq`

English:
theorem TensorProduct.eq_of_fg_of_subtype_eq
  statement: {t' : P otimes[R] N}
  proof: by
  simp only [← Submodule.FG.rTensor.directLimit_apply' R M N hP, EmbeddingLike.apply_eq_iff_eq] at h
  obtain ⟨Q, hPQ, h⟩ := Module.DirectLimit.exists_eq_of_of_eq h
  use Q.val, Subtype.coe_le_coe.mpr hPQ, Q.property

include hP in

中文:
定理 张量积.eq_of_fg_of_subtype_eq
  结论: {t' : P otimes[R] N}
  证明: by
  simp only [← Submodule.FG.rTensor.directLimit_apply' R M N hP, EmbeddingLike.apply_eq_iff_eq] at h
  obtain ⟨Q, hPQ, h⟩ := Module.DirectLimit.exists_eq_of_of_eq h
  use Q.val, Subtype.coe_le_coe.mpr hPQ, Q.property

include hP in

Depends on / 依赖: DirectLimit, EmbeddingLike, EmbeddingLike.apply_eq_iff_eq, Module, Module.DirectLimit.exists_eq_of_of_eq, Q.property, Q.val, Submodule, Submodule.FG.rTensor.directLimit_apply, Subtype, Subtype.coe_le_coe.mpr, apply_eq_iff_eq, coe_le_coe, directLimit_apply, exists_eq_of_of_eq, property, rTensor
-/
theorem TensorProduct.eq_of_fg_of_subtype_eq {t' : P otimes[R] N}
    (h : rTensor N P.subtype t = rTensor N P.subtype t') :
    exists (Q : Submodule R M) (hPQ : P <= Q), Q.FG ∧
      rTensor N (inclusion hPQ) t = rTensor N (inclusion hPQ) t' := by
  simp only [← Submodule.FG.rTensor.directLimit_apply' R M N hP, EmbeddingLike.apply_eq_iff_eq] at h
  obtain ⟨Q, hPQ, h⟩ := Module.DirectLimit.exists_eq_of_of_eq h
  use Q.val, Subtype.coe_le_coe.mpr hPQ, Q.property

include hP in
/--
theorem `TensorProduct.eq_zero_of_fg_of_subtype_eq_zero` / 定理 `TensorProduct.eq_zero_of_fg_of_subtype_eq_zero`

English:
theorem TensorProduct.eq_zero_of_fg_of_subtype_eq_zero
  given: (h : rTensor N P.subtype t = 0)
  proof: by
  rw [← (rTensor N P.subtype).map_zero] at h
  simpa only [map_zero] using TensorProduct.eq_of_fg_of_subtype_eq hP h

include hP hP' in

中文:
定理 张量积.eq_zero_of_fg_of_subtype_eq_zero
  条件: (h : rTensor N P.subtype t = 0)
  证明: by
  rw [← (rTensor N P.subtype).map_zero] at h
  simpa only [map_zero] using TensorProduct.eq_of_fg_of_subtype_eq hP h

include hP hP' in

Depends on / 依赖: P.subtype, TensorProduct, TensorProduct.eq_of_fg_of_subtype_eq, eq_of_fg_of_subtype_eq, map_zero, rTensor, subtype
-/
theorem TensorProduct.eq_zero_of_fg_of_subtype_eq_zero (h : rTensor N P.subtype t = 0) :
    exists (Q : Submodule R M) (hPQ : P <= Q), Q.FG ∧ rTensor N (inclusion hPQ) t = 0 := by
  rw [← (rTensor N P.subtype).map_zero] at h
  simpa only [map_zero] using TensorProduct.eq_of_fg_of_subtype_eq hP h

include hP hP' in
/--
theorem `TensorProduct.eq_of_fg_of_subtype_eq'` / 定理 `TensorProduct.eq_of_fg_of_subtype_eq'`

English:
theorem TensorProduct.eq_of_fg_of_subtype_eq'
  proof: by
  simp only [← subtype_comp_inclusion _ _ (le_sup_left : _ <= P ⊔ P'),
    ← subtype_comp_inclusion _ _ (le_sup_right : _ <= P ⊔ P'),
    rTensor_comp, coe_comp, Function.comp_apply] at h
  let ⟨Q, hQ_le, hQ, h⟩ := TensorProduct.eq_of_fg_of_subtype_eq (hP.sup hP') h
  use Q, le_trans le_sup_left 

中文:
定理 张量积.eq_of_fg_of_subtype_eq'
  证明: by
  simp only [← subtype_comp_inclusion _ _ (le_sup_left : _ <= P ⊔ P'),
    ← subtype_comp_inclusion _ _ (le_sup_right : _ <= P ⊔ P'),
    rTensor_comp, coe_comp, Function.comp_apply] at h
  let ⟨Q, hQ_le, hQ, h⟩ := TensorProduct.eq_of_fg_of_subtype_eq (hP.sup hP') h
  use Q, le_trans le_sup_left 

Depends on / 依赖: Function, Function.comp_apply, TensorProduct, TensorProduct.eq_of_fg_of_subtype_eq, coe_comp, comp_apply, eq_of_fg_of_subtype_eq, hP.sup, hQ_le, le_sup_left, le_sup_right, le_trans, rTensor_comp, subtype_comp_inclusion
-/
theorem TensorProduct.eq_of_fg_of_subtype_eq'
    (h : rTensor N P.subtype t = rTensor N P'.subtype t') :
    exists (Q : Submodule R M) (hPQ : P <= Q) (hP'Q : P' <= Q), Q.FG ∧
      rTensor N (inclusion hPQ) t = rTensor N (inclusion hP'Q) t' := by
  simp only [← subtype_comp_inclusion _ _ (le_sup_left : _ <= P ⊔ P'),
    ← subtype_comp_inclusion _ _ (le_sup_right : _ <= P ⊔ P'),
    rTensor_comp, coe_comp, Function.comp_apply] at h
  let ⟨Q, hQ_le, hQ, h⟩ := TensorProduct.eq_of_fg_of_subtype_eq (hP.sup hP') h
  use Q, le_trans le_sup_left hQ_le, le_trans le_sup_right hQ_le, hQ
  simpa [← comp_apply, ← rTensor_comp] using! h

end TensorProducts

section Algebra

open TensorProduct

variable {R S M N : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
  [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N]
  (u : S otimes[R] N)
  {A : Subalgebra R S} (hA : A.FG) {t t' : A otimes[R] N}
  {A' : Subalgebra R S} (hA' : A'.FG)

/--
theorem `TensorProduct.Algebra.exists_of_fg` / 定理 `TensorProduct.Algebra.exists_of_fg`

English:
theorem TensorProduct.Algebra.exists_of_fg
  proof: by
  obtain ⟨P, ⟨s, hs⟩, hu⟩ := TensorProduct.exists_of_fg u
  use Algebra.adjoin R s, Subalgebra.fg_adjoin_finset _
  have : P <= (Algebra.adjoin R (s : Set S)).toSubmodule := by
    simp only [← hs, span_le, Subalgebra.coe_toSubmodule]
    exact Algebra.subset_adjoin
  rw [← subtype_comp_inclusion

中文:
定理 张量积.代数.存在_of_fg
  证明: by
  obtain ⟨P, ⟨s, hs⟩, hu⟩ := TensorProduct.exists_of_fg u
  use Algebra.adjoin R s, Subalgebra.fg_adjoin_finset _
  have : P <= (Algebra.adjoin R (s : Set S)).toSubmodule := by
    simp only [← hs, span_le, Subalgebra.coe_toSubmodule]
    exact Algebra.subset_adjoin
  rw [← subtype_comp_inclusion

Depends on / 依赖: Algebra, Algebra.adjoin, Algebra.subset_adjoin, Subalgebra, Subalgebra.coe_toSubmodule, Subalgebra.fg_adjoin_finset, TensorProduct, TensorProduct.exists_of_fg, adjoin, coe_toSubmodule, exists_of_fg, fg_adjoin_finset, rTensor_comp, range_comp_le_range, span_le, subset_adjoin, subtype_comp_inclusion, toSubmodule
-/
theorem TensorProduct.Algebra.exists_of_fg :
    exists (A : Subalgebra R S), Subalgebra.FG A ∧ u in range (rTensor N A.val.toLinearMap) := by
  obtain ⟨P, ⟨s, hs⟩, hu⟩ := TensorProduct.exists_of_fg u
  use Algebra.adjoin R s, Subalgebra.fg_adjoin_finset _
  have : P <= (Algebra.adjoin R (s : Set S)).toSubmodule := by
    simp only [← hs, span_le, Subalgebra.coe_toSubmodule]
    exact Algebra.subset_adjoin
  rw [← subtype_comp_inclusion P _ this]; rw [rTensor_comp] at hu
  exact range_comp_le_range _ _ hu

include hA in
/--
theorem `TensorProduct.Algebra.eq_of_fg_of_subtype_eq` / 定理 `TensorProduct.Algebra.eq_of_fg_of_subtype_eq`

English:
theorem TensorProduct.Algebra.eq_of_fg_of_subtype_eq
  proof: by
  classical
  let ⟨P, hP, u, hu⟩ := TensorProduct.exists_of_fg t
  let ⟨P', hP', u', hu'⟩ := TensorProduct.exists_of_fg t'
  let P₁ := Submodule.map A.toSubmodule.subtype (P ⊔ P')
  have hP₁ : Submodule.FG P₁ := Submodule.FG.map _ (Submodule.FG.sup hP hP')
  -- the embeddings from P and P' to P₁


中文:
定理 张量积.代数.eq_of_fg_of_subtype_eq
  证明: by
  classical
  let ⟨P, hP, u, hu⟩ := TensorProduct.exists_of_fg t
  let ⟨P', hP', u', hu'⟩ := TensorProduct.exists_of_fg t'
  let P₁ := Submodule.map A.toSubmodule.subtype (P ⊔ P')
  have hP₁ : Submodule.FG P₁ := Submodule.FG.map _ (Submodule.FG.sup hP hP')
  -- the embeddings from P and P' to P₁


Depends on / 依赖: A.toSubmodule.subtype, Submodule, Submodule.FG, Submodule.FG.map, Submodule.FG.sup, Submodule.map, TensorProduct, TensorProduct.exists_of_fg, classical, exists_of_fg, subtype, toSubmodule
-/
theorem TensorProduct.Algebra.eq_of_fg_of_subtype_eq
    (h : rTensor N A.val.toLinearMap t = rTensor N A.val.toLinearMap t') :
    exists (B : Subalgebra R S) (hAB : A <= B), Subalgebra.FG B
      ∧ rTensor N (Subalgebra.inclusion hAB).toLinearMap t
        = LinearMap.rTensor N (Subalgebra.inclusion hAB).toLinearMap t' := by
  classical
  let ⟨P, hP, u, hu⟩ := TensorProduct.exists_of_fg t
  let ⟨P', hP', u', hu'⟩ := TensorProduct.exists_of_fg t'
  let P₁ := Submodule.map A.toSubmodule.subtype (P ⊔ P')
  have hP₁ : Submodule.FG P₁ := Submodule.FG.map _ (Submodule.FG.sup hP hP')
  -- the embeddings from P and P' to P₁
  let j : P ->ₗ[R] P₁ := (Subalgebra.toSubmodule A).subtype.restrict
      (fun p hp => by
        simp only [coe_subtype, Submodule.map_sup, P₁]
        exact Submodule.mem_sup_left ⟨p, hp, rfl⟩)
  let j' : P' ->ₗ[R] P₁ := (Subalgebra.toSubmodule A).subtype.restrict
      (fun p hp => by
        simp only [coe_subtype, Submodule.map_sup, P₁]
        exact Submodule.mem_sup_right ⟨p, hp, rfl⟩)
  -- we map u and u' to P₁ ⊗[R] N, getting u₁ and u'₁
  set u₁ := rTensor N j u with hu₁
  set u'₁ := rTensor N j' u' with hu'₁
  -- u₁ and u'₁ are equal in S ⊗[R] N
  have : rTensor N P₁.subtype u₁ = rTensor N P₁.subtype u'₁ := by
    rw [hu₁]; rw [hu'₁]
    simp only [← comp_apply, ← rTensor_comp]
    have hj₁ : P₁.subtype ∘ₗ j = A.val.toLinearMap ∘ₗ P.subtype := rfl
    have hj'₁ : P₁.subtype ∘ₗ j' = A.val.toLinearMap ∘ₗ P'.subtype := rfl
    rw [hj₁]; rw [hj'₁]
    simp only [rTensor_comp, comp_apply]
    rw [hu]; rw [hu']; rw [h]
  let ⟨P'₁, hP₁_le, hP'₁, h⟩ := TensorProduct.eq_of_fg_of_subtype_eq hP₁ this
  let ⟨s, hs⟩ := hP'₁
  let ⟨w, hw⟩ := hA
  let B := Algebra.adjoin R ((s union w : Finset S) : Set S)
  have hBA : A <= B := by
    simp only [B, ← hw]
    apply Algebra.adjoin_mono
    simp only [Finset.coe_union, Set.subset_union_right]
  use B, hBA, Subalgebra.fg_adjoin_finset _
  rw [← hu]; rw [← hu']
  simp only [← comp_apply, ← rTensor_comp]
  have hP'₁_le : P'₁ <= B.toSubmodule := by
    simp only [← hs, Finset.coe_union, Submodule.span_le, Subalgebra.coe_toSubmodule, B]
    exact subset_trans Set.subset_union_left Algebra.subset_adjoin
  have k : (Subalgebra.inclusion hBA).toLinearMap ∘ₗ P.subtype
    = inclusion hP'₁_le ∘ₗ inclusion hP₁_le ∘ₗ j := by ext; rfl
  have k' : (Subalgebra.inclusion hBA).toLinearMap ∘ₗ P'.subtype
    = inclusion hP'₁_le ∘ₗ inclusion hP₁_le ∘ₗ j' := by ext; rfl
  rw [k]; rw [k']
  simp only [rTensor_comp, comp_apply]
  rw [← hu₁]; rw [← hu'₁]; rw [h]

include hA hA' in
/--
theorem `TensorProduct.Algebra.eq_of_fg_of_subtype_eq'` / 定理 `TensorProduct.Algebra.eq_of_fg_of_subtype_eq'`

English:
theorem TensorProduct.Algebra.eq_of_fg_of_subtype_eq'
  statement: {t' : A' otimes[R] N}
  proof: by
  have hj : (A ⊔ A').val.comp (Subalgebra.inclusion le_sup_left) = A.val := by ext; rfl
  have hj' : (A ⊔ A').val.comp (Subalgebra.inclusion le_sup_right) = A'.val := by ext; rfl
  simp only [← hj, ← hj', AlgHom.comp_toLinearMap, rTensor_comp, comp_apply] at h
  let ⟨B, hB_le, hB, h⟩ := TensorPro

中文:
定理 张量积.代数.eq_of_fg_of_subtype_eq'
  结论: {t' : A' otimes[R] N}
  证明: by
  have hj : (A ⊔ A').val.comp (Subalgebra.inclusion le_sup_left) = A.val := by ext; rfl
  have hj' : (A ⊔ A').val.comp (Subalgebra.inclusion le_sup_right) = A'.val := by ext; rfl
  simp only [← hj, ← hj', AlgHom.comp_toLinearMap, rTensor_comp, comp_apply] at h
  let ⟨B, hB_le, hB, h⟩ := TensorPro

Depends on / 依赖: A.val, AlgHom, AlgHom.comp_toLinearMap, Algebra, Subalgebra, Subalgebra.FG.sup, Subalgebra.inclusion, TensorProduct, TensorProduct.Algebra.eq_of_fg_of_subtype_eq, comp_apply, comp_toLinearMap, eq_of_fg_of_subtype_eq, hB_le, inclusion, le_sup_left, le_sup_right, le_trans, rTensor_comp, val.comp
-/
theorem TensorProduct.Algebra.eq_of_fg_of_subtype_eq' {t' : A' otimes[R] N}
    (h : rTensor N A.val.toLinearMap t = rTensor N A'.val.toLinearMap t') :
    exists (B : Subalgebra R S) (hAB : A <= B) (hA'B : A' <= B), Subalgebra.FG B
      ∧ rTensor N (Subalgebra.inclusion hAB).toLinearMap t
        = rTensor N (Subalgebra.inclusion hA'B).toLinearMap t' := by
  have hj : (A ⊔ A').val.comp (Subalgebra.inclusion le_sup_left) = A.val := by ext; rfl
  have hj' : (A ⊔ A').val.comp (Subalgebra.inclusion le_sup_right) = A'.val := by ext; rfl
  simp only [← hj, ← hj', AlgHom.comp_toLinearMap, rTensor_comp, comp_apply] at h
  let ⟨B, hB_le, hB, h⟩ := TensorProduct.Algebra.eq_of_fg_of_subtype_eq
    (Subalgebra.FG.sup hA hA') h
  use B, le_trans le_sup_left hB_le, le_trans le_sup_right hB_le, hB
  simpa only [← rTensor_comp, ← comp_apply] using! h

/--
theorem `Submodule.exists_fg_of_baseChange_eq_zero` / 定理 `Submodule.exists_fg_of_baseChange_eq_zero`

English:
theorem Submodule.exists_fg_of_baseChange_eq_zero
  proof: by
  obtain ⟨A, hA, ht_memA⟩ := TensorProduct.Algebra.exists_of_fg t
  obtain ⟨u, hu⟩ := _root_.id ht_memA
  have := TensorProduct.Algebra.eq_of_fg_of_subtype_eq hA (t := f.baseChange _ u) (t' := 0)
  simp only [map_zero, exists_and_left] at this
  have hu' : (A.val.toLinearMap.rTensor N) (f.baseCha

中文:
定理 子模.存在_fg_of_baseChange_eq_zero
  证明: by
  obtain ⟨A, hA, ht_memA⟩ := TensorProduct.Algebra.exists_of_fg t
  obtain ⟨u, hu⟩ := _root_.id ht_memA
  have := TensorProduct.Algebra.eq_of_fg_of_subtype_eq hA (t := f.baseChange _ u) (t' := 0)
  simp only [map_zero, exists_and_left] at this
  have hu' : (A.val.toLinearMap.rTensor N) (f.baseCha

Depends on / 依赖: A.val.toLinearMap.rTensor, Algebra, Subalgebra, Subalgebra.inclusion, TensorProduct, TensorProduct.Algebra.eq_of_fg_of_subtype_eq, TensorProduct.Algebra.exists_of_fg, _root_, _root_.id, baseChange, eq_of_fg_of_subtype_eq, exists_and_left, exists_of_fg, f.baseChange, ht_memA, inclusion, map_zero, rTensor, rTensor_baseChange, toLinearMap
-/
theorem Submodule.exists_fg_of_baseChange_eq_zero
    (f : M ->ₗ[R] N) {t : S otimes[R] M} (ht : f.baseChange S t = 0) :
    exists (A : Subalgebra R S) (_ : A.FG) (u : A otimes[R] M),
      f.baseChange A u = 0 ∧ A.val.toLinearMap.rTensor M u = t := by
  obtain ⟨A, hA, ht_memA⟩ := TensorProduct.Algebra.exists_of_fg t
  obtain ⟨u, hu⟩ := _root_.id ht_memA
  have := TensorProduct.Algebra.eq_of_fg_of_subtype_eq hA (t := f.baseChange _ u) (t' := 0)
  simp only [map_zero, exists_and_left] at this
  have hu' : (A.val.toLinearMap.rTensor N) (f.baseChange (↥A) u) = 0 := by
    rw [← ht]; rw [← hu]; rw [rTensor_baseChange]
  obtain ⟨B, hB, hAB, hu'⟩ := this hu'
  use B, hB, rTensor M (Subalgebra.inclusion hAB).toLinearMap u
  constructor
  · rw [← rTensor_baseChange, hu']
  · rw [← comp_apply, ← rTensor_comp, ← hu]
    congr

end Algebra
