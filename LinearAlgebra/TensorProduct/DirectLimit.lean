/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.Algebra.Colimit.Module
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Tensor product and direct limits commute with each other.

Given a family of `R`-modules `Gᵢ` with a family of compatible `R`-linear maps `fᵢⱼ : Gᵢ → Gⱼ` for
every `i ≤ j` and another `R`-module `M`, we have `(limᵢ Gᵢ) ⊗ M` and `lim (Gᵢ ⊗ M)` are isomorphic
as `R`-modules.

## Main definitions:

* `TensorProduct.directLimitLeft : DirectLimit G f ⊗[R] M ≃ₗ[R] DirectLimit (G · ⊗[R] M) (f ▷ M)`
* `TensorProduct.directLimitRight : M ⊗[R] DirectLimit G f ≃ₗ[R] DirectLimit (M ⊗[R] G ·) (M ◁ f)`

-/

@[expose] public section

open TensorProduct Module Module.DirectLimit

variable {R : Type*} [CommSemiring R]
variable {ι : Type*}
variable [DecidableEq ι] [Preorder ι]
variable {G : ι -> Type*}
variable [forall i, AddCommMonoid (G i)] [forall i, Module R (G i)]
variable (f : forall i j, i <= j -> G i ->ₗ[R] G j)
variable (M : Type*) [AddCommMonoid M] [Module R M]

-- alluding to the notation in `CategoryTheory.Monoidal`
local notation M " ◁ " f => fun i j h => LinearMap.lTensor M (f _ _ h)
local notation f " ▷ " N => fun i j h => LinearMap.rTensor N (f _ _ h)

namespace TensorProduct

/--
Definition of `fromDirectLimit` / `fromDirectLimit` 的定义

English:
definition fromDirectLimit
  signature: :
  body: Module.DirectLimit.lift _ _ _ _ (fun _ => (of _ _ _ _ _).rTensor M)
    fun _ _ _ x => by refine x.induction_on ?_ ?_ ?_ <;> aesop

中文:
定义 fromDirectLimit
  签名: :
  定义体: Module.DirectLimit.lift _ _ _ _ (fun _ => (of _ _ _ _ _).rTensor M)
    fun _ _ _ x => by refine x.induction_on ?_ ?_ ?_ <;> aesop

Depends on / 依赖: DirectLimit, Module, Module.DirectLimit.lift, induction_on, rTensor, x.induction_on
-/
noncomputable def fromDirectLimit :
    DirectLimit (G · otimes[R] M) (f ▷ M) ->ₗ[R] DirectLimit G f otimes[R] M :=
  Module.DirectLimit.lift _ _ _ _ (fun _ => (of _ _ _ _ _).rTensor M)
    fun _ _ _ x => by refine x.induction_on ?_ ?_ ?_ <;> aesop

variable {M} in
/--
lemma `fromDirectLimit_of_tmul` / 引理 `fromDirectLimit_of_tmul`

English:
lemma fromDirectLimit_of_tmul
  given: {i : ι} (g : G i) (m : M)
  proof: lift_of (G := (G · otimes[R] M)) _ _ (g otimesₜ m)

中文:
引理 fromDirectLimit_of_tmul
  条件: {i : ι} (g : G i) (m : M)
  证明: lift_of (G := (G · otimes[R] M)) _ _ (g otimesₜ m)

Depends on / 依赖: FunLike, strongHomClassEmpty
-/
@[simp] lemma fromDirectLimit_of_tmul {i : ι} (g : G i) (m : M) :
    fromDirectLimit f M (of _ _ _ _ i (g otimesₜ m)) = (of _ _ _ f i g) otimesₜ m :=
  lift_of (G := (G · otimes[R] M)) _ _ (g otimesₜ m)

/--
Definition of `toDirectLimit` / `toDirectLimit` 的定义

English:
definition toDirectLimit
  signature: : DirectLimit G f otimes[R] M ->ₗ[R] DirectLimit (G · otimes[R] M) (f ▷ M)
  body: TensorProduct.lift Module.DirectLimit.lift _ _ _ _
    (fun i =>
      (TensorProduct.mk R _ _).compr₂ (of R ι _ (fun _i _j h => (f _ _ h).rTensor M) i))
    fun _ _ _ g => DFunLike.ext _ _ (of_f (G := (G · otimes[R] M)) (x := g otimesₜ ·))

中文:
定义 toDirectLimit
  签名: : DirectLimit G f otimes[R] M ->ₗ[R] DirectLimit (G · otimes[R] M) (f ▷ M)
  定义体: TensorProduct.lift Module.DirectLimit.lift _ _ _ _
    (fun i =>
      (TensorProduct.mk R _ _).compr₂ (of R ι _ (fun _i _j h => (f _ _ h).rTensor M) i))
    fun _ _ _ g => DFunLike.ext _ _ (of_f (G := (G · otimes[R] M)) (x := g otimesₜ ·))

Depends on / 依赖: DFunLike, DFunLike.ext, DirectLimit, Module, Module.DirectLimit.lift, TensorProduct, TensorProduct.lift, TensorProduct.mk, of_f, otimes, rTensor
-/
noncomputable def toDirectLimit : DirectLimit G f otimes[R] M ->ₗ[R] DirectLimit (G · otimes[R] M) (f ▷ M) :=
TensorProduct.lift Module.DirectLimit.lift _ _ _ _
    (fun i =>
      (TensorProduct.mk R _ _).compr₂ (of R ι _ (fun _i _j h => (f _ _ h).rTensor M) i))
    fun _ _ _ g => DFunLike.ext _ _ (of_f (G := (G · otimes[R] M)) (x := g otimesₜ ·))

variable {M} in
/--
lemma `toDirectLimit_tmul_of` / 引理 `toDirectLimit_tmul_of`

English:
lemma toDirectLimit_tmul_of
  proof: by
  rw [toDirectLimit]; rw [lift.tmul]; rw [lift_of]
  rfl

中文:
引理 toDirectLimit_tmul_of
  证明: by
  rw [toDirectLimit]; rw [lift.tmul]; rw [lift_of]
  rfl
-/
@[simp] lemma toDirectLimit_tmul_of
    {i : ι} (g : G i) (m : M) :
    (toDirectLimit f M <| (of _ _ G f i g) otimesₜ m) = (of _ _ _ _ i (g otimesₜ m)) := by
  rw [toDirectLimit]; rw [lift.tmul]; rw [lift_of]
  rfl

attribute [local ext] TensorProduct.ext in
/--
Definition of `directLimitLeft` / `directLimitLeft` 的定义

English:
definition directLimitLeft
  signature: :
  body: LinearEquiv.ofLinearMap (toDirectLimit f M) (fromDirectLimit f M) (by ext; simp) (by ext; simp)

中文:
定义 directLimitLeft
  签名: :
  定义体: LinearEquiv.ofLinearMap (toDirectLimit f M) (fromDirectLimit f M) (by ext; simp) (by ext; simp)

Depends on / 依赖: LinearEquiv, LinearEquiv.ofLinearMap, fromDirectLimit, ofLinearMap, toDirectLimit
-/
noncomputable def directLimitLeft :
    DirectLimit G f otimes[R] M ≃ₗ[R] DirectLimit (G · otimes[R] M) (f ▷ M) :=
  LinearEquiv.ofLinearMap (toDirectLimit f M) (fromDirectLimit f M) (by ext; simp) (by ext; simp)

/--
lemma `directLimitLeft_tmul_of` / 引理 `directLimitLeft_tmul_of`

English:
lemma directLimitLeft_tmul_of
  given: {i : ι} (g : G i) (m : M)
  proof: toDirectLimit_tmul_of f g m

中文:
引理 directLimitLeft_tmul_of
  条件: {i : ι} (g : G i) (m : M)
  证明: toDirectLimit_tmul_of f g m
-/
@[simp] lemma directLimitLeft_tmul_of {i : ι} (g : G i) (m : M) :
    directLimitLeft f M (of _ _ _ _ _ g otimesₜ m) = of _ _ _ (f ▷ M) _ (g otimesₜ m) :=
  toDirectLimit_tmul_of f g m

/--
lemma `directLimitLeft_symm_of_tmul` / 引理 `directLimitLeft_symm_of_tmul`

English:
lemma directLimitLeft_symm_of_tmul
  given: {i : ι} (g : G i) (m : M)
  proof: fromDirectLimit_of_tmul f g m

中文:
引理 directLimitLeft_symm_of_tmul
  条件: {i : ι} (g : G i) (m : M)
  证明: fromDirectLimit_of_tmul f g m
-/
@[simp] lemma directLimitLeft_symm_of_tmul {i : ι} (g : G i) (m : M) :
    (directLimitLeft f M).symm (of _ _ _ _ _ (g otimesₜ m)) = of _ _ _ f _ g otimesₜ m :=
  fromDirectLimit_of_tmul f g m

/--
lemma `directLimitLeft_rTensor_of` / 引理 `directLimitLeft_rTensor_of`

English:
lemma directLimitLeft_rTensor_of
  given: {i : ι} (x : G i otimes[R] M)
  proof: x.induction_on (by simp) (by simp +contextual) (by simp +contextual)

中文:
引理 directLimitLeft_rTensor_of
  条件: {i : ι} (x : G i otimes[R] M)
  证明: x.induction_on (by simp) (by simp +contextual) (by simp +contextual)

Depends on / 依赖: contextual, induction_on, x.induction_on
-/
lemma directLimitLeft_rTensor_of {i : ι} (x : G i otimes[R] M) :
    directLimitLeft f M (LinearMap.rTensor M (of ..) x) = of _ _ _ (f ▷ M) _ x :=
  x.induction_on (by simp) (by simp +contextual) (by simp +contextual)

/--
Definition of `directLimitRight` / `directLimitRight` 的定义

English:
definition directLimitRight
  signature: :
  body: TensorProduct.comm _ _ _ ≪≫ₗ directLimitLeft f M ≪≫ₗ
    Module.DirectLimit.congr (fun _ => TensorProduct.comm _ _ _)
      (fun i j h => TensorProduct.ext <| DFunLike.ext _ _ <| by aesop)

中文:
定义 directLimitRight
  签名: :
  定义体: TensorProduct.comm _ _ _ ≪≫ₗ directLimitLeft f M ≪≫ₗ
    Module.DirectLimit.congr (fun _ => TensorProduct.comm _ _ _)
      (fun i j h => TensorProduct.ext <| DFunLike.ext _ _ <| by aesop)

Depends on / 依赖: DFunLike, DFunLike.ext, DirectLimit, Module, Module.DirectLimit.congr, TensorProduct, TensorProduct.comm, TensorProduct.ext, directLimitLeft
-/
noncomputable def directLimitRight :
    M otimes[R] DirectLimit G f ≃ₗ[R] DirectLimit (M otimes[R] G ·) (M ◁ f) :=
  TensorProduct.comm _ _ _ ≪≫ₗ directLimitLeft f M ≪≫ₗ
    Module.DirectLimit.congr (fun _ => TensorProduct.comm _ _ _)
      (fun i j h => TensorProduct.ext <| DFunLike.ext _ _ <| by aesop)

/--
lemma `directLimitRight_tmul_of` / 引理 `directLimitRight_tmul_of`

English:
lemma directLimitRight_tmul_of
  given: {i : ι} (m : M) (g : G i)
  proof: by
  simp [directLimitRight, congr_apply_of]

中文:
引理 directLimitRight_tmul_of
  条件: {i : ι} (m : M) (g : G i)
  证明: by
  simp [directLimitRight, congr_apply_of]
-/
@[simp] lemma directLimitRight_tmul_of {i : ι} (m : M) (g : G i) :
    directLimitRight f M (m otimesₜ of _ _ _ _ _ g) = of _ _ _ _ i (m otimesₜ g) := by
  simp [directLimitRight, congr_apply_of]

/--
lemma `directLimitRight_symm_of_tmul` / 引理 `directLimitRight_symm_of_tmul`

English:
lemma directLimitRight_symm_of_tmul
  given: {i : ι} (m : M) (g : G i)
  proof: by
  simp [directLimitRight, congr_symm_apply_of]

中文:
引理 directLimitRight_symm_of_tmul
  条件: {i : ι} (m : M) (g : G i)
  证明: by
  simp [directLimitRight, congr_symm_apply_of]
-/
@[simp] lemma directLimitRight_symm_of_tmul {i : ι} (m : M) (g : G i) :
    (directLimitRight f M).symm (of _ _ _ _ _ (m otimesₜ g)) = m otimesₜ of _ _ _ f _ g := by
  simp [directLimitRight, congr_symm_apply_of]

variable [DirectedSystem G (f · · ·)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DirectedSystem (G · otimes[R] M) (f ▷ M)
  body: by
    convert! LinearMap.rTensor_id_apply M (G i) x; ext; apply DirectedSystem.map_self'
  map_map _ _ _ _ _ x := by
    convert! ← (LinearMap.rTensor_comp_apply M _ _ x).symm; ext; apply DirectedSystem.map_map' f

中文:
实例 :
  签名: DirectedSystem (G · otimes[R] M) (f ▷ M)
  定义体: by
    convert! LinearMap.rTensor_id_apply M (G i) x; ext; apply DirectedSystem.map_self'
  map_map _ _ _ _ _ x := by
    convert! ← (LinearMap.rTensor_comp_apply M _ _ x).symm; ext; apply DirectedSystem.map_map' f

Depends on / 依赖: DirectedSystem, DirectedSystem.map_map, DirectedSystem.map_self, LinearMap, LinearMap.rTensor_comp_apply, LinearMap.rTensor_id_apply, convert, map_map, map_self, rTensor_comp_apply, rTensor_id_apply
-/
instance : DirectedSystem (G · otimes[R] M) (f ▷ M) where
  map_self i x := by
    convert! LinearMap.rTensor_id_apply M (G i) x; ext; apply DirectedSystem.map_self'
  map_map _ _ _ _ _ x := by
    convert! ← (LinearMap.rTensor_comp_apply M _ _ x).symm; ext; apply DirectedSystem.map_map' f

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DirectedSystem (M otimes[R] G ·) (M ◁ f)
  body: by
    convert! LinearMap.lTensor_id_apply M _ x; ext; apply DirectedSystem.map_self'
  map_map _ _ _ h₁ h₂ x := by
    convert! ← (LinearMap.lTensor_comp_apply M _ _ x).symm; ext; apply DirectedSystem.map_map' f

中文:
实例 :
  签名: DirectedSystem (M otimes[R] G ·) (M ◁ f)
  定义体: by
    convert! LinearMap.lTensor_id_apply M _ x; ext; apply DirectedSystem.map_self'
  map_map _ _ _ h₁ h₂ x := by
    convert! ← (LinearMap.lTensor_comp_apply M _ _ x).symm; ext; apply DirectedSystem.map_map' f

Depends on / 依赖: DirectedSystem, DirectedSystem.map_map, DirectedSystem.map_self, LinearMap, LinearMap.lTensor_comp_apply, LinearMap.lTensor_id_apply, convert, lTensor_comp_apply, lTensor_id_apply, map_map, map_self
-/
instance : DirectedSystem (M otimes[R] G ·) (M ◁ f) where
  map_self i x := by
    convert! LinearMap.lTensor_id_apply M _ x; ext; apply DirectedSystem.map_self'
  map_map _ _ _ h₁ h₂ x := by
    convert! ← (LinearMap.lTensor_comp_apply M _ _ x).symm; ext; apply DirectedSystem.map_map' f

end TensorProduct
