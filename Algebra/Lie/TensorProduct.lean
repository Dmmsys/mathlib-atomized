/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Tensor products of Lie modules

Tensor products of Lie modules carry natural Lie module structures.

## Tags

lie module, tensor product, universal property
-/

@[expose] public section

universe u v w w₁ w₂ w₃

variable {R : Type u} [CommRing R]

open LieModule

namespace TensorProduct

open scoped TensorProduct

namespace LieModule

variable {L : Type v} {M : Type w} {N : Type w₁} {P : Type w₂} {Q : Type w₃}
variable [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]
variable [AddCommGroup P] [Module R P] [LieRingModule L P] [LieModule R L P]
variable [AddCommGroup Q] [Module R Q] [LieRingModule L Q] [LieModule R L Q]

attribute [local ext] TensorProduct.ext

/--
Definition of `hasBracketAux` / `hasBracketAux` 的定义

English:
definition hasBracketAux
  signature: (x : L)
  body: (toEnd R L M x).rTensor N + (toEnd R L N x).lTensor M

中文:
定义 hasBracketAux
  签名: (x : L)
  定义体: (toEnd R L M x).rTensor N + (toEnd R L N x).lTensor M

Depends on / 依赖: lTensor, rTensor
-/
def hasBracketAux (x : L) : Module.End R (M otimes[R] N) :=
  (toEnd R L M x).rTensor N + (toEnd R L N x).lTensor M

/--
Instance `lieRingModule` / 实例 `lieRingModule`

English:
instance lieRingModule
  signature: : LieRingModule L (M otimes[R] N) where
  body: hasBracketAux x
  add_lie x y t := by
    simp only [hasBracketAux, LinearMap.lTensor_add, LinearMap.rTensor_add, map_add,
      LinearMap.add_apply]
    abel
  lie_add _ := map_add _
  leibniz_lie x y t := by
    suffices (hasBracketAux x).comp (hasBracketAux y) =
        hasBracketAux ⁅x, y⁆ + (ha

中文:
实例 lieRingModule
  签名: : Lie环模 L (M otimes[R] N) where
  定义体: hasBracketAux x
  add_lie x y t := by
    simp only [hasBracketAux, LinearMap.lTensor_add, LinearMap.rTensor_add, map_add,
      LinearMap.add_apply]
    abel
  lie_add _ := map_add _
  leibniz_lie x y t := by
    suffices (hasBracketAux x).comp (hasBracketAux y) =
        hasBracketAux ⁅x, y⁆ + (ha

Depends on / 依赖: LinearMap, LinearMap.map_smul_of_tower, LocalizedModule, LocalizedModule.smul, hasBracketAux, map_smul_of_tower
-/
instance lieRingModule : LieRingModule L (M otimes[R] N) where
  bracket x := hasBracketAux x
  add_lie x y t := by
    simp only [hasBracketAux, LinearMap.lTensor_add, LinearMap.rTensor_add, map_add,
      LinearMap.add_apply]
    abel
  lie_add _ := map_add _
  leibniz_lie x y t := by
    suffices (hasBracketAux x).comp (hasBracketAux y) =
        hasBracketAux ⁅x, y⁆ + (hasBracketAux y).comp (hasBracketAux x) by
      rw [← LinearMap.comp_apply]; rw [this]; rfl
    ext m n
    simp only [hasBracketAux, AlgebraTensorModule.curry_apply, curry_apply, sub_tmul, tmul_sub,
      LinearMap.coe_restrictScalars, Function.comp_apply, LinearMap.coe_comp,
      LinearMap.rTensor_tmul, LieHom.map_lie, toEnd_apply_apply, LinearMap.add_apply,
      map_add, LieHom.lie_apply, Module.End.lie_apply, LinearMap.lTensor_tmul]
    abel

set_option backward.isDefEq.respectTransparency false in
/--
Instance `lieModule` / 实例 `lieModule`

English:
instance lieModule
  signature: : LieModule R L (M otimes[R] N) where
  body: by
    change hasBracketAux (c • x) _ = c • hasBracketAux _ _
    simp only [hasBracketAux, smul_add, LinearMap.rTensor_smul, LinearMap.smul_apply,
      LinearMap.lTensor_smul, map_smul, LinearMap.add_apply]
  lie_smul c _ := map_smul _ c

@[simp]

中文:
实例 lieModule
  签名: : Lie模 R L (M otimes[R] N) where
  定义体: by
    change hasBracketAux (c • x) _ = c • hasBracketAux _ _
    simp only [hasBracketAux, smul_add, LinearMap.rTensor_smul, LinearMap.smul_apply,
      LinearMap.lTensor_smul, map_smul, LinearMap.add_apply]
  lie_smul c _ := map_smul _ c

@[simp]

Depends on / 依赖: LinearMap, LinearMap.add_apply, LinearMap.lTensor_smul, LinearMap.rTensor_smul, LinearMap.smul_apply, LocalizedModule, LocalizedModule.mk_add_mk, add_apply, hasBracketAux, lTensor_smul, lie_smul, map_add, map_smul, mk_add_mk, rTensor_smul, smul_add, smul_apply
-/
instance lieModule : LieModule R L (M otimes[R] N) where
  smul_lie c x t := by
    change hasBracketAux (c • x) _ = c • hasBracketAux _ _
    simp only [hasBracketAux, smul_add, LinearMap.rTensor_smul, LinearMap.smul_apply,
      LinearMap.lTensor_smul, map_smul, LinearMap.add_apply]
  lie_smul c _ := map_smul _ c

@[simp]
/--
theorem `lie_tmul_right` / 定理 `lie_tmul_right`

English:
theorem lie_tmul_right
  given: (x : L) (m : M) (n : N)
  statement: ⁅x, m otimesₜ[R] n⁆ = ⁅x, m⁆ otimesₜ n + m otimesₜ ⁅x, n⁆
  proof: show hasBracketAux x (m otimesₜ[R] n) = _ by
    simp only [hasBracketAux, LinearMap.rTensor_tmul, toEnd_apply_apply,
      LinearMap.add_apply, LinearMap.lTensor_tmul]

中文:
定理 lie_tmul_right
  条件: (x : L) (m : M) (n : N)
  结论: ⁅x, m otimesₜ[R] n⁆ = ⁅x, m⁆ otimesₜ n + m otimesₜ ⁅x, n⁆
  证明: show hasBracketAux x (m otimesₜ[R] n) = _ by
    simp only [hasBracketAux, LinearMap.rTensor_tmul, toEnd_apply_apply,
      LinearMap.add_apply, LinearMap.lTensor_tmul]

Depends on / 依赖: LinearMap, LinearMap.add_apply, LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, _smul, add_apply, hasBracketAux, lTensor_tmul, rTensor_tmul, toEnd_apply_apply, zero_smul
-/
theorem lie_tmul_right (x : L) (m : M) (n : N) : ⁅x, m otimesₜ[R] n⁆ = ⁅x, m⁆ otimesₜ n + m otimesₜ ⁅x, n⁆ :=
  show hasBracketAux x (m otimesₜ[R] n) = _ by
    simp only [hasBracketAux, LinearMap.rTensor_tmul, toEnd_apply_apply,
      LinearMap.add_apply, LinearMap.lTensor_tmul]

variable (R L M N P Q)

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : (M ->ₗ[R] N ->ₗ[R] P) ≃ₗ⁅R,L⁆ M otimes[R] N ->ₗ[R] P
  body: { TensorProduct.lift.equiv (.id R) M N P with
    map_lie' := fun {x f} => by
      ext m n
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
        AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
        lift.equiv_apply, LieHom.lie_app

中文:
定义 lift
  签名: : (M ->ₗ[R] N ->ₗ[R] P) ≃ₗ⁅R,L⁆ M otimes[R] N ->ₗ[R] P
  定义体: { TensorProduct.lift.equiv (.id R) M N P with
    map_lie' := fun {x f} => by
      ext m n
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
        AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
        lift.equiv_apply, LieHom.lie_app

Depends on / 依赖: AddHom, AddHom.toFun_eq_coe, AlgebraTensorModule, AlgebraTensorModule.curry_apply, LieHom, LieHom.lie_apply, LinearEquiv, LinearEquiv.coe_coe, LinearMap, LinearMap.coe_restrictScalars, LinearMap.coe_toAddHom, LinearMap.sub_apply, Module, Module.End.algebraMap_isUnit_inv_apply_eq_iff, Submonoid, Submonoid.coe_one, TensorProduct, TensorProduct.lift.equiv, algebraMap_isUnit_inv_apply_eq_iff, coe_coe
-/
def lift : (M ->ₗ[R] N ->ₗ[R] P) ≃ₗ⁅R,L⁆ M otimes[R] N ->ₗ[R] P :=
  { TensorProduct.lift.equiv (.id R) M N P with
    map_lie' := fun {x f} => by
      ext m n
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
        AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
        lift.equiv_apply, LieHom.lie_apply, LinearMap.sub_apply, lie_tmul_right, map_add]
      abel }

@[simp]
/--
theorem `lift_apply` / 定理 `lift_apply`

English:
theorem lift_apply
  given: (f : M ->ₗ[R] N ->ₗ[R] P) (m : M) (n : N)
  statement: lift R L M N P f (m otimesₜ n) = f m n
  proof: rfl

中文:
定理 lift_apply
  条件: (f : M ->ₗ[R] N ->ₗ[R] P) (m : M) (n : N)
  结论: lift R L M N P f (m otimesₜ n) = f m n
  证明: rfl

Depends on / 依赖: LocalizedModule, LocalizedModule.mk_cancel, Module, Module.End.algebraMap_isUnit_inv_apply_eq_iff, OneMemClass, OneMemClass.coe_one, _one, algebraMap_isUnit_inv_apply_eq_iff, coe_one, fromLocalizedModule_mk, mk_cancel, one_smul
-/
theorem lift_apply (f : M ->ₗ[R] N ->ₗ[R] P) (m : M) (n : N) : lift R L M N P f (m otimesₜ n) = f m n :=
  rfl

/--
Definition of `liftLie` / `liftLie` 的定义

English:
definition liftLie
  signature: : (M ->ₗ⁅R,L⁆ N ->ₗ[R] P) ≃ₗ[R] M otimes[R] N ->ₗ⁅R,L⁆ P
  body: maxTrivLinearMapEquivLieModuleHom.symm ≪≫ₗ ↑(maxTrivEquiv (lift R L M N P)) ≪≫ₗ
    maxTrivLinearMapEquivLieModuleHom

@[simp]

中文:
定义 liftLie
  签名: : (M ->ₗ⁅R,L⁆ N ->ₗ[R] P) ≃ₗ[R] M otimes[R] N ->ₗ⁅R,L⁆ P
  定义体: maxTrivLinearMapEquivLieModuleHom.symm ≪≫ₗ ↑(maxTrivEquiv (lift R L M N P)) ≪≫ₗ
    maxTrivLinearMapEquivLieModuleHom

@[simp]

Depends on / 依赖: Submonoid, Submonoid.smul_def, _cancel, _smul, maxTrivEquiv, maxTrivLinearMapEquivLieModuleHom, maxTrivLinearMapEquivLieModuleHom.symm, smul_def
-/
def liftLie : (M ->ₗ⁅R,L⁆ N ->ₗ[R] P) ≃ₗ[R] M otimes[R] N ->ₗ⁅R,L⁆ P :=
  maxTrivLinearMapEquivLieModuleHom.symm ≪≫ₗ ↑(maxTrivEquiv (lift R L M N P)) ≪≫ₗ
    maxTrivLinearMapEquivLieModuleHom

@[simp]
/--
theorem `coe_liftLie_eq_lift_coe` / 定理 `coe_liftLie_eq_lift_coe`

English:
theorem coe_liftLie_eq_lift_coe
  given: (f : M ->ₗ⁅R,L⁆ N ->ₗ[R] P)
  proof: by
  tauto

中文:
定理 coe_liftLie_eq_lift_coe
  条件: (f : M ->ₗ⁅R,L⁆ N ->ₗ[R] P)
  证明: by
  tauto

Depends on / 依赖: LocalizedModule, LocalizedModule.mk_cancel_common_left, mk_cancel_common_left
-/
theorem coe_liftLie_eq_lift_coe (f : M ->ₗ⁅R,L⁆ N ->ₗ[R] P) :
    ⇑(liftLie R L M N P f) = lift R L M N P f := by
  tauto

/--
theorem `liftLie_apply` / 定理 `liftLie_apply`

English:
theorem liftLie_apply
  given: (f : M ->ₗ⁅R,L⁆ N ->ₗ[R] P) (m : M) (n : N)
  proof: by
  simp only [coe_liftLie_eq_lift_coe, LieModuleHom.coe_toLinearMap, lift_apply]

中文:
定理 liftLie_apply
  条件: (f : M ->ₗ⁅R,L⁆ N ->ₗ[R] P) (m : M) (n : N)
  证明: by
  simp only [coe_liftLie_eq_lift_coe, LieModuleHom.coe_toLinearMap, lift_apply]

Depends on / 依赖: LieModuleHom, LieModuleHom.coe_toLinearMap, LocalizedModule, LocalizedModule.mk_cancel_common_right, coe_liftLie_eq_lift_coe, coe_toLinearMap, lift_apply, mk_cancel_common_right
-/
theorem liftLie_apply (f : M ->ₗ⁅R,L⁆ N ->ₗ[R] P) (m : M) (n : N) :
    liftLie R L M N P f (m otimesₜ n) = f m n := by
  simp only [coe_liftLie_eq_lift_coe, LieModuleHom.coe_toLinearMap, lift_apply]

variable {R L M N P Q}

/-- A pair of Lie module morphisms `f : M → P` and `g : N → Q`, induce a Lie module morphism:
`M ⊗ N → P ⊗ Q`. -/
nonrec def map (f : M ->ₗ⁅R,L⁆ P) (g : N ->ₗ⁅R,L⁆ Q) : M otimes[R] N ->ₗ⁅R,L⁆ P otimes[R] Q :=
  { map (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q) with
    map_lie' := fun {x t} => by
      simp only [LinearMap.toFun_eq_coe]
      refine t.induction_on ?_ ?_ ?_
      · simp only [map_zero, lie_zero]
      · intro m n
        simp only [LieModuleHom.coe_toLinearMap, lie_tmul_right, LieModuleHom.map_lie, map_tmul,
          map_add]
      · intro t₁ t₂ ht₁ ht₂; simp only [ht₁, ht₂, lie_add, map_add] }

@[simp]
/--
theorem `toLinearMap_map` / 定理 `toLinearMap_map`

English:
theorem toLinearMap_map
  given: (f : M ->ₗ⁅R,L⁆ P) (g : N ->ₗ⁅R,L⁆ Q)
  proof: rfl

@[simp]
nonrec theorem map_tmul (f : M ->ₗ⁅R,L⁆ P) (g : N ->ₗ⁅R,L⁆ Q) (m : M) (n : N) :
    map f g (m otimesₜ n) = f m otimesₜ g n :=
  map_tmul _ _ _ _

中文:
定理 toLinearMap_map
  条件: (f : M ->ₗ⁅R,L⁆ P) (g : N ->ₗ⁅R,L⁆ Q)
  证明: rfl

@[simp]
nonrec theorem map_tmul (f : M ->ₗ⁅R,L⁆ P) (g : N ->ₗ⁅R,L⁆ Q) (m : M) (n : N) :
    map f g (m otimesₜ n) = f m otimesₜ g n :=
  map_tmul _ _ _ _

Depends on / 依赖: _add_mk, _cancel_left, smul_add
-/
theorem toLinearMap_map (f : M ->ₗ⁅R,L⁆ P) (g : N ->ₗ⁅R,L⁆ Q) :
    (map f g : M otimes[R] N ->ₗ[R] P otimes[R] Q) = TensorProduct.map (f : M ->ₗ[R] P) (g : N ->ₗ[R] Q) :=
  rfl

@[simp]
nonrec theorem map_tmul (f : M ->ₗ⁅R,L⁆ P) (g : N ->ₗ⁅R,L⁆ Q) (m : M) (n : N) :
    map f g (m otimesₜ n) = f m otimesₜ g n :=
  map_tmul _ _ _ _

/--
Definition of `mapIncl` / `mapIncl` 的定义

English:
definition mapIncl
  signature: (M' : LieSubmodule R L M) (N' : LieSubmodule R L N)
  body: map M'.incl N'.incl

@[simp]

中文:
定义 mapIncl
  签名: (M' : Lie子模 R L M) (N' : Lie子模 R L N)
  定义体: map M'.incl N'.incl

@[simp]

Depends on / 依赖: LocalizedModule, LocalizedModule.mk_eq, eq_comm, eq_iff, fromLocalizedModule, fromLocalizedModule.inj, mk_eq, simp_rw
-/
def mapIncl (M' : LieSubmodule R L M) (N' : LieSubmodule R L N) : M' otimes[R] N' ->ₗ⁅R,L⁆ M otimes[R] N :=
  map M'.incl N'.incl

@[simp]
/--
theorem `mapIncl_def` / 定理 `mapIncl_def`

English:
theorem mapIncl_def
  given: (M' : LieSubmodule R L M) (N' : LieSubmodule R L N)
  proof: rfl

中文:
定理 mapIncl_def
  条件: (M' : Lie子模 R L M) (N' : Lie子模 R L N)
  证明: rfl

Depends on / 依赖: LocalizedModule, LocalizedModule.mk_neg, map_neg, mk_neg
-/
theorem mapIncl_def (M' : LieSubmodule R L M) (N' : LieSubmodule R L N) :
    mapIncl M' N' = map M'.incl N'.incl :=
  rfl

end LieModule

end TensorProduct

namespace LieModule

open scoped TensorProduct

variable (R) (L : Type v) (M : Type w)
variable [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/--
Definition of `toModuleHom` / `toModuleHom` 的定义

English:
definition toModuleHom
  signature: : L otimes[R] M ->ₗ⁅R,L⁆ M
  body: TensorProduct.LieModule.liftLie R L L M M
    { (toEnd R L M : L ->ₗ[R] M ->ₗ[R] M) with
      map_lie' := fun {x m} => by ext n; simp [LieRing.of_associative_ring_bracket] }

@[simp]

中文:
定义 toModuleHom
  签名: : L otimes[R] M ->ₗ⁅R,L⁆ M
  定义体: TensorProduct.LieModule.liftLie R L L M M
    { (toEnd R L M : L ->ₗ[R] M ->ₗ[R] M) with
      map_lie' := fun {x m} => by ext n; simp [LieRing.of_associative_ring_bracket] }

@[simp]

Depends on / 依赖: LieModule, LieRing, LieRing.of_associative_ring_bracket, TensorProduct, TensorProduct.LieModule.liftLie, _add, _neg, liftLie, map_lie, of_associative_ring_bracket, sub_eq_add_neg
-/
def toModuleHom : L otimes[R] M ->ₗ⁅R,L⁆ M :=
  TensorProduct.LieModule.liftLie R L L M M
    { (toEnd R L M : L ->ₗ[R] M ->ₗ[R] M) with
      map_lie' := fun {x m} => by ext n; simp [LieRing.of_associative_ring_bracket] }

@[simp]
/--
theorem `toModuleHom_apply` / 定理 `toModuleHom_apply`

English:
theorem toModuleHom_apply
  given: (x : L) (m : M)
  statement: toModuleHom R L M (x otimesₜ m) = ⁅x, m⁆
  proof: by
  simp only [toModuleHom, TensorProduct.LieModule.liftLie_apply, LieModuleHom.coe_mk,
    LieHom.coe_toLinearMap, toEnd_apply_apply]

中文:
定理 toModuleHom_apply
  条件: (x : L) (m : M)
  结论: toModuleHom R L M (x otimesₜ m) = ⁅x, m⁆
  证明: by
  simp only [toModuleHom, TensorProduct.LieModule.liftLie_apply, LieModuleHom.coe_mk,
    LieHom.coe_toLinearMap, toEnd_apply_apply]

Depends on / 依赖: LieHom, LieHom.coe_toLinearMap, LieModule, LieModuleHom, LieModuleHom.coe_mk, TensorProduct, TensorProduct.LieModule.liftLie_apply, _add_mk, _neg, coe_mk, coe_toLinearMap, liftLie_apply, smul_neg, sub_eq_add_neg, toEnd_apply_apply, toModuleHom
-/
theorem toModuleHom_apply (x : L) (m : M) : toModuleHom R L M (x otimesₜ m) = ⁅x, m⁆ := by
  simp only [toModuleHom, TensorProduct.LieModule.liftLie_apply, LieModuleHom.coe_mk,
    LieHom.coe_toLinearMap, toEnd_apply_apply]

end LieModule

namespace LieSubmodule

open scoped TensorProduct

open TensorProduct.LieModule

open LieModule

variable {L : Type v} {M : Type w}
variable [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable (I : LieIdeal R L) (N : LieSubmodule R L M)

/--
theorem `lieIdeal_oper_eq_tensor_map_range` / 定理 `lieIdeal_oper_eq_tensor_map_range`

English:
theorem lieIdeal_oper_eq_tensor_map_range
  proof: by
  rw [← toSubmodule_inj]; rw [lieIdeal_oper_eq_linear_span]; rw [LieModuleHom.toSubmodule_range]; rw [LieModuleHom.toLinearMap_comp]; rw [LinearMap.range_comp]; rw [mapIncl_def]; rw [toLinearMap_map]; rw [TensorProduct.range_map_eq_span_tmul]; rw [Submodule.map_span]
  congr; ext m; constructor
 

中文:
定理 lieIdeal_oper_eq_tensor_map_range
  证明: by
  rw [← toSubmodule_inj]; rw [lieIdeal_oper_eq_linear_span]; rw [LieModuleHom.toSubmodule_range]; rw [LieModuleHom.toLinearMap_comp]; rw [LinearMap.range_comp]; rw [mapIncl_def]; rw [toLinearMap_map]; rw [TensorProduct.range_map_eq_span_tmul]; rw [Submodule.map_span]
  congr; ext m; constructor
 

Depends on / 依赖: LieModuleHom, LieModuleHom.toLinearMap_comp, LieModuleHom.toSubmodule_range, LinearMap, LinearMap.range_comp, Module, Module.End.algebraMap_isUnit_inv_apply_eq_iff, Submodule, Submodule.map_span, Submonoid, Submonoid.coe_mul, Submonoid.smul_def, TensorProduct, TensorProduct.range_map_eq_span_tmul, _cancel, _smul, algebraMap_isUnit_inv_apply_eq_iff, coe_mul, lieIdeal_oper_eq_linear_span, mapIncl_def
-/
theorem lieIdeal_oper_eq_tensor_map_range :
    ⁅I, N⁆ = ((toModuleHom R L M).comp (mapIncl I N : I otimes[R] N ->ₗ⁅R,L⁆ L otimes[R] M)).range := by
  rw [← toSubmodule_inj]; rw [lieIdeal_oper_eq_linear_span]; rw [LieModuleHom.toSubmodule_range]; rw [LieModuleHom.toLinearMap_comp]; rw [LinearMap.range_comp]; rw [mapIncl_def]; rw [toLinearMap_map]; rw [TensorProduct.range_map_eq_span_tmul]; rw [Submodule.map_span]
  congr; ext m; constructor
  · rintro ⟨⟨x, hx⟩, ⟨n, hn⟩, rfl⟩; use x otimesₜ n; constructor
    · use ⟨x, hx⟩, ⟨n, hn⟩; rfl
    · simp
  · rintro ⟨t, ⟨⟨x, hx⟩, ⟨n, hn⟩, rfl⟩, h⟩; rw [← h]; use ⟨x, hx⟩, ⟨n, hn⟩; rfl

end LieSubmodule
