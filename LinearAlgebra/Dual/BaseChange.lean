/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
/-!
# Base change for the dual of a module

* `Module.Dual.congr` : equivalent modules have equivalent duals.

If `f : Module.Dual R V` and `Algebra R A`, then

* `Module.Dual.baseChange A f` is the element
  of `Module.Dual A (A ⊗[R] V)` deduced by base change.

* `Module.Dual.baseChangeHom` is the `R`-linear map
  given by `Module.Dual.baseChange`.

* `IsBaseChange.dual` : for finite free modules, taking dual commutes with base change.

-/

@[expose] public section

namespace Module.Dual

open TensorProduct LinearEquiv

variable {R : Type*} [CommSemiring R]
  {V : Type*} [AddCommMonoid V] [Module R V]
  {W : Type*} [AddCommMonoid W] [Module R W]
  (A : Type*) [CommSemiring A] [Algebra R A]

/--
Definition of `congr` / `congr` 的定义

English:
definition congr
  signature: (e : V ≃ₗ[R] W)
  body: congrLeft R R e

中文:
定义 congr
  签名: (e : V ≃ₗ[R] W)
  定义体: congrLeft R R e
-/
@[simps!] def congr (e : V ≃ₗ[R] W) :
    Dual R V ≃ₗ[R] Dual R W := congrLeft R R e

/--
Definition of `baseChange` / `baseChange` 的定义

English:
definition baseChange
  signature: : Dual R V ->ₗ[R] Dual A (A otimes[R] V)
  body: (AlgebraTensorModule.rid R A A).compRight R ∘ₗ LinearMap.baseChangeHom R A V R

@[simp]

中文:
定义 baseChange
  签名: : Dual R V ->ₗ[R] Dual A (A otimes[R] V)
  定义体: (AlgebraTensorModule.rid R A A).compRight R ∘ₗ LinearMap.baseChangeHom R A V R

@[simp]

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.rid, LinearMap, LinearMap.baseChangeHom, baseChangeHom, compRight
-/
def baseChange : Dual R V ->ₗ[R] Dual A (A otimes[R] V) :=
  (AlgebraTensorModule.rid R A A).compRight R ∘ₗ LinearMap.baseChangeHom R A V R

@[simp]
/--
theorem `baseChange_apply_tmul` / 定理 `baseChange_apply_tmul`

English:
theorem baseChange_apply_tmul
  given: (f : Dual R V) (a : A) (v : V)
  proof: rfl

中文:
定理 baseChange_apply_tmul
  条件: (f : Dual R V) (a : A) (v : V)
  证明: rfl
-/
theorem baseChange_apply_tmul (f : Dual R V) (a : A) (v : V) :
    f.baseChange A (a otimesₜ v) = (f v) • a :=
  rfl

variable {B : Type*} [CommSemiring B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

open AlgebraTensorModule in
/--
theorem `baseChange_baseChange` / 定理 `baseChange_baseChange`

English:
theorem baseChange_baseChange
  given: (f : Dual R V)
  proof: by
  ext; simp

中文:
定理 baseChange_baseChange
  条件: (f : Dual R V)
  证明: by
  ext; simp
-/
theorem baseChange_baseChange (f : Dual R V) :
    (f.baseChange A).baseChange B = (congr (cancelBaseChange R A B B V)).symm (f.baseChange B) := by
  ext; simp

end Module.Dual

namespace IsBaseChange

open Module TensorProduct

variable {R : Type*} [CommSemiring R]
  {V : Type*} [AddCommMonoid V] [Module R V]
  {W : Type*} [AddCommMonoid W] [Module R W]
  {A : Type*} [CommSemiring A] [Algebra R A] [Module A W] [IsScalarTower R A W]
  {j : V ->ₗ[R] W} (ibc : IsBaseChange A j)

/--
Definition of `toDual` / `toDual` 的定义

English:
definition toDual
  signature: :
  body: linearMapLeftRightHom ibc (Algebra.linearMap R A)

中文:
定义 toDual
  签名: :
  定义体: linearMapLeftRightHom ibc (Algebra.linearMap R A)

Depends on / 依赖: Algebra, Algebra.linearMap, linearMap, linearMapLeftRightHom
-/
noncomputable def toDual :
    Dual R V ->ₗ[R] Dual A W :=
  linearMapLeftRightHom ibc (Algebra.linearMap R A)

/--
theorem `toDual_comp_apply` / 定理 `toDual_comp_apply`

English:
theorem toDual_comp_apply
  given: (f : Dual R V) (v : V)
  proof: by
  simp [toDual, linearMapLeftRightHom_comp_apply]

中文:
定理 toDual_comp_apply
  条件: (f : Dual R V) (v : V)
  证明: by
  simp [toDual, linearMapLeftRightHom_comp_apply]

Depends on / 依赖: linearMapLeftRightHom_comp_apply, toDual
-/
theorem toDual_comp_apply (f : Dual R V) (v : V) :
    ibc.toDual f (j v) = algebraMap R A (f v) := by
  simp [toDual, linearMapLeftRightHom_comp_apply]

/--
theorem `toDual_apply` / 定理 `toDual_apply`

English:
theorem toDual_apply
  given: (f : Dual R V)
  proof: by
  apply ibc.algHom_ext
  intro v
  simp [toDual_comp_apply, Algebra.algebraMap_eq_smul_one]

中文:
定理 toDual_apply
  条件: (f : Dual R V)
  证明: by
  apply ibc.algHom_ext
  intro v
  simp [toDual_comp_apply, Algebra.algebraMap_eq_smul_one]

Depends on / 依赖: Algebra, Algebra.algebraMap_eq_smul_one, _congr_ae, _zero, algHom_ext, algebraMap_eq_smul_one, eLpNorm, hf_zero, hq0_lt, ibc.algHom_ext, toDual_comp_apply
-/
theorem toDual_apply (f : Dual R V) :
    ibc.toDual f = (f.baseChange A).congr ibc.equiv := by
  apply ibc.algHom_ext
  intro v
  simp [toDual_comp_apply, Algebra.algebraMap_eq_smul_one]

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def toDualBaseChangeAux
  body: (TensorProduct.lift {
    toFun a := a • ibc.toDual
    map_add' a b := by simp [add_smul]
    map_smul' r a := by simp }).toAddHom
  map_smul' a g := by
    induction g using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => aesop
    | tmul b f => simp [TensorProduct.smul_t

中文:
定义 noncomputable
  签名: def toDualBaseChangeAux
  定义体: (TensorProduct.lift {
    toFun a := a • ibc.toDual
    map_add' a b := by simp [add_smul]
    map_smul' r a := by simp }).toAddHom
  map_smul' a g := by
    induction g using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => aesop
    | tmul b f => simp [TensorProduct.smul_t

Depends on / 依赖: _congr_ae, _zero, eLpNorm, hf_zero, hq0_ne
-/
private noncomputable def toDualBaseChangeAux :
    A otimes[R] Dual R V ->ₗ[A] Dual A W where
  toAddHom := (TensorProduct.lift {
    toFun a := a • ibc.toDual
    map_add' a b := by simp [add_smul]
    map_smul' r a := by simp }).toAddHom
  map_smul' a g := by
    induction g using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => aesop
    | tmul b f => simp [TensorProduct.smul_tmul', mul_smul]

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
/--
theorem `toDualBaseChangeAux_tmul` / 定理 `toDualBaseChangeAux_tmul`

English:
theorem toDualBaseChangeAux_tmul
  given: (a : A) (f : Dual R V) (v : V)
  proof: by
  simp [toDualBaseChangeAux, toDual_comp_apply]

中文:
定理 toDualBaseChangeAux_tmul
  条件: (a : A) (f : Dual R V) (v : V)
  证明: by
  simp [toDualBaseChangeAux, toDual_comp_apply]
-/
private theorem toDualBaseChangeAux_tmul (a : A) (f : Dual R V) (v : V) :
    (ibc.toDualBaseChangeAux (a otimesₜ[R] f)) (j v) = a * algebraMap R A (f v) := by
  simp [toDualBaseChangeAux, toDual_comp_apply]

variable [Free R V] [Module.Finite R V]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `toDualBaseChange` / `toDualBaseChange` 的定义

English:
definition toDualBaseChange
  signature: :
  body: by
  apply LinearEquiv.ofBijective ibc.toDualBaseChangeAux
  let b := Free.chooseBasis R V
  set ι := Free.ChooseBasisIndex R V
  have ibc_pow : IsBaseChange A ((Algebra.linearMap R A).compLeft ι) := (linearMap R A).finitePow ι
  suffices ibc.toDualBaseChangeAux =
      (((b.constr R).symm.baseChang

中文:
定义 toDualBaseChange
  签名: :
  定义体: by
  apply LinearEquiv.ofBijective ibc.toDualBaseChangeAux
  let b := Free.chooseBasis R V
  set ι := Free.ChooseBasisIndex R V
  have ibc_pow : IsBaseChange A ((Algebra.linearMap R A).compLeft ι) := (linearMap R A).finitePow ι
  suffices ibc.toDualBaseChangeAux =
      (((b.constr R).symm.baseChang

Depends on / 依赖: Algebra, Algebra.linearMap, AlgebraTensorModule, AlgebraTensorModule.curry_apply, ChooseBasisIndex, Free.ChooseBasisIndex, Free.chooseBasis, IsBaseChange, LinearEquiv, LinearEquiv.bijective, LinearEquiv.coe_coe, LinearEquiv.ofBijective, LinearMap, LinearMap.coe_restrictScalars, _congr_enorm_ae, _zero, b.constr, baseChange, bijective, chooseBasis
-/
noncomputable def toDualBaseChange :
    A otimes[R] Dual R V ≃ₗ[A] Dual A W := by
  apply LinearEquiv.ofBijective ibc.toDualBaseChangeAux
  let b := Free.chooseBasis R V
  set ι := Free.ChooseBasisIndex R V
  have ibc_pow : IsBaseChange A ((Algebra.linearMap R A).compLeft ι) := (linearMap R A).finitePow ι
  suffices ibc.toDualBaseChangeAux =
      (((b.constr R).symm.baseChange ..).trans ibc_pow.equiv).trans ((ibc.basis b).constr A) from
    this ▸ LinearEquiv.bijective _
  ext f w
  simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
    LinearEquiv.coe_coe, LinearEquiv.trans_apply]
  induction w using ibc.inductionOn with
  | zero => simp
  | tmul v =>
    simp only [toDualBaseChangeAux_tmul, one_mul]
    conv_lhs => rw [← Basis.sum_equivFun b v, map_sum]
    simp [LinearEquiv.baseChange, basis_repr_comp_apply]
  | smul a w h => simp [h]
  | add x y hx hy => simp [map_add, hx, hy]

/--
theorem `toDualBaseChange_tmul` / 定理 `toDualBaseChange_tmul`

English:
theorem toDualBaseChange_tmul
  given: (a : A) (f : Dual R V) (v : V)
  proof: toDualBaseChangeAux_tmul ibc a f v

中文:
定理 toDualBaseChange_tmul
  条件: (a : A) (f : Dual R V) (v : V)
  证明: toDualBaseChangeAux_tmul ibc a f v

Depends on / 依赖: toDualBaseChangeAux_tmul
-/
theorem toDualBaseChange_tmul (a : A) (f : Dual R V) (v : V) :
    (ibc.toDualBaseChange (a otimesₜ[R] f)) (j v) = a * algebraMap R A (f v) :=
  toDualBaseChangeAux_tmul ibc a f v

set_option backward.isDefEq.respectTransparency false in
/--
theorem `dual` / 定理 `dual`

English:
theorem dual
  statement: IsBaseChange A (ibc.toDual)
  proof: by
  apply of_equiv (toDualBaseChange ibc)
  intro f
  simp [toDualBaseChange, toDualBaseChangeAux]

中文:
定理 dual
  结论: IsBaseChange A (ibc.toDual)
  证明: by
  apply of_equiv (toDualBaseChange ibc)
  intro f
  simp [toDualBaseChange, toDualBaseChangeAux]

Depends on / 依赖: of_equiv, toDualBaseChange, toDualBaseChangeAux
-/
theorem dual : IsBaseChange A (ibc.toDual) := by
  apply of_equiv (toDualBaseChange ibc)
  intro f
  simp [toDualBaseChange, toDualBaseChangeAux]

end IsBaseChange
