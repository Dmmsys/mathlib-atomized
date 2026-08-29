/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Topology.Algebra.ContinuousAffineMap

/-!
# Continuous affine equivalences

In this file, we define continuous affine equivalences, affine equivalences
which are continuous with continuous inverse.

## Main definitions
* `ContinuousAffineEquiv.refl k P`: the identity map as a `ContinuousAffineEquiv`;
* `e.symm`: the inverse map of a `ContinuousAffineEquiv` as a `ContinuousAffineEquiv`;
* `e.trans e'`: composition of two `ContinuousAffineEquiv`s; note that the order
  follows `mathlib`'s `CategoryTheory` convention (apply `e`, then `e'`),
  not the convention used in function composition and compositions of bundled morphisms.

* `e.toHomeomorph`: the continuous affine equivalence `e` as a homeomorphism
* `e.toContinuousAffineMap`: the continuous affine equivalence `e` as a continuous affine map
* `ContinuousLinearEquiv.toContinuousAffineEquiv`: a continuous linear equivalence as a continuous
  affine equivalence
* `ContinuousAffineEquiv.constVAdd`: `AffineEquiv.constVAdd` as a continuous affine equivalence

## TODO
- equip `ContinuousAffineEquiv k P P` with a `Group` structure,
  with multiplication corresponding to composition in `AffineEquiv.group`.

-/

@[expose] public section

open Function

/--
Definition of `ContinuousAffineEquiv` / `ContinuousAffineEquiv` 的定义

English:
structure ContinuousAffineEquiv
  parameters: (k P₁ P₂ : Type*) {V₁ V₂ : Type*} [Ring k]
  extends: P₁ ≃ᵃ[k] P₂
  axioms and operations (2):
    - continuous_toFun : Continuous toFun  [default: by fun_prop]
    - continuous_invFun : Continuous invFun  [default: by fun_prop]

中文:
结构 余ntinuousAffine等价
  参数: (k P₁ P₂ : 类型) {V₁ V₂ : 类型} [环 k]
  继承: P₁ ≃ᵃ[k] P₂
  公理与运算 (2 个):
    - continuous_toFun : 连续 toFun  [默认: by fun_prop]
    - continuous_invFun : 连续 invFun  [默认: by fun_prop]

Depends on / 依赖: Continuous, continuous_invFun, fun_prop, invFun
-/
structure ContinuousAffineEquiv (k P₁ P₂ : Type*) {V₁ V₂ : Type*} [Ring k]
    [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁] [TopologicalSpace P₁]
    [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂] [TopologicalSpace P₂]
    extends P₁ ≃ᵃ[k] P₂ where
  continuous_toFun : Continuous toFun := by fun_prop
  continuous_invFun : Continuous invFun := by fun_prop

@[inherit_doc]
notation:25 P₁ " ≃ᴬ[" k:25 "] " P₂:0 => ContinuousAffineEquiv k P₁ P₂

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [Module k V₁] [AddTorsor V₁ P₁] [TopologicalSpace P₁]
  [AddCommGroup V₂] [Module k V₂] [AddTorsor V₂ P₂] [TopologicalSpace P₂]
  [AddCommGroup V₃] [Module k V₃] [AddTorsor V₃ P₃] [TopologicalSpace P₃]
  [AddCommGroup V₄] [Module k V₄] [AddTorsor V₄ P₄] [TopologicalSpace P₄]

namespace ContinuousAffineEquiv

-- Basic set-up: standard fields, coercions and ext lemmas
section Basic

/--
Definition of `toHomeomorph` / `toHomeomorph` 的定义

English:
definition toHomeomorph
  signature: (e : P₁ ≃ᴬ[k] P₂)
  body: e

中文:
定义 toHomeomorph
  签名: (e : P₁ ≃ᴬ[k] P₂)
  定义体: e
-/
def toHomeomorph (e : P₁ ≃ᴬ[k] P₂) : P₁ ≃ₜ P₂ where
  __ := e

/--
theorem `toAffineEquiv_injective` / 定理 `toAffineEquiv_injective`

English:
theorem toAffineEquiv_injective
  statement: Injective (toAffineEquiv : (P₁ ≃ᴬ[k] P₂) -> P₁ ≃ᵃ[k] P₂)
  proof: by
  rintro ⟨e, econt, einv_cont⟩ ⟨e', e'cont, e'inv_cont⟩ H
  congr

中文:
定理 toAffineEquiv_injective
  结论: 单射 (toAffineEquiv : (P₁ ≃ᴬ[k] P₂) -> P₁ ≃ᵃ[k] P₂)
  证明: by
  rintro ⟨e, econt, einv_cont⟩ ⟨e', e'cont, e'inv_cont⟩ H
  congr

Depends on / 依赖: einv_cont, inv_cont
-/
theorem toAffineEquiv_injective : Injective (toAffineEquiv : (P₁ ≃ᴬ[k] P₂) -> P₁ ≃ᵃ[k] P₂) := by
  rintro ⟨e, econt, einv_cont⟩ ⟨e', e'cont, e'inv_cont⟩ H
  congr

/--
Instance `instEquivLike` / 实例 `instEquivLike`

English:
instance instEquivLike
  signature: : EquivLike (P₁ ≃ᴬ[k] P₂) P₁ P₂ where
  body: f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' _ _ h _ := toAffineEquiv_injective (DFunLike.coe_injective h)

中文:
实例 instEquivLike
  签名: : 等价状 (P₁ ≃ᴬ[k] P₂) P₁ P₂ where
  定义体: f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' _ _ h _ := toAffineEquiv_injective (DFunLike.coe_injective h)

Depends on / 依赖: f.toFun
-/
instance instEquivLike : EquivLike (P₁ ≃ᴬ[k] P₂) P₁ P₂ where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' _ _ h _ := toAffineEquiv_injective (DFunLike.coe_injective h)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HomeomorphClass (P₁ ≃ᴬ[k] P₂) P₁ P₂
  body: f.continuous_toFun
  inv_continuous f := f.continuous_invFun

中文:
实例 :
  签名: 同胚类 (P₁ ≃ᴬ[k] P₂) P₁ P₂
  定义体: f.continuous_toFun
  inv_continuous f := f.continuous_invFun

Depends on / 依赖: continuous_toFun, f.continuous_toFun
-/
instance : HomeomorphClass (P₁ ≃ᴬ[k] P₂) P₁ P₂ where
  map_continuous f := f.continuous_toFun
  inv_continuous f := f.continuous_invFun

attribute [coe] ContinuousAffineEquiv.toAffineEquiv

/--
Instance `coe` / 实例 `coe`

English:
instance coe
  signature: : Coe (P₁ ≃ᴬ[k] P₂) (P₁ ≃ᵃ[k] P₂)
  body: ⟨toAffineEquiv⟩

中文:
实例 coe
  签名: : Coe (P₁ ≃ᴬ[k] P₂) (P₁ ≃ᵃ[k] P₂)
  定义体: ⟨toAffineEquiv⟩

Depends on / 依赖: toAffineEquiv
-/
instance coe : Coe (P₁ ≃ᴬ[k] P₂) (P₁ ≃ᵃ[k] P₂) := ⟨toAffineEquiv⟩

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike (P₁ ≃ᴬ[k] P₂) P₁ P₂ where
  body: f.toAffineEquiv
  coe_injective _ _ h := toAffineEquiv_injective (DFunLike.coe_injective h)

@[simp, norm_cast]

中文:
实例 instFunLike
  签名: : 函数状 (P₁ ≃ᴬ[k] P₂) P₁ P₂ where
  定义体: f.toAffineEquiv
  coe_injective _ _ h := toAffineEquiv_injective (DFunLike.coe_injective h)

@[simp, norm_cast]

Depends on / 依赖: f.toAffineEquiv, toAffineEquiv
-/
instance instFunLike : FunLike (P₁ ≃ᴬ[k] P₂) P₁ P₂ where
  coe f := f.toAffineEquiv
  coe_injective _ _ h := toAffineEquiv_injective (DFunLike.coe_injective h)

@[simp, norm_cast]
/--
theorem `coe_coe` / 定理 `coe_coe`

English:
theorem coe_coe
  given: (e : P₁ ≃ᴬ[k] P₂)
  statement: ⇑(e : P₁ ≃ᵃ[k] P₂) = e
  proof: rfl

@[simp]

中文:
定理 coe_coe
  条件: (e : P₁ ≃ᴬ[k] P₂)
  结论: ⇑(e : P₁ ≃ᵃ[k] P₂) = e
  证明: rfl

@[simp]
-/
theorem coe_coe (e : P₁ ≃ᴬ[k] P₂) : ⇑(e : P₁ ≃ᵃ[k] P₂) = e :=
  rfl

@[simp]
/--
theorem `coe_toEquiv` / 定理 `coe_toEquiv`

English:
theorem coe_toEquiv
  given: (e : P₁ ≃ᴬ[k] P₂)
  statement: ⇑e.toEquiv = e
  proof: rfl

@[ext]

中文:
定理 coe_toEquiv
  条件: (e : P₁ ≃ᴬ[k] P₂)
  结论: ⇑e.toEquiv = e
  证明: rfl

@[ext]
-/
theorem coe_toEquiv (e : P₁ ≃ᴬ[k] P₂) : ⇑e.toEquiv = e :=
  rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {e e' : P₁ ≃ᴬ[k] P₂} (h : forall x, e x = e' x)
  statement: e = e'
  proof: DFunLike.ext _ _ h

@[continuity]

中文:
定理 ext
  条件: {e e' : P₁ ≃ᴬ[k] P₂} (h : 对任意 x, e x = e' x)
  结论: e = e'
  证明: DFunLike.ext _ _ h

@[continuity]

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {e e' : P₁ ≃ᴬ[k] P₂} (h : forall x, e x = e' x) : e = e' :=
  DFunLike.ext _ _ h

@[continuity]
/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  given: (e : P₁ ≃ᴬ[k] P₂)
  statement: Continuous e
  proof: e.2

中文:
定理 continuous
  条件: (e : P₁ ≃ᴬ[k] P₂)
  结论: 连续 e
  证明: e.2
-/
protected theorem continuous (e : P₁ ≃ᴬ[k] P₂) : Continuous e :=
  e.2

/--
Definition of `toContinuousAffineMap` / `toContinuousAffineMap` 的定义

English:
definition toContinuousAffineMap
  signature: (e : P₁ ≃ᴬ[k] P₂)
  body: e
  cont := e.continuous_toFun

中文:
定义 toContinuousAffineMap
  签名: (e : P₁ ≃ᴬ[k] P₂)
  定义体: e
  cont := e.continuous_toFun
-/
def toContinuousAffineMap (e : P₁ ≃ᴬ[k] P₂) : P₁ ->ᴬ[k] P₂ where
  __ := e
  cont := e.continuous_toFun

/--
Instance `ContinuousAffineMap.coe` / 实例 `ContinuousAffineMap.coe`

English:
instance ContinuousAffineMap.coe
  signature: : Coe (P₁ ≃ᴬ[k] P₂) (P₁ ->ᴬ[k] P₂)
  body: ⟨toContinuousAffineMap⟩

@[simp]

中文:
实例 余ntinuousAffine映射.coe
  签名: : Coe (P₁ ≃ᴬ[k] P₂) (P₁ ->ᴬ[k] P₂)
  定义体: ⟨toContinuousAffineMap⟩

@[simp]

Depends on / 依赖: toContinuousAffineMap
-/
instance ContinuousAffineMap.coe : Coe (P₁ ≃ᴬ[k] P₂) (P₁ ->ᴬ[k] P₂) :=
  ⟨toContinuousAffineMap⟩

@[simp]
/--
lemma `coe_toContinuousAffineMap` / 引理 `coe_toContinuousAffineMap`

English:
lemma coe_toContinuousAffineMap
  given: (e : P₁ ≃ᴬ[k] P₂)
  statement: ⇑e.toContinuousAffineMap = e
  proof: rfl

中文:
引理 coe_toContinuousAffineMap
  条件: (e : P₁ ≃ᴬ[k] P₂)
  结论: ⇑e.toContinuousAffineMap = e
  证明: rfl
-/
lemma coe_toContinuousAffineMap (e : P₁ ≃ᴬ[k] P₂) : ⇑e.toContinuousAffineMap = e :=
  rfl

/--
lemma `toContinuousAffineMap_injective` / 引理 `toContinuousAffineMap_injective`

English:
lemma toContinuousAffineMap_injective
  proof: by
  intro e e' h
  ext p
  simp_rw [← coe_toContinuousAffineMap, h]

中文:
引理 toContinuousAffineMap_injective
  证明: by
  intro e e' h
  ext p
  simp_rw [← coe_toContinuousAffineMap, h]

Depends on / 依赖: coe_toContinuousAffineMap, simp_rw
-/
lemma toContinuousAffineMap_injective :
    Function.Injective (toContinuousAffineMap : (P₁ ≃ᴬ[k] P₂) -> (P₁ ->ᴬ[k] P₂)) := by
  intro e e' h
  ext p
  simp_rw [← coe_toContinuousAffineMap, h]

/--
lemma `toContinuousAffineMap_toAffineMap` / 引理 `toContinuousAffineMap_toAffineMap`

English:
lemma toContinuousAffineMap_toAffineMap
  given: (e : P₁ ≃ᴬ[k] P₂)
  proof: rfl

中文:
引理 toContinuousAffineMap_toAffineMap
  条件: (e : P₁ ≃ᴬ[k] P₂)
  证明: rfl
-/
lemma toContinuousAffineMap_toAffineMap (e : P₁ ≃ᴬ[k] P₂) :
    e.toContinuousAffineMap.toAffineMap = e.toAffineEquiv.toAffineMap :=
  rfl

/--
lemma `toContinuousAffineMap_toContinuousMap` / 引理 `toContinuousAffineMap_toContinuousMap`

English:
lemma toContinuousAffineMap_toContinuousMap
  given: (e : P₁ ≃ᴬ[k] P₂)
  proof: rfl

中文:
引理 toContinuousAffineMap_toContinuousMap
  条件: (e : P₁ ≃ᴬ[k] P₂)
  证明: rfl
-/
lemma toContinuousAffineMap_toContinuousMap (e : P₁ ≃ᴬ[k] P₂) :
    e.toContinuousAffineMap.toContinuousMap = toContinuousMap e.toHomeomorph :=
  rfl

end Basic

section ReflSymmTrans

variable (k P₁) in
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: : P₁ ≃ᴬ[k] P₁ where
  body: Equiv.refl P₁
  linear := LinearEquiv.refl k V₁
  map_vadd' _ _ := rfl

@[simp]

中文:
定义 refl
  签名: : P₁ ≃ᴬ[k] P₁ where
  定义体: Equiv.refl P₁
  linear := LinearEquiv.refl k V₁
  map_vadd' _ _ := rfl

@[simp]

Depends on / 依赖: Equiv.refl
-/
def refl : P₁ ≃ᴬ[k] P₁ where
  toEquiv := Equiv.refl P₁
  linear := LinearEquiv.refl k V₁
  map_vadd' _ _ := rfl

@[simp]
/--
theorem `coe_refl` / 定理 `coe_refl`

English:
theorem coe_refl
  statement: ⇑(refl k P₁) = id
  proof: rfl

@[simp]

中文:
定理 coe_refl
  结论: ⇑(refl k P₁) = id
  证明: rfl

@[simp]
-/
theorem coe_refl : ⇑(refl k P₁) = id :=
  rfl

@[simp]
/--
theorem `refl_apply` / 定理 `refl_apply`

English:
theorem refl_apply
  given: (x : P₁)
  statement: refl k P₁ x = x
  proof: rfl

@[simp]

中文:
定理 refl_apply
  条件: (x : P₁)
  结论: refl k P₁ x = x
  证明: rfl

@[simp]
-/
theorem refl_apply (x : P₁) : refl k P₁ x = x :=
  rfl

@[simp]
/--
theorem `toAffineEquiv_refl` / 定理 `toAffineEquiv_refl`

English:
theorem toAffineEquiv_refl
  statement: (refl k P₁).toAffineEquiv = AffineEquiv.refl k P₁
  proof: rfl

@[simp]

中文:
定理 toAffineEquiv_refl
  结论: (refl k P₁).toAffineEquiv = 仿射等价.refl k P₁
  证明: rfl

@[simp]
-/
theorem toAffineEquiv_refl : (refl k P₁).toAffineEquiv = AffineEquiv.refl k P₁ :=
  rfl

@[simp]
/--
theorem `toEquiv_refl` / 定理 `toEquiv_refl`

English:
theorem toEquiv_refl
  statement: (refl k P₁).toEquiv = Equiv.refl P₁
  proof: rfl

中文:
定理 toEquiv_refl
  结论: (refl k P₁).toEquiv = 等价.refl P₁
  证明: rfl
-/
theorem toEquiv_refl : (refl k P₁).toEquiv = Equiv.refl P₁ :=
  rfl

/-- Inverse of a continuous affine equivalence as a continuous affine equivalence. -/
@[symm]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: (e : P₁ ≃ᴬ[k] P₂)
  body: e.toAffineEquiv.symm
  continuous_toFun := e.continuous_invFun
  continuous_invFun := e.continuous_toFun

中文:
定义 symm
  签名: (e : P₁ ≃ᴬ[k] P₂)
  定义体: e.toAffineEquiv.symm
  continuous_toFun := e.continuous_invFun
  continuous_invFun := e.continuous_toFun

Depends on / 依赖: e.toAffineEquiv.symm, toAffineEquiv
-/
def symm (e : P₁ ≃ᴬ[k] P₂) : P₂ ≃ᴬ[k] P₁ where
  toAffineEquiv := e.toAffineEquiv.symm
  continuous_toFun := e.continuous_invFun
  continuous_invFun := e.continuous_toFun

/--
Definition of `Simps.apply` / `Simps.apply` 的定义

English:
definition Simps.apply
  signature: (e : P₁ ≃ᴬ[k] P₂)
  body: e

中文:
定义 Simps.apply
  签名: (e : P₁ ≃ᴬ[k] P₂)
  定义体: e
-/
def Simps.apply (e : P₁ ≃ᴬ[k] P₂) : P₁ -> P₂ :=
  e

/--
Definition of `Simps.symm_apply` / `Simps.symm_apply` 的定义

English:
definition Simps.symm_apply
  signature: (e : P₁ ≃ᴬ[k] P₂)
  body: e.symm

initialize_simps_projections ContinuousAffineEquiv (toFun -> apply, invFun -> symm_apply)

@[simp]

中文:
定义 Simps.symm_apply
  签名: (e : P₁ ≃ᴬ[k] P₂)
  定义体: e.symm

initialize_simps_projections ContinuousAffineEquiv (toFun -> apply, invFun -> symm_apply)

@[simp]
-/
def Simps.symm_apply (e : P₁ ≃ᴬ[k] P₂) : P₂ -> P₁ :=
  e.symm

initialize_simps_projections ContinuousAffineEquiv (toFun -> apply, invFun -> symm_apply)

@[simp]
/--
theorem `toAffineEquiv_symm` / 定理 `toAffineEquiv_symm`

English:
theorem toAffineEquiv_symm
  given: (e : P₁ ≃ᴬ[k] P₂)
  statement: e.symm.toAffineEquiv = e.toAffineEquiv.symm
  proof: rfl

@[simp]

中文:
定理 toAffineEquiv_symm
  条件: (e : P₁ ≃ᴬ[k] P₂)
  结论: e.symm.toAffineEquiv = e.toAffineEquiv.symm
  证明: rfl

@[simp]
-/
theorem toAffineEquiv_symm (e : P₁ ≃ᴬ[k] P₂) : e.symm.toAffineEquiv = e.toAffineEquiv.symm :=
  rfl

@[simp]
/--
theorem `coe_symm_toAffineEquiv` / 定理 `coe_symm_toAffineEquiv`

English:
theorem coe_symm_toAffineEquiv
  given: (e : P₁ ≃ᴬ[k] P₂)
  statement: ⇑e.toAffineEquiv.symm = e.symm
  proof: rfl

@[simp]

中文:
定理 coe_symm_toAffineEquiv
  条件: (e : P₁ ≃ᴬ[k] P₂)
  结论: ⇑e.toAffineEquiv.symm = e.symm
  证明: rfl

@[simp]
-/
theorem coe_symm_toAffineEquiv (e : P₁ ≃ᴬ[k] P₂) : ⇑e.toAffineEquiv.symm = e.symm := rfl

@[simp]
/--
theorem `toEquiv_symm` / 定理 `toEquiv_symm`

English:
theorem toEquiv_symm
  given: (e : P₁ ≃ᴬ[k] P₂)
  statement: e.symm.toEquiv = e.toEquiv.symm
  proof: rfl

@[simp]

中文:
定理 toEquiv_symm
  条件: (e : P₁ ≃ᴬ[k] P₂)
  结论: e.symm.toEquiv = e.toEquiv.symm
  证明: rfl

@[simp]
-/
theorem toEquiv_symm (e : P₁ ≃ᴬ[k] P₂) : e.symm.toEquiv = e.toEquiv.symm := rfl

@[simp]
/--
theorem `coe_symm_toEquiv` / 定理 `coe_symm_toEquiv`

English:
theorem coe_symm_toEquiv
  given: (e : P₁ ≃ᴬ[k] P₂)
  statement: ⇑e.toEquiv.symm = e.symm
  proof: rfl

@[simp]

中文:
定理 coe_symm_toEquiv
  条件: (e : P₁ ≃ᴬ[k] P₂)
  结论: ⇑e.toEquiv.symm = e.symm
  证明: rfl

@[simp]
-/
theorem coe_symm_toEquiv (e : P₁ ≃ᴬ[k] P₂) : ⇑e.toEquiv.symm = e.symm := rfl

@[simp]
/--
theorem `apply_symm_apply` / 定理 `apply_symm_apply`

English:
theorem apply_symm_apply
  given: (e : P₁ ≃ᴬ[k] P₂) (p : P₂)
  statement: e (e.symm p) = p
  proof: e.toEquiv.apply_symm_apply p

@[simp]

中文:
定理 apply_symm_apply
  条件: (e : P₁ ≃ᴬ[k] P₂) (p : P₂)
  结论: e (e.symm p) = p
  证明: e.toEquiv.apply_symm_apply p

@[simp]

Depends on / 依赖: apply_symm_apply, e.toEquiv.apply_symm_apply, toEquiv
-/
theorem apply_symm_apply (e : P₁ ≃ᴬ[k] P₂) (p : P₂) : e (e.symm p) = p :=
  e.toEquiv.apply_symm_apply p

@[simp]
/--
theorem `symm_apply_apply` / 定理 `symm_apply_apply`

English:
theorem symm_apply_apply
  given: (e : P₁ ≃ᴬ[k] P₂) (p : P₁)
  statement: e.symm (e p) = p
  proof: e.toEquiv.symm_apply_apply p

中文:
定理 symm_apply_apply
  条件: (e : P₁ ≃ᴬ[k] P₂) (p : P₁)
  结论: e.symm (e p) = p
  证明: e.toEquiv.symm_apply_apply p

Depends on / 依赖: e.toEquiv.symm_apply_apply, symm_apply_apply, toEquiv
-/
theorem symm_apply_apply (e : P₁ ≃ᴬ[k] P₂) (p : P₁) : e.symm (e p) = p :=
  e.toEquiv.symm_apply_apply p

/--
theorem `apply_eq_iff_eq` / 定理 `apply_eq_iff_eq`

English:
theorem apply_eq_iff_eq
  given: (e : P₁ ≃ᴬ[k] P₂) {p₁ p₂ : P₁}
  statement: e p₁ = e p₂ ↔ p₁ = p₂
  proof: e.toEquiv.apply_eq_iff_eq

@[simp]

中文:
定理 apply_eq_iff_eq
  条件: (e : P₁ ≃ᴬ[k] P₂) {p₁ p₂ : P₁}
  结论: e p₁ = e p₂ ↔ p₁ = p₂
  证明: e.toEquiv.apply_eq_iff_eq

@[simp]

Depends on / 依赖: apply_eq_iff_eq, e.toEquiv.apply_eq_iff_eq, toEquiv
-/
theorem apply_eq_iff_eq (e : P₁ ≃ᴬ[k] P₂) {p₁ p₂ : P₁} : e p₁ = e p₂ ↔ p₁ = p₂ :=
  e.toEquiv.apply_eq_iff_eq

@[simp]
/--
theorem `symm_symm` / 定理 `symm_symm`

English:
theorem symm_symm
  given: (e : P₁ ≃ᴬ[k] P₂)
  statement: e.symm.symm = e
  proof: rfl

中文:
定理 symm_symm
  条件: (e : P₁ ≃ᴬ[k] P₂)
  结论: e.symm.symm = e
  证明: rfl
-/
theorem symm_symm (e : P₁ ≃ᴬ[k] P₂) : e.symm.symm = e := rfl

/--
theorem `symm_bijective` / 定理 `symm_bijective`

English:
theorem symm_bijective
  statement: Function.Bijective (symm : (P₁ ≃ᴬ[k] P₂) -> _)
  proof: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

中文:
定理 symm_bijective
  结论: 函数.双射 (symm : (P₁ ≃ᴬ[k] P₂) -> _)
  证明: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

Depends on / 依赖: Function, Function.bijective_iff_has_inverse.mpr, bijective_iff_has_inverse, symm_symm
-/
theorem symm_bijective : Function.Bijective (symm : (P₁ ≃ᴬ[k] P₂) -> _) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

/--
theorem `symm_symm_apply` / 定理 `symm_symm_apply`

English:
theorem symm_symm_apply
  given: (e : P₁ ≃ᴬ[k] P₂) (x : P₁)
  statement: e.symm.symm x = e x
  proof: rfl

中文:
定理 symm_symm_apply
  条件: (e : P₁ ≃ᴬ[k] P₂) (x : P₁)
  结论: e.symm.symm x = e x
  证明: rfl
-/
theorem symm_symm_apply (e : P₁ ≃ᴬ[k] P₂) (x : P₁) : e.symm.symm x = e x :=
  rfl

/--
theorem `symm_apply_eq` / 定理 `symm_apply_eq`

English:
theorem symm_apply_eq
  given: (e : P₁ ≃ᴬ[k] P₂) {x y}
  statement: e.symm x = y ↔ x = e y
  proof: e.toAffineEquiv.symm_apply_eq

中文:
定理 symm_apply_eq
  条件: (e : P₁ ≃ᴬ[k] P₂) {x y}
  结论: e.symm x = y ↔ x = e y
  证明: e.toAffineEquiv.symm_apply_eq

Depends on / 依赖: e.toAffineEquiv.symm_apply_eq, symm_apply_eq, toAffineEquiv
-/
theorem symm_apply_eq (e : P₁ ≃ᴬ[k] P₂) {x y} : e.symm x = y ↔ x = e y :=
  e.toAffineEquiv.symm_apply_eq

/--
theorem `eq_symm_apply` / 定理 `eq_symm_apply`

English:
theorem eq_symm_apply
  given: (e : P₁ ≃ᴬ[k] P₂) {x y}
  statement: y = e.symm x ↔ e y = x
  proof: e.toAffineEquiv.eq_symm_apply

@[deprecated eq_symm_apply (since := "2026-07-26")]

中文:
定理 eq_symm_apply
  条件: (e : P₁ ≃ᴬ[k] P₂) {x y}
  结论: y = e.symm x ↔ e y = x
  证明: e.toAffineEquiv.eq_symm_apply

@[deprecated eq_symm_apply (since := "2026-07-26")]

Depends on / 依赖: e.toAffineEquiv.eq_symm_apply, eq_symm_apply, toAffineEquiv
-/
theorem eq_symm_apply (e : P₁ ≃ᴬ[k] P₂) {x y} : y = e.symm x ↔ e y = x :=
  e.toAffineEquiv.eq_symm_apply

@[deprecated eq_symm_apply (since := "2026-07-26")]
/--
theorem `apply_eq_iff_eq_symm_apply` / 定理 `apply_eq_iff_eq_symm_apply`

English:
theorem apply_eq_iff_eq_symm_apply
  given: (e : P₁ ≃ᴬ[k] P₂) {p₁ p₂}
  statement: e p₁ = p₂ ↔ p₁ = e.symm p₂
  proof: e.eq_symm_apply.symm

@[simp]

中文:
定理 apply_eq_iff_eq_symm_apply
  条件: (e : P₁ ≃ᴬ[k] P₂) {p₁ p₂}
  结论: e p₁ = p₂ ↔ p₁ = e.symm p₂
  证明: e.eq_symm_apply.symm

@[simp]

Depends on / 依赖: e.eq_symm_apply.symm, eq_symm_apply
-/
theorem apply_eq_iff_eq_symm_apply (e : P₁ ≃ᴬ[k] P₂) {p₁ p₂} : e p₁ = p₂ ↔ p₁ = e.symm p₂ :=
  e.eq_symm_apply.symm

@[simp]
/--
theorem `image_symm` / 定理 `image_symm`

English:
theorem image_symm
  given: (f : P₁ ≃ᴬ[k] P₂) (s : Set P₂)
  statement: f.symm '' s = f ⁻¹' s
  proof: f.symm.toEquiv.image_eq_preimage_symm _

@[simp]

中文:
定理 image_symm
  条件: (f : P₁ ≃ᴬ[k] P₂) (s : 集合 P₂)
  结论: f.symm '' s = f ⁻¹' s
  证明: f.symm.toEquiv.image_eq_preimage_symm _

@[simp]

Depends on / 依赖: f.symm.toEquiv.image_eq_preimage_symm, image_eq_preimage_symm, toEquiv
-/
theorem image_symm (f : P₁ ≃ᴬ[k] P₂) (s : Set P₂) : f.symm '' s = f ⁻¹' s :=
  f.symm.toEquiv.image_eq_preimage_symm _

@[simp]
/--
theorem `preimage_symm` / 定理 `preimage_symm`

English:
theorem preimage_symm
  given: (f : P₁ ≃ᴬ[k] P₂) (s : Set P₁)
  statement: f.symm ⁻¹' s = f '' s
  proof: (f.symm.image_symm _).symm

中文:
定理 preimage_symm
  条件: (f : P₁ ≃ᴬ[k] P₂) (s : 集合 P₁)
  结论: f.symm ⁻¹' s = f '' s
  证明: (f.symm.image_symm _).symm

Depends on / 依赖: f.symm.image_symm, image_symm
-/
theorem preimage_symm (f : P₁ ≃ᴬ[k] P₂) (s : Set P₁) : f.symm ⁻¹' s = f '' s :=
  (f.symm.image_symm _).symm

/--
theorem `bijective` / 定理 `bijective`

English:
theorem bijective
  given: (e : P₁ ≃ᴬ[k] P₂)
  statement: Bijective e
  proof: e.toEquiv.bijective

中文:
定理 bijective
  条件: (e : P₁ ≃ᴬ[k] P₂)
  结论: 双射 e
  证明: e.toEquiv.bijective
-/
protected theorem bijective (e : P₁ ≃ᴬ[k] P₂) : Bijective e :=
  e.toEquiv.bijective

/--
theorem `surjective` / 定理 `surjective`

English:
theorem surjective
  given: (e : P₁ ≃ᴬ[k] P₂)
  statement: Surjective e
  proof: e.toEquiv.surjective

中文:
定理 surjective
  条件: (e : P₁ ≃ᴬ[k] P₂)
  结论: 满射 e
  证明: e.toEquiv.surjective

Depends on / 依赖: SetRel, SetRel.left_subset_comp, antisymm, comp_le_uniformity, comp_le_uniformity.antisymm, isRefl_of_mem_uniformity, le_lift, left_subset_comp, mem_of_superset
-/
protected theorem surjective (e : P₁ ≃ᴬ[k] P₂) : Surjective e :=
  e.toEquiv.surjective

/--
theorem `injective` / 定理 `injective`

English:
theorem injective
  given: (e : P₁ ≃ᴬ[k] P₂)
  statement: Injective e
  proof: e.toEquiv.injective

中文:
定理 injective
  条件: (e : P₁ ≃ᴬ[k] P₂)
  结论: 单射 e
  证明: e.toEquiv.injective
-/
protected theorem injective (e : P₁ ≃ᴬ[k] P₂) : Injective e :=
  e.toEquiv.injective

/--
theorem `image_eq_preimage_symm` / 定理 `image_eq_preimage_symm`

English:
theorem image_eq_preimage_symm
  given: (e : P₁ ≃ᴬ[k] P₂) (s : Set P₁)
  statement: e '' s = e.symm ⁻¹' s
  proof: e.toEquiv.image_eq_preimage_symm s

中文:
定理 image_eq_preimage_symm
  条件: (e : P₁ ≃ᴬ[k] P₂) (s : 集合 P₁)
  结论: e '' s = e.symm ⁻¹' s
  证明: e.toEquiv.image_eq_preimage_symm s
-/
protected theorem image_eq_preimage_symm (e : P₁ ≃ᴬ[k] P₂) (s : Set P₁) : e '' s = e.symm ⁻¹' s :=
  e.toEquiv.image_eq_preimage_symm s

/--
theorem `image_symm_eq_preimage` / 定理 `image_symm_eq_preimage`

English:
theorem image_symm_eq_preimage
  given: (e : P₁ ≃ᴬ[k] P₂) (s : Set P₂)
  proof: by
  rw [e.symm.image_eq_preimage_symm]; rw [e.symm_symm]

@[simp]

中文:
定理 image_symm_eq_preimage
  条件: (e : P₁ ≃ᴬ[k] P₂) (s : 集合 P₂)
  证明: by
  rw [e.symm.image_eq_preimage_symm]; rw [e.symm_symm]

@[simp]
-/
protected theorem image_symm_eq_preimage (e : P₁ ≃ᴬ[k] P₂) (s : Set P₂) :
    e.symm '' s = e ⁻¹' s := by
  rw [e.symm.image_eq_preimage_symm]; rw [e.symm_symm]

@[simp]
/--
theorem `image_preimage` / 定理 `image_preimage`

English:
theorem image_preimage
  given: (e : P₁ ≃ᴬ[k] P₂) (s : Set P₂)
  statement: e '' e ⁻¹' s = s
  proof: e.surjective.image_preimage s

@[simp]

中文:
定理 image_preimage
  条件: (e : P₁ ≃ᴬ[k] P₂) (s : 集合 P₂)
  结论: e '' e ⁻¹' s = s
  证明: e.surjective.image_preimage s

@[simp]

Depends on / 依赖: e.surjective.image_preimage, image_preimage, surjective
-/
theorem image_preimage (e : P₁ ≃ᴬ[k] P₂) (s : Set P₂) : e '' e ⁻¹' s = s :=
  e.surjective.image_preimage s

@[simp]
/--
theorem `preimage_image` / 定理 `preimage_image`

English:
theorem preimage_image
  given: (e : P₁ ≃ᴬ[k] P₂) (s : Set P₁)
  statement: e ⁻¹' e '' s = s
  proof: e.injective.preimage_image s

中文:
定理 preimage_image
  条件: (e : P₁ ≃ᴬ[k] P₂) (s : 集合 P₁)
  结论: e ⁻¹' e '' s = s
  证明: e.injective.preimage_image s

Depends on / 依赖: e.injective.preimage_image, injective, preimage_image
-/
theorem preimage_image (e : P₁ ≃ᴬ[k] P₂) (s : Set P₁) : e ⁻¹' e '' s = s :=
  e.injective.preimage_image s

/--
theorem `symm_image_image` / 定理 `symm_image_image`

English:
theorem symm_image_image
  given: (e : P₁ ≃ᴬ[k] P₂) (s : Set P₁)
  statement: e.symm '' e '' s = s
  proof: e.toEquiv.symm_image_image s

中文:
定理 symm_image_image
  条件: (e : P₁ ≃ᴬ[k] P₂) (s : 集合 P₁)
  结论: e.symm '' e '' s = s
  证明: e.toEquiv.symm_image_image s

Depends on / 依赖: e.toEquiv.symm_image_image, symm_image_image, toEquiv
-/
theorem symm_image_image (e : P₁ ≃ᴬ[k] P₂) (s : Set P₁) : e.symm '' e '' s = s :=
  e.toEquiv.symm_image_image s

/--
theorem `image_symm_image` / 定理 `image_symm_image`

English:
theorem image_symm_image
  given: (e : P₁ ≃ᴬ[k] P₂) (s : Set P₂)
  statement: e '' e.symm '' s = s
  proof: e.symm.symm_image_image s

@[simp]

中文:
定理 image_symm_image
  条件: (e : P₁ ≃ᴬ[k] P₂) (s : 集合 P₂)
  结论: e '' e.symm '' s = s
  证明: e.symm.symm_image_image s

@[simp]

Depends on / 依赖: e.symm.symm_image_image, symm_image_image
-/
theorem image_symm_image (e : P₁ ≃ᴬ[k] P₂) (s : Set P₂) : e '' e.symm '' s = s :=
  e.symm.symm_image_image s

@[simp]
/--
theorem `refl_symm` / 定理 `refl_symm`

English:
theorem refl_symm
  statement: (refl k P₁).symm = refl k P₁
  proof: rfl

@[simp]

中文:
定理 refl_symm
  结论: (refl k P₁).symm = refl k P₁
  证明: rfl

@[simp]
-/
theorem refl_symm : (refl k P₁).symm = refl k P₁ :=
  rfl

@[simp]
/--
theorem `symm_refl` / 定理 `symm_refl`

English:
theorem symm_refl
  statement: (refl k P₁).symm = refl k P₁
  proof: rfl

中文:
定理 symm_refl
  结论: (refl k P₁).symm = refl k P₁
  证明: rfl
-/
theorem symm_refl : (refl k P₁).symm = refl k P₁ :=
  rfl

/-- Composition of two `ContinuousAffineEquiv`alences, applied left to right. -/
@[trans]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (e : P₁ ≃ᴬ[k] P₂) (e' : P₂ ≃ᴬ[k] P₃)
  body: e.toAffineEquiv.trans e'.toAffineEquiv
  continuous_toFun := e'.continuous_toFun.comp (e.continuous_toFun)
  continuous_invFun := e.continuous_invFun.comp (e'.continuous_invFun)

@[simp]

中文:
定义 trans
  签名: (e : P₁ ≃ᴬ[k] P₂) (e' : P₂ ≃ᴬ[k] P₃)
  定义体: e.toAffineEquiv.trans e'.toAffineEquiv
  continuous_toFun := e'.continuous_toFun.comp (e.continuous_toFun)
  continuous_invFun := e.continuous_invFun.comp (e'.continuous_invFun)

@[simp]

Depends on / 依赖: e.toAffineEquiv.trans, toAffineEquiv
-/
def trans (e : P₁ ≃ᴬ[k] P₂) (e' : P₂ ≃ᴬ[k] P₃) : P₁ ≃ᴬ[k] P₃ where
  toAffineEquiv := e.toAffineEquiv.trans e'.toAffineEquiv
  continuous_toFun := e'.continuous_toFun.comp (e.continuous_toFun)
  continuous_invFun := e.continuous_invFun.comp (e'.continuous_invFun)

@[simp]
/--
theorem `coe_trans` / 定理 `coe_trans`

English:
theorem coe_trans
  given: (e : P₁ ≃ᴬ[k] P₂) (e' : P₂ ≃ᴬ[k] P₃)
  statement: ⇑(e.trans e') = e' ∘ e
  proof: rfl

@[simp]

中文:
定理 coe_trans
  条件: (e : P₁ ≃ᴬ[k] P₂) (e' : P₂ ≃ᴬ[k] P₃)
  结论: ⇑(e.trans e') = e' ∘ e
  证明: rfl

@[simp]
-/
theorem coe_trans (e : P₁ ≃ᴬ[k] P₂) (e' : P₂ ≃ᴬ[k] P₃) : ⇑(e.trans e') = e' ∘ e :=
  rfl

@[simp]
/--
theorem `trans_apply` / 定理 `trans_apply`

English:
theorem trans_apply
  given: (e : P₁ ≃ᴬ[k] P₂) (e' : P₂ ≃ᴬ[k] P₃) (p : P₁)
  statement: e.trans e' p = e' (e p)
  proof: rfl

中文:
定理 trans_apply
  条件: (e : P₁ ≃ᴬ[k] P₂) (e' : P₂ ≃ᴬ[k] P₃) (p : P₁)
  结论: e.trans e' p = e' (e p)
  证明: rfl
-/
theorem trans_apply (e : P₁ ≃ᴬ[k] P₂) (e' : P₂ ≃ᴬ[k] P₃) (p : P₁) : e.trans e' p = e' (e p) :=
  rfl

/--
theorem `trans_assoc` / 定理 `trans_assoc`

English:
theorem trans_assoc
  given: (e₁ : P₁ ≃ᴬ[k] P₂) (e₂ : P₂ ≃ᴬ[k] P₃) (e₃ : P₃ ≃ᴬ[k] P₄)
  proof: ext fun _ => rfl

@[simp]

中文:
定理 trans_assoc
  条件: (e₁ : P₁ ≃ᴬ[k] P₂) (e₂ : P₂ ≃ᴬ[k] P₃) (e₃ : P₃ ≃ᴬ[k] P₄)
  证明: ext fun _ => rfl

@[simp]
-/
theorem trans_assoc (e₁ : P₁ ≃ᴬ[k] P₂) (e₂ : P₂ ≃ᴬ[k] P₃) (e₃ : P₃ ≃ᴬ[k] P₄) :
    (e₁.trans e₂).trans e₃ = e₁.trans (e₂.trans e₃) :=
  ext fun _ => rfl

@[simp]
/--
theorem `trans_refl` / 定理 `trans_refl`

English:
theorem trans_refl
  given: (e : P₁ ≃ᴬ[k] P₂)
  statement: e.trans (refl k P₂) = e
  proof: ext fun _ => rfl

@[simp]

中文:
定理 trans_refl
  条件: (e : P₁ ≃ᴬ[k] P₂)
  结论: e.trans (refl k P₂) = e
  证明: ext fun _ => rfl

@[simp]
-/
theorem trans_refl (e : P₁ ≃ᴬ[k] P₂) : e.trans (refl k P₂) = e :=
  ext fun _ => rfl

@[simp]
/--
theorem `refl_trans` / 定理 `refl_trans`

English:
theorem refl_trans
  given: (e : P₁ ≃ᴬ[k] P₂)
  statement: (refl k P₁).trans e = e
  proof: ext fun _ => rfl

@[simp]

中文:
定理 refl_trans
  条件: (e : P₁ ≃ᴬ[k] P₂)
  结论: (refl k P₁).trans e = e
  证明: ext fun _ => rfl

@[simp]
-/
theorem refl_trans (e : P₁ ≃ᴬ[k] P₂) : (refl k P₁).trans e = e :=
  ext fun _ => rfl

@[simp]
/--
theorem `self_trans_symm` / 定理 `self_trans_symm`

English:
theorem self_trans_symm
  given: (e : P₁ ≃ᴬ[k] P₂)
  statement: e.trans e.symm = refl k P₁
  proof: ext e.symm_apply_apply

@[simp]

中文:
定理 self_trans_symm
  条件: (e : P₁ ≃ᴬ[k] P₂)
  结论: e.trans e.symm = refl k P₁
  证明: ext e.symm_apply_apply

@[simp]

Depends on / 依赖: e.symm_apply_apply, symm_apply_apply
-/
theorem self_trans_symm (e : P₁ ≃ᴬ[k] P₂) : e.trans e.symm = refl k P₁ :=
  ext e.symm_apply_apply

@[simp]
/--
theorem `symm_trans_self` / 定理 `symm_trans_self`

English:
theorem symm_trans_self
  given: (e : P₁ ≃ᴬ[k] P₂)
  statement: e.symm.trans e = refl k P₂
  proof: ext e.apply_symm_apply

中文:
定理 symm_trans_self
  条件: (e : P₁ ≃ᴬ[k] P₂)
  结论: e.symm.trans e = refl k P₂
  证明: ext e.apply_symm_apply

Depends on / 依赖: apply_symm_apply, e.apply_symm_apply
-/
theorem symm_trans_self (e : P₁ ≃ᴬ[k] P₂) : e.symm.trans e = refl k P₂ :=
  ext e.apply_symm_apply

/--
lemma `trans_toContinuousAffineMap` / 引理 `trans_toContinuousAffineMap`

English:
lemma trans_toContinuousAffineMap
  given: (e : P₁ ≃ᴬ[k] P₂) (e' : P₂ ≃ᴬ[k] P₃)
  proof: rfl

中文:
引理 trans_toContinuousAffineMap
  条件: (e : P₁ ≃ᴬ[k] P₂) (e' : P₂ ≃ᴬ[k] P₃)
  证明: rfl
-/
lemma trans_toContinuousAffineMap (e : P₁ ≃ᴬ[k] P₂) (e' : P₂ ≃ᴬ[k] P₃) :
    (e.trans e').toContinuousAffineMap = e'.toContinuousAffineMap.comp e.toContinuousAffineMap :=
  rfl

end ReflSymmTrans

section

variable (k)
variable [TopologicalSpace V₁] [IsTopologicalAddTorsor P₁]

/-- The affine homeomorphism `V ≃ᴬ[k] P` given by `v ↦ v +ᵥ p`. This is `Equiv.vaddConst`
as a `ContinuousAffineEquiv`. -/
@[simps! apply symm_apply]
/--
Definition of `vaddConst` / `vaddConst` 的定义

English:
definition vaddConst
  signature: (p : P₁)
  body: AffineEquiv.vaddConst k p
  __ := Homeomorph.vaddConst p

@[simp]

中文:
定义 vaddConst
  签名: (p : P₁)
  定义体: AffineEquiv.vaddConst k p
  __ := Homeomorph.vaddConst p

@[simp]

Depends on / 依赖: AffineEquiv, AffineEquiv.vaddConst, vaddConst
-/
def vaddConst (p : P₁) : V₁ ≃ᴬ[k] P₁ where
  __ := AffineEquiv.vaddConst k p
  __ := Homeomorph.vaddConst p

@[simp]
/--
lemma `toAffineEquiv_vaddConst` / 引理 `toAffineEquiv_vaddConst`

English:
lemma toAffineEquiv_vaddConst
  given: {p : P₁}
  statement: vaddConst k p = AffineEquiv.vaddConst k p
  proof: rfl

中文:
引理 toAffineEquiv_vaddConst
  条件: {p : P₁}
  结论: vaddConst k p = 仿射等价.vaddConst k p
  证明: rfl
-/
lemma toAffineEquiv_vaddConst {p : P₁} : vaddConst k p = AffineEquiv.vaddConst k p := rfl

/-- The affine homeomorphism given by `p' ↦ p -ᵥ p'`. This is `Equiv.constVSub` as a
`ContinuousAffineEquiv`. -/
@[simps! apply symm_apply]
/--
Definition of `constVSub` / `constVSub` 的定义

English:
definition constVSub
  signature: (p : P₁)
  body: AffineEquiv.constVSub k p
  __ := Homeomorph.constVSub p

@[simp]

中文:
定义 constVSub
  签名: (p : P₁)
  定义体: AffineEquiv.constVSub k p
  __ := Homeomorph.constVSub p

@[simp]

Depends on / 依赖: AffineEquiv, AffineEquiv.constVSub, constVSub
-/
def constVSub (p : P₁) : P₁ ≃ᴬ[k] V₁ where
  __ := AffineEquiv.constVSub k p
  __ := Homeomorph.constVSub p

@[simp]
/--
lemma `toAffineEquiv_constVSub` / 引理 `toAffineEquiv_constVSub`

English:
lemma toAffineEquiv_constVSub
  given: {p : P₁}
  statement: constVSub k p = AffineEquiv.constVSub k p
  proof: rfl

中文:
引理 toAffineEquiv_constVSub
  条件: {p : P₁}
  结论: constVSub k p = 仿射等价.constVSub k p
  证明: rfl
-/
lemma toAffineEquiv_constVSub {p : P₁} : constVSub k p = AffineEquiv.constVSub k p := rfl

/--
Definition of `pointReflection` / `pointReflection` 的定义

English:
definition pointReflection
  signature: (x : P₁)
  body: (constVSub k x).trans (vaddConst k x)

@[simp]

中文:
定义 pointReflection
  签名: (x : P₁)
  定义体: (constVSub k x).trans (vaddConst k x)

@[simp]

Depends on / 依赖: constVSub, vaddConst
-/
def pointReflection (x : P₁) : P₁ ≃ᴬ[k] P₁ :=
  (constVSub k x).trans (vaddConst k x)

@[simp]
/--
lemma `coe_pointReflection` / 引理 `coe_pointReflection`

English:
lemma coe_pointReflection
  given: (x : P₁)
  proof: rfl

中文:
引理 coe_pointReflection
  条件: (x : P₁)
  证明: rfl
-/
lemma coe_pointReflection (x : P₁) :
    (pointReflection k x : P₁ -> P₁) = Equiv.pointReflection x := rfl

/--
theorem `pointReflection_apply` / 定理 `pointReflection_apply`

English:
theorem pointReflection_apply
  given: (x y : P₁)
  statement: pointReflection k x y = (x -ᵥ y) +ᵥ x
  proof: rfl

@[simp]

中文:
定理 pointReflection_apply
  条件: (x y : P₁)
  结论: pointReflection k x y = (x -ᵥ y) +ᵥ x
  证明: rfl

@[simp]
-/
theorem pointReflection_apply (x y : P₁) : pointReflection k x y = (x -ᵥ y) +ᵥ x :=
  rfl

@[simp]
/--
theorem `pointReflection_symm` / 定理 `pointReflection_symm`

English:
theorem pointReflection_symm
  given: (x : P₁)
  statement: (pointReflection k x).symm = pointReflection k x
  proof: toAffineEquiv_injective AffineEquiv.pointReflection_symm k x

@[simp]

中文:
定理 pointReflection_symm
  条件: (x : P₁)
  结论: (pointReflection k x).symm = pointReflection k x
  证明: toAffineEquiv_injective AffineEquiv.pointReflection_symm k x

@[simp]

Depends on / 依赖: AffineEquiv, AffineEquiv.pointReflection_symm, pointReflection_symm, toAffineEquiv_injective
-/
theorem pointReflection_symm (x : P₁) : (pointReflection k x).symm = pointReflection k x :=
toAffineEquiv_injective AffineEquiv.pointReflection_symm k x

@[simp]
/--
theorem `toAffineEquiv_pointReflection` / 定理 `toAffineEquiv_pointReflection`

English:
theorem toAffineEquiv_pointReflection
  given: (x : P₁)
  proof: rfl

中文:
定理 toAffineEquiv_pointReflection
  条件: (x : P₁)
  证明: rfl
-/
theorem toAffineEquiv_pointReflection (x : P₁) :
    (pointReflection k x).toAffineEquiv = AffineEquiv.pointReflection k x :=
  rfl

/--
theorem `pointReflection_self` / 定理 `pointReflection_self`

English:
theorem pointReflection_self
  given: (x : P₁)
  statement: pointReflection k x x = x
  proof: vsub_vadd _ _

中文:
定理 pointReflection_self
  条件: (x : P₁)
  结论: pointReflection k x x = x
  证明: vsub_vadd _ _

Depends on / 依赖: vsub_vadd
-/
theorem pointReflection_self (x : P₁) : pointReflection k x x = x :=
  vsub_vadd _ _

/--
theorem `pointReflection_involutive` / 定理 `pointReflection_involutive`

English:
theorem pointReflection_involutive
  given: (x : P₁)
  statement: Involutive (pointReflection k x : P₁ -> P₁)
  proof: Equiv.pointReflection_involutive x

中文:
定理 pointReflection_involutive
  条件: (x : P₁)
  结论: 对合 (pointReflection k x : P₁ -> P₁)
  证明: Equiv.pointReflection_involutive x

Depends on / 依赖: Equiv.pointReflection_involutive, pointReflection_involutive
-/
theorem pointReflection_involutive (x : P₁) : Involutive (pointReflection k x : P₁ -> P₁) :=
  Equiv.pointReflection_involutive x

end

section

variable {E F : Type*} [AddCommGroup E] [Module k E] [TopologicalSpace E]
  [AddCommGroup F] [Module k F] [TopologicalSpace F]

/--
Definition of `_root_.ContinuousLinearEquiv.toContinuousAffineEquiv` / `_root_.ContinuousLinearEquiv.toContinuousAffineEquiv` 的定义

English:
definition _root_.ContinuousLinearEquiv.toContinuousAffineEquiv
  signature: (L : E ≃L[k] F)
  body: L.toAffineEquiv
  continuous_toFun := L.continuous_toFun
  continuous_invFun := L.continuous_invFun

@[simp]

中文:
定义 _root_.连续线性等价.toContinuousAffineEquiv
  签名: (L : E ≃L[k] F)
  定义体: L.toAffineEquiv
  continuous_toFun := L.continuous_toFun
  continuous_invFun := L.continuous_invFun

@[simp]

Depends on / 依赖: L.toAffineEquiv, toAffineEquiv
-/
def _root_.ContinuousLinearEquiv.toContinuousAffineEquiv (L : E ≃L[k] F) : E ≃ᴬ[k] F where
  toAffineEquiv := L.toAffineEquiv
  continuous_toFun := L.continuous_toFun
  continuous_invFun := L.continuous_invFun

@[simp]
/--
theorem `_root_.ContinuousLinearEquiv.coe_toContinuousAffineEquiv` / 定理 `_root_.ContinuousLinearEquiv.coe_toContinuousAffineEquiv`

English:
theorem _root_.ContinuousLinearEquiv.coe_toContinuousAffineEquiv
  given: (e : E ≃L[k] F)
  proof: rfl

中文:
定理 _root_.连续线性等价.coe_toContinuousAffineEquiv
  条件: (e : E ≃L[k] F)
  证明: rfl
-/
theorem _root_.ContinuousLinearEquiv.coe_toContinuousAffineEquiv (e : E ≃L[k] F) :
    ⇑e.toContinuousAffineEquiv = e :=
  rfl

/--
lemma `_root_.ContinuousLinearEquiv.toContinuousAffineEquiv_toContinuousAffineMap` / 引理 `_root_.ContinuousLinearEquiv.toContinuousAffineEquiv_toContinuousAffineMap`

English:
lemma _root_.ContinuousLinearEquiv.toContinuousAffineEquiv_toContinuousAffineMap
  given: (L : E ≃L[k] F)
  proof: rfl

中文:
引理 _root_.连续线性等价.toContinuousAffineEquiv_toContinuousAffineMap
  条件: (L : E ≃L[k] F)
  证明: rfl
-/
lemma _root_.ContinuousLinearEquiv.toContinuousAffineEquiv_toContinuousAffineMap (L : E ≃L[k] F) :
    L.toContinuousAffineEquiv.toContinuousAffineMap =
      L.toContinuousLinearMap.toContinuousAffineMap :=
  rfl

variable (k P₁) in
/--
Definition of `constVAdd` / `constVAdd` 的定义

English:
definition constVAdd
  signature: [ContinuousConstVAdd V₁ P₁] (v : V₁)
  body: AffineEquiv.constVAdd k P₁ v
  continuous_toFun := continuous_const_vadd v
  continuous_invFun := continuous_const_vadd (-v)

中文:
定义 constVAdd
  签名: [连续常数向量加法 V₁ P₁] (v : V₁)
  定义体: AffineEquiv.constVAdd k P₁ v
  continuous_toFun := continuous_const_vadd v
  continuous_invFun := continuous_const_vadd (-v)

Depends on / 依赖: AffineEquiv, AffineEquiv.constVAdd, constVAdd
-/
def constVAdd [ContinuousConstVAdd V₁ P₁] (v : V₁) : P₁ ≃ᴬ[k] P₁ where
  toAffineEquiv := AffineEquiv.constVAdd k P₁ v
  continuous_toFun := continuous_const_vadd v
  continuous_invFun := continuous_const_vadd (-v)

/--
lemma `constVAdd_coe` / 引理 `constVAdd_coe`

English:
lemma constVAdd_coe
  given: [ContinuousConstVAdd V₁ P₁] (v : V₁)
  proof: rfl

中文:
引理 constVAdd_coe
  条件: [连续常数向量加法 V₁ P₁] (v : V₁)
  证明: rfl
-/
lemma constVAdd_coe [ContinuousConstVAdd V₁ P₁] (v : V₁) :
    (constVAdd k P₁ v).toAffineEquiv = .constVAdd k P₁ v := rfl

end

section

variable (e₁ : P₁ ≃ᴬ[k] P₂) (e₂ : P₃ ≃ᴬ[k] P₄)

/-- Product of two continuous affine equivalences. The map comes from `Equiv.prodCongr` -/
@[simps toAffineEquiv]
/--
Definition of `prodCongr` / `prodCongr` 的定义

English:
definition prodCongr
  signature: : P₁ × P₃ ≃ᴬ[k] P₂ × P₄ where
  body: AffineEquiv.prodCongr e₁ e₂
  continuous_toFun := by eta_expand; dsimp; fun_prop
  continuous_invFun := by eta_expand; dsimp; fun_prop

@[simp]

中文:
定义 prodCongr
  签名: : P₁ × P₃ ≃ᴬ[k] P₂ × P₄ where
  定义体: AffineEquiv.prodCongr e₁ e₂
  continuous_toFun := by eta_expand; dsimp; fun_prop
  continuous_invFun := by eta_expand; dsimp; fun_prop

@[simp]

Depends on / 依赖: AffineEquiv, AffineEquiv.prodCongr, prodCongr
-/
def prodCongr : P₁ × P₃ ≃ᴬ[k] P₂ × P₄ where
  __ := AffineEquiv.prodCongr e₁ e₂
  continuous_toFun := by eta_expand; dsimp; fun_prop
  continuous_invFun := by eta_expand; dsimp; fun_prop

@[simp]
/--
theorem `prodCongr_symm` / 定理 `prodCongr_symm`

English:
theorem prodCongr_symm
  statement: (e₁.prodCongr e₂).symm = e₁.symm.prodCongr e₂.symm
  proof: rfl

@[simp]

中文:
定理 prodCongr_symm
  结论: (e₁.prodCongr e₂).symm = e₁.symm.prodCongr e₂.symm
  证明: rfl

@[simp]
-/
theorem prodCongr_symm : (e₁.prodCongr e₂).symm = e₁.symm.prodCongr e₂.symm :=
  rfl

@[simp]
/--
theorem `prodCongr_apply` / 定理 `prodCongr_apply`

English:
theorem prodCongr_apply
  given: (p : P₁ × P₃)
  statement: e₁.prodCongr e₂ p = (e₁ p.1, e₂ p.2)
  proof: rfl

@[simp]

中文:
定理 prodCongr_apply
  条件: (p : P₁ × P₃)
  结论: e₁.prodCongr e₂ p = (e₁ p.1, e₂ p.2)
  证明: rfl

@[simp]
-/
theorem prodCongr_apply (p : P₁ × P₃) : e₁.prodCongr e₂ p = (e₁ p.1, e₂ p.2) :=
  rfl

@[simp]
/--
theorem `prodCongr_toContinuousAffineMap` / 定理 `prodCongr_toContinuousAffineMap`

English:
theorem prodCongr_toContinuousAffineMap
  statement: (e₁.prodCongr e₂).toContinuousAffineMap =
  proof: rfl

中文:
定理 prodCongr_toContinuousAffineMap
  结论: (e₁.prodCongr e₂).toContinuousAffineMap =
  证明: rfl
-/
theorem prodCongr_toContinuousAffineMap : (e₁.prodCongr e₂).toContinuousAffineMap =
    e₁.toContinuousAffineMap.prodMap e₂.toContinuousAffineMap :=
  rfl

end

section

variable (k P₁ P₂ P₃)

/-- Product of affine spaces is commutative up to continuous affine isomorphism. -/
@[simps! apply toAffineEquiv]
/--
Definition of `prodComm` / `prodComm` 的定义

English:
definition prodComm
  signature: : P₁ × P₂ ≃ᴬ[k] P₂ × P₁ where
  body: AffineEquiv.prodComm k P₁ P₂
  continuous_toFun := continuous_swap
  continuous_invFun := continuous_swap

@[simp]

中文:
定义 prodComm
  签名: : P₁ × P₂ ≃ᴬ[k] P₂ × P₁ where
  定义体: AffineEquiv.prodComm k P₁ P₂
  continuous_toFun := continuous_swap
  continuous_invFun := continuous_swap

@[simp]

Depends on / 依赖: AffineEquiv, AffineEquiv.prodComm, prodComm
-/
def prodComm : P₁ × P₂ ≃ᴬ[k] P₂ × P₁ where
  __ := AffineEquiv.prodComm k P₁ P₂
  continuous_toFun := continuous_swap
  continuous_invFun := continuous_swap

@[simp]
/--
theorem `prodComm_symm` / 定理 `prodComm_symm`

English:
theorem prodComm_symm
  statement: (prodComm k P₁ P₂).symm = prodComm k P₂ P₁
  proof: rfl

中文:
定理 prodComm_symm
  结论: (prodComm k P₁ P₂).symm = prodComm k P₂ P₁
  证明: rfl
-/
theorem prodComm_symm : (prodComm k P₁ P₂).symm = prodComm k P₂ P₁ :=
  rfl

set_option backward.defeqAttrib.useBackward true in
/-- Product of affine spaces is associative up to continuous affine isomorphism. -/
@[simps! apply toAffineEquiv]
/--
Definition of `prodAssoc` / `prodAssoc` 的定义

English:
definition prodAssoc
  signature: : (P₁ × P₂) × P₃ ≃ᴬ[k] P₁ × (P₂ × P₃) where
  body: AffineEquiv.prodAssoc k P₁ P₂ P₃
  continuous_toFun := by eta_expand; dsimp; fun_prop
  continuous_invFun := by eta_expand; dsimp; fun_prop

中文:
定义 prodAssoc
  签名: : (P₁ × P₂) × P₃ ≃ᴬ[k] P₁ × (P₂ × P₃) where
  定义体: AffineEquiv.prodAssoc k P₁ P₂ P₃
  continuous_toFun := by eta_expand; dsimp; fun_prop
  continuous_invFun := by eta_expand; dsimp; fun_prop

Depends on / 依赖: AffineEquiv, AffineEquiv.prodAssoc, prodAssoc
-/
def prodAssoc : (P₁ × P₂) × P₃ ≃ᴬ[k] P₁ × (P₂ × P₃) where
  __ := AffineEquiv.prodAssoc k P₁ P₂ P₃
  continuous_toFun := by eta_expand; dsimp; fun_prop
  continuous_invFun := by eta_expand; dsimp; fun_prop

end

end ContinuousAffineEquiv
