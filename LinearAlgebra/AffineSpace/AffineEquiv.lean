/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Affine equivalences

In this file we define `AffineEquiv k P₁ P₂` (notation: `P₁ ≃ᵃ[k] P₂`) to be the type of affine
equivalences between `P₁` and `P₂`, i.e., equivalences such that both forward and inverse maps are
affine maps.

We define the following equivalences:

* `AffineEquiv.refl k P`: the identity map as an `AffineEquiv`;

* `e.symm`: the inverse map of an `AffineEquiv` as an `AffineEquiv`;

* `e.trans e'`: composition of two `AffineEquiv`s; note that the order follows `mathlib`'s
  `CategoryTheory` convention (apply `e`, then `e'`), not the convention used in function
  composition and compositions of bundled morphisms.

We equip `AffineEquiv k P P` with a `Group` structure with multiplication corresponding to
composition in `AffineEquiv.group`.

## Tags

affine space, affine equivalence
-/

@[expose] public section

open Function Set

open Affine

/--
Definition of `AffineEquiv` / `AffineEquiv` 的定义

English:
structure AffineEquiv
  parameters: (k P₁ P₂ : Type*) {V₁ V₂ : Type*} [Ring k] [AddCommGroup V₁] [AddCommGroup V₂]
  extends: P₁ ≃ P₂
  axioms and operations (2):
    - linear : V₁ ≃ₗ[k] V₂
    - map_vadd' : forall (p : P₁) (v : V₁), toEquiv (v +ᵥ p) = linear v +ᵥ toEquiv p

中文:
结构 AffineEquiv
  参数: (k P₁ P₂ : 类型) {V₁ V₂ : 类型} [Ring k] [AddCommGroup V₁] [AddCommGroup V₂]
  继承: P₁ ≃ P₂
  公理与运算 (2 个):
    - linear : V₁ ≃ₗ[k] V₂
    - map_vadd' : 对任意 (p : P₁) (v : V₁), toEquiv (v +ᵥ p) = linear v +ᵥ toEquiv p
-/
structure AffineEquiv (k P₁ P₂ : Type*) {V₁ V₂ : Type*} [Ring k] [AddCommGroup V₁] [AddCommGroup V₂]
  [Module k V₁] [Module k V₂] [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] extends P₁ ≃ P₂ where
  /-- The underlying linear equiv of modules. -/
  linear : V₁ ≃ₗ[k] V₂
  map_vadd' : forall (p : P₁) (v : V₁), toEquiv (v +ᵥ p) = linear v +ᵥ toEquiv p

@[inherit_doc]
notation:25 P₁ " ≃ᵃ[" k:25 "] " P₂:0 => AffineEquiv k P₁ P₂

variable {k P₁ P₂ P₃ P₄ V₁ V₂ V₃ V₄ : Type*} [Ring k]
  [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃] [AddCommGroup V₄]
  [Module k V₁] [Module k V₂] [Module k V₃] [Module k V₄]
  [AddTorsor V₁ P₁] [AddTorsor V₂ P₂] [AddTorsor V₃ P₃] [AddTorsor V₄ P₄]

namespace AffineEquiv

/-- Reinterpret an `AffineEquiv` as an `AffineMap`. -/
@[coe]
/--
Definition of `toAffineMap` / `toAffineMap` 的定义

English:
definition toAffineMap
  signature: (e : P₁ ≃ᵃ[k] P₂)
  body: { e with }

@[simp]

中文:
定义 toAffineMap
  签名: (e : P₁ ≃ᵃ[k] P₂)
  定义体: { e with }

@[simp]
-/
def toAffineMap (e : P₁ ≃ᵃ[k] P₂) : P₁ ->ᵃ[k] P₂ :=
  { e with }

@[simp]
/--
theorem `toAffineMap_mk` / 定理 `toAffineMap_mk`

English:
theorem toAffineMap_mk
  given: (f : P₁ ≃ P₂) (f' : V₁ ≃ₗ[k] V₂) (h)
  proof: rfl

@[simp]

中文:
定理 toAffineMap_mk
  条件: (f : P₁ ≃ P₂) (f' : V₁ ≃ₗ[k] V₂) (h)
  证明: rfl

@[simp]
-/
theorem toAffineMap_mk (f : P₁ ≃ P₂) (f' : V₁ ≃ₗ[k] V₂) (h) :
    toAffineMap (mk f f' h) = ⟨f, f', h⟩ :=
  rfl

@[simp]
/--
theorem `linear_toAffineMap` / 定理 `linear_toAffineMap`

English:
theorem linear_toAffineMap
  given: (e : P₁ ≃ᵃ[k] P₂)
  statement: e.toAffineMap.linear = e.linear
  proof: rfl

中文:
定理 linear_toAffineMap
  条件: (e : P₁ ≃ᵃ[k] P₂)
  结论: e.toAffineMap.linear = e.linear
  证明: rfl
-/
theorem linear_toAffineMap (e : P₁ ≃ᵃ[k] P₂) : e.toAffineMap.linear = e.linear :=
  rfl

/--
theorem `toAffineMap_injective` / 定理 `toAffineMap_injective`

English:
theorem toAffineMap_injective
  statement: Injective (toAffineMap : (P₁ ≃ᵃ[k] P₂) -> P₁ ->ᵃ[k] P₂)
  proof: by
  rintro ⟨e, el, h⟩ ⟨e', el', h'⟩ H
  simp_all

@[simp]

中文:
定理 toAffineMap_injective
  结论: Injective (toAffineMap : (P₁ ≃ᵃ[k] P₂) -> P₁ ->ᵃ[k] P₂)
  证明: by
  rintro ⟨e, el, h⟩ ⟨e', el', h'⟩ H
  simp_all

@[simp]
-/
theorem toAffineMap_injective : Injective (toAffineMap : (P₁ ≃ᵃ[k] P₂) -> P₁ ->ᵃ[k] P₂) := by
  rintro ⟨e, el, h⟩ ⟨e', el', h'⟩ H
  simp_all

@[simp]
/--
theorem `toAffineMap_inj` / 定理 `toAffineMap_inj`

English:
theorem toAffineMap_inj
  given: {e e' : P₁ ≃ᵃ[k] P₂}
  statement: e.toAffineMap = e'.toAffineMap ↔ e = e'
  proof: toAffineMap_injective.eq_iff

中文:
定理 toAffineMap_inj
  条件: {e e' : P₁ ≃ᵃ[k] P₂}
  结论: e.toAffineMap = e'.toAffineMap ↔ e = e'
  证明: toAffineMap_injective.eq_iff

Depends on / 依赖: eq_iff, toAffineMap_injective, toAffineMap_injective.eq_iff
-/
theorem toAffineMap_inj {e e' : P₁ ≃ᵃ[k] P₂} : e.toAffineMap = e'.toAffineMap ↔ e = e' :=
  toAffineMap_injective.eq_iff

/--
Instance `equivLike` / 实例 `equivLike`

English:
instance equivLike
  signature: : EquivLike (P₁ ≃ᵃ[k] P₂) P₁ P₂ where
  body: f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' _ _ h _ := toAffineMap_injective (DFunLike.coe_injective h)

中文:
实例 equivLike
  签名: : EquivLike (P₁ ≃ᵃ[k] P₂) P₁ P₂ where
  定义体: f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' _ _ h _ := toAffineMap_injective (DFunLike.coe_injective h)

Depends on / 依赖: f.toFun
-/
instance equivLike : EquivLike (P₁ ≃ᵃ[k] P₂) P₁ P₂ where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' _ _ h _ := toAffineMap_injective (DFunLike.coe_injective h)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeOut (P₁ ≃ᵃ[k] P₂) (P₁ ≃ P₂)
  body: ⟨AffineEquiv.toEquiv⟩

@[simp]

中文:
实例 :
  签名: CoeOut (P₁ ≃ᵃ[k] P₂) (P₁ ≃ P₂)
  定义体: ⟨AffineEquiv.toEquiv⟩

@[simp]

Depends on / 依赖: AffineEquiv, AffineEquiv.toEquiv, toEquiv
-/
instance : CoeOut (P₁ ≃ᵃ[k] P₂) (P₁ ≃ P₂) :=
  ⟨AffineEquiv.toEquiv⟩

@[simp]
/--
theorem `map_vadd` / 定理 `map_vadd`

English:
theorem map_vadd
  given: (e : P₁ ≃ᵃ[k] P₂) (p : P₁) (v : V₁)
  statement: e (v +ᵥ p) = e.linear v +ᵥ e p
  proof: e.map_vadd' p v

@[simp]

中文:
定理 map_vadd
  条件: (e : P₁ ≃ᵃ[k] P₂) (p : P₁) (v : V₁)
  结论: e (v +ᵥ p) = e.linear v +ᵥ e p
  证明: e.map_vadd' p v

@[simp]

Depends on / 依赖: e.map_vadd, map_vadd
-/
theorem map_vadd (e : P₁ ≃ᵃ[k] P₂) (p : P₁) (v : V₁) : e (v +ᵥ p) = e.linear v +ᵥ e p :=
  e.map_vadd' p v

@[simp]
/--
theorem `coe_toEquiv` / 定理 `coe_toEquiv`

English:
theorem coe_toEquiv
  given: (e : P₁ ≃ᵃ[k] P₂)
  statement: ⇑e.toEquiv = e
  proof: rfl

中文:
定理 coe_toEquiv
  条件: (e : P₁ ≃ᵃ[k] P₂)
  结论: ⇑e.toEquiv = e
  证明: rfl
-/
theorem coe_toEquiv (e : P₁ ≃ᵃ[k] P₂) : ⇑e.toEquiv = e :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (P₁ ≃ᵃ[k] P₂) (P₁ ->ᵃ[k] P₂)
  body: ⟨toAffineMap⟩

@[simp]

中文:
实例 :
  签名: Coe (P₁ ≃ᵃ[k] P₂) (P₁ ->ᵃ[k] P₂)
  定义体: ⟨toAffineMap⟩

@[simp]

Depends on / 依赖: toAffineMap
-/
instance : Coe (P₁ ≃ᵃ[k] P₂) (P₁ ->ᵃ[k] P₂) :=
  ⟨toAffineMap⟩

@[simp]
/--
theorem `coe_toAffineMap` / 定理 `coe_toAffineMap`

English:
theorem coe_toAffineMap
  given: (e : P₁ ≃ᵃ[k] P₂)
  statement: (e.toAffineMap : P₁ -> P₂) = (e : P₁ -> P₂)
  proof: rfl

@[norm_cast, simp]

中文:
定理 coe_toAffineMap
  条件: (e : P₁ ≃ᵃ[k] P₂)
  结论: (e.toAffineMap : P₁ -> P₂) = (e : P₁ -> P₂)
  证明: rfl

@[norm_cast, simp]
-/
theorem coe_toAffineMap (e : P₁ ≃ᵃ[k] P₂) : (e.toAffineMap : P₁ -> P₂) = (e : P₁ -> P₂) :=
  rfl

@[norm_cast, simp]
/--
theorem `coe_coe` / 定理 `coe_coe`

English:
theorem coe_coe
  given: (e : P₁ ≃ᵃ[k] P₂)
  statement: ((e : P₁ ->ᵃ[k] P₂) : P₁ -> P₂) = e
  proof: rfl

@[simp]

中文:
定理 coe_coe
  条件: (e : P₁ ≃ᵃ[k] P₂)
  结论: ((e : P₁ ->ᵃ[k] P₂) : P₁ -> P₂) = e
  证明: rfl

@[simp]
-/
theorem coe_coe (e : P₁ ≃ᵃ[k] P₂) : ((e : P₁ ->ᵃ[k] P₂) : P₁ -> P₂) = e :=
  rfl

@[simp]
/--
theorem `coe_linear` / 定理 `coe_linear`

English:
theorem coe_linear
  given: (e : P₁ ≃ᵃ[k] P₂)
  statement: (e : P₁ ->ᵃ[k] P₂).linear = e.linear
  proof: rfl

@[ext]

中文:
定理 coe_linear
  条件: (e : P₁ ≃ᵃ[k] P₂)
  结论: (e : P₁ ->ᵃ[k] P₂).linear = e.linear
  证明: rfl

@[ext]
-/
theorem coe_linear (e : P₁ ≃ᵃ[k] P₂) : (e : P₁ ->ᵃ[k] P₂).linear = e.linear :=
  rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {e e' : P₁ ≃ᵃ[k] P₂} (h : forall x, e x = e' x)
  statement: e = e'
  proof: DFunLike.ext _ _ h

中文:
定理 ext
  条件: {e e' : P₁ ≃ᵃ[k] P₂} (h : 对任意 x, e x = e' x)
  结论: e = e'
  证明: DFunLike.ext _ _ h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {e e' : P₁ ≃ᵃ[k] P₂} (h : forall x, e x = e' x) : e = e' :=
  DFunLike.ext _ _ h

/--
theorem `coeFn_injective` / 定理 `coeFn_injective`

English:
theorem coeFn_injective
  statement: @Injective (P₁ ≃ᵃ[k] P₂) (P₁ -> P₂) (⇑)
  proof: DFunLike.coe_injective

@[norm_cast]

中文:
定理 coeFn_injective
  结论: @Injective (P₁ ≃ᵃ[k] P₂) (P₁ -> P₂) (⇑)
  证明: DFunLike.coe_injective

@[norm_cast]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem coeFn_injective : @Injective (P₁ ≃ᵃ[k] P₂) (P₁ -> P₂) (⇑) :=
  DFunLike.coe_injective

@[norm_cast]
/--
theorem `coeFn_inj` / 定理 `coeFn_inj`

English:
theorem coeFn_inj
  given: {e e' : P₁ ≃ᵃ[k] P₂}
  statement: (e : P₁ -> P₂) = e' ↔ e = e'
  proof: by simp

中文:
定理 coeFn_inj
  条件: {e e' : P₁ ≃ᵃ[k] P₂}
  结论: (e : P₁ -> P₂) = e' ↔ e = e'
  证明: by simp
-/
theorem coeFn_inj {e e' : P₁ ≃ᵃ[k] P₂} : (e : P₁ -> P₂) = e' ↔ e = e' := by simp

/--
theorem `toEquiv_injective` / 定理 `toEquiv_injective`

English:
theorem toEquiv_injective
  statement: Injective (toEquiv : (P₁ ≃ᵃ[k] P₂) -> P₁ ≃ P₂)
  proof: fun _ _ H =>
ext Equiv.ext_iff.1 H

@[simp]

中文:
定理 toEquiv_injective
  结论: Injective (toEquiv : (P₁ ≃ᵃ[k] P₂) -> P₁ ≃ P₂)
  证明: fun _ _ H =>
ext Equiv.ext_iff.1 H

@[simp]
-/
theorem toEquiv_injective : Injective (toEquiv : (P₁ ≃ᵃ[k] P₂) -> P₁ ≃ P₂) := fun _ _ H =>
ext Equiv.ext_iff.1 H

@[simp]
/--
theorem `toEquiv_inj` / 定理 `toEquiv_inj`

English:
theorem toEquiv_inj
  given: {e e' : P₁ ≃ᵃ[k] P₂}
  statement: e.toEquiv = e'.toEquiv ↔ e = e'
  proof: toEquiv_injective.eq_iff

@[simp]

中文:
定理 toEquiv_inj
  条件: {e e' : P₁ ≃ᵃ[k] P₂}
  结论: e.toEquiv = e'.toEquiv ↔ e = e'
  证明: toEquiv_injective.eq_iff

@[simp]

Depends on / 依赖: eq_iff, toEquiv_injective, toEquiv_injective.eq_iff
-/
theorem toEquiv_inj {e e' : P₁ ≃ᵃ[k] P₂} : e.toEquiv = e'.toEquiv ↔ e = e' :=
  toEquiv_injective.eq_iff

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (e : P₁ ≃ P₂) (e' : V₁ ≃ₗ[k] V₂) (h)
  statement: ((⟨e, e', h⟩ : P₁ ≃ᵃ[k] P₂) : P₁ -> P₂) = e
  proof: rfl

中文:
定理 coe_mk
  条件: (e : P₁ ≃ P₂) (e' : V₁ ≃ₗ[k] V₂) (h)
  结论: ((⟨e, e', h⟩ : P₁ ≃ᵃ[k] P₂) : P₁ -> P₂) = e
  证明: rfl
-/
theorem coe_mk (e : P₁ ≃ P₂) (e' : V₁ ≃ₗ[k] V₂) (h) : ((⟨e, e', h⟩ : P₁ ≃ᵃ[k] P₂) : P₁ -> P₂) = e :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: (e : P₁ -> P₂) (e' : V₁ ≃ₗ[k] V₂) (p : P₁) (h : forall p' : P₁, e p' = e' (p' -ᵥ p) +ᵥ e p)
  body: e
  invFun := fun q' : P₂ => e'.symm (q' -ᵥ e p) +ᵥ p
  left_inv p' := by simp [h p', vadd_vsub, vsub_vadd]
  right_inv q' := by simp [h (e'.symm (q' -ᵥ e p) +ᵥ p), vadd_vsub, vsub_vadd]
  linear := e'
  map_vadd' p' v := by simp [h p', h (v +ᵥ p'), vadd_vsub_assoc, vadd_vadd]

@[simp]

中文:
定义 mk'
  签名: (e : P₁ -> P₂) (e' : V₁ ≃ₗ[k] V₂) (p : P₁) (h : 对任意 p' : P₁, e p' = e' (p' -ᵥ p) +ᵥ e p)
  定义体: e
  invFun := fun q' : P₂ => e'.symm (q' -ᵥ e p) +ᵥ p
  left_inv p' := by simp [h p', vadd_vsub, vsub_vadd]
  right_inv q' := by simp [h (e'.symm (q' -ᵥ e p) +ᵥ p), vadd_vsub, vsub_vadd]
  linear := e'
  map_vadd' p' v := by simp [h p', h (v +ᵥ p'), vadd_vsub_assoc, vadd_vadd]

@[simp]
-/
def mk' (e : P₁ -> P₂) (e' : V₁ ≃ₗ[k] V₂) (p : P₁) (h : forall p' : P₁, e p' = e' (p' -ᵥ p) +ᵥ e p) :
    P₁ ≃ᵃ[k] P₂ where
  toFun := e
  invFun := fun q' : P₂ => e'.symm (q' -ᵥ e p) +ᵥ p
  left_inv p' := by simp [h p', vadd_vsub, vsub_vadd]
  right_inv q' := by simp [h (e'.symm (q' -ᵥ e p) +ᵥ p), vadd_vsub, vsub_vadd]
  linear := e'
  map_vadd' p' v := by simp [h p', h (v +ᵥ p'), vadd_vsub_assoc, vadd_vadd]

@[simp]
/--
theorem `coe_mk'` / 定理 `coe_mk'`

English:
theorem coe_mk'
  given: (e : P₁ ≃ P₂) (e' : V₁ ≃ₗ[k] V₂) (p h)
  statement: ⇑(mk' e e' p h) = e
  proof: rfl

@[simp]

中文:
定理 coe_mk'
  条件: (e : P₁ ≃ P₂) (e' : V₁ ≃ₗ[k] V₂) (p h)
  结论: ⇑(mk' e e' p h) = e
  证明: rfl

@[simp]
-/
theorem coe_mk' (e : P₁ ≃ P₂) (e' : V₁ ≃ₗ[k] V₂) (p h) : ⇑(mk' e e' p h) = e :=
  rfl

@[simp]
/--
theorem `linear_mk'` / 定理 `linear_mk'`

English:
theorem linear_mk'
  given: (e : P₁ ≃ P₂) (e' : V₁ ≃ₗ[k] V₂) (p h)
  statement: (mk' e e' p h).linear = e'
  proof: rfl

中文:
定理 linear_mk'
  条件: (e : P₁ ≃ P₂) (e' : V₁ ≃ₗ[k] V₂) (p h)
  结论: (mk' e e' p h).linear = e'
  证明: rfl
-/
theorem linear_mk' (e : P₁ ≃ P₂) (e' : V₁ ≃ₗ[k] V₂) (p h) : (mk' e e' p h).linear = e' :=
  rfl

/-- Inverse of an affine equivalence as an affine equivalence. -/
@[symm]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: (e : P₁ ≃ᵃ[k] P₂)
  body: e.toEquiv.symm
  linear := e.linear.symm
  map_vadd' p v :=
e.toEquiv.symm.eq_symm_apply.1 by
      rw [Equiv.symm_symm]; rw [e.map_vadd' ((Equiv.symm e.toEquiv) p) ((LinearEquiv.symm e.linear) v)]; rw [LinearEquiv.apply_symm_apply]; rw [Equiv.apply_symm_apply]

@[simp]

中文:
定义 symm
  签名: (e : P₁ ≃ᵃ[k] P₂)
  定义体: e.toEquiv.symm
  linear := e.linear.symm
  map_vadd' p v :=
e.toEquiv.symm.eq_symm_apply.1 by
      rw [Equiv.symm_symm]; rw [e.map_vadd' ((Equiv.symm e.toEquiv) p) ((LinearEquiv.symm e.linear) v)]; rw [LinearEquiv.apply_symm_apply]; rw [Equiv.apply_symm_apply]

@[simp]

Depends on / 依赖: e.toEquiv.symm, toEquiv
-/
def symm (e : P₁ ≃ᵃ[k] P₂) : P₂ ≃ᵃ[k] P₁ where
  toEquiv := e.toEquiv.symm
  linear := e.linear.symm
  map_vadd' p v :=
e.toEquiv.symm.eq_symm_apply.1 by
      rw [Equiv.symm_symm]; rw [e.map_vadd' ((Equiv.symm e.toEquiv) p) ((LinearEquiv.symm e.linear) v)]; rw [LinearEquiv.apply_symm_apply]; rw [Equiv.apply_symm_apply]

@[simp]
/--
theorem `toEquiv_symm` / 定理 `toEquiv_symm`

English:
theorem toEquiv_symm
  given: (e : P₁ ≃ᵃ[k] P₂)
  statement: e.symm.toEquiv = e.toEquiv.symm
  proof: rfl

@[simp]

中文:
定理 toEquiv_symm
  条件: (e : P₁ ≃ᵃ[k] P₂)
  结论: e.symm.toEquiv = e.toEquiv.symm
  证明: rfl

@[simp]
-/
theorem toEquiv_symm (e : P₁ ≃ᵃ[k] P₂) : e.symm.toEquiv = e.toEquiv.symm :=
  rfl

@[simp]
/--
theorem `coe_symm_toEquiv` / 定理 `coe_symm_toEquiv`

English:
theorem coe_symm_toEquiv
  given: (e : P₁ ≃ᵃ[k] P₂)
  statement: ⇑e.toEquiv.symm = e.symm
  proof: rfl

@[simp]

中文:
定理 coe_symm_toEquiv
  条件: (e : P₁ ≃ᵃ[k] P₂)
  结论: ⇑e.toEquiv.symm = e.symm
  证明: rfl

@[simp]
-/
theorem coe_symm_toEquiv (e : P₁ ≃ᵃ[k] P₂) : ⇑e.toEquiv.symm = e.symm :=
  rfl

@[simp]
/--
theorem `linear_symm` / 定理 `linear_symm`

English:
theorem linear_symm
  given: (e : P₁ ≃ᵃ[k] P₂)
  statement: e.symm.linear = e.linear.symm
  proof: rfl

中文:
定理 linear_symm
  条件: (e : P₁ ≃ᵃ[k] P₂)
  结论: e.symm.linear = e.linear.symm
  证明: rfl
-/
theorem linear_symm (e : P₁ ≃ᵃ[k] P₂) : e.symm.linear = e.linear.symm :=
  rfl

/--
Definition of `Simps.apply` / `Simps.apply` 的定义

English:
definition Simps.apply
  signature: (e : P₁ ≃ᵃ[k] P₂)
  body: e

中文:
定义 Simps.apply
  签名: (e : P₁ ≃ᵃ[k] P₂)
  定义体: e
-/
def Simps.apply (e : P₁ ≃ᵃ[k] P₂) : P₁ -> P₂ :=
  e

/--
Definition of `Simps.symm_apply` / `Simps.symm_apply` 的定义

English:
definition Simps.symm_apply
  signature: (e : P₁ ≃ᵃ[k] P₂)
  body: e.symm

initialize_simps_projections AffineEquiv (toEquiv_toFun -> apply, toEquiv_invFun -> symm_apply,
  linear -> linear, as_prefix linear, -toEquiv)

中文:
定义 Simps.symm_apply
  签名: (e : P₁ ≃ᵃ[k] P₂)
  定义体: e.symm

initialize_simps_projections AffineEquiv (toEquiv_toFun -> apply, toEquiv_invFun -> symm_apply,
  linear -> linear, as_prefix linear, -toEquiv)
-/
def Simps.symm_apply (e : P₁ ≃ᵃ[k] P₂) : P₂ -> P₁ :=
  e.symm

initialize_simps_projections AffineEquiv (toEquiv_toFun -> apply, toEquiv_invFun -> symm_apply,
  linear -> linear, as_prefix linear, -toEquiv)

/--
theorem `bijective` / 定理 `bijective`

English:
theorem bijective
  given: (e : P₁ ≃ᵃ[k] P₂)
  statement: Bijective e
  proof: e.toEquiv.bijective

中文:
定理 bijective
  条件: (e : P₁ ≃ᵃ[k] P₂)
  结论: Bijective e
  证明: e.toEquiv.bijective
-/
protected theorem bijective (e : P₁ ≃ᵃ[k] P₂) : Bijective e :=
  e.toEquiv.bijective

/--
theorem `surjective` / 定理 `surjective`

English:
theorem surjective
  given: (e : P₁ ≃ᵃ[k] P₂)
  statement: Surjective e
  proof: e.toEquiv.surjective

中文:
定理 surjective
  条件: (e : P₁ ≃ᵃ[k] P₂)
  结论: Surjective e
  证明: e.toEquiv.surjective
-/
protected theorem surjective (e : P₁ ≃ᵃ[k] P₂) : Surjective e :=
  e.toEquiv.surjective

/--
theorem `injective` / 定理 `injective`

English:
theorem injective
  given: (e : P₁ ≃ᵃ[k] P₂)
  statement: Injective e
  proof: e.toEquiv.injective

中文:
定理 injective
  条件: (e : P₁ ≃ᵃ[k] P₂)
  结论: Injective e
  证明: e.toEquiv.injective
-/
protected theorem injective (e : P₁ ≃ᵃ[k] P₂) : Injective e :=
  e.toEquiv.injective

/-- Bijective affine maps are affine isomorphisms. -/
@[simps! linear apply]
/--
Definition of `ofBijective` / `ofBijective` 的定义

English:
definition ofBijective
  signature: {φ : P₁ ->ᵃ[k] P₂} (hφ : Function.Bijective φ)
  body: { Equiv.ofBijective _ hφ with
    linear := LinearEquiv.ofBijective φ.linear (φ.linear_bijective_iff.mpr hφ)
    map_vadd' := φ.map_vadd }

中文:
定义 ofBijective
  签名: {φ : P₁ ->ᵃ[k] P₂} (hφ : Function.Bijective φ)
  定义体: { Equiv.ofBijective _ hφ with
    linear := LinearEquiv.ofBijective φ.linear (φ.linear_bijective_iff.mpr hφ)
    map_vadd' := φ.map_vadd }

Depends on / 依赖: Equiv.ofBijective, LinearEquiv, LinearEquiv.ofBijective, linear, linear_bijective_iff, linear_bijective_iff.mpr, map_vadd, ofBijective
-/
noncomputable def ofBijective {φ : P₁ ->ᵃ[k] P₂} (hφ : Function.Bijective φ) : P₁ ≃ᵃ[k] P₂ :=
  { Equiv.ofBijective _ hφ with
    linear := LinearEquiv.ofBijective φ.linear (φ.linear_bijective_iff.mpr hφ)
    map_vadd' := φ.map_vadd }

/--
theorem `ofBijective.symm_eq` / 定理 `ofBijective.symm_eq`

English:
theorem ofBijective.symm_eq
  given: {φ : P₁ ->ᵃ[k] P₂} (hφ : Function.Bijective φ)
  proof: rfl

中文:
定理 ofBijective.symm_eq
  条件: {φ : P₁ ->ᵃ[k] P₂} (hφ : Function.Bijective φ)
  证明: rfl
-/
theorem ofBijective.symm_eq {φ : P₁ ->ᵃ[k] P₂} (hφ : Function.Bijective φ) :
    (ofBijective hφ).symm.toEquiv = (Equiv.ofBijective _ hφ).symm :=
  rfl

/--
theorem `range_eq` / 定理 `range_eq`

English:
theorem range_eq
  given: (e : P₁ ≃ᵃ[k] P₂)
  statement: range e = univ
  proof: by simp

@[simp]

中文:
定理 range_eq
  条件: (e : P₁ ≃ᵃ[k] P₂)
  结论: range e = univ
  证明: by simp

@[simp]
-/
theorem range_eq (e : P₁ ≃ᵃ[k] P₂) : range e = univ := by simp

@[simp]
/--
theorem `apply_symm_apply` / 定理 `apply_symm_apply`

English:
theorem apply_symm_apply
  given: (e : P₁ ≃ᵃ[k] P₂) (p : P₂)
  statement: e (e.symm p) = p
  proof: e.toEquiv.apply_symm_apply p

@[simp]

中文:
定理 apply_symm_apply
  条件: (e : P₁ ≃ᵃ[k] P₂) (p : P₂)
  结论: e (e.symm p) = p
  证明: e.toEquiv.apply_symm_apply p

@[simp]

Depends on / 依赖: apply_symm_apply, e.toEquiv.apply_symm_apply, toEquiv
-/
theorem apply_symm_apply (e : P₁ ≃ᵃ[k] P₂) (p : P₂) : e (e.symm p) = p :=
  e.toEquiv.apply_symm_apply p

@[simp]
/--
theorem `symm_apply_apply` / 定理 `symm_apply_apply`

English:
theorem symm_apply_apply
  given: (e : P₁ ≃ᵃ[k] P₂) (p : P₁)
  statement: e.symm (e p) = p
  proof: e.toEquiv.symm_apply_apply p

中文:
定理 symm_apply_apply
  条件: (e : P₁ ≃ᵃ[k] P₂) (p : P₁)
  结论: e.symm (e p) = p
  证明: e.toEquiv.symm_apply_apply p

Depends on / 依赖: e.toEquiv.symm_apply_apply, symm_apply_apply, toEquiv
-/
theorem symm_apply_apply (e : P₁ ≃ᵃ[k] P₂) (p : P₁) : e.symm (e p) = p :=
  e.toEquiv.symm_apply_apply p

/--
theorem `symm_apply_eq` / 定理 `symm_apply_eq`

English:
theorem symm_apply_eq
  given: (e : P₁ ≃ᵃ[k] P₂) {p₁ p₂}
  statement: e.symm p₁ = p₂ ↔ p₁ = e p₂
  proof: e.toEquiv.symm_apply_eq

中文:
定理 symm_apply_eq
  条件: (e : P₁ ≃ᵃ[k] P₂) {p₁ p₂}
  结论: e.symm p₁ = p₂ ↔ p₁ = e p₂
  证明: e.toEquiv.symm_apply_eq

Depends on / 依赖: e.toEquiv.symm_apply_eq, symm_apply_eq, toEquiv
-/
theorem symm_apply_eq (e : P₁ ≃ᵃ[k] P₂) {p₁ p₂} : e.symm p₁ = p₂ ↔ p₁ = e p₂ :=
  e.toEquiv.symm_apply_eq

/--
theorem `eq_symm_apply` / 定理 `eq_symm_apply`

English:
theorem eq_symm_apply
  given: (e : P₁ ≃ᵃ[k] P₂) {p₁ p₂}
  statement: p₂ = e.symm p₁ ↔ e p₂ = p₁
  proof: e.toEquiv.eq_symm_apply

@[deprecated eq_symm_apply (since := "2026-07-26")]

中文:
定理 eq_symm_apply
  条件: (e : P₁ ≃ᵃ[k] P₂) {p₁ p₂}
  结论: p₂ = e.symm p₁ ↔ e p₂ = p₁
  证明: e.toEquiv.eq_symm_apply

@[deprecated eq_symm_apply (since := "2026-07-26")]

Depends on / 依赖: e.toEquiv.eq_symm_apply, eq_symm_apply, toEquiv
-/
theorem eq_symm_apply (e : P₁ ≃ᵃ[k] P₂) {p₁ p₂} : p₂ = e.symm p₁ ↔ e p₂ = p₁ :=
  e.toEquiv.eq_symm_apply

@[deprecated eq_symm_apply (since := "2026-07-26")]
/--
theorem `apply_eq_iff_eq_symm_apply` / 定理 `apply_eq_iff_eq_symm_apply`

English:
theorem apply_eq_iff_eq_symm_apply
  given: (e : P₁ ≃ᵃ[k] P₂) {p₁ p₂}
  statement: e p₁ = p₂ ↔ p₁ = e.symm p₂
  proof: e.eq_symm_apply.symm

中文:
定理 apply_eq_iff_eq_symm_apply
  条件: (e : P₁ ≃ᵃ[k] P₂) {p₁ p₂}
  结论: e p₁ = p₂ ↔ p₁ = e.symm p₂
  证明: e.eq_symm_apply.symm

Depends on / 依赖: e.eq_symm_apply.symm, eq_symm_apply
-/
theorem apply_eq_iff_eq_symm_apply (e : P₁ ≃ᵃ[k] P₂) {p₁ p₂} : e p₁ = p₂ ↔ p₁ = e.symm p₂ :=
  e.eq_symm_apply.symm

/--
theorem `apply_eq_iff_eq` / 定理 `apply_eq_iff_eq`

English:
theorem apply_eq_iff_eq
  given: (e : P₁ ≃ᵃ[k] P₂) {p₁ p₂ : P₁}
  statement: e p₁ = e p₂ ↔ p₁ = p₂
  proof: by simp

@[simp]

中文:
定理 apply_eq_iff_eq
  条件: (e : P₁ ≃ᵃ[k] P₂) {p₁ p₂ : P₁}
  结论: e p₁ = e p₂ ↔ p₁ = p₂
  证明: by simp

@[simp]

Depends on / 依赖: finSuccEquiv
-/
theorem apply_eq_iff_eq (e : P₁ ≃ᵃ[k] P₂) {p₁ p₂ : P₁} : e p₁ = e p₂ ↔ p₁ = p₂ := by simp

@[simp]
/--
theorem `image_symm` / 定理 `image_symm`

English:
theorem image_symm
  given: (f : P₁ ≃ᵃ[k] P₂) (s : Set P₂)
  statement: f.symm '' s = f ⁻¹' s
  proof: f.symm.toEquiv.image_eq_preimage_symm _

@[simp]

中文:
定理 image_symm
  条件: (f : P₁ ≃ᵃ[k] P₂) (s : Set P₂)
  结论: f.symm '' s = f ⁻¹' s
  证明: f.symm.toEquiv.image_eq_preimage_symm _

@[simp]

Depends on / 依赖: Fin.insertNth_apply_succAbove, f.symm.toEquiv.image_eq_preimage_symm, image_eq_preimage_symm, insertNth_apply_succAbove, toEquiv
-/
theorem image_symm (f : P₁ ≃ᵃ[k] P₂) (s : Set P₂) : f.symm '' s = f ⁻¹' s :=
  f.symm.toEquiv.image_eq_preimage_symm _

@[simp]
/--
theorem `preimage_symm` / 定理 `preimage_symm`

English:
theorem preimage_symm
  given: (f : P₁ ≃ᵃ[k] P₂) (s : Set P₁)
  statement: f.symm ⁻¹' s = f '' s
  proof: (f.symm.image_symm _).symm

中文:
定理 preimage_symm
  条件: (f : P₁ ≃ᵃ[k] P₂) (s : Set P₁)
  结论: f.symm ⁻¹' s = f '' s
  证明: (f.symm.image_symm _).symm

Depends on / 依赖: Fin.succAbove_of_castSucc_lt, _succAbove, f.symm.image_symm, finSuccEquiv, image_symm, succAbove_of_castSucc_lt
-/
theorem preimage_symm (f : P₁ ≃ᵃ[k] P₂) (s : Set P₁) : f.symm ⁻¹' s = f '' s :=
  (f.symm.image_symm _).symm

variable (k P₁)

/-- Identity map as an `AffineEquiv`. -/
@[refl]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: : P₁ ≃ᵃ[k] P₁ where
  body: Equiv.refl P₁
  linear := LinearEquiv.refl k V₁
  map_vadd' _ _ := rfl

@[simp]

中文:
定义 refl
  签名: : P₁ ≃ᵃ[k] P₁ where
  定义体: Equiv.refl P₁
  linear := LinearEquiv.refl k V₁
  map_vadd' _ _ := rfl

@[simp]

Depends on / 依赖: Equiv.refl, Fin.succAbove_of_le_castSucc, _succAbove, finSuccEquiv, succAbove_of_le_castSucc
-/
def refl : P₁ ≃ᵃ[k] P₁ where
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
theorem `coe_refl_to_affineMap` / 定理 `coe_refl_to_affineMap`

English:
theorem coe_refl_to_affineMap
  statement: ↑(refl k P₁) = AffineMap.id k P₁
  proof: rfl

@[simp]

中文:
定理 coe_refl_to_affineMap
  结论: ↑(refl k P₁) = AffineMap.id k P₁
  证明: rfl

@[simp]
-/
theorem coe_refl_to_affineMap : ↑(refl k P₁) = AffineMap.id k P₁ :=
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

Depends on / 依赖: eq_symm_apply, eq_symm_apply.symm, finSuccEquiv
-/
theorem refl_apply (x : P₁) : refl k P₁ x = x :=
  rfl

@[simp]
/--
theorem `toEquiv_refl` / 定理 `toEquiv_refl`

English:
theorem toEquiv_refl
  statement: (refl k P₁).toEquiv = Equiv.refl P₁
  proof: rfl

@[simp]

中文:
定理 toEquiv_refl
  结论: (refl k P₁).toEquiv = Equiv.refl P₁
  证明: rfl

@[simp]

Depends on / 依赖: eq_comm, eq_symm_apply, eq_symm_apply.symm.trans, finSuccEquiv
-/
theorem toEquiv_refl : (refl k P₁).toEquiv = Equiv.refl P₁ :=
  rfl

@[simp]
/--
theorem `linear_refl` / 定理 `linear_refl`

English:
theorem linear_refl
  statement: (refl k P₁).linear = LinearEquiv.refl k V₁
  proof: rfl

@[simp]

中文:
定理 linear_refl
  结论: (refl k P₁).linear = LinearEquiv.refl k V₁
  证明: rfl

@[simp]

Depends on / 依赖: Fin.succAbove_of_castSucc_lt, succAbove_of_castSucc_lt
-/
theorem linear_refl : (refl k P₁).linear = LinearEquiv.refl k V₁ :=
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

Depends on / 依赖: Fin.succAbove_of_le_castSucc, succAbove_of_le_castSucc
-/
theorem symm_refl : (refl k P₁).symm = refl k P₁ :=
  rfl

variable {k P₁}

/-- Composition of two `AffineEquiv`alences, applied left to right. -/
@[trans]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (e : P₁ ≃ᵃ[k] P₂) (e' : P₂ ≃ᵃ[k] P₃)
  body: e.toEquiv.trans e'.toEquiv
  linear := e.linear.trans e'.linear
  map_vadd' p v := by
    simp only [LinearEquiv.trans_apply, coe_toEquiv, (· ∘ ·), Equiv.coe_trans, map_vadd]

@[simp]

中文:
定义 trans
  签名: (e : P₁ ≃ᵃ[k] P₂) (e' : P₂ ≃ᵃ[k] P₃)
  定义体: e.toEquiv.trans e'.toEquiv
  linear := e.linear.trans e'.linear
  map_vadd' p v := by
    simp only [LinearEquiv.trans_apply, coe_toEquiv, (· ∘ ·), Equiv.coe_trans, map_vadd]

@[simp]

Depends on / 依赖: _symm_some_below, e.toEquiv.trans, finSuccEquiv, toEquiv
-/
def trans (e : P₁ ≃ᵃ[k] P₂) (e' : P₂ ≃ᵃ[k] P₃) : P₁ ≃ᵃ[k] P₃ where
  toEquiv := e.toEquiv.trans e'.toEquiv
  linear := e.linear.trans e'.linear
  map_vadd' p v := by
    simp only [LinearEquiv.trans_apply, coe_toEquiv, (· ∘ ·), Equiv.coe_trans, map_vadd]

@[simp]
/--
theorem `coe_trans` / 定理 `coe_trans`

English:
theorem coe_trans
  given: (e : P₁ ≃ᵃ[k] P₂) (e' : P₂ ≃ᵃ[k] P₃)
  statement: ⇑(e.trans e') = e' ∘ e
  proof: rfl

@[simp]

中文:
定理 coe_trans
  条件: (e : P₁ ≃ᵃ[k] P₂) (e' : P₂ ≃ᵃ[k] P₃)
  结论: ⇑(e.trans e') = e' ∘ e
  证明: rfl

@[simp]

Depends on / 依赖: _symm_some_above, finSuccEquiv
-/
theorem coe_trans (e : P₁ ≃ᵃ[k] P₂) (e' : P₂ ≃ᵃ[k] P₃) : ⇑(e.trans e') = e' ∘ e :=
  rfl

@[simp]
/--
theorem `coe_trans_to_affineMap` / 定理 `coe_trans_to_affineMap`

English:
theorem coe_trans_to_affineMap
  given: (e : P₁ ≃ᵃ[k] P₂) (e' : P₂ ≃ᵃ[k] P₃)
  proof: rfl

@[simp]

中文:
定理 coe_trans_to_affineMap
  条件: (e : P₁ ≃ᵃ[k] P₂) (e' : P₂ ≃ᵃ[k] P₃)
  证明: rfl

@[simp]
-/
theorem coe_trans_to_affineMap (e : P₁ ≃ᵃ[k] P₂) (e' : P₂ ≃ᵃ[k] P₃) :
    (e.trans e' : P₁ ->ᵃ[k] P₃) = (e' : P₂ ->ᵃ[k] P₃).comp e :=
  rfl

@[simp]
/--
theorem `trans_apply` / 定理 `trans_apply`

English:
theorem trans_apply
  given: (e : P₁ ≃ᵃ[k] P₂) (e' : P₂ ≃ᵃ[k] P₃) (p : P₁)
  statement: e.trans e' p = e' (e p)
  proof: rfl

中文:
定理 trans_apply
  条件: (e : P₁ ≃ᵃ[k] P₂) (e' : P₂ ≃ᵃ[k] P₃) (p : P₁)
  结论: e.trans e' p = e' (e p)
  证明: rfl
-/
theorem trans_apply (e : P₁ ≃ᵃ[k] P₂) (e' : P₂ ≃ᵃ[k] P₃) (p : P₁) : e.trans e' p = e' (e p) :=
  rfl

/--
theorem `trans_assoc` / 定理 `trans_assoc`

English:
theorem trans_assoc
  given: (e₁ : P₁ ≃ᵃ[k] P₂) (e₂ : P₂ ≃ᵃ[k] P₃) (e₃ : P₃ ≃ᵃ[k] P₄)
  proof: ext fun _ => rfl

@[simp]

中文:
定理 trans_assoc
  条件: (e₁ : P₁ ≃ᵃ[k] P₂) (e₂ : P₂ ≃ᵃ[k] P₃) (e₃ : P₃ ≃ᵃ[k] P₄)
  证明: ext fun _ => rfl

@[simp]
-/
theorem trans_assoc (e₁ : P₁ ≃ᵃ[k] P₂) (e₂ : P₂ ≃ᵃ[k] P₃) (e₃ : P₃ ≃ᵃ[k] P₄) :
    (e₁.trans e₂).trans e₃ = e₁.trans (e₂.trans e₃) :=
  ext fun _ => rfl

@[simp]
/--
theorem `trans_refl` / 定理 `trans_refl`

English:
theorem trans_refl
  given: (e : P₁ ≃ᵃ[k] P₂)
  statement: e.trans (refl k P₂) = e
  proof: ext fun _ => rfl

@[simp]

中文:
定理 trans_refl
  条件: (e : P₁ ≃ᵃ[k] P₂)
  结论: e.trans (refl k P₂) = e
  证明: ext fun _ => rfl

@[simp]
-/
theorem trans_refl (e : P₁ ≃ᵃ[k] P₂) : e.trans (refl k P₂) = e :=
  ext fun _ => rfl

@[simp]
/--
theorem `refl_trans` / 定理 `refl_trans`

English:
theorem refl_trans
  given: (e : P₁ ≃ᵃ[k] P₂)
  statement: (refl k P₁).trans e = e
  proof: ext fun _ => rfl

@[simp]

中文:
定理 refl_trans
  条件: (e : P₁ ≃ᵃ[k] P₂)
  结论: (refl k P₁).trans e = e
  证明: ext fun _ => rfl

@[simp]
-/
theorem refl_trans (e : P₁ ≃ᵃ[k] P₂) : (refl k P₁).trans e = e :=
  ext fun _ => rfl

@[simp]
/--
theorem `self_trans_symm` / 定理 `self_trans_symm`

English:
theorem self_trans_symm
  given: (e : P₁ ≃ᵃ[k] P₂)
  statement: e.trans e.symm = refl k P₁
  proof: ext e.symm_apply_apply

@[simp]

中文:
定理 self_trans_symm
  条件: (e : P₁ ≃ᵃ[k] P₂)
  结论: e.trans e.symm = refl k P₁
  证明: ext e.symm_apply_apply

@[simp]

Depends on / 依赖: e.symm_apply_apply, symm_apply_apply
-/
theorem self_trans_symm (e : P₁ ≃ᵃ[k] P₂) : e.trans e.symm = refl k P₁ :=
  ext e.symm_apply_apply

@[simp]
/--
theorem `symm_trans_self` / 定理 `symm_trans_self`

English:
theorem symm_trans_self
  given: (e : P₁ ≃ᵃ[k] P₂)
  statement: e.symm.trans e = refl k P₂
  proof: ext e.apply_symm_apply

中文:
定理 symm_trans_self
  条件: (e : P₁ ≃ᵃ[k] P₂)
  结论: e.symm.trans e = refl k P₂
  证明: ext e.apply_symm_apply

Depends on / 依赖: apply_symm_apply, e.apply_symm_apply
-/
theorem symm_trans_self (e : P₁ ≃ᵃ[k] P₂) : e.symm.trans e = refl k P₂ :=
  ext e.apply_symm_apply

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `apply_lineMap` / 定理 `apply_lineMap`

English:
theorem apply_lineMap
  given: (e : P₁ ≃ᵃ[k] P₂) (a b : P₁) (c : k)
  proof: e.toAffineMap.apply_lineMap a b c

中文:
定理 apply_lineMap
  条件: (e : P₁ ≃ᵃ[k] P₂) (a b : P₁) (c : k)
  证明: e.toAffineMap.apply_lineMap a b c

Depends on / 依赖: apply_lineMap, e.toAffineMap.apply_lineMap, toAffineMap
-/
theorem apply_lineMap (e : P₁ ≃ᵃ[k] P₂) (a b : P₁) (c : k) :
    e (AffineMap.lineMap a b c) = AffineMap.lineMap (e a) (e b) c :=
  e.toAffineMap.apply_lineMap a b c

/--
Instance `group` / 实例 `group`

English:
instance group
  signature: : Group (P₁ ≃ᵃ[k] P₁) where
  body: refl k P₁
  mul e e' := e'.trans e
  inv := symm
  mul_assoc _ _ _ := trans_assoc _ _ _
  one_mul := trans_refl
  mul_one := refl_trans
  inv_mul_cancel := self_trans_symm

中文:
实例 group
  签名: : Group (P₁ ≃ᵃ[k] P₁) where
  定义体: refl k P₁
  mul e e' := e'.trans e
  inv := symm
  mul_assoc _ _ _ := trans_assoc _ _ _
  one_mul := trans_refl
  mul_one := refl_trans
  inv_mul_cancel := self_trans_symm
-/
instance group : Group (P₁ ≃ᵃ[k] P₁) where
  one := refl k P₁
  mul e e' := e'.trans e
  inv := symm
  mul_assoc _ _ _ := trans_assoc _ _ _
  one_mul := trans_refl
  mul_one := refl_trans
  inv_mul_cancel := self_trans_symm

/--
theorem `one_def` / 定理 `one_def`

English:
theorem one_def
  statement: (1 : P₁ ≃ᵃ[k] P₁) = refl k P₁
  proof: rfl

@[simp]

中文:
定理 one_def
  结论: (1 : P₁ ≃ᵃ[k] P₁) = refl k P₁
  证明: rfl

@[simp]

Depends on / 依赖: Fin.succAbove_last, _succAbove, finSuccEquiv, succAbove_last
-/
theorem one_def : (1 : P₁ ≃ᵃ[k] P₁) = refl k P₁ :=
  rfl

@[simp]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ⇑(1 : P₁ ≃ᵃ[k] P₁) = id
  proof: rfl

中文:
定理 coe_one
  结论: ⇑(1 : P₁ ≃ᵃ[k] P₁) = id
  证明: rfl
-/
theorem coe_one : ⇑(1 : P₁ ≃ᵃ[k] P₁) = id :=
  rfl

/--
theorem `mul_def` / 定理 `mul_def`

English:
theorem mul_def
  given: (e e' : P₁ ≃ᵃ[k] P₁)
  statement: e * e' = e'.trans e
  proof: rfl

@[simp]

中文:
定理 mul_def
  条件: (e e' : P₁ ≃ᵃ[k] P₁)
  结论: e * e' = e'.trans e
  证明: rfl

@[simp]

Depends on / 依赖: Fin.exists_castSucc_eq, Fin.exists_succAbove_eq, exists_castSucc_eq, exists_succAbove_eq
-/
theorem mul_def (e e' : P₁ ≃ᵃ[k] P₁) : e * e' = e'.trans e :=
  rfl

@[simp]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (e e' : P₁ ≃ᵃ[k] P₁)
  statement: ⇑(e * e') = e ∘ e'
  proof: rfl

中文:
定理 coe_mul
  条件: (e e' : P₁ ≃ᵃ[k] P₁)
  结论: ⇑(e * e') = e ∘ e'
  证明: rfl
-/
theorem coe_mul (e e' : P₁ ≃ᵃ[k] P₁) : ⇑(e * e') = e ∘ e' :=
  rfl

/--
theorem `inv_def` / 定理 `inv_def`

English:
theorem inv_def
  given: (e : P₁ ≃ᵃ[k] P₁)
  statement: e⁻¹ = e.symm
  proof: rfl

中文:
定理 inv_def
  条件: (e : P₁ ≃ᵃ[k] P₁)
  结论: e⁻¹ = e.symm
  证明: rfl
-/
theorem inv_def (e : P₁ ≃ᵃ[k] P₁) : e⁻¹ = e.symm :=
  rfl

/-- `AffineEquiv.linear` on automorphisms is a `MonoidHom`. -/
@[simps]
/--
Definition of `linearHom` / `linearHom` 的定义

English:
definition linearHom
  signature: : (P₁ ≃ᵃ[k] P₁) ->* V₁ ≃ₗ[k] V₁ where
  body: linear
  map_one' := rfl
  map_mul' _ _ := rfl

中文:
定义 linearHom
  签名: : (P₁ ≃ᵃ[k] P₁) ->* V₁ ≃ₗ[k] V₁ where
  定义体: linear
  map_one' := rfl
  map_mul' _ _ := rfl

Depends on / 依赖: linear
-/
def linearHom : (P₁ ≃ᵃ[k] P₁) ->* V₁ ≃ₗ[k] V₁ where
  toFun := linear
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The group of `AffineEquiv`s are equivalent to the group of units of `AffineMap`.

This is the affine version of `LinearMap.GeneralLinearGroup.generalLinearEquiv`. -/
@[simps -isSimp]
/--
Definition of `equivUnitsAffineMap` / `equivUnitsAffineMap` 的定义

English:
definition equivUnitsAffineMap
  signature: : (P₁ ≃ᵃ[k] P₁) ≃* (P₁ ->ᵃ[k] P₁)ˣ where
  body: { val := e, inv := e.symm,
      val_inv := congr_arg toAffineMap e.symm_trans_self
      inv_val := congr_arg toAffineMap e.self_trans_symm }
  invFun u :=
    { toFun := (u : P₁ ->ᵃ[k] P₁)
      invFun := (↑u⁻¹ : P₁ ->ᵃ[k] P₁)
      left_inv := AffineMap.congr_fun u.inv_mul
      right_inv := Affi

中文:
定义 equivUnitsAffineMap
  签名: : (P₁ ≃ᵃ[k] P₁) ≃* (P₁ ->ᵃ[k] P₁)ˣ where
  定义体: { val := e, inv := e.symm,
      val_inv := congr_arg toAffineMap e.symm_trans_self
      inv_val := congr_arg toAffineMap e.self_trans_symm }
  invFun u :=
    { toFun := (u : P₁ ->ᵃ[k] P₁)
      invFun := (↑u⁻¹ : P₁ ->ᵃ[k] P₁)
      left_inv := AffineMap.congr_fun u.inv_mul
      right_inv := Affi

Depends on / 依赖: AffineMap, AffineMap.congr_fun, AffineMap.linearHom, GeneralLinearGroup, LinearMap, LinearMap.GeneralLinearGroup.generalLinearEquiv, Units.map, congr_arg, congr_fun, e.self_trans_symm, e.symm, e.symm_trans_self, generalLinearEquiv, invFun, inv_mul, inv_val, left_inv, linear, linearHom, map_mul
-/
def equivUnitsAffineMap : (P₁ ≃ᵃ[k] P₁) ≃* (P₁ ->ᵃ[k] P₁)ˣ where
  toFun e :=
    { val := e, inv := e.symm,
      val_inv := congr_arg toAffineMap e.symm_trans_self
      inv_val := congr_arg toAffineMap e.self_trans_symm }
  invFun u :=
    { toFun := (u : P₁ ->ᵃ[k] P₁)
      invFun := (↑u⁻¹ : P₁ ->ᵃ[k] P₁)
      left_inv := AffineMap.congr_fun u.inv_mul
      right_inv := AffineMap.congr_fun u.mul_inv
      linear :=
LinearMap.GeneralLinearGroup.generalLinearEquiv _ _ Units.map AffineMap.linearHom u
      map_vadd' := fun _ _ => (u : P₁ ->ᵃ[k] P₁).map_vadd _ _ }
  map_mul' _ _ := rfl

section

variable (e₁ : P₁ ≃ᵃ[k] P₂) (e₂ : P₃ ≃ᵃ[k] P₄)

/-- Product of two affine equivalences. The map comes from `Equiv.prodCongr` -/
@[simps linear]
/--
Definition of `prodCongr` / `prodCongr` 的定义

English:
definition prodCongr
  signature: : P₁ × P₃ ≃ᵃ[k] P₂ × P₄ where
  body: Equiv.prodCongr e₁ e₂
  linear := e₁.linear.prodCongr e₂.linear
  map_vadd' := by simp

@[simp]

中文:
定义 prodCongr
  签名: : P₁ × P₃ ≃ᵃ[k] P₂ × P₄ where
  定义体: Equiv.prodCongr e₁ e₂
  linear := e₁.linear.prodCongr e₂.linear
  map_vadd' := by simp

@[simp]

Depends on / 依赖: Equiv.prodCongr, prodCongr
-/
def prodCongr : P₁ × P₃ ≃ᵃ[k] P₂ × P₄ where
  __ := Equiv.prodCongr e₁ e₂
  linear := e₁.linear.prodCongr e₂.linear
  map_vadd' := by simp

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

@[simp, norm_cast]

中文:
定理 prodCongr_apply
  条件: (p : P₁ × P₃)
  结论: e₁.prodCongr e₂ p = (e₁ p.1, e₂ p.2)
  证明: rfl

@[simp, norm_cast]
-/
theorem prodCongr_apply (p : P₁ × P₃) : e₁.prodCongr e₂ p = (e₁ p.1, e₂ p.2) :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_prodCongr` / 定理 `coe_prodCongr`

English:
theorem coe_prodCongr
  proof: rfl

中文:
定理 coe_prodCongr
  证明: rfl
-/
theorem coe_prodCongr :
    (e₁.prodCongr e₂ : P₁ × P₃ ->ᵃ[k] P₂ × P₄) = (e₁ : P₁ ->ᵃ[k] P₂).prodMap (e₂ : P₃ ->ᵃ[k] P₄) :=
  rfl

end

section

variable (k P₁ P₂ P₃)

/-- Product of affine spaces is commutative up to affine isomorphism. -/
@[simps! apply linear]
/--
Definition of `prodComm` / `prodComm` 的定义

English:
definition prodComm
  signature: : P₁ × P₂ ≃ᵃ[k] P₂ × P₁ where
  body: Equiv.prodComm P₁ P₂
  linear := LinearEquiv.prodComm k V₁ V₂
  map_vadd' := by simp

@[simp]

中文:
定义 prodComm
  签名: : P₁ × P₂ ≃ᵃ[k] P₂ × P₁ where
  定义体: Equiv.prodComm P₁ P₂
  linear := LinearEquiv.prodComm k V₁ V₂
  map_vadd' := by simp

@[simp]

Depends on / 依赖: Equiv.prodComm, prodComm
-/
def prodComm : P₁ × P₂ ≃ᵃ[k] P₂ × P₁ where
  __ := Equiv.prodComm P₁ P₂
  linear := LinearEquiv.prodComm k V₁ V₂
  map_vadd' := by simp

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

/-- Product of affine spaces is associative up to affine isomorphism. -/
@[simps! apply symm_apply linear]
/--
Definition of `prodAssoc` / `prodAssoc` 的定义

English:
definition prodAssoc
  signature: : (P₁ × P₂) × P₃ ≃ᵃ[k] P₁ × (P₂ × P₃) where
  body: Equiv.prodAssoc P₁ P₂ P₃
  linear := LinearEquiv.prodAssoc k V₁ V₂ V₃
  map_vadd' := by simp

中文:
定义 prodAssoc
  签名: : (P₁ × P₂) × P₃ ≃ᵃ[k] P₁ × (P₂ × P₃) where
  定义体: Equiv.prodAssoc P₁ P₂ P₃
  linear := LinearEquiv.prodAssoc k V₁ V₂ V₃
  map_vadd' := by simp

Depends on / 依赖: Equiv.prodAssoc, prodAssoc
-/
def prodAssoc : (P₁ × P₂) × P₃ ≃ᵃ[k] P₁ × (P₂ × P₃) where
  __ := Equiv.prodAssoc P₁ P₂ P₃
  linear := LinearEquiv.prodAssoc k V₁ V₂ V₃
  map_vadd' := by simp

end

variable (k)

/-- The map `v ↦ v +ᵥ b` as an affine equivalence between a module `V` and an affine space `P` with
tangent space `V`. -/
@[simps! linear apply symm_apply]
/--
Definition of `vaddConst` / `vaddConst` 的定义

English:
definition vaddConst
  signature: (b : P₁)
  body: Equiv.vaddConst b
  linear := LinearEquiv.refl _ _
  map_vadd' _ _ := add_vadd _ _ _

中文:
定义 vaddConst
  签名: (b : P₁)
  定义体: Equiv.vaddConst b
  linear := LinearEquiv.refl _ _
  map_vadd' _ _ := add_vadd _ _ _

Depends on / 依赖: Equiv.vaddConst, vaddConst
-/
def vaddConst (b : P₁) : V₁ ≃ᵃ[k] P₁ where
  toEquiv := Equiv.vaddConst b
  linear := LinearEquiv.refl _ _
  map_vadd' _ _ := add_vadd _ _ _

/-- `p' ↦ p -ᵥ p'` as an equivalence. -/
@[simps! linear apply symm_apply]
/--
Definition of `constVSub` / `constVSub` 的定义

English:
definition constVSub
  signature: (p : P₁)
  body: Equiv.constVSub p
  linear := LinearEquiv.neg k
  map_vadd' p' v := by simp [vsub_vadd_eq_vsub_sub, neg_add_eq_sub]

@[simp]

中文:
定义 constVSub
  签名: (p : P₁)
  定义体: Equiv.constVSub p
  linear := LinearEquiv.neg k
  map_vadd' p' v := by simp [vsub_vadd_eq_vsub_sub, neg_add_eq_sub]

@[simp]

Depends on / 依赖: Equiv.constVSub, constVSub
-/
def constVSub (p : P₁) : P₁ ≃ᵃ[k] V₁ where
  toEquiv := Equiv.constVSub p
  linear := LinearEquiv.neg k
  map_vadd' p' v := by simp [vsub_vadd_eq_vsub_sub, neg_add_eq_sub]

@[simp]
/--
theorem `coe_constVSub` / 定理 `coe_constVSub`

English:
theorem coe_constVSub
  given: (p : P₁)
  statement: ⇑(constVSub k p) = (p -ᵥ ·)
  proof: rfl

@[simp]

中文:
定理 coe_constVSub
  条件: (p : P₁)
  结论: ⇑(constVSub k p) = (p -ᵥ ·)
  证明: rfl

@[simp]
-/
theorem coe_constVSub (p : P₁) : ⇑(constVSub k p) = (p -ᵥ ·) :=
  rfl

@[simp]
/--
theorem `coe_constVSub_symm` / 定理 `coe_constVSub_symm`

English:
theorem coe_constVSub_symm
  given: (p : P₁)
  statement: ⇑(constVSub k p).symm = fun v : V₁ => -v +ᵥ p
  proof: rfl

中文:
定理 coe_constVSub_symm
  条件: (p : P₁)
  结论: ⇑(constVSub k p).symm = fun v : V₁ => -v +ᵥ p
  证明: rfl
-/
theorem coe_constVSub_symm (p : P₁) : ⇑(constVSub k p).symm = fun v : V₁ => -v +ᵥ p :=
  rfl

variable (P₁)

/-- The map `p ↦ v +ᵥ p` as an affine automorphism of an affine space.

Note that there is no need for an `AffineMap.constVAdd` as it is always an equivalence.
This is roughly to `DistribMulAction.toLinearEquiv` as `+ᵥ` is to `•`. -/
@[simps! apply linear]
/--
Definition of `constVAdd` / `constVAdd` 的定义

English:
definition constVAdd
  signature: (v : V₁)
  body: Equiv.constVAdd P₁ v
  linear := LinearEquiv.refl _ _
  map_vadd' _ _ := vadd_comm _ _ _

@[simp]

中文:
定义 constVAdd
  签名: (v : V₁)
  定义体: Equiv.constVAdd P₁ v
  linear := LinearEquiv.refl _ _
  map_vadd' _ _ := vadd_comm _ _ _

@[simp]

Depends on / 依赖: Equiv.constVAdd, constVAdd
-/
def constVAdd (v : V₁) : P₁ ≃ᵃ[k] P₁ where
  toEquiv := Equiv.constVAdd P₁ v
  linear := LinearEquiv.refl _ _
  map_vadd' _ _ := vadd_comm _ _ _

@[simp]
/--
theorem `constVAdd_zero` / 定理 `constVAdd_zero`

English:
theorem constVAdd_zero
  statement: constVAdd k P₁ 0 = AffineEquiv.refl _ _
  proof: ext zero_vadd _

@[simp]

中文:
定理 constVAdd_zero
  结论: constVAdd k P₁ 0 = AffineEquiv.refl _ _
  证明: ext zero_vadd _

@[simp]

Depends on / 依赖: zero_vadd
-/
theorem constVAdd_zero : constVAdd k P₁ 0 = AffineEquiv.refl _ _ :=
ext zero_vadd _

@[simp]
/--
theorem `constVAdd_add` / 定理 `constVAdd_add`

English:
theorem constVAdd_add
  given: (v w : V₁)
  proof: ext add_vadd _ _

@[simp]

中文:
定理 constVAdd_add
  条件: (v w : V₁)
  证明: ext add_vadd _ _

@[simp]

Depends on / 依赖: add_vadd
-/
theorem constVAdd_add (v w : V₁) :
    constVAdd k P₁ (v + w) = (constVAdd k P₁ w).trans (constVAdd k P₁ v) :=
ext add_vadd _ _

@[simp]
/--
theorem `constVAdd_symm` / 定理 `constVAdd_symm`

English:
theorem constVAdd_symm
  given: (v : V₁)
  statement: (constVAdd k P₁ v).symm = constVAdd k P₁ (-v)
  proof: ext fun _ => rfl

中文:
定理 constVAdd_symm
  条件: (v : V₁)
  结论: (constVAdd k P₁ v).symm = constVAdd k P₁ (-v)
  证明: ext fun _ => rfl
-/
theorem constVAdd_symm (v : V₁) : (constVAdd k P₁ v).symm = constVAdd k P₁ (-v) :=
  ext fun _ => rfl

/-- A more bundled version of `AffineEquiv.constVAdd`. -/
@[simps]
/--
Definition of `constVAddHom` / `constVAddHom` 的定义

English:
definition constVAddHom
  signature: : Multiplicative V₁ ->* P₁ ≃ᵃ[k] P₁ where
  body: constVAdd k P₁ v.toAdd
  map_one' := constVAdd_zero _ _
  map_mul' := constVAdd_add _ P₁

中文:
定义 constVAddHom
  签名: : Multiplicative V₁ ->* P₁ ≃ᵃ[k] P₁ where
  定义体: constVAdd k P₁ v.toAdd
  map_one' := constVAdd_zero _ _
  map_mul' := constVAdd_add _ P₁

Depends on / 依赖: constVAdd, v.toAdd
-/
def constVAddHom : Multiplicative V₁ ->* P₁ ≃ᵃ[k] P₁ where
  toFun v := constVAdd k P₁ v.toAdd
  map_one' := constVAdd_zero _ _
  map_mul' := constVAdd_add _ P₁

/--
theorem `constVAdd_nsmul` / 定理 `constVAdd_nsmul`

English:
theorem constVAdd_nsmul
  given: (n : Nat) (v : V₁)
  statement: constVAdd k P₁ (n • v) = constVAdd k P₁ v ^ n
  proof: (constVAddHom k P₁).map_pow _ _

中文:
定理 constVAdd_nsmul
  条件: (n : 自然数) (v : V₁)
  结论: constVAdd k P₁ (n • v) = constVAdd k P₁ v ^ n
  证明: (constVAddHom k P₁).map_pow _ _

Depends on / 依赖: constVAddHom, map_pow
-/
theorem constVAdd_nsmul (n : Nat) (v : V₁) : constVAdd k P₁ (n • v) = constVAdd k P₁ v ^ n :=
  (constVAddHom k P₁).map_pow _ _

/--
theorem `constVAdd_zsmul` / 定理 `constVAdd_zsmul`

English:
theorem constVAdd_zsmul
  given: (z : Int) (v : V₁)
  statement: constVAdd k P₁ (z • v) = constVAdd k P₁ v ^ z
  proof: (constVAddHom k P₁).map_zpow _ _

中文:
定理 constVAdd_zsmul
  条件: (z : 整数) (v : V₁)
  结论: constVAdd k P₁ (z • v) = constVAdd k P₁ v ^ z
  证明: (constVAddHom k P₁).map_zpow _ _

Depends on / 依赖: constVAddHom, map_zpow
-/
theorem constVAdd_zsmul (z : Int) (v : V₁) : constVAdd k P₁ (z • v) = constVAdd k P₁ v ^ z :=
  (constVAddHom k P₁).map_zpow _ _

section Homothety

variable {R V P : Type*} [CommRing R] [AddCommGroup V] [Module R V] [AffineSpace V P]

/--
Definition of `homothetyUnitsMulHom` / `homothetyUnitsMulHom` 的定义

English:
definition homothetyUnitsMulHom
  signature: (p : P)
  body: equivUnitsAffineMap.symm.toMonoidHom.comp Units.map (AffineMap.homothetyHom p)

@[simp]

中文:
定义 homothetyUnitsMulHom
  签名: (p : P)
  定义体: equivUnitsAffineMap.symm.toMonoidHom.comp Units.map (AffineMap.homothetyHom p)

@[simp]

Depends on / 依赖: AffineMap, AffineMap.homothetyHom, Units.map, equivUnitsAffineMap, equivUnitsAffineMap.symm.toMonoidHom.comp, homothetyHom, toMonoidHom
-/
def homothetyUnitsMulHom (p : P) : Rˣ ->* P ≃ᵃ[R] P :=
equivUnitsAffineMap.symm.toMonoidHom.comp Units.map (AffineMap.homothetyHom p)

@[simp]
/--
theorem `coe_homothetyUnitsMulHom_apply` / 定理 `coe_homothetyUnitsMulHom_apply`

English:
theorem coe_homothetyUnitsMulHom_apply
  given: (p : P) (t : Rˣ)
  proof: rfl

@[simp]

中文:
定理 coe_homothetyUnitsMulHom_apply
  条件: (p : P) (t : Rˣ)
  证明: rfl

@[simp]
-/
theorem coe_homothetyUnitsMulHom_apply (p : P) (t : Rˣ) :
    (homothetyUnitsMulHom p t : P -> P) = AffineMap.homothety p (t : R) :=
  rfl

@[simp]
/--
theorem `coe_homothetyUnitsMulHom_apply_symm` / 定理 `coe_homothetyUnitsMulHom_apply_symm`

English:
theorem coe_homothetyUnitsMulHom_apply_symm
  given: (p : P) (t : Rˣ)
  proof: rfl

@[simp]

中文:
定理 coe_homothetyUnitsMulHom_apply_symm
  条件: (p : P) (t : Rˣ)
  证明: rfl

@[simp]
-/
theorem coe_homothetyUnitsMulHom_apply_symm (p : P) (t : Rˣ) :
    ((homothetyUnitsMulHom p t).symm : P -> P) = AffineMap.homothety p (↑t⁻¹ : R) :=
  rfl

@[simp]
/--
theorem `coe_homothetyUnitsMulHom_eq_homothetyHom_coe` / 定理 `coe_homothetyUnitsMulHom_eq_homothetyHom_coe`

English:
theorem coe_homothetyUnitsMulHom_eq_homothetyHom_coe
  given: (p : P)
  proof: funext fun _ => rfl

中文:
定理 coe_homothetyUnitsMulHom_eq_homothetyHom_coe
  条件: (p : P)
  证明: funext fun _ => rfl
-/
theorem coe_homothetyUnitsMulHom_eq_homothetyHom_coe (p : P) :
    ((↑) : (P ≃ᵃ[R] P) -> P ->ᵃ[R] P) ∘ homothetyUnitsMulHom p =
      AffineMap.homothetyHom p ∘ ((↑) : Rˣ -> R) :=
  funext fun _ => rfl

end Homothety

variable {P₁}

open Function

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
def pointReflection (x : P₁) : P₁ ≃ᵃ[k] P₁ :=
  (constVSub k x).trans (vaddConst k x)

@[simp]
/--
lemma `coe_pointReflection` / 引理 `coe_pointReflection`

English:
lemma coe_pointReflection
  given: (x y : P₁)
  statement: pointReflection k x y = Equiv.pointReflection x y
  proof: rfl

@[deprecated (since := "2026-06-22")]
alias pointReflection_apply_eq_equivPointReflection_apply := coe_pointReflection

中文:
引理 coe_pointReflection
  条件: (x y : P₁)
  结论: pointReflection k x y = Equiv.pointReflection x y
  证明: rfl

@[deprecated (since := "2026-06-22")]
alias pointReflection_apply_eq_equivPointReflection_apply := coe_pointReflection
-/
lemma coe_pointReflection (x y : P₁) : pointReflection k x y = Equiv.pointReflection x y :=
  rfl

@[deprecated (since := "2026-06-22")]
alias pointReflection_apply_eq_equivPointReflection_apply := coe_pointReflection

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
  proof: toEquiv_injective Equiv.pointReflection_symm x

@[simp]

中文:
定理 pointReflection_symm
  条件: (x : P₁)
  结论: (pointReflection k x).symm = pointReflection k x
  证明: toEquiv_injective Equiv.pointReflection_symm x

@[simp]

Depends on / 依赖: Equiv.pointReflection_symm, pointReflection_symm, toEquiv_injective
-/
theorem pointReflection_symm (x : P₁) : (pointReflection k x).symm = pointReflection k x :=
toEquiv_injective Equiv.pointReflection_symm x

@[simp]
/--
theorem `toEquiv_pointReflection` / 定理 `toEquiv_pointReflection`

English:
theorem toEquiv_pointReflection
  given: (x : P₁)
  proof: rfl

中文:
定理 toEquiv_pointReflection
  条件: (x : P₁)
  证明: rfl
-/
theorem toEquiv_pointReflection (x : P₁) :
    (pointReflection k x).toEquiv = Equiv.pointReflection x :=
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
  结论: Involutive (pointReflection k x : P₁ -> P₁)
  证明: Equiv.pointReflection_involutive x

Depends on / 依赖: Equiv.pointReflection_involutive, pointReflection_involutive
-/
theorem pointReflection_involutive (x : P₁) : Involutive (pointReflection k x : P₁ -> P₁) :=
  Equiv.pointReflection_involutive x

/--
theorem `pointReflection_fixed_iff_of_injective_two_nsmul` / 定理 `pointReflection_fixed_iff_of_injective_two_nsmul`

English:
theorem pointReflection_fixed_iff_of_injective_two_nsmul
  statement: {x y : P₁}
  proof: Equiv.pointReflection_fixed_iff_of_injective_two_nsmul h

中文:
定理 pointReflection_fixed_iff_of_injective_two_nsmul
  结论: {x y : P₁}
  证明: Equiv.pointReflection_fixed_iff_of_injective_two_nsmul h

Depends on / 依赖: Equiv.pointReflection_fixed_iff_of_injective_two_nsmul, pointReflection_fixed_iff_of_injective_two_nsmul
-/
theorem pointReflection_fixed_iff_of_injective_two_nsmul {x y : P₁}
    (h : Injective (2 • · : V₁ -> V₁)) : pointReflection k x y = y ↔ y = x :=
  Equiv.pointReflection_fixed_iff_of_injective_two_nsmul h

/--
theorem `injective_pointReflection_left_of_injective_two_nsmul` / 定理 `injective_pointReflection_left_of_injective_two_nsmul`

English:
theorem injective_pointReflection_left_of_injective_two_nsmul
  proof: Equiv.injective_pointReflection_left_of_injective_two_nsmul h y

中文:
定理 injective_pointReflection_left_of_injective_two_nsmul
  证明: Equiv.injective_pointReflection_left_of_injective_two_nsmul h y

Depends on / 依赖: Equiv.injective_pointReflection_left_of_injective_two_nsmul, injective_pointReflection_left_of_injective_two_nsmul
-/
theorem injective_pointReflection_left_of_injective_two_nsmul
    (h : Injective (2 • · : V₁ -> V₁)) (y : P₁) :
    Injective fun x : P₁ => pointReflection k x y :=
  Equiv.injective_pointReflection_left_of_injective_two_nsmul h y

/--
theorem `injective_pointReflection_left_of_module` / 定理 `injective_pointReflection_left_of_module`

English:
theorem injective_pointReflection_left_of_module
  given: [Invertible (2 : k)]
  proof: injective_pointReflection_left_of_injective_two_nsmul k fun x y h => by
    dsimp at h
    rwa [two_nsmul, two_nsmul, ← two_smul k x, ← two_smul k y,
      (isUnit_of_invertible (2 : k)).smul_left_cancel] at h

中文:
定理 injective_pointReflection_left_of_module
  条件: [Invertible (2 : k)]
  证明: injective_pointReflection_left_of_injective_two_nsmul k fun x y h => by
    dsimp at h
    rwa [two_nsmul, two_nsmul, ← two_smul k x, ← two_smul k y,
      (isUnit_of_invertible (2 : k)).smul_left_cancel] at h

Depends on / 依赖: injective_pointReflection_left_of_injective_two_nsmul, isUnit_of_invertible, smul_left_cancel, two_nsmul, two_smul
-/
theorem injective_pointReflection_left_of_module [Invertible (2 : k)] :
    forall y, Injective fun x : P₁ => pointReflection k x y :=
  injective_pointReflection_left_of_injective_two_nsmul k fun x y h => by
    dsimp at h
    rwa [two_nsmul, two_nsmul, ← two_smul k x, ← two_smul k y,
      (isUnit_of_invertible (2 : k)).smul_left_cancel] at h

/--
theorem `pointReflection_fixed_iff_of_module` / 定理 `pointReflection_fixed_iff_of_module`

English:
theorem pointReflection_fixed_iff_of_module
  given: [Invertible (2 : k)] {x y : P₁}
  proof: ((injective_pointReflection_left_of_module k y).eq_iff' (pointReflection_self k y)).trans eq_comm

中文:
定理 pointReflection_fixed_iff_of_module
  条件: [Invertible (2 : k)] {x y : P₁}
  证明: ((injective_pointReflection_left_of_module k y).eq_iff' (pointReflection_self k y)).trans eq_comm

Depends on / 依赖: eq_comm, eq_iff, injective_pointReflection_left_of_module, pointReflection_self
-/
theorem pointReflection_fixed_iff_of_module [Invertible (2 : k)] {x y : P₁} :
    pointReflection k x y = y ↔ y = x :=
  ((injective_pointReflection_left_of_module k y).eq_iff' (pointReflection_self k y)).trans eq_comm

end AffineEquiv

namespace LinearEquiv

/--
Definition of `toAffineEquiv` / `toAffineEquiv` 的定义

English:
definition toAffineEquiv
  signature: (e : V₁ ≃ₗ[k] V₂)
  body: e.toEquiv
  linear := e
  map_vadd' p v := e.map_add v p

@[simp]

中文:
定义 toAffineEquiv
  签名: (e : V₁ ≃ₗ[k] V₂)
  定义体: e.toEquiv
  linear := e
  map_vadd' p v := e.map_add v p

@[simp]

Depends on / 依赖: e.toEquiv, toEquiv
-/
def toAffineEquiv (e : V₁ ≃ₗ[k] V₂) : V₁ ≃ᵃ[k] V₂ where
  toEquiv := e.toEquiv
  linear := e
  map_vadd' p v := e.map_add v p

@[simp]
/--
theorem `coe_toAffineEquiv` / 定理 `coe_toAffineEquiv`

English:
theorem coe_toAffineEquiv
  given: (e : V₁ ≃ₗ[k] V₂)
  statement: ⇑e.toAffineEquiv = e
  proof: rfl

中文:
定理 coe_toAffineEquiv
  条件: (e : V₁ ≃ₗ[k] V₂)
  结论: ⇑e.toAffineEquiv = e
  证明: rfl
-/
theorem coe_toAffineEquiv (e : V₁ ≃ₗ[k] V₂) : ⇑e.toAffineEquiv = e :=
  rfl

end LinearEquiv

namespace AffineEquiv

section ofLinearEquiv

variable {k V P : Type*}
variable [Ring k] [AddCommGroup V] [Module k V] [AddTorsor V P]

/--
Definition of `ofLinearEquiv` / `ofLinearEquiv` 的定义

English:
definition ofLinearEquiv
  signature: (A : V ≃ₗ[k] V) (p₀ p₁ : P)
  body: (vaddConst k p₀).symm.trans (A.toAffineEquiv.trans (vaddConst k p₁))

@[simp]

中文:
定义 ofLinearEquiv
  签名: (A : V ≃ₗ[k] V) (p₀ p₁ : P)
  定义体: (vaddConst k p₀).symm.trans (A.toAffineEquiv.trans (vaddConst k p₁))

@[simp]

Depends on / 依赖: A.toAffineEquiv.trans, symm.trans, toAffineEquiv, vaddConst
-/
def ofLinearEquiv (A : V ≃ₗ[k] V) (p₀ p₁ : P) : P ≃ᵃ[k] P :=
  (vaddConst k p₀).symm.trans (A.toAffineEquiv.trans (vaddConst k p₁))

@[simp]
/--
theorem `ofLinearEquiv_apply` / 定理 `ofLinearEquiv_apply`

English:
theorem ofLinearEquiv_apply
  given: (A : V ≃ₗ[k] V) (p₀ p₁ : P) (x : P)
  proof: rfl

@[simp]

中文:
定理 ofLinearEquiv_apply
  条件: (A : V ≃ₗ[k] V) (p₀ p₁ : P) (x : P)
  证明: rfl

@[simp]
-/
theorem ofLinearEquiv_apply (A : V ≃ₗ[k] V) (p₀ p₁ : P) (x : P) :
    ofLinearEquiv A p₀ p₁ x = A (x -ᵥ p₀) +ᵥ p₁ :=
  rfl

@[simp]
/--
theorem `linear_ofLinearEquiv` / 定理 `linear_ofLinearEquiv`

English:
theorem linear_ofLinearEquiv
  given: (A : V ≃ₗ[k] V) (p₀ p₁ : P)
  proof: rfl

@[simp]

中文:
定理 linear_ofLinearEquiv
  条件: (A : V ≃ₗ[k] V) (p₀ p₁ : P)
  证明: rfl

@[simp]
-/
theorem linear_ofLinearEquiv (A : V ≃ₗ[k] V) (p₀ p₁ : P) :
    (ofLinearEquiv A p₀ p₁).linear = A :=
  rfl

@[simp]
/--
theorem `ofLinearEquiv_refl` / 定理 `ofLinearEquiv_refl`

English:
theorem ofLinearEquiv_refl
  given: (p : P)
  proof: by
  ext x
  simp [ofLinearEquiv_apply]

@[simp]

中文:
定理 ofLinearEquiv_refl
  条件: (p : P)
  证明: by
  ext x
  simp [ofLinearEquiv_apply]

@[simp]

Depends on / 依赖: ofLinearEquiv_apply
-/
theorem ofLinearEquiv_refl (p : P) :
    ofLinearEquiv (.refl k V) p p = .refl k P := by
  ext x
  simp [ofLinearEquiv_apply]

@[simp]
/--
theorem `ofLinearEquiv_trans_ofLinearEquiv` / 定理 `ofLinearEquiv_trans_ofLinearEquiv`

English:
theorem ofLinearEquiv_trans_ofLinearEquiv
  given: (A B : V ≃ₗ[k] V) (p₀ p₁ p₂ : P)
  proof: by
  ext x
  simp

中文:
定理 ofLinearEquiv_trans_ofLinearEquiv
  条件: (A B : V ≃ₗ[k] V) (p₀ p₁ p₂ : P)
  证明: by
  ext x
  simp
-/
theorem ofLinearEquiv_trans_ofLinearEquiv (A B : V ≃ₗ[k] V) (p₀ p₁ p₂ : P) :
    (ofLinearEquiv A p₀ p₁).trans (ofLinearEquiv B p₁ p₂) =
      ofLinearEquiv (A.trans B) p₀ p₂ := by
  ext x
  simp

end ofLinearEquiv

section arrowCongrEquiv

variable (e₁ : P₁ ≃ᵃ[k] P₂) (e₂ : P₃ ≃ᵃ[k] P₄)

/--
Definition of `arrowCongrEquiv` / `arrowCongrEquiv` 的定义

English:
definition arrowCongrEquiv
  signature: : (P₁ ->ᵃ[k] P₃) ≃ (P₂ ->ᵃ[k] P₄) where
  body: e₂.toAffineMap.comp f.comp e₁.symm.toAffineMap
invFun f := e₂.symm.toAffineMap.comp f.comp e₁.toAffineMap
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

@[simp]

中文:
定义 arrowCongrEquiv
  签名: : (P₁ ->ᵃ[k] P₃) ≃ (P₂ ->ᵃ[k] P₄) where
  定义体: e₂.toAffineMap.comp f.comp e₁.symm.toAffineMap
invFun f := e₂.symm.toAffineMap.comp f.comp e₁.toAffineMap
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

@[simp]

Depends on / 依赖: f.comp, symm.toAffineMap, toAffineMap, toAffineMap.comp
-/
def arrowCongrEquiv : (P₁ ->ᵃ[k] P₃) ≃ (P₂ ->ᵃ[k] P₄) where
toFun f := e₂.toAffineMap.comp f.comp e₁.symm.toAffineMap
invFun f := e₂.symm.toAffineMap.comp f.comp e₁.toAffineMap
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

@[simp]
/--
theorem `arrowCongrEquiv_apply` / 定理 `arrowCongrEquiv_apply`

English:
theorem arrowCongrEquiv_apply
  given: (f : P₁ ->ᵃ[k] P₃) (x : P₂)
  proof: rfl

@[simp]

中文:
定理 arrowCongrEquiv_apply
  条件: (f : P₁ ->ᵃ[k] P₃) (x : P₂)
  证明: rfl

@[simp]
-/
theorem arrowCongrEquiv_apply (f : P₁ ->ᵃ[k] P₃) (x : P₂) :
    e₁.arrowCongrEquiv e₂ f x = e₂ (f (e₁.symm x)) :=
  rfl

@[simp]
/--
theorem `arrowCongrEquiv_symm_apply` / 定理 `arrowCongrEquiv_symm_apply`

English:
theorem arrowCongrEquiv_symm_apply
  given: (f : P₂ ->ᵃ[k] P₄) (x : P₁)
  proof: rfl

中文:
定理 arrowCongrEquiv_symm_apply
  条件: (f : P₂ ->ᵃ[k] P₄) (x : P₁)
  证明: rfl
-/
theorem arrowCongrEquiv_symm_apply (f : P₂ ->ᵃ[k] P₄) (x : P₁) :
    (e₁.arrowCongrEquiv e₂).symm f x = e₂.symm (f (e₁ x)) :=
  rfl

end arrowCongrEquiv

section CommRing

variable {R : Type*} [CommRing R] [Module R V₁] [Module R V₂] [Module R V₃] [Module R V₄]

section arrowCongrₗ

variable (e₁ : P₁ ≃ᵃ[R] P₂) (e₂ : V₃ ≃ₗ[R] V₄)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `arrowCongrₗ` / `arrowCongrₗ` 的定义

English:
definition arrowCongrₗ
  signature: : (P₁ ->ᵃ[R] V₃) ≃ₗ[R] (P₂ ->ᵃ[R] V₄) where
  body: e₁.arrowCongrEquiv e₂.toAffineEquiv
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp]

中文:
定义 arrowCongrₗ
  签名: : (P₁ ->ᵃ[R] V₃) ≃ₗ[R] (P₂ ->ᵃ[R] V₄) where
  定义体: e₁.arrowCongrEquiv e₂.toAffineEquiv
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp]

Depends on / 依赖: arrowCongrEquiv, toAffineEquiv
-/
def arrowCongrₗ : (P₁ ->ᵃ[R] V₃) ≃ₗ[R] (P₂ ->ᵃ[R] V₄) where
  __ := e₁.arrowCongrEquiv e₂.toAffineEquiv
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp]
/--
theorem `arrowCongrₗ_apply` / 定理 `arrowCongrₗ_apply`

English:
theorem arrowCongrₗ_apply
  given: (f : P₁ ->ᵃ[R] V₃) (x : P₂)
  proof: rfl

@[simp]

中文:
定理 arrowCongrₗ_apply
  条件: (f : P₁ ->ᵃ[R] V₃) (x : P₂)
  证明: rfl

@[simp]
-/
theorem arrowCongrₗ_apply (f : P₁ ->ᵃ[R] V₃) (x : P₂) :
    e₁.arrowCongrₗ e₂ f x = e₂ (f (e₁.symm x)) :=
  rfl

@[simp]
/--
theorem `arrowCongrₗ_symm_apply` / 定理 `arrowCongrₗ_symm_apply`

English:
theorem arrowCongrₗ_symm_apply
  given: (f : P₂ ->ᵃ[R] V₄) (x : P₁)
  proof: rfl

中文:
定理 arrowCongrₗ_symm_apply
  条件: (f : P₂ ->ᵃ[R] V₄) (x : P₁)
  证明: rfl
-/
theorem arrowCongrₗ_symm_apply (f : P₂ ->ᵃ[R] V₄) (x : P₁) :
    (e₁.arrowCongrₗ e₂).symm f x = e₂.symm (f (e₁ x)) :=
  rfl

end arrowCongrₗ

section arrowCongr

variable (e₁ : P₁ ≃ᵃ[R] P₂) (e₂ : P₃ ≃ᵃ[R] P₄)

/-- Affine isomorphisms between the domains and codomains of two spaces of affine maps give an
affine isomorphism between the two function spaces.

See also `AffineEquiv.arrowCongrEquiv` and `AffineEquiv.arrowCongrₗ`. -/
@[simps linear]
/--
Definition of `arrowCongr` / `arrowCongr` 的定义

English:
definition arrowCongr
  signature: : (P₁ ->ᵃ[R] P₃) ≃ᵃ[R] (P₂ ->ᵃ[R] P₄) where
  body: e₁.arrowCongrEquiv e₂
  linear := e₁.arrowCongrₗ e₂.linear
  map_vadd' _ _ := by ext; simp

@[simp]

中文:
定义 arrowCongr
  签名: : (P₁ ->ᵃ[R] P₃) ≃ᵃ[R] (P₂ ->ᵃ[R] P₄) where
  定义体: e₁.arrowCongrEquiv e₂
  linear := e₁.arrowCongrₗ e₂.linear
  map_vadd' _ _ := by ext; simp

@[simp]

Depends on / 依赖: arrowCongrEquiv
-/
def arrowCongr : (P₁ ->ᵃ[R] P₃) ≃ᵃ[R] (P₂ ->ᵃ[R] P₄) where
  __ := e₁.arrowCongrEquiv e₂
  linear := e₁.arrowCongrₗ e₂.linear
  map_vadd' _ _ := by ext; simp

@[simp]
/--
theorem `arrowCongr_apply` / 定理 `arrowCongr_apply`

English:
theorem arrowCongr_apply
  given: (f : P₁ ->ᵃ[R] P₃) (x : P₂)
  proof: rfl

@[simp]

中文:
定理 arrowCongr_apply
  条件: (f : P₁ ->ᵃ[R] P₃) (x : P₂)
  证明: rfl

@[simp]
-/
theorem arrowCongr_apply (f : P₁ ->ᵃ[R] P₃) (x : P₂) :
    e₁.arrowCongr e₂ f x = e₂ (f (e₁.symm x)) :=
  rfl

@[simp]
/--
theorem `arrowCongr_symm_apply` / 定理 `arrowCongr_symm_apply`

English:
theorem arrowCongr_symm_apply
  given: (f : P₂ ->ᵃ[R] P₄) (x : P₁)
  proof: rfl

中文:
定理 arrowCongr_symm_apply
  条件: (f : P₂ ->ᵃ[R] P₄) (x : P₁)
  证明: rfl
-/
theorem arrowCongr_symm_apply (f : P₂ ->ᵃ[R] P₄) (x : P₁) :
    (e₁.arrowCongr e₂).symm f x = e₂.symm (f (e₁ x)) :=
  rfl

end arrowCongr

end CommRing

section congrLeft

variable (R W : Type*) [Ring R] [AddCommGroup W] [Module k W] [Module R W] [SMulCommClass k R W]
  (e : P₁ ≃ᵃ[k] P₂)

/--
Definition of `congrLeftₗ` / `congrLeftₗ` 的定义

English:
definition congrLeftₗ
  signature: : (P₁ ->ᵃ[k] W) ≃ₗ[R] (P₂ ->ᵃ[k] W) where
  body: e.arrowCongrEquiv (.refl k W)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp]

中文:
定义 congrLeftₗ
  签名: : (P₁ ->ᵃ[k] W) ≃ₗ[R] (P₂ ->ᵃ[k] W) where
  定义体: e.arrowCongrEquiv (.refl k W)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp]

Depends on / 依赖: arrowCongrEquiv, e.arrowCongrEquiv
-/
def congrLeftₗ : (P₁ ->ᵃ[k] W) ≃ₗ[R] (P₂ ->ᵃ[k] W) where
  __ := e.arrowCongrEquiv (.refl k W)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp]
/--
theorem `congrLeftₗ_apply` / 定理 `congrLeftₗ_apply`

English:
theorem congrLeftₗ_apply
  given: (f : P₁ ->ᵃ[k] W) (x : P₂)
  statement: e.congrLeftₗ R W f x = f (e.symm x)
  proof: rfl

@[simp]

中文:
定理 congrLeftₗ_apply
  条件: (f : P₁ ->ᵃ[k] W) (x : P₂)
  结论: e.congrLeftₗ R W f x = f (e.symm x)
  证明: rfl

@[simp]
-/
theorem congrLeftₗ_apply (f : P₁ ->ᵃ[k] W) (x : P₂) : e.congrLeftₗ R W f x = f (e.symm x) :=
  rfl

@[simp]
/--
theorem `congrLeftₗ_symm_apply` / 定理 `congrLeftₗ_symm_apply`

English:
theorem congrLeftₗ_symm_apply
  given: (f : P₂ ->ᵃ[k] W) (x : P₁)
  statement: (e.congrLeftₗ R W).symm f x = f (e x)
  proof: rfl

中文:
定理 congrLeftₗ_symm_apply
  条件: (f : P₂ ->ᵃ[k] W) (x : P₁)
  结论: (e.congrLeftₗ R W).symm f x = f (e x)
  证明: rfl
-/
theorem congrLeftₗ_symm_apply (f : P₂ ->ᵃ[k] W) (x : P₁) : (e.congrLeftₗ R W).symm f x = f (e x) :=
  rfl

variable {W} (Q : Type*) [AddTorsor W Q]

/--
Definition of `congrLeft` / `congrLeft` 的定义

English:
definition congrLeft
  signature: : (P₁ ->ᵃ[k] Q) ≃ᵃ[R] (P₂ ->ᵃ[k] Q) where
  body: e.arrowCongrEquiv (.refl k Q)
  linear := e.congrLeftₗ R W
  map_vadd' _ _ := by ext; simp

@[simp]

中文:
定义 congrLeft
  签名: : (P₁ ->ᵃ[k] Q) ≃ᵃ[R] (P₂ ->ᵃ[k] Q) where
  定义体: e.arrowCongrEquiv (.refl k Q)
  linear := e.congrLeftₗ R W
  map_vadd' _ _ := by ext; simp

@[simp]

Depends on / 依赖: arrowCongrEquiv, e.arrowCongrEquiv
-/
def congrLeft : (P₁ ->ᵃ[k] Q) ≃ᵃ[R] (P₂ ->ᵃ[k] Q) where
  __ := e.arrowCongrEquiv (.refl k Q)
  linear := e.congrLeftₗ R W
  map_vadd' _ _ := by ext; simp

@[simp]
/--
theorem `congrLeft_apply` / 定理 `congrLeft_apply`

English:
theorem congrLeft_apply
  given: (f : P₁ ->ᵃ[k] Q) (x : P₂)
  statement: e.congrLeft R Q f x = f (e.symm x)
  proof: rfl

@[simp]

中文:
定理 congrLeft_apply
  条件: (f : P₁ ->ᵃ[k] Q) (x : P₂)
  结论: e.congrLeft R Q f x = f (e.symm x)
  证明: rfl

@[simp]
-/
theorem congrLeft_apply (f : P₁ ->ᵃ[k] Q) (x : P₂) : e.congrLeft R Q f x = f (e.symm x) :=
  rfl

@[simp]
/--
theorem `congrLeft_symm_apply` / 定理 `congrLeft_symm_apply`

English:
theorem congrLeft_symm_apply
  given: (f : P₂ ->ᵃ[k] Q) (x : P₁)
  statement: (e.congrLeft R Q).symm f x = f (e x)
  proof: rfl

中文:
定理 congrLeft_symm_apply
  条件: (f : P₂ ->ᵃ[k] Q) (x : P₁)
  结论: (e.congrLeft R Q).symm f x = f (e x)
  证明: rfl
-/
theorem congrLeft_symm_apply (f : P₂ ->ᵃ[k] Q) (x : P₁) : (e.congrLeft R Q).symm f x = f (e x) :=
  rfl

end congrLeft

end AffineEquiv

namespace AffineMap

open AffineEquiv

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lineMap_vadd` / 定理 `lineMap_vadd`

English:
theorem lineMap_vadd
  given: (v v' : V₁) (p : P₁) (c : k)
  proof: (vaddConst k p).apply_lineMap v v' c

中文:
定理 lineMap_vadd
  条件: (v v' : V₁) (p : P₁) (c : k)
  证明: (vaddConst k p).apply_lineMap v v' c

Depends on / 依赖: apply_lineMap, vaddConst
-/
theorem lineMap_vadd (v v' : V₁) (p : P₁) (c : k) :
    lineMap v v' c +ᵥ p = lineMap (v +ᵥ p) (v' +ᵥ p) c :=
  (vaddConst k p).apply_lineMap v v' c

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lineMap_vsub` / 定理 `lineMap_vsub`

English:
theorem lineMap_vsub
  given: (p₁ p₂ p₃ : P₁) (c : k)
  proof: (vaddConst k p₃).symm.apply_lineMap p₁ p₂ c

中文:
定理 lineMap_vsub
  条件: (p₁ p₂ p₃ : P₁) (c : k)
  证明: (vaddConst k p₃).symm.apply_lineMap p₁ p₂ c

Depends on / 依赖: apply_lineMap, symm.apply_lineMap, vaddConst
-/
theorem lineMap_vsub (p₁ p₂ p₃ : P₁) (c : k) :
    lineMap p₁ p₂ c -ᵥ p₃ = lineMap (p₁ -ᵥ p₃) (p₂ -ᵥ p₃) c :=
  (vaddConst k p₃).symm.apply_lineMap p₁ p₂ c

set_option backward.isDefEq.respectTransparency false in
/--
theorem `vsub_lineMap` / 定理 `vsub_lineMap`

English:
theorem vsub_lineMap
  given: (p₁ p₂ p₃ : P₁) (c : k)
  proof: (constVSub k p₁).apply_lineMap p₂ p₃ c

中文:
定理 vsub_lineMap
  条件: (p₁ p₂ p₃ : P₁) (c : k)
  证明: (constVSub k p₁).apply_lineMap p₂ p₃ c

Depends on / 依赖: apply_lineMap, constVSub
-/
theorem vsub_lineMap (p₁ p₂ p₃ : P₁) (c : k) :
    p₁ -ᵥ lineMap p₂ p₃ c = lineMap (p₁ -ᵥ p₂) (p₁ -ᵥ p₃) c :=
  (constVSub k p₁).apply_lineMap p₂ p₃ c

set_option backward.isDefEq.respectTransparency false in
/--
theorem `vadd_lineMap` / 定理 `vadd_lineMap`

English:
theorem vadd_lineMap
  given: (v : V₁) (p₁ p₂ : P₁) (c : k)
  proof: (constVAdd k P₁ v).apply_lineMap p₁ p₂ c

中文:
定理 vadd_lineMap
  条件: (v : V₁) (p₁ p₂ : P₁) (c : k)
  证明: (constVAdd k P₁ v).apply_lineMap p₁ p₂ c

Depends on / 依赖: apply_lineMap, constVAdd
-/
theorem vadd_lineMap (v : V₁) (p₁ p₂ : P₁) (c : k) :
    v +ᵥ lineMap p₁ p₂ c = lineMap (v +ᵥ p₁) (v +ᵥ p₂) c :=
  (constVAdd k P₁ v).apply_lineMap p₁ p₂ c

variable {R' : Type*} [CommRing R'] [Module R' V₁]

/--
theorem `homothety_neg_one_apply` / 定理 `homothety_neg_one_apply`

English:
theorem homothety_neg_one_apply
  given: (c p : P₁)
  statement: homothety c (-1 : R') p = pointReflection R' c p
  proof: by
  simp [homothety_apply, Equiv.pointReflection_apply]

中文:
定理 homothety_neg_one_apply
  条件: (c p : P₁)
  结论: homothety c (-1 : R') p = pointReflection R' c p
  证明: by
  simp [homothety_apply, Equiv.pointReflection_apply]

Depends on / 依赖: Equiv.pointReflection_apply, homothety_apply, pointReflection_apply
-/
theorem homothety_neg_one_apply (c p : P₁) : homothety c (-1 : R') p = pointReflection R' c p := by
  simp [homothety_apply, Equiv.pointReflection_apply]

end AffineMap
