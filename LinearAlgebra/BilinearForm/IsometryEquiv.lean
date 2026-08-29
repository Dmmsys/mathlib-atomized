/-
Copyright (c) 2025 Sahan Wijetunga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sahan Wijetunga
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Hom
public import Mathlib.LinearAlgebra.BilinearForm.Isometry

/-!
# Isometric equivalences with respect to bilinear forms

In this file, we define isometry equivalences of bilinear spaces as linear equivalences
that respect the associated bilinear forms. This file should be kept in sync with the
corresponding file for quadratic maps, namely
`Mathlib/LinearAlgebra/QuadraticForm/IsometryEquiv.lean`

## Main definitions

* `LinearMap.BilinForm.IsometryEquiv`: `LinearEquiv`s which map between two different bilinear forms
* `LinearMap.BilinForm.Equivalent`: propositional version of the above
-/
@[expose] public section

variable {R M M₁ M₂ M₃ M₄ N : Type*}

namespace LinearMap

namespace BilinForm

variable [CommSemiring R]
variable [AddCommMonoid M]
variable [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄]
variable [AddCommMonoid N]
variable [Module R M] [Module R M₁] [Module R M₂] [Module R M₃] [Module R M₄] [Module R N]

/--
Definition of `IsometryEquiv` / `IsometryEquiv` 的定义

English:
structure IsometryEquiv
  parameters: (B₁ : LinearMap.BilinForm R M₁) (B₂ : LinearMap.BilinForm R M₂)
  extends: M₁ ≃ₗ[R] M₂
  axioms and operations (1):
    - map_app' : forall n m, B₂ (toFun n) (toFun m) = B₁ n m

中文:
结构 等距等价
  参数: (B₁ : 线性映射.BilinForm R M₁) (B₂ : 线性映射.BilinForm R M₂)
  继承: M₁ ≃ₗ[R] M₂
  公理与运算 (1 个):
    - map_app' : 对任意 n m, B₂ (toFun n) (toFun m) = B₁ n m
-/
structure IsometryEquiv (B₁ : LinearMap.BilinForm R M₁) (B₂ : LinearMap.BilinForm R M₂)
    extends M₁ ≃ₗ[R] M₂ where
  map_app' : forall n m, B₂ (toFun n) (toFun m) = B₁ n m

/--
Definition of `Equivalent` / `Equivalent` 的定义

English:
definition Equivalent
  signature: (B₁ : LinearMap.BilinForm R M₁) (B₂ : LinearMap.BilinForm R M₂)
  body: Nonempty (B₁.IsometryEquiv B₂)

中文:
定义 Equivalent
  签名: (B₁ : 线性映射.BilinForm R M₁) (B₂ : 线性映射.BilinForm R M₂)
  定义体: Nonempty (B₁.IsometryEquiv B₂)

Depends on / 依赖: IsometryEquiv, Nonempty
-/
def Equivalent (B₁ : LinearMap.BilinForm R M₁) (B₂ : LinearMap.BilinForm R M₂) :
    Prop :=
  Nonempty (B₁.IsometryEquiv B₂)

namespace IsometryEquiv

variable {B₁ : LinearMap.BilinForm R M₁} {B₂ : LinearMap.BilinForm R M₂}
  {B₃ : LinearMap.BilinForm R M₃}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EquivLike (B₁.IsometryEquiv B₂) M₁ M₂
  body: f.toLinearEquiv
  inv f := f.toLinearEquiv.symm
  left_inv f := f.toLinearEquiv.left_inv
  right_inv f := f.toLinearEquiv.right_inv
  coe_injective' f g := by cases f; cases g; simp +contextual

中文:
实例 :
  签名: 等价状 (B₁.等距等价 B₂) M₁ M₂
  定义体: f.toLinearEquiv
  inv f := f.toLinearEquiv.symm
  left_inv f := f.toLinearEquiv.left_inv
  right_inv f := f.toLinearEquiv.right_inv
  coe_injective' f g := by cases f; cases g; simp +contextual

Depends on / 依赖: f.toLinearEquiv, toLinearEquiv
-/
instance : EquivLike (B₁.IsometryEquiv B₂) M₁ M₂ where
  coe f := f.toLinearEquiv
  inv f := f.toLinearEquiv.symm
  left_inv f := f.toLinearEquiv.left_inv
  right_inv f := f.toLinearEquiv.right_inv
  coe_injective' f g := by cases f; cases g; simp +contextual

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LinearEquivClass (B₁.IsometryEquiv B₂) R M₁ M₂
  body: map_add f.toLinearEquiv
  map_smulₛₗ f := map_smulₛₗ f.toLinearEquiv

中文:
实例 :
  签名: LinearEquivClass (B₁.等距等价 B₂) R M₁ M₂
  定义体: map_add f.toLinearEquiv
  map_smulₛₗ f := map_smulₛₗ f.toLinearEquiv

Depends on / 依赖: f.toLinearEquiv, map_add, toLinearEquiv
-/
instance : LinearEquivClass (B₁.IsometryEquiv B₂) R M₁ M₂ where
  map_add f := map_add f.toLinearEquiv
  map_smulₛₗ f := map_smulₛₗ f.toLinearEquiv

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeOut (B₁.IsometryEquiv B₂) (M₁ ≃ₗ[R] M₂)
  body: ⟨IsometryEquiv.toLinearEquiv⟩

@[simp]

中文:
实例 :
  签名: CoeOut (B₁.等距等价 B₂) (M₁ ≃ₗ[R] M₂)
  定义体: ⟨IsometryEquiv.toLinearEquiv⟩

@[simp]

Depends on / 依赖: IsometryEquiv, IsometryEquiv.toLinearEquiv, toLinearEquiv
-/
instance : CoeOut (B₁.IsometryEquiv B₂) (M₁ ≃ₗ[R] M₂) :=
  ⟨IsometryEquiv.toLinearEquiv⟩

@[simp]
/--
theorem `coe_toLinearEquiv` / 定理 `coe_toLinearEquiv`

English:
theorem coe_toLinearEquiv
  given: (f : B₁.IsometryEquiv B₂)
  statement: ⇑(f : M₁ ≃ₗ[R] M₂) = f
  proof: rfl

@[simp]

中文:
定理 coe_toLinearEquiv
  条件: (f : B₁.等距等价 B₂)
  结论: ⇑(f : M₁ ≃ₗ[R] M₂) = f
  证明: rfl

@[simp]
-/
theorem coe_toLinearEquiv (f : B₁.IsometryEquiv B₂) : ⇑(f : M₁ ≃ₗ[R] M₂) = f :=
  rfl

@[simp]
/--
theorem `map_app` / 定理 `map_app`

English:
theorem map_app
  given: (f : B₁.IsometryEquiv B₂) (m n : M₁)
  statement: B₂ (f n) (f m) = B₁ n m
  proof: f.map_app' n m

中文:
定理 map_app
  条件: (f : B₁.等距等价 B₂) (m n : M₁)
  结论: B₂ (f n) (f m) = B₁ n m
  证明: f.map_app' n m

Depends on / 依赖: f.map_app, map_app
-/
theorem map_app (f : B₁.IsometryEquiv B₂) (m n : M₁) : B₂ (f n) (f m) = B₁ n m :=
  f.map_app' n m

/-- The identity isometric equivalence between a bilinear form and itself. -/
@[refl]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: (B : LinearMap.BilinForm R M)
  body: { LinearEquiv.refl R M with map_app' := fun _ _ => rfl }

中文:
定义 refl
  签名: (B : 线性映射.BilinForm R M)
  定义体: { LinearEquiv.refl R M with map_app' := fun _ _ => rfl }

Depends on / 依赖: LinearEquiv, LinearEquiv.refl, map_app
-/
def refl (B : LinearMap.BilinForm R M) : B.IsometryEquiv B :=
  { LinearEquiv.refl R M with map_app' := fun _ _ => rfl }

/-- The inverse isometric equivalence of an isometric equivalence between two bilinear forms. -/
@[symm]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: (f : B₁.IsometryEquiv B₂)
  body: { (f : M₁ ≃ₗ[R] M₂).symm with
    map_app' := by
      intro _ _; rw [← f.map_app]; congr
      repeat exact f.toLinearEquiv.apply_symm_apply _ }

中文:
定义 symm
  签名: (f : B₁.等距等价 B₂)
  定义体: { (f : M₁ ≃ₗ[R] M₂).symm with
    map_app' := by
      intro _ _; rw [← f.map_app]; congr
      repeat exact f.toLinearEquiv.apply_symm_apply _ }

Depends on / 依赖: apply_symm_apply, f.map_app, f.toLinearEquiv.apply_symm_apply, map_app, repeat, toLinearEquiv
-/
def symm (f : B₁.IsometryEquiv B₂) : B₂.IsometryEquiv B₁ :=
  { (f : M₁ ≃ₗ[R] M₂).symm with
    map_app' := by
      intro _ _; rw [← f.map_app]; congr
      repeat exact f.toLinearEquiv.apply_symm_apply _ }

/-- The composition of two isometric equivalences between bilinear forms. -/
@[trans]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (f : B₁.IsometryEquiv B₂) (g : B₂.IsometryEquiv B₃)
  body: { (f : M₁ ≃ₗ[R] M₂).trans (g : M₂ ≃ₗ[R] M₃) with
    map_app' := by intro n m; rw [← f.map_app, ← g.map_app]; rfl }

中文:
定义 trans
  签名: (f : B₁.等距等价 B₂) (g : B₂.等距等价 B₃)
  定义体: { (f : M₁ ≃ₗ[R] M₂).trans (g : M₂ ≃ₗ[R] M₃) with
    map_app' := by intro n m; rw [← f.map_app, ← g.map_app]; rfl }

Depends on / 依赖: f.map_app, g.map_app, map_app
-/
def trans (f : B₁.IsometryEquiv B₂) (g : B₂.IsometryEquiv B₃) : B₁.IsometryEquiv B₃ :=
  { (f : M₁ ≃ₗ[R] M₂).trans (g : M₂ ≃ₗ[R] M₃) with
    map_app' := by intro n m; rw [← f.map_app, ← g.map_app]; rfl }

/-- Isometric equivalences are isometric maps -/
@[simps]
/--
Definition of `toIsometry` / `toIsometry` 的定义

English:
definition toIsometry
  signature: (g : B₁.IsometryEquiv B₂)
  body: g x
  __ := g

中文:
定义 toIsometry
  签名: (g : B₁.等距等价 B₂)
  定义体: g x
  __ := g
-/
def toIsometry (g : B₁.IsometryEquiv B₂) : B₁ ->bᵢ B₂ where
  toFun x := g x
  __ := g

end IsometryEquiv

namespace Equivalent

variable {B₁ : LinearMap.BilinForm R M₁} {B₂ : LinearMap.BilinForm R M₂}
  {B₃ : LinearMap.BilinForm R M₃}

@[refl]
/--
theorem `refl` / 定理 `refl`

English:
theorem refl
  given: (Q : LinearMap.BilinForm R M)
  statement: Q.Equivalent Q
  proof: ⟨IsometryEquiv.refl Q⟩

@[symm]

中文:
定理 refl
  条件: (Q : 线性映射.BilinForm R M)
  结论: Q.Equivalent Q
  证明: ⟨IsometryEquiv.refl Q⟩

@[symm]

Depends on / 依赖: IsometryEquiv, IsometryEquiv.refl
-/
theorem refl (Q : LinearMap.BilinForm R M) : Q.Equivalent Q :=
  ⟨IsometryEquiv.refl Q⟩

@[symm]
/--
theorem `symm` / 定理 `symm`

English:
theorem symm
  given: (h : B₁.Equivalent B₂)
  statement: B₂.Equivalent B₁
  proof: h.elim fun f => ⟨f.symm⟩

@[trans]

中文:
定理 symm
  条件: (h : B₁.Equivalent B₂)
  结论: B₂.Equivalent B₁
  证明: h.elim fun f => ⟨f.symm⟩

@[trans]

Depends on / 依赖: f.symm, h.elim
-/
theorem symm (h : B₁.Equivalent B₂) : B₂.Equivalent B₁ :=
  h.elim fun f => ⟨f.symm⟩

@[trans]
/--
theorem `trans` / 定理 `trans`

English:
theorem trans
  given: (h : B₁.Equivalent B₂) (h' : B₂.Equivalent B₃)
  statement: B₁.Equivalent B₃
  proof: h'.elim h.elim fun f g => ⟨f.trans g⟩

中文:
定理 trans
  条件: (h : B₁.Equivalent B₂) (h' : B₂.Equivalent B₃)
  结论: B₁.Equivalent B₃
  证明: h'.elim h.elim fun f g => ⟨f.trans g⟩

Depends on / 依赖: f.trans, h.elim
-/
theorem trans (h : B₁.Equivalent B₂) (h' : B₂.Equivalent B₃) : B₁.Equivalent B₃ :=
h'.elim h.elim fun f g => ⟨f.trans g⟩

end Equivalent

/--
Definition of `isometryEquivOfCompLinearEquiv` / `isometryEquivOfCompLinearEquiv` 的定义

English:
definition isometryEquivOfCompLinearEquiv
  signature: (B : LinearMap.BilinForm R M) (f : M₁ ≃ₗ[R] M)
  body: { f.symm with
    map_app' := by
      intro _ _
      simp only [comp_apply, LinearEquiv.coe_coe, LinearEquiv.toFun_eq_coe,
        f.apply_symm_apply] }

中文:
定义 isometryEquivOfCompLinearEquiv
  签名: (B : 线性映射.BilinForm R M) (f : M₁ ≃ₗ[R] M)
  定义体: { f.symm with
    map_app' := by
      intro _ _
      simp only [comp_apply, LinearEquiv.coe_coe, LinearEquiv.toFun_eq_coe,
        f.apply_symm_apply] }

Depends on / 依赖: LinearEquiv, LinearEquiv.coe_coe, LinearEquiv.toFun_eq_coe, apply_symm_apply, coe_coe, comp_apply, f.apply_symm_apply, f.symm, map_app, toFun_eq_coe
-/
def isometryEquivOfCompLinearEquiv (B : LinearMap.BilinForm R M) (f : M₁ ≃ₗ[R] M) :
    B.IsometryEquiv (B.comp (f : M₁ ->ₗ[R] M) (f : M₁ ->ₗ[R] M)) :=
  { f.symm with
    map_app' := by
      intro _ _
      simp only [comp_apply, LinearEquiv.coe_coe, LinearEquiv.toFun_eq_coe,
        f.apply_symm_apply] }

end LinearMap.BilinForm
