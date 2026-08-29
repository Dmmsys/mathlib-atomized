/-
Copyright (c) 2025 Sahan Wijetunga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sahan Wijetunga
-/
module

public import Mathlib.LinearAlgebra.BilinearMap

/-!
# Isometric linear maps

In this file, we define isometries of bilinear spaces as linear maps that respect the
associated bilinear forms.
This file should be kept in sync with the corresponding file for quadratic maps, namely
`Mathlib/LinearAlgebra/QuadraticForm/Isometry.lean`

## Main definitions

* ` LinearMap.BilinForm.Isometry`: `LinearMap`s which respect a given pair of bilinear forms

## Notation

`B₁ →bᵢ B₂` is notation for `B₁.Isometry B₂`.
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
Definition of `Isometry` / `Isometry` 的定义

English:
structure Isometry
  parameters: (B₁ : LinearMap.BilinForm R M₁) (B₂ : LinearMap.BilinForm R M₂)
  extends: M₁ ->ₗ[R] M₂
  axioms and operations (1):
    - map_app'((m m' : M₁)) : B₂ (toFun m) (toFun m') = B₁ m m'

中文:
结构 Isometry
  参数: (B₁ : LinearMap.BilinForm R M₁) (B₂ : LinearMap.BilinForm R M₂)
  继承: M₁ ->ₗ[R] M₂
  公理与运算 (1 个):
    - map_app'((m m' : M₁)) : B₂ (toFun m) (toFun m') = B₁ m m'
-/
structure Isometry (B₁ : LinearMap.BilinForm R M₁) (B₂ : LinearMap.BilinForm R M₂)
    extends M₁ ->ₗ[R] M₂ where
  /-- The bilinear forms agree across the map. -/
  map_app' (m m' : M₁) : B₂ (toFun m) (toFun m') = B₁ m m'

namespace Isometry

@[inherit_doc]
notation:25 B₁ " ->bᵢ " B₂:0 => Isometry B₁ B₂

variable {B₁ : LinearMap.BilinForm R M₁} {B₂ : LinearMap.BilinForm R M₂}
variable {B₃ : LinearMap.BilinForm R M₃} {B₄ : LinearMap.BilinForm R M₄}

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike (B₁ ->bᵢ B₂) M₁ M₂ where
  body: f.toLinearMap
  coe_injective f g h := by cases f; cases g; congr; exact DFunLike.coe_injective h

中文:
实例 instFunLike
  签名: : FunLike (B₁ ->bᵢ B₂) M₁ M₂ where
  定义体: f.toLinearMap
  coe_injective f g h := by cases f; cases g; congr; exact DFunLike.coe_injective h

Depends on / 依赖: f.toLinearMap, toLinearMap
-/
instance instFunLike : FunLike (B₁ ->bᵢ B₂) M₁ M₂ where
  coe f := f.toLinearMap
  coe_injective f g h := by cases f; cases g; congr; exact DFunLike.coe_injective h

/--
Instance `instLinearMapClass` / 实例 `instLinearMapClass`

English:
instance instLinearMapClass
  signature: : LinearMapClass (B₁ ->bᵢ B₂) R M₁ M₂ where
  body: f.toLinearMap.map_add
  map_smulₛₗ f := f.toLinearMap.map_smul

中文:
实例 instLinearMapClass
  签名: : LinearMapClass (B₁ ->bᵢ B₂) R M₁ M₂ where
  定义体: f.toLinearMap.map_add
  map_smulₛₗ f := f.toLinearMap.map_smul

Depends on / 依赖: f.toLinearMap.map_add, map_add, toLinearMap
-/
instance instLinearMapClass : LinearMapClass (B₁ ->bᵢ B₂) R M₁ M₂ where
  map_add f := f.toLinearMap.map_add
  map_smulₛₗ f := f.toLinearMap.map_smul

/--
theorem `toLinearMap_injective` / 定理 `toLinearMap_injective`

English:
theorem toLinearMap_injective
  proof: fun _f _g h =>
  DFunLike.coe_injective (congr_arg DFunLike.coe h :)

@[ext]

中文:
定理 toLinearMap_injective
  证明: fun _f _g h =>
  DFunLike.coe_injective (congr_arg DFunLike.coe h :)

@[ext]
-/
theorem toLinearMap_injective :
    Function.Injective (Isometry.toLinearMap : (B₁ ->bᵢ B₂) -> M₁ ->ₗ[R] M₂) := fun _f _g h =>
  DFunLike.coe_injective (congr_arg DFunLike.coe h :)

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: ⦃f g
  statement: B₁ ->bᵢ B₂⦄ (h : forall x, f x = g x) : f = g
  proof: DFunLike.ext _ _ h

中文:
定理 ext
  条件: ⦃f g
  结论: B₁ ->bᵢ B₂⦄ (h : 对任意 x, f x = g x) : f = g
  证明: DFunLike.ext _ _ h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext ⦃f g : B₁ ->bᵢ B₂⦄ (h : forall x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

/--
Definition of `Simps.apply` / `Simps.apply` 的定义

English:
definition Simps.apply
  signature: (f : B₁ ->bᵢ B₂)
  body: f

initialize_simps_projections Isometry (toFun -> apply)

@[simp]

中文:
定义 Simps.apply
  签名: (f : B₁ ->bᵢ B₂)
  定义体: f

initialize_simps_projections Isometry (toFun -> apply)

@[simp]
-/
protected def Simps.apply (f : B₁ ->bᵢ B₂) : M₁ -> M₂ := f

initialize_simps_projections Isometry (toFun -> apply)

@[simp]
/--
theorem `map_app` / 定理 `map_app`

English:
theorem map_app
  given: (f : B₁ ->bᵢ B₂) (m m' : M₁)
  statement: B₂ (f m) (f m') = B₁ m m'
  proof: f.map_app' m m'

@[simp]

中文:
定理 map_app
  条件: (f : B₁ ->bᵢ B₂) (m m' : M₁)
  结论: B₂ (f m) (f m') = B₁ m m'
  证明: f.map_app' m m'

@[simp]

Depends on / 依赖: f.map_app, map_app
-/
theorem map_app (f : B₁ ->bᵢ B₂) (m m' : M₁) : B₂ (f m) (f m') = B₁ m m' :=
  f.map_app' m m'

@[simp]
/--
theorem `coe_toLinearMap` / 定理 `coe_toLinearMap`

English:
theorem coe_toLinearMap
  given: (f : B₁ ->bᵢ B₂)
  statement: ⇑f.toLinearMap = f
  proof: rfl

中文:
定理 coe_toLinearMap
  条件: (f : B₁ ->bᵢ B₂)
  结论: ⇑f.toLinearMap = f
  证明: rfl
-/
theorem coe_toLinearMap (f : B₁ ->bᵢ B₂) : ⇑f.toLinearMap = f :=
  rfl

/-- The identity isometry from a bilinear form to itself. -/
@[simps!]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (B : LinearMap.BilinForm R M)
  body: LinearMap.id
  map_app' _ _ := rfl

中文:
定义 id
  签名: (B : LinearMap.BilinForm R M)
  定义体: LinearMap.id
  map_app' _ _ := rfl

Depends on / 依赖: LinearMap, LinearMap.id
-/
def id (B : LinearMap.BilinForm R M) : B ->bᵢ B where
  __ := LinearMap.id
  map_app' _ _ := rfl

/-- The identity isometry between equal bilinear forms. -/
@[simps!]
/--
Definition of `ofEq` / `ofEq` 的定义

English:
definition ofEq
  signature: {B₁ B₂ : LinearMap.BilinForm R M₁} (h : B₁ = B₂)
  body: LinearMap.id
  map_app' _ _ := h ▸ rfl

@[simp]

中文:
定义 ofEq
  签名: {B₁ B₂ : LinearMap.BilinForm R M₁} (h : B₁ = B₂)
  定义体: LinearMap.id
  map_app' _ _ := h ▸ rfl

@[simp]

Depends on / 依赖: LinearMap, LinearMap.id
-/
def ofEq {B₁ B₂ : LinearMap.BilinForm R M₁} (h : B₁ = B₂) : B₁ ->bᵢ B₂ where
  __ := LinearMap.id
  map_app' _ _ := h ▸ rfl

@[simp]
/--
theorem `ofEq_rfl` / 定理 `ofEq_rfl`

English:
theorem ofEq_rfl
  given: {B : LinearMap.BilinForm R M₁}
  statement: ofEq (rfl : B = B) = .id B
  proof: rfl

中文:
定理 ofEq_rfl
  条件: {B : LinearMap.BilinForm R M₁}
  结论: ofEq (rfl : B = B) = .id B
  证明: rfl
-/
theorem ofEq_rfl {B : LinearMap.BilinForm R M₁} : ofEq (rfl : B = B) = .id B := rfl

/-- The composition of two isometries between bilinear forms. -/
@[simps]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (g : B₂ ->bᵢ B₃) (f : B₁ ->bᵢ B₂)
  body: g (f x)
  map_app' x y := by rw [← f.map_app, ← g.map_app]
  __ := (g.toLinearMap : M₂ ->ₗ[R] M₃) ∘ₗ (f.toLinearMap : M₁ ->ₗ[R] M₂)

@[simp]

中文:
定义 comp
  签名: (g : B₂ ->bᵢ B₃) (f : B₁ ->bᵢ B₂)
  定义体: g (f x)
  map_app' x y := by rw [← f.map_app, ← g.map_app]
  __ := (g.toLinearMap : M₂ ->ₗ[R] M₃) ∘ₗ (f.toLinearMap : M₁ ->ₗ[R] M₂)

@[simp]
-/
def comp (g : B₂ ->bᵢ B₃) (f : B₁ ->bᵢ B₂) : B₁ ->bᵢ B₃ where
  toFun x := g (f x)
  map_app' x y := by rw [← f.map_app, ← g.map_app]
  __ := (g.toLinearMap : M₂ ->ₗ[R] M₃) ∘ₗ (f.toLinearMap : M₁ ->ₗ[R] M₂)

@[simp]
/--
theorem `toLinearMap_comp` / 定理 `toLinearMap_comp`

English:
theorem toLinearMap_comp
  given: (g : B₂ ->bᵢ B₃) (f : B₁ ->bᵢ B₂)
  proof: rfl

@[simp]

中文:
定理 toLinearMap_comp
  条件: (g : B₂ ->bᵢ B₃) (f : B₁ ->bᵢ B₂)
  证明: rfl

@[simp]
-/
theorem toLinearMap_comp (g : B₂ ->bᵢ B₃) (f : B₁ ->bᵢ B₂) :
    (g.comp f).toLinearMap = g.toLinearMap.comp f.toLinearMap :=
  rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : B₁ ->bᵢ B₂)
  statement: (id B₂).comp f = f
  proof: ext fun _ => rfl

@[simp]

中文:
定理 id_comp
  条件: (f : B₁ ->bᵢ B₂)
  结论: (id B₂).comp f = f
  证明: ext fun _ => rfl

@[simp]
-/
theorem id_comp (f : B₁ ->bᵢ B₂) : (id B₂).comp f = f :=
  ext fun _ => rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : B₁ ->bᵢ B₂)
  statement: f.comp (id B₁) = f
  proof: ext fun _ => rfl

中文:
定理 comp_id
  条件: (f : B₁ ->bᵢ B₂)
  结论: f.comp (id B₁) = f
  证明: ext fun _ => rfl
-/
theorem comp_id (f : B₁ ->bᵢ B₂) : f.comp (id B₁) = f :=
  ext fun _ => rfl

/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (h : B₃ ->bᵢ B₄) (g : B₂ ->bᵢ B₃) (f : B₁ ->bᵢ B₂)
  proof: ext fun _ => rfl

中文:
定理 comp_assoc
  条件: (h : B₃ ->bᵢ B₄) (g : B₂ ->bᵢ B₃) (f : B₁ ->bᵢ B₂)
  证明: ext fun _ => rfl
-/
theorem comp_assoc (h : B₃ ->bᵢ B₄) (g : B₂ ->bᵢ B₃) (f : B₁ ->bᵢ B₂) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  ext fun _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero ((0 : LinearMap.BilinForm R M₁) ->bᵢ B₂)
  body: { (0 : M₁ ->ₗ[R] M₂) with map_app' := fun _ _ => map_zero _ }

中文:
实例 :
  签名: Zero ((0 : LinearMap.BilinForm R M₁) ->bᵢ B₂)
  定义体: { (0 : M₁ ->ₗ[R] M₂) with map_app' := fun _ _ => map_zero _ }

Depends on / 依赖: map_app, map_zero
-/
instance : Zero ((0 : LinearMap.BilinForm R M₁) ->bᵢ B₂) where
  zero := { (0 : M₁ ->ₗ[R] M₂) with map_app' := fun _ _ => map_zero _ }

/--
Instance `hasZeroOfSubsingleton` / 实例 `hasZeroOfSubsingleton`

English:
instance hasZeroOfSubsingleton
  signature: [Subsingleton M₁]
  body: { (0 : M₁ ->ₗ[R] M₂) with
    map_app' := fun x y => by
      rw [Subsingleton.elim x 0]; rw [Subsingleton.elim y 0]
      simp }

中文:
实例 hasZeroOfSubsingleton
  签名: [Subsingleton M₁]
  定义体: { (0 : M₁ ->ₗ[R] M₂) with
    map_app' := fun x y => by
      rw [Subsingleton.elim x 0]; rw [Subsingleton.elim y 0]
      simp }

Depends on / 依赖: Subsingleton, Subsingleton.elim, map_app
-/
instance hasZeroOfSubsingleton [Subsingleton M₁] : Zero (B₁ ->bᵢ B₂) where
  zero :=
  { (0 : M₁ ->ₗ[R] M₂) with
    map_app' := fun x y => by
      rw [Subsingleton.elim x 0]; rw [Subsingleton.elim y 0]
      simp }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: M₂] : Subsingleton (B₁ ->bᵢ B₂)
  body: ⟨fun _ _ => ext fun _ => Subsingleton.elim _ _⟩

中文:
实例 [Subsingleton
  签名: M₂] : Subsingleton (B₁ ->bᵢ B₂)
  定义体: ⟨fun _ _ => ext fun _ => Subsingleton.elim _ _⟩

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
instance [Subsingleton M₂] : Subsingleton (B₁ ->bᵢ B₂) :=
  ⟨fun _ _ => ext fun _ => Subsingleton.elim _ _⟩

end Isometry

end BilinForm

end LinearMap
