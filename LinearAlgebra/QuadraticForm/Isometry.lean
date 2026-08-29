/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Isometric linear maps

## Main definitions

* `QuadraticMap.Isometry`: `LinearMap`s which map between two different quadratic forms

## Notation

`Q₁ →qᵢ Q₂` is notation for `Q₁.Isometry Q₂`.
-/

@[expose] public section

variable {R M M₁ M₂ M₃ M₄ N : Type*}

namespace QuadraticMap

variable [CommSemiring R]
variable [AddCommMonoid M]
variable [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄]
variable [AddCommMonoid N]
variable [Module R M] [Module R M₁] [Module R M₂] [Module R M₃] [Module R M₄] [Module R N]

/--
Definition of `Isometry` / `Isometry` 的定义

English:
structure Isometry
  parameters: (Q₁ : QuadraticMap R M₁ N) (Q₂ : QuadraticMap R M₂ N)
  extends: M₁ ->ₗ[R] M₂
  axioms and operations (1):
    - map_app' : forall m, Q₂ (toFun m) = Q₁ m

中文:
结构 Isometry
  参数: (Q₁ : QuadraticMap R M₁ N) (Q₂ : QuadraticMap R M₂ N)
  继承: M₁ ->ₗ[R] M₂
  公理与运算 (1 个):
    - map_app' : 对任意 m, Q₂ (toFun m) = Q₁ m
-/
structure Isometry (Q₁ : QuadraticMap R M₁ N) (Q₂ : QuadraticMap R M₂ N) extends M₁ ->ₗ[R] M₂ where
  /-- The quadratic form agrees across the map. -/
  map_app' : forall m, Q₂ (toFun m) = Q₁ m

namespace Isometry

@[inherit_doc]
notation:25 Q₁ " ->qᵢ " Q₂:0 => Isometry Q₁ Q₂

variable {Q₁ : QuadraticMap R M₁ N} {Q₂ : QuadraticMap R M₂ N}
variable {Q₃ : QuadraticMap R M₃ N} {Q₄ : QuadraticMap R M₄ N}

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike (Q₁ ->qᵢ Q₂) M₁ M₂ where
  body: f.toLinearMap
  coe_injective f g h := by cases f; cases g; congr; exact DFunLike.coe_injective h

中文:
实例 instFunLike
  签名: : FunLike (Q₁ ->qᵢ Q₂) M₁ M₂ where
  定义体: f.toLinearMap
  coe_injective f g h := by cases f; cases g; congr; exact DFunLike.coe_injective h

Depends on / 依赖: f.toLinearMap, toLinearMap
-/
instance instFunLike : FunLike (Q₁ ->qᵢ Q₂) M₁ M₂ where
  coe f := f.toLinearMap
  coe_injective f g h := by cases f; cases g; congr; exact DFunLike.coe_injective h

/--
Instance `instLinearMapClass` / 实例 `instLinearMapClass`

English:
instance instLinearMapClass
  signature: : LinearMapClass (Q₁ ->qᵢ Q₂) R M₁ M₂ where
  body: f.toLinearMap.map_add
  map_smulₛₗ f := f.toLinearMap.map_smul

中文:
实例 instLinearMapClass
  签名: : LinearMapClass (Q₁ ->qᵢ Q₂) R M₁ M₂ where
  定义体: f.toLinearMap.map_add
  map_smulₛₗ f := f.toLinearMap.map_smul

Depends on / 依赖: f.toLinearMap.map_add, map_add, toLinearMap
-/
instance instLinearMapClass : LinearMapClass (Q₁ ->qᵢ Q₂) R M₁ M₂ where
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
    Function.Injective (Isometry.toLinearMap : (Q₁ ->qᵢ Q₂) -> M₁ ->ₗ[R] M₂) := fun _f _g h =>
  DFunLike.coe_injective (congr_arg DFunLike.coe h :)

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: ⦃f g
  statement: Q₁ ->qᵢ Q₂⦄ (h : forall x, f x = g x) : f = g
  proof: DFunLike.ext _ _ h

中文:
定理 ext
  条件: ⦃f g
  结论: Q₁ ->qᵢ Q₂⦄ (h : 对任意 x, f x = g x) : f = g
  证明: DFunLike.ext _ _ h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext ⦃f g : Q₁ ->qᵢ Q₂⦄ (h : forall x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

/--
Definition of `Simps.apply` / `Simps.apply` 的定义

English:
definition Simps.apply
  signature: (f : Q₁ ->qᵢ Q₂)
  body: f

initialize_simps_projections Isometry (toFun -> apply)

@[simp]

中文:
定义 Simps.apply
  签名: (f : Q₁ ->qᵢ Q₂)
  定义体: f

initialize_simps_projections Isometry (toFun -> apply)

@[simp]
-/
protected def Simps.apply (f : Q₁ ->qᵢ Q₂) : M₁ -> M₂ := f

initialize_simps_projections Isometry (toFun -> apply)

@[simp]
/--
theorem `map_app` / 定理 `map_app`

English:
theorem map_app
  given: (f : Q₁ ->qᵢ Q₂) (m : M₁)
  statement: Q₂ (f m) = Q₁ m
  proof: f.map_app' m

@[simp]

中文:
定理 map_app
  条件: (f : Q₁ ->qᵢ Q₂) (m : M₁)
  结论: Q₂ (f m) = Q₁ m
  证明: f.map_app' m

@[simp]

Depends on / 依赖: f.map_app, map_app
-/
theorem map_app (f : Q₁ ->qᵢ Q₂) (m : M₁) : Q₂ (f m) = Q₁ m :=
  f.map_app' m

@[simp]
/--
theorem `coe_toLinearMap` / 定理 `coe_toLinearMap`

English:
theorem coe_toLinearMap
  given: (f : Q₁ ->qᵢ Q₂)
  statement: ⇑f.toLinearMap = f
  proof: rfl

中文:
定理 coe_toLinearMap
  条件: (f : Q₁ ->qᵢ Q₂)
  结论: ⇑f.toLinearMap = f
  证明: rfl
-/
theorem coe_toLinearMap (f : Q₁ ->qᵢ Q₂) : ⇑f.toLinearMap = f :=
  rfl

/-- The identity isometry from a quadratic form to itself. -/
@[simps!]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (Q : QuadraticMap R M N)
  body: LinearMap.id
  map_app' _ := rfl

中文:
定义 id
  签名: (Q : QuadraticMap R M N)
  定义体: LinearMap.id
  map_app' _ := rfl

Depends on / 依赖: LinearMap, LinearMap.id
-/
def id (Q : QuadraticMap R M N) : Q ->qᵢ Q where
  __ := LinearMap.id
  map_app' _ := rfl

/-- The identity isometry between equal quadratic forms. -/
@[simps!]
/--
Definition of `ofEq` / `ofEq` 的定义

English:
definition ofEq
  signature: {Q₁ Q₂ : QuadraticMap R M₁ N} (h : Q₁ = Q₂)
  body: LinearMap.id
  map_app' _ := h ▸ rfl

@[simp]

中文:
定义 ofEq
  签名: {Q₁ Q₂ : QuadraticMap R M₁ N} (h : Q₁ = Q₂)
  定义体: LinearMap.id
  map_app' _ := h ▸ rfl

@[simp]

Depends on / 依赖: LinearMap, LinearMap.id
-/
def ofEq {Q₁ Q₂ : QuadraticMap R M₁ N} (h : Q₁ = Q₂) : Q₁ ->qᵢ Q₂ where
  __ := LinearMap.id
  map_app' _ := h ▸ rfl

@[simp]
/--
theorem `ofEq_rfl` / 定理 `ofEq_rfl`

English:
theorem ofEq_rfl
  given: {Q : QuadraticMap R M₁ N}
  statement: ofEq (rfl : Q = Q) = .id Q
  proof: rfl

中文:
定理 ofEq_rfl
  条件: {Q : QuadraticMap R M₁ N}
  结论: ofEq (rfl : Q = Q) = .id Q
  证明: rfl
-/
theorem ofEq_rfl {Q : QuadraticMap R M₁ N} : ofEq (rfl : Q = Q) = .id Q := rfl

/-- The composition of two isometries between quadratic forms. -/
@[simps]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (g : Q₂ ->qᵢ Q₃) (f : Q₁ ->qᵢ Q₂)
  body: g (f x)
  map_app' x := by rw [← f.map_app, ← g.map_app]
  __ := (g.toLinearMap : M₂ ->ₗ[R] M₃) ∘ₗ (f.toLinearMap : M₁ ->ₗ[R] M₂)

@[simp]

中文:
定义 comp
  签名: (g : Q₂ ->qᵢ Q₃) (f : Q₁ ->qᵢ Q₂)
  定义体: g (f x)
  map_app' x := by rw [← f.map_app, ← g.map_app]
  __ := (g.toLinearMap : M₂ ->ₗ[R] M₃) ∘ₗ (f.toLinearMap : M₁ ->ₗ[R] M₂)

@[simp]
-/
def comp (g : Q₂ ->qᵢ Q₃) (f : Q₁ ->qᵢ Q₂) : Q₁ ->qᵢ Q₃ where
  toFun x := g (f x)
  map_app' x := by rw [← f.map_app, ← g.map_app]
  __ := (g.toLinearMap : M₂ ->ₗ[R] M₃) ∘ₗ (f.toLinearMap : M₁ ->ₗ[R] M₂)

@[simp]
/--
theorem `toLinearMap_comp` / 定理 `toLinearMap_comp`

English:
theorem toLinearMap_comp
  given: (g : Q₂ ->qᵢ Q₃) (f : Q₁ ->qᵢ Q₂)
  proof: rfl

@[simp]

中文:
定理 toLinearMap_comp
  条件: (g : Q₂ ->qᵢ Q₃) (f : Q₁ ->qᵢ Q₂)
  证明: rfl

@[simp]
-/
theorem toLinearMap_comp (g : Q₂ ->qᵢ Q₃) (f : Q₁ ->qᵢ Q₂) :
    (g.comp f).toLinearMap = g.toLinearMap.comp f.toLinearMap :=
  rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : Q₁ ->qᵢ Q₂)
  statement: (id Q₂).comp f = f
  proof: ext fun _ => rfl

@[simp]

中文:
定理 id_comp
  条件: (f : Q₁ ->qᵢ Q₂)
  结论: (id Q₂).comp f = f
  证明: ext fun _ => rfl

@[simp]
-/
theorem id_comp (f : Q₁ ->qᵢ Q₂) : (id Q₂).comp f = f :=
  ext fun _ => rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : Q₁ ->qᵢ Q₂)
  statement: f.comp (id Q₁) = f
  proof: ext fun _ => rfl

中文:
定理 comp_id
  条件: (f : Q₁ ->qᵢ Q₂)
  结论: f.comp (id Q₁) = f
  证明: ext fun _ => rfl
-/
theorem comp_id (f : Q₁ ->qᵢ Q₂) : f.comp (id Q₁) = f :=
  ext fun _ => rfl

/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (h : Q₃ ->qᵢ Q₄) (g : Q₂ ->qᵢ Q₃) (f : Q₁ ->qᵢ Q₂)
  proof: ext fun _ => rfl

中文:
定理 comp_assoc
  条件: (h : Q₃ ->qᵢ Q₄) (g : Q₂ ->qᵢ Q₃) (f : Q₁ ->qᵢ Q₂)
  证明: ext fun _ => rfl
-/
theorem comp_assoc (h : Q₃ ->qᵢ Q₄) (g : Q₂ ->qᵢ Q₃) (f : Q₁ ->qᵢ Q₂) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  ext fun _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero ((0 : QuadraticMap R M₁ N) ->qᵢ Q₂)
  body: { (0 : M₁ ->ₗ[R] M₂) with map_app' := fun _ => map_zero _ }

中文:
实例 :
  签名: Zero ((0 : QuadraticMap R M₁ N) ->qᵢ Q₂)
  定义体: { (0 : M₁ ->ₗ[R] M₂) with map_app' := fun _ => map_zero _ }

Depends on / 依赖: map_app, map_zero
-/
instance : Zero ((0 : QuadraticMap R M₁ N) ->qᵢ Q₂) where
  zero := { (0 : M₁ ->ₗ[R] M₂) with map_app' := fun _ => map_zero _ }

/--
Instance `hasZeroOfSubsingleton` / 实例 `hasZeroOfSubsingleton`

English:
instance hasZeroOfSubsingleton
  signature: [Subsingleton M₁]
  body: { (0 : M₁ ->ₗ[R] M₂) with
    map_app' := fun m => Subsingleton.elim 0 m ▸ (map_zero _).trans (map_zero _).symm }

中文:
实例 hasZeroOfSubsingleton
  签名: [Subsingleton M₁]
  定义体: { (0 : M₁ ->ₗ[R] M₂) with
    map_app' := fun m => Subsingleton.elim 0 m ▸ (map_zero _).trans (map_zero _).symm }

Depends on / 依赖: Subsingleton, Subsingleton.elim, map_app, map_zero
-/
instance hasZeroOfSubsingleton [Subsingleton M₁] : Zero (Q₁ ->qᵢ Q₂) where
  zero :=
  { (0 : M₁ ->ₗ[R] M₂) with
    map_app' := fun m => Subsingleton.elim 0 m ▸ (map_zero _).trans (map_zero _).symm }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: M₂] : Subsingleton (Q₁ ->qᵢ Q₂)
  body: ⟨fun _ _ => ext fun _ => Subsingleton.elim _ _⟩

中文:
实例 [Subsingleton
  签名: M₂] : Subsingleton (Q₁ ->qᵢ Q₂)
  定义体: ⟨fun _ _ => ext fun _ => Subsingleton.elim _ _⟩

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
instance [Subsingleton M₂] : Subsingleton (Q₁ ->qᵢ Q₂) :=
  ⟨fun _ _ => ext fun _ => Subsingleton.elim _ _⟩

end Isometry

end QuadraticMap
