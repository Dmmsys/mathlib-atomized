/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Tactic.Convert

/-!
# Functions functorial with respect to equivalences

An `EquivFunctor` is a function from `Type → Type` equipped with the additional data of
coherently mapping equivalences to equivalences.

In categorical language, it is an endofunctor of the "core" of the category `Type`.
-/

@[expose] public section


universe u₀ u₁ u₂ v₀ v₁ v₂

open Function

/--
Definition of `EquivFunctor` / `EquivFunctor` 的定义

English:
class EquivFunctor
  parameters: (f : Type u₀ -> Type u₁)
  axioms and operations (3):
    - map : forall {α β}, α ≃ β -> f α -> f β
    - map_refl' : forall α, map (Equiv.refl α) = @id (f α)  [default: by rfl]
    - map_trans' : forall {α β γ} (k : α ≃ β) (h : β ≃ γ), map (k.trans h) = map h ∘ map k  [default: by rfl]

中文:
类 等价函子
  参数: (f : 类型u₀ -> 类型u₁)
  公理与运算 (3 个):
    - map : 对任意 {α β}, α ≃ β -> f α -> f β
    - map_refl' : 对任意 α, map (等价.refl α) = @id (f α)  [默认: by rfl]
    - map_trans' : 对任意 {α β γ} (k : α ≃ β) (h : β ≃ γ), map (k.trans h) = map h ∘ map k  [默认: by rfl]
-/
class EquivFunctor (f : Type u₀ -> Type u₁) where
  /-- The action of `f` on isomorphisms. -/
  map : forall {α β}, α ≃ β -> f α -> f β
  /-- `map` of `f` preserves the identity morphism. -/
  map_refl' : forall α, map (Equiv.refl α) = @id (f α) := by rfl
  /-- `map` is functorial on equivalences. -/
  map_trans' : forall {α β γ} (k : α ≃ β) (h : β ≃ γ), map (k.trans h) = map h ∘ map k := by rfl

attribute [simp] EquivFunctor.map_refl'

namespace EquivFunctor

section

variable (f : Type u₀ -> Type u₁) [EquivFunctor f] {α β : Type u₀} (e : α ≃ β)

/--
Definition of `mapEquiv` / `mapEquiv` 的定义

English:
definition mapEquiv
  signature: : f α ≃ f β where
  body: EquivFunctor.map e
  invFun := EquivFunctor.map e.symm
  left_inv x := by
    convert! (congr_fun (EquivFunctor.map_trans' e e.symm) x).symm
    simp
  right_inv y := by
    convert! (congr_fun (EquivFunctor.map_trans' e.symm e) y).symm
    simp

@[simp]

中文:
定义 mapEquiv
  签名: : f α ≃ f β where
  定义体: EquivFunctor.map e
  invFun := EquivFunctor.map e.symm
  left_inv x := by
    convert! (congr_fun (EquivFunctor.map_trans' e e.symm) x).symm
    simp
  right_inv y := by
    convert! (congr_fun (EquivFunctor.map_trans' e.symm e) y).symm
    simp

@[simp]

Depends on / 依赖: EquivFunctor, EquivFunctor.map
-/
def mapEquiv : f α ≃ f β where
  toFun := EquivFunctor.map e
  invFun := EquivFunctor.map e.symm
  left_inv x := by
    convert! (congr_fun (EquivFunctor.map_trans' e e.symm) x).symm
    simp
  right_inv y := by
    convert! (congr_fun (EquivFunctor.map_trans' e.symm e) y).symm
    simp

@[simp]
/--
theorem `mapEquiv_apply` / 定理 `mapEquiv_apply`

English:
theorem mapEquiv_apply
  given: (x : f α)
  statement: mapEquiv f e x = EquivFunctor.map e x
  proof: rfl

中文:
定理 mapEquiv_apply
  条件: (x : f α)
  结论: mapEquiv f e x = 等价函子.map e x
  证明: rfl
-/
theorem mapEquiv_apply (x : f α) : mapEquiv f e x = EquivFunctor.map e x :=
  rfl

/--
theorem `mapEquiv_symm_apply` / 定理 `mapEquiv_symm_apply`

English:
theorem mapEquiv_symm_apply
  given: (y : f β)
  statement: (mapEquiv f e).symm y = EquivFunctor.map e.symm y
  proof: rfl

@[simp]

中文:
定理 mapEquiv_symm_apply
  条件: (y : f β)
  结论: (mapEquiv f e).symm y = 等价函子.map e.symm y
  证明: rfl

@[simp]
-/
theorem mapEquiv_symm_apply (y : f β) : (mapEquiv f e).symm y = EquivFunctor.map e.symm y :=
  rfl

@[simp]
/--
theorem `mapEquiv_refl` / 定理 `mapEquiv_refl`

English:
theorem mapEquiv_refl
  given: (α)
  statement: mapEquiv f (Equiv.refl α) = Equiv.refl (f α)
  proof: by
  ext; simp [mapEquiv]

@[simp]

中文:
定理 mapEquiv_refl
  条件: (α)
  结论: mapEquiv f (等价.refl α) = 等价.refl (f α)
  证明: by
  ext; simp [mapEquiv]

@[simp]

Depends on / 依赖: mapEquiv
-/
theorem mapEquiv_refl (α) : mapEquiv f (Equiv.refl α) = Equiv.refl (f α) := by
  ext; simp [mapEquiv]

@[simp]
/--
theorem `mapEquiv_symm` / 定理 `mapEquiv_symm`

English:
theorem mapEquiv_symm
  statement: (mapEquiv f e).symm = mapEquiv f e.symm
  proof: Equiv.ext mapEquiv_symm_apply f e

中文:
定理 mapEquiv_symm
  结论: (mapEquiv f e).symm = mapEquiv f e.symm
  证明: Equiv.ext mapEquiv_symm_apply f e

Depends on / 依赖: Equiv.ext, mapEquiv_symm_apply
-/
theorem mapEquiv_symm : (mapEquiv f e).symm = mapEquiv f e.symm :=
Equiv.ext mapEquiv_symm_apply f e

set_option backward.isDefEq.respectTransparency false in
/-- The composition of `mapEquiv`s is carried over the `EquivFunctor`.
For plain `Functor`s, this lemma is named `map_map` when applied
or `map_comp_map` when not applied.
-/
@[simp]
/--
theorem `mapEquiv_trans` / 定理 `mapEquiv_trans`

English:
theorem mapEquiv_trans
  given: {γ : Type u₀} (ab : α ≃ β) (bc : β ≃ γ)
  proof: Equiv.ext fun x => by simp [mapEquiv, map_trans']

中文:
定理 mapEquiv_trans
  条件: {γ : 类型u₀} (ab : α ≃ β) (bc : β ≃ γ)
  证明: Equiv.ext fun x => by simp [mapEquiv, map_trans']

Depends on / 依赖: Equiv.ext, mapEquiv, map_trans
-/
theorem mapEquiv_trans {γ : Type u₀} (ab : α ≃ β) (bc : β ≃ γ) :
    (mapEquiv f ab).trans (mapEquiv f bc) = mapEquiv f (ab.trans bc) :=
  Equiv.ext fun x => by simp [mapEquiv, map_trans']

end

instance (priority := 100) ofLawfulFunctor (f : Type u₀ -> Type u₁) [Functor f] [LawfulFunctor f] :
    EquivFunctor f where
  map {_ _} e := Functor.map e
  map_refl' α := by
    ext
    apply LawfulFunctor.id_map
  map_trans' {α β γ} k h := by
    ext x
    apply LawfulFunctor.comp_map k h x

/--
theorem `mapEquiv.injective` / 定理 `mapEquiv.injective`

English:
theorem mapEquiv.injective
  statement: (f : Type u₀ -> Type u₁)
  proof: fun e₁ e₂ H =>
    Equiv.ext fun x => h β (by simpa [EquivFunctor.map] using Equiv.congr_fun H (pure x))

中文:
定理 mapEquiv.injective
  结论: (f : 类型u₀ -> 类型u₁)
  证明: fun e₁ e₂ H =>
    Equiv.ext fun x => h β (by simpa [EquivFunctor.map] using Equiv.congr_fun H (pure x))

Depends on / 依赖: Equiv.congr_fun, Equiv.ext, EquivFunctor, EquivFunctor.map, congr_fun
-/
theorem mapEquiv.injective (f : Type u₀ -> Type u₁)
    [Applicative f] [LawfulApplicative f] {α β : Type u₀}
    (h : forall γ, Function.Injective (pure : γ -> f γ)) :
      Function.Injective (@EquivFunctor.mapEquiv f _ α β) :=
  fun e₁ e₂ H =>
    Equiv.ext fun x => h β (by simpa [EquivFunctor.map] using Equiv.congr_fun H (pure x))

end EquivFunctor
