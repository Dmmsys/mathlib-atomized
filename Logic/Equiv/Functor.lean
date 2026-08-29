/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Simon Hudon, Kim Morrison
-/
module

public import Mathlib.Control.Bifunctor
public import Mathlib.Logic.Equiv.Defs

/-!
# Functor and bifunctors can be applied to `Equiv`s.

We define
```lean
def Functor.mapEquiv (f : Type u → Type v) [Functor f] [LawfulFunctor f] :
    α ≃ β → f α ≃ f β
```
and
```lean
def Bifunctor.mapEquiv (F : Type u → Type v → Type w) [Bifunctor F] [LawfulBifunctor F] :
    α ≃ β → α' ≃ β' → F α α' ≃ F β β'
```
-/

@[expose] public section


universe u v w

variable {α β : Type u}

open Equiv

namespace Functor

variable (f : Type u -> Type v) [Functor f] [LawfulFunctor f]

/--
Definition of `mapEquiv` / `mapEquiv` 的定义

English:
definition mapEquiv
  signature: (h : α ≃ β)
  body: map h
  invFun := map h.symm
  left_inv x := by simp [map_map]
  right_inv x := by simp [map_map]

@[simp]

中文:
定义 mapEquiv
  签名: (h : α ≃ β)
  定义体: map h
  invFun := map h.symm
  left_inv x := by simp [map_map]
  right_inv x := by simp [map_map]

@[simp]
-/
def mapEquiv (h : α ≃ β) : f α ≃ f β where
  toFun := map h
  invFun := map h.symm
  left_inv x := by simp [map_map]
  right_inv x := by simp [map_map]

@[simp]
/--
theorem `mapEquiv_apply` / 定理 `mapEquiv_apply`

English:
theorem mapEquiv_apply
  given: (h : α ≃ β) (x : f α)
  statement: (mapEquiv f h : f α ≃ f β) x = map h x
  proof: rfl

@[simp]

中文:
定理 mapEquiv_apply
  条件: (h : α ≃ β) (x : f α)
  结论: (mapEquiv f h : f α ≃ f β) x = map h x
  证明: rfl

@[simp]
-/
theorem mapEquiv_apply (h : α ≃ β) (x : f α) : (mapEquiv f h : f α ≃ f β) x = map h x :=
  rfl

@[simp]
/--
theorem `mapEquiv_symm_apply` / 定理 `mapEquiv_symm_apply`

English:
theorem mapEquiv_symm_apply
  given: (h : α ≃ β) (y : f β)
  proof: rfl

@[simp]

中文:
定理 mapEquiv_symm_apply
  条件: (h : α ≃ β) (y : f β)
  证明: rfl

@[simp]
-/
theorem mapEquiv_symm_apply (h : α ≃ β) (y : f β) :
    (mapEquiv f h : f α ≃ f β).symm y = map h.symm y :=
  rfl

@[simp]
/--
theorem `mapEquiv_refl` / 定理 `mapEquiv_refl`

English:
theorem mapEquiv_refl
  statement: mapEquiv f (Equiv.refl α) = Equiv.refl (f α)
  proof: by
  ext x
  simp only [mapEquiv_apply, refl_apply]
  exact LawfulFunctor.id_map x

中文:
定理 mapEquiv_refl
  结论: mapEquiv f (Equiv.refl α) = Equiv.refl (f α)
  证明: by
  ext x
  simp only [mapEquiv_apply, refl_apply]
  exact LawfulFunctor.id_map x

Depends on / 依赖: LawfulFunctor, LawfulFunctor.id_map, id_map, mapEquiv_apply, refl_apply
-/
theorem mapEquiv_refl : mapEquiv f (Equiv.refl α) = Equiv.refl (f α) := by
  ext x
  simp only [mapEquiv_apply, refl_apply]
  exact LawfulFunctor.id_map x

end Functor

namespace Bifunctor

variable {α' β' : Type v} (F : Type u -> Type v -> Type w) [Bifunctor F] [LawfulBifunctor F]

/--
Definition of `mapEquiv` / `mapEquiv` 的定义

English:
definition mapEquiv
  signature: (h : α ≃ β) (h' : α' ≃ β')
  body: bimap h h'
  invFun := bimap h.symm h'.symm
  left_inv x := by simp [bimap_bimap, id_bimap]
  right_inv x := by simp [bimap_bimap, id_bimap]

@[simp]

中文:
定义 mapEquiv
  签名: (h : α ≃ β) (h' : α' ≃ β')
  定义体: bimap h h'
  invFun := bimap h.symm h'.symm
  left_inv x := by simp [bimap_bimap, id_bimap]
  right_inv x := by simp [bimap_bimap, id_bimap]

@[simp]
-/
def mapEquiv (h : α ≃ β) (h' : α' ≃ β') : F α α' ≃ F β β' where
  toFun := bimap h h'
  invFun := bimap h.symm h'.symm
  left_inv x := by simp [bimap_bimap, id_bimap]
  right_inv x := by simp [bimap_bimap, id_bimap]

@[simp]
/--
theorem `mapEquiv_apply` / 定理 `mapEquiv_apply`

English:
theorem mapEquiv_apply
  given: (h : α ≃ β) (h' : α' ≃ β') (x : F α α')
  proof: rfl

@[simp]

中文:
定理 mapEquiv_apply
  条件: (h : α ≃ β) (h' : α' ≃ β') (x : F α α')
  证明: rfl

@[simp]
-/
theorem mapEquiv_apply (h : α ≃ β) (h' : α' ≃ β') (x : F α α') :
    (mapEquiv F h h' : F α α' ≃ F β β') x = bimap h h' x :=
  rfl

@[simp]
/--
theorem `mapEquiv_symm_apply` / 定理 `mapEquiv_symm_apply`

English:
theorem mapEquiv_symm_apply
  given: (h : α ≃ β) (h' : α' ≃ β') (y : F β β')
  proof: rfl

@[simp]

中文:
定理 mapEquiv_symm_apply
  条件: (h : α ≃ β) (h' : α' ≃ β') (y : F β β')
  证明: rfl

@[simp]
-/
theorem mapEquiv_symm_apply (h : α ≃ β) (h' : α' ≃ β') (y : F β β') :
    (mapEquiv F h h' : F α α' ≃ F β β').symm y = bimap h.symm h'.symm y :=
  rfl

@[simp]
/--
theorem `mapEquiv_refl_refl` / 定理 `mapEquiv_refl_refl`

English:
theorem mapEquiv_refl_refl
  statement: mapEquiv F (Equiv.refl α) (Equiv.refl α') = Equiv.refl (F α α')
  proof: by
  ext x
  simp [id_bimap]

中文:
定理 mapEquiv_refl_refl
  结论: mapEquiv F (Equiv.refl α) (Equiv.refl α') = Equiv.refl (F α α')
  证明: by
  ext x
  simp [id_bimap]

Depends on / 依赖: id_bimap
-/
theorem mapEquiv_refl_refl : mapEquiv F (Equiv.refl α) (Equiv.refl α') = Equiv.refl (F α α') := by
  ext x
  simp [id_bimap]

end Bifunctor
