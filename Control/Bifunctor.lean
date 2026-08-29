/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.Control.Functor
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Attr.Register

/-!
# Functors with two arguments

This file defines bifunctors.

A bifunctor is a function `F : Type* → Type* → Type*` along with a bimap which turns `F α β` into
`F α' β'` given two functions `α → α'` and `β → β'`. It further
* respects the identity: `bimap id id = id`
* composes in the obvious way: `(bimap f' g') ∘ (bimap f g) = bimap (f' ∘ f) (g' ∘ g)`

## Main declarations

* `Bifunctor`: A typeclass for the bare bimap of a bifunctor.
* `LawfulBifunctor`: A typeclass asserting this bimap respects the bifunctor laws.
-/

public section


universe u₀ u₁ u₂ v₀ v₁ v₂

open Function

/--
Definition of `Bifunctor` / `Bifunctor` 的定义

English:
class Bifunctor
  parameters: (F : Type u₀ -> Type u₁ -> Type u₂)
  axioms and operations (1):
    - bimap : forall {α α' β β'}, (α -> α') -> (β -> β') -> F α β -> F α' β'

中文:
类 双函子
  参数: (F : 类型u₀ -> 类型u₁ -> 类型u₂)
  公理与运算 (1 个):
    - bimap : 对任意 {α α' β β'}, (α -> α') -> (β -> β') -> F α β -> F α' β'
-/
class Bifunctor (F : Type u₀ -> Type u₁ -> Type u₂) where
  bimap : forall {α α' β β'}, (α -> α') -> (β -> β') -> F α β -> F α' β'

export Bifunctor (bimap)

/--
Definition of `LawfulBifunctor` / `LawfulBifunctor` 的定义

English:
class LawfulBifunctor
  parameters: (F : Type u₀ -> Type u₁ -> Type u₂) [Bifunctor F]
  axioms and operations (2):
    - id_bimap : forall {α β} (x : F α β), bimap id id x = x
    - bimap_bimap : forall {α₀ α₁ α₂ β₀ β₁ β₂} (f : α₀ -> α₁) (f' : α₁ -> α₂) (g : β₀ -> β₁) (g' : β₁ -> β₂) (x : F α₀ β₀), bimap f' g' (bimap f g x) = bimap (f' ∘ f) (g' ∘ g) x

中文:
类 LawfulBifunctor
  参数: (F : 类型u₀ -> 类型u₁ -> 类型u₂) [双函子 F]
  公理与运算 (2 个):
    - id_bimap : 对任意 {α β} (x : F α β), bimap id id x = x
    - bimap_bimap : 对任意 {α₀ α₁ α₂ β₀ β₁ β₂} (f : α₀ -> α₁) (f' : α₁ -> α₂) (g : β₀ -> β₁) (g' : β₁ -> β₂) (x : F α₀ β₀), bimap f' g' (bimap f g x) = bimap (f' ∘ f) (g' ∘ g) x
-/
class LawfulBifunctor (F : Type u₀ -> Type u₁ -> Type u₂) [Bifunctor F] : Prop where
  id_bimap : forall {α β} (x : F α β), bimap id id x = x
  bimap_bimap :
    forall {α₀ α₁ α₂ β₀ β₁ β₂} (f : α₀ -> α₁) (f' : α₁ -> α₂) (g : β₀ -> β₁) (g' : β₁ -> β₂) (x : F α₀ β₀),
      bimap f' g' (bimap f g x) = bimap (f' ∘ f) (g' ∘ g) x

export LawfulBifunctor (id_bimap bimap_bimap)

attribute [higher_order bimap_id_id] id_bimap

attribute [higher_order bimap_comp_bimap] bimap_bimap

export LawfulBifunctor (bimap_id_id bimap_comp_bimap)

variable {F : Type u₀ -> Type u₁ -> Type u₂} [Bifunctor F]

namespace Bifunctor

/--
Definition of `fst` / `fst` 的定义

English:
abbreviation fst
  signature: {α α' β} (f : α -> α')
  body: bimap f id

中文:
缩写 fst
  签名: {α α' β} (f : α -> α')
  定义体: bimap f id
-/
abbrev fst {α α' β} (f : α -> α') : F α β -> F α' β :=
  bimap f id

/--
Definition of `snd` / `snd` 的定义

English:
abbreviation snd
  signature: {α β β'} (f : β -> β')
  body: bimap id f

中文:
缩写 snd
  签名: {α β β'} (f : β -> β')
  定义体: bimap id f
-/
abbrev snd {α β β'} (f : β -> β') : F α β -> F α β' :=
  bimap id f

variable [LawfulBifunctor F]

@[higher_order fst_id]
/--
theorem `id_fst` / 定理 `id_fst`

English:
theorem id_fst
  statement: forall {α β} (x : F α β), fst id x = x
  proof: @id_bimap _ _ _

@[higher_order snd_id]

中文:
定理 id_fst
  结论: 对任意 {α β} (x : F α β), fst id x = x
  证明: @id_bimap _ _ _

@[higher_order snd_id]

Depends on / 依赖: id_bimap
-/
theorem id_fst : forall {α β} (x : F α β), fst id x = x :=
  @id_bimap _ _ _

@[higher_order snd_id]
/--
theorem `id_snd` / 定理 `id_snd`

English:
theorem id_snd
  statement: forall {α β} (x : F α β), snd id x = x
  proof: @id_bimap _ _ _

@[higher_order fst_comp_fst]

中文:
定理 id_snd
  结论: 对任意 {α β} (x : F α β), snd id x = x
  证明: @id_bimap _ _ _

@[higher_order fst_comp_fst]

Depends on / 依赖: id_bimap
-/
theorem id_snd : forall {α β} (x : F α β), snd id x = x :=
  @id_bimap _ _ _

@[higher_order fst_comp_fst]
/--
theorem `comp_fst` / 定理 `comp_fst`

English:
theorem comp_fst
  given: {α₀ α₁ α₂ β} (f : α₀ -> α₁) (f' : α₁ -> α₂) (x : F α₀ β)
  proof: by simp [fst, bimap_bimap]

@[higher_order fst_comp_snd]

中文:
定理 comp_fst
  条件: {α₀ α₁ α₂ β} (f : α₀ -> α₁) (f' : α₁ -> α₂) (x : F α₀ β)
  证明: by simp [fst, bimap_bimap]

@[higher_order fst_comp_snd]

Depends on / 依赖: bimap_bimap
-/
theorem comp_fst {α₀ α₁ α₂ β} (f : α₀ -> α₁) (f' : α₁ -> α₂) (x : F α₀ β) :
    fst f' (fst f x) = fst (f' ∘ f) x := by simp [fst, bimap_bimap]

@[higher_order fst_comp_snd]
/--
theorem `fst_snd` / 定理 `fst_snd`

English:
theorem fst_snd
  given: {α₀ α₁ β₀ β₁} (f : α₀ -> α₁) (f' : β₀ -> β₁) (x : F α₀ β₀)
  proof: by simp [fst, bimap_bimap]

@[higher_order snd_comp_fst]

中文:
定理 fst_snd
  条件: {α₀ α₁ β₀ β₁} (f : α₀ -> α₁) (f' : β₀ -> β₁) (x : F α₀ β₀)
  证明: by simp [fst, bimap_bimap]

@[higher_order snd_comp_fst]

Depends on / 依赖: bimap_bimap
-/
theorem fst_snd {α₀ α₁ β₀ β₁} (f : α₀ -> α₁) (f' : β₀ -> β₁) (x : F α₀ β₀) :
    fst f (snd f' x) = bimap f f' x := by simp [fst, bimap_bimap]

@[higher_order snd_comp_fst]
/--
theorem `snd_fst` / 定理 `snd_fst`

English:
theorem snd_fst
  given: {α₀ α₁ β₀ β₁} (f : α₀ -> α₁) (f' : β₀ -> β₁) (x : F α₀ β₀)
  proof: by simp [snd, bimap_bimap]

@[higher_order snd_comp_snd]

中文:
定理 snd_fst
  条件: {α₀ α₁ β₀ β₁} (f : α₀ -> α₁) (f' : β₀ -> β₁) (x : F α₀ β₀)
  证明: by simp [snd, bimap_bimap]

@[higher_order snd_comp_snd]

Depends on / 依赖: bimap_bimap
-/
theorem snd_fst {α₀ α₁ β₀ β₁} (f : α₀ -> α₁) (f' : β₀ -> β₁) (x : F α₀ β₀) :
    snd f' (fst f x) = bimap f f' x := by simp [snd, bimap_bimap]

@[higher_order snd_comp_snd]
/--
theorem `comp_snd` / 定理 `comp_snd`

English:
theorem comp_snd
  given: {α β₀ β₁ β₂} (g : β₀ -> β₁) (g' : β₁ -> β₂) (x : F α β₀)
  proof: by simp [snd, bimap_bimap]

中文:
定理 comp_snd
  条件: {α β₀ β₁ β₂} (g : β₀ -> β₁) (g' : β₁ -> β₂) (x : F α β₀)
  证明: by simp [snd, bimap_bimap]

Depends on / 依赖: bimap_bimap
-/
theorem comp_snd {α β₀ β₁ β₂} (g : β₀ -> β₁) (g' : β₁ -> β₂) (x : F α β₀) :
    snd g' (snd g x) = snd (g' ∘ g) x := by simp [snd, bimap_bimap]

attribute [functor_norm]
  bimap_bimap comp_snd comp_fst snd_comp_snd snd_comp_fst fst_comp_snd fst_comp_fst
  bimap_comp_bimap bimap_id_id fst_id snd_id

end Bifunctor

open Functor

/--
Instance `Prod.bifunctor` / 实例 `Prod.bifunctor`

English:
instance Prod.bifunctor
  signature: : Bifunctor Prod where bimap
  body: @Prod.map

中文:
实例 积类型.bifunctor
  签名: : 双函子 积类型 where bimap
  定义体: @Prod.map

Depends on / 依赖: Prod.map
-/
instance Prod.bifunctor : Bifunctor Prod where bimap := @Prod.map

/--
Instance `Prod.lawfulBifunctor` / 实例 `Prod.lawfulBifunctor`

English:
instance Prod.lawfulBifunctor
  signature: : LawfulBifunctor Prod where
  body: rfl
  bimap_bimap _ _ _ _ _ := rfl

中文:
实例 积类型.lawfulBifunctor
  签名: : LawfulBifunctor 积类型 where
  定义体: rfl
  bimap_bimap _ _ _ _ _ := rfl
-/
instance Prod.lawfulBifunctor : LawfulBifunctor Prod where
  id_bimap _ := rfl
  bimap_bimap _ _ _ _ _ := rfl

/--
Instance `Bifunctor.const` / 实例 `Bifunctor.const`

English:
instance Bifunctor.const
  signature: : Bifunctor Const where bimap f _
  body: f

中文:
实例 双函子.const
  签名: : 双函子 Const where bimap f _
  定义体: f
-/
instance Bifunctor.const : Bifunctor Const where bimap f _ := f

/--
Instance `LawfulBifunctor.const` / 实例 `LawfulBifunctor.const`

English:
instance LawfulBifunctor.const
  signature: : LawfulBifunctor Const where
  body: rfl
  bimap_bimap _ _ _ _ _ := rfl

中文:
实例 LawfulBifunctor.const
  签名: : LawfulBifunctor Const where
  定义体: rfl
  bimap_bimap _ _ _ _ _ := rfl
-/
instance LawfulBifunctor.const : LawfulBifunctor Const where
  id_bimap _ := rfl
  bimap_bimap _ _ _ _ _ := rfl

/--
Instance `Bifunctor.flip` / 实例 `Bifunctor.flip`

English:
instance Bifunctor.flip
  signature: : Bifunctor (flip F) where
  body: (bimap f' f x : F β' α')

中文:
实例 双函子.flip
  签名: : 双函子 (flip F) where
  定义体: (bimap f' f x : F β' α')
-/
instance Bifunctor.flip : Bifunctor (flip F) where
  bimap {_α α' _β β'} f f' x := (bimap f' f x : F β' α')

set_option backward.isDefEq.respectTransparency false in
/--
Instance `LawfulBifunctor.flip` / 实例 `LawfulBifunctor.flip`

English:
instance LawfulBifunctor.flip
  signature: [LawfulBifunctor F]
  body: by simp [bimap, functor_norm]
  bimap_bimap := by simp [bimap, functor_norm]

中文:
实例 LawfulBifunctor.flip
  签名: [LawfulBifunctor F]
  定义体: by simp [bimap, functor_norm]
  bimap_bimap := by simp [bimap, functor_norm]

Depends on / 依赖: bimap_bimap, functor_norm
-/
instance LawfulBifunctor.flip [LawfulBifunctor F] : LawfulBifunctor (flip F) where
  id_bimap := by simp [bimap, functor_norm]
  bimap_bimap := by simp [bimap, functor_norm]

/--
Instance `Sum.bifunctor` / 实例 `Sum.bifunctor`

English:
instance Sum.bifunctor
  signature: : Bifunctor Sum where bimap
  body: @Sum.map

中文:
实例 和.bifunctor
  签名: : 双函子 和 where bimap
  定义体: @Sum.map

Depends on / 依赖: Sum.map
-/
instance Sum.bifunctor : Bifunctor Sum where bimap := @Sum.map

/--
Instance `Sum.lawfulBifunctor` / 实例 `Sum.lawfulBifunctor`

English:
instance Sum.lawfulBifunctor
  signature: : LawfulBifunctor Sum where
  body: by aesop
  bimap_bimap := by aesop

中文:
实例 和.lawfulBifunctor
  签名: : LawfulBifunctor 和 where
  定义体: by aesop
  bimap_bimap := by aesop

Depends on / 依赖: bimap_bimap
-/
instance Sum.lawfulBifunctor : LawfulBifunctor Sum where
  id_bimap := by aesop
  bimap_bimap := by aesop

open Bifunctor

instance (priority := 10) Bifunctor.functor {α} : Functor (F α) where map f x := snd f x

instance (priority := 10) Bifunctor.lawfulFunctor [LawfulBifunctor F] {α} :
    LawfulFunctor (F α) where
  id_map := by simp [Functor.map, functor_norm]
  comp_map := by simp [Functor.map, functor_norm]
  map_const := by simp [mapConst, Functor.map]

section Bicompl

variable (G : Type* -> Type u₀) (H : Type* -> Type u₁) [Functor G] [Functor H]

/--
Instance `Function.bicompl.bifunctor` / 实例 `Function.bicompl.bifunctor`

English:
instance Function.bicompl.bifunctor
  signature: : Bifunctor (bicompl F G H) where
  body: (bimap (map f) (map f') x : F (G α') (H β'))

中文:
实例 函数.bicompl.bifunctor
  签名: : 双函子 (bicompl F G H) where
  定义体: (bimap (map f) (map f') x : F (G α') (H β'))
-/
instance Function.bicompl.bifunctor : Bifunctor (bicompl F G H) where
  bimap {_α α' _β β'} f f' x := (bimap (map f) (map f') x : F (G α') (H β'))

set_option backward.isDefEq.respectTransparency false in
/--
Instance `Function.bicompl.lawfulBifunctor` / 实例 `Function.bicompl.lawfulBifunctor`

English:
instance Function.bicompl.lawfulBifunctor
  signature: [LawfulFunctor G] [LawfulFunctor H] [LawfulBifunctor F]
  body: by
  constructor <;> intros <;> simp [bimap, map_id, map_comp_map, functor_norm]

中文:
实例 函数.bicompl.lawfulBifunctor
  签名: [Lawful函子 G] [Lawful函子 H] [LawfulBifunctor F]
  定义体: by
  constructor <;> intros <;> simp [bimap, map_id, map_comp_map, functor_norm]

Depends on / 依赖: functor_norm, intros, map_comp_map, map_id
-/
instance Function.bicompl.lawfulBifunctor [LawfulFunctor G] [LawfulFunctor H] [LawfulBifunctor F] :
    LawfulBifunctor (bicompl F G H) := by
  constructor <;> intros <;> simp [bimap, map_id, map_comp_map, functor_norm]

end Bicompl

section Bicompr

variable (G : Type u₂ -> Type*) [Functor G]

/--
Instance `Function.bicompr.bifunctor` / 实例 `Function.bicompr.bifunctor`

English:
instance Function.bicompr.bifunctor
  signature: : Bifunctor (bicompr G F) where
  body: (map (bimap f f') x : G (F α' β'))

中文:
实例 函数.bicompr.bifunctor
  签名: : 双函子 (bicompr G F) where
  定义体: (map (bimap f f') x : G (F α' β'))
-/
instance Function.bicompr.bifunctor : Bifunctor (bicompr G F) where
  bimap {_α α' _β β'} f f' x := (map (bimap f f') x : G (F α' β'))

set_option backward.isDefEq.respectTransparency false in
/--
Instance `Function.bicompr.lawfulBifunctor` / 实例 `Function.bicompr.lawfulBifunctor`

English:
instance Function.bicompr.lawfulBifunctor
  signature: [LawfulFunctor G] [LawfulBifunctor F]
  body: by
  constructor <;> intros <;> simp [bimap, functor_norm]

中文:
实例 函数.bicompr.lawfulBifunctor
  签名: [Lawful函子 G] [LawfulBifunctor F]
  定义体: by
  constructor <;> intros <;> simp [bimap, functor_norm]

Depends on / 依赖: functor_norm, intros
-/
instance Function.bicompr.lawfulBifunctor [LawfulFunctor G] [LawfulBifunctor F] :
    LawfulBifunctor (bicompr G F) := by
  constructor <;> intros <;> simp [bimap, functor_norm]

end Bicompr
