/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.Control.Bitraversable.Lemmas
public import Mathlib.Control.Traversable.Lemmas

/-!
# Bitraversable instances

This file provides `Bitraversable` instances for concrete bifunctors:
* `Prod`
* `Sum`
* `Functor.Const`
* `flip`
* `Function.bicompl`
* `Function.bicompr`

## References

* Hackage: <https://hackage.haskell.org/package/base-4.12.0.0/docs/Data-Bitraversable.html>

## Tags

traversable bitraversable functor bifunctor applicative
-/

@[expose] public section


universe u v w

variable {t : Type u -> Type u -> Type u} [Bitraversable t]

section

variable {F : Type u -> Type u} [Applicative F]

/--
Definition of `Prod.bitraverse` / `Prod.bitraverse` 的定义

English:
definition Prod.bitraverse
  signature: {α α' β β'} (f : α -> F α') (f' : β -> F β')

中文:
定义 积类型.bitraverse
  签名: {α α' β β'} (f : α -> F α') (f' : β -> F β')
-/
def Prod.bitraverse {α α' β β'} (f : α -> F α') (f' : β -> F β') : α × β -> F (α' × β')
| (x, y) => Prod.mk < > f x <*> f' y

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bitraversable Prod
  body: @Prod.bitraverse

中文:
实例 :
  签名: Bitraversable 积类型
  定义体: @Prod.bitraverse

Depends on / 依赖: Prod.bitraverse, bitraverse
-/
instance : Bitraversable Prod where bitraverse := @Prod.bitraverse

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulBitraversable Prod
  body: by
  constructor <;> intros <;> casesm _ × _ <;>
    simp [bitraverse, Prod.bitraverse, functor_norm] <;> rfl

中文:
实例 :
  签名: LawfulBitraversable 积类型
  定义体: by
  constructor <;> intros <;> casesm _ × _ <;>
    simp [bitraverse, Prod.bitraverse, functor_norm] <;> rfl

Depends on / 依赖: Prod.bitraverse, bitraverse, casesm, functor_norm, intros
-/
instance : LawfulBitraversable Prod := by
  constructor <;> intros <;> casesm _ × _ <;>
    simp [bitraverse, Prod.bitraverse, functor_norm] <;> rfl

open Functor

/--
Definition of `Sum.bitraverse` / `Sum.bitraverse` 的定义

English:
definition Sum.bitraverse
  signature: {α α' β β'} (f : α -> F α') (f' : β -> F β')

中文:
定义 和.bitraverse
  签名: {α α' β β'} (f : α -> F α') (f' : β -> F β')
-/
def Sum.bitraverse {α α' β β'} (f : α -> F α') (f' : β -> F β') : α oplus β -> F (α' oplus β')
| Sum.inl x => Sum.inl < > f x
| Sum.inr x => Sum.inr < > f' x

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bitraversable Sum
  body: @Sum.bitraverse

中文:
实例 :
  签名: Bitraversable 和
  定义体: @Sum.bitraverse

Depends on / 依赖: Sum.bitraverse, bitraverse
-/
instance : Bitraversable Sum where bitraverse := @Sum.bitraverse

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulBitraversable Sum
  body: by
  constructor <;> intros <;> casesm _ oplus _ <;>
    simp [bitraverse, Sum.bitraverse, functor_norm] <;> rfl

中文:
实例 :
  签名: LawfulBitraversable 和
  定义体: by
  constructor <;> intros <;> casesm _ oplus _ <;>
    simp [bitraverse, Sum.bitraverse, functor_norm] <;> rfl

Depends on / 依赖: Sum.bitraverse, bitraverse, casesm, functor_norm, intros
-/
instance : LawfulBitraversable Sum := by
  constructor <;> intros <;> casesm _ oplus _ <;>
    simp [bitraverse, Sum.bitraverse, functor_norm] <;> rfl


set_option linter.unusedVariables false in
/-- The bitraverse function for `Const`. It throws away the second map. -/
@[nolint unusedArguments]
/--
Definition of `Const.bitraverse` / `Const.bitraverse` 的定义

English:
definition Const.bitraverse
  signature: {F : Type u -> Type u} [Applicative F] {α α' β β'} (f : α -> F α')
  body: f

中文:
定义 Const.bitraverse
  签名: {F : 类型u -> 类型u} [适用 F] {α α' β β'} (f : α -> F α')
  定义体: f
-/
def Const.bitraverse {F : Type u -> Type u} [Applicative F] {α α' β β'} (f : α -> F α')
    (f' : β -> F β') : Const α β -> F (Const α' β') :=
  f

/--
Instance `Bitraversable.const` / 实例 `Bitraversable.const`

English:
instance Bitraversable.const
  signature: : Bitraversable Const where bitraverse
  body: @Const.bitraverse

中文:
实例 Bitraversable.const
  签名: : Bitraversable Const where bitraverse
  定义体: @Const.bitraverse

Depends on / 依赖: Const.bitraverse, bitraverse
-/
instance Bitraversable.const : Bitraversable Const where bitraverse := @Const.bitraverse

/--
Instance `LawfulBitraversable.const` / 实例 `LawfulBitraversable.const`

English:
instance LawfulBitraversable.const
  signature: : LawfulBitraversable Const
  body: by
  constructor <;> intros <;> simp [bitraverse, Const.bitraverse, functor_norm] <;> rfl

中文:
实例 LawfulBitraversable.const
  签名: : LawfulBitraversable Const
  定义体: by
  constructor <;> intros <;> simp [bitraverse, Const.bitraverse, functor_norm] <;> rfl

Depends on / 依赖: Const.bitraverse, bitraverse, functor_norm, intros
-/
instance LawfulBitraversable.const : LawfulBitraversable Const := by
  constructor <;> intros <;> simp [bitraverse, Const.bitraverse, functor_norm] <;> rfl

/-- The bitraverse function for `flip`. -/
nonrec def flip.bitraverse {α α' β β'} (f : α -> F α') (f' : β -> F β') :
    flip t α β -> F (flip t α' β') :=
  (bitraverse f' f : t β α -> F (t β' α'))

/--
Instance `Bitraversable.flip` / 实例 `Bitraversable.flip`

English:
instance Bitraversable.flip
  signature: : Bitraversable (flip t) where bitraverse
  body: @flip.bitraverse t _

中文:
实例 Bitraversable.flip
  签名: : Bitraversable (flip t) where bitraverse
  定义体: @flip.bitraverse t _

Depends on / 依赖: bitraverse, flip.bitraverse
-/
instance Bitraversable.flip : Bitraversable (flip t) where bitraverse := @flip.bitraverse t _

open LawfulBitraversable

/--
Instance `LawfulBitraversable.flip` / 实例 `LawfulBitraversable.flip`

English:
instance LawfulBitraversable.flip
  signature: [LawfulBitraversable t]
  body: by
  constructor <;> intros <;> casesm LawfulBitraversable t <;> apply_assumption only [*]

中文:
实例 LawfulBitraversable.flip
  签名: [LawfulBitraversable t]
  定义体: by
  constructor <;> intros <;> casesm LawfulBitraversable t <;> apply_assumption only [*]

Depends on / 依赖: LawfulBitraversable, apply_assumption, casesm, intros
-/
instance LawfulBitraversable.flip [LawfulBitraversable t] : LawfulBitraversable (flip t) := by
  constructor <;> intros <;> casesm LawfulBitraversable t <;> apply_assumption only [*]

open Bitraversable

instance (priority := 10) Bitraversable.traversable {α} : Traversable (t α) where
  traverse := @tsnd t _ _

instance (priority := 10) Bitraversable.isLawfulTraversable [LawfulBitraversable t] {α} :
    LawfulTraversable (t α) := by
  constructor <;> intros <;>
    simp [traverse, comp_tsnd, functor_norm]
  · simp [tsnd_eq_snd_id, (· <$> ·)]
  · simp [tsnd, binaturality, Function.comp_def, functor_norm]

end

open Bifunctor Traversable LawfulTraversable LawfulBitraversable

open Function (bicompl bicompr)

section Bicompl

variable (F G : Type u -> Type u) [Traversable F] [Traversable G]

/-- The bitraverse function for `bicompl`. -/
nonrec def Bicompl.bitraverse {m} [Applicative m] {α β α' β'} (f : α -> m β) (f' : α' -> m β') :
    bicompl t F G α α' -> m (bicompl t F G β β') :=
  (bitraverse (traverse f) (traverse f') : t (F α) (G α') -> m _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bitraversable (bicompl t F G)
  body: @Bicompl.bitraverse t _ F G _ _

中文:
实例 :
  签名: Bitraversable (bicompl t F G)
  定义体: @Bicompl.bitraverse t _ F G _ _

Depends on / 依赖: Bicompl, Bicompl.bitraverse, bitraverse
-/
instance : Bitraversable (bicompl t F G) where bitraverse := @Bicompl.bitraverse t _ F G _ _

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LawfulTraversable
  signature: F] [LawfulTraversable G] [LawfulBitraversable t] :
  body: by
  constructor <;> intros <;>
    simp [bitraverse, Bicompl.bitraverse, bimap, traverse_id, bitraverse_id_id, comp_bitraverse,
      functor_norm]
  · simp [traverse_eq_map_id', bitraverse_eq_bimap_id]
  · dsimp only [bicompl]
    simp [binaturality, naturality_pf]

中文:
实例 [合法可遍历
  签名: F] [合法可遍历 G] [LawfulBitraversable t] :
  定义体: by
  constructor <;> intros <;>
    simp [bitraverse, Bicompl.bitraverse, bimap, traverse_id, bitraverse_id_id, comp_bitraverse,
      functor_norm]
  · simp [traverse_eq_map_id', bitraverse_eq_bimap_id]
  · dsimp only [bicompl]
    simp [binaturality, naturality_pf]

Depends on / 依赖: Bicompl, Bicompl.bitraverse, bicompl, binaturality, bitraverse, bitraverse_eq_bimap_id, bitraverse_id_id, comp_bitraverse, functor_norm, intros, naturality_pf, traverse_eq_map_id, traverse_id
-/
instance [LawfulTraversable F] [LawfulTraversable G] [LawfulBitraversable t] :
    LawfulBitraversable (bicompl t F G) := by
  constructor <;> intros <;>
    simp [bitraverse, Bicompl.bitraverse, bimap, traverse_id, bitraverse_id_id, comp_bitraverse,
      functor_norm]
  · simp [traverse_eq_map_id', bitraverse_eq_bimap_id]
  · dsimp only [bicompl]
    simp [binaturality, naturality_pf]

end Bicompl

section Bicompr

variable (F : Type u -> Type u) [Traversable F]

/-- The bitraverse function for `bicompr`. -/
nonrec def Bicompr.bitraverse {m} [Applicative m] {α β α' β'} (f : α -> m β) (f' : α' -> m β') :
    bicompr F t α α' -> m (bicompr F t β β') :=
  (traverse (bitraverse f f') : F (t α α') -> m _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bitraversable (bicompr F t)
  body: @Bicompr.bitraverse t _ F _

中文:
实例 :
  签名: Bitraversable (bicompr F t)
  定义体: @Bicompr.bitraverse t _ F _

Depends on / 依赖: Bicompr, Bicompr.bitraverse, bitraverse
-/
instance : Bitraversable (bicompr F t) where bitraverse := @Bicompr.bitraverse t _ F _

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LawfulTraversable
  signature: F] [LawfulBitraversable t] : LawfulBitraversable (bicompr F t)
  body: by
  constructor <;> intros <;>
    simp [bitraverse, Bicompr.bitraverse, bitraverse_id_id, functor_norm]
  · simp only [bitraverse_eq_bimap_id', traverse_eq_map_id', Function.comp_apply]; rfl
  · dsimp only [bicompr]
    simp [naturality, binaturality']

中文:
实例 [合法可遍历
  签名: F] [LawfulBitraversable t] : LawfulBitraversable (bicompr F t)
  定义体: by
  constructor <;> intros <;>
    simp [bitraverse, Bicompr.bitraverse, bitraverse_id_id, functor_norm]
  · simp only [bitraverse_eq_bimap_id', traverse_eq_map_id', Function.comp_apply]; rfl
  · dsimp only [bicompr]
    simp [naturality, binaturality']

Depends on / 依赖: Bicompr, Bicompr.bitraverse, Function, Function.comp_apply, bicompr, binaturality, bitraverse, bitraverse_eq_bimap_id, bitraverse_id_id, comp_apply, functor_norm, intros, naturality, traverse_eq_map_id
-/
instance [LawfulTraversable F] [LawfulBitraversable t] : LawfulBitraversable (bicompr F t) := by
  constructor <;> intros <;>
    simp [bitraverse, Bicompr.bitraverse, bitraverse_id_id, functor_norm]
  · simp only [bitraverse_eq_bimap_id', traverse_eq_map_id', Function.comp_apply]; rfl
  · dsimp only [bicompr]
    simp [naturality, binaturality']

end Bicompr
