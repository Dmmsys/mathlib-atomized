/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.Control.Applicative
public import Mathlib.Control.Traversable.Basic
public import Mathlib.Data.List.Forall2
public import Mathlib.Data.Set.Functor

/-!
# LawfulTraversable instances

This file provides instances of `LawfulTraversable` for types from the core library: `Option`,
`List` and `Sum`.
-/

public section


universe u v

section Option

open Functor

variable {F G : Type u -> Type u}
variable [Applicative F] [Applicative G]
variable [LawfulApplicative G]

/--
theorem `Option.id_traverse` / 定理 `Option.id_traverse`

English:
theorem Option.id_traverse
  given: {α} (x : Option α)
  statement: Option.traverse (pure : α -> Id α) x = pure x
  proof: by
  cases x <;> rfl

中文:
定理 选项类型.id_traverse
  条件: {α} (x : 选项类型 α)
  结论: 选项类型.traverse (pure : α -> Id α) x = pure x
  证明: by
  cases x <;> rfl
-/
theorem Option.id_traverse {α} (x : Option α) : Option.traverse (pure : α -> Id α) x = pure x := by
  cases x <;> rfl

/--
theorem `Option.comp_traverse` / 定理 `Option.comp_traverse`

English:
theorem Option.comp_traverse
  given: {α β γ} (f : β -> F γ) (g : α -> G β) (x : Option α)
  proof: by
  cases x <;> (simp [Option.traverse, Option.mapM, functor_norm] <;> rfl)

中文:
定理 选项类型.comp_traverse
  条件: {α β γ} (f : β -> F γ) (g : α -> G β) (x : 选项类型 α)
  证明: by
  cases x <;> (simp [Option.traverse, Option.mapM, functor_norm] <;> rfl)

Depends on / 依赖: Option.mapM, Option.traverse, functor_norm, traverse
-/
theorem Option.comp_traverse {α β γ} (f : β -> F γ) (g : α -> G β) (x : Option α) :
    Option.traverse (Comp.mk ∘ (f <$> ·) ∘ g) x =
      Comp.mk (Option.traverse f <$> Option.traverse g x) := by
  cases x <;> (simp [Option.traverse, Option.mapM, functor_norm] <;> rfl)

/--
theorem `Option.traverse_eq_map_id` / 定理 `Option.traverse_eq_map_id`

English:
theorem Option.traverse_eq_map_id
  given: {α β} (f : α -> β) (x : Option α)
  proof: by cases x <;> rfl

中文:
定理 选项类型.traverse_eq_map_id
  条件: {α β} (f : α -> β) (x : 选项类型 α)
  证明: by cases x <;> rfl
-/
theorem Option.traverse_eq_map_id {α β} (f : α -> β) (x : Option α) :
    Option.traverse ((pure : _ -> Id _) ∘ f) x = (pure : _ -> Id _) (f <$> x) := by cases x <;> rfl

variable (η : ApplicativeTransformation F G)

/--
theorem `Option.naturality` / 定理 `Option.naturality`

English:
theorem Option.naturality
  given: [LawfulApplicative F] {α β} (f : α -> F β) (x : Option α)
  proof: by
  rcases x with - | x <;> simp! [*, functor_norm, Option.traverse]

中文:
定理 选项类型.naturality
  条件: [合法适用 F] {α β} (f : α -> F β) (x : 选项类型 α)
  证明: by
  rcases x with - | x <;> simp! [*, functor_norm, Option.traverse]

Depends on / 依赖: Option.traverse, functor_norm, traverse
-/
theorem Option.naturality [LawfulApplicative F] {α β} (f : α -> F β) (x : Option α) :
    η (Option.traverse f x) = Option.traverse (@η _ ∘ f) x := by
  rcases x with - | x <;> simp! [*, functor_norm, Option.traverse]

end Option

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulTraversable Option
  body: { show LawfulMonad Option from inferInstance with
    id_traverse := Option.id_traverse
    comp_traverse := Option.comp_traverse
    traverse_eq_map_id := Option.traverse_eq_map_id
    naturality := fun η _ _ f x => Option.naturality η f x }

中文:
实例 :
  签名: 合法可遍历 选项类型
  定义体: { show LawfulMonad Option from inferInstance with
    id_traverse := Option.id_traverse
    comp_traverse := Option.comp_traverse
    traverse_eq_map_id := Option.traverse_eq_map_id
    naturality := fun η _ _ f x => Option.naturality η f x }

Depends on / 依赖: LawfulMonad, Option.comp_traverse, Option.id_traverse, Option.naturality, Option.traverse_eq_map_id, comp_traverse, id_traverse, naturality, traverse_eq_map_id
-/
instance : LawfulTraversable Option :=
  { show LawfulMonad Option from inferInstance with
    id_traverse := Option.id_traverse
    comp_traverse := Option.comp_traverse
    traverse_eq_map_id := Option.traverse_eq_map_id
    naturality := fun η _ _ f x => Option.naturality η f x }

namespace List

variable {F G : Type u -> Type u}
variable [Applicative F] [Applicative G]

section

variable [LawfulApplicative G]

open Applicative Functor List

/--
theorem `id_traverse` / 定理 `id_traverse`

English:
theorem id_traverse
  given: {α} (xs : List α)
  statement: (List.traverse pure xs : Id _) = pure xs
  proof: by
  induction xs <;> simp! [*, List.traverse, functor_norm]

中文:
定理 id_traverse
  条件: {α} (xs : 列表 α)
  结论: (列表.traverse pure xs : Id _) = pure xs
  证明: by
  induction xs <;> simp! [*, List.traverse, functor_norm]
-/
protected theorem id_traverse {α} (xs : List α) : (List.traverse pure xs : Id _) = pure xs := by
  induction xs <;> simp! [*, List.traverse, functor_norm]

/--
theorem `comp_traverse` / 定理 `comp_traverse`

English:
theorem comp_traverse
  given: {α β γ} (f : β -> F γ) (g : α -> G β) (x : List α)
  proof: by
  induction x <;> simp! [*, functor_norm] <;> rfl

中文:
定理 comp_traverse
  条件: {α β γ} (f : β -> F γ) (g : α -> G β) (x : 列表 α)
  证明: by
  induction x <;> simp! [*, functor_norm] <;> rfl
-/
protected theorem comp_traverse {α β γ} (f : β -> F γ) (g : α -> G β) (x : List α) :
    List.traverse (Comp.mk ∘ (f <$> ·) ∘ g) x =
    Comp.mk (List.traverse f <$> List.traverse g x) := by
  induction x <;> simp! [*, functor_norm] <;> rfl

/--
theorem `traverse_eq_map_id` / 定理 `traverse_eq_map_id`

English:
theorem traverse_eq_map_id
  given: {α β} (f : α -> β) (x : List α)
  proof: by
  induction x <;> simp! [*, functor_norm]

中文:
定理 traverse_eq_map_id
  条件: {α β} (f : α -> β) (x : 列表 α)
  证明: by
  induction x <;> simp! [*, functor_norm]
-/
protected theorem traverse_eq_map_id {α β} (f : α -> β) (x : List α) :
    List.traverse ((pure : _ -> Id _) ∘ f) x = (pure : _ -> Id _) (f <$> x) := by
  induction x <;> simp! [*, functor_norm]

variable [LawfulApplicative F] (η : ApplicativeTransformation F G)

/--
theorem `naturality` / 定理 `naturality`

English:
theorem naturality
  given: {α β} (f : α -> F β) (x : List α)
  proof: by
  induction x <;> simp! [*, functor_norm]

中文:
定理 naturality
  条件: {α β} (f : α -> F β) (x : 列表 α)
  证明: by
  induction x <;> simp! [*, functor_norm]
-/
protected theorem naturality {α β} (f : α -> F β) (x : List α) :
    η (List.traverse f x) = List.traverse (@η _ ∘ f) x := by
  induction x <;> simp! [*, functor_norm]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulTraversable.{u} List
  body: { show LawfulMonad List from inferInstance with
    id_traverse := List.id_traverse
    comp_traverse := List.comp_traverse
    traverse_eq_map_id := List.traverse_eq_map_id
    naturality := List.naturality }

中文:
实例 :
  签名: 合法可遍历.{u} 列表
  定义体: { show LawfulMonad List from inferInstance with
    id_traverse := List.id_traverse
    comp_traverse := List.comp_traverse
    traverse_eq_map_id := List.traverse_eq_map_id
    naturality := List.naturality }

Depends on / 依赖: LawfulMonad, List.comp_traverse, List.id_traverse, List.naturality, List.traverse_eq_map_id, comp_traverse, id_traverse, naturality, traverse_eq_map_id
-/
instance : LawfulTraversable.{u} List :=
  { show LawfulMonad List from inferInstance with
    id_traverse := List.id_traverse
    comp_traverse := List.comp_traverse
    traverse_eq_map_id := List.traverse_eq_map_id
    naturality := List.naturality }

end

section Traverse

variable {α' β' : Type u} (f : α' -> F β')

@[simp]
/--
theorem `traverse_nil` / 定理 `traverse_nil`

English:
theorem traverse_nil
  statement: traverse f ([] : List α') = (pure [] : F (List β'))
  proof: rfl

@[simp]

中文:
定理 traverse_nil
  结论: traverse f ([] : 列表 α') = (pure [] : F (列表 β'))
  证明: rfl

@[simp]
-/
theorem traverse_nil : traverse f ([] : List α') = (pure [] : F (List β')) :=
  rfl

@[simp]
/--
theorem `traverse_cons` / 定理 `traverse_cons`

English:
theorem traverse_cons
  given: (a : α') (l : List α')
  proof: rfl

中文:
定理 traverse_cons
  条件: (a : α') (l : 列表 α')
  证明: rfl
-/
theorem traverse_cons (a : α') (l : List α') :
traverse f (a :: l) = (· :: ·) < > f a <*> traverse f l :=
  rfl

variable [LawfulApplicative F]

@[simp]
/--
theorem `traverse_append` / 定理 `traverse_append`

English:
theorem traverse_append

中文:
定理 traverse_append
-/
theorem traverse_append :
forall as bs : List α', traverse f (as ++ bs) = (· ++ ·) < > traverse f as <*> traverse f bs
  | [], bs => by simp [functor_norm]
  | a :: as, bs => by simp [traverse_append as bs, functor_norm]; congr

/--
theorem `mem_traverse` / 定理 `mem_traverse`

English:
theorem mem_traverse
  given: {f : α' -> Set β'}

中文:
定理 mem_traverse
  条件: {f : α' -> 集合 β'}
-/
theorem mem_traverse {f : α' -> Set β'} :
    forall (l : List α') (n : List β'), n in traverse f l ↔ Forall₂ (fun b a => b in f a) n l
  | [], [] => by simp
  | a :: as, [] => by simp
  | [], b :: bs => by simp
  | a :: as, b :: bs => by simp [mem_traverse as bs]

end Traverse

end List

namespace Sum

section Traverse

variable {σ : Type u}
variable {F G : Type u -> Type u}
variable [Applicative F] [Applicative G]

open Applicative Functor

/--
theorem `traverse_map` / 定理 `traverse_map`

English:
theorem traverse_map
  given: {α β γ : Type u} (g : α -> β) (f : β -> G γ) (x : σ oplus α)
  proof: by
  cases x <;> simp [Sum.traverse, functor_norm] <;> rfl

中文:
定理 traverse_map
  条件: {α β γ : 类型u} (g : α -> β) (f : β -> G γ) (x : σ oplus α)
  证明: by
  cases x <;> simp [Sum.traverse, functor_norm] <;> rfl
-/
protected theorem traverse_map {α β γ : Type u} (g : α -> β) (f : β -> G γ) (x : σ oplus α) :
    Sum.traverse f (g <$> x) = Sum.traverse (f ∘ g) x := by
  cases x <;> simp [Sum.traverse, functor_norm] <;> rfl

/--
theorem `id_traverse` / 定理 `id_traverse`

English:
theorem id_traverse
  given: {σ α} (x : σ oplus α)
  proof: by cases x <;> rfl

中文:
定理 id_traverse
  条件: {σ α} (x : σ oplus α)
  证明: by cases x <;> rfl
-/
protected theorem id_traverse {σ α} (x : σ oplus α) :
    Sum.traverse (pure : α -> Id α) x = x := by cases x <;> rfl

variable [LawfulApplicative G]

/--
theorem `comp_traverse` / 定理 `comp_traverse`

English:
theorem comp_traverse
  given: {α β γ : Type u} (f : β -> F γ) (g : α -> G β) (x : σ oplus α)
  proof: by
  cases x <;> (simp! [Sum.traverse, map_id, functor_norm] <;> rfl)

中文:
定理 comp_traverse
  条件: {α β γ : 类型u} (f : β -> F γ) (g : α -> G β) (x : σ oplus α)
  证明: by
  cases x <;> (simp! [Sum.traverse, map_id, functor_norm] <;> rfl)
-/
protected theorem comp_traverse {α β γ : Type u} (f : β -> F γ) (g : α -> G β) (x : σ oplus α) :
    Sum.traverse (Comp.mk ∘ (f <$> ·) ∘ g) x =
    Comp.mk.{u} (Sum.traverse f <$> Sum.traverse g x) := by
  cases x <;> (simp! [Sum.traverse, map_id, functor_norm] <;> rfl)

/--
theorem `traverse_eq_map_id` / 定理 `traverse_eq_map_id`

English:
theorem traverse_eq_map_id
  given: {α β} (f : α -> β) (x : σ oplus α)
  proof: by
  induction x <;> simp! [*, functor_norm] <;> rfl

中文:
定理 traverse_eq_map_id
  条件: {α β} (f : α -> β) (x : σ oplus α)
  证明: by
  induction x <;> simp! [*, functor_norm] <;> rfl
-/
protected theorem traverse_eq_map_id {α β} (f : α -> β) (x : σ oplus α) :
    Sum.traverse ((pure : _ -> Id _) ∘ f) x = (pure : _ -> Id _) (f <$> x) := by
  induction x <;> simp! [*, functor_norm] <;> rfl

/--
theorem `map_traverse` / 定理 `map_traverse`

English:
theorem map_traverse
  given: {α β γ} (g : α -> G β) (f : β -> γ) (x : σ oplus α)
  proof: by
  cases x <;> simp [Sum.traverse, functor_norm] <;> congr

中文:
定理 map_traverse
  条件: {α β γ} (g : α -> G β) (f : β -> γ) (x : σ oplus α)
  证明: by
  cases x <;> simp [Sum.traverse, functor_norm] <;> congr
-/
protected theorem map_traverse {α β γ} (g : α -> G β) (f : β -> γ) (x : σ oplus α) :
(f <$> ·) < > Sum.traverse g x = Sum.traverse (f <$> g ·) x := by
  cases x <;> simp [Sum.traverse, functor_norm] <;> congr

variable [LawfulApplicative F] (η : ApplicativeTransformation F G)

/--
theorem `naturality` / 定理 `naturality`

English:
theorem naturality
  given: {α β} (f : α -> F β) (x : σ oplus α)
  proof: by
  cases x <;> simp! [Sum.traverse, functor_norm]

中文:
定理 naturality
  条件: {α β} (f : α -> F β) (x : σ oplus α)
  证明: by
  cases x <;> simp! [Sum.traverse, functor_norm]
-/
protected theorem naturality {α β} (f : α -> F β) (x : σ oplus α) :
    η (Sum.traverse f x) = Sum.traverse (@η _ ∘ f) x := by
  cases x <;> simp! [Sum.traverse, functor_norm]

end Traverse

instance {σ : Type u} : LawfulTraversable.{u} (Sum σ) :=
  { show LawfulMonad (Sum σ) from inferInstance with
    id_traverse := Sum.id_traverse
    comp_traverse := Sum.comp_traverse
    traverse_eq_map_id := Sum.traverse_eq_map_id
    naturality := Sum.naturality }

end Sum
