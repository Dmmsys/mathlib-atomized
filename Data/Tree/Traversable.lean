/-
Copyright (c) 2025 Edward van de Meent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edward van de Meent
-/
module

public import Mathlib.Data.Tree.Basic
public import Mathlib.Control.Applicative
public import Mathlib.Control.Traversable.Basic

/-!
# Traversable Binary Tree

Provides a `Traversable` instance for the `Tree` type.
-/

public section

universe u v w

namespace BinaryTree
section Traverse
variable {α β : Type*}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Traversable BinaryTree
  body: map
  traverse := traverse

中文:
实例 :
  签名: 可遍历 BinaryTree
  定义体: map
  traverse := traverse
-/
instance : Traversable BinaryTree where
  map := map
  traverse := traverse

/--
lemma `comp_traverse` / 引理 `comp_traverse`

English:
lemma comp_traverse
  proof: by
  induction t with
  | nil => rw [traverse, traverse, map_pure, traverse]; rfl
  | node v l r hl hr =>
    rw [traverse]; rw [hl]; rw [hr]; rw [traverse]
    simp only [Function.comp_def, Function.comp_apply, Functor.Comp.map_mk, Functor.map_map,
      Comp.seq_mk, seq_map_assoc, map_seq]
    rfl

中文:
引理 comp_traverse
  证明: by
  induction t with
  | nil => rw [traverse, traverse, map_pure, traverse]; rfl
  | node v l r hl hr =>
    rw [traverse]; rw [hl]; rw [hr]; rw [traverse]
    simp only [Function.comp_def, Function.comp_apply, Functor.Comp.map_mk, Functor.map_map,
      Comp.seq_mk, seq_map_assoc, map_seq]
    rfl

Depends on / 依赖: Comp.seq_mk, Function, Function.comp_apply, Function.comp_def, Functor, Functor.Comp.map_mk, Functor.map_map, comp_apply, comp_def, map_map, map_mk, map_pure, map_seq, seq_map_assoc, seq_mk, traverse
-/
lemma comp_traverse
    {F : Type u -> Type v} {G : Type v -> Type w} [Applicative F] [Applicative G]
    [LawfulApplicative G] {β : Type v} {γ : Type u} (f : β -> F γ) (g : α -> G β)
    (t : BinaryTree α) : t.traverse (Functor.Comp.mk ∘ (f <$> ·) ∘ g) =
      Functor.Comp.mk ((·.traverse f) <$> (t.traverse g)) := by
  induction t with
  | nil => rw [traverse, traverse, map_pure, traverse]; rfl
  | node v l r hl hr =>
    rw [traverse]; rw [hl]; rw [hr]; rw [traverse]
    simp only [Function.comp_def, Function.comp_apply, Functor.Comp.map_mk, Functor.map_map,
      Comp.seq_mk, seq_map_assoc, map_seq]
    rfl

/--
lemma `traverse_eq_map_id` / 引理 `traverse_eq_map_id`

English:
lemma traverse_eq_map_id
  given: (f : α -> β) (t : BinaryTree α)
  proof: by
  induction t with
  | nil => rw [traverse, map]
  | node v l r hl hr =>
    rw [traverse]; rw [map]; rw [hl]; rw [hr]; rw [Function.comp_apply]; rw [map_pure]; rw [pure_seq]; rw [map_pure]; rw [pure_seq]; rw [map_pure]

中文:
引理 traverse_eq_map_id
  条件: (f : α -> β) (t : BinaryTree α)
  证明: by
  induction t with
  | nil => rw [traverse, map]
  | node v l r hl hr =>
    rw [traverse]; rw [map]; rw [hl]; rw [hr]; rw [Function.comp_apply]; rw [map_pure]; rw [pure_seq]; rw [map_pure]; rw [pure_seq]; rw [map_pure]

Depends on / 依赖: Function, Function.comp_apply, comp_apply, map_pure, pure_seq, traverse
-/
lemma traverse_eq_map_id (f : α -> β) (t : BinaryTree α) :
    t.traverse ((pure : β -> Id β) ∘ f) = pure (t.map f) := by
  induction t with
  | nil => rw [traverse, map]
  | node v l r hl hr =>
    rw [traverse]; rw [map]; rw [hl]; rw [hr]; rw [Function.comp_apply]; rw [map_pure]; rw [pure_seq]; rw [map_pure]; rw [pure_seq]; rw [map_pure]

/--
lemma `naturality` / 引理 `naturality`

English:
lemma naturality
  statement: {F G : Type u -> Type*} [Applicative F] [Applicative G] [LawfulApplicative F]
  proof: by
  induction t with
  | nil => rw [traverse, traverse, η.preserves_pure]
  | node v l r hl hr =>
    rw [traverse]; rw [traverse]; rw [η.preserves_seq]; rw [η.preserves_seq]; rw [η.preserves_map]; rw [hl]; rw [hr]; rw [Function.comp_apply]

中文:
引理 naturality
  结论: {F G : 类型u -> 类型} [适用 F] [适用 G] [合法适用 F]
  证明: by
  induction t with
  | nil => rw [traverse, traverse, η.preserves_pure]
  | node v l r hl hr =>
    rw [traverse]; rw [traverse]; rw [η.preserves_seq]; rw [η.preserves_seq]; rw [η.preserves_map]; rw [hl]; rw [hr]; rw [Function.comp_apply]

Depends on / 依赖: Function, Function.comp_apply, comp_apply, preserves_map, preserves_pure, preserves_seq, traverse
-/
lemma naturality {F G : Type u -> Type*} [Applicative F] [Applicative G] [LawfulApplicative F]
    [LawfulApplicative G] (η : ApplicativeTransformation F G) {β : Type u} (f : α -> F β)
    (t : BinaryTree α) : η (t.traverse f) = t.traverse (η.app β ∘ f : α -> G β) := by
  induction t with
  | nil => rw [traverse, traverse, η.preserves_pure]
  | node v l r hl hr =>
    rw [traverse]; rw [traverse]; rw [η.preserves_seq]; rw [η.preserves_seq]; rw [η.preserves_map]; rw [hl]; rw [hr]; rw [Function.comp_apply]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulTraversable BinaryTree
  body: rfl
  id_map := id_map
  comp_map := comp_map
  id_traverse t := traverse_pure t
  comp_traverse := comp_traverse
  traverse_eq_map_id := traverse_eq_map_id
  naturality η := naturality η

中文:
实例 :
  签名: 合法可遍历 BinaryTree
  定义体: rfl
  id_map := id_map
  comp_map := comp_map
  id_traverse t := traverse_pure t
  comp_traverse := comp_traverse
  traverse_eq_map_id := traverse_eq_map_id
  naturality η := naturality η
-/
instance : LawfulTraversable BinaryTree where
  map_const := rfl
  id_map := id_map
  comp_map := comp_map
  id_traverse t := traverse_pure t
  comp_traverse := comp_traverse
  traverse_eq_map_id := traverse_eq_map_id
  naturality η := naturality η

end Traverse

end BinaryTree
