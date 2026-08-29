/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Simon Hudon, Kenny Lau
-/
module

public import Mathlib.Data.Multiset.Bind
public import Mathlib.Control.Traversable.Lemmas
public import Mathlib.Control.Traversable.Instances

/-!
# Functoriality of `Multiset`.
-/

@[expose] public section


universe u

namespace Multiset

open List

/--
Instance `functor` / 实例 `functor`

English:
instance functor
  signature: : Functor Multiset where map
  body: @map

@[simp]

中文:
实例 functor
  签名: : Functor Multiset where map
  定义体: @map

@[simp]
-/
instance functor : Functor Multiset where map := @map

@[simp]
/--
theorem `fmap_def` / 定理 `fmap_def`

English:
theorem fmap_def
  given: {α' β'} {s : Multiset α'} (f : α' -> β')
  statement: f < > s = s.map f
  proof: rfl

中文:
定理 fmap_def
  条件: {α' β'} {s : Multiset α'} (f : α' -> β')
  结论: f < > s = s.map f
  证明: rfl
-/
theorem fmap_def {α' β'} {s : Multiset α'} (f : α' -> β') : f < > s = s.map f :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulFunctor Multiset
  body: by simp
  comp_map := by simp
  map_const {_ _} := rfl

中文:
实例 :
  签名: LawfulFunctor Multiset
  定义体: by simp
  comp_map := by simp
  map_const {_ _} := rfl

Depends on / 依赖: comp_map, map_const
-/
instance : LawfulFunctor Multiset where
  id_map := by simp
  comp_map := by simp
  map_const {_ _} := rfl

open LawfulTraversable CommApplicative

variable {F : Type u -> Type u} [Applicative F] [CommApplicative F]
variable {α' β' : Type u} (f : α' -> F β')

/--
Definition of `traverse` / `traverse` 的定义

English:
definition traverse
  signature: : Multiset α' -> F (Multiset β')
  body: by
  refine Quotient.lift (Functor.map ofList ∘ Traversable.traverse f) ?_
  introv p; unfold Function.comp
  induction p with
  | nil => rfl
  | @cons x l₁ l₂ _ h =>
    have :
Multiset.cons < > f x <*> ofList < > Traversable.traverse f l₁ =
Multiset.cons < > f x <*> ofList < > Traversable.traverse

中文:
定义 traverse
  签名: : Multiset α' -> F (Multiset β')
  定义体: by
  refine Quotient.lift (Functor.map ofList ∘ Traversable.traverse f) ?_
  introv p; unfold Function.comp
  induction p with
  | nil => rfl
  | @cons x l₁ l₂ _ h =>
    have :
Multiset.cons < > f x <*> ofList < > Traversable.traverse f l₁ =
Multiset.cons < > f x <*> ofList < > Traversable.traverse

Depends on / 依赖: CommApp, Function, Function.comp, Functor, Functor.map, Multiset, Multiset.cons, Quotient, Quotient.lift, Traversable, Traversable.traverse, functor_norm, introv, ofList, traverse
-/
def traverse : Multiset α' -> F (Multiset β') := by
  refine Quotient.lift (Functor.map ofList ∘ Traversable.traverse f) ?_
  introv p; unfold Function.comp
  induction p with
  | nil => rfl
  | @cons x l₁ l₂ _ h =>
    have :
Multiset.cons < > f x <*> ofList < > Traversable.traverse f l₁ =
Multiset.cons < > f x <*> ofList < > Traversable.traverse f l₂ := by
      rw [h]
    simpa [functor_norm] using! this
  | swap x y l =>
    have :
(fun a b (l : List β') => (↑(a :: b :: l) : Multiset β')) < > f y <*> f x =
(fun a b l => ↑(a :: b :: l)) < > f x <*> f y := by
      rw [CommApplicative.commutative_map]
      congr 2
      funext a b l
      simpa [flip] using! Perm.swap a b l
    simp [Function.comp_def, this, functor_norm]
  | trans => simp [*]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Monad Multiset
  body: { Multiset.functor with
    pure := fun x => {x}
    bind := @bind }

@[simp]

中文:
实例 :
  签名: Monad Multiset
  定义体: { Multiset.functor with
    pure := fun x => {x}
    bind := @bind }

@[simp]

Depends on / 依赖: Multiset, Multiset.functor, functor
-/
instance : Monad Multiset :=
  { Multiset.functor with
    pure := fun x => {x}
    bind := @bind }

@[simp]
/--
theorem `pure_def` / 定理 `pure_def`

English:
theorem pure_def
  given: {α}
  statement: (pure : α -> Multiset α) = singleton
  proof: rfl

@[simp]

中文:
定理 pure_def
  条件: {α}
  结论: (pure : α -> Multiset α) = singleton
  证明: rfl

@[simp]
-/
theorem pure_def {α} : (pure : α -> Multiset α) = singleton :=
  rfl

@[simp]
/--
theorem `bind_def` / 定理 `bind_def`

English:
theorem bind_def
  given: {α β}
  statement: (· >>= ·) = @bind α β
  proof: rfl

中文:
定理 bind_def
  条件: {α β}
  结论: (· >>= ·) = @bind α β
  证明: rfl
-/
theorem bind_def {α β} : (· >>= ·) = @bind α β :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulMonad Multiset
  body: LawfulMonad.mk'
  (bind_pure_comp := fun _ _ => by simp only [pure_def, bind_def, bind_singleton, fmap_def])
  (id_map := fun _ => by simp only [fmap_def, id_eq, map_id'])
  (pure_bind := fun _ _ => by simp only [pure_def, bind_def, singleton_bind])
  (bind_assoc := @bind_assoc)

中文:
实例 :
  签名: LawfulMonad Multiset
  定义体: LawfulMonad.mk'
  (bind_pure_comp := fun _ _ => by simp only [pure_def, bind_def, bind_singleton, fmap_def])
  (id_map := fun _ => by simp only [fmap_def, id_eq, map_id'])
  (pure_bind := fun _ _ => by simp only [pure_def, bind_def, singleton_bind])
  (bind_assoc := @bind_assoc)

Depends on / 依赖: LawfulMonad, LawfulMonad.mk
-/
instance : LawfulMonad Multiset := LawfulMonad.mk'
  (bind_pure_comp := fun _ _ => by simp only [pure_def, bind_def, bind_singleton, fmap_def])
  (id_map := fun _ => by simp only [fmap_def, id_eq, map_id'])
  (pure_bind := fun _ _ => by simp only [pure_def, bind_def, singleton_bind])
  (bind_assoc := @bind_assoc)

open Functor

open Traversable

@[simp]
/--
theorem `map_comp_coe` / 定理 `map_comp_coe`

English:
theorem map_comp_coe
  given: {α β} (h : α -> β)
  proof: by
  funext; simp only [Function.comp_apply, fmap_def, map_coe, List.map_eq_map]

中文:
定理 map_comp_coe
  条件: {α β} (h : α -> β)
  证明: by
  funext; simp only [Function.comp_apply, fmap_def, map_coe, List.map_eq_map]

Depends on / 依赖: Function, Function.comp_apply, List.map_eq_map, comp_apply, fmap_def, map_coe, map_eq_map
-/
theorem map_comp_coe {α β} (h : α -> β) :
    Functor.map h ∘ ofList = (ofList ∘ Functor.map h : List α -> Multiset β) := by
  funext; simp only [Function.comp_apply, fmap_def, map_coe, List.map_eq_map]

/--
theorem `id_traverse` / 定理 `id_traverse`

English:
theorem id_traverse
  given: {α : Type*} (x : Multiset α)
  statement: traverse (pure : α -> Id α) x = pure x
  proof: by
  induction x using Quotient.inductionOn
  simp [traverse]

中文:
定理 id_traverse
  条件: {α : 类型} (x : Multiset α)
  结论: traverse (pure : α -> Id α) x = pure x
  证明: by
  induction x using Quotient.inductionOn
  simp [traverse]

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn, traverse
-/
theorem id_traverse {α : Type*} (x : Multiset α) : traverse (pure : α -> Id α) x = pure x := by
  induction x using Quotient.inductionOn
  simp [traverse]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `comp_traverse` / 定理 `comp_traverse`

English:
theorem comp_traverse
  statement: {G H : Type _ -> Type _} [Applicative G] [Applicative H] [CommApplicative G]
  proof: by
  induction x using Quotient.inductionOn
  simp only [traverse, quot_mk_to_coe, lift_coe, Function.comp_apply, Functor.map_map, functor_norm]

中文:
定理 comp_traverse
  结论: {G H : Type _ -> Type _} [Applicative G] [Applicative H] [CommApplicative G]
  证明: by
  induction x using Quotient.inductionOn
  simp only [traverse, quot_mk_to_coe, lift_coe, Function.comp_apply, Functor.map_map, functor_norm]

Depends on / 依赖: Function, Function.comp_apply, Functor, Functor.map_map, Quotient, Quotient.inductionOn, comp_apply, functor_norm, inductionOn, lift_coe, map_map, quot_mk_to_coe, traverse
-/
theorem comp_traverse {G H : Type _ -> Type _} [Applicative G] [Applicative H] [CommApplicative G]
    [CommApplicative H] {α β γ : Type _} (g : α -> G β) (h : β -> H γ) (x : Multiset α) :
    traverse (Comp.mk ∘ Functor.map h ∘ g) x =
    Comp.mk (Functor.map (traverse h) (traverse g x)) := by
  induction x using Quotient.inductionOn
  simp only [traverse, quot_mk_to_coe, lift_coe, Function.comp_apply, Functor.map_map, functor_norm]

/--
theorem `map_traverse` / 定理 `map_traverse`

English:
theorem map_traverse
  statement: {G : Type* -> Type _} [Applicative G] [CommApplicative G] {α β γ : Type _}
  proof: by
  induction x using Quotient.inductionOn
  simp only [traverse, quot_mk_to_coe, lift_coe, Function.comp_apply, Functor.map_map]
  rw [Traversable.map_traverse']
  simp only [fmap_def, Function.comp_apply, Functor.map_map, List.map_eq_map, map_coe]

中文:
定理 map_traverse
  结论: {G : 类型 -> Type _} [Applicative G] [CommApplicative G] {α β γ : Type _}
  证明: by
  induction x using Quotient.inductionOn
  simp only [traverse, quot_mk_to_coe, lift_coe, Function.comp_apply, Functor.map_map]
  rw [Traversable.map_traverse']
  simp only [fmap_def, Function.comp_apply, Functor.map_map, List.map_eq_map, map_coe]

Depends on / 依赖: Function, Function.comp_apply, Functor, Functor.map_map, List.map_eq_map, Quotient, Quotient.inductionOn, Traversable, Traversable.map_traverse, comp_apply, fmap_def, inductionOn, lift_coe, map_coe, map_eq_map, map_map, map_traverse, quot_mk_to_coe, traverse
-/
theorem map_traverse {G : Type* -> Type _} [Applicative G] [CommApplicative G] {α β γ : Type _}
    (g : α -> G β) (h : β -> γ) (x : Multiset α) :
    Functor.map (Functor.map h) (traverse g x) = traverse (Functor.map h ∘ g) x := by
  induction x using Quotient.inductionOn
  simp only [traverse, quot_mk_to_coe, lift_coe, Function.comp_apply, Functor.map_map]
  rw [Traversable.map_traverse']
  simp only [fmap_def, Function.comp_apply, Functor.map_map, List.map_eq_map, map_coe]

/--
theorem `traverse_map` / 定理 `traverse_map`

English:
theorem traverse_map
  statement: {G : Type* -> Type _} [Applicative G] [CommApplicative G] {α β γ : Type _}
  proof: by
  induction x using Quotient.inductionOn
  simp only [traverse, quot_mk_to_coe, map_coe, lift_coe, Function.comp_apply]
  rw [← Traversable.traverse_map h g]; rw [List.map_eq_map]

中文:
定理 traverse_map
  结论: {G : 类型 -> Type _} [Applicative G] [CommApplicative G] {α β γ : Type _}
  证明: by
  induction x using Quotient.inductionOn
  simp only [traverse, quot_mk_to_coe, map_coe, lift_coe, Function.comp_apply]
  rw [← Traversable.traverse_map h g]; rw [List.map_eq_map]

Depends on / 依赖: Function, Function.comp_apply, List.map_eq_map, Quotient, Quotient.inductionOn, Traversable, Traversable.traverse_map, comp_apply, inductionOn, lift_coe, map_coe, map_eq_map, quot_mk_to_coe, traverse, traverse_map
-/
theorem traverse_map {G : Type* -> Type _} [Applicative G] [CommApplicative G] {α β γ : Type _}
    (g : α -> β) (h : β -> G γ) (x : Multiset α) : traverse h (map g x) = traverse (h ∘ g) x := by
  induction x using Quotient.inductionOn
  simp only [traverse, quot_mk_to_coe, map_coe, lift_coe, Function.comp_apply]
  rw [← Traversable.traverse_map h g]; rw [List.map_eq_map]

/--
theorem `naturality` / 定理 `naturality`

English:
theorem naturality
  statement: {G H : Type _ -> Type _} [Applicative G] [Applicative H] [CommApplicative G]
  proof: by
  induction x using Quotient.inductionOn
  simp only [quot_mk_to_coe, traverse, lift_coe, Function.comp_apply,
    ApplicativeTransformation.preserves_map, LawfulTraversable.naturality]

中文:
定理 naturality
  结论: {G H : Type _ -> Type _} [Applicative G] [Applicative H] [CommApplicative G]
  证明: by
  induction x using Quotient.inductionOn
  simp only [quot_mk_to_coe, traverse, lift_coe, Function.comp_apply,
    ApplicativeTransformation.preserves_map, LawfulTraversable.naturality]

Depends on / 依赖: ApplicativeTransformation, ApplicativeTransformation.preserves_map, Function, Function.comp_apply, LawfulTraversable, LawfulTraversable.naturality, Quotient, Quotient.inductionOn, comp_apply, inductionOn, lift_coe, naturality, preserves_map, quot_mk_to_coe, traverse
-/
theorem naturality {G H : Type _ -> Type _} [Applicative G] [Applicative H] [CommApplicative G]
    [CommApplicative H] (eta : ApplicativeTransformation G H) {α β : Type _} (f : α -> G β)
    (x : Multiset α) : eta (traverse f x) = traverse (@eta _ ∘ f) x := by
  induction x using Quotient.inductionOn
  simp only [quot_mk_to_coe, traverse, lift_coe, Function.comp_apply,
    ApplicativeTransformation.preserves_map, LawfulTraversable.naturality]

end Multiset
