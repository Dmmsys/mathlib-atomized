/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.Control.Traversable.Lemmas
public import Mathlib.Logic.Equiv.Defs
public import Batteries.Tactic.SeqFocus

import Mathlib.Tactic.Attr.Register

/-!
# Transferring `Traversable` instances along isomorphisms

This file allows to transfer `Traversable` instances along isomorphisms.

## Main declarations

* `Equiv.map`: Turns functorially a function `α → β` into a function `t' α → t' β` using the functor
  `t` and the equivalence `Π α, t α ≃ t' α`.
* `Equiv.functor`: `Equiv.map` as a functor.
* `Equiv.traverse`: Turns traversably a function `α → m β` into a function `t' α → m (t' β)` using
  the traversable functor `t` and the equivalence `Π α, t α ≃ t' α`.
* `Equiv.traversable`: `Equiv.traverse` as a traversable functor.
* `Equiv.isLawfulTraversable`: `Equiv.traverse` as a lawful traversable functor.
-/

@[expose] public section


universe u

namespace Equiv

section Functor

variable {t t' : Type u -> Type u} (eqv : forall α, t α ≃ t' α)
variable [Functor t]

open Functor

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {α β : Type u} (f : α -> β) (x : t' α)
  body: eqv β map f ((eqv α).symm x)

中文:
定义 map
  签名: {α β : 类型u} (f : α -> β) (x : t' α)
  定义体: eqv β map f ((eqv α).symm x)
-/
protected def map {α β : Type u} (f : α -> β) (x : t' α) : t' β :=
eqv β map f ((eqv α).symm x)

/-- The function `Equiv.map` transfers the functoriality of `t` to
`t'` using the equivalences `eqv`. -/
@[instance_reducible]
/--
Definition of `functor` / `functor` 的定义

English:
definition functor
  signature: : Functor t' where map
  body: Equiv.map eqv

中文:
定义 functor
  签名: : 函子 t' where map
  定义体: Equiv.map eqv
-/
protected def functor : Functor t' where map := Equiv.map eqv

variable [LawfulFunctor t]

/--
theorem `id_map` / 定理 `id_map`

English:
theorem id_map
  given: {α : Type u} (x : t' α)
  statement: Equiv.map eqv id x = x
  proof: by
  simp [Equiv.map, id_map]

中文:
定理 id_map
  条件: {α : 类型u} (x : t' α)
  结论: 等价.map eqv id x = x
  证明: by
  simp [Equiv.map, id_map]
-/
protected theorem id_map {α : Type u} (x : t' α) : Equiv.map eqv id x = x := by
  simp [Equiv.map, id_map]

/--
theorem `comp_map` / 定理 `comp_map`

English:
theorem comp_map
  given: {α β γ : Type u} (g : α -> β) (h : β -> γ) (x : t' α)
  proof: by
  simp [Equiv.map, Function.comp_def]

中文:
定理 comp_map
  条件: {α β γ : 类型u} (g : α -> β) (h : β -> γ) (x : t' α)
  证明: by
  simp [Equiv.map, Function.comp_def]
-/
protected theorem comp_map {α β γ : Type u} (g : α -> β) (h : β -> γ) (x : t' α) :
    Equiv.map eqv (h ∘ g) x = Equiv.map eqv h (Equiv.map eqv g x) := by
  simp [Equiv.map, Function.comp_def]

/--
theorem `lawfulFunctor` / 定理 `lawfulFunctor`

English:
theorem lawfulFunctor
  statement: @LawfulFunctor _ (Equiv.functor eqv)
  proof: -- Add the instance to the local context (since `Equiv.functor` is not an instance).
  -- Although it can be found by unification, Lean prefers to synthesize instances and
  -- then check that they are defeq to the instance found by unification.
  let _inst := Equiv.functor eqv
  { map_const := fun 

中文:
定理 lawfulFunctor
  结论: @Lawful函子 _ (等价.functor eqv)
  证明: -- Add the instance to the local context (since `Equiv.functor` is not an instance).
  -- Although it can be found by unification, Lean prefers to synthesize instances and
  -- then check that they are defeq to the instance found by unification.
  let _inst := Equiv.functor eqv
  { map_const := fun 
-/
protected theorem lawfulFunctor : @LawfulFunctor _ (Equiv.functor eqv) :=
  -- Add the instance to the local context (since `Equiv.functor` is not an instance).
  -- Although it can be found by unification, Lean prefers to synthesize instances and
  -- then check that they are defeq to the instance found by unification.
  let _inst := Equiv.functor eqv
  { map_const := fun {_ _} => rfl
    id_map := Equiv.id_map eqv
    comp_map := Equiv.comp_map eqv }

/--
theorem `lawfulFunctor'` / 定理 `lawfulFunctor'`

English:
theorem lawfulFunctor'
  statement: [F : Functor t']
  proof: by
  have : F = Equiv.functor eqv := by
    cases F
    dsimp [Equiv.functor]
    congr <;> ext <;> [rw [← h₀]; rw [← h₁]] <;> rfl
  subst this
  exact Equiv.lawfulFunctor eqv

中文:
定理 lawfulFunctor'
  结论: [F : 函子 t']
  证明: by
  have : F = Equiv.functor eqv := by
    cases F
    dsimp [Equiv.functor]
    congr <;> ext <;> [rw [← h₀]; rw [← h₁]] <;> rfl
  subst this
  exact Equiv.lawfulFunctor eqv
-/
protected theorem lawfulFunctor' [F : Functor t']
    (h₀ : forall {α β} (f : α -> β), Functor.map f = Equiv.map eqv f)
    (h₁ : forall {α β} (f : β), Functor.mapConst f = (Equiv.map eqv ∘ Function.const α) f) :
    LawfulFunctor t' := by
  have : F = Equiv.functor eqv := by
    cases F
    dsimp [Equiv.functor]
    congr <;> ext <;> [rw [← h₀]; rw [← h₁]] <;> rfl
  subst this
  exact Equiv.lawfulFunctor eqv

end Functor

section Traversable

variable {t t' : Type u -> Type u} (eqv : forall α, t α ≃ t' α)
variable [Traversable t]
variable {m : Type u -> Type u} [Applicative m]
variable {α β : Type u}

/--
Definition of `traverse` / `traverse` 的定义

English:
definition traverse
  signature: (f : α -> m β) (x : t' α)
  body: eqv β < > traverse f ((eqv α).symm x)

中文:
定义 traverse
  签名: (f : α -> m β) (x : t' α)
  定义体: eqv β < > traverse f ((eqv α).symm x)
-/
protected def traverse (f : α -> m β) (x : t' α) : m (t' β) :=
eqv β < > traverse f ((eqv α).symm x)

/--
theorem `traverse_def` / 定理 `traverse_def`

English:
theorem traverse_def
  given: (f : α -> m β) (x : t' α)
  proof: rfl

中文:
定理 traverse_def
  条件: (f : α -> m β) (x : t' α)
  证明: rfl
-/
theorem traverse_def (f : α -> m β) (x : t' α) :
Equiv.traverse eqv f x = eqv β < > traverse f ((eqv α).symm x) :=
  rfl

/-- The function `Equiv.traverse` transfers a traversable functor
instance across the equivalences `eqv`. -/
@[instance_reducible]
/--
Definition of `traversable` / `traversable` 的定义

English:
definition traversable
  signature: : Traversable t' where
  body: Equiv.functor eqv
  traverse := Equiv.traverse eqv

中文:
定义 traversable
  签名: : 可遍历 t' where
  定义体: Equiv.functor eqv
  traverse := Equiv.traverse eqv
-/
protected def traversable : Traversable t' where
  toFunctor := Equiv.functor eqv
  traverse := Equiv.traverse eqv

end Traversable

section Equiv

variable {t t' : Type u -> Type u} (eqv : forall α, t α ≃ t' α)

-- Is this to do with the fact it lives in `Type (u+1)` not `Prop`?
variable [Traversable t] [LawfulTraversable t]
variable {F G : Type u -> Type u} [Applicative F] [Applicative G]
variable [LawfulApplicative F] [LawfulApplicative G]
variable (η : ApplicativeTransformation F G)
variable {α β γ : Type u}

open LawfulTraversable Functor

/--
theorem `id_traverse` / 定理 `id_traverse`

English:
theorem id_traverse
  given: (x : t' α)
  statement: Equiv.traverse eqv (pure : α -> Id α) x = pure x
  proof: by
  rw [Equiv.traverse]; rw [id_traverse]; rw [map_pure]; rw [apply_symm_apply]

中文:
定理 id_traverse
  条件: (x : t' α)
  结论: 等价.traverse eqv (pure : α -> Id α) x = pure x
  证明: by
  rw [Equiv.traverse]; rw [id_traverse]; rw [map_pure]; rw [apply_symm_apply]
-/
protected theorem id_traverse (x : t' α) : Equiv.traverse eqv (pure : α -> Id α) x = pure x := by
  rw [Equiv.traverse]; rw [id_traverse]; rw [map_pure]; rw [apply_symm_apply]

/--
theorem `traverse_eq_map_id` / 定理 `traverse_eq_map_id`

English:
theorem traverse_eq_map_id
  given: (f : α -> β) (x : t' α)
  proof: by
  simp only [Equiv.traverse, traverse_eq_map_id]; rfl

中文:
定理 traverse_eq_map_id
  条件: (f : α -> β) (x : t' α)
  证明: by
  simp only [Equiv.traverse, traverse_eq_map_id]; rfl
-/
protected theorem traverse_eq_map_id (f : α -> β) (x : t' α) :
    Equiv.traverse eqv ((pure : β -> Id β) ∘ f) x = pure (Equiv.map eqv f x) := by
  simp only [Equiv.traverse, traverse_eq_map_id]; rfl

/--
theorem `comp_traverse` / 定理 `comp_traverse`

English:
theorem comp_traverse
  given: (f : β -> F γ) (g : α -> G β) (x : t' α)
  proof: by
  rw [traverse_def]; rw [comp_traverse]; rw [Comp.map_mk]
  simp only [map_map, traverse_def, symm_apply_apply]

中文:
定理 comp_traverse
  条件: (f : β -> F γ) (g : α -> G β) (x : t' α)
  证明: by
  rw [traverse_def]; rw [comp_traverse]; rw [Comp.map_mk]
  simp only [map_map, traverse_def, symm_apply_apply]
-/
protected theorem comp_traverse (f : β -> F γ) (g : α -> G β) (x : t' α) :
    Equiv.traverse eqv (Comp.mk ∘ Functor.map f ∘ g) x =
      Comp.mk (Equiv.traverse eqv f <$> Equiv.traverse eqv g x) := by
  rw [traverse_def]; rw [comp_traverse]; rw [Comp.map_mk]
  simp only [map_map, traverse_def, symm_apply_apply]

/--
theorem `naturality` / 定理 `naturality`

English:
theorem naturality
  given: (f : α -> F β) (x : t' α)
  proof: by
  simp only [Equiv.traverse, functor_norm]

中文:
定理 naturality
  条件: (f : α -> F β) (x : t' α)
  证明: by
  simp only [Equiv.traverse, functor_norm]
-/
protected theorem naturality (f : α -> F β) (x : t' α) :
    η (Equiv.traverse eqv f x) = Equiv.traverse eqv (@η _ ∘ f) x := by
  simp only [Equiv.traverse, functor_norm]

/--
theorem `isLawfulTraversable` / 定理 `isLawfulTraversable`

English:
theorem isLawfulTraversable
  statement: @LawfulTraversable t' (Equiv.traversable eqv)
  proof: let _inst := Equiv.traversable eqv
  { toLawfulFunctor := Equiv.lawfulFunctor eqv
    id_traverse := Equiv.id_traverse eqv
    comp_traverse := Equiv.comp_traverse eqv
    traverse_eq_map_id := Equiv.traverse_eq_map_id eqv
    naturality := Equiv.naturality eqv }

中文:
定理 isLawfulTraversable
  结论: @合法可遍历 t' (等价.traversable eqv)
  证明: let _inst := Equiv.traversable eqv
  { toLawfulFunctor := Equiv.lawfulFunctor eqv
    id_traverse := Equiv.id_traverse eqv
    comp_traverse := Equiv.comp_traverse eqv
    traverse_eq_map_id := Equiv.traverse_eq_map_id eqv
    naturality := Equiv.naturality eqv }
-/
protected theorem isLawfulTraversable : @LawfulTraversable t' (Equiv.traversable eqv) :=
  let _inst := Equiv.traversable eqv
  { toLawfulFunctor := Equiv.lawfulFunctor eqv
    id_traverse := Equiv.id_traverse eqv
    comp_traverse := Equiv.comp_traverse eqv
    traverse_eq_map_id := Equiv.traverse_eq_map_id eqv
    naturality := Equiv.naturality eqv }

/--
theorem `isLawfulTraversable'` / 定理 `isLawfulTraversable'`

English:
theorem isLawfulTraversable'
  statement: [Traversable t']
  proof: Equiv.lawfulFunctor' eqv @h₀ @h₁
  id_traverse _ := by rw [h₂, Equiv.id_traverse]
  comp_traverse _ _ _ := by rw [h₂, Equiv.comp_traverse, h₂]; congr; rw [h₂]
  traverse_eq_map_id _ _ := by rw [h₂, Equiv.traverse_eq_map_id, h₀]
  naturality _ _ _ _ _ := by rw [h₂, Equiv.naturality, h₂]

中文:
定理 isLawfulTraversable'
  结论: [可遍历 t']
  证明: Equiv.lawfulFunctor' eqv @h₀ @h₁
  id_traverse _ := by rw [h₂, Equiv.id_traverse]
  comp_traverse _ _ _ := by rw [h₂, Equiv.comp_traverse, h₂]; congr; rw [h₂]
  traverse_eq_map_id _ _ := by rw [h₂, Equiv.traverse_eq_map_id, h₀]
  naturality _ _ _ _ _ := by rw [h₂, Equiv.naturality, h₂]
-/
protected theorem isLawfulTraversable' [Traversable t']
    (h₀ : forall {α β} (f : α -> β), map f = Equiv.map eqv f)
    (h₁ : forall {α β} (f : β), mapConst f = (Equiv.map eqv ∘ Function.const α) f)
    (h₂ : forall {F : Type u -> Type u} [Applicative F],
      forall [LawfulApplicative F] {α β} (f : α -> F β), traverse f = Equiv.traverse eqv f) :
    LawfulTraversable t' where
  -- we can't use the same approach as for `lawful_functor'` because
  -- h₂ needs a `LawfulApplicative` assumption
  toLawfulFunctor := Equiv.lawfulFunctor' eqv @h₀ @h₁
  id_traverse _ := by rw [h₂, Equiv.id_traverse]
  comp_traverse _ _ _ := by rw [h₂, Equiv.comp_traverse, h₂]; congr; rw [h₂]
  traverse_eq_map_id _ _ := by rw [h₂, Equiv.traverse_eq_map_id, h₀]
  naturality _ _ _ _ _ := by rw [h₂, Equiv.naturality, h₂]

end Equiv

end Equiv
