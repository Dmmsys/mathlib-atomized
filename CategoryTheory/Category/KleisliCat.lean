/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.CategoryTheory.Category.Basic

/-!
# The Kleisli construction on the Type category

Define the Kleisli category for (control) monads.
`CategoryTheory/Monad/Kleisli` defines the general version for a monad on `C`, and demonstrates
the equivalence between the two.

## TODO

Generalise this to work with CategoryTheory.Monad
-/

@[expose] public section


universe u v

namespace CategoryTheory

-- This file is about Lean 3 declaration "Kleisli".

/-- The Kleisli category on the (type-)monad `m`. Note that the monad is not assumed to be lawful
yet. -/
@[nolint unusedArguments]
/--
Definition of `KleisliCat` / `KleisliCat` 的定义

English:
definition KleisliCat
  signature: (_ : Type u -> Type v)
  body: Type u

中文:
定义 KleisliCat
  签名: (_ : 类型u -> 类型v)
  定义体: Type u
-/
def KleisliCat (_ : Type u -> Type v) :=
  Type u

/--
Definition of `KleisliCat.mk` / `KleisliCat.mk` 的定义

English:
definition KleisliCat.mk
  signature: (m) (α : Type u)
  body: α

中文:
定义 KleisliCat.mk
  签名: (m) (α : 类型u)
  定义体: α
-/
def KleisliCat.mk (m) (α : Type u) : KleisliCat m :=
  α

/--
Instance `KleisliCat.categoryStruct` / 实例 `KleisliCat.categoryStruct`

English:
instance KleisliCat.categoryStruct
  signature: {m} [Monad.{u, v} m]
  body: α -> m β
  id _ x := pure x
  comp f g := f >=> g

@[ext]

中文:
实例 KleisliCat.categoryStruct
  签名: {m} [Monad.{u, v} m]
  定义体: α -> m β
  id _ x := pure x
  comp f g := f >=> g

@[ext]
-/
instance KleisliCat.categoryStruct {m} [Monad.{u, v} m] :
    CategoryStruct (KleisliCat m) where
  Hom α β := α -> m β
  id _ x := pure x
  comp f g := f >=> g

@[ext]
/--
theorem `KleisliCat.ext` / 定理 `KleisliCat.ext`

English:
theorem KleisliCat.ext
  statement: {m} [Monad.{u, v} m] (α β : KleisliCat m)
  proof: funext h

中文:
定理 KleisliCat.ext
  结论: {m} [Monad.{u, v} m] (α β : KleisliCat m)
  证明: funext h
-/
theorem KleisliCat.ext {m} [Monad.{u, v} m] (α β : KleisliCat m)
    (f g : α ⟶ β) (h : forall x, f x = g x) : f = g := funext h

set_option backward.isDefEq.respectTransparency false in
/--
Instance `KleisliCat.category` / 实例 `KleisliCat.category`

English:
instance KleisliCat.category
  signature: {m} [Monad.{u, v} m] [LawfulMonad m]
  body: by
  refine { id_comp := ?_, comp_id := ?_, assoc := ?_ } <;> intros <;>
  ext <;>
  simp +unfoldPartialApp [CategoryStruct.id, CategoryStruct.comp, (· >=> ·)]

@[simp]

中文:
实例 KleisliCat.category
  签名: {m} [Monad.{u, v} m] [LawfulMonad m]
  定义体: by
  refine { id_comp := ?_, comp_id := ?_, assoc := ?_ } <;> intros <;>
  ext <;>
  simp +unfoldPartialApp [CategoryStruct.id, CategoryStruct.comp, (· >=> ·)]

@[simp]

Depends on / 依赖: CategoryStruct, CategoryStruct.comp, CategoryStruct.id, comp_id, id_comp, intros, unfoldPartialApp
-/
instance KleisliCat.category {m} [Monad.{u, v} m] [LawfulMonad m] : Category (KleisliCat m) := by
  refine { id_comp := ?_, comp_id := ?_, assoc := ?_ } <;> intros <;>
  ext <;>
  simp +unfoldPartialApp [CategoryStruct.id, CategoryStruct.comp, (· >=> ·)]

@[simp]
/--
theorem `KleisliCat.id_def` / 定理 `KleisliCat.id_def`

English:
theorem KleisliCat.id_def
  given: {m} [Monad m] (α : KleisliCat m)
  statement: 𝟙 α = @pure m _ α
  proof: rfl

中文:
定理 KleisliCat.id_def
  条件: {m} [Monad m] (α : KleisliCat m)
  结论: 𝟙 α = @pure m _ α
  证明: rfl
-/
theorem KleisliCat.id_def {m} [Monad m] (α : KleisliCat m) : 𝟙 α = @pure m _ α :=
  rfl

/--
theorem `KleisliCat.comp_def` / 定理 `KleisliCat.comp_def`

English:
theorem KleisliCat.comp_def
  given: {m} [Monad m] (α β γ : KleisliCat m) (xs : α ⟶ β) (ys : β ⟶ γ) (a : α)
  proof: rfl

中文:
定理 KleisliCat.comp_def
  条件: {m} [Monad m] (α β γ : KleisliCat m) (xs : α ⟶ β) (ys : β ⟶ γ) (a : α)
  证明: rfl
-/
theorem KleisliCat.comp_def {m} [Monad m] (α β γ : KleisliCat m) (xs : α ⟶ β) (ys : β ⟶ γ) (a : α) :
    (xs ≫ ys) a = xs a >>= ys :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (KleisliCat id)
  body: ⟨PUnit⟩

中文:
实例 :
  签名: Inhabited (KleisliCat id)
  定义体: ⟨PUnit⟩
-/
instance : Inhabited (KleisliCat id) :=
  ⟨PUnit⟩

instance {α : Type u} [Inhabited α] : Inhabited (KleisliCat.mk id α) :=
  ⟨show α from default⟩

end CategoryTheory
