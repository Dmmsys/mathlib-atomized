/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Discrete.Basic

/-!
# The empty category

Defines a category structure on `PEmpty`, and the unique functor `PEmpty ⥤ C` for any category `C`.
-/

@[expose] public section

universe w v v' u u'
-- morphism levels before object levels. See note [category theory universes].
namespace CategoryTheory

variable (C : Type u) [Category.{v} C] (D : Type u') [Category.{v'} D]

instance (α : Type*) [IsEmpty α] : IsEmpty (Discrete α) := Function.isEmpty Discrete.as

/--
Definition of `functorOfIsEmpty` / `functorOfIsEmpty` 的定义

English:
definition functorOfIsEmpty
  signature: [IsEmpty C]
  body: isEmptyElim
  map := fun {X} => isEmptyElim X
  map_id := fun {X} => isEmptyElim X
  map_comp := fun {X} => isEmptyElim X

中文:
定义 functorOfIsEmpty
  签名: [IsEmpty C]
  定义体: isEmptyElim
  map := fun {X} => isEmptyElim X
  map_id := fun {X} => isEmptyElim X
  map_comp := fun {X} => isEmptyElim X

Depends on / 依赖: isEmptyElim
-/
def functorOfIsEmpty [IsEmpty C] : C ⥤ D where
  obj := isEmptyElim
  map := fun {X} => isEmptyElim X
  map_id := fun {X} => isEmptyElim X
  map_comp := fun {X} => isEmptyElim X

variable {C D}

/--
Definition of `Functor.isEmptyExt` / `Functor.isEmptyExt` 的定义

English:
definition Functor.isEmptyExt
  signature: [IsEmpty C] (F G : C ⥤ D)
  body: NatIso.ofComponents isEmptyElim (fun {X} => isEmptyElim X)

中文:
定义 Functor.isEmptyExt
  签名: [IsEmpty C] (F G : C ⥤ D)
  定义体: NatIso.ofComponents isEmptyElim (fun {X} => isEmptyElim X)

Depends on / 依赖: NatIso, NatIso.ofComponents, isEmptyElim, ofComponents
-/
def Functor.isEmptyExt [IsEmpty C] (F G : C ⥤ D) : F ≅ G :=
  NatIso.ofComponents isEmptyElim (fun {X} => isEmptyElim X)

variable (C D)

/--
Definition of `equivalenceOfIsEmpty` / `equivalenceOfIsEmpty` 的定义

English:
definition equivalenceOfIsEmpty
  signature: [IsEmpty C] [IsEmpty D]
  body: functorOfIsEmpty C D
  inverse := functorOfIsEmpty D C
  unitIso := Functor.isEmptyExt _ _
  counitIso := Functor.isEmptyExt _ _
  functor_unitIso_comp := isEmptyElim

中文:
定义 equivalenceOfIsEmpty
  签名: [IsEmpty C] [IsEmpty D]
  定义体: functorOfIsEmpty C D
  inverse := functorOfIsEmpty D C
  unitIso := Functor.isEmptyExt _ _
  counitIso := Functor.isEmptyExt _ _
  functor_unitIso_comp := isEmptyElim

Depends on / 依赖: functorOfIsEmpty
-/
def equivalenceOfIsEmpty [IsEmpty C] [IsEmpty D] : C ≌ D where
  functor := functorOfIsEmpty C D
  inverse := functorOfIsEmpty D C
  unitIso := Functor.isEmptyExt _ _
  counitIso := Functor.isEmptyExt _ _
  functor_unitIso_comp := isEmptyElim

/--
Definition of `emptyEquivalence` / `emptyEquivalence` 的定义

English:
definition emptyEquivalence
  signature: : Discrete.{w} PEmpty ≌ Discrete.{v} PEmpty
  body: equivalenceOfIsEmpty _ _

中文:
定义 emptyEquivalence
  签名: : Discrete.{w} PEmpty ≌ Discrete.{v} PEmpty
  定义体: equivalenceOfIsEmpty _ _

Depends on / 依赖: equivalenceOfIsEmpty
-/
def emptyEquivalence : Discrete.{w} PEmpty ≌ Discrete.{v} PEmpty := equivalenceOfIsEmpty _ _

namespace Functor

/--
Definition of `empty` / `empty` 的定义

English:
definition empty
  signature: : Discrete.{w} PEmpty ⥤ C
  body: Discrete.functor PEmpty.elim

中文:
定义 empty
  签名: : Discrete.{w} PEmpty ⥤ C
  定义体: Discrete.functor PEmpty.elim

Depends on / 依赖: Discrete, Discrete.functor, PEmpty, PEmpty.elim, functor
-/
def empty : Discrete.{w} PEmpty ⥤ C :=
  Discrete.functor PEmpty.elim

variable {C}

/--
Definition of `emptyExt` / `emptyExt` 的定义

English:
definition emptyExt
  signature: (F G : Discrete.{w} PEmpty ⥤ C)
  body: Discrete.natIso fun x => x.as.elim

中文:
定义 emptyExt
  签名: (F G : Discrete.{w} PEmpty ⥤ C)
  定义体: Discrete.natIso fun x => x.as.elim

Depends on / 依赖: Discrete, Discrete.natIso, natIso, x.as.elim
-/
def emptyExt (F G : Discrete.{w} PEmpty ⥤ C) : F ≅ G :=
  Discrete.natIso fun x => x.as.elim

/--
Definition of `uniqueFromEmpty` / `uniqueFromEmpty` 的定义

English:
definition uniqueFromEmpty
  signature: (F : Discrete.{w} PEmpty ⥤ C)
  body: emptyExt _ _

中文:
定义 uniqueFromEmpty
  签名: (F : Discrete.{w} PEmpty ⥤ C)
  定义体: emptyExt _ _

Depends on / 依赖: emptyExt
-/
def uniqueFromEmpty (F : Discrete.{w} PEmpty ⥤ C) : F ≅ empty C :=
  emptyExt _ _

/--
theorem `empty_ext'` / 定理 `empty_ext'`

English:
theorem empty_ext'
  given: (F G : Discrete.{w} PEmpty ⥤ C)
  statement: F = G
  proof: Functor.ext (fun x => x.as.elim) fun x _ _ => x.as.elim

中文:
定理 empty_ext'
  条件: (F G : Discrete.{w} PEmpty ⥤ C)
  结论: F = G
  证明: Functor.ext (fun x => x.as.elim) fun x _ _ => x.as.elim

Depends on / 依赖: Functor, Functor.ext, x.as.elim
-/
theorem empty_ext' (F G : Discrete.{w} PEmpty ⥤ C) : F = G :=
  Functor.ext (fun x => x.as.elim) fun x _ _ => x.as.elim

end Functor

end CategoryTheory
