/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Galois.Examples
public import Mathlib.CategoryTheory.Galois.Prorepresentability

/-!

# Induced functor to finite `Aut F`-sets

Any (fiber) functor `F : C ⥤ FintypeCat` factors via the forgetful functor
from finite `Aut F`-sets to finite sets. In this file we collect basic properties
of the induced functor `H : C ⥤ Action FintypeCat (Aut F)`.

See `Mathlib/CategoryTheory/Galois/Full.lean` for the proof that `H` is (faithfully) full.

-/

@[expose] public section

universe u

namespace CategoryTheory

namespace PreGaloisCategory

open Limits CategoryTheory.Functor

variable {C : Type*} [Category* C] (F : C ⥤ FintypeCat.{u})

/--
Definition of `functorToAction` / `functorToAction` 的定义

English:
definition functorToAction
  signature: : C ⥤ Action FintypeCat.{u} (Aut F) where
  body: Action.FintypeCat.ofMulAction (Aut F) (F.obj X)
  map f := {
    hom := F.map f
comm := fun g => symm g.hom.naturality f
  }

中文:
定义 functorToAction
  签名: : C ⥤ 作用 FintypeCat.{u} (Aut F) where
  定义体: Action.FintypeCat.ofMulAction (Aut F) (F.obj X)
  map f := {
    hom := F.map f
comm := fun g => symm g.hom.naturality f
  }

Depends on / 依赖: Action, Action.FintypeCat.ofMulAction, F.obj, FintypeCat, ofMulAction
-/
def functorToAction : C ⥤ Action FintypeCat.{u} (Aut F) where
  obj X := Action.FintypeCat.ofMulAction (Aut F) (F.obj X)
  map f := {
    hom := F.map f
comm := fun g => symm g.hom.naturality f
  }

/--
lemma `functorToAction_comp_forget₂_eq` / 引理 `functorToAction_comp_forget₂_eq`

English:
lemma functorToAction_comp_forget₂_eq
  statement: functorToAction F ⋙ forget₂ _ FintypeCat = F
  proof: rfl

@[simp]

中文:
引理 functorToAction_comp_forget₂_eq
  结论: functorToAction F ⋙ forget₂ _ FintypeCat = F
  证明: rfl

@[simp]
-/
lemma functorToAction_comp_forget₂_eq : functorToAction F ⋙ forget₂ _ FintypeCat = F := rfl

@[simp]
/--
lemma `functorToAction_map` / 引理 `functorToAction_map`

English:
lemma functorToAction_map
  given: {X Y : C} (f : X ⟶ Y)
  statement: ((functorToAction F).map f).hom = F.map f
  proof: rfl

中文:
引理 functorToAction_map
  条件: {X Y : C} (f : X ⟶ Y)
  结论: ((functorToAction F).map f).hom = F.map f
  证明: rfl
-/
lemma functorToAction_map {X Y : C} (f : X ⟶ Y) : ((functorToAction F).map f).hom = F.map f :=
  rfl

instance (X : C) : MulAction (Aut X) ((functorToAction F).obj X).V :=
inferInstanceAs MulAction (Aut X) (F.obj X)

variable [GaloisCategory C] [FiberFunctor F]

instance (X : C) [IsGalois X] : MulAction.IsPretransitive (Aut X) ((functorToAction F).obj X).V :=
  isPretransitive_of_isGalois F X

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Functor.Faithful (functorToAction F)
  body: have : Functor.Faithful (functorToAction F ⋙ forget₂ _ FintypeCat) :=
inferInstanceAs Functor.Faithful F
  Functor.Faithful.of_comp (functorToAction F) (forget₂ _ FintypeCat)

中文:
实例 :
  签名: 函子.忠实 (functorToAction F)
  定义体: have : Functor.Faithful (functorToAction F ⋙ forget₂ _ FintypeCat) :=
inferInstanceAs Functor.Faithful F
  Functor.Faithful.of_comp (functorToAction F) (forget₂ _ FintypeCat)

Depends on / 依赖: Faithful, FintypeCat, Functor, Functor.Faithful, Functor.Faithful.of_comp, functorToAction, of_comp
-/
instance : Functor.Faithful (functorToAction F) :=
  have : Functor.Faithful (functorToAction F ⋙ forget₂ _ FintypeCat) :=
inferInstanceAs Functor.Faithful F
  Functor.Faithful.of_comp (functorToAction F) (forget₂ _ FintypeCat)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesMonomorphisms (functorToAction F)
  body: have : PreservesMonomorphisms (functorToAction F ⋙ forget₂ _ FintypeCat) :=
inferInstanceAs PreservesMonomorphisms F
  preservesMonomorphisms_of_preserves_of_reflects (functorToAction F) (forget₂ _ FintypeCat)

中文:
实例 :
  签名: 保持Monomorphisms (functorToAction F)
  定义体: have : PreservesMonomorphisms (functorToAction F ⋙ forget₂ _ FintypeCat) :=
inferInstanceAs PreservesMonomorphisms F
  preservesMonomorphisms_of_preserves_of_reflects (functorToAction F) (forget₂ _ FintypeCat)

Depends on / 依赖: FintypeCat, PreservesMonomorphisms, functorToAction, preservesMonomorphisms_of_preserves_of_reflects
-/
instance : PreservesMonomorphisms (functorToAction F) :=
  have : PreservesMonomorphisms (functorToAction F ⋙ forget₂ _ FintypeCat) :=
inferInstanceAs PreservesMonomorphisms F
  preservesMonomorphisms_of_preserves_of_reflects (functorToAction F) (forget₂ _ FintypeCat)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ReflectsMonomorphisms (functorToAction F)
  body: reflectsMonomorphisms_of_faithful _

中文:
实例 :
  签名: 反映单态射 (functorToAction F)
  定义体: reflectsMonomorphisms_of_faithful _

Depends on / 依赖: reflectsMonomorphisms_of_faithful
-/
instance : ReflectsMonomorphisms (functorToAction F) := reflectsMonomorphisms_of_faithful _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Functor.ReflectsIsomorphisms (functorToAction F)
  body: have : IsIso (F.map f) := (forget₂ _ FintypeCat).map_isIso ((functorToAction F).map f)
    isIso_of_reflects_iso f F

中文:
实例 :
  签名: 函子.反映同构 (functorToAction F)
  定义体: have : IsIso (F.map f) := (forget₂ _ FintypeCat).map_isIso ((functorToAction F).map f)
    isIso_of_reflects_iso f F

Depends on / 依赖: F.map, FintypeCat, functorToAction, isIso_of_reflects_iso, map_isIso
-/
instance : Functor.ReflectsIsomorphisms (functorToAction F) where
  reflects f _ :=
    have : IsIso (F.map f) := (forget₂ _ FintypeCat).map_isIso ((functorToAction F).map f)
    isIso_of_reflects_iso f F

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesFiniteCoproducts (functorToAction F)
  body: ⟨fun _ => Action.preservesColimitsOfShape_of_preserves (functorToAction F)
    (inferInstanceAs <| PreservesColimitsOfShape (Discrete _) F)⟩

中文:
实例 :
  签名: 保持FiniteCoproducts (functorToAction F)
  定义体: ⟨fun _ => Action.preservesColimitsOfShape_of_preserves (functorToAction F)
    (inferInstanceAs <| PreservesColimitsOfShape (Discrete _) F)⟩

Depends on / 依赖: Action, Action.preservesColimitsOfShape_of_preserves, Discrete, PreservesColimitsOfShape, functorToAction, preservesColimitsOfShape_of_preserves
-/
noncomputable instance : PreservesFiniteCoproducts (functorToAction F) :=
  ⟨fun _ => Action.preservesColimitsOfShape_of_preserves (functorToAction F)
    (inferInstanceAs <| PreservesColimitsOfShape (Discrete _) F)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesFiniteProducts (functorToAction F)
  body: ⟨fun _ => Action.preservesLimitsOfShape_of_preserves (functorToAction F)
    (inferInstanceAs <| PreservesLimitsOfShape (Discrete _) F)⟩

中文:
实例 :
  签名: 保持FiniteProducts (functorToAction F)
  定义体: ⟨fun _ => Action.preservesLimitsOfShape_of_preserves (functorToAction F)
    (inferInstanceAs <| PreservesLimitsOfShape (Discrete _) F)⟩

Depends on / 依赖: Action, Action.preservesLimitsOfShape_of_preserves, Discrete, PreservesLimitsOfShape, functorToAction, preservesLimitsOfShape_of_preserves
-/
noncomputable instance : PreservesFiniteProducts (functorToAction F) :=
  ⟨fun _ => Action.preservesLimitsOfShape_of_preserves (functorToAction F)
    (inferInstanceAs <| PreservesLimitsOfShape (Discrete _) F)⟩

noncomputable instance (G : Type*) [Group G] [Finite G] :
    PreservesColimitsOfShape (SingleObj G) (functorToAction F) :=
Action.preservesColimitsOfShape_of_preserves _
inferInstanceAs PreservesColimitsOfShape (SingleObj G) F

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesIsConnected (functorToAction F)
  body: ⟨fun {X} _ => FintypeCat.Action.isConnected_of_transitive (Aut F) (F.obj X)⟩

中文:
实例 :
  签名: 保持是连通 (functorToAction F)
  定义体: ⟨fun {X} _ => FintypeCat.Action.isConnected_of_transitive (Aut F) (F.obj X)⟩

Depends on / 依赖: Action, F.obj, FintypeCat, FintypeCat.Action.isConnected_of_transitive, isConnected_of_transitive
-/
instance : PreservesIsConnected (functorToAction F) :=
  ⟨fun {X} _ => FintypeCat.Action.isConnected_of_transitive (Aut F) (F.obj X)⟩

end PreGaloisCategory

end CategoryTheory
