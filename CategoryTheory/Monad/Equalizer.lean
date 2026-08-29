/-
Copyright (c) 2024 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Reflexive
public import Mathlib.CategoryTheory.Limits.Shapes.SplitEqualizer
public import Mathlib.CategoryTheory.Monad.Algebra

/-!
# Special equalizers associated to a comonad

Associated to a comonad `T : C ⥤ C` we have important equalizer constructions:
Any coalgebra is an equalizer (in the category of coalgebras) of cofree coalgebras. Furthermore,
this equalizer is coreflexive.
In `C`, this fork diagram is a split equalizer (in particular, it is still an equalizer).
This split equalizer is known as the Beck equalizer (as it features heavily in Beck's
comonadicity theorem).

This file is adapted from `Mathlib/CategoryTheory/Monad/Coequalizer.lean`.
Please try to keep them in sync.

-/

@[expose] public section


universe v₁ u₁

namespace CategoryTheory

namespace Comonad

open Limits

variable {C : Type u₁}
variable [Category.{v₁} C]
variable {T : Comonad C} (X : Coalgebra T)

/-!
Show that any coalgebra is an equalizer of cofree coalgebras.
-/


/-- The top map in the equalizer diagram we will construct. -/
@[simps!]
/--
Definition of `CofreeEqualizer.topMap` / `CofreeEqualizer.topMap` 的定义

English:
definition CofreeEqualizer.topMap
  signature: : (Comonad.cofree T).obj X.A ⟶ (Comonad.cofree T).obj (T.obj X.A)
  body: (Comonad.cofree T).map X.a

中文:
定义 CofreeEqualizer.topMap
  签名: : (Comonad.cofree T).obj X.A ⟶ (Comonad.cofree T).obj (T.obj X.A)
  定义体: (Comonad.cofree T).map X.a

Depends on / 依赖: Comonad, Comonad.cofree, cofree
-/
def CofreeEqualizer.topMap : (Comonad.cofree T).obj X.A ⟶ (Comonad.cofree T).obj (T.obj X.A) :=
  (Comonad.cofree T).map X.a

/-- The bottom map in the equalizer diagram we will construct. -/
@[simps]
/--
Definition of `CofreeEqualizer.bottomMap` / `CofreeEqualizer.bottomMap` 的定义

English:
definition CofreeEqualizer.bottomMap
  signature: :
  body: T.δ.app X.A
  h := T.coassoc X.A

中文:
定义 CofreeEqualizer.bottomMap
  签名: :
  定义体: T.δ.app X.A
  h := T.coassoc X.A
-/
def CofreeEqualizer.bottomMap :
    (Comonad.cofree T).obj X.A ⟶ (Comonad.cofree T).obj (T.obj X.A) where
  f := T.δ.app X.A
  h := T.coassoc X.A

/-- The fork map in the equalizer diagram we will construct. -/
@[simps]
/--
Definition of `CofreeEqualizer.ι` / `CofreeEqualizer.ι` 的定义

English:
definition CofreeEqualizer.ι
  signature: : X ⟶ (Comonad.cofree T).obj X.A where
  body: X.a
  h := X.coassoc.symm

中文:
定义 CofreeEqualizer.ι
  签名: : X ⟶ (Comonad.cofree T).obj X.A where
  定义体: X.a
  h := X.coassoc.symm
-/
def CofreeEqualizer.ι : X ⟶ (Comonad.cofree T).obj X.A where
  f := X.a
  h := X.coassoc.symm

/--
theorem `CofreeEqualizer.condition` / 定理 `CofreeEqualizer.condition`

English:
theorem CofreeEqualizer.condition
  proof: Coalgebra.Hom.ext X.coassoc.symm

中文:
定理 CofreeEqualizer.condition
  证明: Coalgebra.Hom.ext X.coassoc.symm

Depends on / 依赖: Coalgebra, Coalgebra.Hom.ext, G.IsEquivalence, IsCoverDense, IsEquivalence, X.coassoc.symm, coassoc
-/
theorem CofreeEqualizer.condition :
    CofreeEqualizer.ι X ≫ CofreeEqualizer.topMap X =
      CofreeEqualizer.ι X ≫ CofreeEqualizer.bottomMap X :=
  Coalgebra.Hom.ext X.coassoc.symm

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsCoreflexivePair (CofreeEqualizer.topMap X) (CofreeEqualizer.bottomMap X)
  body: by
  apply IsCoreflexivePair.mk' _ _ _
  · apply (cofree T).map (T.ε.app X.A)
  · ext
    dsimp
    rw [← Functor.map_comp]; rw [X.counit]; rw [Functor.map_id]
  · ext
    apply Comonad.right_counit

中文:
实例 :
  签名: IsCoreflexivePair (CofreeEqualizer.topMap X) (CofreeEqualizer.bottomMap X)
  定义体: by
  apply IsCoreflexivePair.mk' _ _ _
  · apply (cofree T).map (T.ε.app X.A)
  · ext
    dsimp
    rw [← Functor.map_comp]; rw [X.counit]; rw [Functor.map_id]
  · ext
    apply Comonad.right_counit

Depends on / 依赖: Comonad, Comonad.right_counit, Functor, Functor.map_comp, Functor.map_id, IsCoreflexivePair, IsCoreflexivePair.mk, X.counit, cofree, counit, map_comp, map_id, right_counit
-/
instance : IsCoreflexivePair (CofreeEqualizer.topMap X) (CofreeEqualizer.bottomMap X) := by
  apply IsCoreflexivePair.mk' _ _ _
  · apply (cofree T).map (T.ε.app X.A)
  · ext
    dsimp
    rw [← Functor.map_comp]; rw [X.counit]; rw [Functor.map_id]
  · ext
    apply Comonad.right_counit

/-- Construct the Beck fork in the category of coalgebras. This fork is coreflexive as well as an
equalizer.
-/
@[simps!]
/--
Definition of `beckCoalgebraFork` / `beckCoalgebraFork` 的定义

English:
definition beckCoalgebraFork
  signature: : Fork (CofreeEqualizer.topMap X) (CofreeEqualizer.bottomMap X)
  body: Fork.ofι _ (CofreeEqualizer.condition X)

中文:
定义 beckCoalgebraFork
  签名: : Fork (CofreeEqualizer.topMap X) (CofreeEqualizer.bottomMap X)
  定义体: Fork.ofι _ (CofreeEqualizer.condition X)

Depends on / 依赖: CofreeEqualizer, CofreeEqualizer.condition, Fork.of, condition
-/
def beckCoalgebraFork : Fork (CofreeEqualizer.topMap X) (CofreeEqualizer.bottomMap X) :=
  Fork.ofι _ (CofreeEqualizer.condition X)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `beckCoalgebraEqualizer` / `beckCoalgebraEqualizer` 的定义

English:
definition beckCoalgebraEqualizer
  signature: : IsLimit (beckCoalgebraFork X)
  body: Fork.IsLimit.mk' _ fun s => by
    have h₁ : s.ι.f ≫ (T : C ⥤ C).map X.a = s.ι.f ≫ T.δ.app X.A :=
      congr_arg Comonad.Coalgebra.Hom.f s.condition
    have h₂ : s.pt.a ≫ (T : C ⥤ C).map s.ι.f = s.ι.f ≫ T.δ.app X.A := s.ι.h
    refine ⟨⟨s.ι.f ≫ T.ε.app _, ?_⟩, ?_, ?_⟩
    · dsimp
      rw [Functor

中文:
定义 beckCoalgebraEqualizer
  签名: : IsLimit (beckCoalgebraFork X)
  定义体: Fork.IsLimit.mk' _ fun s => by
    have h₁ : s.ι.f ≫ (T : C ⥤ C).map X.a = s.ι.f ≫ T.δ.app X.A :=
      congr_arg Comonad.Coalgebra.Hom.f s.condition
    have h₂ : s.pt.a ≫ (T : C ⥤ C).map s.ι.f = s.ι.f ≫ T.δ.app X.A := s.ι.h
    refine ⟨⟨s.ι.f ≫ T.ε.app _, ?_⟩, ?_, ?_⟩
    · dsimp
      rw [Functor

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Coalgebra, Comonad, Comonad.Coalgebra.Hom.f, Comonad.left_counit, Comonad.right_counit, Fork.IsLimit.mk, Functor, Functor.map_comp, IsLimit, T.counit_naturality, comp_id, condition, congr_arg, counit_naturality, left_counit, map_comp, naturality_assoc
-/
def beckCoalgebraEqualizer : IsLimit (beckCoalgebraFork X) :=
  Fork.IsLimit.mk' _ fun s => by
    have h₁ : s.ι.f ≫ (T : C ⥤ C).map X.a = s.ι.f ≫ T.δ.app X.A :=
      congr_arg Comonad.Coalgebra.Hom.f s.condition
    have h₂ : s.pt.a ≫ (T : C ⥤ C).map s.ι.f = s.ι.f ≫ T.δ.app X.A := s.ι.h
    refine ⟨⟨s.ι.f ≫ T.ε.app _, ?_⟩, ?_, ?_⟩
    · dsimp
      rw [Functor.map_comp]; rw [reassoc_of% h₂]; rw [Comonad.right_counit]
      dsimp
      rw [Category.comp_id]; rw [Category.assoc]; rw [← T.counit_naturality]; rw [reassoc_of% h₁]; rw [Comonad.left_counit]
      simp
    · ext
      simpa [← T.ε.naturality_assoc, T.left_counit_assoc] using! h₁ =≫ T.ε.app ((T : C ⥤ C).obj X.A)
    · intro m hm
      ext
      dsimp only
      rw [← hm]
      simp [beckCoalgebraFork, X.counit]

/--
Definition of `beckSplitEqualizer` / `beckSplitEqualizer` 的定义

English:
definition beckSplitEqualizer
  signature: : IsSplitEqualizer (T.map X.a) (T.δ.app _) X.a
  body: ⟨T.ε.app _, T.ε.app _, X.coassoc.symm, X.counit, T.left_counit _, (T.ε.naturality _)⟩

中文:
定义 beckSplitEqualizer
  签名: : IsSplitEqualizer (T.map X.a) (T.δ.app _) X.a
  定义体: ⟨T.ε.app _, T.ε.app _, X.coassoc.symm, X.counit, T.left_counit _, (T.ε.naturality _)⟩

Depends on / 依赖: T.left_counit, X.coassoc.symm, X.counit, coassoc, counit, left_counit, naturality
-/
def beckSplitEqualizer : IsSplitEqualizer (T.map X.a) (T.δ.app _) X.a :=
  ⟨T.ε.app _, T.ε.app _, X.coassoc.symm, X.counit, T.left_counit _, (T.ε.naturality _)⟩

/-- This is the Beck fork. It is a split equalizer, in particular an equalizer. -/
@[simps! pt]
/--
Definition of `beckFork` / `beckFork` 的定义

English:
definition beckFork
  signature: : Fork (T.map X.a) (T.δ.app _)
  body: (beckSplitEqualizer X).asFork

@[simp]

中文:
定义 beckFork
  签名: : Fork (T.map X.a) (T.δ.app _)
  定义体: (beckSplitEqualizer X).asFork

@[simp]

Depends on / 依赖: asFork, beckSplitEqualizer
-/
def beckFork : Fork (T.map X.a) (T.δ.app _) :=
  (beckSplitEqualizer X).asFork

@[simp]
/--
theorem `beckFork_ι` / 定理 `beckFork_ι`

English:
theorem beckFork_ι
  statement: (beckFork X).ι = X.a
  proof: rfl

中文:
定理 beckFork_ι
  结论: (beckFork X).ι = X.a
  证明: rfl
-/
theorem beckFork_ι : (beckFork X).ι = X.a :=
  rfl

/--
Definition of `beckEqualizer` / `beckEqualizer` 的定义

English:
definition beckEqualizer
  signature: : IsLimit (beckFork X)
  body: (beckSplitEqualizer X).isEqualizer

@[simp]

中文:
定义 beckEqualizer
  签名: : IsLimit (beckFork X)
  定义体: (beckSplitEqualizer X).isEqualizer

@[simp]

Depends on / 依赖: beckSplitEqualizer, isEqualizer
-/
def beckEqualizer : IsLimit (beckFork X) :=
  (beckSplitEqualizer X).isEqualizer

@[simp]
/--
theorem `beckEqualizer_lift` / 定理 `beckEqualizer_lift`

English:
theorem beckEqualizer_lift
  given: (s : Fork (T.toFunctor.map X.a) (T.δ.app X.A))
  proof: rfl

中文:
定理 beckEqualizer_lift
  条件: (s : Fork (T.toFunctor.map X.a) (T.δ.app X.A))
  证明: rfl
-/
theorem beckEqualizer_lift (s : Fork (T.toFunctor.map X.a) (T.δ.app X.A)) :
    (beckEqualizer X).lift s = s.ι ≫ T.ε.app _ :=
  rfl

end Comonad

end CategoryTheory
