/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Reflexive
public import Mathlib.CategoryTheory.Limits.Shapes.SplitCoequalizer
public import Mathlib.CategoryTheory.Monad.Algebra

/-!
# Special coequalizers associated to a monad

Associated to a monad `T : C ⥤ C` we have important coequalizer constructions:
Any algebra is a coequalizer (in the category of algebras) of free algebras. Furthermore, this
coequalizer is reflexive.
In `C`, this cofork diagram is a split coequalizer (in particular, it is still a coequalizer).
This split coequalizer is known as the Beck coequalizer (as it features heavily in Beck's
monadicity theorem).

This file has been adapted to `Mathlib/CategoryTheory/Monad/Equalizer.lean`.
Please try to keep them in sync.

-/

@[expose] public section


universe v₁ u₁

namespace CategoryTheory

namespace Monad

open Limits

variable {C : Type u₁}
variable [Category.{v₁} C]
variable {T : Monad C} (X : Algebra T)

/-!
Show that any algebra is a coequalizer of free algebras.
-/


/-- The top map in the coequalizer diagram we will construct. -/
@[simps!]
/--
Definition of `FreeCoequalizer.topMap` / `FreeCoequalizer.topMap` 的定义

English:
definition FreeCoequalizer.topMap
  signature: : (Monad.free T).obj (T.obj X.A) ⟶ (Monad.free T).obj X.A
  body: (Monad.free T).map X.a

中文:
定义 FreeCoequalizer.topMap
  签名: : (Monad.free T).obj (T.obj X.A) ⟶ (Monad.free T).obj X.A
  定义体: (Monad.free T).map X.a

Depends on / 依赖: Monad.free
-/
def FreeCoequalizer.topMap : (Monad.free T).obj (T.obj X.A) ⟶ (Monad.free T).obj X.A :=
  (Monad.free T).map X.a

/-- The bottom map in the coequalizer diagram we will construct. -/
@[simps]
/--
Definition of `FreeCoequalizer.bottomMap` / `FreeCoequalizer.bottomMap` 的定义

English:
definition FreeCoequalizer.bottomMap
  signature: : (Monad.free T).obj (T.obj X.A) ⟶ (Monad.free T).obj X.A where
  body: T.μ.app X.A
  h := T.assoc X.A

中文:
定义 FreeCoequalizer.bottomMap
  签名: : (Monad.free T).obj (T.obj X.A) ⟶ (Monad.free T).obj X.A where
  定义体: T.μ.app X.A
  h := T.assoc X.A
-/
def FreeCoequalizer.bottomMap : (Monad.free T).obj (T.obj X.A) ⟶ (Monad.free T).obj X.A where
  f := T.μ.app X.A
  h := T.assoc X.A

/-- The cofork map in the coequalizer diagram we will construct. -/
@[simps]
/--
Definition of `FreeCoequalizer.π` / `FreeCoequalizer.π` 的定义

English:
definition FreeCoequalizer.π
  signature: : (Monad.free T).obj X.A ⟶ X where
  body: X.a
  h := X.assoc.symm

中文:
定义 FreeCoequalizer.π
  签名: : (Monad.free T).obj X.A ⟶ X where
  定义体: X.a
  h := X.assoc.symm
-/
def FreeCoequalizer.π : (Monad.free T).obj X.A ⟶ X where
  f := X.a
  h := X.assoc.symm

/--
theorem `FreeCoequalizer.condition` / 定理 `FreeCoequalizer.condition`

English:
theorem FreeCoequalizer.condition
  proof: Algebra.Hom.ext X.assoc.symm

中文:
定理 FreeCoequalizer.condition
  证明: Algebra.Hom.ext X.assoc.symm

Depends on / 依赖: Algebra, Algebra.Hom.ext, X.assoc.symm
-/
theorem FreeCoequalizer.condition :
    FreeCoequalizer.topMap X ≫ FreeCoequalizer.π X =
      FreeCoequalizer.bottomMap X ≫ FreeCoequalizer.π X :=
  Algebra.Hom.ext X.assoc.symm

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsReflexivePair (FreeCoequalizer.topMap X) (FreeCoequalizer.bottomMap X)
  body: by
  apply IsReflexivePair.mk' _ _ _
  · apply (free T).map (T.η.app X.A)
  · ext
    dsimp
    rw [← Functor.map_comp]; rw [X.unit]; rw [Functor.map_id]
  · ext
    apply Monad.right_unit

中文:
实例 :
  签名: IsReflexivePair (FreeCoequalizer.topMap X) (FreeCoequalizer.bottomMap X)
  定义体: by
  apply IsReflexivePair.mk' _ _ _
  · apply (free T).map (T.η.app X.A)
  · ext
    dsimp
    rw [← Functor.map_comp]; rw [X.unit]; rw [Functor.map_id]
  · ext
    apply Monad.right_unit

Depends on / 依赖: Functor, Functor.map_comp, Functor.map_id, IsReflexivePair, IsReflexivePair.mk, Monad.right_unit, X.unit, map_comp, map_id, right_unit
-/
instance : IsReflexivePair (FreeCoequalizer.topMap X) (FreeCoequalizer.bottomMap X) := by
  apply IsReflexivePair.mk' _ _ _
  · apply (free T).map (T.η.app X.A)
  · ext
    dsimp
    rw [← Functor.map_comp]; rw [X.unit]; rw [Functor.map_id]
  · ext
    apply Monad.right_unit

/-- Construct the Beck cofork in the category of algebras. This cofork is reflexive as well as a
coequalizer.
-/
@[simps!]
/--
Definition of `beckAlgebraCofork` / `beckAlgebraCofork` 的定义

English:
definition beckAlgebraCofork
  signature: : Cofork (FreeCoequalizer.topMap X) (FreeCoequalizer.bottomMap X)
  body: Cofork.ofπ _ (FreeCoequalizer.condition X)

中文:
定义 beckAlgebraCofork
  签名: : Cofork (FreeCoequalizer.topMap X) (FreeCoequalizer.bottomMap X)
  定义体: Cofork.ofπ _ (FreeCoequalizer.condition X)

Depends on / 依赖: Cofork, Cofork.of, FreeCoequalizer, FreeCoequalizer.condition, condition
-/
def beckAlgebraCofork : Cofork (FreeCoequalizer.topMap X) (FreeCoequalizer.bottomMap X) :=
  Cofork.ofπ _ (FreeCoequalizer.condition X)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `beckAlgebraCoequalizer` / `beckAlgebraCoequalizer` 的定义

English:
definition beckAlgebraCoequalizer
  signature: : IsColimit (beckAlgebraCofork X)
  body: Cofork.IsColimit.mk' _ fun s => by
    have h₁ : (T : C ⥤ C).map X.a ≫ s.π.f = T.μ.app X.A ≫ s.π.f :=
      congr_arg Monad.Algebra.Hom.f s.condition
    have h₂ : (T : C ⥤ C).map s.π.f ≫ s.pt.a = T.μ.app X.A ≫ s.π.f := s.π.h
    refine ⟨⟨T.η.app _ ≫ s.π.f, ?_⟩, ?_, ?_⟩
    · dsimp
      rw [Functor

中文:
定义 beckAlgebraCoequalizer
  签名: : IsColimit (beckAlgebraCofork X)
  定义体: Cofork.IsColimit.mk' _ fun s => by
    have h₁ : (T : C ⥤ C).map X.a ≫ s.π.f = T.μ.app X.A ≫ s.π.f :=
      congr_arg Monad.Algebra.Hom.f s.condition
    have h₂ : (T : C ⥤ C).map s.π.f ≫ s.pt.a = T.μ.app X.A ≫ s.π.f := s.π.h
    refine ⟨⟨T.η.app _ ≫ s.π.f, ?_⟩, ?_, ?_⟩
    · dsimp
      rw [Functor

Depends on / 依赖: Algebra, Category, Category.assoc, Cofork, Cofork.IsColimit.mk, Functor, Functor.map_comp, IsColimit, Monad.Algebra.Hom.f, Monad.left_unit_assoc, Monad.right_unit_assoc, T.left_unit_assoc, condition, congr_arg, left_unit_assoc, map_comp, naturality_assoc, right_unit_assoc, s.condition, s.pt.a
-/
def beckAlgebraCoequalizer : IsColimit (beckAlgebraCofork X) :=
  Cofork.IsColimit.mk' _ fun s => by
    have h₁ : (T : C ⥤ C).map X.a ≫ s.π.f = T.μ.app X.A ≫ s.π.f :=
      congr_arg Monad.Algebra.Hom.f s.condition
    have h₂ : (T : C ⥤ C).map s.π.f ≫ s.pt.a = T.μ.app X.A ≫ s.π.f := s.π.h
    refine ⟨⟨T.η.app _ ≫ s.π.f, ?_⟩, ?_, ?_⟩
    · dsimp
      rw [Functor.map_comp]; rw [Category.assoc]; rw [h₂]; rw [Monad.right_unit_assoc]; rw [show X.a ≫ _ ≫ _ = _ from T.η.naturality_assoc _ _]; rw [h₁]; rw [Monad.left_unit_assoc]
    · ext
      simpa [← T.η.naturality_assoc, T.left_unit_assoc] using! T.η.app ((T : C ⥤ C).obj X.A) ≫= h₁
    · intro m hm
      ext
      dsimp only
      rw [← hm]
      apply (X.unit_assoc _).symm

/--
Definition of `beckSplitCoequalizer` / `beckSplitCoequalizer` 的定义

English:
definition beckSplitCoequalizer
  signature: : IsSplitCoequalizer (T.map X.a) (T.μ.app _) X.a
  body: ⟨T.η.app _, T.η.app _, X.assoc.symm, X.unit, T.left_unit _, (T.η.naturality _).symm⟩

中文:
定义 beckSplitCoequalizer
  签名: : IsSplitCoequalizer (T.map X.a) (T.μ.app _) X.a
  定义体: ⟨T.η.app _, T.η.app _, X.assoc.symm, X.unit, T.left_unit _, (T.η.naturality _).symm⟩

Depends on / 依赖: T.left_unit, X.assoc.symm, X.unit, left_unit, naturality
-/
def beckSplitCoequalizer : IsSplitCoequalizer (T.map X.a) (T.μ.app _) X.a :=
  ⟨T.η.app _, T.η.app _, X.assoc.symm, X.unit, T.left_unit _, (T.η.naturality _).symm⟩

/-- This is the Beck cofork. It is a split coequalizer, in particular a coequalizer. -/
@[simps! pt]
/--
Definition of `beckCofork` / `beckCofork` 的定义

English:
definition beckCofork
  signature: : Cofork (T.map X.a) (T.μ.app _)
  body: (beckSplitCoequalizer X).asCofork

@[simp]

中文:
定义 beckCofork
  签名: : Cofork (T.map X.a) (T.μ.app _)
  定义体: (beckSplitCoequalizer X).asCofork

@[simp]

Depends on / 依赖: asCofork, beckSplitCoequalizer
-/
def beckCofork : Cofork (T.map X.a) (T.μ.app _) :=
  (beckSplitCoequalizer X).asCofork

@[simp]
/--
theorem `beckCofork_π` / 定理 `beckCofork_π`

English:
theorem beckCofork_π
  statement: (beckCofork X).π = X.a
  proof: rfl

中文:
定理 beckCofork_π
  结论: (beckCofork X).π = X.a
  证明: rfl
-/
theorem beckCofork_π : (beckCofork X).π = X.a :=
  rfl

/--
Definition of `beckCoequalizer` / `beckCoequalizer` 的定义

English:
definition beckCoequalizer
  signature: : IsColimit (beckCofork X)
  body: (beckSplitCoequalizer X).isCoequalizer

@[simp]

中文:
定义 beckCoequalizer
  签名: : IsColimit (beckCofork X)
  定义体: (beckSplitCoequalizer X).isCoequalizer

@[simp]

Depends on / 依赖: beckSplitCoequalizer, isCoequalizer
-/
def beckCoequalizer : IsColimit (beckCofork X) :=
  (beckSplitCoequalizer X).isCoequalizer

@[simp]
/--
theorem `beckCoequalizer_desc` / 定理 `beckCoequalizer_desc`

English:
theorem beckCoequalizer_desc
  given: (s : Cofork (T.toFunctor.map X.a) (T.μ.app X.A))
  proof: rfl

中文:
定理 beckCoequalizer_desc
  条件: (s : Cofork (T.toFunctor.map X.a) (T.μ.app X.A))
  证明: rfl
-/
theorem beckCoequalizer_desc (s : Cofork (T.toFunctor.map X.a) (T.μ.app X.A)) :
    (beckCoequalizer X).desc s = T.η.app _ ≫ s.π :=
  rfl

end Monad

end CategoryTheory
