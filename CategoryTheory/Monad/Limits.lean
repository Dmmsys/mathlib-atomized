/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta, Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
# Limits and colimits in the category of (co)algebras

This file shows that the forgetful functor `forget T : Algebra T ⥤ C` for a monad `T : C ⥤ C`
creates limits and creates any colimits which `T` preserves.
This is used to show that `Algebra T` has any limits which `C` has, and any colimits which `C` has
and `T` preserves.
This is generalised to the case of a monadic functor `D ⥤ C`.

Dually, this file shows that the forgetful functor `forget T : Coalgebra T ⥤ C` for a
comonad `T : C ⥤ C` creates colimits and creates any limits which `T` preserves.
This is used to show that `Coalgebra T` has any colimits which `C` has, and any limits which `C` has
and `T` preserves.
This is generalised to the case of a comonadic functor `D ⥤ C`.
-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section


namespace CategoryTheory

open Category CategoryTheory.Functor

open CategoryTheory.Limits

universe v u v₁ v₂ u₁ u₂

-- morphism levels before object levels. See note [category_theory universes].
namespace Monad

variable {C : Type u₁} [Category.{v₁} C]
variable {T : Monad C}
variable {J : Type u} [Category.{v} J]

namespace ForgetCreatesLimits

variable (D : J ⥤ Algebra T) (c : Cone (D ⋙ T.forget)) (t : IsLimit c)

set_option backward.defeqAttrib.useBackward true in
/-- (Impl) The natural transformation used to define the new cone -/
@[simps]
/--
Definition of `γ` / `γ` 的定义

English:
definition γ
  signature: : D ⋙ T.forget ⋙ ↑T ⟶ D ⋙ T.forget where app j
  body: (D.obj j).a

中文:
定义 γ
  签名: : D ⋙ T.forget ⋙ ↑T ⟶ D ⋙ T.forget where app j
  定义体: (D.obj j).a

Depends on / 依赖: D.obj
-/
def γ : D ⋙ T.forget ⋙ ↑T ⟶ D ⋙ T.forget where app j := (D.obj j).a

/-- (Impl) This new cone is used to construct the algebra structure -/
@[simps! π_app]
/--
Definition of `newCone` / `newCone` 的定义

English:
definition newCone
  signature: : Cone (D ⋙ forget T) where
  body: T.obj c.pt
  π := (Functor.constComp _ _ (T : C ⥤ C)).inv ≫ whiskerRight c.π (T : C ⥤ C) ≫ γ D

中文:
定义 newCone
  签名: : 锥 (D ⋙ forget T) where
  定义体: T.obj c.pt
  π := (Functor.constComp _ _ (T : C ⥤ C)).inv ≫ whiskerRight c.π (T : C ⥤ C) ≫ γ D

Depends on / 依赖: T.obj, c.pt
-/
def newCone : Cone (D ⋙ forget T) where
  pt := T.obj c.pt
  π := (Functor.constComp _ _ (T : C ⥤ C)).inv ≫ whiskerRight c.π (T : C ⥤ C) ≫ γ D

set_option backward.isDefEq.respectTransparency false in
/-- The algebra structure which will be the apex of the new limit cone for `D`. -/
@[simps]
/--
Definition of `conePoint` / `conePoint` 的定义

English:
definition conePoint
  signature: : Algebra T where
  body: c.pt
  a := t.lift (newCone D c)
  unit :=
    t.hom_ext fun j => by
      rw [Category.assoc]; rw [t.fac]; rw [newCone_π_app]; rw [← T.η.naturality_assoc]; rw [Functor.id_map]; rw [(D.obj j).unit]
      simp
  assoc :=
    t.hom_ext fun j => by
      rw [Category.assoc]; rw [Category.assoc]; rw [t.fac (newCone D c)]; rw [newCone_π_app]; rw [←
        Functor.map_comp_assoc]; rw [t.fac (newCone D c)]; rw [newCone_π_app]; rw [← T.μ.naturality_assoc]; rw [(D.obj j).assoc]; rw [Functor.map_comp]; rw [Category.assoc]
      rfl

中文:
定义 conePoint
  签名: : 代数 T where
  定义体: c.pt
  a := t.lift (newCone D c)
  unit :=
    t.hom_ext fun j => by
      rw [Category.assoc]; rw [t.fac]; rw [newCone_π_app]; rw [← T.η.naturality_assoc]; rw [Functor.id_map]; rw [(D.obj j).unit]
      simp
  assoc :=
    t.hom_ext fun j => by
      rw [Category.assoc]; rw [Category.assoc]; rw [t.fac (newCone D c)]; rw [newCone_π_app]; rw [←
        Functor.map_comp_assoc]; rw [t.fac (newCone D c)]; rw [newCone_π_app]; rw [← T.μ.naturality_assoc]; rw [(D.obj j).assoc]; rw [Functor.map_comp]; rw [Category.assoc]
      rfl

Depends on / 依赖: c.pt
-/
def conePoint : Algebra T where
  A := c.pt
  a := t.lift (newCone D c)
  unit :=
    t.hom_ext fun j => by
      rw [Category.assoc]; rw [t.fac]; rw [newCone_π_app]; rw [← T.η.naturality_assoc]; rw [Functor.id_map]; rw [(D.obj j).unit]
      simp
  assoc :=
    t.hom_ext fun j => by
      rw [Category.assoc]; rw [Category.assoc]; rw [t.fac (newCone D c)]; rw [newCone_π_app]; rw [←
        Functor.map_comp_assoc]; rw [t.fac (newCone D c)]; rw [newCone_π_app]; rw [← T.μ.naturality_assoc]; rw [(D.obj j).assoc]; rw [Functor.map_comp]; rw [Category.assoc]
      rfl

set_option backward.isDefEq.respectTransparency false in
/-- (Impl) Construct the lifted cone in `Algebra T` which will be limiting. -/
@[simps]
/--
Definition of `liftedCone` / `liftedCone` 的定义

English:
definition liftedCone
  signature: : Cone D where
  body: conePoint D c t
  π :=
    { app := fun j => { f := c.π.app j }
      naturality := fun X Y f => by
        ext1
        simpa using (c.w f).symm }

中文:
定义 liftedCone
  签名: : 锥 D where
  定义体: conePoint D c t
  π :=
    { app := fun j => { f := c.π.app j }
      naturality := fun X Y f => by
        ext1
        simpa using (c.w f).symm }

Depends on / 依赖: conePoint
-/
def liftedCone : Cone D where
  pt := conePoint D c t
  π :=
    { app := fun j => { f := c.π.app j }
      naturality := fun X Y f => by
        ext1
        simpa using (c.w f).symm }

set_option backward.isDefEq.respectTransparency false in
/-- (Impl) Prove that the lifted cone is limiting. -/
@[simps]
/--
Definition of `liftedConeIsLimit` / `liftedConeIsLimit` 的定义

English:
definition liftedConeIsLimit
  signature: : IsLimit (liftedCone D c t) where
  body: { f := t.lift ((forget T).mapCone s)
      h :=
        t.hom_ext fun j => by
          dsimp
          rw [Category.assoc]; rw [Category.assoc]; rw [t.fac]; rw [newCone_π_app]; rw [← Functor.map_comp_assoc]; rw [t.fac]; rw [Functor.mapCone_π_app]
          apply (s.π.app j).h }
  uniq s m J := by
    ext1
    apply t.hom_ext
    intro j
    simpa [t.fac ((forget T).mapCone s) j] using congr_arg Algebra.Hom.f (J j)

中文:
定义 liftedConeIsLimit
  签名: : 是极限 (liftedCone D c t) where
  定义体: { f := t.lift ((forget T).mapCone s)
      h :=
        t.hom_ext fun j => by
          dsimp
          rw [Category.assoc]; rw [Category.assoc]; rw [t.fac]; rw [newCone_π_app]; rw [← Functor.map_comp_assoc]; rw [t.fac]; rw [Functor.mapCone_π_app]
          apply (s.π.app j).h }
  uniq s m J := by
    ext1
    apply t.hom_ext
    intro j
    simpa [t.fac ((forget T).mapCone s) j] using congr_arg Algebra.Hom.f (J j)

Depends on / 依赖: Algebra, Algebra.Hom.f, Category, Category.assoc, Functor, Functor.mapCone_, Functor.map_comp_assoc, congr_arg, forget, hom_ext, mapCone, map_comp_assoc, t.fac, t.hom_ext, t.lift
-/
def liftedConeIsLimit : IsLimit (liftedCone D c t) where
  lift s :=
    { f := t.lift ((forget T).mapCone s)
      h :=
        t.hom_ext fun j => by
          dsimp
          rw [Category.assoc]; rw [Category.assoc]; rw [t.fac]; rw [newCone_π_app]; rw [← Functor.map_comp_assoc]; rw [t.fac]; rw [Functor.mapCone_π_app]
          apply (s.π.app j).h }
  uniq s m J := by
    ext1
    apply t.hom_ext
    intro j
    simpa [t.fac ((forget T).mapCone s) j] using congr_arg Algebra.Hom.f (J j)

end ForgetCreatesLimits

-- Theorem 5.6.5 from [Riehl][riehl2017]
/--
Instance `forgetCreatesLimits` / 实例 `forgetCreatesLimits`

English:
instance forgetCreatesLimits
  signature: : CreatesLimitsOfSize (forget T) where
  body: {
    CreatesLimit := fun {D} =>
      createsLimitOfReflectsIso fun c t =>
        { liftedCone := ForgetCreatesLimits.liftedCone D c t
          validLift := Cone.ext (Iso.refl _) fun _ => (id_comp _).symm
          makesLimit := ForgetCreatesLimits.liftedConeIsLimit _ _ _ } }

中文:
实例 forgetCreatesLimits
  签名: : CreatesLimitsOfSize (forget T) where
  定义体: {
    CreatesLimit := fun {D} =>
      createsLimitOfReflectsIso fun c t =>
        { liftedCone := ForgetCreatesLimits.liftedCone D c t
          validLift := Cone.ext (Iso.refl _) fun _ => (id_comp _).symm
          makesLimit := ForgetCreatesLimits.liftedConeIsLimit _ _ _ } }
-/
noncomputable instance forgetCreatesLimits : CreatesLimitsOfSize (forget T) where
  CreatesLimitsOfShape := {
    CreatesLimit := fun {D} =>
      createsLimitOfReflectsIso fun c t =>
        { liftedCone := ForgetCreatesLimits.liftedCone D c t
          validLift := Cone.ext (Iso.refl _) fun _ => (id_comp _).symm
          makesLimit := ForgetCreatesLimits.liftedConeIsLimit _ _ _ } }

/--
theorem `hasLimit_of_comp_forget_hasLimit` / 定理 `hasLimit_of_comp_forget_hasLimit`

English:
theorem hasLimit_of_comp_forget_hasLimit
  given: (D : J ⥤ Algebra T) [HasLimit (D ⋙ forget T)]
  proof: hasLimit_of_created D (forget T)

中文:
定理 hasLimit_of_comp_forget_hasLimit
  条件: (D : J ⥤ 代数 T) [有极限 (D ⋙ forget T)]
  证明: hasLimit_of_created D (forget T)

Depends on / 依赖: forget, hasLimit_of_created
-/
theorem hasLimit_of_comp_forget_hasLimit (D : J ⥤ Algebra T) [HasLimit (D ⋙ forget T)] :
    HasLimit D :=
  hasLimit_of_created D (forget T)

namespace ForgetCreatesColimits

-- Let's hide the implementation details in a namespace
variable {D : J ⥤ Algebra T} (c : Cocone (D ⋙ forget T)) (t : IsColimit c)

-- We have a diagram D of shape J in the category of algebras, and we assume that we are given a
-- colimit for its image D ⋙ forget T under the forgetful functor, say its point is L.
-- We'll construct a colimiting coalgebra for D, whose carrier will also be L.
-- To do this, we must find a map TL ⟶ L. Since T preserves colimits, TL is also a colimit.
-- In particular, it is a colimit for the diagram `(D ⋙ forget T) ⋙ T`
-- so to construct a map TL ⟶ L it suffices to show that L is the point of a cocone for this
-- diagram. In other words, we need a natural transformation from const L to `(D ⋙ forget T) ⋙ T`.
-- But we already know that L is the point of a cocone for the diagram `D ⋙ forget T`, so it
-- suffices to give a natural transformation `((D ⋙ forget T) ⋙ T) ⟶ (D ⋙ forget T)`:
/-- (Impl)
The natural transformation given by the algebra structure maps, used to construct a cocone `c` with
point `colimit (D ⋙ forget T)`.
-/
@[simps]
/--
Definition of `γ` / `γ` 的定义

English:
definition γ
  signature: : (D ⋙ forget T) ⋙ ↑T ⟶ D ⋙ forget T where app j
  body: (D.obj j).a

中文:
定义 γ
  签名: : (D ⋙ forget T) ⋙ ↑T ⟶ D ⋙ forget T where app j
  定义体: (D.obj j).a

Depends on / 依赖: D.obj
-/
def γ : (D ⋙ forget T) ⋙ ↑T ⟶ D ⋙ forget T where app j := (D.obj j).a

/-- (Impl)
A cocone for the diagram `(D ⋙ forget T) ⋙ T` found by composing the natural transformation `γ`
with the colimiting cocone for `D ⋙ forget T`.
-/
@[simps]
/--
Definition of `newCocone` / `newCocone` 的定义

English:
definition newCocone
  signature: : Cocone ((D ⋙ forget T) ⋙ (T : C ⥤ C)) where
  body: c.pt
  ι := γ ≫ c.ι

中文:
定义 newCocone
  签名: : 余锥 ((D ⋙ forget T) ⋙ (T : C ⥤ C)) where
  定义体: c.pt
  ι := γ ≫ c.ι

Depends on / 依赖: c.pt
-/
def newCocone : Cocone ((D ⋙ forget T) ⋙ (T : C ⥤ C)) where
  pt := c.pt
  ι := γ ≫ c.ι

variable [PreservesColimit (D ⋙ forget T) (T : C ⥤ C)]

/--
Definition of `lambda` / `lambda` 的定义

English:
abbreviation lambda
  signature: : ((T : C ⥤ C).mapCocone c).pt ⟶ c.pt
  body: (isColimitOfPreserves _ t).desc (newCocone c)

中文:
缩写 lambda
  签名: : ((T : C ⥤ C).mapCocone c).pt ⟶ c.pt
  定义体: (isColimitOfPreserves _ t).desc (newCocone c)

Depends on / 依赖: isColimitOfPreserves, newCocone
-/
noncomputable abbrev lambda : ((T : C ⥤ C).mapCocone c).pt ⟶ c.pt :=
  (isColimitOfPreserves _ t).desc (newCocone c)

/--
theorem `commuting` / 定理 `commuting`

English:
theorem commuting
  given: (j : J)
  statement: (T : C ⥤ C).map (c.ι.app j) ≫ lambda c t = (D.obj j).a ≫ c.ι.app j
  proof: (isColimitOfPreserves _ t).fac (newCocone c) j

中文:
定理 commuting
  条件: (j : J)
  结论: (T : C ⥤ C).map (c.ι.app j) ≫ lambda c t = (D.obj j).a ≫ c.ι.app j
  证明: (isColimitOfPreserves _ t).fac (newCocone c) j

Depends on / 依赖: isColimitOfPreserves, newCocone
-/
theorem commuting (j : J) : (T : C ⥤ C).map (c.ι.app j) ≫ lambda c t = (D.obj j).a ≫ c.ι.app j :=
  (isColimitOfPreserves _ t).fac (newCocone c) j

variable [PreservesColimit ((D ⋙ forget T) ⋙ ↑T) (T : C ⥤ C)]

set_option backward.isDefEq.respectTransparency false in
/-- (Impl)
Construct the colimiting algebra from the map `λ : TL ⟶ L` given by `lambda`. We are required to
show it satisfies the two algebra laws, which follow from the algebra laws for the image of `D` and
our `commuting` lemma.
-/
@[simps]
/--
Definition of `coconePoint` / `coconePoint` 的定义

English:
definition coconePoint
  signature: : Algebra T where
  body: c.pt
  a := lambda c t
  unit := by
    apply t.hom_ext
    intro j
    rw [show c.ι.app j ≫ T.η.app c.pt ≫ _ = T.η.app (D.obj j).A ≫ _ ≫ _ from
        T.η.naturality_assoc _ _]; rw [commuting]; rw [Algebra.unit_assoc (D.obj j)]
    simp
  assoc := by
    refine (isColimitOfPreserves _ (isColimitOfPreserves _ t)).hom_ext fun j => ?_
    rw [Functor.mapCocone_ι_app]; rw [Functor.mapCocone_ι_app]; rw [show (T : C ⥤ C).map ((T : C ⥤ C).map _) ≫ _ ≫ _ = _ from T.μ.naturality_assoc _ _]; rw [←
      Functor.map_comp_assoc]; rw [commuting]; rw [Functor.map_comp]; rw [Category.assoc]; rw [commuting]
    apply (D.obj j).assoc_assoc _

中文:
定义 coconePoint
  签名: : 代数 T where
  定义体: c.pt
  a := lambda c t
  unit := by
    apply t.hom_ext
    intro j
    rw [show c.ι.app j ≫ T.η.app c.pt ≫ _ = T.η.app (D.obj j).A ≫ _ ≫ _ from
        T.η.naturality_assoc _ _]; rw [commuting]; rw [Algebra.unit_assoc (D.obj j)]
    simp
  assoc := by
    refine (isColimitOfPreserves _ (isColimitOfPreserves _ t)).hom_ext fun j => ?_
    rw [Functor.mapCocone_ι_app]; rw [Functor.mapCocone_ι_app]; rw [show (T : C ⥤ C).map ((T : C ⥤ C).map _) ≫ _ ≫ _ = _ from T.μ.naturality_assoc _ _]; rw [←
      Functor.map_comp_assoc]; rw [commuting]; rw [Functor.map_comp]; rw [Category.assoc]; rw [commuting]
    apply (D.obj j).assoc_assoc _

Depends on / 依赖: c.pt
-/
noncomputable def coconePoint : Algebra T where
  A := c.pt
  a := lambda c t
  unit := by
    apply t.hom_ext
    intro j
    rw [show c.ι.app j ≫ T.η.app c.pt ≫ _ = T.η.app (D.obj j).A ≫ _ ≫ _ from
        T.η.naturality_assoc _ _]; rw [commuting]; rw [Algebra.unit_assoc (D.obj j)]
    simp
  assoc := by
    refine (isColimitOfPreserves _ (isColimitOfPreserves _ t)).hom_ext fun j => ?_
    rw [Functor.mapCocone_ι_app]; rw [Functor.mapCocone_ι_app]; rw [show (T : C ⥤ C).map ((T : C ⥤ C).map _) ≫ _ ≫ _ = _ from T.μ.naturality_assoc _ _]; rw [←
      Functor.map_comp_assoc]; rw [commuting]; rw [Functor.map_comp]; rw [Category.assoc]; rw [commuting]
    apply (D.obj j).assoc_assoc _

set_option backward.isDefEq.respectTransparency.types false in
/-- (Impl) Construct the lifted cocone in `Algebra T` which will be colimiting. -/
@[simps]
/--
Definition of `liftedCocone` / `liftedCocone` 的定义

English:
definition liftedCocone
  signature: : Cocone D where
  body: coconePoint c t
  ι :=
    { app := fun j =>
        { f := c.ι.app j
          h := commuting _ _ _ }
      naturality := fun A B f => by
        ext1
        dsimp
        rw [comp_id]
        apply c.w }

中文:
定义 liftedCocone
  签名: : 余锥 D where
  定义体: coconePoint c t
  ι :=
    { app := fun j =>
        { f := c.ι.app j
          h := commuting _ _ _ }
      naturality := fun A B f => by
        ext1
        dsimp
        rw [comp_id]
        apply c.w }

Depends on / 依赖: coconePoint
-/
noncomputable def liftedCocone : Cocone D where
  pt := coconePoint c t
  ι :=
    { app := fun j =>
        { f := c.ι.app j
          h := commuting _ _ _ }
      naturality := fun A B f => by
        ext1
        dsimp
        rw [comp_id]
        apply c.w }

set_option backward.isDefEq.respectTransparency false in
/-- (Impl) Prove that the lifted cocone is colimiting. -/
@[simps]
/--
Definition of `liftedCoconeIsColimit` / `liftedCoconeIsColimit` 的定义

English:
definition liftedCoconeIsColimit
  signature: : IsColimit (liftedCocone c t) where
  body: { f := t.desc ((forget T).mapCocone s)
      h :=
        (isColimitOfPreserves (T : C ⥤ C) t).hom_ext fun j => by
          dsimp
          rw [← Functor.map_comp_assoc]; rw [← Category.assoc]; rw [t.fac]; rw [commuting]; rw [Category.assoc]; rw [t.fac]
          apply Algebra.Hom.h }
  uniq s m J := by
    ext1
    apply t.hom_ext
    intro j
    simpa using congr_arg Algebra.Hom.f (J j)

中文:
定义 liftedCoconeIsColimit
  签名: : 是余极限 (liftedCocone c t) where
  定义体: { f := t.desc ((forget T).mapCocone s)
      h :=
        (isColimitOfPreserves (T : C ⥤ C) t).hom_ext fun j => by
          dsimp
          rw [← Functor.map_comp_assoc]; rw [← Category.assoc]; rw [t.fac]; rw [commuting]; rw [Category.assoc]; rw [t.fac]
          apply Algebra.Hom.h }
  uniq s m J := by
    ext1
    apply t.hom_ext
    intro j
    simpa using congr_arg Algebra.Hom.f (J j)

Depends on / 依赖: Algebra, Algebra.Hom.f, Algebra.Hom.h, Category, Category.assoc, Functor, Functor.map_comp_assoc, commuting, congr_arg, forget, hom_ext, isColimitOfPreserves, mapCocone, map_comp_assoc, t.desc, t.fac, t.hom_ext
-/
noncomputable def liftedCoconeIsColimit : IsColimit (liftedCocone c t) where
  desc s :=
    { f := t.desc ((forget T).mapCocone s)
      h :=
        (isColimitOfPreserves (T : C ⥤ C) t).hom_ext fun j => by
          dsimp
          rw [← Functor.map_comp_assoc]; rw [← Category.assoc]; rw [t.fac]; rw [commuting]; rw [Category.assoc]; rw [t.fac]
          apply Algebra.Hom.h }
  uniq s m J := by
    ext1
    apply t.hom_ext
    intro j
    simpa using congr_arg Algebra.Hom.f (J j)

end ForgetCreatesColimits

open ForgetCreatesColimits

-- TODO: the converse of this is true as well
set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `forgetCreatesColimit` / 实例 `forgetCreatesColimit`

English:
instance forgetCreatesColimit
  signature: (D : J ⥤ Algebra T)
  body: createsColimitOfReflectsIso fun c t =>
    { liftedCocone :=
        { pt := coconePoint c t
          ι :=
            { app := fun j =>
                { f := c.ι.app j
                  h := commuting _ _ _ }
              naturality := fun A B f => by
                ext1
                simpa using (c.w f) } }
      validLift := Cocone.ext (Iso.refl _)
      makesColimit := liftedCoconeIsColimit _ _ }

中文:
实例 forgetCreatesColimit
  签名: (D : J ⥤ 代数 T)
  定义体: createsColimitOfReflectsIso fun c t =>
    { liftedCocone :=
        { pt := coconePoint c t
          ι :=
            { app := fun j =>
                { f := c.ι.app j
                  h := commuting _ _ _ }
              naturality := fun A B f => by
                ext1
                simpa using (c.w f) } }
      validLift := Cocone.ext (Iso.refl _)
      makesColimit := liftedCoconeIsColimit _ _ }

Depends on / 依赖: Cocone, Cocone.ext, Iso.refl, coconePoint, commuting, createsColimitOfReflectsIso, liftedCocone, liftedCoconeIsColimit, makesColimit, naturality, validLift
-/
noncomputable instance forgetCreatesColimit (D : J ⥤ Algebra T)
    [PreservesColimit (D ⋙ forget T) (T : C ⥤ C)]
    [PreservesColimit ((D ⋙ forget T) ⋙ ↑T) (T : C ⥤ C)] : CreatesColimit D (forget T) :=
  createsColimitOfReflectsIso fun c t =>
    { liftedCocone :=
        { pt := coconePoint c t
          ι :=
            { app := fun j =>
                { f := c.ι.app j
                  h := commuting _ _ _ }
              naturality := fun A B f => by
                ext1
                simpa using (c.w f) } }
      validLift := Cocone.ext (Iso.refl _)
      makesColimit := liftedCoconeIsColimit _ _ }

/--
Instance `forgetCreatesColimitsOfShape` / 实例 `forgetCreatesColimitsOfShape`

English:
instance forgetCreatesColimitsOfShape
  signature: [PreservesColimitsOfShape J (T : C ⥤ C)]
  body: by infer_instance

中文:
实例 forgetCreatesColimitsOfShape
  签名: [保持形状余极限 J (T : C ⥤ C)]
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
noncomputable instance forgetCreatesColimitsOfShape [PreservesColimitsOfShape J (T : C ⥤ C)] :
    CreatesColimitsOfShape J (forget T) where CreatesColimit := by infer_instance

/--
Instance `forgetCreatesColimits` / 实例 `forgetCreatesColimits`

English:
instance forgetCreatesColimits
  signature: [PreservesColimitsOfSize.{v, u} (T : C ⥤ C)]
  body: by infer_instance

中文:
实例 forgetCreatesColimits
  签名: [保持余limitsOfSize.{v, u} (T : C ⥤ C)]
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
noncomputable instance forgetCreatesColimits [PreservesColimitsOfSize.{v, u} (T : C ⥤ C)] :
    CreatesColimitsOfSize.{v, u} (forget T) where CreatesColimitsOfShape := by infer_instance

/--
theorem `forget_creates_colimits_of_monad_preserves` / 定理 `forget_creates_colimits_of_monad_preserves`

English:
theorem forget_creates_colimits_of_monad_preserves
  statement: [PreservesColimitsOfShape J (T : C ⥤ C)]
  proof: hasColimit_of_created D (forget T)

中文:
定理 forget_creates_colimits_of_monad_preserves
  结论: [保持形状余极限 J (T : C ⥤ C)]
  证明: hasColimit_of_created D (forget T)

Depends on / 依赖: forget, hasColimit_of_created
-/
theorem forget_creates_colimits_of_monad_preserves [PreservesColimitsOfShape J (T : C ⥤ C)]
    (D : J ⥤ Algebra T) [HasColimit (D ⋙ forget T)] : HasColimit D :=
  hasColimit_of_created D (forget T)

end Monad

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {J : Type u} [Category.{v} J]

/--
Instance `comp_comparison_forget_hasLimit` / 实例 `comp_comparison_forget_hasLimit`

English:
instance comp_comparison_forget_hasLimit
  signature: (F : J ⥤ D) (R : D ⥤ C) [MonadicRightAdjoint R]
  body: by
  assumption

中文:
实例 comp_comparison_forget_hasLimit
  签名: (F : J ⥤ D) (R : D ⥤ C) [MonadicRightAdjoint R]
  定义体: by
  assumption
-/
instance comp_comparison_forget_hasLimit (F : J ⥤ D) (R : D ⥤ C) [MonadicRightAdjoint R]
    [HasLimit (F ⋙ R)] :
    HasLimit ((F ⋙ Monad.comparison (monadicAdjunction R)) ⋙ Monad.forget _) := by
  assumption

/--
Instance `comp_comparison_hasLimit` / 实例 `comp_comparison_hasLimit`

English:
instance comp_comparison_hasLimit
  signature: (F : J ⥤ D) (R : D ⥤ C) [MonadicRightAdjoint R]
  body: Monad.hasLimit_of_comp_forget_hasLimit (F ⋙ Monad.comparison (monadicAdjunction R))

中文:
实例 comp_comparison_hasLimit
  签名: (F : J ⥤ D) (R : D ⥤ C) [MonadicRightAdjoint R]
  定义体: Monad.hasLimit_of_comp_forget_hasLimit (F ⋙ Monad.comparison (monadicAdjunction R))

Depends on / 依赖: Monad.comparison, Monad.hasLimit_of_comp_forget_hasLimit, comparison, hasLimit_of_comp_forget_hasLimit, monadicAdjunction
-/
instance comp_comparison_hasLimit (F : J ⥤ D) (R : D ⥤ C) [MonadicRightAdjoint R]
    [HasLimit (F ⋙ R)] : HasLimit (F ⋙ Monad.comparison (monadicAdjunction R)) :=
  Monad.hasLimit_of_comp_forget_hasLimit (F ⋙ Monad.comparison (monadicAdjunction R))

/-- Any monadic functor creates limits. -/
@[instance_reducible]
/--
Definition of `monadicCreatesLimits` / `monadicCreatesLimits` 的定义

English:
definition monadicCreatesLimits
  signature: (R : D ⥤ C) [MonadicRightAdjoint R]
  body: createsLimitsOfNatIso (Monad.comparisonForget (monadicAdjunction R))

中文:
定义 monadicCreatesLimits
  签名: (R : D ⥤ C) [MonadicRightAdjoint R]
  定义体: createsLimitsOfNatIso (Monad.comparisonForget (monadicAdjunction R))

Depends on / 依赖: Monad.comparisonForget, comparisonForget, createsLimitsOfNatIso, monadicAdjunction
-/
noncomputable def monadicCreatesLimits (R : D ⥤ C) [MonadicRightAdjoint R] :
    CreatesLimitsOfSize.{v, u} R :=
  createsLimitsOfNatIso (Monad.comparisonForget (monadicAdjunction R))

/-- The forgetful functor from the Eilenberg-Moore category for a monad creates any colimit
which the monad itself preserves.
-/
@[instance_reducible]
/--
Definition of `monadicCreatesColimitOfPreservesColimit` / `monadicCreatesColimitOfPreservesColimit` 的定义

English:
definition monadicCreatesColimitOfPreservesColimit
  signature: (R : D ⥤ C) (K : J ⥤ D)
  body: by
  -- Porting note: It would be nice to have a variant of apply which introduces goals for missing
  -- instances.
  letI A := Monad.comparison (monadicAdjunction R)
  letI B := Monad.forget (Adjunction.toMonad (monadicAdjunction R))
  let i : (K ⋙ Monad.comparison (monadicAdjunction R)) ⋙ Monad.forget _ ≅ K ⋙ R :=
    Functor.associator _ _ _ ≪≫
      isoWhiskerLeft K (Monad.comparisonForget (monadicAdjunction R))
  letI : PreservesColimit ((K ⋙ A) ⋙ Monad.forget
    (Adjunction.toMonad (monadicAdjunction R)))
      (Adjunction.toMonad (monadicAdjunction R)).toFunctor := by
    dsimp
    exact preservesColimit_of_iso_diagram _ i.symm
  letI : PreservesColimit
    (((K ⋙ A) ⋙ Monad.forget (Adjunction.toMonad (monadicAdjunction R))) ⋙
      (Adjunction.toMonad (monadicAdjunction R)).toFunctor)
      (Adjunction.toMonad (monadicAdjunction R)).toFunctor := by
    dsimp
    exact preservesColimit_of_iso_diagram _ (isoWhiskerRight i (monadicLeftAdjoint R ⋙ R)).symm
  letI : CreatesColimit (K ⋙ A) B := CategoryTheory.Monad.forgetCreatesColimit _
  letI : CreatesColimit K (A ⋙ B) := CategoryTheory.compCreatesColimit _ _
  let e := Monad.comparisonForget (monadicAdjunction R)
  apply createsColimitOfNatIso e

中文:
定义 monadicCreatesColimitOfPreservesColimit
  签名: (R : D ⥤ C) (K : J ⥤ D)
  定义体: by
  -- Porting note: It would be nice to have a variant of apply which introduces goals for missing
  -- instances.
  letI A := Monad.comparison (monadicAdjunction R)
  letI B := Monad.forget (Adjunction.toMonad (monadicAdjunction R))
  let i : (K ⋙ Monad.comparison (monadicAdjunction R)) ⋙ Monad.forget _ ≅ K ⋙ R :=
    Functor.associator _ _ _ ≪≫
      isoWhiskerLeft K (Monad.comparisonForget (monadicAdjunction R))
  letI : PreservesColimit ((K ⋙ A) ⋙ Monad.forget
    (Adjunction.toMonad (monadicAdjunction R)))
      (Adjunction.toMonad (monadicAdjunction R)).toFunctor := by
    dsimp
    exact preservesColimit_of_iso_diagram _ i.symm
  letI : PreservesColimit
    (((K ⋙ A) ⋙ Monad.forget (Adjunction.toMonad (monadicAdjunction R))) ⋙
      (Adjunction.toMonad (monadicAdjunction R)).toFunctor)
      (Adjunction.toMonad (monadicAdjunction R)).toFunctor := by
    dsimp
    exact preservesColimit_of_iso_diagram _ (isoWhiskerRight i (monadicLeftAdjoint R ⋙ R)).symm
  letI : CreatesColimit (K ⋙ A) B := CategoryTheory.Monad.forgetCreatesColimit _
  letI : CreatesColimit K (A ⋙ B) := CategoryTheory.compCreatesColimit _ _
  let e := Monad.comparisonForget (monadicAdjunction R)
  apply createsColimitOfNatIso e
-/
noncomputable def monadicCreatesColimitOfPreservesColimit (R : D ⥤ C) (K : J ⥤ D)
    [MonadicRightAdjoint R] [PreservesColimit (K ⋙ R) (monadicLeftAdjoint R ⋙ R)]
    [PreservesColimit ((K ⋙ R) ⋙ monadicLeftAdjoint R ⋙ R) (monadicLeftAdjoint R ⋙ R)] :
      CreatesColimit K R := by
  -- Porting note: It would be nice to have a variant of apply which introduces goals for missing
  -- instances.
  letI A := Monad.comparison (monadicAdjunction R)
  letI B := Monad.forget (Adjunction.toMonad (monadicAdjunction R))
  let i : (K ⋙ Monad.comparison (monadicAdjunction R)) ⋙ Monad.forget _ ≅ K ⋙ R :=
    Functor.associator _ _ _ ≪≫
      isoWhiskerLeft K (Monad.comparisonForget (monadicAdjunction R))
  letI : PreservesColimit ((K ⋙ A) ⋙ Monad.forget
    (Adjunction.toMonad (monadicAdjunction R)))
      (Adjunction.toMonad (monadicAdjunction R)).toFunctor := by
    dsimp
    exact preservesColimit_of_iso_diagram _ i.symm
  letI : PreservesColimit
    (((K ⋙ A) ⋙ Monad.forget (Adjunction.toMonad (monadicAdjunction R))) ⋙
      (Adjunction.toMonad (monadicAdjunction R)).toFunctor)
      (Adjunction.toMonad (monadicAdjunction R)).toFunctor := by
    dsimp
    exact preservesColimit_of_iso_diagram _ (isoWhiskerRight i (monadicLeftAdjoint R ⋙ R)).symm
  letI : CreatesColimit (K ⋙ A) B := CategoryTheory.Monad.forgetCreatesColimit _
  letI : CreatesColimit K (A ⋙ B) := CategoryTheory.compCreatesColimit _ _
  let e := Monad.comparisonForget (monadicAdjunction R)
  apply createsColimitOfNatIso e

/-- A monadic functor creates any colimits of shapes it preserves. -/
@[instance_reducible]
/--
Definition of `monadicCreatesColimitsOfShapeOfPreservesColimitsOfShape` / `monadicCreatesColimitsOfShapeOfPreservesColimitsOfShape` 的定义

English:
definition monadicCreatesColimitsOfShapeOfPreservesColimitsOfShape
  signature: (R : D ⥤ C)
  body: letI : PreservesColimitsOfShape J (monadicLeftAdjoint R) := by
    apply (Adjunction.leftAdjoint_preservesColimits (monadicAdjunction R)).1
  letI : PreservesColimitsOfShape J (monadicLeftAdjoint R ⋙ R) := by
    apply CategoryTheory.Limits.comp_preservesColimitsOfShape _ _
  ⟨monadicCreatesColimitOfPreservesColimit _ _⟩

中文:
定义 monadicCreatesColimitsOfShapeOfPreservesColimitsOfShape
  签名: (R : D ⥤ C)
  定义体: letI : PreservesColimitsOfShape J (monadicLeftAdjoint R) := by
    apply (Adjunction.leftAdjoint_preservesColimits (monadicAdjunction R)).1
  letI : PreservesColimitsOfShape J (monadicLeftAdjoint R ⋙ R) := by
    apply CategoryTheory.Limits.comp_preservesColimitsOfShape _ _
  ⟨monadicCreatesColimitOfPreservesColimit _ _⟩

Depends on / 依赖: Adjunction, Adjunction.leftAdjoint_preservesColimits, CategoryTheory, CategoryTheory.Limits.comp_preservesColimitsOfShape, Limits, PreservesColimitsOfShape, comp_preservesColimitsOfShape, leftAdjoint_preservesColimits, monadicAdjunction, monadicCreatesColimitOfPreservesColimit, monadicLeftAdjoint
-/
noncomputable def monadicCreatesColimitsOfShapeOfPreservesColimitsOfShape (R : D ⥤ C)
    [MonadicRightAdjoint R] [PreservesColimitsOfShape J R] : CreatesColimitsOfShape J R :=
  letI : PreservesColimitsOfShape J (monadicLeftAdjoint R) := by
    apply (Adjunction.leftAdjoint_preservesColimits (monadicAdjunction R)).1
  letI : PreservesColimitsOfShape J (monadicLeftAdjoint R ⋙ R) := by
    apply CategoryTheory.Limits.comp_preservesColimitsOfShape _ _
  ⟨monadicCreatesColimitOfPreservesColimit _ _⟩

/-- A monadic functor creates colimits if it preserves colimits. -/
@[instance_reducible]
/--
Definition of `monadicCreatesColimitsOfPreservesColimits` / `monadicCreatesColimitsOfPreservesColimits` 的定义

English:
definition monadicCreatesColimitsOfPreservesColimits
  signature: (R : D ⥤ C) [MonadicRightAdjoint R]
  body: monadicCreatesColimitsOfShapeOfPreservesColimitsOfShape _

中文:
定义 monadicCreatesColimitsOfPreservesColimits
  签名: (R : D ⥤ C) [MonadicRightAdjoint R]
  定义体: monadicCreatesColimitsOfShapeOfPreservesColimitsOfShape _

Depends on / 依赖: monadicCreatesColimitsOfShapeOfPreservesColimitsOfShape
-/
noncomputable def monadicCreatesColimitsOfPreservesColimits (R : D ⥤ C) [MonadicRightAdjoint R]
    [PreservesColimitsOfSize.{v, u} R] : CreatesColimitsOfSize.{v, u} R where
  CreatesColimitsOfShape :=
    monadicCreatesColimitsOfShapeOfPreservesColimitsOfShape _

section

/--
theorem `hasLimit_of_reflective` / 定理 `hasLimit_of_reflective`

English:
theorem hasLimit_of_reflective
  given: (F : J ⥤ D) (R : D ⥤ C) [HasLimit (F ⋙ R)] [Reflective R]
  proof: haveI := monadicCreatesLimits.{v, u} R
  hasLimit_of_created F R

中文:
定理 hasLimit_of_reflective
  条件: (F : J ⥤ D) (R : D ⥤ C) [有极限 (F ⋙ R)] [反射 R]
  证明: haveI := monadicCreatesLimits.{v, u} R
  hasLimit_of_created F R

Depends on / 依赖: hasLimit_of_created, monadicCreatesLimits
-/
theorem hasLimit_of_reflective (F : J ⥤ D) (R : D ⥤ C) [HasLimit (F ⋙ R)] [Reflective R] :
    HasLimit F :=
  haveI := monadicCreatesLimits.{v, u} R
  hasLimit_of_created F R

/--
theorem `hasLimitsOfShape_of_reflective` / 定理 `hasLimitsOfShape_of_reflective`

English:
theorem hasLimitsOfShape_of_reflective
  given: [HasLimitsOfShape J C] (R : D ⥤ C) [Reflective R]
  proof: ⟨fun F => hasLimit_of_reflective F R⟩

中文:
定理 hasLimitsOfShape_of_reflective
  条件: [有形状极限 J C] (R : D ⥤ C) [反射 R]
  证明: ⟨fun F => hasLimit_of_reflective F R⟩

Depends on / 依赖: hasLimit_of_reflective
-/
theorem hasLimitsOfShape_of_reflective [HasLimitsOfShape J C] (R : D ⥤ C) [Reflective R] :
    HasLimitsOfShape J D :=
  ⟨fun F => hasLimit_of_reflective F R⟩

/--
theorem `hasLimits_of_reflective` / 定理 `hasLimits_of_reflective`

English:
theorem hasLimits_of_reflective
  given: (R : D ⥤ C) [HasLimitsOfSize.{v, u} C] [Reflective R]
  proof: ⟨fun _ => hasLimitsOfShape_of_reflective R⟩

中文:
定理 hasLimits_of_reflective
  条件: (R : D ⥤ C) [有LimitsOfSize.{v, u} C] [反射 R]
  证明: ⟨fun _ => hasLimitsOfShape_of_reflective R⟩

Depends on / 依赖: hasLimitsOfShape_of_reflective
-/
theorem hasLimits_of_reflective (R : D ⥤ C) [HasLimitsOfSize.{v, u} C] [Reflective R] :
    HasLimitsOfSize.{v, u} D :=
  ⟨fun _ => hasLimitsOfShape_of_reflective R⟩

/--
theorem `hasColimitsOfShape_of_reflective` / 定理 `hasColimitsOfShape_of_reflective`

English:
theorem hasColimitsOfShape_of_reflective
  given: (R : D ⥤ C) [Reflective R] [HasColimitsOfShape J C]
  proof: fun F => by
      let c := (monadicLeftAdjoint R).mapCocone (colimit.cocone (F ⋙ R))
      let : PreservesColimitsOfShape J _ :=
        (monadicAdjunction R).leftAdjoint_preservesColimits.1
      let t : IsColimit c := isColimitOfPreserves (monadicLeftAdjoint R) (colimit.isColimit _)
      apply HasColimit.mk ⟨_, (IsColimit.precomposeInvEquiv _ _).symm t⟩
      apply
        (isoWhiskerLeft F (asIso (monadicAdjunction R).counit) :) ≪≫ F.rightUnitor

中文:
定理 hasColimitsOfShape_of_reflective
  条件: (R : D ⥤ C) [反射 R] [有形状余极限 J C]
  证明: fun F => by
      let c := (monadicLeftAdjoint R).mapCocone (colimit.cocone (F ⋙ R))
      let : PreservesColimitsOfShape J _ :=
        (monadicAdjunction R).leftAdjoint_preservesColimits.1
      let t : IsColimit c := isColimitOfPreserves (monadicLeftAdjoint R) (colimit.isColimit _)
      apply HasColimit.mk ⟨_, (IsColimit.precomposeInvEquiv _ _).symm t⟩
      apply
        (isoWhiskerLeft F (asIso (monadicAdjunction R).counit) :) ≪≫ F.rightUnitor

Depends on / 依赖: F.rightUnitor, HasColimit, HasColimit.mk, IsColimit, IsColimit.precomposeInvEquiv, PreservesColimitsOfShape, cocone, colimit, colimit.cocone, colimit.isColimit, counit, isColimit, isColimitOfPreserves, isoWhiskerLeft, leftAdjoint_preservesColimits, mapCocone, monadicAdjunction, monadicLeftAdjoint, precomposeInvEquiv, rightUnitor
-/
theorem hasColimitsOfShape_of_reflective (R : D ⥤ C) [Reflective R] [HasColimitsOfShape J C] :
    HasColimitsOfShape J D where
  has_colimit := fun F => by
      let c := (monadicLeftAdjoint R).mapCocone (colimit.cocone (F ⋙ R))
      let : PreservesColimitsOfShape J _ :=
        (monadicAdjunction R).leftAdjoint_preservesColimits.1
      let t : IsColimit c := isColimitOfPreserves (monadicLeftAdjoint R) (colimit.isColimit _)
      apply HasColimit.mk ⟨_, (IsColimit.precomposeInvEquiv _ _).symm t⟩
      apply
        (isoWhiskerLeft F (asIso (monadicAdjunction R).counit) :) ≪≫ F.rightUnitor

/--
theorem `hasColimits_of_reflective` / 定理 `hasColimits_of_reflective`

English:
theorem hasColimits_of_reflective
  given: (R : D ⥤ C) [Reflective R] [HasColimitsOfSize.{v, u} C]
  proof: ⟨fun _ => hasColimitsOfShape_of_reflective R⟩

中文:
定理 hasColimits_of_reflective
  条件: (R : D ⥤ C) [反射 R] [有余limitsOfSize.{v, u} C]
  证明: ⟨fun _ => hasColimitsOfShape_of_reflective R⟩

Depends on / 依赖: hasColimitsOfShape_of_reflective
-/
theorem hasColimits_of_reflective (R : D ⥤ C) [Reflective R] [HasColimitsOfSize.{v, u} C] :
    HasColimitsOfSize.{v, u} D :=
  ⟨fun _ => hasColimitsOfShape_of_reflective R⟩

/--
lemma `leftAdjoint_preservesTerminal_of_reflective` / 引理 `leftAdjoint_preservesTerminal_of_reflective`

English:
lemma leftAdjoint_preservesTerminal_of_reflective
  given: (R : D ⥤ C) [Reflective R]
  proof: by
    let F := Functor.empty.{v} D
    let : PreservesLimit (F ⋙ R) (monadicLeftAdjoint R) := by
      constructor
      intro c h
      have : HasLimit (F ⋙ R) := ⟨⟨⟨c, h⟩⟩⟩
      have : HasLimit F := hasLimit_of_reflective F R
      constructor
      apply isLimitChangeEmptyCone D (limit.isLimit F)
      apply (asIso ((monadicAdjunction R).counit.app _)).symm.trans
      apply (monadicLeftAdjoint R).mapIso
      letI := monadicCreatesLimits.{v, v} R
      let A := CategoryTheory.preservesLimit_of_createsLimit_and_hasLimit F R
      apply (isLimitOfPreserves _ (limit.isLimit F)).conePointUniqueUpToIso h
    apply preservesLimit_of_iso_diagram _ (Functor.emptyExt (F ⋙ R) _)

中文:
引理 leftAdjoint_preservesTerminal_of_reflective
  条件: (R : D ⥤ C) [反射 R]
  证明: by
    let F := Functor.empty.{v} D
    let : PreservesLimit (F ⋙ R) (monadicLeftAdjoint R) := by
      constructor
      intro c h
      have : HasLimit (F ⋙ R) := ⟨⟨⟨c, h⟩⟩⟩
      have : HasLimit F := hasLimit_of_reflective F R
      constructor
      apply isLimitChangeEmptyCone D (limit.isLimit F)
      apply (asIso ((monadicAdjunction R).counit.app _)).symm.trans
      apply (monadicLeftAdjoint R).mapIso
      letI := monadicCreatesLimits.{v, v} R
      let A := CategoryTheory.preservesLimit_of_createsLimit_and_hasLimit F R
      apply (isLimitOfPreserves _ (limit.isLimit F)).conePointUniqueUpToIso h
    apply preservesLimit_of_iso_diagram _ (Functor.emptyExt (F ⋙ R) _)

Depends on / 依赖: CategoryTheory, CategoryTheory.preservesLimit_of_createsLimit_and_hasLimit, Functor, Functor.empty, HasLimit, PreservesLimit, counit, counit.app, hasLimit_of_reflective, isLimit, isLimitChangeEmptyCone, isLimitOfPreserves, limit.isLimit, mapIso, monadicAdjunction, monadicCreatesLimits, monadicLeftAdjoint, preservesLimit_of_createsLimit_and_hasLimit, symm.trans
-/
lemma leftAdjoint_preservesTerminal_of_reflective (R : D ⥤ C) [Reflective R] :
    PreservesLimitsOfShape (Discrete.{v} PEmpty) (monadicLeftAdjoint R) where
  preservesLimit {K} := by
    let F := Functor.empty.{v} D
    let : PreservesLimit (F ⋙ R) (monadicLeftAdjoint R) := by
      constructor
      intro c h
      have : HasLimit (F ⋙ R) := ⟨⟨⟨c, h⟩⟩⟩
      have : HasLimit F := hasLimit_of_reflective F R
      constructor
      apply isLimitChangeEmptyCone D (limit.isLimit F)
      apply (asIso ((monadicAdjunction R).counit.app _)).symm.trans
      apply (monadicLeftAdjoint R).mapIso
      letI := monadicCreatesLimits.{v, v} R
      let A := CategoryTheory.preservesLimit_of_createsLimit_and_hasLimit F R
      apply (isLimitOfPreserves _ (limit.isLimit F)).conePointUniqueUpToIso h
    apply preservesLimit_of_iso_diagram _ (Functor.emptyExt (F ⋙ R) _)

end

-- We dualise all of the above for comonads.
namespace Comonad

variable {T : Comonad C}

namespace ForgetCreatesColimits'

variable (D : J ⥤ Coalgebra T) (c : Cocone (D ⋙ T.forget)) (t : IsColimit c)

/-- (Impl) The natural transformation used to define the new cocone -/
@[simps]
/--
Definition of `γ` / `γ` 的定义

English:
definition γ
  signature: : D ⋙ T.forget ⟶ D ⋙ T.forget ⋙ ↑T where app j
  body: (D.obj j).a

中文:
定义 γ
  签名: : D ⋙ T.forget ⟶ D ⋙ T.forget ⋙ ↑T where app j
  定义体: (D.obj j).a

Depends on / 依赖: D.obj
-/
def γ : D ⋙ T.forget ⟶ D ⋙ T.forget ⋙ ↑T where app j := (D.obj j).a

/-- (Impl) This new cocone is used to construct the coalgebra structure -/
@[simps! ι_app]
/--
Definition of `newCocone` / `newCocone` 的定义

English:
definition newCocone
  signature: : Cocone (D ⋙ forget T) where
  body: T.obj c.pt
  ι := γ D ≫ whiskerRight c.ι (T : C ⥤ C) ≫ (Functor.constComp J _ (T : C ⥤ C)).hom

中文:
定义 newCocone
  签名: : 余锥 (D ⋙ forget T) where
  定义体: T.obj c.pt
  ι := γ D ≫ whiskerRight c.ι (T : C ⥤ C) ≫ (Functor.constComp J _ (T : C ⥤ C)).hom

Depends on / 依赖: T.obj, c.pt
-/
def newCocone : Cocone (D ⋙ forget T) where
  pt := T.obj c.pt
  ι := γ D ≫ whiskerRight c.ι (T : C ⥤ C) ≫ (Functor.constComp J _ (T : C ⥤ C)).hom

set_option backward.isDefEq.respectTransparency false in
/-- The coalgebra structure which will be the point of the new colimit cone for `D`. -/
@[simps]
/--
Definition of `coconePoint` / `coconePoint` 的定义

English:
definition coconePoint
  signature: : Coalgebra T where
  body: c.pt
  a := t.desc (newCocone D c)
  counit := t.hom_ext fun j => by
    simp only [Functor.comp_obj, forget_obj, Functor.id_obj,
      IsColimit.fac_assoc, newCocone_ι_app, assoc, NatTrans.naturality, Functor.id_map, comp_id]
    rw [← Category.assoc]; rw [(D.obj j).counit]; rw [Category.id_comp]
  coassoc := t.hom_ext fun j => by
    simp only [Functor.comp_obj, forget_obj, IsColimit.fac_assoc,
      newCocone_ι_app, assoc, NatTrans.naturality, Functor.comp_map]
    rw [← Category.assoc]; rw [(D.obj j).coassoc]; rw [← Functor.map_comp]; rw [t.fac (newCocone D c) j]; rw [newCocone_ι_app]; rw [Functor.map_comp]; rw [assoc]

中文:
定义 coconePoint
  签名: : 余algebra T where
  定义体: c.pt
  a := t.desc (newCocone D c)
  counit := t.hom_ext fun j => by
    simp only [Functor.comp_obj, forget_obj, Functor.id_obj,
      IsColimit.fac_assoc, newCocone_ι_app, assoc, NatTrans.naturality, Functor.id_map, comp_id]
    rw [← Category.assoc]; rw [(D.obj j).counit]; rw [Category.id_comp]
  coassoc := t.hom_ext fun j => by
    simp only [Functor.comp_obj, forget_obj, IsColimit.fac_assoc,
      newCocone_ι_app, assoc, NatTrans.naturality, Functor.comp_map]
    rw [← Category.assoc]; rw [(D.obj j).coassoc]; rw [← Functor.map_comp]; rw [t.fac (newCocone D c) j]; rw [newCocone_ι_app]; rw [Functor.map_comp]; rw [assoc]

Depends on / 依赖: c.pt
-/
def coconePoint : Coalgebra T where
  A := c.pt
  a := t.desc (newCocone D c)
  counit := t.hom_ext fun j => by
    simp only [Functor.comp_obj, forget_obj, Functor.id_obj,
      IsColimit.fac_assoc, newCocone_ι_app, assoc, NatTrans.naturality, Functor.id_map, comp_id]
    rw [← Category.assoc]; rw [(D.obj j).counit]; rw [Category.id_comp]
  coassoc := t.hom_ext fun j => by
    simp only [Functor.comp_obj, forget_obj, IsColimit.fac_assoc,
      newCocone_ι_app, assoc, NatTrans.naturality, Functor.comp_map]
    rw [← Category.assoc]; rw [(D.obj j).coassoc]; rw [← Functor.map_comp]; rw [t.fac (newCocone D c) j]; rw [newCocone_ι_app]; rw [Functor.map_comp]; rw [assoc]

set_option backward.isDefEq.respectTransparency false in
/-- (Impl) Construct the lifted cocone in `Coalgebra T` which will be colimiting. -/
@[simps]
/--
Definition of `liftedCocone` / `liftedCocone` 的定义

English:
definition liftedCocone
  signature: : Cocone D where
  body: coconePoint D c t
  ι :=
    { app := fun j => { f := c.ι.app j }
      naturality := fun X Y f => by
        ext1
        simpa using (c.w f) }

中文:
定义 liftedCocone
  签名: : 余锥 D where
  定义体: coconePoint D c t
  ι :=
    { app := fun j => { f := c.ι.app j }
      naturality := fun X Y f => by
        ext1
        simpa using (c.w f) }

Depends on / 依赖: coconePoint
-/
def liftedCocone : Cocone D where
  pt := coconePoint D c t
  ι :=
    { app := fun j => { f := c.ι.app j }
      naturality := fun X Y f => by
        ext1
        simpa using (c.w f) }

set_option backward.isDefEq.respectTransparency false in
/-- (Impl) Prove that the lifted cocone is colimiting. -/
@[simps]
/--
Definition of `liftedCoconeIsColimit` / `liftedCoconeIsColimit` 的定义

English:
definition liftedCoconeIsColimit
  signature: : IsColimit (liftedCocone D c t) where
  body: { f := t.desc ((forget T).mapCocone s)
      h :=
        t.hom_ext fun j => by
          dsimp
          rw [← Category.assoc]; rw [← Category.assoc]; rw [t.fac]; rw [newCocone_ι_app]; rw [t.fac]; rw [Functor.mapCocone_ι_app]; rw [Category.assoc]; rw [← Functor.map_comp]; rw [t.fac]
          apply (s.ι.app j).h }
  uniq s m J := by
    ext1
    apply t.hom_ext
    intro j
    simpa [t.fac ((forget T).mapCocone s) j] using congr_arg Coalgebra.Hom.f (J j)

中文:
定义 liftedCoconeIsColimit
  签名: : 是余极限 (liftedCocone D c t) where
  定义体: { f := t.desc ((forget T).mapCocone s)
      h :=
        t.hom_ext fun j => by
          dsimp
          rw [← Category.assoc]; rw [← Category.assoc]; rw [t.fac]; rw [newCocone_ι_app]; rw [t.fac]; rw [Functor.mapCocone_ι_app]; rw [Category.assoc]; rw [← Functor.map_comp]; rw [t.fac]
          apply (s.ι.app j).h }
  uniq s m J := by
    ext1
    apply t.hom_ext
    intro j
    simpa [t.fac ((forget T).mapCocone s) j] using congr_arg Coalgebra.Hom.f (J j)

Depends on / 依赖: Category, Category.assoc, Coalgebra, Coalgebra.Hom.f, Functor, Functor.mapCocone_, Functor.map_comp, congr_arg, forget, hom_ext, mapCocone, map_comp, t.desc, t.fac, t.hom_ext
-/
def liftedCoconeIsColimit : IsColimit (liftedCocone D c t) where
  desc s :=
    { f := t.desc ((forget T).mapCocone s)
      h :=
        t.hom_ext fun j => by
          dsimp
          rw [← Category.assoc]; rw [← Category.assoc]; rw [t.fac]; rw [newCocone_ι_app]; rw [t.fac]; rw [Functor.mapCocone_ι_app]; rw [Category.assoc]; rw [← Functor.map_comp]; rw [t.fac]
          apply (s.ι.app j).h }
  uniq s m J := by
    ext1
    apply t.hom_ext
    intro j
    simpa [t.fac ((forget T).mapCocone s) j] using congr_arg Coalgebra.Hom.f (J j)

end ForgetCreatesColimits'

-- Dual to theorem 5.6.5 from [Riehl][riehl2017]
/--
Instance `forgetCreatesColimit` / 实例 `forgetCreatesColimit`

English:
instance forgetCreatesColimit
  signature: : CreatesColimitsOfSize (forget T) where
  body: {
    CreatesColimit := fun {D} =>
      createsColimitOfReflectsIso fun c t =>
        { liftedCocone := ForgetCreatesColimits'.liftedCocone D c t
          validLift := Cocone.ext (Iso.refl _) fun _ => (comp_id _)
          makesColimit := ForgetCreatesColimits'.liftedCoconeIsColimit _ _ _ } }

中文:
实例 forgetCreatesColimit
  签名: : CreatesColimitsOfSize (forget T) where
  定义体: {
    CreatesColimit := fun {D} =>
      createsColimitOfReflectsIso fun c t =>
        { liftedCocone := ForgetCreatesColimits'.liftedCocone D c t
          validLift := Cocone.ext (Iso.refl _) fun _ => (comp_id _)
          makesColimit := ForgetCreatesColimits'.liftedCoconeIsColimit _ _ _ } }
-/
noncomputable instance forgetCreatesColimit : CreatesColimitsOfSize (forget T) where
  CreatesColimitsOfShape := {
    CreatesColimit := fun {D} =>
      createsColimitOfReflectsIso fun c t =>
        { liftedCocone := ForgetCreatesColimits'.liftedCocone D c t
          validLift := Cocone.ext (Iso.refl _) fun _ => (comp_id _)
          makesColimit := ForgetCreatesColimits'.liftedCoconeIsColimit _ _ _ } }

/--
theorem `hasColimit_of_comp_forget_hasColimit` / 定理 `hasColimit_of_comp_forget_hasColimit`

English:
theorem hasColimit_of_comp_forget_hasColimit
  given: (D : J ⥤ Coalgebra T) [HasColimit (D ⋙ forget T)]
  proof: hasColimit_of_created D (forget T)

中文:
定理 hasColimit_of_comp_forget_hasColimit
  条件: (D : J ⥤ 余algebra T) [有余极限 (D ⋙ forget T)]
  证明: hasColimit_of_created D (forget T)

Depends on / 依赖: forget, hasColimit_of_created
-/
theorem hasColimit_of_comp_forget_hasColimit (D : J ⥤ Coalgebra T) [HasColimit (D ⋙ forget T)] :
    HasColimit D :=
  hasColimit_of_created D (forget T)

namespace ForgetCreatesLimits'

-- Let's hide the implementation details in a namespace
variable {D : J ⥤ Coalgebra T} (c : Cone (D ⋙ forget T)) (t : IsLimit c)

/-- (Impl)
The natural transformation given by the coalgebra structure maps, used to construct a cone `c` with
point `limit (D ⋙ forget T)`.
-/
@[simps]
/--
Definition of `γ` / `γ` 的定义

English:
definition γ
  signature: : D ⋙ forget T ⟶ (D ⋙ forget T) ⋙ ↑T where app j
  body: (D.obj j).a

中文:
定义 γ
  签名: : D ⋙ forget T ⟶ (D ⋙ forget T) ⋙ ↑T where app j
  定义体: (D.obj j).a

Depends on / 依赖: D.obj
-/
def γ : D ⋙ forget T ⟶ (D ⋙ forget T) ⋙ ↑T where app j := (D.obj j).a

/-- (Impl)
A cone for the diagram `(D ⋙ forget T) ⋙ T` found by composing the natural transformation `γ`
with the limiting cone for `D ⋙ forget T`.
-/
@[simps]
/--
Definition of `newCone` / `newCone` 的定义

English:
definition newCone
  signature: : Cone ((D ⋙ forget T) ⋙ (T : C ⥤ C)) where
  body: c.pt
  π := c.π ≫ γ

中文:
定义 newCone
  签名: : 锥 ((D ⋙ forget T) ⋙ (T : C ⥤ C)) where
  定义体: c.pt
  π := c.π ≫ γ

Depends on / 依赖: c.pt
-/
def newCone : Cone ((D ⋙ forget T) ⋙ (T : C ⥤ C)) where
  pt := c.pt
  π := c.π ≫ γ

variable [PreservesLimit (D ⋙ forget T) (T : C ⥤ C)]

/--
Definition of `lambda` / `lambda` 的定义

English:
abbreviation lambda
  signature: : c.pt ⟶ ((T : C ⥤ C).mapCone c).pt
  body: (isLimitOfPreserves _ t).lift (newCone c)

中文:
缩写 lambda
  签名: : c.pt ⟶ ((T : C ⥤ C).mapCone c).pt
  定义体: (isLimitOfPreserves _ t).lift (newCone c)

Depends on / 依赖: isLimitOfPreserves, newCone
-/
noncomputable abbrev lambda : c.pt ⟶ ((T : C ⥤ C).mapCone c).pt :=
  (isLimitOfPreserves _ t).lift (newCone c)

/--
theorem `commuting` / 定理 `commuting`

English:
theorem commuting
  given: (j : J)
  statement: lambda c t ≫ (T : C ⥤ C).map (c.π.app j) = c.π.app j ≫ (D.obj j).a
  proof: (isLimitOfPreserves _ t).fac (newCone c) j

中文:
定理 commuting
  条件: (j : J)
  结论: lambda c t ≫ (T : C ⥤ C).map (c.π.app j) = c.π.app j ≫ (D.obj j).a
  证明: (isLimitOfPreserves _ t).fac (newCone c) j

Depends on / 依赖: isLimitOfPreserves, newCone
-/
theorem commuting (j : J) : lambda c t ≫ (T : C ⥤ C).map (c.π.app j) = c.π.app j ≫ (D.obj j).a :=
  (isLimitOfPreserves _ t).fac (newCone c) j

variable [PreservesLimit ((D ⋙ forget T) ⋙ T.toFunctor) T.toFunctor]
variable [PreservesColimit ((D ⋙ forget T) ⋙ ↑T) (T : C ⥤ C)]

set_option backward.isDefEq.respectTransparency false in
/-- (Impl)
Construct the limiting coalgebra from the map `λ : L ⟶ TL` given by `lambda`. We are required to
show it satisfies the two coalgebra laws, which follow from the coalgebra laws for the image of `D`
and our `commuting` lemma.
-/
@[simps]
/--
Definition of `conePoint` / `conePoint` 的定义

English:
definition conePoint
  signature: : Coalgebra T where
  body: c.pt
  a := lambda c t
  counit := t.hom_ext fun j => by
    rw [assoc]; rw [← show _ = _ ≫ c.π.app j from T.ε.naturality _]; rw [← assoc]; rw [commuting]; rw [assoc]
    simp [Coalgebra.counit (D.obj j)]
  coassoc := by
    refine (isLimitOfPreserves _ (isLimitOfPreserves _ t)).hom_ext fun j => ?_
    rw [Functor.mapCone_π_app]; rw [Functor.mapCone_π_app]; rw [assoc]; rw [← show _ = _ ≫ T.map (T.map _) from T.δ.naturality _]; rw [assoc]; rw [← Functor.map_comp]; rw [commuting]; rw [Functor.map_comp]; rw [← assoc]; rw [commuting]
    simp only [Functor.comp_obj, forget_obj, Functor.const_obj_obj, assoc]
    rw [(D.obj j).coassoc]; rw [← assoc]; rw [← assoc]; rw [commuting]

中文:
定义 conePoint
  签名: : 余algebra T where
  定义体: c.pt
  a := lambda c t
  counit := t.hom_ext fun j => by
    rw [assoc]; rw [← show _ = _ ≫ c.π.app j from T.ε.naturality _]; rw [← assoc]; rw [commuting]; rw [assoc]
    simp [Coalgebra.counit (D.obj j)]
  coassoc := by
    refine (isLimitOfPreserves _ (isLimitOfPreserves _ t)).hom_ext fun j => ?_
    rw [Functor.mapCone_π_app]; rw [Functor.mapCone_π_app]; rw [assoc]; rw [← show _ = _ ≫ T.map (T.map _) from T.δ.naturality _]; rw [assoc]; rw [← Functor.map_comp]; rw [commuting]; rw [Functor.map_comp]; rw [← assoc]; rw [commuting]
    simp only [Functor.comp_obj, forget_obj, Functor.const_obj_obj, assoc]
    rw [(D.obj j).coassoc]; rw [← assoc]; rw [← assoc]; rw [commuting]

Depends on / 依赖: c.pt
-/
noncomputable def conePoint : Coalgebra T where
  A := c.pt
  a := lambda c t
  counit := t.hom_ext fun j => by
    rw [assoc]; rw [← show _ = _ ≫ c.π.app j from T.ε.naturality _]; rw [← assoc]; rw [commuting]; rw [assoc]
    simp [Coalgebra.counit (D.obj j)]
  coassoc := by
    refine (isLimitOfPreserves _ (isLimitOfPreserves _ t)).hom_ext fun j => ?_
    rw [Functor.mapCone_π_app]; rw [Functor.mapCone_π_app]; rw [assoc]; rw [← show _ = _ ≫ T.map (T.map _) from T.δ.naturality _]; rw [assoc]; rw [← Functor.map_comp]; rw [commuting]; rw [Functor.map_comp]; rw [← assoc]; rw [commuting]
    simp only [Functor.comp_obj, forget_obj, Functor.const_obj_obj, assoc]
    rw [(D.obj j).coassoc]; rw [← assoc]; rw [← assoc]; rw [commuting]

set_option backward.isDefEq.respectTransparency.types false in
/-- (Impl) Construct the lifted cone in `Coalgebra T` which will be limiting. -/
@[simps]
/--
Definition of `liftedCone` / `liftedCone` 的定义

English:
definition liftedCone
  signature: : Cone D where
  body: conePoint c t
  π :=
    { app := fun j =>
        { f := c.π.app j
          h := commuting _ _ _ }
      naturality := fun A B f => by
        ext1
        dsimp
        rw [id_comp]; rw [← c.w]
        rfl }

中文:
定义 liftedCone
  签名: : 锥 D where
  定义体: conePoint c t
  π :=
    { app := fun j =>
        { f := c.π.app j
          h := commuting _ _ _ }
      naturality := fun A B f => by
        ext1
        dsimp
        rw [id_comp]; rw [← c.w]
        rfl }

Depends on / 依赖: conePoint
-/
noncomputable def liftedCone : Cone D where
  pt := conePoint c t
  π :=
    { app := fun j =>
        { f := c.π.app j
          h := commuting _ _ _ }
      naturality := fun A B f => by
        ext1
        dsimp
        rw [id_comp]; rw [← c.w]
        rfl }

set_option backward.isDefEq.respectTransparency false in
/-- (Impl) Prove that the lifted cone is limiting. -/
@[simps]
/--
Definition of `liftedConeIsLimit` / `liftedConeIsLimit` 的定义

English:
definition liftedConeIsLimit
  signature: : IsLimit (liftedCone c t) where
  body: { f := t.lift ((forget T).mapCone s)
      h :=
        (isLimitOfPreserves (T : C ⥤ C) t).hom_ext fun j => by
          dsimp
          rw [Category.assoc]; rw [← t.fac]; rw [Category.assoc]; rw [t.fac]; rw [commuting]; rw [← assoc]; rw [← assoc]; rw [t.fac]; rw [assoc]; rw [← Functor.map_comp]; rw [t.fac]
          exact (s.π.app j).h }
  uniq s m J := by
    ext1
    apply t.hom_ext
    intro j
    simpa using congr_arg Coalgebra.Hom.f (J j)

中文:
定义 liftedConeIsLimit
  签名: : 是极限 (liftedCone c t) where
  定义体: { f := t.lift ((forget T).mapCone s)
      h :=
        (isLimitOfPreserves (T : C ⥤ C) t).hom_ext fun j => by
          dsimp
          rw [Category.assoc]; rw [← t.fac]; rw [Category.assoc]; rw [t.fac]; rw [commuting]; rw [← assoc]; rw [← assoc]; rw [t.fac]; rw [assoc]; rw [← Functor.map_comp]; rw [t.fac]
          exact (s.π.app j).h }
  uniq s m J := by
    ext1
    apply t.hom_ext
    intro j
    simpa using congr_arg Coalgebra.Hom.f (J j)

Depends on / 依赖: Category, Category.assoc, Coalgebra, Coalgebra.Hom.f, Functor, Functor.map_comp, commuting, congr_arg, forget, hom_ext, isLimitOfPreserves, mapCone, map_comp, t.fac, t.hom_ext, t.lift
-/
noncomputable def liftedConeIsLimit : IsLimit (liftedCone c t) where
  lift s :=
    { f := t.lift ((forget T).mapCone s)
      h :=
        (isLimitOfPreserves (T : C ⥤ C) t).hom_ext fun j => by
          dsimp
          rw [Category.assoc]; rw [← t.fac]; rw [Category.assoc]; rw [t.fac]; rw [commuting]; rw [← assoc]; rw [← assoc]; rw [t.fac]; rw [assoc]; rw [← Functor.map_comp]; rw [t.fac]
          exact (s.π.app j).h }
  uniq s m J := by
    ext1
    apply t.hom_ext
    intro j
    simpa using congr_arg Coalgebra.Hom.f (J j)

end ForgetCreatesLimits'

open ForgetCreatesLimits'

-- TODO: the converse of this is true as well
set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `forgetCreatesLimit` / 实例 `forgetCreatesLimit`

English:
instance forgetCreatesLimit
  signature: (D : J ⥤ Coalgebra T)
  body: createsLimitOfReflectsIso fun c t =>
    { liftedCone :=
        { pt := conePoint c t
          π :=
            { app := fun j =>
                { f := c.π.app j
                  h := commuting _ _ _ }
              naturality := fun A B f => by
                ext1
                simpa using (c.w f).symm } }
      validLift := Cone.ext (Iso.refl _)
      makesLimit := liftedConeIsLimit _ _ }

中文:
实例 forgetCreatesLimit
  签名: (D : J ⥤ 余algebra T)
  定义体: createsLimitOfReflectsIso fun c t =>
    { liftedCone :=
        { pt := conePoint c t
          π :=
            { app := fun j =>
                { f := c.π.app j
                  h := commuting _ _ _ }
              naturality := fun A B f => by
                ext1
                simpa using (c.w f).symm } }
      validLift := Cone.ext (Iso.refl _)
      makesLimit := liftedConeIsLimit _ _ }

Depends on / 依赖: Cone.ext, Iso.refl, commuting, conePoint, createsLimitOfReflectsIso, liftedCone, liftedConeIsLimit, makesLimit, naturality, validLift
-/
noncomputable instance forgetCreatesLimit (D : J ⥤ Coalgebra T)
    [PreservesLimit (D ⋙ forget T) (T : C ⥤ C)]
    [PreservesLimit ((D ⋙ forget T) ⋙ ↑T) (T : C ⥤ C)] : CreatesLimit D (forget T) :=
  createsLimitOfReflectsIso fun c t =>
    { liftedCone :=
        { pt := conePoint c t
          π :=
            { app := fun j =>
                { f := c.π.app j
                  h := commuting _ _ _ }
              naturality := fun A B f => by
                ext1
                simpa using (c.w f).symm } }
      validLift := Cone.ext (Iso.refl _)
      makesLimit := liftedConeIsLimit _ _ }

/--
Instance `forgetCreatesLimitsOfShape` / 实例 `forgetCreatesLimitsOfShape`

English:
instance forgetCreatesLimitsOfShape
  signature: [PreservesLimitsOfShape J (T : C ⥤ C)]
  body: by infer_instance

中文:
实例 forgetCreatesLimitsOfShape
  签名: [保持形状极限 J (T : C ⥤ C)]
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
noncomputable instance forgetCreatesLimitsOfShape [PreservesLimitsOfShape J (T : C ⥤ C)] :
    CreatesLimitsOfShape J (forget T) where CreatesLimit := by infer_instance

/--
Instance `forgetCreatesLimits` / 实例 `forgetCreatesLimits`

English:
instance forgetCreatesLimits
  signature: [PreservesLimitsOfSize.{v, u} (T : C ⥤ C)]
  body: by infer_instance

中文:
实例 forgetCreatesLimits
  签名: [保持LimitsOfSize.{v, u} (T : C ⥤ C)]
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
noncomputable instance forgetCreatesLimits [PreservesLimitsOfSize.{v, u} (T : C ⥤ C)] :
    CreatesLimitsOfSize.{v, u} (forget T) where CreatesLimitsOfShape := by infer_instance

/--
theorem `forget_creates_limits_of_comonad_preserves` / 定理 `forget_creates_limits_of_comonad_preserves`

English:
theorem forget_creates_limits_of_comonad_preserves
  statement: [PreservesLimitsOfShape J (T : C ⥤ C)]
  proof: hasLimit_of_created D (forget T)

中文:
定理 forget_creates_limits_of_comonad_preserves
  结论: [保持形状极限 J (T : C ⥤ C)]
  证明: hasLimit_of_created D (forget T)

Depends on / 依赖: forget, hasLimit_of_created
-/
theorem forget_creates_limits_of_comonad_preserves [PreservesLimitsOfShape J (T : C ⥤ C)]
    (D : J ⥤ Coalgebra T) [HasLimit (D ⋙ forget T)] : HasLimit D :=
  hasLimit_of_created D (forget T)

end Comonad

/--
Instance `comp_comparison_forget_hasColimit` / 实例 `comp_comparison_forget_hasColimit`

English:
instance comp_comparison_forget_hasColimit
  signature: (F : J ⥤ D) (R : D ⥤ C) [ComonadicLeftAdjoint R]
  body: by
  assumption

中文:
实例 comp_comparison_forget_hasColimit
  签名: (F : J ⥤ D) (R : D ⥤ C) [余monadicLeftAdjoint R]
  定义体: by
  assumption
-/
instance comp_comparison_forget_hasColimit (F : J ⥤ D) (R : D ⥤ C) [ComonadicLeftAdjoint R]
    [HasColimit (F ⋙ R)] :
    HasColimit ((F ⋙ Comonad.comparison (comonadicAdjunction R)) ⋙ Comonad.forget _) := by
  assumption

/--
Instance `comp_comparison_hasColimit` / 实例 `comp_comparison_hasColimit`

English:
instance comp_comparison_hasColimit
  signature: (F : J ⥤ D) (R : D ⥤ C) [ComonadicLeftAdjoint R]
  body: Comonad.hasColimit_of_comp_forget_hasColimit (F ⋙ Comonad.comparison (comonadicAdjunction R))

中文:
实例 comp_comparison_hasColimit
  签名: (F : J ⥤ D) (R : D ⥤ C) [余monadicLeftAdjoint R]
  定义体: Comonad.hasColimit_of_comp_forget_hasColimit (F ⋙ Comonad.comparison (comonadicAdjunction R))

Depends on / 依赖: Comonad, Comonad.comparison, Comonad.hasColimit_of_comp_forget_hasColimit, comonadicAdjunction, comparison, hasColimit_of_comp_forget_hasColimit
-/
instance comp_comparison_hasColimit (F : J ⥤ D) (R : D ⥤ C) [ComonadicLeftAdjoint R]
    [HasColimit (F ⋙ R)] : HasColimit (F ⋙ Comonad.comparison (comonadicAdjunction R)) :=
  Comonad.hasColimit_of_comp_forget_hasColimit (F ⋙ Comonad.comparison (comonadicAdjunction R))

/-- Any comonadic functor creates colimits. -/
@[instance_reducible]
/--
Definition of `comonadicCreatesColimits` / `comonadicCreatesColimits` 的定义

English:
definition comonadicCreatesColimits
  signature: (R : D ⥤ C) [ComonadicLeftAdjoint R]
  body: createsColimitsOfNatIso (Comonad.comparisonForget (comonadicAdjunction R))

中文:
定义 comonadicCreatesColimits
  签名: (R : D ⥤ C) [余monadicLeftAdjoint R]
  定义体: createsColimitsOfNatIso (Comonad.comparisonForget (comonadicAdjunction R))

Depends on / 依赖: Comonad, Comonad.comparisonForget, comonadicAdjunction, comparisonForget, createsColimitsOfNatIso
-/
noncomputable def comonadicCreatesColimits (R : D ⥤ C) [ComonadicLeftAdjoint R] :
    CreatesColimitsOfSize.{v, u} R :=
  createsColimitsOfNatIso (Comonad.comparisonForget (comonadicAdjunction R))

/-- The forgetful functor from the Eilenberg-Moore category for a comonad creates any limit
which the comonad itself preserves.
-/
@[instance_reducible]
/--
Definition of `comonadicCreatesLimitOfPreservesLimit` / `comonadicCreatesLimitOfPreservesLimit` 的定义

English:
definition comonadicCreatesLimitOfPreservesLimit
  signature: (R : D ⥤ C) (K : J ⥤ D)
  body: by
  letI A := Comonad.comparison (comonadicAdjunction R)
  letI B := Comonad.forget (Adjunction.toComonad (comonadicAdjunction R))
  let i : (K ⋙ Comonad.comparison (comonadicAdjunction R)) ⋙ Comonad.forget _ ≅ K ⋙ R :=
    Functor.associator _ _ _ ≪≫
      isoWhiskerLeft K (Comonad.comparisonForget (comonadicAdjunction R))
  letI : PreservesLimit ((K ⋙ A) ⋙ Comonad.forget
    (Adjunction.toComonad (comonadicAdjunction R)))
      (Adjunction.toComonad (comonadicAdjunction R)).toFunctor := by
    dsimp
    exact preservesLimit_of_iso_diagram _ i.symm
  letI : PreservesLimit
    (((K ⋙ A) ⋙ Comonad.forget (Adjunction.toComonad (comonadicAdjunction R))) ⋙
      (Adjunction.toComonad (comonadicAdjunction R)).toFunctor)
      (Adjunction.toComonad (comonadicAdjunction R)).toFunctor := by
    dsimp
    exact preservesLimit_of_iso_diagram _ (isoWhiskerRight i (comonadicRightAdjoint R ⋙ R)).symm
  letI : CreatesLimit (K ⋙ A) B := CategoryTheory.Comonad.forgetCreatesLimit _
  letI : CreatesLimit K (A ⋙ B) := CategoryTheory.compCreatesLimit _ _
  let e := Comonad.comparisonForget (comonadicAdjunction R)
  apply createsLimitOfNatIso e

中文:
定义 comonadicCreatesLimitOfPreservesLimit
  签名: (R : D ⥤ C) (K : J ⥤ D)
  定义体: by
  letI A := Comonad.comparison (comonadicAdjunction R)
  letI B := Comonad.forget (Adjunction.toComonad (comonadicAdjunction R))
  let i : (K ⋙ Comonad.comparison (comonadicAdjunction R)) ⋙ Comonad.forget _ ≅ K ⋙ R :=
    Functor.associator _ _ _ ≪≫
      isoWhiskerLeft K (Comonad.comparisonForget (comonadicAdjunction R))
  letI : PreservesLimit ((K ⋙ A) ⋙ Comonad.forget
    (Adjunction.toComonad (comonadicAdjunction R)))
      (Adjunction.toComonad (comonadicAdjunction R)).toFunctor := by
    dsimp
    exact preservesLimit_of_iso_diagram _ i.symm
  letI : PreservesLimit
    (((K ⋙ A) ⋙ Comonad.forget (Adjunction.toComonad (comonadicAdjunction R))) ⋙
      (Adjunction.toComonad (comonadicAdjunction R)).toFunctor)
      (Adjunction.toComonad (comonadicAdjunction R)).toFunctor := by
    dsimp
    exact preservesLimit_of_iso_diagram _ (isoWhiskerRight i (comonadicRightAdjoint R ⋙ R)).symm
  letI : CreatesLimit (K ⋙ A) B := CategoryTheory.Comonad.forgetCreatesLimit _
  letI : CreatesLimit K (A ⋙ B) := CategoryTheory.compCreatesLimit _ _
  let e := Comonad.comparisonForget (comonadicAdjunction R)
  apply createsLimitOfNatIso e

Depends on / 依赖: Adjunction, Adjunction.toComonad, Comonad, Comonad.comparison, Comonad.comparisonForget, Comonad.forget, Functor, Functor.associator, PreservesLimit, associator, comonadicAdjunction, comparison, comparisonForget, forget, isoWhiskerLeft, preservesLimit_of_, toComonad, toFunctor
-/
noncomputable def comonadicCreatesLimitOfPreservesLimit (R : D ⥤ C) (K : J ⥤ D)
    [ComonadicLeftAdjoint R] [PreservesLimit (K ⋙ R) (comonadicRightAdjoint R ⋙ R)]
    [PreservesLimit ((K ⋙ R) ⋙ comonadicRightAdjoint R ⋙ R) (comonadicRightAdjoint R ⋙ R)] :
      CreatesLimit K R := by
  letI A := Comonad.comparison (comonadicAdjunction R)
  letI B := Comonad.forget (Adjunction.toComonad (comonadicAdjunction R))
  let i : (K ⋙ Comonad.comparison (comonadicAdjunction R)) ⋙ Comonad.forget _ ≅ K ⋙ R :=
    Functor.associator _ _ _ ≪≫
      isoWhiskerLeft K (Comonad.comparisonForget (comonadicAdjunction R))
  letI : PreservesLimit ((K ⋙ A) ⋙ Comonad.forget
    (Adjunction.toComonad (comonadicAdjunction R)))
      (Adjunction.toComonad (comonadicAdjunction R)).toFunctor := by
    dsimp
    exact preservesLimit_of_iso_diagram _ i.symm
  letI : PreservesLimit
    (((K ⋙ A) ⋙ Comonad.forget (Adjunction.toComonad (comonadicAdjunction R))) ⋙
      (Adjunction.toComonad (comonadicAdjunction R)).toFunctor)
      (Adjunction.toComonad (comonadicAdjunction R)).toFunctor := by
    dsimp
    exact preservesLimit_of_iso_diagram _ (isoWhiskerRight i (comonadicRightAdjoint R ⋙ R)).symm
  letI : CreatesLimit (K ⋙ A) B := CategoryTheory.Comonad.forgetCreatesLimit _
  letI : CreatesLimit K (A ⋙ B) := CategoryTheory.compCreatesLimit _ _
  let e := Comonad.comparisonForget (comonadicAdjunction R)
  apply createsLimitOfNatIso e

/-- A comonadic functor creates any limits of shapes it preserves. -/
@[instance_reducible]
/--
Definition of `comonadicCreatesLimitsOfShapeOfPreservesLimitsOfShape` / `comonadicCreatesLimitsOfShapeOfPreservesLimitsOfShape` 的定义

English:
definition comonadicCreatesLimitsOfShapeOfPreservesLimitsOfShape
  signature: (R : D ⥤ C)
  body: letI : PreservesLimitsOfShape J (comonadicRightAdjoint R) := by
    apply (Adjunction.rightAdjoint_preservesLimits (comonadicAdjunction R)).1
  letI : PreservesLimitsOfShape J (comonadicRightAdjoint R ⋙ R) := by
    apply CategoryTheory.Limits.comp_preservesLimitsOfShape _ _
  ⟨comonadicCreatesLimitOfPreservesLimit _ _⟩

中文:
定义 comonadicCreatesLimitsOfShapeOfPreservesLimitsOfShape
  签名: (R : D ⥤ C)
  定义体: letI : PreservesLimitsOfShape J (comonadicRightAdjoint R) := by
    apply (Adjunction.rightAdjoint_preservesLimits (comonadicAdjunction R)).1
  letI : PreservesLimitsOfShape J (comonadicRightAdjoint R ⋙ R) := by
    apply CategoryTheory.Limits.comp_preservesLimitsOfShape _ _
  ⟨comonadicCreatesLimitOfPreservesLimit _ _⟩

Depends on / 依赖: Adjunction, Adjunction.rightAdjoint_preservesLimits, CategoryTheory, CategoryTheory.Limits.comp_preservesLimitsOfShape, Limits, PreservesLimitsOfShape, comonadicAdjunction, comonadicCreatesLimitOfPreservesLimit, comonadicRightAdjoint, comp_preservesLimitsOfShape, rightAdjoint_preservesLimits
-/
noncomputable def comonadicCreatesLimitsOfShapeOfPreservesLimitsOfShape (R : D ⥤ C)
    [ComonadicLeftAdjoint R] [PreservesLimitsOfShape J R] : CreatesLimitsOfShape J R :=
  letI : PreservesLimitsOfShape J (comonadicRightAdjoint R) := by
    apply (Adjunction.rightAdjoint_preservesLimits (comonadicAdjunction R)).1
  letI : PreservesLimitsOfShape J (comonadicRightAdjoint R ⋙ R) := by
    apply CategoryTheory.Limits.comp_preservesLimitsOfShape _ _
  ⟨comonadicCreatesLimitOfPreservesLimit _ _⟩

/-- A comonadic functor creates limits if it preserves limits. -/
@[instance_reducible]
/--
Definition of `comonadicCreatesLimitsOfPreservesLimits` / `comonadicCreatesLimitsOfPreservesLimits` 的定义

English:
definition comonadicCreatesLimitsOfPreservesLimits
  signature: (R : D ⥤ C) [ComonadicLeftAdjoint R]
  body: comonadicCreatesLimitsOfShapeOfPreservesLimitsOfShape _

中文:
定义 comonadicCreatesLimitsOfPreservesLimits
  签名: (R : D ⥤ C) [余monadicLeftAdjoint R]
  定义体: comonadicCreatesLimitsOfShapeOfPreservesLimitsOfShape _

Depends on / 依赖: comonadicCreatesLimitsOfShapeOfPreservesLimitsOfShape
-/
noncomputable def comonadicCreatesLimitsOfPreservesLimits (R : D ⥤ C) [ComonadicLeftAdjoint R]
    [PreservesLimitsOfSize.{v, u} R] : CreatesLimitsOfSize.{v, u} R where
  CreatesLimitsOfShape :=
    comonadicCreatesLimitsOfShapeOfPreservesLimitsOfShape _

section

/--
theorem `hasColimit_of_coreflective` / 定理 `hasColimit_of_coreflective`

English:
theorem hasColimit_of_coreflective
  given: (F : J ⥤ D) (R : D ⥤ C) [HasColimit (F ⋙ R)] [Coreflective R]
  proof: haveI := comonadicCreatesColimits.{v, u} R
  hasColimit_of_created F R

中文:
定理 hasColimit_of_coreflective
  条件: (F : J ⥤ D) (R : D ⥤ C) [有余极限 (F ⋙ R)] [余反射 R]
  证明: haveI := comonadicCreatesColimits.{v, u} R
  hasColimit_of_created F R

Depends on / 依赖: comonadicCreatesColimits, hasColimit_of_created
-/
theorem hasColimit_of_coreflective (F : J ⥤ D) (R : D ⥤ C) [HasColimit (F ⋙ R)] [Coreflective R] :
    HasColimit F :=
  haveI := comonadicCreatesColimits.{v, u} R
  hasColimit_of_created F R

/--
theorem `hasColimitsOfShape_of_coreflective` / 定理 `hasColimitsOfShape_of_coreflective`

English:
theorem hasColimitsOfShape_of_coreflective
  given: [HasColimitsOfShape J C] (R : D ⥤ C) [Coreflective R]
  proof: ⟨fun F => hasColimit_of_coreflective F R⟩

中文:
定理 hasColimitsOfShape_of_coreflective
  条件: [有形状余极限 J C] (R : D ⥤ C) [余反射 R]
  证明: ⟨fun F => hasColimit_of_coreflective F R⟩

Depends on / 依赖: hasColimit_of_coreflective
-/
theorem hasColimitsOfShape_of_coreflective [HasColimitsOfShape J C] (R : D ⥤ C) [Coreflective R] :
    HasColimitsOfShape J D :=
  ⟨fun F => hasColimit_of_coreflective F R⟩

/--
theorem `hasColimits_of_coreflective` / 定理 `hasColimits_of_coreflective`

English:
theorem hasColimits_of_coreflective
  given: (R : D ⥤ C) [HasColimitsOfSize.{v, u} C] [Coreflective R]
  proof: ⟨fun _ => hasColimitsOfShape_of_coreflective R⟩

中文:
定理 hasColimits_of_coreflective
  条件: (R : D ⥤ C) [有余limitsOfSize.{v, u} C] [余反射 R]
  证明: ⟨fun _ => hasColimitsOfShape_of_coreflective R⟩

Depends on / 依赖: hasColimitsOfShape_of_coreflective
-/
theorem hasColimits_of_coreflective (R : D ⥤ C) [HasColimitsOfSize.{v, u} C] [Coreflective R] :
    HasColimitsOfSize.{v, u} D :=
  ⟨fun _ => hasColimitsOfShape_of_coreflective R⟩

/--
theorem `hasLimitsOfShape_of_coreflective` / 定理 `hasLimitsOfShape_of_coreflective`

English:
theorem hasLimitsOfShape_of_coreflective
  given: (R : D ⥤ C) [Coreflective R] [HasLimitsOfShape J C]
  proof: fun F => by
      let c := (comonadicRightAdjoint R).mapCone (limit.cone (F ⋙ R))
      let : PreservesLimitsOfShape J _ :=
        (comonadicAdjunction R).rightAdjoint_preservesLimits.1
      let t : IsLimit c := isLimitOfPreserves (comonadicRightAdjoint R) (limit.isLimit _)
      apply HasLimit.mk ⟨_, (IsLimit.postcomposeHomEquiv _ _).symm t⟩
      apply
        (F.rightUnitor ≪≫ (isoWhiskerLeft F ((asIso (comonadicAdjunction R).unit) :))).symm

中文:
定理 hasLimitsOfShape_of_coreflective
  条件: (R : D ⥤ C) [余反射 R] [有形状极限 J C]
  证明: fun F => by
      let c := (comonadicRightAdjoint R).mapCone (limit.cone (F ⋙ R))
      let : PreservesLimitsOfShape J _ :=
        (comonadicAdjunction R).rightAdjoint_preservesLimits.1
      let t : IsLimit c := isLimitOfPreserves (comonadicRightAdjoint R) (limit.isLimit _)
      apply HasLimit.mk ⟨_, (IsLimit.postcomposeHomEquiv _ _).symm t⟩
      apply
        (F.rightUnitor ≪≫ (isoWhiskerLeft F ((asIso (comonadicAdjunction R).unit) :))).symm

Depends on / 依赖: F.rightUnitor, HasLimit, HasLimit.mk, IsLimit, IsLimit.postcomposeHomEquiv, PreservesLimitsOfShape, comonadicAdjunction, comonadicRightAdjoint, isLimit, isLimitOfPreserves, isoWhiskerLeft, limit.cone, limit.isLimit, mapCone, postcomposeHomEquiv, rightAdjoint_preservesLimits, rightUnitor
-/
theorem hasLimitsOfShape_of_coreflective (R : D ⥤ C) [Coreflective R] [HasLimitsOfShape J C] :
    HasLimitsOfShape J D where
  has_limit := fun F => by
      let c := (comonadicRightAdjoint R).mapCone (limit.cone (F ⋙ R))
      let : PreservesLimitsOfShape J _ :=
        (comonadicAdjunction R).rightAdjoint_preservesLimits.1
      let t : IsLimit c := isLimitOfPreserves (comonadicRightAdjoint R) (limit.isLimit _)
      apply HasLimit.mk ⟨_, (IsLimit.postcomposeHomEquiv _ _).symm t⟩
      apply
        (F.rightUnitor ≪≫ (isoWhiskerLeft F ((asIso (comonadicAdjunction R).unit) :))).symm

/--
theorem `hasLimits_of_coreflective` / 定理 `hasLimits_of_coreflective`

English:
theorem hasLimits_of_coreflective
  given: (R : D ⥤ C) [Coreflective R] [HasLimitsOfSize.{v, u} C]
  proof: ⟨fun _ => hasLimitsOfShape_of_coreflective R⟩

中文:
定理 hasLimits_of_coreflective
  条件: (R : D ⥤ C) [余反射 R] [有LimitsOfSize.{v, u} C]
  证明: ⟨fun _ => hasLimitsOfShape_of_coreflective R⟩

Depends on / 依赖: hasLimitsOfShape_of_coreflective
-/
theorem hasLimits_of_coreflective (R : D ⥤ C) [Coreflective R] [HasLimitsOfSize.{v, u} C] :
    HasLimitsOfSize.{v, u} D :=
  ⟨fun _ => hasLimitsOfShape_of_coreflective R⟩

/--
lemma `rightAdjoint_preservesInitial_of_coreflective` / 引理 `rightAdjoint_preservesInitial_of_coreflective`

English:
lemma rightAdjoint_preservesInitial_of_coreflective
  given: (R : D ⥤ C) [Coreflective R]
  proof: by
    let F := Functor.empty.{v} D
    let : PreservesColimit (F ⋙ R) (comonadicRightAdjoint R) := by
      constructor
      intro c h
      have : HasColimit (F ⋙ R) := ⟨⟨⟨c, h⟩⟩⟩
      have : HasColimit F := hasColimit_of_coreflective F R
      constructor
      apply isColimitChangeEmptyCocone D (colimit.isColimit F)
      apply (asIso ((comonadicAdjunction R).unit.app _)).trans
      apply (comonadicRightAdjoint R).mapIso
      letI := comonadicCreatesColimits.{v, v} R
      let A := CategoryTheory.preservesColimit_of_createsColimit_and_hasColimit F R
      apply (isColimitOfPreserves _ (colimit.isColimit F)).coconePointUniqueUpToIso h
    apply preservesColimit_of_iso_diagram _ (Functor.emptyExt (F ⋙ R) _)

中文:
引理 rightAdjoint_preservesInitial_of_coreflective
  条件: (R : D ⥤ C) [余反射 R]
  证明: by
    let F := Functor.empty.{v} D
    let : PreservesColimit (F ⋙ R) (comonadicRightAdjoint R) := by
      constructor
      intro c h
      have : HasColimit (F ⋙ R) := ⟨⟨⟨c, h⟩⟩⟩
      have : HasColimit F := hasColimit_of_coreflective F R
      constructor
      apply isColimitChangeEmptyCocone D (colimit.isColimit F)
      apply (asIso ((comonadicAdjunction R).unit.app _)).trans
      apply (comonadicRightAdjoint R).mapIso
      letI := comonadicCreatesColimits.{v, v} R
      let A := CategoryTheory.preservesColimit_of_createsColimit_and_hasColimit F R
      apply (isColimitOfPreserves _ (colimit.isColimit F)).coconePointUniqueUpToIso h
    apply preservesColimit_of_iso_diagram _ (Functor.emptyExt (F ⋙ R) _)

Depends on / 依赖: CategoryTheory, CategoryTheory.preservesColimit_of_createsColimit_and_hasColimit, Functor, Functor.empty, HasColimit, PreservesColimit, colimit, colimit.isColimit, comonadicAdjunction, comonadicCreatesColimits, comonadicRightAdjoint, hasColimit_of_coreflective, isColimit, isColimitChangeEmptyCocone, mapIso, preservesColimit_of_createsColimit_and_hasColimit, unit.app
-/
lemma rightAdjoint_preservesInitial_of_coreflective (R : D ⥤ C) [Coreflective R] :
    PreservesColimitsOfShape (Discrete.{v} PEmpty) (comonadicRightAdjoint R) where
  preservesColimit {K} := by
    let F := Functor.empty.{v} D
    let : PreservesColimit (F ⋙ R) (comonadicRightAdjoint R) := by
      constructor
      intro c h
      have : HasColimit (F ⋙ R) := ⟨⟨⟨c, h⟩⟩⟩
      have : HasColimit F := hasColimit_of_coreflective F R
      constructor
      apply isColimitChangeEmptyCocone D (colimit.isColimit F)
      apply (asIso ((comonadicAdjunction R).unit.app _)).trans
      apply (comonadicRightAdjoint R).mapIso
      letI := comonadicCreatesColimits.{v, v} R
      let A := CategoryTheory.preservesColimit_of_createsColimit_and_hasColimit F R
      apply (isColimitOfPreserves _ (colimit.isColimit F)).coconePointUniqueUpToIso h
    apply preservesColimit_of_iso_diagram _ (Functor.emptyExt (F ⋙ R) _)

end

end CategoryTheory
