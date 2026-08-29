/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Transport

/-!

# Transport a symmetric monoidal structure along an equivalence of categories
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory Category Monoidal MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

namespace CategoryTheory.Monoidal

open Functor.LaxMonoidal Functor.OplaxMonoidal

set_option backward.isDefEq.respectTransparency false in
/--
Instance `Transported.instBraidedCategory` / 实例 `Transported.instBraidedCategory`

English:
instance Transported.instBraidedCategory
  signature: (e : C ≌ D) [MonoidalCategory C] [BraidedCategory C]
  body: .ofFaithful e.inverse (fun _ _ => e.functor.mapIso (β_ _ _)) fun _ _ => by
    simp +instances [fromInducedCoreMonoidal, Functor.CoreMonoidal.toLaxMonoidal]

local notation "e'" e => equivalenceTransported e

中文:
实例 Transported.instBraidedCategory
  签名: (e : C ≌ D) [MonoidalCategory C] [BraidedCategory C]
  定义体: .ofFaithful e.inverse (fun _ _ => e.functor.mapIso (β_ _ _)) fun _ _ => by
    simp +instances [fromInducedCoreMonoidal, Functor.CoreMonoidal.toLaxMonoidal]

local notation "e'" e => equivalenceTransported e

Depends on / 依赖: CoreMonoidal, Functor, Functor.CoreMonoidal.toLaxMonoidal, e.functor.mapIso, e.inverse, fromInducedCoreMonoidal, functor, instances, inverse, mapIso, ofFaithful, toLaxMonoidal
-/
instance Transported.instBraidedCategory (e : C ≌ D) [MonoidalCategory C] [BraidedCategory C] :
    BraidedCategory (Transported e) :=
  .ofFaithful e.inverse (fun _ _ => e.functor.mapIso (β_ _ _)) fun _ _ => by
    simp +instances [fromInducedCoreMonoidal, Functor.CoreMonoidal.toLaxMonoidal]

local notation "e'" e => equivalenceTransported e

set_option backward.isDefEq.respectTransparency false in
instance (e : C ≌ D) [MonoidalCategory C] [BraidedCategory C] :
    (e' e).inverse.Braided where
  braided X Y := by
    simp +instances [Transported.instBraidedCategory, BraidedCategory.ofFaithful,
      fromInducedCoreMonoidal, Functor.CoreMonoidal.toLaxMonoidal]

noncomputable section

/--
This is a def because once we have that both `(e' e).inverse` and `(e' e).functor` are
braided, this causes a diamond.
-/
@[instance_reducible]
/--
Definition of `transportedFunctorCompInverseLaxBraided` / `transportedFunctorCompInverseLaxBraided` 的定义

English:
definition transportedFunctorCompInverseLaxBraided
  signature: (e : C ≌ D) [MonoidalCategory C] [BraidedCategory C]
  body: Functor.LaxBraided.ofNatIso (e' e).unitIso

中文:
定义 transportedFunctorCompInverseLaxBraided
  签名: (e : C ≌ D) [MonoidalCategory C] [BraidedCategory C]
  定义体: Functor.LaxBraided.ofNatIso (e' e).unitIso

Depends on / 依赖: Functor, Functor.LaxBraided.ofNatIso, LaxBraided, ofNatIso, unitIso
-/
def transportedFunctorCompInverseLaxBraided (e : C ≌ D) [MonoidalCategory C] [BraidedCategory C] :
    ((e' e).functor ⋙ (e' e).inverse).LaxBraided :=
  Functor.LaxBraided.ofNatIso (e' e).unitIso

attribute [local instance] transportedFunctorCompInverseLaxBraided in
/--
This is a def because once we have that both `(e' e).inverse` and `(e' e).functor` are
braided, this causes a diamond.
-/
@[instance_reducible]
/--
Definition of `transportedFunctorCompInverseBraided` / `transportedFunctorCompInverseBraided` 的定义

English:
definition transportedFunctorCompInverseBraided
  signature: (e : C ≌ D) [MonoidalCategory C] [BraidedCategory C]

中文:
定义 transportedFunctorCompInverseBraided
  签名: (e : C ≌ D) [MonoidalCategory C] [BraidedCategory C]
-/
def transportedFunctorCompInverseBraided (e : C ≌ D) [MonoidalCategory C] [BraidedCategory C] :
    ((e' e).functor ⋙ (e' e).inverse).Braided where

set_option backward.defeqAttrib.useBackward true in
attribute [local instance] transportedFunctorCompInverseBraided in
instance (e : C ≌ D) [MonoidalCategory C] [BraidedCategory C] :
    (e' e).functor.Braided where
  braided X Y := by
    apply (e' e).inverse.map_injective
    have : (β_ (((e' e).functor ⋙ (e' e).inverse).obj X)
        (((e' e).functor ⋙ (e' e).inverse).obj Y)).hom =
          Functor.LaxMonoidal.μ (((e' e).functor ⋙ (e' e).inverse)) X Y ≫
            ((e' e).functor ⋙ (e' e).inverse).map (β_ X Y).hom ≫
              Functor.OplaxMonoidal.δ ((e' e).functor ⋙ (e' e).inverse) Y X := by
      simp only [((e' e).functor ⋙ (e' e).inverse).map_braiding X Y,
        assoc, Functor.Monoidal.μ_δ, comp_id, Functor.Monoidal.μ_δ_assoc]
    simp_all

end

/--
Instance `Transported.instSymmetricCategory` / 实例 `Transported.instSymmetricCategory`

English:
instance Transported.instSymmetricCategory
  signature: (e : C ≌ D) [MonoidalCategory C]
  body: .ofFaithful (equivalenceTransported e).inverse

中文:
实例 Transported.instSymmetricCategory
  签名: (e : C ≌ D) [MonoidalCategory C]
  定义体: .ofFaithful (equivalenceTransported e).inverse

Depends on / 依赖: equivalenceTransported, inverse, ofFaithful
-/
instance Transported.instSymmetricCategory (e : C ≌ D) [MonoidalCategory C]
    [SymmetricCategory C] : SymmetricCategory (Transported e) :=
  .ofFaithful (equivalenceTransported e).inverse

end CategoryTheory.Monoidal
