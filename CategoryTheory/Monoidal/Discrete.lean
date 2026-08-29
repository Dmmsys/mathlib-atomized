/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
# Monoids as discrete monoidal categories

The discrete category on a monoid is a monoidal category.
Multiplicative morphisms induce monoidal functors.
-/

@[expose] public section


universe u u'

open CategoryTheory Discrete MonoidalCategory

variable (M : Type u) [Monoid M]

namespace CategoryTheory

@[to_additive (attr := simps tensorObj_as leftUnitor rightUnitor associator) Discrete.addMonoidal]
/--
Instance `Discrete.monoidal` / 实例 `Discrete.monoidal`

English:
instance Discrete.monoidal
  signature: : MonoidalCategory (Discrete M) where
  body: Discrete.mk 1
  tensorObj X Y := Discrete.mk (X.as * Y.as)
  whiskerLeft X _ _ f := eqToHom (by rw [eq_of_hom f])
  whiskerRight f X := eqToHom (by rw [eq_of_hom f])
  tensorHom f g := eqToHom (by rw [eq_of_hom f, eq_of_hom g])
  leftUnitor X := Discrete.eqToIso (one_mul X.as)
  rightUnitor X := Dis

中文:
实例 Discrete.monoidal
  签名: : MonoidalCategory (Discrete M) where
  定义体: Discrete.mk 1
  tensorObj X Y := Discrete.mk (X.as * Y.as)
  whiskerLeft X _ _ f := eqToHom (by rw [eq_of_hom f])
  whiskerRight f X := eqToHom (by rw [eq_of_hom f])
  tensorHom f g := eqToHom (by rw [eq_of_hom f, eq_of_hom g])
  leftUnitor X := Discrete.eqToIso (one_mul X.as)
  rightUnitor X := Dis

Depends on / 依赖: Discrete, Discrete.mk
-/
instance Discrete.monoidal : MonoidalCategory (Discrete M) where
  tensorUnit := Discrete.mk 1
  tensorObj X Y := Discrete.mk (X.as * Y.as)
  whiskerLeft X _ _ f := eqToHom (by rw [eq_of_hom f])
  whiskerRight f X := eqToHom (by rw [eq_of_hom f])
  tensorHom f g := eqToHom (by rw [eq_of_hom f, eq_of_hom g])
  leftUnitor X := Discrete.eqToIso (one_mul X.as)
  rightUnitor X := Discrete.eqToIso (mul_one X.as)
  associator _ _ _ := Discrete.eqToIso (mul_assoc _ _ _)

@[to_additive (attr := simp) Discrete.addMonoidal_tensorUnit_as]
/--
lemma `Discrete.monoidal_tensorUnit_as` / 引理 `Discrete.monoidal_tensorUnit_as`

English:
lemma Discrete.monoidal_tensorUnit_as
  statement: (𝟙_ (Discrete M)).as = 1
  proof: rfl

中文:
引理 Discrete.monoidal_tensorUnit_as
  结论: (𝟙_ (Discrete M)).as = 1
  证明: rfl
-/
lemma Discrete.monoidal_tensorUnit_as : (𝟙_ (Discrete M)).as = 1 := rfl

variable {M} {N : Type u'} [Monoid N]

/-- A multiplicative morphism between monoids gives a monoidal functor between the corresponding
discrete monoidal categories.
-/
@[to_additive Discrete.addMonoidalFunctor /--
An additive morphism between `AddMonoid`s gives a
monoidal functor between the corresponding discrete monoidal categories. -/]
/--
Definition of `Discrete.monoidalFunctor` / `Discrete.monoidalFunctor` 的定义

English:
definition Discrete.monoidalFunctor
  signature: (F : M ->* N)
  body: Discrete.functor (fun X => Discrete.mk (F X))

@[to_additive (attr := simp) Discrete.addMonoidalFunctor_obj]

中文:
定义 Discrete.monoidalFunctor
  签名: (F : M ->* N)
  定义体: Discrete.functor (fun X => Discrete.mk (F X))

@[to_additive (attr := simp) Discrete.addMonoidalFunctor_obj]

Depends on / 依赖: Discrete, Discrete.functor, Discrete.mk, functor
-/
def Discrete.monoidalFunctor (F : M ->* N) : Discrete M ⥤ Discrete N :=
  Discrete.functor (fun X => Discrete.mk (F X))

@[to_additive (attr := simp) Discrete.addMonoidalFunctor_obj]
/--
lemma `Discrete.monoidalFunctor_obj` / 引理 `Discrete.monoidalFunctor_obj`

English:
lemma Discrete.monoidalFunctor_obj
  given: (F : M ->* N) (m : M)
  proof: rfl

@[to_additive Discrete.addMonoidalFunctorMonoidal]

中文:
引理 Discrete.monoidalFunctor_obj
  条件: (F : M ->* N) (m : M)
  证明: rfl

@[to_additive Discrete.addMonoidalFunctorMonoidal]
-/
lemma Discrete.monoidalFunctor_obj (F : M ->* N) (m : M) :
    (Discrete.monoidalFunctor F).obj (Discrete.mk m) = Discrete.mk (F m) := rfl

@[to_additive Discrete.addMonoidalFunctorMonoidal]
/--
Instance `Discrete.monoidalFunctorMonoidal` / 实例 `Discrete.monoidalFunctorMonoidal`

English:
instance Discrete.monoidalFunctorMonoidal
  signature: (F : M ->* N)
  body: Functor.CoreMonoidal.toMonoidal
      { εIso := Discrete.eqToIso F.map_one.symm
        μIso := fun m₁ m₂ => Discrete.eqToIso (F.map_mul _ _).symm }

中文:
实例 Discrete.monoidalFunctorMonoidal
  签名: (F : M ->* N)
  定义体: Functor.CoreMonoidal.toMonoidal
      { εIso := Discrete.eqToIso F.map_one.symm
        μIso := fun m₁ m₂ => Discrete.eqToIso (F.map_mul _ _).symm }

Depends on / 依赖: CoreMonoidal, Discrete, Discrete.eqToIso, F.map_mul, F.map_one.symm, Functor, Functor.CoreMonoidal.toMonoidal, eqToIso, map_mul, map_one, toMonoidal
-/
instance Discrete.monoidalFunctorMonoidal (F : M ->* N) :
    (Discrete.monoidalFunctor F).Monoidal :=
    Functor.CoreMonoidal.toMonoidal
      { εIso := Discrete.eqToIso F.map_one.symm
        μIso := fun m₁ m₂ => Discrete.eqToIso (F.map_mul _ _).symm }

open Functor.LaxMonoidal Functor.OplaxMonoidal

@[to_additive Discrete.addMonoidalFunctor_ε]
/--
lemma `Discrete.monoidalFunctor_ε` / 引理 `Discrete.monoidalFunctor_ε`

English:
lemma Discrete.monoidalFunctor_ε
  given: (F : M ->* N)
  proof: rfl

@[to_additive Discrete.addMonoidalFunctor_η]

中文:
引理 Discrete.monoidalFunctor_ε
  条件: (F : M ->* N)
  证明: rfl

@[to_additive Discrete.addMonoidalFunctor_η]
-/
lemma Discrete.monoidalFunctor_ε (F : M ->* N) :
    ε (monoidalFunctor F) = Discrete.eqToHom F.map_one.symm := rfl

@[to_additive Discrete.addMonoidalFunctor_η]
/--
lemma `Discrete.monoidalFunctor_η` / 引理 `Discrete.monoidalFunctor_η`

English:
lemma Discrete.monoidalFunctor_η
  given: (F : M ->* N)
  proof: rfl

@[to_additive Discrete.addMonoidalFunctor_μ]

中文:
引理 Discrete.monoidalFunctor_η
  条件: (F : M ->* N)
  证明: rfl

@[to_additive Discrete.addMonoidalFunctor_μ]
-/
lemma Discrete.monoidalFunctor_η (F : M ->* N) :
    η (monoidalFunctor F) = Discrete.eqToHom F.map_one := rfl

@[to_additive Discrete.addMonoidalFunctor_μ]
/--
lemma `Discrete.monoidalFunctor_μ` / 引理 `Discrete.monoidalFunctor_μ`

English:
lemma Discrete.monoidalFunctor_μ
  given: (F : M ->* N) (m₁ m₂ : Discrete M)
  proof: rfl

@[to_additive Discrete.addMonoidalFunctor_δ]

中文:
引理 Discrete.monoidalFunctor_μ
  条件: (F : M ->* N) (m₁ m₂ : Discrete M)
  证明: rfl

@[to_additive Discrete.addMonoidalFunctor_δ]
-/
lemma Discrete.monoidalFunctor_μ (F : M ->* N) (m₁ m₂ : Discrete M) :
    μ (monoidalFunctor F) m₁ m₂ = Discrete.eqToHom (F.map_mul _ _).symm := rfl

@[to_additive Discrete.addMonoidalFunctor_δ]
/--
lemma `Discrete.monoidalFunctor_δ` / 引理 `Discrete.monoidalFunctor_δ`

English:
lemma Discrete.monoidalFunctor_δ
  given: (F : M ->* N) (m₁ m₂ : Discrete M)
  proof: rfl

中文:
引理 Discrete.monoidalFunctor_δ
  条件: (F : M ->* N) (m₁ m₂ : Discrete M)
  证明: rfl
-/
lemma Discrete.monoidalFunctor_δ (F : M ->* N) (m₁ m₂ : Discrete M) :
    δ (monoidalFunctor F) m₁ m₂ = Discrete.eqToHom (F.map_mul _ _) := rfl

variable {K : Type u} [Monoid K]

/-- The monoidal natural isomorphism corresponding to composing two multiplicative morphisms.
-/
@[to_additive Discrete.addMonoidalFunctorComp
      /-- The monoidal natural isomorphism corresponding to
composing two additive morphisms. -/]
/--
Definition of `Discrete.monoidalFunctorComp` / `Discrete.monoidalFunctorComp` 的定义

English:
definition Discrete.monoidalFunctorComp
  signature: (F : M ->* N) (G : N ->* K)
  body: Iso.refl _

中文:
定义 Discrete.monoidalFunctorComp
  签名: (F : M ->* N) (G : N ->* K)
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
def Discrete.monoidalFunctorComp (F : M ->* N) (G : N ->* K) :
    Discrete.monoidalFunctor F ⋙ Discrete.monoidalFunctor G ≅
      Discrete.monoidalFunctor (G.comp F) := Iso.refl _

set_option backward.isDefEq.respectTransparency false in
@[to_additive Discrete.addMonoidalFunctorComp_isMonoidal]
/--
Instance `Discrete.monoidalFunctorComp_isMonoidal` / 实例 `Discrete.monoidalFunctorComp_isMonoidal`

English:
instance Discrete.monoidalFunctorComp_isMonoidal
  signature: (F : M ->* N) (G : N ->* K)
  body: by
    dsimp only [comp_ε, monoidalFunctorComp, Iso.refl, Discrete.monoidalFunctor_ε]
    simp [eqToHom_map]
  tensor _ _ := by
    dsimp only [comp_μ, monoidalFunctorComp, Iso.refl, Discrete.monoidalFunctor_μ]
    simp [eqToHom_map]

中文:
实例 Discrete.monoidalFunctorComp_isMonoidal
  签名: (F : M ->* N) (G : N ->* K)
  定义体: by
    dsimp only [comp_ε, monoidalFunctorComp, Iso.refl, Discrete.monoidalFunctor_ε]
    simp [eqToHom_map]
  tensor _ _ := by
    dsimp only [comp_μ, monoidalFunctorComp, Iso.refl, Discrete.monoidalFunctor_μ]
    simp [eqToHom_map]

Depends on / 依赖: Discrete, Discrete.monoidalFunctor_, Iso.refl, eqToHom_map, monoidalFunctorComp, tensor
-/
instance Discrete.monoidalFunctorComp_isMonoidal (F : M ->* N) (G : N ->* K) :
    NatTrans.IsMonoidal (Discrete.monoidalFunctorComp F G).hom where
  unit := by
    dsimp only [comp_ε, monoidalFunctorComp, Iso.refl, Discrete.monoidalFunctor_ε]
    simp [eqToHom_map]
  tensor _ _ := by
    dsimp only [comp_μ, monoidalFunctorComp, Iso.refl, Discrete.monoidalFunctor_μ]
    simp [eqToHom_map]

end CategoryTheory
