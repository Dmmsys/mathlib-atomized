/-
Copyright (c) 2026 Daniel Carranza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Carranza
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# The currying-uncurrying isomorphism between internal homs of a closed monoidal category

For a closed monoidal category `C`, we construct the isomorphism of internal hom objects
`C(x ⊗ y, z) ≅ C(y, C(x, z))` for any triple of objects `x y z : C`.

-/

@[expose] public section

universe u v

namespace CategoryTheory

open Category MonoidalCategory

namespace MonoidalClosed

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

-- TODO: Prove naturality of this morphism (requires the appropriate instances of `[Closed _]` for
-- objects in `C`).
/--
Definition of `ihomCurry` / `ihomCurry` 的定义

English:
definition ihomCurry
  signature: (x y z : C) [Closed x] [Closed y] [Closed (x otimes y)]
  body: curry (curry ((α_ x y _).inv ≫ (ihom.ev _).app z))

中文:
定义 ihomCurry
  签名: (x y z : C) [Closed x] [Closed y] [Closed (x otimes y)]
  定义体: curry (curry ((α_ x y _).inv ≫ (ihom.ev _).app z))

Depends on / 依赖: ihom.ev
-/
def ihomCurry (x y z : C) [Closed x] [Closed y] [Closed (x otimes y)] :
    (ihom (x otimes y)).obj z ⟶ (ihom y).obj ((ihom x).obj z) :=
  curry (curry ((α_ x y _).inv ≫ (ihom.ev _).app z))

/--
lemma `uncurry_ihomCurry` / 引理 `uncurry_ihomCurry`

English:
lemma uncurry_ihomCurry
  given: (x y z : C) [Closed x] [Closed y] [Closed (x otimes y)]
  proof: uncurry_curry _

中文:
引理 uncurry_ihomCurry
  条件: (x y z : C) [Closed x] [Closed y] [Closed (x otimes y)]
  证明: uncurry_curry _

Depends on / 依赖: uncurry_curry
-/
lemma uncurry_ihomCurry (x y z : C) [Closed x] [Closed y] [Closed (x otimes y)] :
    uncurry (ihomCurry x y z) = curry ((α_ x y _).inv ≫ (ihom.ev _).app z) :=
  uncurry_curry _

/--
lemma `uncurry_uncurry_ihomCurry` / 引理 `uncurry_uncurry_ihomCurry`

English:
lemma uncurry_uncurry_ihomCurry
  given: (x y z : C) [Closed x] [Closed y] [Closed (x otimes y)]
  proof: by
  simp [uncurry_ihomCurry]

中文:
引理 uncurry_uncurry_ihomCurry
  条件: (x y z : C) [Closed x] [Closed y] [Closed (x otimes y)]
  证明: by
  simp [uncurry_ihomCurry]

Depends on / 依赖: uncurry_ihomCurry
-/
lemma uncurry_uncurry_ihomCurry (x y z : C) [Closed x] [Closed y] [Closed (x otimes y)] :
    uncurry (uncurry (ihomCurry x y z)) = (α_ x y _).inv ≫ (ihom.ev _).app z := by
  simp [uncurry_ihomCurry]

-- TODO: Prove naturality of this morphism (requires the appropriate instances of `[Closed _]` for
-- objects in `C`).
/--
Definition of `ihomUncurry` / `ihomUncurry` 的定义

English:
definition ihomUncurry
  signature: (x y z : C) [Closed x] [Closed y] [Closed (x otimes y)]
  body: curry ((α_ x y _).hom ≫ x ◁ (ihom.ev y).app ((ihom x).obj z) ≫ (ihom.ev x).app z)

中文:
定义 ihomUncurry
  签名: (x y z : C) [Closed x] [Closed y] [Closed (x otimes y)]
  定义体: curry ((α_ x y _).hom ≫ x ◁ (ihom.ev y).app ((ihom x).obj z) ≫ (ihom.ev x).app z)

Depends on / 依赖: ihom.ev
-/
def ihomUncurry (x y z : C) [Closed x] [Closed y] [Closed (x otimes y)] :
    (ihom y).obj ((ihom x).obj z) ⟶ (ihom (x otimes y)).obj z :=
  curry ((α_ x y _).hom ≫ x ◁ (ihom.ev y).app ((ihom x).obj z) ≫ (ihom.ev x).app z)

/--
lemma `uncurry_ihomUncurry` / 引理 `uncurry_ihomUncurry`

English:
lemma uncurry_ihomUncurry
  given: (x y z : C) [Closed x] [Closed y] [Closed (x otimes y)]
  proof: uncurry_curry _

@[reassoc (attr := simp)]

中文:
引理 uncurry_ihomUncurry
  条件: (x y z : C) [Closed x] [Closed y] [Closed (x otimes y)]
  证明: uncurry_curry _

@[reassoc (attr := simp)]

Depends on / 依赖: uncurry_curry
-/
lemma uncurry_ihomUncurry (x y z : C) [Closed x] [Closed y] [Closed (x otimes y)] :
    uncurry (ihomUncurry x y z) = (α_ x y _).hom ≫ x ◁ (ihom.ev y).app ((ihom x).obj z) ≫
    (ihom.ev x).app z :=
  uncurry_curry _

@[reassoc (attr := simp)]
/--
theorem `ihomUncurry_ihomCurry` / 定理 `ihomUncurry_ihomCurry`

English:
theorem ihomUncurry_ihomCurry
  given: (x y z : C) [Closed x] [Closed y] [Closed (x otimes y)]
  proof: by
  apply uncurry_injective
  apply uncurry_injective
  simp only [uncurry_natural_left, uncurry_uncurry_ihomCurry, Functor.id_obj, uncurry_id_eq_ev]
  rw [associator_inv_naturality_right_assoc]; rw [← dsimp% uncurry_eq]; rw [uncurry_ihomUncurry]
  simp
  rfl

@[reassoc (attr := simp)]

中文:
定理 ihomUncurry_ihomCurry
  条件: (x y z : C) [Closed x] [Closed y] [Closed (x otimes y)]
  证明: by
  apply uncurry_injective
  apply uncurry_injective
  simp only [uncurry_natural_left, uncurry_uncurry_ihomCurry, Functor.id_obj, uncurry_id_eq_ev]
  rw [associator_inv_naturality_right_assoc]; rw [← dsimp% uncurry_eq]; rw [uncurry_ihomUncurry]
  simp
  rfl

@[reassoc (attr := simp)]

Depends on / 依赖: Functor, Functor.id_obj, associator_inv_naturality_right_assoc, id_obj, uncurry_eq, uncurry_id_eq_ev, uncurry_ihomUncurry, uncurry_injective, uncurry_natural_left, uncurry_uncurry_ihomCurry
-/
theorem ihomUncurry_ihomCurry (x y z : C) [Closed x] [Closed y] [Closed (x otimes y)] :
    ihomUncurry x y z ≫ ihomCurry x y z = 𝟙 _ := by
  apply uncurry_injective
  apply uncurry_injective
  simp only [uncurry_natural_left, uncurry_uncurry_ihomCurry, Functor.id_obj, uncurry_id_eq_ev]
  rw [associator_inv_naturality_right_assoc]; rw [← dsimp% uncurry_eq]; rw [uncurry_ihomUncurry]
  simp
  rfl

@[reassoc (attr := simp)]
/--
theorem `ihomCurry_ihomUncurry` / 定理 `ihomCurry_ihomUncurry`

English:
theorem ihomCurry_ihomUncurry
  given: (x y z : C) [Closed x] [Closed y] [Closed (x otimes y)]
  proof: by
  apply uncurry_injective
  rw [uncurry_natural_left]; rw [uncurry_id_eq_ev]; rw [uncurry_ihomUncurry]
  dsimp
  rw [associator_naturality_right_assoc]; rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  simp [← dsimp% uncurry_eq, uncurry_uncurry_ihomCurry]

中文:
定理 ihomCurry_ihomUncurry
  条件: (x y z : C) [Closed x] [Closed y] [Closed (x otimes y)]
  证明: by
  apply uncurry_injective
  rw [uncurry_natural_left]; rw [uncurry_id_eq_ev]; rw [uncurry_ihomUncurry]
  dsimp
  rw [associator_naturality_right_assoc]; rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  simp [← dsimp% uncurry_eq, uncurry_uncurry_ihomCurry]

Depends on / 依赖: MonoidalCategory, MonoidalCategory.whiskerLeft_comp_assoc, associator_naturality_right_assoc, uncurry_eq, uncurry_id_eq_ev, uncurry_ihomUncurry, uncurry_injective, uncurry_natural_left, uncurry_uncurry_ihomCurry, whiskerLeft_comp_assoc
-/
theorem ihomCurry_ihomUncurry (x y z : C) [Closed x] [Closed y] [Closed (x otimes y)] :
    ihomCurry x y z ≫ ihomUncurry x y z = 𝟙 _ := by
  apply uncurry_injective
  rw [uncurry_natural_left]; rw [uncurry_id_eq_ev]; rw [uncurry_ihomUncurry]
  dsimp
  rw [associator_naturality_right_assoc]; rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  simp [← dsimp% uncurry_eq, uncurry_uncurry_ihomCurry]

/-- The internal currying-uncurrying isomorphism `C(x ⊗ y, z) ≅ C(y, C(x, z))`. -/
@[simps]
/--
Definition of `ihomCurryIso` / `ihomCurryIso` 的定义

English:
definition ihomCurryIso
  signature: (x y z : C) [Closed x] [Closed y] [Closed (x otimes y)]
  body: ihomCurry x y z
  inv := ihomUncurry x y z
  hom_inv_id := ihomCurry_ihomUncurry x y z
  inv_hom_id := ihomUncurry_ihomCurry x y z

中文:
定义 ihomCurryIso
  签名: (x y z : C) [Closed x] [Closed y] [Closed (x otimes y)]
  定义体: ihomCurry x y z
  inv := ihomUncurry x y z
  hom_inv_id := ihomCurry_ihomUncurry x y z
  inv_hom_id := ihomUncurry_ihomCurry x y z

Depends on / 依赖: ihomCurry
-/
def ihomCurryIso (x y z : C) [Closed x] [Closed y] [Closed (x otimes y)] :
    (ihom (x otimes y)).obj z ≅ (ihom y).obj ((ihom x).obj z) where
  hom := ihomCurry x y z
  inv := ihomUncurry x y z
  hom_inv_id := ihomCurry_ihomUncurry x y z
  inv_hom_id := ihomUncurry_ihomCurry x y z

end CategoryTheory.MonoidalClosed

end
