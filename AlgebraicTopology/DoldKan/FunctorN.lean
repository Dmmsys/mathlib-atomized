/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.DoldKan.PInfty

/-!

# Construction of functors N for the Dold-Kan correspondence

In this file, we construct functors `N₁ : SimplicialObject C ⥤ Karoubi (ChainComplex C ℕ)`
and `N₂ : Karoubi (SimplicialObject C) ⥤ Karoubi (ChainComplex C ℕ)`
for any preadditive category `C`. (The indices of these functors are the number of occurrences
of `Karoubi` at the source or the target.)

In the case `C` is additive, the functor `N₂` shall be the functor of the equivalence
`CategoryTheory.Preadditive.DoldKan.equivalence` defined in `EquivalenceAdditive.lean`.

In the case the category `C` is pseudoabelian, the composition of `N₁` with the inverse of the
equivalence `ChainComplex C ℕ ⥤ Karoubi (ChainComplex C ℕ)` will be the functor
`CategoryTheory.Idempotents.DoldKan.N` of the equivalence of categories
`CategoryTheory.Idempotents.DoldKan.equivalence : SimplicialObject C ≌ ChainComplex C ℕ`
defined in `EquivalencePseudoabelian.lean`.

When the category `C` is abelian, a relation between `N₁` and the
normalized Moore complex functor shall be obtained in `Normalized.lean`.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/

@[expose] public section


open CategoryTheory CategoryTheory.Category CategoryTheory.Idempotents

noncomputable section

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type*} [Category* C] [Preadditive C]

set_option backward.isDefEq.respectTransparency false in
/-- The functor `SimplicialObject C ⥤ Karoubi (ChainComplex C ℕ)` which maps
`X` to the formal direct factor of `K[X]` defined by `PInfty`. -/
@[simps, implicit_reducible]
/--
Definition of `N₁` / `N₁` 的定义

English:
definition N₁
  signature: : SimplicialObject C ⥤ Karoubi (ChainComplex C Nat) where
  body: { X := AlternatingFaceMapComplex.obj X
      p := PInfty
      idem := PInfty_idem }
  map f :=
    { f := PInfty ≫ AlternatingFaceMapComplex.map f }

中文:
定义 N₁
  签名: : SimplicialObject C ⥤ Karoubi (ChainComplex C 自然数) where
  定义体: { X := AlternatingFaceMapComplex.obj X
      p := PInfty
      idem := PInfty_idem }
  map f :=
    { f := PInfty ≫ AlternatingFaceMapComplex.map f }

Depends on / 依赖: AlternatingFaceMapComplex, AlternatingFaceMapComplex.map, AlternatingFaceMapComplex.obj, PInfty, PInfty_idem
-/
def N₁ : SimplicialObject C ⥤ Karoubi (ChainComplex C Nat) where
  obj X :=
    { X := AlternatingFaceMapComplex.obj X
      p := PInfty
      idem := PInfty_idem }
  map f :=
    { f := PInfty ≫ AlternatingFaceMapComplex.map f }

/-- The extension of `N₁` to the Karoubi envelope of `SimplicialObject C`. -/
@[simps!]
/--
Definition of `N₂` / `N₂` 的定义

English:
definition N₂
  signature: : Karoubi (SimplicialObject C) ⥤ Karoubi (ChainComplex C Nat)
  body: (functorExtension₁ _ _).obj N₁

中文:
定义 N₂
  签名: : Karoubi (SimplicialObject C) ⥤ Karoubi (ChainComplex C 自然数)
  定义体: (functorExtension₁ _ _).obj N₁
-/
def N₂ : Karoubi (SimplicialObject C) ⥤ Karoubi (ChainComplex C Nat) :=
  (functorExtension₁ _ _).obj N₁

/--
Definition of `toKaroubiCompN₂IsoN₁` / `toKaroubiCompN₂IsoN₁` 的定义

English:
definition toKaroubiCompN₂IsoN₁
  signature: : toKaroubi (SimplicialObject C) ⋙ N₂ ≅ N₁
  body: (functorExtension₁CompWhiskeringLeftToKaroubiIso _ _).app N₁

@[simp]

中文:
定义 toKaroubiCompN₂IsoN₁
  签名: : toKaroubi (SimplicialObject C) ⋙ N₂ ≅ N₁
  定义体: (functorExtension₁CompWhiskeringLeftToKaroubiIso _ _).app N₁

@[simp]
-/
def toKaroubiCompN₂IsoN₁ : toKaroubi (SimplicialObject C) ⋙ N₂ ≅ N₁ :=
  (functorExtension₁CompWhiskeringLeftToKaroubiIso _ _).app N₁

@[simp]
/--
lemma `toKaroubiCompN₂IsoN₁_hom_app` / 引理 `toKaroubiCompN₂IsoN₁_hom_app`

English:
lemma toKaroubiCompN₂IsoN₁_hom_app
  given: (X : SimplicialObject C)
  proof: rfl

@[simp]

中文:
引理 toKaroubiCompN₂IsoN₁_hom_app
  条件: (X : SimplicialObject C)
  证明: rfl

@[simp]
-/
lemma toKaroubiCompN₂IsoN₁_hom_app (X : SimplicialObject C) :
    (toKaroubiCompN₂IsoN₁.hom.app X).f = PInfty := rfl

@[simp]
/--
lemma `toKaroubiCompN₂IsoN₁_inv_app` / 引理 `toKaroubiCompN₂IsoN₁_inv_app`

English:
lemma toKaroubiCompN₂IsoN₁_inv_app
  given: (X : SimplicialObject C)
  proof: rfl

中文:
引理 toKaroubiCompN₂IsoN₁_inv_app
  条件: (X : SimplicialObject C)
  证明: rfl
-/
lemma toKaroubiCompN₂IsoN₁_inv_app (X : SimplicialObject C) :
    (toKaroubiCompN₂IsoN₁.inv.app X).f = PInfty := rfl

end DoldKan

end AlgebraicTopology
