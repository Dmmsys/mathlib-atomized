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
/-
**AlgebraicTopology.DoldKan.N** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicTopology.DoldK
an`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `SimplicialObject C ⥤ Karoubi (ChainComplex C ℕ)` which maps
`X` to the formal direct factor of `K[X]` defined by `PInfty`.
-/
def N₁ : SimplicialObject C ⥤ Karoubi (ChainComplex C ℕ) where
  obj X :=
    { X := AlternatingFaceMapComplex.obj X
      p := PInfty
      idem := PInfty_idem }
  map f :=
    { f := PInfty ≫ AlternatingFaceMapComplex.map f }

/-- The extension of `N₁` to the Karoubi envelope of `SimplicialObject C`. -/
@[simps!]
/-
**AlgebraicTopology.DoldKan.N** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicTopology.DoldK
an`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The extension of `N₁` to the Karoubi envelope of `SimplicialObject C`.
-/
def N₂ : Karoubi (SimplicialObject C) ⥤ Karoubi (ChainComplex C ℕ) :=
  (functorExtension₁ _ _).obj N₁

/-- The canonical isomorphism `toKaroubi (SimplicialObject C) ⋙ N₂ ≅ N₁`. -/
/-
**AlgebraicTopology.DoldKan.toKaroubiCompN** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicT
opology.DoldKan`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `toKaroubi (SimplicialObject C) ⋙ N₂ ≅ N₁`.
-/
def toKaroubiCompN₂IsoN₁ : toKaroubi (SimplicialObject C) ⋙ N₂ ≅ N₁ :=
  (functorExtension₁CompWhiskeringLeftToKaroubiIso _ _).app N₁

@[simp]
/-
**AlgebraicTopology.DoldKan.toKaroubiCompN** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicT
opology.DoldKan`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toKaroubiCompN₂IsoN₁_hom_app (X : SimplicialObject C) :
    (toKaroubiCompN₂IsoN₁.hom.app X).f = PInfty := rfl

@[simp]
/-
**AlgebraicTopology.DoldKan.toKaroubiCompN** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicT
opology.DoldKan`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toKaroubiCompN₂IsoN₁_inv_app (X : SimplicialObject C) :
    (toKaroubiCompN₂IsoN₁.inv.app X).f = PInfty := rfl

end DoldKan

end AlgebraicTopology

