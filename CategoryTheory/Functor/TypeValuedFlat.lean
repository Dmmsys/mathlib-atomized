/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# Type-valued flat functors

A functor `F : C ⥤ Type w` is a flat Type-valued functor if the category
`F.Elements` is cofiltered. (This is not equivalent to saying that `F`
is representably flat in the sense of the typeclass `RepresentablyFlat`
defined in the file `Mathlib/CategoryTheory/Functor/Flat.lean`, see also
https://golem.ph.utexas.edu/category/2011/06/flat_functors_and_morphisms_of.html
for a clarification about the differences between these notions.)

In this file, we show that if finite limits exist in `C` and are preserved by `F`,
then `F.Elements` is cofiltered.

-/

public section

universe w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

/--
lemma `Functor.isCofiltered_elements` / 引理 `Functor.isCofiltered_elements`

English:
lemma Functor.isCofiltered_elements
  proof: ⟨⊤_ C, (terminalIsTerminal.isTerminalObj F).from PUnit .unit⟩
  cone_objs := by
    rintro ⟨X, x⟩ ⟨Y, y⟩
    let h := mapIsLimitOfPreservesOfIsLimit F _ _ (prodIsProd X Y)
    let h' := Types.binaryProductLimit (F.obj X) (F.obj Y)
    exact ⟨⟨X ⨯ Y, (h'.conePointUniqueUpToIso h).hom ⟨x, y⟩⟩,
      ⟨

中文:
引理 Functor.isCofiltered_elements
  证明: ⟨⊤_ C, (terminalIsTerminal.isTerminalObj F).from PUnit .unit⟩
  cone_objs := by
    rintro ⟨X, x⟩ ⟨Y, y⟩
    let h := mapIsLimitOfPreservesOfIsLimit F _ _ (prodIsProd X Y)
    let h' := Types.binaryProductLimit (F.obj X) (F.obj Y)
    exact ⟨⟨X ⨯ Y, (h'.conePointUniqueUpToIso h).hom ⟨x, y⟩⟩,
      ⟨

Depends on / 依赖: isTerminalObj, terminalIsTerminal, terminalIsTerminal.isTerminalObj
-/
lemma Functor.isCofiltered_elements
    (F : C ⥤ Type w) [HasFiniteLimits C] [PreservesFiniteLimits F] :
    IsCofiltered F.Elements where
  nonempty := ⟨⊤_ C, (terminalIsTerminal.isTerminalObj F).from PUnit .unit⟩
  cone_objs := by
    rintro ⟨X, x⟩ ⟨Y, y⟩
    let h := mapIsLimitOfPreservesOfIsLimit F _ _ (prodIsProd X Y)
    let h' := Types.binaryProductLimit (F.obj X) (F.obj Y)
    exact ⟨⟨X ⨯ Y, (h'.conePointUniqueUpToIso h).hom ⟨x, y⟩⟩,
      ⟨prod.fst, ConcreteCategory.congr_hom (h'.conePointUniqueUpToIso_hom_comp h (.mk .left)) _⟩,
      ⟨prod.snd, ConcreteCategory.congr_hom (h'.conePointUniqueUpToIso_hom_comp h (.mk .right)) _⟩,
      by tauto⟩
  cone_maps := by
    rintro ⟨X, x⟩ ⟨Y, y⟩ ⟨f, hf⟩ ⟨g, hg⟩
    dsimp at f g hf hg
    rw [← hg] at hf
    let h := isLimitForkMapOfIsLimit F _ (equalizerIsEqualizer f g)
    let h' := (Types.equalizerLimit (g := F.map f) (h := F.map g)).isLimit
    exact ⟨⟨equalizer f g, (h'.conePointUniqueUpToIso h).hom ⟨x, hf⟩⟩,
      ⟨equalizer.ι f g, ConcreteCategory.congr_hom
        (h'.conePointUniqueUpToIso_hom_comp h .zero) ⟨x, hf⟩⟩,
      by ext; exact equalizer.condition f g⟩

namespace FunctorToTypes

variable (F : C ⥤ Type w) {X : C} (x : F.obj X)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `fromOverSubfunctor` / `fromOverSubfunctor` 的定义

English:
definition fromOverSubfunctor
  signature: : Subfunctor (Over.forget X ⋙ F) where
  body: F.map U.hom ⁻¹' {x}
  map _ _ _ := by simpa [← comp_apply, ← Functor.map_comp]

@[simp]

中文:
定义 fromOverSubfunctor
  签名: : Subfunctor (Over.forget X ⋙ F) where
  定义体: F.map U.hom ⁻¹' {x}
  map _ _ _ := by simpa [← comp_apply, ← Functor.map_comp]

@[simp]

Depends on / 依赖: F.map, U.hom
-/
def fromOverSubfunctor : Subfunctor (Over.forget X ⋙ F) where
  obj U := F.map U.hom ⁻¹' {x}
  map _ _ _ := by simpa [← comp_apply, ← Functor.map_comp]

@[simp]
/--
lemma `mem_fromOverSubfunctor_iff` / 引理 `mem_fromOverSubfunctor_iff`

English:
lemma mem_fromOverSubfunctor_iff
  given: {U : Over X} (u : F.obj U.left)
  proof: Iff.rfl

中文:
引理 mem_fromOverSubfunctor_iff
  条件: {U : Over X} (u : F.obj U.left)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_fromOverSubfunctor_iff {U : Over X} (u : F.obj U.left) :
    u in (fromOverSubfunctor F x).obj U ↔ F.map U.hom u = x := Iff.rfl

/--
Definition of `fromOverFunctor` / `fromOverFunctor` 的定义

English:
abbreviation fromOverFunctor
  signature: : Over X ⥤ Type w
  body: (fromOverSubfunctor F x).toFunctor

中文:
缩写 fromOverFunctor
  签名: : Over X ⥤ Type w
  定义体: (fromOverSubfunctor F x).toFunctor

Depends on / 依赖: fromOverSubfunctor, toFunctor
-/
abbrev fromOverFunctor : Over X ⥤ Type w := (fromOverSubfunctor F x).toFunctor

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open CategoryOfElements in
/--
Definition of `fromOverFunctorElementsEquivalence` / `fromOverFunctorElementsEquivalence` 的定义

English:
definition fromOverFunctorElementsEquivalence
  signature: :
  body: Over.mk (homMk (F.elementsMk u.fst.left u.snd.1) _ u.fst.hom u.snd.2)
  functor.map f :=
    Over.homMk (homMk _ _ f.val.left (Subtype.ext_iff.1 f.prop))
  inverse.obj u :=
    Functor.elementsMk _ (Over.mk u.hom.1) ⟨u.left.snd, u.hom.2⟩
  inverse.map f := homMk _ _ (Over.homMk f.left.val (Subtype.e

中文:
定义 fromOverFunctorElementsEquivalence
  签名: :
  定义体: Over.mk (homMk (F.elementsMk u.fst.left u.snd.1) _ u.fst.hom u.snd.2)
  functor.map f :=
    Over.homMk (homMk _ _ f.val.left (Subtype.ext_iff.1 f.prop))
  inverse.obj u :=
    Functor.elementsMk _ (Over.mk u.hom.1) ⟨u.left.snd, u.hom.2⟩
  inverse.map f := homMk _ _ (Over.homMk f.left.val (Subtype.e

Depends on / 依赖: F.elementsMk, Functor, Functor.elementsMk, Iso.refl, Over.homMk, Over.mk, Over.w, Subtype, Subtype.ext_iff, cat_disch, counitIso, elementsMk, ext_iff, f.left.val, f.prop, f.val.left, functor, functor.map, inverse, inverse.map
-/
def fromOverFunctorElementsEquivalence :
    (fromOverFunctor F x).Elements ≌ Over (F.elementsMk X x) where
  functor.obj u :=
    Over.mk (homMk (F.elementsMk u.fst.left u.snd.1) _ u.fst.hom u.snd.2)
  functor.map f :=
    Over.homMk (homMk _ _ f.val.left (Subtype.ext_iff.1 f.prop))
  inverse.obj u :=
    Functor.elementsMk _ (Over.mk u.hom.1) ⟨u.left.snd, u.hom.2⟩
  inverse.map f := homMk _ _ (Over.homMk f.left.val (Subtype.ext_iff.1 (Over.w f)))
    (by cat_disch)
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  -- `cat_disch` can fill in this proof, but is unfortunately quite slow.
  functor_unitIso_comp X := by simp_all; rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsCofiltered
  signature: F.Elements] : IsCofiltered (fromOverFunctor F x).Elements
  body: .of_equivalence (fromOverFunctorElementsEquivalence F x).symm

中文:
实例 [IsCofiltered
  签名: F.Elements] : IsCofiltered (fromOverFunctor F x).Elements
  定义体: .of_equivalence (fromOverFunctorElementsEquivalence F x).symm

Depends on / 依赖: fromOverFunctorElementsEquivalence, of_equivalence
-/
instance [IsCofiltered F.Elements] : IsCofiltered (fromOverFunctor F x).Elements :=
  .of_equivalence (fromOverFunctorElementsEquivalence F x).symm

end FunctorToTypes

end CategoryTheory
