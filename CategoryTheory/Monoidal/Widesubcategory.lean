/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

module

public import Mathlib.CategoryTheory.CopyDiscardCategory.Basic
public import Mathlib.CategoryTheory.Localization.Monoidal.Basic
public import Mathlib.CategoryTheory.Widesubcategory

/-!
# Monoidal structures on wide subcategories

Given a monoidal category `C` and a morphism property `P : MorphismProperty C`,
this file introduces conditions on `P` ensuring that `WideSubcategory P` inherits
additional structures.

We define stability classes under associators, unitors, and braidings, and use
them to construct monoidal, braided, and symmetric structures on
`WideSubcategory P`.

-/

public section

namespace CategoryTheory

open scoped MonoidalCategory

variable {C : Type*} [Category* C] (P : MorphismProperty C) [MonoidalCategory C]

namespace MorphismProperty

/--
Definition of `IsStableUnderAssociator` / `IsStableUnderAssociator` 的定义

English:
class IsStableUnderAssociator
  parameters: (P : MorphismProperty C)
  axioms and operations (2):
    - associator_hom_mem((P) (c c' c'' : C)) : P (α_ c c' c'').hom
    - associator_inv_mem((P) (c c' c'' : C)) : P (α_ c c' c'').inv

中文:
类 IsStableUnderAssociator
  参数: (P : Morphism命题erty C)
  公理与运算 (2 个):
    - associator_hom_mem((P) (c c' c'' : C)) : P (α_ c c' c'').hom
    - associator_inv_mem((P) (c c' c'' : C)) : P (α_ c c' c'').inv
-/
class IsStableUnderAssociator (P : MorphismProperty C) : Prop where
  associator_hom_mem (P) (c c' c'' : C) : P (α_ c c' c'').hom
  associator_inv_mem (P) (c c' c'' : C) : P (α_ c c' c'').inv

export IsStableUnderAssociator (associator_hom_mem associator_inv_mem)

/--
Definition of `IsStableUnderUnitor` / `IsStableUnderUnitor` 的定义

English:
class IsStableUnderUnitor
  parameters: (P : MorphismProperty C)
  axioms and operations (4):
    - leftUnitor_hom_mem((P) (c : C)) : P ((fun_ c).hom)
    - leftUnitor_inv_mem((P) (c : C)) : P ((fun_ c).inv)
    - rightUnitor_hom_mem((P) (c : C)) : P ((ρ_ c).hom)
    - rightUnitor_inv_mem((P) (c : C)) : P ((ρ_ c).inv)

中文:
类 IsStableUnderUnitor
  参数: (P : Morphism命题erty C)
  公理与运算 (4 个):
    - leftUnitor_hom_mem((P) (c : C)) : P ((fun_ c).hom)
    - leftUnitor_inv_mem((P) (c : C)) : P ((fun_ c).inv)
    - rightUnitor_hom_mem((P) (c : C)) : P ((ρ_ c).hom)
    - rightUnitor_inv_mem((P) (c : C)) : P ((ρ_ c).inv)
-/
class IsStableUnderUnitor (P : MorphismProperty C) : Prop where
  leftUnitor_hom_mem (P) (c : C) : P ((fun_ c).hom)
  leftUnitor_inv_mem (P) (c : C) : P ((fun_ c).inv)
  rightUnitor_hom_mem (P) (c : C) : P ((ρ_ c).hom)
  rightUnitor_inv_mem (P) (c : C) : P ((ρ_ c).inv)

export IsStableUnderUnitor (leftUnitor_hom_mem leftUnitor_inv_mem rightUnitor_hom_mem
  rightUnitor_inv_mem)

/--
Definition of `IsMonoidalStable` / `IsMonoidalStable` 的定义

English:
class IsMonoidalStable
  parameters: : Prop extends IsMonoidal P, IsStableUnderAssociator P,
  extends: IsMonoidal P, IsStableUnderAssociator P, 
  (no additional axioms)

中文:
类 IsMonoidalStable
  参数: : 命题 extends IsMonoidal P, IsStableUnderAssociator P,
  继承: IsMonoidal P, IsStableUnderAssociator P, 
  (无附加公理)
-/
class IsMonoidalStable : Prop extends IsMonoidal P, IsStableUnderAssociator P,
    IsStableUnderUnitor P

/--
Definition of `IsStableUnderBraiding` / `IsStableUnderBraiding` 的定义

English:
class IsStableUnderBraiding
  parameters: [BraidedCategory C] (P : MorphismProperty C)
  extends: IsMonoidalStable P
  axioms and operations (2):
    - braiding_hom_mem((P) (c c' : C)) : P (β_ c c').hom
    - braiding_inv_mem((P) (c c' : C)) : P (β_ c c').inv

中文:
类 IsStableUnderBraiding
  参数: [BraidedCategory C] (P : Morphism命题erty C)
  继承: IsMonoidalStable P
  公理与运算 (2 个):
    - braiding_hom_mem((P) (c c' : C)) : P (β_ c c').hom
    - braiding_inv_mem((P) (c c' : C)) : P (β_ c c').inv
-/
class IsStableUnderBraiding [BraidedCategory C] (P : MorphismProperty C) : Prop
    extends IsMonoidalStable P where
  braiding_hom_mem (P) (c c' : C) : P (β_ c c').hom
  braiding_inv_mem (P) (c c' : C) : P (β_ c c').inv

export IsStableUnderBraiding (braiding_hom_mem braiding_inv_mem)

end MorphismProperty

namespace WideSubcategory

@[simps]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsMonoidalStable]
  signature: : MonoidalCategoryStruct (WideSubcategory P) where
  body: ⟨c.obj otimes c'.obj⟩
  whiskerLeft c _ _ f := ⟨c.obj ◁ f.1, P.whiskerLeft_mem _ _ f.2⟩
  whiskerRight f c' := ⟨f.1 ▷ c'.obj, P.whiskerRight_mem _ f.2 _⟩
  tensorUnit := ⟨𝟙_ C⟩
  associator _ _ _ :=
    isoMk (α_ _ _ _) (P.associator_hom_mem _ _ _) (P.associator_inv_mem _ _ _)
  leftUnitor _ :=
    

中文:
实例 [P.IsMonoidalStable]
  签名: : MonoidalCategoryStruct (WideSubcategory P) where
  定义体: ⟨c.obj otimes c'.obj⟩
  whiskerLeft c _ _ f := ⟨c.obj ◁ f.1, P.whiskerLeft_mem _ _ f.2⟩
  whiskerRight f c' := ⟨f.1 ▷ c'.obj, P.whiskerRight_mem _ f.2 _⟩
  tensorUnit := ⟨𝟙_ C⟩
  associator _ _ _ :=
    isoMk (α_ _ _ _) (P.associator_hom_mem _ _ _) (P.associator_inv_mem _ _ _)
  leftUnitor _ :=
    

Depends on / 依赖: c.obj, otimes
-/
instance [P.IsMonoidalStable] : MonoidalCategoryStruct (WideSubcategory P) where
  tensorObj c c' := ⟨c.obj otimes c'.obj⟩
  whiskerLeft c _ _ f := ⟨c.obj ◁ f.1, P.whiskerLeft_mem _ _ f.2⟩
  whiskerRight f c' := ⟨f.1 ▷ c'.obj, P.whiskerRight_mem _ f.2 _⟩
  tensorUnit := ⟨𝟙_ C⟩
  associator _ _ _ :=
    isoMk (α_ _ _ _) (P.associator_hom_mem _ _ _) (P.associator_inv_mem _ _ _)
  leftUnitor _ :=
    isoMk (fun_ _) (P.leftUnitor_hom_mem _) (P.leftUnitor_inv_mem _)
  rightUnitor _ :=
    isoMk (ρ_ _) (P.rightUnitor_hom_mem _) (P.rightUnitor_inv_mem _)
  tensorHom f g := ⟨f.1 otimesₘ g.1, P.tensorHom_mem _ _ f.2 g.2⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsMonoidalStable]
  signature: : MonoidalCategory (WideSubcategory P)
  body: Monoidal.induced (wideSubcategoryInclusion P)
    { εIso := Iso.refl _
      μIso _ _ := Iso.refl _ }

中文:
实例 [P.IsMonoidalStable]
  签名: : MonoidalCategory (WideSubcategory P)
  定义体: Monoidal.induced (wideSubcategoryInclusion P)
    { εIso := Iso.refl _
      μIso _ _ := Iso.refl _ }

Depends on / 依赖: Iso.refl, Monoidal, Monoidal.induced, induced, wideSubcategoryInclusion
-/
instance [P.IsMonoidalStable] : MonoidalCategory (WideSubcategory P) :=
  Monoidal.induced (wideSubcategoryInclusion P)
    { εIso := Iso.refl _
      μIso _ _ := Iso.refl _ }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [BraidedCategory
  signature: C] [P.IsStableUnderBraiding] :
  body: isoMk (β_ _ _) (P.braiding_hom_mem _ _) (P.braiding_inv_mem _ _)

中文:
实例 [BraidedCategory
  签名: C] [P.IsStableUnderBraiding] :
  定义体: isoMk (β_ _ _) (P.braiding_hom_mem _ _) (P.braiding_inv_mem _ _)

Depends on / 依赖: P.braiding_hom_mem, P.braiding_inv_mem, braiding_hom_mem, braiding_inv_mem
-/
instance [BraidedCategory C] [P.IsStableUnderBraiding] :
    BraidedCategory (WideSubcategory P) where
  braiding _ _ :=
    isoMk (β_ _ _) (P.braiding_hom_mem _ _) (P.braiding_inv_mem _ _)

variable {P} in
open MonoidalCategory in
@[simp]
/--
lemma `tensorμ_hom` / 引理 `tensorμ_hom`

English:
lemma tensorμ_hom
  given: [BraidedCategory C] [P.IsStableUnderBraiding] (X Y Z T : WideSubcategory P)
  proof: rfl

中文:
引理 tensorμ_hom
  条件: [BraidedCategory C] [P.IsStableUnderBraiding] (X Y Z T : WideSubcategory P)
  证明: rfl
-/
lemma tensorμ_hom [BraidedCategory C] [P.IsStableUnderBraiding] (X Y Z T : WideSubcategory P) :
    (tensorμ X Y Z T).hom = tensorμ _ _ _ _ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SymmetricCategory
  signature: C] [P.IsStableUnderBraiding] :
  body: by
    ext
    exact SymmetricCategory.symmetry _ _

中文:
实例 [SymmetricCategory
  签名: C] [P.IsStableUnderBraiding] :
  定义体: by
    ext
    exact SymmetricCategory.symmetry _ _

Depends on / 依赖: SymmetricCategory, SymmetricCategory.symmetry, symmetry
-/
instance [SymmetricCategory C] [P.IsStableUnderBraiding] :
    SymmetricCategory (WideSubcategory P) where
  symmetry c c' := by
    ext
    exact SymmetricCategory.symmetry _ _

end WideSubcategory

end CategoryTheory
