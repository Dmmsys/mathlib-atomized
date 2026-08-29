/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Preserving binary products

Constructions to relate the notions of preserving binary products and reflecting binary products
to concrete binary fans.

In particular, we show that `ProdComparison G X Y` is an isomorphism iff `G` preserves
the product of `X` and `Y`.
-/

@[expose] public section


noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (G : C ⥤ D)

namespace CategoryTheory.Limits

section

variable {P X Y Z : C} (f : P ⟶ X) (g : P ⟶ Y)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isLimitMapConeBinaryFanEquiv` / `isLimitMapConeBinaryFanEquiv` 的定义

English:
definition isLimitMapConeBinaryFanEquiv
  signature: :
  body: (IsLimit.postcomposeHomEquiv (diagramIsoPair _) _).symm.trans
    (IsLimit.equivIsoLimit
      (Cone.ext (Iso.refl _)
        (by rintro (_ | _) <;> simp)))

中文:
定义 isLimitMapConeBinaryFanEquiv
  签名: :
  定义体: (IsLimit.postcomposeHomEquiv (diagramIsoPair _) _).symm.trans
    (IsLimit.equivIsoLimit
      (Cone.ext (Iso.refl _)
        (by rintro (_ | _) <;> simp)))

Depends on / 依赖: Cone.ext, IsLimit, IsLimit.equivIsoLimit, IsLimit.postcomposeHomEquiv, Iso.refl, diagramIsoPair, equivIsoLimit, postcomposeHomEquiv, symm.trans
-/
def isLimitMapConeBinaryFanEquiv :
    IsLimit (G.mapCone (BinaryFan.mk f g)) ≃ IsLimit (BinaryFan.mk (G.map f) (G.map g)) :=
  (IsLimit.postcomposeHomEquiv (diagramIsoPair _) _).symm.trans
    (IsLimit.equivIsoLimit
      (Cone.ext (Iso.refl _)
        (by rintro (_ | _) <;> simp)))

/--
Definition of `mapIsLimitOfPreservesOfIsLimit` / `mapIsLimitOfPreservesOfIsLimit` 的定义

English:
definition mapIsLimitOfPreservesOfIsLimit
  signature: [PreservesLimit (pair X Y) G] (l : IsLimit (BinaryFan.mk f g))
  body: isLimitMapConeBinaryFanEquiv G f g (isLimitOfPreserves G l)

中文:
定义 mapIsLimitOfPreservesOfIsLimit
  签名: [保持极限 (pair X Y) G] (l : 是极限 (BinaryFan.mk f g))
  定义体: isLimitMapConeBinaryFanEquiv G f g (isLimitOfPreserves G l)

Depends on / 依赖: isLimitMapConeBinaryFanEquiv, isLimitOfPreserves
-/
def mapIsLimitOfPreservesOfIsLimit [PreservesLimit (pair X Y) G] (l : IsLimit (BinaryFan.mk f g)) :
    IsLimit (BinaryFan.mk (G.map f) (G.map g)) :=
  isLimitMapConeBinaryFanEquiv G f g (isLimitOfPreserves G l)

/--
Definition of `isLimitOfReflectsOfMapIsLimit` / `isLimitOfReflectsOfMapIsLimit` 的定义

English:
definition isLimitOfReflectsOfMapIsLimit
  signature: [ReflectsLimit (pair X Y) G]
  body: isLimitOfReflects G ((isLimitMapConeBinaryFanEquiv G f g).symm l)

中文:
定义 isLimitOfReflectsOfMapIsLimit
  签名: [反映极限 (pair X Y) G]
  定义体: isLimitOfReflects G ((isLimitMapConeBinaryFanEquiv G f g).symm l)

Depends on / 依赖: isLimitMapConeBinaryFanEquiv, isLimitOfReflects
-/
def isLimitOfReflectsOfMapIsLimit [ReflectsLimit (pair X Y) G]
    (l : IsLimit (BinaryFan.mk (G.map f) (G.map g))) : IsLimit (BinaryFan.mk f g) :=
  isLimitOfReflects G ((isLimitMapConeBinaryFanEquiv G f g).symm l)

variable (X Y)
variable [HasBinaryProduct X Y]

/--
Definition of `isLimitOfHasBinaryProductOfPreservesLimit` / `isLimitOfHasBinaryProductOfPreservesLimit` 的定义

English:
definition isLimitOfHasBinaryProductOfPreservesLimit
  signature: [PreservesLimit (pair X Y) G]
  body: mapIsLimitOfPreservesOfIsLimit G _ _ (prodIsProd X Y)

中文:
定义 isLimitOfHasBinaryProductOfPreservesLimit
  签名: [保持极限 (pair X Y) G]
  定义体: mapIsLimitOfPreservesOfIsLimit G _ _ (prodIsProd X Y)

Depends on / 依赖: mapIsLimitOfPreservesOfIsLimit, prodIsProd
-/
def isLimitOfHasBinaryProductOfPreservesLimit [PreservesLimit (pair X Y) G] :
    IsLimit (BinaryFan.mk (G.map (Limits.prod.fst : X ⨯ Y ⟶ X)) (G.map Limits.prod.snd)) :=
  mapIsLimitOfPreservesOfIsLimit G _ _ (prodIsProd X Y)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PreservesLimit
  signature: (pair X Y) G] :
  body: ⟨_, isLimitOfHasBinaryProductOfPreservesLimit G X Y⟩

中文:
实例 [保持极限
  签名: (pair X Y) G] :
  定义体: ⟨_, isLimitOfHasBinaryProductOfPreservesLimit G X Y⟩

Depends on / 依赖: isLimitOfHasBinaryProductOfPreservesLimit
-/
instance [PreservesLimit (pair X Y) G] :
    HasBinaryProduct (G.obj X) (G.obj Y) :=
  ⟨_, isLimitOfHasBinaryProductOfPreservesLimit G X Y⟩

variable [HasBinaryProduct (G.obj X) (G.obj Y)]

/--
lemma `PreservesLimitPair.of_iso_prod_comparison` / 引理 `PreservesLimitPair.of_iso_prod_comparison`

English:
lemma PreservesLimitPair.of_iso_prod_comparison
  given: [i : IsIso (prodComparison G X Y)]
  proof: by
  apply preservesLimit_of_preserves_limit_cone (prodIsProd X Y)
  apply (isLimitMapConeBinaryFanEquiv _ _ _).symm _
  refine @IsLimit.ofPointIso _ _ _ _ _ _ _ (limit.isLimit (pair (G.obj X) (G.obj Y))) ?_
  apply i

中文:
引理 PreservesLimitPair.of_iso_prod_comparison
  条件: [i : 是同构 (prodComparison G X Y)]
  证明: by
  apply preservesLimit_of_preserves_limit_cone (prodIsProd X Y)
  apply (isLimitMapConeBinaryFanEquiv _ _ _).symm _
  refine @IsLimit.ofPointIso _ _ _ _ _ _ _ (limit.isLimit (pair (G.obj X) (G.obj Y))) ?_
  apply i

Depends on / 依赖: G.obj, IsLimit, IsLimit.ofPointIso, isLimit, isLimitMapConeBinaryFanEquiv, limit.isLimit, ofPointIso, preservesLimit_of_preserves_limit_cone, prodIsProd
-/
lemma PreservesLimitPair.of_iso_prod_comparison [i : IsIso (prodComparison G X Y)] :
    PreservesLimit (pair X Y) G := by
  apply preservesLimit_of_preserves_limit_cone (prodIsProd X Y)
  apply (isLimitMapConeBinaryFanEquiv _ _ _).symm _
  refine @IsLimit.ofPointIso _ _ _ _ _ _ _ (limit.isLimit (pair (G.obj X) (G.obj Y))) ?_
  apply i

variable [PreservesLimit (pair X Y) G]

/--
Definition of `PreservesLimitPair.iso` / `PreservesLimitPair.iso` 的定义

English:
definition PreservesLimitPair.iso
  signature: : G.obj (X ⨯ Y) ≅ G.obj X ⨯ G.obj Y
  body: IsLimit.conePointUniqueUpToIso (isLimitOfHasBinaryProductOfPreservesLimit G X Y) (limit.isLimit _)

@[simp]

中文:
定义 PreservesLimitPair.iso
  签名: : G.obj (X ⨯ Y) ≅ G.obj X ⨯ G.obj Y
  定义体: IsLimit.conePointUniqueUpToIso (isLimitOfHasBinaryProductOfPreservesLimit G X Y) (limit.isLimit _)

@[simp]

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso, conePointUniqueUpToIso, isLimit, isLimitOfHasBinaryProductOfPreservesLimit, limit.isLimit
-/
def PreservesLimitPair.iso : G.obj (X ⨯ Y) ≅ G.obj X ⨯ G.obj Y :=
  IsLimit.conePointUniqueUpToIso (isLimitOfHasBinaryProductOfPreservesLimit G X Y) (limit.isLimit _)

@[simp]
/--
theorem `PreservesLimitPair.iso_hom` / 定理 `PreservesLimitPair.iso_hom`

English:
theorem PreservesLimitPair.iso_hom
  statement: (PreservesLimitPair.iso G X Y).hom = prodComparison G X Y
  proof: rfl

@[simp, reassoc]

中文:
定理 PreservesLimitPair.iso_hom
  结论: (PreservesLimitPair.iso G X Y).hom = prodComparison G X Y
  证明: rfl

@[simp, reassoc]
-/
theorem PreservesLimitPair.iso_hom : (PreservesLimitPair.iso G X Y).hom = prodComparison G X Y :=
  rfl

@[simp, reassoc]
/--
theorem `PreservesLimitPair.iso_inv_fst` / 定理 `PreservesLimitPair.iso_inv_fst`

English:
theorem PreservesLimitPair.iso_inv_fst
  proof: by
  rw [← Iso.cancel_iso_hom_left (PreservesLimitPair.iso G X Y)]; rw [← Category.assoc]; rw [Iso.hom_inv_id]
  simp

@[simp, reassoc]

中文:
定理 PreservesLimitPair.iso_inv_fst
  证明: by
  rw [← Iso.cancel_iso_hom_left (PreservesLimitPair.iso G X Y)]; rw [← Category.assoc]; rw [Iso.hom_inv_id]
  simp

@[simp, reassoc]

Depends on / 依赖: Category, Category.assoc, Iso.cancel_iso_hom_left, Iso.hom_inv_id, PreservesLimitPair, PreservesLimitPair.iso, cancel_iso_hom_left, hom_inv_id
-/
theorem PreservesLimitPair.iso_inv_fst :
    (PreservesLimitPair.iso G X Y).inv ≫ G.map prod.fst = prod.fst := by
  rw [← Iso.cancel_iso_hom_left (PreservesLimitPair.iso G X Y)]; rw [← Category.assoc]; rw [Iso.hom_inv_id]
  simp

@[simp, reassoc]
/--
theorem `PreservesLimitPair.iso_inv_snd` / 定理 `PreservesLimitPair.iso_inv_snd`

English:
theorem PreservesLimitPair.iso_inv_snd
  proof: by
  rw [← Iso.cancel_iso_hom_left (PreservesLimitPair.iso G X Y)]; rw [← Category.assoc]; rw [Iso.hom_inv_id]
  simp

中文:
定理 PreservesLimitPair.iso_inv_snd
  证明: by
  rw [← Iso.cancel_iso_hom_left (PreservesLimitPair.iso G X Y)]; rw [← Category.assoc]; rw [Iso.hom_inv_id]
  simp

Depends on / 依赖: Category, Category.assoc, Iso.cancel_iso_hom_left, Iso.hom_inv_id, PreservesLimitPair, PreservesLimitPair.iso, cancel_iso_hom_left, hom_inv_id
-/
theorem PreservesLimitPair.iso_inv_snd :
    (PreservesLimitPair.iso G X Y).inv ≫ G.map prod.snd = prod.snd := by
  rw [← Iso.cancel_iso_hom_left (PreservesLimitPair.iso G X Y)]; rw [← Category.assoc]; rw [Iso.hom_inv_id]
  simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (prodComparison G X Y)
  body: by
  rw [← PreservesLimitPair.iso_hom]
  infer_instance

中文:
实例 :
  签名: 是同构 (prodComparison G X Y)
  定义体: by
  rw [← PreservesLimitPair.iso_hom]
  infer_instance

Depends on / 依赖: PreservesLimitPair, PreservesLimitPair.iso_hom, infer_instance, iso_hom
-/
instance : IsIso (prodComparison G X Y) := by
  rw [← PreservesLimitPair.iso_hom]
  infer_instance

/--
lemma `preservesBinaryProducts_of_isIso_prodComparison` / 引理 `preservesBinaryProducts_of_isIso_prodComparison`

English:
lemma preservesBinaryProducts_of_isIso_prodComparison
  proof: by
    intro K
    have : PreservesLimit (pair (K.obj ⟨WalkingPair.left⟩) (K.obj ⟨WalkingPair.right⟩)) G :=
      PreservesLimitPair.of_iso_prod_comparison ..
    apply preservesLimit_of_iso_diagram G (diagramIsoPair K).symm

中文:
引理 preservesBinaryProducts_of_isIso_prodComparison
  证明: by
    intro K
    have : PreservesLimit (pair (K.obj ⟨WalkingPair.left⟩) (K.obj ⟨WalkingPair.right⟩)) G :=
      PreservesLimitPair.of_iso_prod_comparison ..
    apply preservesLimit_of_iso_diagram G (diagramIsoPair K).symm

Depends on / 依赖: K.obj, PreservesLimit, PreservesLimitPair, PreservesLimitPair.of_iso_prod_comparison, WalkingPair, WalkingPair.left, WalkingPair.right, diagramIsoPair, of_iso_prod_comparison, preservesLimit_of_iso_diagram
-/
lemma preservesBinaryProducts_of_isIso_prodComparison
    [HasBinaryProducts C] [HasBinaryProducts D]
    [i : forall {X Y : C}, IsIso (prodComparison G X Y)] :
    PreservesLimitsOfShape (Discrete WalkingPair) G where
  preservesLimit := by
    intro K
    have : PreservesLimit (pair (K.obj ⟨WalkingPair.left⟩) (K.obj ⟨WalkingPair.right⟩)) G :=
      PreservesLimitPair.of_iso_prod_comparison ..
    apply preservesLimit_of_iso_diagram G (diagramIsoPair K).symm

end

section

variable {P X Y Z : C} (f : X ⟶ P) (g : Y ⟶ P)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isColimitMapCoconeBinaryCofanEquiv` / `isColimitMapCoconeBinaryCofanEquiv` 的定义

English:
definition isColimitMapCoconeBinaryCofanEquiv
  signature: :
  body: (IsColimit.precomposeHomEquiv (diagramIsoPair _).symm _).symm.trans
    (IsColimit.equivIsoColimit
      (Cocone.ext (Iso.refl _)
        (by rintro (_ | _) <;> simp)))

中文:
定义 isColimitMapCoconeBinaryCofanEquiv
  签名: :
  定义体: (IsColimit.precomposeHomEquiv (diagramIsoPair _).symm _).symm.trans
    (IsColimit.equivIsoColimit
      (Cocone.ext (Iso.refl _)
        (by rintro (_ | _) <;> simp)))

Depends on / 依赖: Cocone, Cocone.ext, IsColimit, IsColimit.equivIsoColimit, IsColimit.precomposeHomEquiv, Iso.refl, diagramIsoPair, equivIsoColimit, precomposeHomEquiv, symm.trans
-/
def isColimitMapCoconeBinaryCofanEquiv :
    IsColimit (Functor.mapCocone G (BinaryCofan.mk f g))
    ≃ IsColimit (BinaryCofan.mk (G.map f) (G.map g)) :=
  (IsColimit.precomposeHomEquiv (diagramIsoPair _).symm _).symm.trans
    (IsColimit.equivIsoColimit
      (Cocone.ext (Iso.refl _)
        (by rintro (_ | _) <;> simp)))

/--
Definition of `mapIsColimitOfPreservesOfIsColimit` / `mapIsColimitOfPreservesOfIsColimit` 的定义

English:
definition mapIsColimitOfPreservesOfIsColimit
  signature: [PreservesColimit (pair X Y) G]
  body: isColimitMapCoconeBinaryCofanEquiv G f g (isColimitOfPreserves G l)

中文:
定义 mapIsColimitOfPreservesOfIsColimit
  签名: [保持余极限 (pair X Y) G]
  定义体: isColimitMapCoconeBinaryCofanEquiv G f g (isColimitOfPreserves G l)

Depends on / 依赖: isColimitMapCoconeBinaryCofanEquiv, isColimitOfPreserves
-/
def mapIsColimitOfPreservesOfIsColimit [PreservesColimit (pair X Y) G]
    (l : IsColimit (BinaryCofan.mk f g)) : IsColimit (BinaryCofan.mk (G.map f) (G.map g)) :=
  isColimitMapCoconeBinaryCofanEquiv G f g (isColimitOfPreserves G l)

/--
Definition of `isColimitOfReflectsOfMapIsColimit` / `isColimitOfReflectsOfMapIsColimit` 的定义

English:
definition isColimitOfReflectsOfMapIsColimit
  signature: [ReflectsColimit (pair X Y) G]
  body: isColimitOfReflects G ((isColimitMapCoconeBinaryCofanEquiv G f g).symm l)

中文:
定义 isColimitOfReflectsOfMapIsColimit
  签名: [反映余极限 (pair X Y) G]
  定义体: isColimitOfReflects G ((isColimitMapCoconeBinaryCofanEquiv G f g).symm l)

Depends on / 依赖: isColimitMapCoconeBinaryCofanEquiv, isColimitOfReflects
-/
def isColimitOfReflectsOfMapIsColimit [ReflectsColimit (pair X Y) G]
    (l : IsColimit (BinaryCofan.mk (G.map f) (G.map g))) : IsColimit (BinaryCofan.mk f g) :=
  isColimitOfReflects G ((isColimitMapCoconeBinaryCofanEquiv G f g).symm l)

variable (X Y)
variable [HasBinaryCoproduct X Y]

/--
Definition of `isColimitOfHasBinaryCoproductOfPreservesColimit` / `isColimitOfHasBinaryCoproductOfPreservesColimit` 的定义

English:
definition isColimitOfHasBinaryCoproductOfPreservesColimit
  signature: [PreservesColimit (pair X Y) G]
  body: mapIsColimitOfPreservesOfIsColimit G _ _ (coprodIsCoprod X Y)

中文:
定义 isColimitOfHasBinaryCoproductOfPreservesColimit
  签名: [保持余极限 (pair X Y) G]
  定义体: mapIsColimitOfPreservesOfIsColimit G _ _ (coprodIsCoprod X Y)

Depends on / 依赖: coprodIsCoprod, mapIsColimitOfPreservesOfIsColimit
-/
def isColimitOfHasBinaryCoproductOfPreservesColimit [PreservesColimit (pair X Y) G] :
    IsColimit (BinaryCofan.mk (G.map (Limits.coprod.inl : X ⟶ X ⨿ Y)) (G.map Limits.coprod.inr)) :=
  mapIsColimitOfPreservesOfIsColimit G _ _ (coprodIsCoprod X Y)

variable [HasBinaryCoproduct (G.obj X) (G.obj Y)]

/--
lemma `PreservesColimitPair.of_iso_coprod_comparison` / 引理 `PreservesColimitPair.of_iso_coprod_comparison`

English:
lemma PreservesColimitPair.of_iso_coprod_comparison
  given: [i : IsIso (coprodComparison G X Y)]
  proof: by
  apply preservesColimit_of_preserves_colimit_cocone (coprodIsCoprod X Y)
  apply (isColimitMapCoconeBinaryCofanEquiv _ _ _).symm _
  refine @IsColimit.ofPointIso _ _ _ _ _ _ _ (colimit.isColimit (pair (G.obj X) (G.obj Y))) ?_
  apply i

中文:
引理 PreservesColimitPair.of_iso_coprod_comparison
  条件: [i : 是同构 (coprodComparison G X Y)]
  证明: by
  apply preservesColimit_of_preserves_colimit_cocone (coprodIsCoprod X Y)
  apply (isColimitMapCoconeBinaryCofanEquiv _ _ _).symm _
  refine @IsColimit.ofPointIso _ _ _ _ _ _ _ (colimit.isColimit (pair (G.obj X) (G.obj Y))) ?_
  apply i

Depends on / 依赖: G.obj, IsColimit, IsColimit.ofPointIso, colimit, colimit.isColimit, coprodIsCoprod, isColimit, isColimitMapCoconeBinaryCofanEquiv, ofPointIso, preservesColimit_of_preserves_colimit_cocone
-/
lemma PreservesColimitPair.of_iso_coprod_comparison [i : IsIso (coprodComparison G X Y)] :
    PreservesColimit (pair X Y) G := by
  apply preservesColimit_of_preserves_colimit_cocone (coprodIsCoprod X Y)
  apply (isColimitMapCoconeBinaryCofanEquiv _ _ _).symm _
  refine @IsColimit.ofPointIso _ _ _ _ _ _ _ (colimit.isColimit (pair (G.obj X) (G.obj Y))) ?_
  apply i

variable [PreservesColimit (pair X Y) G]

/--
Definition of `PreservesColimitPair.iso` / `PreservesColimitPair.iso` 的定义

English:
definition PreservesColimitPair.iso
  signature: : G.obj X ⨿ G.obj Y ≅ G.obj (X ⨿ Y)
  body: IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (isColimitOfHasBinaryCoproductOfPreservesColimit G X Y)

@[simp]

中文:
定义 PreservesColimitPair.iso
  签名: : G.obj X ⨿ G.obj Y ≅ G.obj (X ⨿ Y)
  定义体: IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (isColimitOfHasBinaryCoproductOfPreservesColimit G X Y)

@[simp]

Depends on / 依赖: IsColimit, IsColimit.coconePointUniqueUpToIso, coconePointUniqueUpToIso, colimit, colimit.isColimit, isColimit, isColimitOfHasBinaryCoproductOfPreservesColimit
-/
def PreservesColimitPair.iso : G.obj X ⨿ G.obj Y ≅ G.obj (X ⨿ Y) :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (isColimitOfHasBinaryCoproductOfPreservesColimit G X Y)

@[simp]
/--
theorem `PreservesColimitPair.iso_hom` / 定理 `PreservesColimitPair.iso_hom`

English:
theorem PreservesColimitPair.iso_hom
  proof: rfl

中文:
定理 PreservesColimitPair.iso_hom
  证明: rfl
-/
theorem PreservesColimitPair.iso_hom :
    (PreservesColimitPair.iso G X Y).hom = coprodComparison G X Y := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (coprodComparison G X Y)
  body: by
  rw [← PreservesColimitPair.iso_hom]
  infer_instance

中文:
实例 :
  签名: 是同构 (coprodComparison G X Y)
  定义体: by
  rw [← PreservesColimitPair.iso_hom]
  infer_instance

Depends on / 依赖: PreservesColimitPair, PreservesColimitPair.iso_hom, infer_instance, iso_hom
-/
instance : IsIso (coprodComparison G X Y) := by
  rw [← PreservesColimitPair.iso_hom]
  infer_instance

/--
lemma `preservesBinaryCoproducts_of_isIso_coprodComparison` / 引理 `preservesBinaryCoproducts_of_isIso_coprodComparison`

English:
lemma preservesBinaryCoproducts_of_isIso_coprodComparison
  proof: by
    intro K
    have : PreservesColimit (pair (K.obj ⟨WalkingPair.left⟩) (K.obj ⟨WalkingPair.right⟩)) G :=
      PreservesColimitPair.of_iso_coprod_comparison ..
    apply preservesColimit_of_iso_diagram G (diagramIsoPair K).symm

中文:
引理 preservesBinaryCoproducts_of_isIso_coprodComparison
  证明: by
    intro K
    have : PreservesColimit (pair (K.obj ⟨WalkingPair.left⟩) (K.obj ⟨WalkingPair.right⟩)) G :=
      PreservesColimitPair.of_iso_coprod_comparison ..
    apply preservesColimit_of_iso_diagram G (diagramIsoPair K).symm

Depends on / 依赖: K.obj, PreservesColimit, PreservesColimitPair, PreservesColimitPair.of_iso_coprod_comparison, WalkingPair, WalkingPair.left, WalkingPair.right, diagramIsoPair, of_iso_coprod_comparison, preservesColimit_of_iso_diagram
-/
lemma preservesBinaryCoproducts_of_isIso_coprodComparison
    [HasBinaryCoproducts C] [HasBinaryCoproducts D]
    [i : forall {X Y : C}, IsIso (coprodComparison G X Y)] :
    PreservesColimitsOfShape (Discrete WalkingPair) G where
  preservesColimit := by
    intro K
    have : PreservesColimit (pair (K.obj ⟨WalkingPair.left⟩) (K.obj ⟨WalkingPair.right⟩)) G :=
      PreservesColimitPair.of_iso_coprod_comparison ..
    apply preservesColimit_of_iso_diagram G (diagramIsoPair K).symm

end

end CategoryTheory.Limits
