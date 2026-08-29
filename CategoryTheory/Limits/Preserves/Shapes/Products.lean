/-
Copyright (c) 2020 Kim Morrison, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Preserving products

Constructions to relate the notions of preserving products and reflecting products
to concrete fans.

In particular, we show that `piComparison G f` is an isomorphism iff `G` preserves
the limit of `f`.
-/

@[expose] public section


noncomputable section

universe w v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (G : C ⥤ D)

namespace CategoryTheory.Limits

variable {J : Type w} (f : J -> C)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isLimitMapConeFanMkEquiv` / `isLimitMapConeFanMkEquiv` 的定义

English:
definition isLimitMapConeFanMkEquiv
  signature: {P : C} (g : forall j, P ⟶ f j)
  body: by
  refine (IsLimit.postcomposeHomEquiv ?_ _).symm.trans (IsLimit.equivIsoLimit ?_)
  · exact Discrete.natIso fun j => Iso.refl (G.obj (f j.as))
  exact Cone.ext (Iso.refl _) fun j => by dsimp; cases j; simp

中文:
定义 isLimitMapConeFanMkEquiv
  签名: {P : C} (g : 对任意 j, P ⟶ f j)
  定义体: by
  refine (IsLimit.postcomposeHomEquiv ?_ _).symm.trans (IsLimit.equivIsoLimit ?_)
  · exact Discrete.natIso fun j => Iso.refl (G.obj (f j.as))
  exact Cone.ext (Iso.refl _) fun j => by dsimp; cases j; simp

Depends on / 依赖: Cone.ext, Discrete, Discrete.natIso, G.obj, IsLimit, IsLimit.equivIsoLimit, IsLimit.postcomposeHomEquiv, Iso.refl, equivIsoLimit, j.as, natIso, postcomposeHomEquiv, symm.trans
-/
def isLimitMapConeFanMkEquiv {P : C} (g : forall j, P ⟶ f j) :
    IsLimit (Functor.mapCone G (Fan.mk P g)) ≃
      IsLimit (Fan.mk _ fun j => G.map (g j) : Fan fun j => G.obj (f j)) := by
  refine (IsLimit.postcomposeHomEquiv ?_ _).symm.trans (IsLimit.equivIsoLimit ?_)
  · exact Discrete.natIso fun j => Iso.refl (G.obj (f j.as))
  exact Cone.ext (Iso.refl _) fun j => by dsimp; cases j; simp

/--
Definition of `isLimitFanMkObjOfIsLimit` / `isLimitFanMkObjOfIsLimit` 的定义

English:
definition isLimitFanMkObjOfIsLimit
  signature: [PreservesLimit (Discrete.functor f) G] {P : C} (g : forall j, P ⟶ f j)
  body: isLimitMapConeFanMkEquiv _ _ _ (isLimitOfPreserves G t)

中文:
定义 isLimitFanMkObjOfIsLimit
  签名: [PreservesLimit (Discrete.functor f) G] {P : C} (g : 对任意 j, P ⟶ f j)
  定义体: isLimitMapConeFanMkEquiv _ _ _ (isLimitOfPreserves G t)

Depends on / 依赖: isLimitMapConeFanMkEquiv, isLimitOfPreserves
-/
def isLimitFanMkObjOfIsLimit [PreservesLimit (Discrete.functor f) G] {P : C} (g : forall j, P ⟶ f j)
    (t : IsLimit (Fan.mk _ g)) :
    IsLimit (Fan.mk (G.obj P) fun j => G.map (g j) : Fan fun j => G.obj (f j)) :=
  isLimitMapConeFanMkEquiv _ _ _ (isLimitOfPreserves G t)

/--
Definition of `isLimitOfIsLimitFanMkObj` / `isLimitOfIsLimitFanMkObj` 的定义

English:
definition isLimitOfIsLimitFanMkObj
  signature: [ReflectsLimit (Discrete.functor f) G] {P : C} (g : forall j, P ⟶ f j)
  body: isLimitOfReflects G ((isLimitMapConeFanMkEquiv _ _ _).symm t)

中文:
定义 isLimitOfIsLimitFanMkObj
  签名: [ReflectsLimit (Discrete.functor f) G] {P : C} (g : 对任意 j, P ⟶ f j)
  定义体: isLimitOfReflects G ((isLimitMapConeFanMkEquiv _ _ _).symm t)

Depends on / 依赖: isLimitMapConeFanMkEquiv, isLimitOfReflects
-/
def isLimitOfIsLimitFanMkObj [ReflectsLimit (Discrete.functor f) G] {P : C} (g : forall j, P ⟶ f j)
    (t : IsLimit (Fan.mk _ fun j => G.map (g j) : Fan fun j => G.obj (f j))) :
    IsLimit (Fan.mk P g) :=
  isLimitOfReflects G ((isLimitMapConeFanMkEquiv _ _ _).symm t)

section

variable [HasProduct f]

/--
Definition of `isLimitOfHasProductOfPreservesLimit` / `isLimitOfHasProductOfPreservesLimit` 的定义

English:
definition isLimitOfHasProductOfPreservesLimit
  signature: [PreservesLimit (Discrete.functor f) G]
  body: isLimitFanMkObjOfIsLimit G f _ (productIsProduct _)

中文:
定义 isLimitOfHasProductOfPreservesLimit
  签名: [PreservesLimit (Discrete.functor f) G]
  定义体: isLimitFanMkObjOfIsLimit G f _ (productIsProduct _)

Depends on / 依赖: isLimitFanMkObjOfIsLimit, productIsProduct
-/
def isLimitOfHasProductOfPreservesLimit [PreservesLimit (Discrete.functor f) G] :
    IsLimit (Fan.mk _ fun j : J => G.map (Pi.π f j) : Fan fun j => G.obj (f j)) :=
  isLimitFanMkObjOfIsLimit G f _ (productIsProduct _)

variable [HasProduct fun j : J => G.obj (f j)]

/--
lemma `PreservesProduct.of_iso_comparison` / 引理 `PreservesProduct.of_iso_comparison`

English:
lemma PreservesProduct.of_iso_comparison
  given: [i : IsIso (piComparison G f)]
  proof: by
  apply preservesLimit_of_preserves_limit_cone (productIsProduct f)
  apply (isLimitMapConeFanMkEquiv _ _ _).symm _
  exact @IsLimit.ofPointIso _ _ _ _ _ _ _
    (limit.isLimit (Discrete.functor fun j : J => G.obj (f j))) i

@[reassoc (attr := simp)]

中文:
引理 PreservesProduct.of_iso_comparison
  条件: [i : IsIso (piComparison G f)]
  证明: by
  apply preservesLimit_of_preserves_limit_cone (productIsProduct f)
  apply (isLimitMapConeFanMkEquiv _ _ _).symm _
  exact @IsLimit.ofPointIso _ _ _ _ _ _ _
    (limit.isLimit (Discrete.functor fun j : J => G.obj (f j))) i

@[reassoc (attr := simp)]

Depends on / 依赖: Discrete, Discrete.functor, G.obj, IsLimit, IsLimit.ofPointIso, functor, isLimit, isLimitMapConeFanMkEquiv, limit.isLimit, ofPointIso, preservesLimit_of_preserves_limit_cone, productIsProduct
-/
lemma PreservesProduct.of_iso_comparison [i : IsIso (piComparison G f)] :
    PreservesLimit (Discrete.functor f) G := by
  apply preservesLimit_of_preserves_limit_cone (productIsProduct f)
  apply (isLimitMapConeFanMkEquiv _ _ _).symm _
  exact @IsLimit.ofPointIso _ _ _ _ _ _ _
    (limit.isLimit (Discrete.functor fun j : J => G.obj (f j))) i

@[reassoc (attr := simp)]
/--
lemma `inv_piComparison_comp_map_π` / 引理 `inv_piComparison_comp_map_π`

English:
lemma inv_piComparison_comp_map_π
  given: [IsIso (piComparison G f)] (j : J)
  proof: by
  simp only [IsIso.inv_comp_eq, piComparison_comp_π]

中文:
引理 inv_piComparison_comp_map_π
  条件: [IsIso (piComparison G f)] (j : J)
  证明: by
  simp only [IsIso.inv_comp_eq, piComparison_comp_π]

Depends on / 依赖: IsIso.inv_comp_eq, inv_comp_eq
-/
lemma inv_piComparison_comp_map_π [IsIso (piComparison G f)] (j : J) :
     inv (piComparison G f) ≫ G.map (Pi.π _ j) =
      Pi.π (fun x => (G.obj (f x))) j := by
  simp only [IsIso.inv_comp_eq, piComparison_comp_π]

variable [PreservesLimit (Discrete.functor f) G]

/--
Definition of `PreservesProduct.iso` / `PreservesProduct.iso` 的定义

English:
definition PreservesProduct.iso
  signature: : G.obj (∏ᶜ f) ≅ ∏ᶜ fun j => G.obj (f j)
  body: IsLimit.conePointUniqueUpToIso (isLimitOfHasProductOfPreservesLimit G f) (limit.isLimit _)

@[simp]

中文:
定义 PreservesProduct.iso
  签名: : G.obj (∏ᶜ f) ≅ ∏ᶜ fun j => G.obj (f j)
  定义体: IsLimit.conePointUniqueUpToIso (isLimitOfHasProductOfPreservesLimit G f) (limit.isLimit _)

@[simp]

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso, conePointUniqueUpToIso, isLimit, isLimitOfHasProductOfPreservesLimit, limit.isLimit
-/
def PreservesProduct.iso : G.obj (∏ᶜ f) ≅ ∏ᶜ fun j => G.obj (f j) :=
  IsLimit.conePointUniqueUpToIso (isLimitOfHasProductOfPreservesLimit G f) (limit.isLimit _)

@[simp]
/--
theorem `PreservesProduct.iso_hom` / 定理 `PreservesProduct.iso_hom`

English:
theorem PreservesProduct.iso_hom
  statement: (PreservesProduct.iso G f).hom = piComparison G f
  proof: rfl

中文:
定理 PreservesProduct.iso_hom
  结论: (PreservesProduct.iso G f).hom = piComparison G f
  证明: rfl

Depends on / 依赖: IsComonHom, f.hom
-/
theorem PreservesProduct.iso_hom : (PreservesProduct.iso G f).hom = piComparison G f :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (piComparison G f)
  body: by
  rw [← PreservesProduct.iso_hom]
  infer_instance

中文:
实例 :
  签名: IsIso (piComparison G f)
  定义体: by
  rw [← PreservesProduct.iso_hom]
  infer_instance

Depends on / 依赖: PreservesProduct, PreservesProduct.iso_hom, infer_instance, iso_hom
-/
instance : IsIso (piComparison G f) := by
  rw [← PreservesProduct.iso_hom]
  infer_instance

instance {I : Type*} [Category* I] [IsGroupoid I] (F : C ⥤ D) [PreservesLimitsOfShape I F] :
    PreservesLimitsOfShape Iᵒᵖ F :=
  letI : Groupoid I := Groupoid.ofIsGroupoid
  preservesLimitsOfShape_of_equiv (Groupoid.invEquivalence I) F

end

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isColimitMapCoconeCofanMkEquiv` / `isColimitMapCoconeCofanMkEquiv` 的定义

English:
definition isColimitMapCoconeCofanMkEquiv
  signature: {P : C} (g : forall j, f j ⟶ P)
  body: by
  refine (IsColimit.precomposeHomEquiv ?_ _).symm.trans (IsColimit.equivIsoColimit ?_)
  · refine Discrete.natIso fun j => Iso.refl (G.obj (f j.as))
  refine Cocone.ext (Iso.refl _) fun j => by dsimp; cases j; simp

中文:
定义 isColimitMapCoconeCofanMkEquiv
  签名: {P : C} (g : 对任意 j, f j ⟶ P)
  定义体: by
  refine (IsColimit.precomposeHomEquiv ?_ _).symm.trans (IsColimit.equivIsoColimit ?_)
  · refine Discrete.natIso fun j => Iso.refl (G.obj (f j.as))
  refine Cocone.ext (Iso.refl _) fun j => by dsimp; cases j; simp

Depends on / 依赖: Cocone, Cocone.ext, Discrete, Discrete.natIso, G.obj, IsColimit, IsColimit.equivIsoColimit, IsColimit.precomposeHomEquiv, Iso.refl, equivIsoColimit, j.as, natIso, precomposeHomEquiv, symm.trans
-/
def isColimitMapCoconeCofanMkEquiv {P : C} (g : forall j, f j ⟶ P) :
    IsColimit (Functor.mapCocone G (Cofan.mk P g)) ≃
      IsColimit (Cofan.mk _ fun j => G.map (g j) : Cofan fun j => G.obj (f j)) := by
  refine (IsColimit.precomposeHomEquiv ?_ _).symm.trans (IsColimit.equivIsoColimit ?_)
  · refine Discrete.natIso fun j => Iso.refl (G.obj (f j.as))
  refine Cocone.ext (Iso.refl _) fun j => by dsimp; cases j; simp

/--
Definition of `isColimitCofanMkObjOfIsColimit` / `isColimitCofanMkObjOfIsColimit` 的定义

English:
definition isColimitCofanMkObjOfIsColimit
  signature: [PreservesColimit (Discrete.functor f) G] {P : C}
  body: isColimitMapCoconeCofanMkEquiv _ _ _ (isColimitOfPreserves G t)

中文:
定义 isColimitCofanMkObjOfIsColimit
  签名: [PreservesColimit (Discrete.functor f) G] {P : C}
  定义体: isColimitMapCoconeCofanMkEquiv _ _ _ (isColimitOfPreserves G t)

Depends on / 依赖: isColimitMapCoconeCofanMkEquiv, isColimitOfPreserves
-/
def isColimitCofanMkObjOfIsColimit [PreservesColimit (Discrete.functor f) G] {P : C}
    (g : forall j, f j ⟶ P) (t : IsColimit (Cofan.mk _ g)) :
    IsColimit (Cofan.mk (G.obj P) fun j => G.map (g j) : Cofan fun j => G.obj (f j)) :=
  isColimitMapCoconeCofanMkEquiv _ _ _ (isColimitOfPreserves G t)

/--
Definition of `isColimitOfIsColimitCofanMkObj` / `isColimitOfIsColimitCofanMkObj` 的定义

English:
definition isColimitOfIsColimitCofanMkObj
  signature: [ReflectsColimit (Discrete.functor f) G] {P : C}
  body: isColimitOfReflects G ((isColimitMapCoconeCofanMkEquiv _ _ _).symm t)

中文:
定义 isColimitOfIsColimitCofanMkObj
  签名: [ReflectsColimit (Discrete.functor f) G] {P : C}
  定义体: isColimitOfReflects G ((isColimitMapCoconeCofanMkEquiv _ _ _).symm t)

Depends on / 依赖: isColimitMapCoconeCofanMkEquiv, isColimitOfReflects
-/
def isColimitOfIsColimitCofanMkObj [ReflectsColimit (Discrete.functor f) G] {P : C}
    (g : forall j, f j ⟶ P)
    (t : IsColimit (Cofan.mk _ fun j => G.map (g j) : Cofan fun j => G.obj (f j))) :
    IsColimit (Cofan.mk P g) :=
  isColimitOfReflects G ((isColimitMapCoconeCofanMkEquiv _ _ _).symm t)

section

variable [HasCoproduct f]

/--
Definition of `isColimitOfHasCoproductOfPreservesColimit` / `isColimitOfHasCoproductOfPreservesColimit` 的定义

English:
definition isColimitOfHasCoproductOfPreservesColimit
  signature: [PreservesColimit (Discrete.functor f) G]
  body: isColimitCofanMkObjOfIsColimit G f _ (coproductIsCoproduct _)

中文:
定义 isColimitOfHasCoproductOfPreservesColimit
  签名: [PreservesColimit (Discrete.functor f) G]
  定义体: isColimitCofanMkObjOfIsColimit G f _ (coproductIsCoproduct _)

Depends on / 依赖: coproductIsCoproduct, isColimitCofanMkObjOfIsColimit
-/
def isColimitOfHasCoproductOfPreservesColimit [PreservesColimit (Discrete.functor f) G] :
    IsColimit (Cofan.mk _ fun j : J => G.map (Sigma.ι f j) : Cofan fun j => G.obj (f j)) :=
  isColimitCofanMkObjOfIsColimit G f _ (coproductIsCoproduct _)

variable [HasCoproduct fun j : J => G.obj (f j)]

/--
lemma `PreservesCoproduct.of_iso_comparison` / 引理 `PreservesCoproduct.of_iso_comparison`

English:
lemma PreservesCoproduct.of_iso_comparison
  given: [i : IsIso (sigmaComparison G f)]
  proof: by
  apply preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct f)
  apply (isColimitMapCoconeCofanMkEquiv _ _ _).symm _
  exact @IsColimit.ofPointIso _ _ _ _ _ _ _
    (colimit.isColimit (Discrete.functor fun j : J => G.obj (f j))) i

@[reassoc (attr := simp)]

中文:
引理 PreservesCoproduct.of_iso_comparison
  条件: [i : IsIso (sigmaComparison G f)]
  证明: by
  apply preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct f)
  apply (isColimitMapCoconeCofanMkEquiv _ _ _).symm _
  exact @IsColimit.ofPointIso _ _ _ _ _ _ _
    (colimit.isColimit (Discrete.functor fun j : J => G.obj (f j))) i

@[reassoc (attr := simp)]

Depends on / 依赖: Discrete, Discrete.functor, G.obj, IsColimit, IsColimit.ofPointIso, colimit, colimit.isColimit, coproductIsCoproduct, functor, isColimit, isColimitMapCoconeCofanMkEquiv, ofPointIso, preservesColimit_of_preserves_colimit_cocone
-/
lemma PreservesCoproduct.of_iso_comparison [i : IsIso (sigmaComparison G f)] :
    PreservesColimit (Discrete.functor f) G := by
  apply preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct f)
  apply (isColimitMapCoconeCofanMkEquiv _ _ _).symm _
  exact @IsColimit.ofPointIso _ _ _ _ _ _ _
    (colimit.isColimit (Discrete.functor fun j : J => G.obj (f j))) i

@[reassoc (attr := simp)]
/--
lemma `map_ι_comp_inv_sigmaComparison` / 引理 `map_ι_comp_inv_sigmaComparison`

English:
lemma map_ι_comp_inv_sigmaComparison
  given: [IsIso (sigmaComparison G f)] (j : J)
  proof: by
  simp

中文:
引理 map_ι_comp_inv_sigmaComparison
  条件: [IsIso (sigmaComparison G f)] (j : J)
  证明: by
  simp
-/
lemma map_ι_comp_inv_sigmaComparison [IsIso (sigmaComparison G f)] (j : J) :
    G.map (Sigma.ι _ j) ≫ inv (sigmaComparison G f) =
      Sigma.ι (fun x => (G.obj (f x))) j := by
  simp

variable [PreservesColimit (Discrete.functor f) G]

/--
Definition of `PreservesCoproduct.iso` / `PreservesCoproduct.iso` 的定义

English:
definition PreservesCoproduct.iso
  signature: : G.obj (∐ f) ≅ ∐ fun j => G.obj (f j)
  body: IsColimit.coconePointUniqueUpToIso (isColimitOfHasCoproductOfPreservesColimit G f)
    (colimit.isColimit _)

@[simp]

中文:
定义 PreservesCoproduct.iso
  签名: : G.obj (∐ f) ≅ ∐ fun j => G.obj (f j)
  定义体: IsColimit.coconePointUniqueUpToIso (isColimitOfHasCoproductOfPreservesColimit G f)
    (colimit.isColimit _)

@[simp]

Depends on / 依赖: IsColimit, IsColimit.coconePointUniqueUpToIso, coconePointUniqueUpToIso, colimit, colimit.isColimit, isColimit, isColimitOfHasCoproductOfPreservesColimit
-/
def PreservesCoproduct.iso : G.obj (∐ f) ≅ ∐ fun j => G.obj (f j) :=
  IsColimit.coconePointUniqueUpToIso (isColimitOfHasCoproductOfPreservesColimit G f)
    (colimit.isColimit _)

@[simp]
/--
theorem `PreservesCoproduct.inv_hom` / 定理 `PreservesCoproduct.inv_hom`

English:
theorem PreservesCoproduct.inv_hom
  statement: (PreservesCoproduct.iso G f).inv = sigmaComparison G f
  proof: rfl

中文:
定理 PreservesCoproduct.inv_hom
  结论: (PreservesCoproduct.iso G f).inv = sigmaComparison G f
  证明: rfl
-/
theorem PreservesCoproduct.inv_hom : (PreservesCoproduct.iso G f).inv = sigmaComparison G f := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsIso (sigmaComparison G f)
  body: by
  rw [← PreservesCoproduct.inv_hom]
  infer_instance

中文:
实例 :
  签名: IsIso (sigmaComparison G f)
  定义体: by
  rw [← PreservesCoproduct.inv_hom]
  infer_instance

Depends on / 依赖: PreservesCoproduct, PreservesCoproduct.inv_hom, infer_instance, inv_hom
-/
instance : IsIso (sigmaComparison G f) := by
  rw [← PreservesCoproduct.inv_hom]
  infer_instance

end

/--
lemma `preservesLimitsOfShape_of_discrete` / 引理 `preservesLimitsOfShape_of_discrete`

English:
lemma preservesLimitsOfShape_of_discrete
  statement: (F : C ⥤ D)
  proof: preservesLimit_of_iso_diagram F (Discrete.natIsoFunctor).symm

中文:
引理 preservesLimitsOfShape_of_discrete
  结论: (F : C ⥤ D)
  证明: preservesLimit_of_iso_diagram F (Discrete.natIsoFunctor).symm

Depends on / 依赖: Discrete, Discrete.natIsoFunctor, natIsoFunctor, preservesLimit_of_iso_diagram
-/
lemma preservesLimitsOfShape_of_discrete (F : C ⥤ D)
    [forall (f : J -> C), PreservesLimit (Discrete.functor f) F] :
    PreservesLimitsOfShape (Discrete J) F where
  preservesLimit := preservesLimit_of_iso_diagram F (Discrete.natIsoFunctor).symm

/--
lemma `preservesColimitsOfShape_of_discrete` / 引理 `preservesColimitsOfShape_of_discrete`

English:
lemma preservesColimitsOfShape_of_discrete
  statement: (F : C ⥤ D)
  proof: preservesColimit_of_iso_diagram F (Discrete.natIsoFunctor).symm

中文:
引理 preservesColimitsOfShape_of_discrete
  结论: (F : C ⥤ D)
  证明: preservesColimit_of_iso_diagram F (Discrete.natIsoFunctor).symm

Depends on / 依赖: Discrete, Discrete.natIsoFunctor, natIsoFunctor, preservesColimit_of_iso_diagram
-/
lemma preservesColimitsOfShape_of_discrete (F : C ⥤ D)
    [forall (f : J -> C), PreservesColimit (Discrete.functor f) F] :
    PreservesColimitsOfShape (Discrete J) F where
  preservesColimit := preservesColimit_of_iso_diagram F (Discrete.natIsoFunctor).symm

instance {I : Type w} (F : C ⥤ D) [PreservesColimitsOfShape (Discrete I) F] :
    PreservesColimitsOfShape (Discrete I)ᵒᵖ F :=
  preservesColimitsOfShape_of_equiv (Discrete.opposite I).symm F

end CategoryTheory.Limits
