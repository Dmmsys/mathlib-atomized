/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Filtered
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products

/-!
# Constructing colimits from finite colimits and filtered colimits

We construct colimits of size `w` from finite colimits and filtered colimits of size `w`. Since
`w`-sized colimits are constructed from coequalizers and `w`-sized coproducts, it suffices to
construct `w`-sized coproducts from finite coproducts and `w`-sized filtered colimits.

The idea is simple: to construct coproducts of shape `α`, we take the colimit of the filtered
diagram of all coproducts of finite subsets of `α`.

We also deduce the dual statement by invoking the original statement in `Cᵒᵖ`.
-/

@[expose] public section


universe w v u

noncomputable section

open CategoryTheory Opposite

variable {C : Type u} [Category.{v} C] {α : Type w}

namespace CategoryTheory.Limits

namespace CoproductsFromFiniteFiltered

variable [HasFiniteCoproducts C]

set_option backward.isDefEq.respectTransparency false in
/-- If `C` has finite coproducts, a functor `Discrete α ⥤ C` lifts to a functor
`Finset (Discrete α) ⥤ C` by taking coproducts. -/
@[simps!]
/--
Definition of `liftToFinsetObj` / `liftToFinsetObj` 的定义

English:
definition liftToFinsetObj
  signature: (F : Discrete α ⥤ C)
  body: ∐ fun x : s => F.obj x
  map {_ Y} h := Sigma.desc fun y =>
    Sigma.ι (fun (x : { x // x in Y }) => F.obj x) ⟨y, h.down.down y.2⟩

中文:
定义 liftToFinsetObj
  签名: (F : Discrete α ⥤ C)
  定义体: ∐ fun x : s => F.obj x
  map {_ Y} h := Sigma.desc fun y =>
    Sigma.ι (fun (x : { x // x in Y }) => F.obj x) ⟨y, h.down.down y.2⟩

Depends on / 依赖: F.obj
-/
def liftToFinsetObj (F : Discrete α ⥤ C) : Finset (Discrete α) ⥤ C where
  obj s := ∐ fun x : s => F.obj x
  map {_ Y} h := Sigma.desc fun y =>
    Sigma.ι (fun (x : { x // x in Y }) => F.obj x) ⟨y, h.down.down y.2⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `C` has finite coproducts and filtered colimits, we can construct arbitrary coproducts by
taking the colimit of the diagram formed by the coproducts of finite sets over the indexing type. -/
@[simps!]
/--
Definition of `liftToFinsetColimitCocone` / `liftToFinsetColimitCocone` 的定义

English:
definition liftToFinsetColimitCocone
  signature: [HasColimitsOfShape (Finset (Discrete α)) C]
  body: { pt := colimit (liftToFinsetObj F)
      ι :=
        Discrete.natTrans fun j =>
          Sigma.ι (fun x : ({j} : Finset (Discrete α)) => F.obj x) ⟨j, by simp⟩ ≫
            colimit.ι (liftToFinsetObj F) {j} }
  isColimit :=
    { desc := fun s =>
        colimit.desc (liftToFinsetObj F)
         

中文:
定义 liftToFinsetColimitCocone
  签名: [HasColimitsOfShape (Finset (Discrete α)) C]
  定义体: { pt := colimit (liftToFinsetObj F)
      ι :=
        Discrete.natTrans fun j =>
          Sigma.ι (fun x : ({j} : Finset (Discrete α)) => F.obj x) ⟨j, by simp⟩ ≫
            colimit.ι (liftToFinsetObj F) {j} }
  isColimit :=
    { desc := fun s =>
        colimit.desc (liftToFinsetObj F)
         

Depends on / 依赖: Discrete, Discrete.natTrans, F.obj, Finset, Finset.s, Sigma.desc, colimit, colimit.desc, colimit.hom_ext, colimit.w, convert, hom_ext, isColimit, liftToFinsetObj, natTrans, s.pt
-/
def liftToFinsetColimitCocone [HasColimitsOfShape (Finset (Discrete α)) C]
    (F : Discrete α ⥤ C) : ColimitCocone F where
  cocone :=
    { pt := colimit (liftToFinsetObj F)
      ι :=
        Discrete.natTrans fun j =>
          Sigma.ι (fun x : ({j} : Finset (Discrete α)) => F.obj x) ⟨j, by simp⟩ ≫
            colimit.ι (liftToFinsetObj F) {j} }
  isColimit :=
    { desc := fun s =>
        colimit.desc (liftToFinsetObj F)
          { pt := s.pt
            ι := { app := fun _ => Sigma.desc fun x => s.ι.app x } }
      uniq := fun s m h => by
        apply colimit.hom_ext
        rintro t
        dsimp [liftToFinsetObj]
        apply colimit.hom_ext
        rintro ⟨⟨j, hj⟩⟩
        convert! h j using 1
        · simp [← colimit.w (liftToFinsetObj F) ⟨⟨Finset.singleton_subset_iff.2 hj⟩⟩]
          rfl
        · simp }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (C) (α) in
/-- The functor taking a functor `Discrete α ⥤ C` to a functor `Finset (Discrete α) ⥤ C` by taking
coproducts. -/
@[simps!]
/--
Definition of `liftToFinset` / `liftToFinset` 的定义

English:
definition liftToFinset
  signature: : (Discrete α ⥤ C) ⥤ (Finset (Discrete α) ⥤ C) where
  body: liftToFinsetObj
  map := fun β => { app := fun _ => Sigma.map (fun x => β.app x.val) }

中文:
定义 liftToFinset
  签名: : (Discrete α ⥤ C) ⥤ (Finset (Discrete α) ⥤ C) where
  定义体: liftToFinsetObj
  map := fun β => { app := fun _ => Sigma.map (fun x => β.app x.val) }

Depends on / 依赖: liftToFinsetObj
-/
def liftToFinset : (Discrete α ⥤ C) ⥤ (Finset (Discrete α) ⥤ C) where
  obj := liftToFinsetObj
  map := fun β => { app := fun _ => Sigma.map (fun x => β.app x.val) }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The converse of the construction in `liftToFinsetColimitCocone`: we can form a cocone on the
coproduct of `f` whose legs are the coproducts over the finite subsets of `α`. -/
@[simps!]
/--
Definition of `finiteSubcoproductsCocone` / `finiteSubcoproductsCocone` 的定义

English:
definition finiteSubcoproductsCocone
  signature: (f : α -> C) [HasCoproduct f]
  body: ∐ f
  ι := { app S := Sigma.desc fun s => Sigma.ι f _ }

中文:
定义 finiteSubcoproductsCocone
  签名: (f : α -> C) [HasCoproduct f]
  定义体: ∐ f
  ι := { app S := Sigma.desc fun s => Sigma.ι f _ }
-/
def finiteSubcoproductsCocone (f : α -> C) [HasCoproduct f] :
    Cocone (liftToFinsetObj (Discrete.functor f)) where
  pt := ∐ f
  ι := { app S := Sigma.desc fun s => Sigma.ι f _ }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isColimitFiniteSubproductsCocone` / `isColimitFiniteSubproductsCocone` 的定义

English:
definition isColimitFiniteSubproductsCocone
  signature: (f : α -> C) [HasColimitsOfShape (Finset (Discrete α)) C]
  body: IsColimit.ofIsoColimit (colimit.isColimit _)
    (Cocone.ext (IsColimit.coconePointUniqueUpToIso
      (liftToFinsetColimitCocone (Discrete.functor f)).isColimit (colimit.isColimit _) :) (by
    intro S
    simp only [liftToFinsetObj_obj, Discrete.functor_obj_eq_as, finiteSubcoproductsCocone_pt,
   

中文:
定义 isColimitFiniteSubproductsCocone
  签名: (f : α -> C) [HasColimitsOfShape (Finset (Discrete α)) C]
  定义体: IsColimit.ofIsoColimit (colimit.isColimit _)
    (Cocone.ext (IsColimit.coconePointUniqueUpToIso
      (liftToFinsetColimitCocone (Discrete.functor f)).isColimit (colimit.isColimit _) :) (by
    intro S
    simp only [liftToFinsetObj_obj, Discrete.functor_obj_eq_as, finiteSubcoproductsCocone_pt,
   

Depends on / 依赖: Category, Category.assoc, Cocone, Cocone.ext, Discrete, Discrete.functor, Discrete.functor_obj_eq_as, IsColimit, IsColimit.coconePointUniqueUpToIso, IsColimit.comp_coconePointUniqueUpToIso_hom, IsColimit.ofIsoColimit, coconePointUniqueUpToIso, cocone_x, colimit, colimit.cocone_, colimit.cocone_x, colimit.isC, colimit.isColimit, comp_coconePointUniqueUpToIso_hom, convert
-/
def isColimitFiniteSubproductsCocone (f : α -> C) [HasColimitsOfShape (Finset (Discrete α)) C]
    [HasCoproduct f] : IsColimit (finiteSubcoproductsCocone f) :=
  IsColimit.ofIsoColimit (colimit.isColimit _)
    (Cocone.ext (IsColimit.coconePointUniqueUpToIso
      (liftToFinsetColimitCocone (Discrete.functor f)).isColimit (colimit.isColimit _) :) (by
    intro S
    simp only [liftToFinsetObj_obj, Discrete.functor_obj_eq_as, finiteSubcoproductsCocone_pt,
      colimit.cocone_x, colimit.cocone_ι, finiteSubcoproductsCocone_ι_app]
    ext j
    rw [← Category.assoc]
    convert!
      IsColimit.comp_coconePointUniqueUpToIso_hom
        (liftToFinsetColimitCocone (Discrete.functor f)).isColimit (colimit.isColimit _) j
    · simp [← colimit.w (liftToFinsetObj _) (homOfLE (x := {j.1}) (y := S) (by simp))]
    · simp))

end CoproductsFromFiniteFiltered

open CoproductsFromFiniteFiltered

/--
theorem `hasCoproducts_of_finite_and_filtered` / 定理 `hasCoproducts_of_finite_and_filtered`

English:
theorem hasCoproducts_of_finite_and_filtered
  statement: [HasFiniteCoproducts C]
  proof: fun α => by
  exact ⟨fun F => HasColimit.mk (liftToFinsetColimitCocone F)⟩

中文:
定理 hasCoproducts_of_finite_and_filtered
  结论: [HasFiniteCoproducts C]
  证明: fun α => by
  exact ⟨fun F => HasColimit.mk (liftToFinsetColimitCocone F)⟩

Depends on / 依赖: HasColimit, HasColimit.mk, liftToFinsetColimitCocone
-/
theorem hasCoproducts_of_finite_and_filtered [HasFiniteCoproducts C]
    [HasFilteredColimitsOfSize.{w, w} C] : HasCoproducts.{w} C := fun α => by
  exact ⟨fun F => HasColimit.mk (liftToFinsetColimitCocone F)⟩

/--
theorem `has_colimits_of_finite_and_filtered` / 定理 `has_colimits_of_finite_and_filtered`

English:
theorem has_colimits_of_finite_and_filtered
  statement: [HasFiniteColimits C]
  proof: have : HasCoproducts.{w} C := hasCoproducts_of_finite_and_filtered
  has_colimits_of_hasCoequalizers_and_coproducts

中文:
定理 has_colimits_of_finite_and_filtered
  结论: [HasFiniteColimits C]
  证明: have : HasCoproducts.{w} C := hasCoproducts_of_finite_and_filtered
  has_colimits_of_hasCoequalizers_and_coproducts

Depends on / 依赖: HasCoproducts, hasCoproducts_of_finite_and_filtered, has_colimits_of_hasCoequalizers_and_coproducts
-/
theorem has_colimits_of_finite_and_filtered [HasFiniteColimits C]
    [HasFilteredColimitsOfSize.{w, w} C] : HasColimitsOfSize.{w, w} C :=
  have : HasCoproducts.{w} C := hasCoproducts_of_finite_and_filtered
  has_colimits_of_hasCoequalizers_and_coproducts

/--
theorem `hasProducts_of_finite_and_cofiltered` / 定理 `hasProducts_of_finite_and_cofiltered`

English:
theorem hasProducts_of_finite_and_cofiltered
  statement: [HasFiniteProducts C]
  proof: have : HasCoproducts.{w} Cᵒᵖ := hasCoproducts_of_finite_and_filtered
  hasProducts_of_opposite

中文:
定理 hasProducts_of_finite_and_cofiltered
  结论: [HasFiniteProducts C]
  证明: have : HasCoproducts.{w} Cᵒᵖ := hasCoproducts_of_finite_and_filtered
  hasProducts_of_opposite

Depends on / 依赖: HasCoproducts, hasCoproducts_of_finite_and_filtered, hasProducts_of_opposite
-/
theorem hasProducts_of_finite_and_cofiltered [HasFiniteProducts C]
    [HasCofilteredLimitsOfSize.{w, w} C] : HasProducts.{w} C :=
  have : HasCoproducts.{w} Cᵒᵖ := hasCoproducts_of_finite_and_filtered
  hasProducts_of_opposite

/--
theorem `has_limits_of_finite_and_cofiltered` / 定理 `has_limits_of_finite_and_cofiltered`

English:
theorem has_limits_of_finite_and_cofiltered
  statement: [HasFiniteLimits C]
  proof: have : HasProducts.{w} C := hasProducts_of_finite_and_cofiltered
  has_limits_of_hasEqualizers_and_products

中文:
定理 has_limits_of_finite_and_cofiltered
  结论: [HasFiniteLimits C]
  证明: have : HasProducts.{w} C := hasProducts_of_finite_and_cofiltered
  has_limits_of_hasEqualizers_and_products

Depends on / 依赖: HasProducts, hasProducts_of_finite_and_cofiltered, has_limits_of_hasEqualizers_and_products
-/
theorem has_limits_of_finite_and_cofiltered [HasFiniteLimits C]
    [HasCofilteredLimitsOfSize.{w, w} C] : HasLimitsOfSize.{w, w} C :=
  have : HasProducts.{w} C := hasProducts_of_finite_and_cofiltered
  has_limits_of_hasEqualizers_and_products

namespace CoproductsFromFiniteFiltered

section

variable [HasFiniteCoproducts C] [HasColimitsOfShape (Finset (Discrete α)) C]
    [HasColimitsOfShape (Discrete α) C]

set_option backward.isDefEq.respectTransparency false in
/-- Helper construction for `liftToFinsetColimIso`. -/
@[reassoc]
/--
theorem `liftToFinsetColimIso_aux` / 定理 `liftToFinsetColimIso_aux`

English:
theorem liftToFinsetColimIso_aux
  given: (F : Discrete α ⥤ C) {J : Finset (Discrete α)} (j : J)
  proof: by
  simp [colimit.isoColimitCocone, IsColimit.coconePointUniqueUpToIso]

中文:
定理 liftToFinsetColimIso_aux
  条件: (F : Discrete α ⥤ C) {J : Finset (Discrete α)} (j : J)
  证明: by
  simp [colimit.isoColimitCocone, IsColimit.coconePointUniqueUpToIso]

Depends on / 依赖: IsColimit, IsColimit.coconePointUniqueUpToIso, coconePointUniqueUpToIso, colimit, colimit.isoColimitCocone, isoColimitCocone
-/
theorem liftToFinsetColimIso_aux (F : Discrete α ⥤ C) {J : Finset (Discrete α)} (j : J) :
    Sigma.ι (F.obj ·.val) j ≫ colimit.ι (liftToFinsetObj F) J ≫
      (colimit.isoColimitCocone (liftToFinsetColimitCocone F)).inv
    = colimit.ι F j := by
  simp [colimit.isoColimitCocone, IsColimit.coconePointUniqueUpToIso]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `liftToFinsetColimIso` / `liftToFinsetColimIso` 的定义

English:
definition liftToFinsetColimIso
  signature: : liftToFinset C α ⋙ colim ≅ colim
  body: NatIso.ofComponents
    (fun F => Iso.symm <| colimit.isoColimitCocone (liftToFinsetColimitCocone F))
    (fun β => by
      simp only [Functor.comp_obj, colim_obj, Functor.comp_map, colim_map, Iso.symm_hom]
      ext J
      simp only [liftToFinset_obj_obj]
      ext j
      simp [liftToFinset, lif

中文:
定义 liftToFinsetColimIso
  签名: : liftToFinset C α ⋙ colim ≅ colim
  定义体: NatIso.ofComponents
    (fun F => Iso.symm <| colimit.isoColimitCocone (liftToFinsetColimitCocone F))
    (fun β => by
      simp only [Functor.comp_obj, colim_obj, Functor.comp_map, colim_map, Iso.symm_hom]
      ext J
      simp only [liftToFinset_obj_obj]
      ext j
      simp [liftToFinset, lif

Depends on / 依赖: Functor, Functor.comp_map, Functor.comp_obj, Iso.symm, Iso.symm_hom, NatIso, NatIso.ofComponents, colim_map, colim_obj, colimit, colimit.isoColimitCocone, comp_map, comp_obj, isoColimitCocone, liftToFinset, liftToFinsetColimIso_aux, liftToFinsetColimIso_aux_assoc, liftToFinsetColimitCocone, liftToFinset_obj_obj, ofComponents
-/
def liftToFinsetColimIso : liftToFinset C α ⋙ colim ≅ colim :=
  NatIso.ofComponents
    (fun F => Iso.symm <| colimit.isoColimitCocone (liftToFinsetColimitCocone F))
    (fun β => by
      simp only [Functor.comp_obj, colim_obj, Functor.comp_map, colim_map, Iso.symm_hom]
      ext J
      simp only [liftToFinset_obj_obj]
      ext j
      simp [liftToFinset, liftToFinsetColimIso_aux, liftToFinsetColimIso_aux_assoc])

end

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `liftToFinsetEvaluationIso` / `liftToFinsetEvaluationIso` 的定义

English:
definition liftToFinsetEvaluationIso
  signature: [HasFiniteCoproducts C] (I : Finset (Discrete α))
  body: NatIso.ofComponents (fun _ => HasColimit.isoOfNatIso (Discrete.natIso fun _ => Iso.refl _))
    fun _ => by dsimp; ext; simp

中文:
定义 liftToFinsetEvaluationIso
  签名: [HasFiniteCoproducts C] (I : Finset (Discrete α))
  定义体: NatIso.ofComponents (fun _ => HasColimit.isoOfNatIso (Discrete.natIso fun _ => Iso.refl _))
    fun _ => by dsimp; ext; simp

Depends on / 依赖: Discrete
-/
def liftToFinsetEvaluationIso [HasFiniteCoproducts C] (I : Finset (Discrete α)) :
    liftToFinset C α ⋙ (evaluation _ _).obj I ≅
    (Functor.whiskeringLeft _ _ _).obj (Discrete.functor (·.val)) ⋙ colim (J := Discrete I) :=
  NatIso.ofComponents (fun _ => HasColimit.isoOfNatIso (Discrete.natIso fun _ => Iso.refl _))
    fun _ => by dsimp; ext; simp

end CoproductsFromFiniteFiltered

namespace ProductsFromFiniteCofiltered

variable [HasFiniteProducts C]

set_option backward.isDefEq.respectTransparency false in
/-- If `C` has finite coproducts, a functor `Discrete α ⥤ C` lifts to a functor
`Finset (Discrete α) ⥤ C` by taking coproducts. -/
@[simps!]
/--
Definition of `liftToFinsetObj` / `liftToFinsetObj` 的定义

English:
definition liftToFinsetObj
  signature: (F : Discrete α ⥤ C)
  body: ∏ᶜ (fun x : s.unop => F.obj x)
  map {Y _} h := Pi.lift fun y =>
    Pi.π (fun (x : { x // x in Y.unop }) => F.obj x) ⟨y, h.unop.down.down y.2⟩

中文:
定义 liftToFinsetObj
  签名: (F : Discrete α ⥤ C)
  定义体: ∏ᶜ (fun x : s.unop => F.obj x)
  map {Y _} h := Pi.lift fun y =>
    Pi.π (fun (x : { x // x in Y.unop }) => F.obj x) ⟨y, h.unop.down.down y.2⟩

Depends on / 依赖: F.obj, s.unop
-/
def liftToFinsetObj (F : Discrete α ⥤ C) : (Finset (Discrete α))ᵒᵖ ⥤ C where
  obj s := ∏ᶜ (fun x : s.unop => F.obj x)
  map {Y _} h := Pi.lift fun y =>
    Pi.π (fun (x : { x // x in Y.unop }) => F.obj x) ⟨y, h.unop.down.down y.2⟩


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `C` has finite coproducts and filtered colimits, we can construct arbitrary coproducts by
taking the colimit of the diagram formed by the coproducts of finite sets over the indexing type. -/
@[simps!]
/--
Definition of `liftToFinsetLimitCone` / `liftToFinsetLimitCone` 的定义

English:
definition liftToFinsetLimitCone
  signature: [HasLimitsOfShape (Finset (Discrete α))ᵒᵖ C]
  body: { pt := limit (liftToFinsetObj F)
      π := Discrete.natTrans fun j =>
        limit.π (liftToFinsetObj F) ⟨{j}⟩ ≫ Pi.π _ (⟨j, by simp⟩ : ({j} : Finset (Discrete α))) }
  isLimit :=
    { lift := fun s =>
        limit.lift (liftToFinsetObj F)
          { pt := s.pt
            π := { app := fun _ 

中文:
定义 liftToFinsetLimitCone
  签名: [HasLimitsOfShape (Finset (Discrete α))ᵒᵖ C]
  定义体: { pt := limit (liftToFinsetObj F)
      π := Discrete.natTrans fun j =>
        limit.π (liftToFinsetObj F) ⟨{j}⟩ ≫ Pi.π _ (⟨j, by simp⟩ : ({j} : Finset (Discrete α))) }
  isLimit :=
    { lift := fun s =>
        limit.lift (liftToFinsetObj F)
          { pt := s.pt
            π := { app := fun _ 

Depends on / 依赖: Discrete, Discrete.natTrans, Finset, Finset.singleton_subset_iff, Pi.lift, convert, hom_ext, isLimit, liftToFinsetObj, limit.hom_ext, limit.lift, limit.w, natTrans, s.pt, singleton_subset_iff
-/
def liftToFinsetLimitCone [HasLimitsOfShape (Finset (Discrete α))ᵒᵖ C]
    (F : Discrete α ⥤ C) : LimitCone F where
  cone :=
    { pt := limit (liftToFinsetObj F)
      π := Discrete.natTrans fun j =>
        limit.π (liftToFinsetObj F) ⟨{j}⟩ ≫ Pi.π _ (⟨j, by simp⟩ : ({j} : Finset (Discrete α))) }
  isLimit :=
    { lift := fun s =>
        limit.lift (liftToFinsetObj F)
          { pt := s.pt
            π := { app := fun _ => Pi.lift fun x => s.π.app x } }
      uniq := fun s m h => by
        apply limit.hom_ext
        rintro t
        dsimp [liftToFinsetObj]
        apply limit.hom_ext
        rintro ⟨⟨j, hj⟩⟩
        convert! h j using 1
        · simp [← limit.w (liftToFinsetObj F) ⟨⟨⟨Finset.singleton_subset_iff.2 hj⟩⟩⟩]
          rfl
        · simp }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The converse of the construction in `liftToFinsetLimitCone`: we can form a cone on the
product of `f` whose legs are the products over the finite subsets of `α`. -/
@[simps!]
/--
Definition of `finiteSubproductsCone` / `finiteSubproductsCone` 的定义

English:
definition finiteSubproductsCone
  signature: (f : α -> C) [HasProduct f]
  body: ∏ᶜ f
  π := { app S := Pi.lift fun s => Pi.π f _ }

中文:
定义 finiteSubproductsCone
  签名: (f : α -> C) [HasProduct f]
  定义体: ∏ᶜ f
  π := { app S := Pi.lift fun s => Pi.π f _ }
-/
def finiteSubproductsCone (f : α -> C) [HasProduct f] :
    Cone (liftToFinsetObj (Discrete.functor f)) where
  pt := ∏ᶜ f
  π := { app S := Pi.lift fun s => Pi.π f _ }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isLimitFiniteSubproductsCone` / `isLimitFiniteSubproductsCone` 的定义

English:
definition isLimitFiniteSubproductsCone
  signature: (f : α -> C) [HasLimitsOfShape (Finset (Discrete α))ᵒᵖ C]
  body: IsLimit.ofIsoLimit (limit.isLimit _)
    (Cone.ext (IsLimit.conePointUniqueUpToIso
      (liftToFinsetLimitCone (Discrete.functor f)).isLimit (limit.isLimit _) :) (by
    intro S
    simp only [limit.cone_x, Functor.const_obj_obj, liftToFinsetObj_obj, Discrete.functor_obj_eq_as,
      limit.cone_π, 

中文:
定义 isLimitFiniteSubproductsCone
  签名: (f : α -> C) [HasLimitsOfShape (Finset (Discrete α))ᵒᵖ C]
  定义体: IsLimit.ofIsoLimit (limit.isLimit _)
    (Cone.ext (IsLimit.conePointUniqueUpToIso
      (liftToFinsetLimitCone (Discrete.functor f)).isLimit (limit.isLimit _) :) (by
    intro S
    simp only [limit.cone_x, Functor.const_obj_obj, liftToFinsetObj_obj, Discrete.functor_obj_eq_as,
      limit.cone_π, 

Depends on / 依赖: Category, Category.assoc, Cone.ext, Discrete, Discrete.functor, Discrete.functor_obj_eq_as, Fan.mk_, Fan.mk_pt, Functor, Functor.const_obj_obj, IsLimit, IsLimit.conePointUniqueUpToIso, IsLimit.ofIsoLimit, conePointUniqueUpToIso, conePointUniqueUpToIso_hom_comp, cone_x, const_obj_obj, finiteSubproductsCone_pt, functor, functor_obj_eq_as
-/
def isLimitFiniteSubproductsCone (f : α -> C) [HasLimitsOfShape (Finset (Discrete α))ᵒᵖ C]
    [HasProduct f] : IsLimit (finiteSubproductsCone f) :=
  IsLimit.ofIsoLimit (limit.isLimit _)
    (Cone.ext (IsLimit.conePointUniqueUpToIso
      (liftToFinsetLimitCone (Discrete.functor f)).isLimit (limit.isLimit _) :) (by
    intro S
    simp only [limit.cone_x, Functor.const_obj_obj, liftToFinsetObj_obj, Discrete.functor_obj_eq_as,
      limit.cone_π, finiteSubproductsCone_pt, finiteSubproductsCone_π_app]
    ext j
    simp only [Discrete.functor_obj_eq_as, Category.assoc, limit.lift_π, Fan.mk_pt, Fan.mk_π_app,
      limit.conePointUniqueUpToIso_hom_comp, liftToFinsetLimitCone_cone_pt, Discrete.mk_as,
      liftToFinsetLimitCone_cone_π_app]
    simp [← limit.w (liftToFinsetObj _)
      (Quiver.Hom.op (homOfLE (x := {j.1}) (y := S.unop) (by simp)))]))

variable (C) (α)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The functor taking a functor `Discrete α ⥤ C` to a functor `Finset (Discrete α) ⥤ C` by taking
coproducts. -/
@[simps!]
/--
Definition of `liftToFinset` / `liftToFinset` 的定义

English:
definition liftToFinset
  signature: : (Discrete α ⥤ C) ⥤ ((Finset (Discrete α))ᵒᵖ ⥤ C) where
  body: liftToFinsetObj
  map := fun β => { app := fun _ => Pi.map (fun x => β.app x.val) }

中文:
定义 liftToFinset
  签名: : (Discrete α ⥤ C) ⥤ ((Finset (Discrete α))ᵒᵖ ⥤ C) where
  定义体: liftToFinsetObj
  map := fun β => { app := fun _ => Pi.map (fun x => β.app x.val) }

Depends on / 依赖: liftToFinsetObj
-/
def liftToFinset : (Discrete α ⥤ C) ⥤ ((Finset (Discrete α))ᵒᵖ ⥤ C) where
  obj := liftToFinsetObj
  map := fun β => { app := fun _ => Pi.map (fun x => β.app x.val) }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `liftToFinsetLimIso` / `liftToFinsetLimIso` 的定义

English:
definition liftToFinsetLimIso
  signature: [HasLimitsOfShape (Finset (Discrete α))ᵒᵖ C]
  body: NatIso.ofComponents
    (fun F => Iso.symm <| limit.isoLimitCone (liftToFinsetLimitCone F))
    (fun β => by
      simp only [Functor.comp_obj, lim_obj, Functor.comp_map, lim_map, Iso.symm_hom]
      ext J
      simp [liftToFinset])

中文:
定义 liftToFinsetLimIso
  签名: [HasLimitsOfShape (Finset (Discrete α))ᵒᵖ C]
  定义体: NatIso.ofComponents
    (fun F => Iso.symm <| limit.isoLimitCone (liftToFinsetLimitCone F))
    (fun β => by
      simp only [Functor.comp_obj, lim_obj, Functor.comp_map, lim_map, Iso.symm_hom]
      ext J
      simp [liftToFinset])

Depends on / 依赖: Functor, Functor.comp_map, Functor.comp_obj, Iso.symm, Iso.symm_hom, NatIso, NatIso.ofComponents, comp_map, comp_obj, isoLimitCone, liftToFinset, liftToFinsetLimitCone, lim_map, lim_obj, limit.isoLimitCone, ofComponents, symm_hom
-/
def liftToFinsetLimIso [HasLimitsOfShape (Finset (Discrete α))ᵒᵖ C]
    [HasLimitsOfShape (Discrete α) C] : liftToFinset C α ⋙ lim ≅ lim :=
  NatIso.ofComponents
    (fun F => Iso.symm <| limit.isoLimitCone (liftToFinsetLimitCone F))
    (fun β => by
      simp only [Functor.comp_obj, lim_obj, Functor.comp_map, lim_map, Iso.symm_hom]
      ext J
      simp [liftToFinset])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `liftToFinsetEvaluationIso` / `liftToFinsetEvaluationIso` 的定义

English:
definition liftToFinsetEvaluationIso
  signature: (I : Finset (Discrete α))
  body: NatIso.ofComponents (fun _ => HasLimit.isoOfNatIso (Discrete.natIso fun _ => Iso.refl _))
    fun _ => by dsimp; ext; simp [Pi.map]

中文:
定义 liftToFinsetEvaluationIso
  签名: (I : Finset (Discrete α))
  定义体: NatIso.ofComponents (fun _ => HasLimit.isoOfNatIso (Discrete.natIso fun _ => Iso.refl _))
    fun _ => by dsimp; ext; simp [Pi.map]

Depends on / 依赖: Discrete
-/
def liftToFinsetEvaluationIso (I : Finset (Discrete α)) :
    liftToFinset C α ⋙ (evaluation _ _).obj ⟨I⟩ ≅
    (Functor.whiskeringLeft _ _ _).obj (Discrete.functor (·.val)) ⋙ lim (J := Discrete I) :=
  NatIso.ofComponents (fun _ => HasLimit.isoOfNatIso (Discrete.natIso fun _ => Iso.refl _))
    fun _ => by dsimp; ext; simp [Pi.map]

end ProductsFromFiniteCofiltered

end CategoryTheory.Limits
