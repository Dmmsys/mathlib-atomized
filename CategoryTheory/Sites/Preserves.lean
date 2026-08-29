/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import Mathlib.CategoryTheory.Sites.EqualizerSheafCondition
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Sheaves preserve products

We prove that a presheaf which satisfies the sheaf condition with respect to certain presieves
preserve "the corresponding products".

## Main results

More precisely, given a presheaf `F : Cᵒᵖ ⥤ Type*`, we have:

* If `F` satisfies the sheaf condition with respect to the empty sieve on the initial object of `C`,
  then `F` preserves terminal objects.
  See `preservesTerminalOfIsSheafForEmpty`.

* If `F` furthermore satisfies the sheaf condition with respect to the presieve consisting of the
  inclusion arrows in a coproduct in `C`, then `F` preserves the corresponding product.
  See `preservesProductOfIsSheafFor`.

* If `F` preserves a product, then it satisfies the sheaf condition with respect to the
  corresponding presieve of arrows.
  See `isSheafFor_of_preservesProduct`.
-/

@[expose] public section

universe v u w

namespace CategoryTheory.Presieve

variable {C : Type u} [Category.{v} C] {I : C} (F : Cᵒᵖ ⥤ Type w)

open Limits Opposite

variable (hF : (ofArrows (X := I) Empty.elim Empty.instIsEmpty.elim).IsSheafFor F)

section Terminal

variable (I) in
/--
If `F` is a presheaf which satisfies the sheaf condition with respect to the empty presieve on any
object, then `F` takes that object to the terminal object.
-/
noncomputable
/--
Definition of `isTerminal_of_isSheafFor_empty_presieve` / `isTerminal_of_isSheafFor_empty_presieve` 的定义

English:
definition isTerminal_of_isSheafFor_empty_presieve
  signature: : IsTerminal (F.obj (op I))
  body: by
  refine @IsTerminal.ofUnique _ _ _ fun Y => ?_
  choose t h using hF (by tauto) (by tauto)
  exact ⟨⟨↾fun _ => t⟩, fun a => by ext; exact h.2 _ (by tauto)⟩

include hF in

中文:
定义 isTerminal_of_isSheafFor_empty_presieve
  签名: : 是终止 (F.obj (op I))
  定义体: by
  refine @IsTerminal.ofUnique _ _ _ fun Y => ?_
  choose t h using hF (by tauto) (by tauto)
  exact ⟨⟨↾fun _ => t⟩, fun a => by ext; exact h.2 _ (by tauto)⟩

include hF in

Depends on / 依赖: IsTerminal, IsTerminal.ofUnique, ofUnique
-/
def isTerminal_of_isSheafFor_empty_presieve : IsTerminal (F.obj (op I)) := by
  refine @IsTerminal.ofUnique _ _ _ fun Y => ?_
  choose t h using hF (by tauto) (by tauto)
  exact ⟨⟨↾fun _ => t⟩, fun a => by ext; exact h.2 _ (by tauto)⟩

include hF in
/--
lemma `preservesTerminal_of_isSheaf_for_empty` / 引理 `preservesTerminal_of_isSheaf_for_empty`

English:
lemma preservesTerminal_of_isSheaf_for_empty
  given: (hI : IsInitial I)
  proof: have := hI.hasInitial
  (preservesTerminal_of_iso F
    ((F.mapIso (terminalIsoIsTerminal (terminalOpOfInitial initialIsInitial)) ≪≫
    (F.mapIso (initialIsoIsInitial hI).symm.op) ≪≫
    (terminalIsoIsTerminal (isTerminal_of_isSheafFor_empty_presieve I F hF)).symm)))

中文:
引理 preservesTerminal_of_isSheaf_for_empty
  条件: (hI : IsInitial I)
  证明: have := hI.hasInitial
  (preservesTerminal_of_iso F
    ((F.mapIso (terminalIsoIsTerminal (terminalOpOfInitial initialIsInitial)) ≪≫
    (F.mapIso (initialIsoIsInitial hI).symm.op) ≪≫
    (terminalIsoIsTerminal (isTerminal_of_isSheafFor_empty_presieve I F hF)).symm)))

Depends on / 依赖: F.mapIso, hI.hasInitial, hasInitial, initialIsInitial, initialIsoIsInitial, isTerminal_of_isSheafFor_empty_presieve, mapIso, preservesTerminal_of_iso, symm.op, terminalIsoIsTerminal, terminalOpOfInitial
-/
lemma preservesTerminal_of_isSheaf_for_empty (hI : IsInitial I) :
    PreservesLimit (Functor.empty.{0} Cᵒᵖ) F :=
  have := hI.hasInitial
  (preservesTerminal_of_iso F
    ((F.mapIso (terminalIsoIsTerminal (terminalOpOfInitial initialIsInitial)) ≪≫
    (F.mapIso (initialIsoIsInitial hI).symm.op) ≪≫
    (terminalIsoIsTerminal (isTerminal_of_isSheafFor_empty_presieve I F hF)).symm)))

end Terminal

section Product

variable (hI : IsInitial I)

-- This is the data of a particular disjoint coproduct in `C`.
variable {α : Type*} [Small.{w} α] {X : α -> C} (c : Cofan X) (hc : IsColimit c)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
theorem `piComparison_fac` / 定理 `piComparison_fac`

English:
theorem piComparison_fac
  proof: ⟨⟨c, hc⟩⟩
    piComparison F (fun x => op (X x)) = F.map (opCoproductIsoProduct' hc (productIsProduct _)).inv ≫
    Equalizer.Presieve.Arrows.forkMap F X c.inj := by
  have : HasCoproduct X := ⟨⟨c, hc⟩⟩
  dsimp only [Equalizer.Presieve.Arrows.forkMap]
  have h : Pi.lift (fun i => F.map (c.inj i).op) =
      F.map (Pi.lift (fun i => (c.inj i).op)) ≫ piComparison F _ := by simp
  rw [h]; rw [← Category.assoc]; rw [← Functor.map_comp]
  have hh : Pi.lift (fun i => (c.inj i).op) = (productIsProduct (op <| X ·)).lift c.op := by
    simp [Pi.lift, productIsProduct]
  rw [hh]; rw [← desc_op_comp_opCoproductIsoProduct'_hom hc]
  simp

中文:
定理 piComparison_fac
  证明: ⟨⟨c, hc⟩⟩
    piComparison F (fun x => op (X x)) = F.map (opCoproductIsoProduct' hc (productIsProduct _)).inv ≫
    Equalizer.Presieve.Arrows.forkMap F X c.inj := by
  have : HasCoproduct X := ⟨⟨c, hc⟩⟩
  dsimp only [Equalizer.Presieve.Arrows.forkMap]
  have h : Pi.lift (fun i => F.map (c.inj i).op) =
      F.map (Pi.lift (fun i => (c.inj i).op)) ≫ piComparison F _ := by simp
  rw [h]; rw [← Category.assoc]; rw [← Functor.map_comp]
  have hh : Pi.lift (fun i => (c.inj i).op) = (productIsProduct (op <| X ·)).lift c.op := by
    simp [Pi.lift, productIsProduct]
  rw [hh]; rw [← desc_op_comp_opCoproductIsoProduct'_hom hc]
  simp
-/
theorem piComparison_fac :
    have : HasCoproduct X := ⟨⟨c, hc⟩⟩
    piComparison F (fun x => op (X x)) = F.map (opCoproductIsoProduct' hc (productIsProduct _)).inv ≫
    Equalizer.Presieve.Arrows.forkMap F X c.inj := by
  have : HasCoproduct X := ⟨⟨c, hc⟩⟩
  dsimp only [Equalizer.Presieve.Arrows.forkMap]
  have h : Pi.lift (fun i => F.map (c.inj i).op) =
      F.map (Pi.lift (fun i => (c.inj i).op)) ≫ piComparison F _ := by simp
  rw [h]; rw [← Category.assoc]; rw [← Functor.map_comp]
  have hh : Pi.lift (fun i => (c.inj i).op) = (productIsProduct (op <| X ·)).lift c.op := by
    simp [Pi.lift, productIsProduct]
  rw [hh]; rw [← desc_op_comp_opCoproductIsoProduct'_hom hc]
  simp

variable [(ofArrows X c.inj).HasPairwisePullbacks]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include hc in
/--
theorem `isSheafFor_of_preservesProduct` / 定理 `isSheafFor_of_preservesProduct`

English:
theorem isSheafFor_of_preservesProduct
  given: [PreservesLimit (Discrete.functor (fun x => op (X x))) F]
  proof: by
  rw [Equalizer.Presieve.Arrows.sheaf_condition]; rw [Limits.Types.type_equalizer_iff_unique]
  have : HasCoproduct X := ⟨⟨c, hc⟩⟩
  have hi : IsIso (piComparison F (fun x => op (X x))) := inferInstance
  rw [piComparison_fac (hc := hc)]; rw [isIso_iff_bijective]; rw [Function.bijective_iff_existsUnique] at hi
  intro b _
  obtain ⟨t, ht₁, ht₂⟩ := hi b
  refine ⟨F.map ((opCoproductIsoProduct' hc (productIsProduct _)).inv) t, ht₁, fun y hy => ?_⟩
  apply_fun F.map ((opCoproductIsoProduct' hc (productIsProduct _)).hom) using injective_of_mono _
  simp only [Fan.mk_pt, ← comp_apply, ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id, id_apply]
  apply ht₂ (F.map ((opCoproductIsoProduct' hc (productIsProduct _)).hom) y)
    (by simp [← hy, ← comp_apply])

中文:
定理 isSheafFor_of_preservesProduct
  条件: [保持极限 (离散.functor (fun x => op (X x))) F]
  证明: by
  rw [Equalizer.Presieve.Arrows.sheaf_condition]; rw [Limits.Types.type_equalizer_iff_unique]
  have : HasCoproduct X := ⟨⟨c, hc⟩⟩
  have hi : IsIso (piComparison F (fun x => op (X x))) := inferInstance
  rw [piComparison_fac (hc := hc)]; rw [isIso_iff_bijective]; rw [Function.bijective_iff_existsUnique] at hi
  intro b _
  obtain ⟨t, ht₁, ht₂⟩ := hi b
  refine ⟨F.map ((opCoproductIsoProduct' hc (productIsProduct _)).inv) t, ht₁, fun y hy => ?_⟩
  apply_fun F.map ((opCoproductIsoProduct' hc (productIsProduct _)).hom) using injective_of_mono _
  simp only [Fan.mk_pt, ← comp_apply, ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id, id_apply]
  apply ht₂ (F.map ((opCoproductIsoProduct' hc (productIsProduct _)).hom) y)
    (by simp [← hy, ← comp_apply])

Depends on / 依赖: Arrows, Equalizer, Equalizer.Presieve.Arrows.sheaf_condition, F.map, Function, Function.bijective_iff_existsUnique, HasCoproduct, Limits, Limits.Types.type_equalizer_iff_unique, Presieve, apply_fun, bijective_iff_existsUnique, isIso_iff_bijective, opCoproductIsoProduct, piComparison, piComparison_fac, productIsProduct, sheaf_condition, type_equalizer_iff_unique
-/
theorem isSheafFor_of_preservesProduct [PreservesLimit (Discrete.functor (fun x => op (X x))) F] :
    (ofArrows X c.inj).IsSheafFor F := by
  rw [Equalizer.Presieve.Arrows.sheaf_condition]; rw [Limits.Types.type_equalizer_iff_unique]
  have : HasCoproduct X := ⟨⟨c, hc⟩⟩
  have hi : IsIso (piComparison F (fun x => op (X x))) := inferInstance
  rw [piComparison_fac (hc := hc)]; rw [isIso_iff_bijective]; rw [Function.bijective_iff_existsUnique] at hi
  intro b _
  obtain ⟨t, ht₁, ht₂⟩ := hi b
  refine ⟨F.map ((opCoproductIsoProduct' hc (productIsProduct _)).inv) t, ht₁, fun y hy => ?_⟩
  apply_fun F.map ((opCoproductIsoProduct' hc (productIsProduct _)).hom) using injective_of_mono _
  simp only [Fan.mk_pt, ← comp_apply, ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id, id_apply]
  apply ht₂ (F.map ((opCoproductIsoProduct' hc (productIsProduct _)).hom) y)
    (by simp [← hy, ← comp_apply])

variable [HasInitial C] [forall i, Mono (c.inj i)]
  (hd : Pairwise fun i j => IsPullback (initial.to _) (initial.to _) (c.inj i) (c.inj j))

set_option backward.isDefEq.respectTransparency false in
include hd hF hI in
/--
theorem `firstMap_eq_secondMap` / 定理 `firstMap_eq_secondMap`

English:
theorem firstMap_eq_secondMap
  proof: by
  ext ⟨i, j⟩ a
  simp only [Equalizer.Presieve.Arrows.firstMap, limit.lift_π, Fan.mk_π_app,
    TypeCat.Fun.toFun_apply, comp_apply, Equalizer.Presieve.Arrows.secondMap]
  by_cases hi : i = j
  · rw [hi, Mono.right_cancellation _ _ pullback.condition]
  · have := preservesTerminal_of_isSheaf_for_empty F hF hI
    apply_fun (F.mapIso ((hd hi).isoPullback).op ≪≫ F.mapIso (terminalIsoIsTerminal
      (terminalOpOfInitial initialIsInitial)).symm ≪≫ (PreservesTerminal.iso F)).hom using
      injective_of_mono _
    ext ⟨i⟩
    exact i.elim

中文:
定理 firstMap_eq_secondMap
  证明: by
  ext ⟨i, j⟩ a
  simp only [Equalizer.Presieve.Arrows.firstMap, limit.lift_π, Fan.mk_π_app,
    TypeCat.Fun.toFun_apply, comp_apply, Equalizer.Presieve.Arrows.secondMap]
  by_cases hi : i = j
  · rw [hi, Mono.right_cancellation _ _ pullback.condition]
  · have := preservesTerminal_of_isSheaf_for_empty F hF hI
    apply_fun (F.mapIso ((hd hi).isoPullback).op ≪≫ F.mapIso (terminalIsoIsTerminal
      (terminalOpOfInitial initialIsInitial)).symm ≪≫ (PreservesTerminal.iso F)).hom using
      injective_of_mono _
    ext ⟨i⟩
    exact i.elim

Depends on / 依赖: Arrows, Equalizer, Equalizer.Presieve.Arrows.firstMap, Equalizer.Presieve.Arrows.secondMap, F.mapIso, Fan.mk_, Mono.right_cancellation, PreservesTerminal, PreservesTerminal.iso, Presieve, TypeCat, TypeCat.Fun.toFun_apply, apply_fun, comp_apply, condition, firstMap, initialIsInitial, injective_of_mono, isoPullback, limit.lift_
-/
theorem firstMap_eq_secondMap :
    Equalizer.Presieve.Arrows.firstMap F X c.inj =
    Equalizer.Presieve.Arrows.secondMap F X c.inj := by
  ext ⟨i, j⟩ a
  simp only [Equalizer.Presieve.Arrows.firstMap, limit.lift_π, Fan.mk_π_app,
    TypeCat.Fun.toFun_apply, comp_apply, Equalizer.Presieve.Arrows.secondMap]
  by_cases hi : i = j
  · rw [hi, Mono.right_cancellation _ _ pullback.condition]
  · have := preservesTerminal_of_isSheaf_for_empty F hF hI
    apply_fun (F.mapIso ((hd hi).isoPullback).op ≪≫ F.mapIso (terminalIsoIsTerminal
      (terminalOpOfInitial initialIsInitial)).symm ≪≫ (PreservesTerminal.iso F)).hom using
      injective_of_mono _
    ext ⟨i⟩
    exact i.elim

set_option backward.isDefEq.respectTransparency false in
include hc hd hF hI in
/--
lemma `preservesProduct_of_isSheafFor` / 引理 `preservesProduct_of_isSheafFor`

English:
lemma preservesProduct_of_isSheafFor
  proof: by
  have : HasCoproduct X := ⟨⟨c, hc⟩⟩
  refine @PreservesProduct.of_iso_comparison _ _ _ _ F _ (fun x => op (X x)) _ _ ?_
  rw [piComparison_fac (hc := hc)]
  refine IsIso.comp_isIso' inferInstance ?_
  rw [isIso_iff_bijective]; rw [Function.bijective_iff_existsUnique]
  rw [Equalizer.Presieve.Arrows.sheaf_condition]; rw [Limits.Types.type_equalizer_iff_unique] at hF'
  exact fun b => hF' b (ConcreteCategory.congr_hom (firstMap_eq_secondMap F hF hI c hd) b)

include hc hd hF hI in

中文:
引理 preservesProduct_of_isSheafFor
  证明: by
  have : HasCoproduct X := ⟨⟨c, hc⟩⟩
  refine @PreservesProduct.of_iso_comparison _ _ _ _ F _ (fun x => op (X x)) _ _ ?_
  rw [piComparison_fac (hc := hc)]
  refine IsIso.comp_isIso' inferInstance ?_
  rw [isIso_iff_bijective]; rw [Function.bijective_iff_existsUnique]
  rw [Equalizer.Presieve.Arrows.sheaf_condition]; rw [Limits.Types.type_equalizer_iff_unique] at hF'
  exact fun b => hF' b (ConcreteCategory.congr_hom (firstMap_eq_secondMap F hF hI c hd) b)

include hc hd hF hI in

Depends on / 依赖: Arrows, ConcreteCategory, ConcreteCategory.congr_hom, Equalizer, Equalizer.Presieve.Arrows.sheaf_condition, Function, Function.bijective_iff_existsUnique, HasCoproduct, IsIso.comp_isIso, Limits, Limits.Types.type_equalizer_iff_unique, PreservesProduct, PreservesProduct.of_iso_comparison, Presieve, bijective_iff_existsUnique, comp_isIso, congr_hom, firstMap_eq_secondMap, isIso_iff_bijective, of_iso_comparison
-/
lemma preservesProduct_of_isSheafFor
    (hF' : (ofArrows X c.inj).IsSheafFor F) :
    PreservesLimit (Discrete.functor (fun x => op (X x))) F := by
  have : HasCoproduct X := ⟨⟨c, hc⟩⟩
  refine @PreservesProduct.of_iso_comparison _ _ _ _ F _ (fun x => op (X x)) _ _ ?_
  rw [piComparison_fac (hc := hc)]
  refine IsIso.comp_isIso' inferInstance ?_
  rw [isIso_iff_bijective]; rw [Function.bijective_iff_existsUnique]
  rw [Equalizer.Presieve.Arrows.sheaf_condition]; rw [Limits.Types.type_equalizer_iff_unique] at hF'
  exact fun b => hF' b (ConcreteCategory.congr_hom (firstMap_eq_secondMap F hF hI c hd) b)

include hc hd hF hI in
/--
theorem `isSheafFor_iff_preservesProduct` / 定理 `isSheafFor_iff_preservesProduct`

English:
theorem isSheafFor_iff_preservesProduct
  statement: (ofArrows X c.inj).IsSheafFor F ↔
  proof: ⟨fun hF' => preservesProduct_of_isSheafFor _ hF hI c hc hd hF',
    fun _ => isSheafFor_of_preservesProduct F c hc⟩

中文:
定理 isSheafFor_iff_preservesProduct
  结论: (ofArrows X c.inj).IsSheafFor F ↔
  证明: ⟨fun hF' => preservesProduct_of_isSheafFor _ hF hI c hc hd hF',
    fun _ => isSheafFor_of_preservesProduct F c hc⟩

Depends on / 依赖: isSheafFor_of_preservesProduct, preservesProduct_of_isSheafFor
-/
theorem isSheafFor_iff_preservesProduct : (ofArrows X c.inj).IsSheafFor F ↔
    PreservesLimit (Discrete.functor (fun x => op (X x))) F :=
  ⟨fun hF' => preservesProduct_of_isSheafFor _ hF hI c hc hd hF',
    fun _ => isSheafFor_of_preservesProduct F c hc⟩

end Product

end CategoryTheory.Presieve
