/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Sums.Associator
public import Mathlib.CategoryTheory.Products.Associator

/-!
# Functors out of sums of categories.

This file records the universal property of sums of categories as an equivalence of
categories `Sum.functorEquiv : A ⊕ A' ⥤ B ≌ (A ⥤ B) × (A' ⥤ B)`, and characterizes its
precompositions with the left and right inclusion as corresponding to the projections on
the product side.

-/

@[expose] public section

namespace CategoryTheory

open CategoryTheory.Functor

open scoped CategoryTheory.Prod

universe v u

variable (A : Type*) [Category* A] (A' : Type*) [Category* A']
  (B : Type u) [Category.{v} B]

namespace Sum

set_option backward.defeqAttrib.useBackward true in
/-- The equivalence between functors from a sum and the product of the functor categories. -/
@[simps]
/--
Definition of `functorEquiv` / `functorEquiv` 的定义

English:
definition functorEquiv
  signature: : A oplus A' ⥤ B ≌ (A ⥤ B) × (A' ⥤ B) where
  body: { obj F := ⟨inl_ A A' ⋙ F, inr_ A A' ⋙ F⟩
      map η := whiskerLeft (inl_ A A') η ×ₘ whiskerLeft (inr_ A A') η }
  inverse :=
    { obj F := Functor.sum' F.1 F.2
      map η := NatTrans.sum' η.1 η.2 }
unitIso := NatIso.ofComponents fun F => F.isoSum
  counitIso := NatIso.ofComponents (fun F =>
    

中文:
定义 functorEquiv
  签名: : A oplus A' ⥤ B ≌ (A ⥤ B) × (A' ⥤ B) where
  定义体: { obj F := ⟨inl_ A A' ⋙ F, inr_ A A' ⋙ F⟩
      map η := whiskerLeft (inl_ A A') η ×ₘ whiskerLeft (inr_ A A') η }
  inverse :=
    { obj F := Functor.sum' F.1 F.2
      map η := NatTrans.sum' η.1 η.2 }
unitIso := NatIso.ofComponents fun F => F.isoSum
  counitIso := NatIso.ofComponents (fun F =>
    

Depends on / 依赖: F.isoSum, Functor, Functor.inlCompSum, Functor.inrCompSum, Functor.sum, NatIso, NatIso.ofComponents, NatTrans, NatTrans.sum, counitIso, etaIso, inlCompSum, inl_, inrCompSum, inr_, inverse, isoSum, ofComponents, prod.etaIso, unitIso
-/
def functorEquiv : A oplus A' ⥤ B ≌ (A ⥤ B) × (A' ⥤ B) where
  functor :=
    { obj F := ⟨inl_ A A' ⋙ F, inr_ A A' ⋙ F⟩
      map η := whiskerLeft (inl_ A A') η ×ₘ whiskerLeft (inr_ A A') η }
  inverse :=
    { obj F := Functor.sum' F.1 F.2
      map η := NatTrans.sum' η.1 η.2 }
unitIso := NatIso.ofComponents fun F => F.isoSum
  counitIso := NatIso.ofComponents (fun F =>
    (Functor.inlCompSum' _ _).prod (Functor.inrCompSum' _ _) ≪≫ prod.etaIso F)

variable {A A' B}

@[simp]
/--
lemma `functorEquiv_unit_app_app_inl` / 引理 `functorEquiv_unit_app_app_inl`

English:
lemma functorEquiv_unit_app_app_inl
  given: (X : A oplus A' ⥤ B) (a : A)
  proof: rfl

@[simp]

中文:
引理 functorEquiv_unit_app_app_inl
  条件: (X : A oplus A' ⥤ B) (a : A)
  证明: rfl

@[simp]
-/
lemma functorEquiv_unit_app_app_inl (X : A oplus A' ⥤ B) (a : A) :
    ((functorEquiv A A' B).unit.app X).app (.inl a) = 𝟙 (X.obj (.inl a)) :=
  rfl

@[simp]
/--
lemma `functorEquiv_unit_app_app_inr` / 引理 `functorEquiv_unit_app_app_inr`

English:
lemma functorEquiv_unit_app_app_inr
  given: (X : A oplus A' ⥤ B) (a' : A')
  proof: rfl

@[simp]

中文:
引理 functorEquiv_unit_app_app_inr
  条件: (X : A oplus A' ⥤ B) (a' : A')
  证明: rfl

@[simp]
-/
lemma functorEquiv_unit_app_app_inr (X : A oplus A' ⥤ B) (a' : A') :
    ((functorEquiv A A' B).unit.app X).app (.inr a') = 𝟙 (X.obj (.inr a')) :=
  rfl

@[simp]
/--
lemma `functorEquiv_unitIso_inv_app_app_inl` / 引理 `functorEquiv_unitIso_inv_app_app_inl`

English:
lemma functorEquiv_unitIso_inv_app_app_inl
  given: (X : A oplus A' ⥤ B) (a : A)
  proof: rfl

@[simp]

中文:
引理 functorEquiv_unitIso_inv_app_app_inl
  条件: (X : A oplus A' ⥤ B) (a : A)
  证明: rfl

@[simp]
-/
lemma functorEquiv_unitIso_inv_app_app_inl (X : A oplus A' ⥤ B) (a : A) :
    ((functorEquiv A A' B).unitIso.inv.app X).app (.inl a) = 𝟙 (X.obj (.inl a)) :=
  rfl

@[simp]
/--
lemma `functorEquiv_unitIso_inv_app_app_inr` / 引理 `functorEquiv_unitIso_inv_app_app_inr`

English:
lemma functorEquiv_unitIso_inv_app_app_inr
  given: (X : A oplus A' ⥤ B) (a' : A')
  proof: rfl

中文:
引理 functorEquiv_unitIso_inv_app_app_inr
  条件: (X : A oplus A' ⥤ B) (a' : A')
  证明: rfl
-/
lemma functorEquiv_unitIso_inv_app_app_inr (X : A oplus A' ⥤ B) (a' : A') :
    ((functorEquiv A A' B).unitIso.inv.app X).app (.inr a') = 𝟙 (X.obj (.inr a')) :=
  rfl

set_option backward.defeqAttrib.useBackward true in
/-- Composing the forward direction of `functorEquiv` with the first projection is the same as
precomposition with `inl_ A A'`. -/
@[simps!]
/--
Definition of `functorEquivFunctorCompFstIso` / `functorEquivFunctorCompFstIso` 的定义

English:
definition functorEquivFunctorCompFstIso
  signature: :
  body: NatIso.ofComponents (fun _ => Iso.refl _)

中文:
定义 functorEquivFunctorCompFstIso
  签名: :
  定义体: NatIso.ofComponents (fun _ => Iso.refl _)

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def functorEquivFunctorCompFstIso :
    (functorEquiv A A' B).functor ⋙ Prod.fst (A ⥤ B) (A' ⥤ B) ≅
    (whiskeringLeft A (A oplus A') B).obj (inl_ A A') :=
  NatIso.ofComponents (fun _ => Iso.refl _)

set_option backward.defeqAttrib.useBackward true in
/-- Composing the forward direction of `functorEquiv` with the second projection is the same as
precomposition with `inr_ A A'`. -/
@[simps!]
/--
Definition of `functorEquivFunctorCompSndIso` / `functorEquivFunctorCompSndIso` 的定义

English:
definition functorEquivFunctorCompSndIso
  signature: :
  body: NatIso.ofComponents (fun _ => Iso.refl _)

中文:
定义 functorEquivFunctorCompSndIso
  签名: :
  定义体: NatIso.ofComponents (fun _ => Iso.refl _)

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def functorEquivFunctorCompSndIso :
    (functorEquiv A A' B).functor ⋙ Prod.snd (A ⥤ B) (A' ⥤ B) ≅
    (whiskeringLeft A' (A oplus A') B).obj (inr_ A A') :=
  NatIso.ofComponents (fun _ => Iso.refl _)

set_option backward.defeqAttrib.useBackward true in
/-- Composing the backward direction of `functorEquiv` with precomposition with `inl_ A A'`.
is naturally isomorphic to the first projection. -/
@[simps!]
/--
Definition of `functorEquivInverseCompWhiskeringLeftInlIso` / `functorEquivInverseCompWhiskeringLeftInlIso` 的定义

English:
definition functorEquivInverseCompWhiskeringLeftInlIso
  signature: :
  body: NatIso.ofComponents (fun _ => Functor.inlCompSum' _ _)

中文:
定义 functorEquivInverseCompWhiskeringLeftInlIso
  签名: :
  定义体: NatIso.ofComponents (fun _ => Functor.inlCompSum' _ _)

Depends on / 依赖: Functor, Functor.inlCompSum, NatIso, NatIso.ofComponents, inlCompSum, ofComponents
-/
def functorEquivInverseCompWhiskeringLeftInlIso :
    (functorEquiv A A' B).inverse ⋙ (whiskeringLeft A (A oplus A') B).obj (inl_ A A') ≅
    Prod.fst (A ⥤ B) (A' ⥤ B) :=
  NatIso.ofComponents (fun _ => Functor.inlCompSum' _ _)

set_option backward.defeqAttrib.useBackward true in
/-- Composing the backward direction of `functorEquiv` with the second projection is the same as
precomposition with `inr_ A A'`. -/
@[simps!]
/--
Definition of `functorEquivInverseCompWhiskeringLeftInrIso` / `functorEquivInverseCompWhiskeringLeftInrIso` 的定义

English:
definition functorEquivInverseCompWhiskeringLeftInrIso
  signature: :
  body: NatIso.ofComponents (fun _ => Functor.inrCompSum' _ _)

#adaptation_note

中文:
定义 functorEquivInverseCompWhiskeringLeftInrIso
  签名: :
  定义体: NatIso.ofComponents (fun _ => Functor.inrCompSum' _ _)

#adaptation_note

Depends on / 依赖: Functor, Functor.inrCompSum, NatIso, NatIso.ofComponents, inrCompSum, ofComponents
-/
def functorEquivInverseCompWhiskeringLeftInrIso :
    (functorEquiv A A' B).inverse ⋙ (whiskeringLeft A' (A oplus A') B).obj (inr_ A A') ≅
    Prod.snd (A ⥤ B) (A' ⥤ B) :=
  NatIso.ofComponents (fun _ => Functor.inrCompSum' _ _)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- A consequence of `functorEquiv`: we can construct a natural transformation of functors
`A ⊕ A' ⥤ B` from the data of natural transformations of their whiskering with `inl_` and `inr_`. -/
@[simps!]
/--
Definition of `natTransOfWhiskerLeftInlInr` / `natTransOfWhiskerLeftInlInr` 的定义

English:
definition natTransOfWhiskerLeftInlInr
  signature: {F G : A oplus A' ⥤ B}
  body: (Sum.functorEquiv A A' B).unit.app F ≫
    (Sum.functorEquiv A A' B).inverse.map ((η₁, η₂) :) ≫
      (Sum.functorEquiv A A' B).unitInv.app G

中文:
定义 natTransOfWhiskerLeftInlInr
  签名: {F G : A oplus A' ⥤ B}
  定义体: (Sum.functorEquiv A A' B).unit.app F ≫
    (Sum.functorEquiv A A' B).inverse.map ((η₁, η₂) :) ≫
      (Sum.functorEquiv A A' B).unitInv.app G

Depends on / 依赖: Sum.functorEquiv, functorEquiv, inverse, inverse.map, unit.app, unitInv, unitInv.app
-/
def natTransOfWhiskerLeftInlInr {F G : A oplus A' ⥤ B}
    (η₁ : Sum.inl_ A A' ⋙ F ⟶ Sum.inl_ A A' ⋙ G) (η₂ : Sum.inr_ A A' ⋙ F ⟶ Sum.inr_ A A' ⋙ G) :
    F ⟶ G :=
  (Sum.functorEquiv A A' B).unit.app F ≫
    (Sum.functorEquiv A A' B).inverse.map ((η₁, η₂) :) ≫
      (Sum.functorEquiv A A' B).unitInv.app G

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `natTransOfWhiskerLeftInlInr_id` / 引理 `natTransOfWhiskerLeftInlInr_id`

English:
lemma natTransOfWhiskerLeftInlInr_id
  given: {F : A oplus A' ⥤ B}
  proof: by
  cat_disch

中文:
引理 natTransOfWhiskerLeftInlInr_id
  条件: {F : A oplus A' ⥤ B}
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma natTransOfWhiskerLeftInlInr_id {F : A oplus A' ⥤ B} :
    natTransOfWhiskerLeftInlInr (𝟙 (Sum.inl_ A A' ⋙ F)) (𝟙 (Sum.inr_ A A' ⋙ F)) = 𝟙 F := by
  cat_disch

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `natTransOfWhiskerLeftInlInr_comp` / 引理 `natTransOfWhiskerLeftInlInr_comp`

English:
lemma natTransOfWhiskerLeftInlInr_comp
  statement: {F G H : A oplus A' ⥤ B}
  proof: by
  cat_disch

中文:
引理 natTransOfWhiskerLeftInlInr_comp
  结论: {F G H : A oplus A' ⥤ B}
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma natTransOfWhiskerLeftInlInr_comp {F G H : A oplus A' ⥤ B}
    (η₁ : Sum.inl_ A A' ⋙ F ⟶ Sum.inl_ A A' ⋙ G) (η₂ : Sum.inr_ A A' ⋙ F ⟶ Sum.inr_ A A' ⋙ G)
    (ν₁ : Sum.inl_ A A' ⋙ G ⟶ Sum.inl_ A A' ⋙ H) (ν₂ : Sum.inr_ A A' ⋙ G ⟶ Sum.inr_ A A' ⋙ H) :
    natTransOfWhiskerLeftInlInr (η₁ ≫ ν₁) (η₂ ≫ ν₂) = natTransOfWhiskerLeftInlInr η₁ η₂ ≫
      natTransOfWhiskerLeftInlInr ν₁ ν₂ := by
  cat_disch

set_option backward.isDefEq.respectTransparency false in
/-- A consequence of `functorEquiv`: we can construct a natural isomorphism of functors
`A ⊕ A' ⥤ B` from the data of natural isomorphisms of their whiskering with `inl_` and `inr_`. -/
@[simps]
/--
Definition of `natIsoOfWhiskerLeftInlInr` / `natIsoOfWhiskerLeftInlInr` 的定义

English:
definition natIsoOfWhiskerLeftInlInr
  signature: {F G : A oplus A' ⥤ B}
  body: natTransOfWhiskerLeftInlInr η₁.hom η₂.hom
  inv := natTransOfWhiskerLeftInlInr η₁.inv η₂.inv

中文:
定义 natIsoOfWhiskerLeftInlInr
  签名: {F G : A oplus A' ⥤ B}
  定义体: natTransOfWhiskerLeftInlInr η₁.hom η₂.hom
  inv := natTransOfWhiskerLeftInlInr η₁.inv η₂.inv

Depends on / 依赖: natTransOfWhiskerLeftInlInr
-/
def natIsoOfWhiskerLeftInlInr {F G : A oplus A' ⥤ B}
    (η₁ : Sum.inl_ A A' ⋙ F ≅ Sum.inl_ A A' ⋙ G) (η₂ : Sum.inr_ A A' ⋙ F ≅ Sum.inr_ A A' ⋙ G) :
    F ≅ G where
  hom := natTransOfWhiskerLeftInlInr η₁.hom η₂.hom
  inv := natTransOfWhiskerLeftInlInr η₁.inv η₂.inv

/--
lemma `natIsoOfWhiskerLeftInlInr_eq` / 引理 `natIsoOfWhiskerLeftInlInr_eq`

English:
lemma natIsoOfWhiskerLeftInlInr_eq
  statement: {F G : A oplus A' ⥤ B}
  proof: by
  cat_disch

中文:
引理 natIsoOfWhiskerLeftInlInr_eq
  结论: {F G : A oplus A' ⥤ B}
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma natIsoOfWhiskerLeftInlInr_eq {F G : A oplus A' ⥤ B}
    (η₁ : Sum.inl_ A A' ⋙ F ≅ Sum.inl_ A A' ⋙ G) (η₂ : Sum.inr_ A A' ⋙ F ≅ Sum.inr_ A A' ⋙ G) :
    natIsoOfWhiskerLeftInlInr η₁ η₂ =
    (Sum.functorEquiv A A' B).unitIso.app _ ≪≫
      (Sum.functorEquiv A A' B).inverse.mapIso (Iso.prod η₁ η₂) ≪≫
      (Sum.functorEquiv A A' B).unitIso.symm.app _ := by
  cat_disch

namespace Swap

set_option backward.defeqAttrib.useBackward true in
/-- `functorEquiv A A' B` transforms `Swap.equivalence` into `Prod.braiding`. -/
@[simps! hom_app_fst hom_app_snd inv_app_fst inv_app_snd]
/--
Definition of `equivalenceFunctorEquivFunctorIso` / `equivalenceFunctorEquivFunctorIso` 的定义

English:
definition equivalenceFunctorEquivFunctorIso
  signature: :
  body: NatIso.ofComponents (fun E =>
    Iso.prod
      ((Functor.associator _ _ E).symm ≪≫ isoWhiskerRight (Sum.swapCompInl A' A) _)
      ((Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (Sum.swapCompInr A' A) _))

中文:
定义 equivalenceFunctorEquivFunctorIso
  签名: :
  定义体: NatIso.ofComponents (fun E =>
    Iso.prod
      ((Functor.associator _ _ E).symm ≪≫ isoWhiskerRight (Sum.swapCompInl A' A) _)
      ((Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (Sum.swapCompInr A' A) _))

Depends on / 依赖: Functor, Functor.associator, Iso.prod, NatIso, NatIso.ofComponents, Sum.swapCompInl, Sum.swapCompInr, associator, isoWhiskerRight, ofComponents, swapCompInl, swapCompInr
-/
def equivalenceFunctorEquivFunctorIso :
    ((equivalence A A').congrLeft.trans <| functorEquiv A' A B).functor ≅
      ((functorEquiv A A' B).trans <| Prod.braiding (A ⥤ B) (A' ⥤ B)).functor :=
  NatIso.ofComponents (fun E =>
    Iso.prod
      ((Functor.associator _ _ E).symm ≪≫ isoWhiskerRight (Sum.swapCompInl A' A) _)
      ((Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (Sum.swapCompInr A' A) _))

end Swap

section CompatibilityWithProductAssociator

variable (T : Type*) [Category* T]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The equivalence `Sum.functorEquiv` sends associativity of sums to associativity of products -/
@[simps! hom_app_fst hom_app_snd_fst hom_app_snd_snd inv_app_fst inv_app_snd_fst inv_app_snd_snd]
/--
Definition of `associativityFunctorEquivNaturalityFunctorIso` / `associativityFunctorEquivNaturalityFunctorIso` 的定义

English:
definition associativityFunctorEquivNaturalityFunctorIso
  signature: :
  body: (prod.associativity _ _ _)
  NatIso.ofComponents (fun E => Iso.prod
    ((Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (sum.inlCompInverseAssociator A A' T) E ≪≫ Functor.associator _ _ _)
    (Iso.prod
      (isoWhiskerLeft _ (Functor.associator _ _ E).symm ≪≫ (Functor.associator _ _ E).s

中文:
定义 associativityFunctorEquivNaturalityFunctorIso
  签名: :
  定义体: (prod.associativity _ _ _)
  NatIso.ofComponents (fun E => Iso.prod
    ((Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (sum.inlCompInverseAssociator A A' T) E ≪≫ Functor.associator _ _ _)
    (Iso.prod
      (isoWhiskerLeft _ (Functor.associator _ _ E).symm ≪≫ (Functor.associator _ _ E).s

Depends on / 依赖: associativity, prod.associativity
-/
def associativityFunctorEquivNaturalityFunctorIso :
    ((sum.associativity A A' T).congrLeft.trans <| (Sum.functorEquiv A (A' oplus T) B).trans <|
Equivalence.refl.prod Sum.functorEquiv _ _ B).functor ≅
        (Sum.functorEquiv (A oplus A') T B).trans
.trans ((Sum.functorEquiv A A' B).prod Equivalence.refl)
.functor := (prod.associativity _ _ _)
  NatIso.ofComponents (fun E => Iso.prod
    ((Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (sum.inlCompInverseAssociator A A' T) E ≪≫ Functor.associator _ _ _)
    (Iso.prod
      (isoWhiskerLeft _ (Functor.associator _ _ E).symm ≪≫ (Functor.associator _ _ E).symm ≪≫
        isoWhiskerRight (sum.inlCompInrCompInverseAssociator A A' T) E ≪≫ Functor.associator _ _ E)
      (isoWhiskerLeft _ (Functor.associator _ _ E).symm ≪≫ (Functor.associator _ _ E).symm ≪≫
        isoWhiskerRight (sum.inrCompInrCompInverseAssociator A A' T) E))) (by
      intros
      ext
      all_goals
        dsimp
        simp only [Category.comp_id, Category.id_comp, NatTrans.naturality])

end CompatibilityWithProductAssociator

end Sum

end CategoryTheory
