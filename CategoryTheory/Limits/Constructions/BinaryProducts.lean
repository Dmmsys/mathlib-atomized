/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Constructing binary product from pullbacks and terminal object.

The product is the pullback over the terminal objects. In particular, if a category
has pullbacks and a terminal object, then it has binary products.

We also provide the dual.
-/

@[expose] public section


universe v v' u u'

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] (F : C ⥤ D)

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isBinaryProductOfIsTerminalIsPullback` / `isBinaryProductOfIsTerminalIsPullback` 的定义

English:
definition isBinaryProductOfIsTerminalIsPullback
  signature: (F : Discrete WalkingPair ⥤ C) (c : Cone F) {X : C}
  body: hc.lift
      (PullbackCone.mk (s.π.app ⟨WalkingPair.left⟩) (s.π.app ⟨WalkingPair.right⟩) (hX.hom_ext _ _))
  fac _ j :=
    Discrete.casesOn j fun j =>
      WalkingPair.casesOn j (hc.fac _ WalkingCospan.left) (hc.fac _ WalkingCospan.right)
  uniq s m J := by
    let c' :=
      PullbackCone.mk (m 

中文:
定义 isBinaryProductOfIsTerminalIsPullback
  签名: (F : Discrete WalkingPair ⥤ C) (c : Cone F) {X : C}
  定义体: hc.lift
      (PullbackCone.mk (s.π.app ⟨WalkingPair.left⟩) (s.π.app ⟨WalkingPair.right⟩) (hX.hom_ext _ _))
  fac _ j :=
    Discrete.casesOn j fun j =>
      WalkingPair.casesOn j (hc.fac _ WalkingCospan.left) (hc.fac _ WalkingCospan.right)
  uniq s m J := by
    let c' :=
      PullbackCone.mk (m 

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Category.id_comp, Discrete, Discrete.casesOn, H.isLimit, IsLimit, IsLimit.equivOfNatIsoOfIso, Iso.refl, PullbackCone, PullbackCone.mk, PullbackCone.mk_, WalkingCospan, WalkingCospan.ext, WalkingCospan.left, WalkingCospan.right, WalkingPair, WalkingPair.casesOn, WalkingPair.left
-/
def isBinaryProductOfIsTerminalIsPullback (F : Discrete WalkingPair ⥤ C) (c : Cone F) {X : C}
    (hX : IsTerminal X) (f : F.obj ⟨WalkingPair.left⟩ ⟶ X) (g : F.obj ⟨WalkingPair.right⟩ ⟶ X)
    (hc : IsLimit
      (PullbackCone.mk (c.π.app ⟨WalkingPair.left⟩) (c.π.app ⟨WalkingPair.right⟩ :) <|
        hX.hom_ext (_ ≫ f) (_ ≫ g))) : IsLimit c where
  lift s :=
    hc.lift
      (PullbackCone.mk (s.π.app ⟨WalkingPair.left⟩) (s.π.app ⟨WalkingPair.right⟩) (hX.hom_ext _ _))
  fac _ j :=
    Discrete.casesOn j fun j =>
      WalkingPair.casesOn j (hc.fac _ WalkingCospan.left) (hc.fac _ WalkingCospan.right)
  uniq s m J := by
    let c' :=
      PullbackCone.mk (m ≫ c.π.app ⟨WalkingPair.left⟩) (m ≫ c.π.app ⟨WalkingPair.right⟩ :)
        (hX.hom_ext (_ ≫ f) (_ ≫ g))
    dsimp; rw [← J, ← J]
    apply hc.hom_ext
    rintro (_ | (_ | _)) <;> simp only [PullbackCone.mk_π_app]
    exacts [(Category.assoc _ _ _).symm.trans (hc.fac_assoc c' WalkingCospan.left f).symm,
      (hc.fac c' WalkingCospan.left).symm, (hc.fac c' WalkingCospan.right).symm]

/--
Definition of `isProductOfIsTerminalIsPullback` / `isProductOfIsTerminalIsPullback` 的定义

English:
definition isProductOfIsTerminalIsPullback
  signature: {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ X) (k : W ⟶ Y)
  body: by
  apply isBinaryProductOfIsTerminalIsPullback _ _ H₁
  exact H₂

中文:
定义 isProductOfIsTerminalIsPullback
  签名: {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ X) (k : W ⟶ Y)
  定义体: by
  apply isBinaryProductOfIsTerminalIsPullback _ _ H₁
  exact H₂

Depends on / 依赖: isBinaryProductOfIsTerminalIsPullback
-/
def isProductOfIsTerminalIsPullback {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ X) (k : W ⟶ Y)
    (H₁ : IsTerminal Z)
    (H₂ : IsLimit (PullbackCone.mk _ _ (show h ≫ f = k ≫ g from H₁.hom_ext _ _))) :
    IsLimit (BinaryFan.mk h k) := by
  apply isBinaryProductOfIsTerminalIsPullback _ _ H₁
  exact H₂

/--
Definition of `isPullbackOfIsTerminalIsProduct` / `isPullbackOfIsTerminalIsProduct` 的定义

English:
definition isPullbackOfIsTerminalIsProduct
  signature: {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ X) (k : W ⟶ Y)
  body: by
  apply PullbackCone.isLimitAux'
  intro s
  use BinaryFan.IsLimit.lift H₂ s.fst s.snd
  use BinaryFan.IsLimit.lift_fst _ _ _
  use BinaryFan.IsLimit.lift_snd _ _ _
  intro m h₁ h₂
  apply H₂.hom_ext
  rintro ⟨⟨⟩⟩
  · exact h₁.trans (H₂.fac (BinaryFan.mk s.fst s.snd) ⟨WalkingPair.left⟩).symm
  · 

中文:
定义 isPullbackOfIsTerminalIsProduct
  签名: {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ X) (k : W ⟶ Y)
  定义体: by
  apply PullbackCone.isLimitAux'
  intro s
  use BinaryFan.IsLimit.lift H₂ s.fst s.snd
  use BinaryFan.IsLimit.lift_fst _ _ _
  use BinaryFan.IsLimit.lift_snd _ _ _
  intro m h₁ h₂
  apply H₂.hom_ext
  rintro ⟨⟨⟩⟩
  · exact h₁.trans (H₂.fac (BinaryFan.mk s.fst s.snd) ⟨WalkingPair.left⟩).symm
  · 

Depends on / 依赖: BinaryFan, BinaryFan.IsLimit.lift, BinaryFan.IsLimit.lift_fst, BinaryFan.IsLimit.lift_snd, BinaryFan.mk, IsLimit, PullbackCone, PullbackCone.isLimitAux, WalkingPair, WalkingPair.left, WalkingPair.right, h.map, h.of_map, hom_ext, isLimitAux, lift_fst, lift_snd, of_map, s.fst, s.snd
-/
def isPullbackOfIsTerminalIsProduct {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ X) (k : W ⟶ Y)
    (H₁ : IsTerminal Z) (H₂ : IsLimit (BinaryFan.mk h k)) :
    IsLimit (PullbackCone.mk _ _ (show h ≫ f = k ≫ g from H₁.hom_ext _ _)) := by
  apply PullbackCone.isLimitAux'
  intro s
  use BinaryFan.IsLimit.lift H₂ s.fst s.snd
  use BinaryFan.IsLimit.lift_fst _ _ _
  use BinaryFan.IsLimit.lift_snd _ _ _
  intro m h₁ h₂
  apply H₂.hom_ext
  rintro ⟨⟨⟩⟩
  · exact h₁.trans (H₂.fac (BinaryFan.mk s.fst s.snd) ⟨WalkingPair.left⟩).symm
  · exact h₂.trans (H₂.fac (BinaryFan.mk s.fst s.snd) ⟨WalkingPair.right⟩).symm

/--
Definition of `limitConeOfTerminalAndPullbacks` / `limitConeOfTerminalAndPullbacks` 的定义

English:
definition limitConeOfTerminalAndPullbacks
  signature: [HasTerminal C] [HasPullbacks C]
  body: { pt :=
        pullback (terminal.from (F.obj ⟨WalkingPair.left⟩))
          (terminal.from (F.obj ⟨WalkingPair.right⟩))
      π :=
        Discrete.natTrans fun x =>
          Discrete.casesOn x fun x => WalkingPair.casesOn x (pullback.fst _ _) (pullback.snd _ _) }
  isLimit :=
    isBinaryProduct

中文:
定义 limitConeOfTerminalAndPullbacks
  签名: [HasTerminal C] [HasPullbacks C]
  定义体: { pt :=
        pullback (terminal.from (F.obj ⟨WalkingPair.left⟩))
          (terminal.from (F.obj ⟨WalkingPair.right⟩))
      π :=
        Discrete.natTrans fun x =>
          Discrete.casesOn x fun x => WalkingPair.casesOn x (pullback.fst _ _) (pullback.snd _ _) }
  isLimit :=
    isBinaryProduct

Depends on / 依赖: Category, Category.comp_id, Category.id_comp, Discrete, Discrete.casesOn, Discrete.natTrans, F.obj, H.isColimit, IsColimit, IsColimit.equivOfNatIsoOfIso, Iso.refl, WalkingPair, WalkingPair.casesOn, WalkingPair.left, WalkingPair.right, WalkingSpan, WalkingSpan.ext, casesOn, comp_id, equivOfNatIsoOfIso
-/
noncomputable def limitConeOfTerminalAndPullbacks [HasTerminal C] [HasPullbacks C]
    (F : Discrete WalkingPair ⥤ C) : LimitCone F where
  cone :=
    { pt :=
        pullback (terminal.from (F.obj ⟨WalkingPair.left⟩))
          (terminal.from (F.obj ⟨WalkingPair.right⟩))
      π :=
        Discrete.natTrans fun x =>
          Discrete.casesOn x fun x => WalkingPair.casesOn x (pullback.fst _ _) (pullback.snd _ _) }
  isLimit :=
    isBinaryProductOfIsTerminalIsPullback F _ terminalIsTerminal _ _ (pullbackIsPullback _ _)

variable (C) in
-- This is not an instance, as it is not always how one wants to construct binary products!
/--
theorem `hasBinaryProducts_of_hasTerminal_and_pullbacks` / 定理 `hasBinaryProducts_of_hasTerminal_and_pullbacks`

English:
theorem hasBinaryProducts_of_hasTerminal_and_pullbacks
  given: [HasTerminal C] [HasPullbacks C]
  proof: { has_limit := fun F => HasLimit.mk (limitConeOfTerminalAndPullbacks F) }

中文:
定理 hasBinaryProducts_of_hasTerminal_and_pullbacks
  条件: [HasTerminal C] [HasPullbacks C]
  证明: { has_limit := fun F => HasLimit.mk (limitConeOfTerminalAndPullbacks F) }

Depends on / 依赖: HasLimit, HasLimit.mk, has_limit, limitConeOfTerminalAndPullbacks
-/
theorem hasBinaryProducts_of_hasTerminal_and_pullbacks [HasTerminal C] [HasPullbacks C] :
    HasBinaryProducts C :=
  { has_limit := fun F => HasLimit.mk (limitConeOfTerminalAndPullbacks F) }

/--
lemma `preservesBinaryProducts_of_preservesTerminal_and_pullbacks` / 引理 `preservesBinaryProducts_of_preservesTerminal_and_pullbacks`

English:
lemma preservesBinaryProducts_of_preservesTerminal_and_pullbacks
  statement: [HasTerminal C]
  proof: ⟨fun {K} =>
    preservesLimit_of_preserves_limit_cone (limitConeOfTerminalAndPullbacks K).2
      (by
        apply
          isBinaryProductOfIsTerminalIsPullback _ _ (isLimitOfHasTerminalOfPreservesLimit F)
        apply isLimitOfHasPullbackOfPreservesLimit)⟩

中文:
引理 preservesBinaryProducts_of_preservesTerminal_and_pullbacks
  结论: [HasTerminal C]
  证明: ⟨fun {K} =>
    preservesLimit_of_preserves_limit_cone (limitConeOfTerminalAndPullbacks K).2
      (by
        apply
          isBinaryProductOfIsTerminalIsPullback _ _ (isLimitOfHasTerminalOfPreservesLimit F)
        apply isLimitOfHasPullbackOfPreservesLimit)⟩

Depends on / 依赖: h.map, h.of_map, isBinaryProductOfIsTerminalIsPullback, isLimitOfHasPullbackOfPreservesLimit, isLimitOfHasTerminalOfPreservesLimit, limitConeOfTerminalAndPullbacks, of_map, preservesLimit_of_preserves_limit_cone
-/
lemma preservesBinaryProducts_of_preservesTerminal_and_pullbacks [HasTerminal C]
    [HasPullbacks C] [PreservesLimitsOfShape (Discrete.{0} PEmpty) F]
    [PreservesLimitsOfShape WalkingCospan F] : PreservesLimitsOfShape (Discrete WalkingPair) F :=
  ⟨fun {K} =>
    preservesLimit_of_preserves_limit_cone (limitConeOfTerminalAndPullbacks K).2
      (by
        apply
          isBinaryProductOfIsTerminalIsPullback _ _ (isLimitOfHasTerminalOfPreservesLimit F)
        apply isLimitOfHasPullbackOfPreservesLimit)⟩

/--
Definition of `prodIsoPullback` / `prodIsoPullback` 的定义

English:
definition prodIsoPullback
  signature: [HasTerminal C] [HasPullbacks C] (X Y : C)
  body: limit.isoLimitCone (limitConeOfTerminalAndPullbacks _)

@[reassoc (attr := simp)]

中文:
定义 prodIsoPullback
  签名: [HasTerminal C] [HasPullbacks C] (X Y : C)
  定义体: limit.isoLimitCone (limitConeOfTerminalAndPullbacks _)

@[reassoc (attr := simp)]

Depends on / 依赖: isoLimitCone, limit.isoLimitCone, limitConeOfTerminalAndPullbacks
-/
noncomputable def prodIsoPullback [HasTerminal C] [HasPullbacks C] (X Y : C)
    [HasBinaryProduct X Y] : X ⨯ Y ≅ pullback (terminal.from X) (terminal.from Y) :=
  limit.isoLimitCone (limitConeOfTerminalAndPullbacks _)

@[reassoc (attr := simp)]
/--
lemma `prodIsoPullback_hom_fst` / 引理 `prodIsoPullback_hom_fst`

English:
lemma prodIsoPullback_hom_fst
  statement: [HasTerminal C] [HasPullbacks C] (X Y : C)
  proof: limit.isoLimitCone_hom_π (limitConeOfTerminalAndPullbacks _) ⟨.left⟩

@[reassoc (attr := simp)]

中文:
引理 prodIsoPullback_hom_fst
  结论: [HasTerminal C] [HasPullbacks C] (X Y : C)
  证明: limit.isoLimitCone_hom_π (limitConeOfTerminalAndPullbacks _) ⟨.left⟩

@[reassoc (attr := simp)]

Depends on / 依赖: limit.isoLimitCone_hom_, limitConeOfTerminalAndPullbacks
-/
lemma prodIsoPullback_hom_fst [HasTerminal C] [HasPullbacks C] (X Y : C)
    [HasBinaryProduct X Y] : (prodIsoPullback X Y).hom ≫ pullback.fst _ _ = prod.fst :=
  limit.isoLimitCone_hom_π (limitConeOfTerminalAndPullbacks _) ⟨.left⟩

@[reassoc (attr := simp)]
/--
lemma `prodIsoPullback_hom_snd` / 引理 `prodIsoPullback_hom_snd`

English:
lemma prodIsoPullback_hom_snd
  statement: [HasTerminal C] [HasPullbacks C] (X Y : C)
  proof: limit.isoLimitCone_hom_π (limitConeOfTerminalAndPullbacks _) ⟨.right⟩

@[reassoc (attr := simp)]

中文:
引理 prodIsoPullback_hom_snd
  结论: [HasTerminal C] [HasPullbacks C] (X Y : C)
  证明: limit.isoLimitCone_hom_π (limitConeOfTerminalAndPullbacks _) ⟨.right⟩

@[reassoc (attr := simp)]

Depends on / 依赖: limit.isoLimitCone_hom_, limitConeOfTerminalAndPullbacks
-/
lemma prodIsoPullback_hom_snd [HasTerminal C] [HasPullbacks C] (X Y : C)
    [HasBinaryProduct X Y] : (prodIsoPullback X Y).hom ≫ pullback.snd _ _ = prod.snd :=
  limit.isoLimitCone_hom_π (limitConeOfTerminalAndPullbacks _) ⟨.right⟩

@[reassoc (attr := simp)]
/--
lemma `prodIsoPullback_inv_fst` / 引理 `prodIsoPullback_inv_fst`

English:
lemma prodIsoPullback_inv_fst
  statement: [HasTerminal C] [HasPullbacks C] (X Y : C)
  proof: limit.isoLimitCone_inv_π (limitConeOfTerminalAndPullbacks _) ⟨.left⟩

@[reassoc (attr := simp)]

中文:
引理 prodIsoPullback_inv_fst
  结论: [HasTerminal C] [HasPullbacks C] (X Y : C)
  证明: limit.isoLimitCone_inv_π (limitConeOfTerminalAndPullbacks _) ⟨.left⟩

@[reassoc (attr := simp)]

Depends on / 依赖: limit.isoLimitCone_inv_, limitConeOfTerminalAndPullbacks
-/
lemma prodIsoPullback_inv_fst [HasTerminal C] [HasPullbacks C] (X Y : C)
    [HasBinaryProduct X Y] : (prodIsoPullback X Y).inv ≫ prod.fst = pullback.fst _ _ :=
  limit.isoLimitCone_inv_π (limitConeOfTerminalAndPullbacks _) ⟨.left⟩

@[reassoc (attr := simp)]
/--
lemma `prodIsoPullback_inv_snd` / 引理 `prodIsoPullback_inv_snd`

English:
lemma prodIsoPullback_inv_snd
  statement: [HasTerminal C] [HasPullbacks C] (X Y : C)
  proof: limit.isoLimitCone_inv_π (limitConeOfTerminalAndPullbacks _) ⟨.right⟩

中文:
引理 prodIsoPullback_inv_snd
  结论: [HasTerminal C] [HasPullbacks C] (X Y : C)
  证明: limit.isoLimitCone_inv_π (limitConeOfTerminalAndPullbacks _) ⟨.right⟩

Depends on / 依赖: limit.isoLimitCone_inv_, limitConeOfTerminalAndPullbacks
-/
lemma prodIsoPullback_inv_snd [HasTerminal C] [HasPullbacks C] (X Y : C)
    [HasBinaryProduct X Y] : (prodIsoPullback X Y).inv ≫ prod.snd = pullback.snd _ _ :=
  limit.isoLimitCone_inv_π (limitConeOfTerminalAndPullbacks _) ⟨.right⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isBinaryCoproductOfIsInitialIsPushout` / `isBinaryCoproductOfIsInitialIsPushout` 的定义

English:
definition isBinaryCoproductOfIsInitialIsPushout
  signature: (F : Discrete WalkingPair ⥤ C) (c : Cocone F) {X : C}
  body: hc.desc
      (PushoutCocone.mk (s.ι.app ⟨WalkingPair.left⟩) (s.ι.app ⟨WalkingPair.right⟩) (hX.hom_ext _ _))
  fac _ j :=
    Discrete.casesOn j fun j =>
      WalkingPair.casesOn j (hc.fac _ WalkingSpan.left) (hc.fac _ WalkingSpan.right)
  uniq s m J := by
    let c' :=
      PushoutCocone.mk (c.ι.

中文:
定义 isBinaryCoproductOfIsInitialIsPushout
  签名: (F : Discrete WalkingPair ⥤ C) (c : Cocone F) {X : C}
  定义体: hc.desc
      (PushoutCocone.mk (s.ι.app ⟨WalkingPair.left⟩) (s.ι.app ⟨WalkingPair.right⟩) (hX.hom_ext _ _))
  fac _ j :=
    Discrete.casesOn j fun j =>
      WalkingPair.casesOn j (hc.fac _ WalkingSpan.left) (hc.fac _ WalkingSpan.right)
  uniq s m J := by
    let c' :=
      PushoutCocone.mk (c.ι.

Depends on / 依赖: Category, Category.assoc, Discrete, Discrete.casesOn, PushoutCocone, PushoutCocone.mk, PushoutCocone.mk_, WalkingPair, WalkingPair.casesOn, WalkingPair.left, WalkingPair.right, WalkingSpan, WalkingSpan.left, WalkingSpan.right, casesOn, hX.hom_ext, hc.desc, hc.fac, hc.hom_ext, hom_ext
-/
def isBinaryCoproductOfIsInitialIsPushout (F : Discrete WalkingPair ⥤ C) (c : Cocone F) {X : C}
    (hX : IsInitial X) (f : X ⟶ F.obj ⟨WalkingPair.left⟩) (g : X ⟶ F.obj ⟨WalkingPair.right⟩)
    (hc :
      IsColimit
        (PushoutCocone.mk (c.ι.app ⟨WalkingPair.left⟩) (c.ι.app ⟨WalkingPair.right⟩ :) <|
          hX.hom_ext (f ≫ _) (g ≫ _))) :
    IsColimit c where
  desc s :=
    hc.desc
      (PushoutCocone.mk (s.ι.app ⟨WalkingPair.left⟩) (s.ι.app ⟨WalkingPair.right⟩) (hX.hom_ext _ _))
  fac _ j :=
    Discrete.casesOn j fun j =>
      WalkingPair.casesOn j (hc.fac _ WalkingSpan.left) (hc.fac _ WalkingSpan.right)
  uniq s m J := by
    let c' :=
      PushoutCocone.mk (c.ι.app ⟨WalkingPair.left⟩ ≫ m) (c.ι.app ⟨WalkingPair.right⟩ ≫ m)
        (hX.hom_ext (f ≫ _) (g ≫ _))
    dsimp; rw [← J, ← J]
    apply hc.hom_ext
    rintro (_ | (_ | _)) <;>
      simp only [PushoutCocone.mk_ι_app, Category.assoc]
    on_goal 1 => congr 1
    exacts [(hc.fac c' WalkingSpan.left).symm, (hc.fac c' WalkingSpan.left).symm,
      (hc.fac c' WalkingSpan.right).symm]

/--
Definition of `isCoproductOfIsInitialIsPushout` / `isCoproductOfIsInitialIsPushout` 的定义

English:
definition isCoproductOfIsInitialIsPushout
  signature: {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ X) (k : W ⟶ Y)
  body: by
  apply isBinaryCoproductOfIsInitialIsPushout _ _ H₁
  exact H₂

中文:
定义 isCoproductOfIsInitialIsPushout
  签名: {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ X) (k : W ⟶ Y)
  定义体: by
  apply isBinaryCoproductOfIsInitialIsPushout _ _ H₁
  exact H₂

Depends on / 依赖: isBinaryCoproductOfIsInitialIsPushout
-/
def isCoproductOfIsInitialIsPushout {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ X) (k : W ⟶ Y)
    (H₁ : IsInitial W)
    (H₂ : IsColimit (PushoutCocone.mk _ _ (show h ≫ f = k ≫ g from H₁.hom_ext _ _))) :
    IsColimit (BinaryCofan.mk f g) := by
  apply isBinaryCoproductOfIsInitialIsPushout _ _ H₁
  exact H₂

/--
Definition of `isPushoutOfIsInitialIsCoproduct` / `isPushoutOfIsInitialIsCoproduct` 的定义

English:
definition isPushoutOfIsInitialIsCoproduct
  signature: {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ X) (k : W ⟶ Y)
  body: by
  apply PushoutCocone.isColimitAux'
  intro s
  use BinaryCofan.IsColimit.desc H₂ s.inl s.inr
  use BinaryCofan.IsColimit.inl_desc H₂ _ _
  use BinaryCofan.IsColimit.inr_desc H₂ _ _
  intro m h₁ h₂
  apply H₂.hom_ext
  rintro ⟨⟨⟩⟩
  · exact h₁.trans (H₂.fac (BinaryCofan.mk s.inl s.inr) ⟨WalkingPa

中文:
定义 isPushoutOfIsInitialIsCoproduct
  签名: {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ X) (k : W ⟶ Y)
  定义体: by
  apply PushoutCocone.isColimitAux'
  intro s
  use BinaryCofan.IsColimit.desc H₂ s.inl s.inr
  use BinaryCofan.IsColimit.inl_desc H₂ _ _
  use BinaryCofan.IsColimit.inr_desc H₂ _ _
  intro m h₁ h₂
  apply H₂.hom_ext
  rintro ⟨⟨⟩⟩
  · exact h₁.trans (H₂.fac (BinaryCofan.mk s.inl s.inr) ⟨WalkingPa

Depends on / 依赖: BinaryCofan, BinaryCofan.IsColimit.desc, BinaryCofan.IsColimit.inl_desc, BinaryCofan.IsColimit.inr_desc, BinaryCofan.mk, IsColimit, PushoutCocone, PushoutCocone.isColimitAux, WalkingPair, WalkingPair.left, WalkingPair.right, hom_ext, inl_desc, inr_desc, isColimitAux, s.inl, s.inr
-/
def isPushoutOfIsInitialIsCoproduct {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ X) (k : W ⟶ Y)
    (H₁ : IsInitial W) (H₂ : IsColimit (BinaryCofan.mk f g)) :
    IsColimit (PushoutCocone.mk _ _ (show h ≫ f = k ≫ g from H₁.hom_ext _ _)) := by
  apply PushoutCocone.isColimitAux'
  intro s
  use BinaryCofan.IsColimit.desc H₂ s.inl s.inr
  use BinaryCofan.IsColimit.inl_desc H₂ _ _
  use BinaryCofan.IsColimit.inr_desc H₂ _ _
  intro m h₁ h₂
  apply H₂.hom_ext
  rintro ⟨⟨⟩⟩
  · exact h₁.trans (H₂.fac (BinaryCofan.mk s.inl s.inr) ⟨WalkingPair.left⟩).symm
  · exact h₂.trans (H₂.fac (BinaryCofan.mk s.inl s.inr) ⟨WalkingPair.right⟩).symm

/--
Definition of `colimitCoconeOfInitialAndPushouts` / `colimitCoconeOfInitialAndPushouts` 的定义

English:
definition colimitCoconeOfInitialAndPushouts
  signature: [HasInitial C] [HasPushouts C]
  body: { pt := pushout (initial.to (F.obj ⟨WalkingPair.left⟩)) (initial.to (F.obj ⟨WalkingPair.right⟩))
      ι :=
        Discrete.natTrans fun x =>
          Discrete.casesOn x fun x => WalkingPair.casesOn x (pushout.inl _ _) (pushout.inr _ _) }
  isColimit := isBinaryCoproductOfIsInitialIsPushout F _ in

中文:
定义 colimitCoconeOfInitialAndPushouts
  签名: [HasInitial C] [HasPushouts C]
  定义体: { pt := pushout (initial.to (F.obj ⟨WalkingPair.left⟩)) (initial.to (F.obj ⟨WalkingPair.right⟩))
      ι :=
        Discrete.natTrans fun x =>
          Discrete.casesOn x fun x => WalkingPair.casesOn x (pushout.inl _ _) (pushout.inr _ _) }
  isColimit := isBinaryCoproductOfIsInitialIsPushout F _ in

Depends on / 依赖: Discrete, Discrete.casesOn, Discrete.natTrans, F.obj, WalkingPair, WalkingPair.casesOn, WalkingPair.left, WalkingPair.right, casesOn, initial, initial.to, initialIsInitial, isBinaryCoproductOfIsInitialIsPushout, isColimit, natTrans, pushout, pushout.inl, pushout.inr, pushoutIsPushout
-/
noncomputable def colimitCoconeOfInitialAndPushouts [HasInitial C] [HasPushouts C]
    (F : Discrete WalkingPair ⥤ C) : ColimitCocone F where
  cocone :=
    { pt := pushout (initial.to (F.obj ⟨WalkingPair.left⟩)) (initial.to (F.obj ⟨WalkingPair.right⟩))
      ι :=
        Discrete.natTrans fun x =>
          Discrete.casesOn x fun x => WalkingPair.casesOn x (pushout.inl _ _) (pushout.inr _ _) }
  isColimit := isBinaryCoproductOfIsInitialIsPushout F _ initialIsInitial _ _ (pushoutIsPushout _ _)

variable (C) in
-- This is not an instance, as it is not always how one wants to construct binary coproducts!
/--
theorem `hasBinaryCoproducts_of_hasInitial_and_pushouts` / 定理 `hasBinaryCoproducts_of_hasInitial_and_pushouts`

English:
theorem hasBinaryCoproducts_of_hasInitial_and_pushouts
  given: [HasInitial C] [HasPushouts C]
  proof: { has_colimit := fun F => HasColimit.mk (colimitCoconeOfInitialAndPushouts F) }

中文:
定理 hasBinaryCoproducts_of_hasInitial_and_pushouts
  条件: [HasInitial C] [HasPushouts C]
  证明: { has_colimit := fun F => HasColimit.mk (colimitCoconeOfInitialAndPushouts F) }

Depends on / 依赖: HasColimit, HasColimit.mk, colimitCoconeOfInitialAndPushouts, has_colimit
-/
theorem hasBinaryCoproducts_of_hasInitial_and_pushouts [HasInitial C] [HasPushouts C] :
    HasBinaryCoproducts C :=
  { has_colimit := fun F => HasColimit.mk (colimitCoconeOfInitialAndPushouts F) }

/--
lemma `preservesBinaryCoproducts_of_preservesInitial_and_pushouts` / 引理 `preservesBinaryCoproducts_of_preservesInitial_and_pushouts`

English:
lemma preservesBinaryCoproducts_of_preservesInitial_and_pushouts
  statement: [HasInitial C]
  proof: ⟨fun {K} =>
    preservesColimit_of_preserves_colimit_cocone (colimitCoconeOfInitialAndPushouts K).2 (by
      apply
        isBinaryCoproductOfIsInitialIsPushout _ _
          (isColimitOfHasInitialOfPreservesColimit F)
      apply isColimitOfHasPushoutOfPreservesColimit)⟩

中文:
引理 preservesBinaryCoproducts_of_preservesInitial_and_pushouts
  结论: [HasInitial C]
  证明: ⟨fun {K} =>
    preservesColimit_of_preserves_colimit_cocone (colimitCoconeOfInitialAndPushouts K).2 (by
      apply
        isBinaryCoproductOfIsInitialIsPushout _ _
          (isColimitOfHasInitialOfPreservesColimit F)
      apply isColimitOfHasPushoutOfPreservesColimit)⟩

Depends on / 依赖: colimitCoconeOfInitialAndPushouts, isBinaryCoproductOfIsInitialIsPushout, isColimitOfHasInitialOfPreservesColimit, isColimitOfHasPushoutOfPreservesColimit, preservesColimit_of_preserves_colimit_cocone
-/
lemma preservesBinaryCoproducts_of_preservesInitial_and_pushouts [HasInitial C]
    [HasPushouts C] [PreservesColimitsOfShape (Discrete.{0} PEmpty) F]
    [PreservesColimitsOfShape WalkingSpan F] : PreservesColimitsOfShape (Discrete WalkingPair) F :=
  ⟨fun {K} =>
    preservesColimit_of_preserves_colimit_cocone (colimitCoconeOfInitialAndPushouts K).2 (by
      apply
        isBinaryCoproductOfIsInitialIsPushout _ _
          (isColimitOfHasInitialOfPreservesColimit F)
      apply isColimitOfHasPushoutOfPreservesColimit)⟩

/--
Definition of `coprodIsoPushout` / `coprodIsoPushout` 的定义

English:
definition coprodIsoPushout
  signature: [HasInitial C] [HasPushouts C] (X Y : C)
  body: colimit.isoColimitCocone (colimitCoconeOfInitialAndPushouts _)

@[reassoc (attr := simp)]

中文:
定义 coprodIsoPushout
  签名: [HasInitial C] [HasPushouts C] (X Y : C)
  定义体: colimit.isoColimitCocone (colimitCoconeOfInitialAndPushouts _)

@[reassoc (attr := simp)]

Depends on / 依赖: colimit, colimit.isoColimitCocone, colimitCoconeOfInitialAndPushouts, isoColimitCocone
-/
noncomputable def coprodIsoPushout [HasInitial C] [HasPushouts C] (X Y : C)
    [HasBinaryCoproduct X Y] : X ⨿ Y ≅ pushout (initial.to X) (initial.to Y) :=
  colimit.isoColimitCocone (colimitCoconeOfInitialAndPushouts _)

@[reassoc (attr := simp)]
/--
lemma `inl_coprodIsoPushout_hom` / 引理 `inl_coprodIsoPushout_hom`

English:
lemma inl_coprodIsoPushout_hom
  statement: [HasInitial C] [HasPushouts C] (X Y : C)
  proof: colimit.isoColimitCocone_ι_hom (colimitCoconeOfInitialAndPushouts _) _

@[reassoc (attr := simp)]

中文:
引理 inl_coprodIsoPushout_hom
  结论: [HasInitial C] [HasPushouts C] (X Y : C)
  证明: colimit.isoColimitCocone_ι_hom (colimitCoconeOfInitialAndPushouts _) _

@[reassoc (attr := simp)]

Depends on / 依赖: Discrete, PreservesLimitsOfShape, WalkingPair, colimit, colimit.isoColimitCocone_, colimitCoconeOfInitialAndPushouts
-/
lemma inl_coprodIsoPushout_hom [HasInitial C] [HasPushouts C] (X Y : C)
    [HasBinaryCoproduct X Y] : coprod.inl ≫ (coprodIsoPushout X Y).hom = pushout.inl _ _ :=
  colimit.isoColimitCocone_ι_hom (colimitCoconeOfInitialAndPushouts _) _

@[reassoc (attr := simp)]
/--
lemma `inr_coprodIsoPushout_hom` / 引理 `inr_coprodIsoPushout_hom`

English:
lemma inr_coprodIsoPushout_hom
  statement: [HasInitial C] [HasPushouts C] (X Y : C)
  proof: colimit.isoColimitCocone_ι_hom (colimitCoconeOfInitialAndPushouts _) _

@[reassoc (attr := simp)]

中文:
引理 inr_coprodIsoPushout_hom
  结论: [HasInitial C] [HasPushouts C] (X Y : C)
  证明: colimit.isoColimitCocone_ι_hom (colimitCoconeOfInitialAndPushouts _) _

@[reassoc (attr := simp)]

Depends on / 依赖: Discrete, PreservesColimitsOfShape, WalkingPair, colimit, colimit.isoColimitCocone_, colimitCoconeOfInitialAndPushouts
-/
lemma inr_coprodIsoPushout_hom [HasInitial C] [HasPushouts C] (X Y : C)
    [HasBinaryCoproduct X Y] : coprod.inr ≫ (coprodIsoPushout X Y).hom = pushout.inr _ _ :=
  colimit.isoColimitCocone_ι_hom (colimitCoconeOfInitialAndPushouts _) _

@[reassoc (attr := simp)]
/--
lemma `inl_coprodIsoPushout_inv` / 引理 `inl_coprodIsoPushout_inv`

English:
lemma inl_coprodIsoPushout_inv
  statement: [HasInitial C] [HasPushouts C] (X Y : C)
  proof: colimit.isoColimitCocone_ι_inv (colimitCoconeOfInitialAndPushouts (pair X Y)) ⟨.left⟩

@[reassoc (attr := simp)]

中文:
引理 inl_coprodIsoPushout_inv
  结论: [HasInitial C] [HasPushouts C] (X Y : C)
  证明: colimit.isoColimitCocone_ι_inv (colimitCoconeOfInitialAndPushouts (pair X Y)) ⟨.left⟩

@[reassoc (attr := simp)]

Depends on / 依赖: colimit, colimit.isoColimitCocone_, colimitCoconeOfInitialAndPushouts
-/
lemma inl_coprodIsoPushout_inv [HasInitial C] [HasPushouts C] (X Y : C)
    [HasBinaryCoproduct X Y] : pushout.inl _ _ ≫ (coprodIsoPushout X Y).inv = coprod.inl :=
  colimit.isoColimitCocone_ι_inv (colimitCoconeOfInitialAndPushouts (pair X Y)) ⟨.left⟩

@[reassoc (attr := simp)]
/--
lemma `inr_coprodIsoPushout_inv` / 引理 `inr_coprodIsoPushout_inv`

English:
lemma inr_coprodIsoPushout_inv
  statement: [HasInitial C] [HasPushouts C] (X Y : C)
  proof: colimit.isoColimitCocone_ι_inv (colimitCoconeOfInitialAndPushouts (pair X Y)) ⟨.right⟩

中文:
引理 inr_coprodIsoPushout_inv
  结论: [HasInitial C] [HasPushouts C] (X Y : C)
  证明: colimit.isoColimitCocone_ι_inv (colimitCoconeOfInitialAndPushouts (pair X Y)) ⟨.right⟩

Depends on / 依赖: colimit, colimit.isoColimitCocone_, colimitCoconeOfInitialAndPushouts
-/
lemma inr_coprodIsoPushout_inv [HasInitial C] [HasPushouts C] (X Y : C)
    [HasBinaryCoproduct X Y] : pushout.inr _ _ ≫ (coprodIsoPushout X Y).inv = coprod.inr :=
  colimit.isoColimitCocone_ι_inv (colimitCoconeOfInitialAndPushouts (pair X Y)) ⟨.right⟩
