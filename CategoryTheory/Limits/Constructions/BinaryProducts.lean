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
/-- If a span is the pullback span over the terminal object, then it is a binary product. -/
/-
**isBinaryProductOfIsTerminalIsPullback** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：isBinaryProductOfIsTerminalIsPullback (F : Discrete WalkingPair ⥤ C) (c : 
Cone F) {X : C} (hX : IsTerminal X) (f : F.obj ⟨WalkingPair.left⟩ ⟶ X) (g : F.ob
j ⟨WalkingPair.right⟩ ⟶ X) (hc : IsLimit (PullbackCone.mk (c.π.app ⟨WalkingPair.
left⟩) (c.π.app ⟨WalkingPair.right⟩ :) <| hX.hom_ext (_ ≫ f) (_ ≫ g))) : IsLimit
 c where lift s
参数：F : Discrete WalkingPair ⥤ C；c : Cone F；hX : IsTerminal X；f : F.obj ⟨WalkingP
air.left⟩ ⟶ X；g : F.obj ⟨WalkingPair.right⟩ ⟶ X；hc : IsLimit (PullbackCone.mk (c
.π.app ⟨WalkingPair.left⟩) (c.π.app ⟨WalkingPair.right⟩ :) <| hX.hom_ext (_ ≫ f)
 (_ ≫ g))。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a span is the pullback span over the terminal object, then it is a binary pro
duct.
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

/-- The pullback over the terminal object is the product -/
/-
**isProductOfIsTerminalIsPullback** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：isProductOfIsTerminalIsPullback {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h :
 W ⟶ X) (k : W ⟶ Y) (H₁ : IsTerminal Z) (H₂ : IsLimit (PullbackCone.mk _ _ (show
 h ≫ f = k ≫ g from H₁.hom_ext _ _))) : IsLimit (BinaryFan.mk h k)
参数：f : X ⟶ Z；g : Y ⟶ Z；h : W ⟶ X；k : W ⟶ Y；H₁ : IsTerminal Z；H₂ : IsLimit (Pullb
ackCone.mk _ _ (show h ≫ f = k ≫ g from H₁.hom_ext _ _))。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback over the terminal object is the product
-/
def isProductOfIsTerminalIsPullback {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ X) (k : W ⟶ Y)
    (H₁ : IsTerminal Z)
    (H₂ : IsLimit (PullbackCone.mk _ _ (show h ≫ f = k ≫ g from H₁.hom_ext _ _))) :
    IsLimit (BinaryFan.mk h k) := by
  apply isBinaryProductOfIsTerminalIsPullback _ _ H₁
  exact H₂

/-- The product is the pullback over the terminal object. -/
/-
**isPullbackOfIsTerminalIsProduct** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：isPullbackOfIsTerminalIsProduct {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h :
 W ⟶ X) (k : W ⟶ Y) (H₁ : IsTerminal Z) (H₂ : IsLimit (BinaryFan.mk h k)) : IsLi
mit (PullbackCone.mk _ _ (show h ≫ f = k ≫ g from H₁.hom_ext _ _))
参数：f : X ⟶ Z；g : Y ⟶ Z；h : W ⟶ X；k : W ⟶ Y；H₁ : IsTerminal Z；H₂ : IsLimit (Binar
yFan.mk h k)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product is the pullback over the terminal object.
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

/-- Any category with pullbacks and a terminal object has a limit cone for each walking pair. -/
/-
**limitConeOfTerminalAndPullbacks** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：limitConeOfTerminalAndPullbacks [HasTerminal C] [HasPullbacks C] (F : Disc
rete WalkingPair ⥤ C) : LimitCone F where cone
参数：F : Discrete WalkingPair ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any category with pullbacks and a terminal object has a limit cone for each walk
ing pair.
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
/-- Any category with pullbacks and terminal object has binary products. -/
/-
**hasBinaryProducts_of_hasTerminal_and_pullbacks** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasBinaryProducts_of_hasTerminal_and_pullbacks [HasTerminal C] [HasPullbac
ks C] : HasBinaryProducts C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…

--- 原说明 ---
Any category with pullbacks and terminal object has binary products.
-/
theorem hasBinaryProducts_of_hasTerminal_and_pullbacks [HasTerminal C] [HasPullbacks C] :
    HasBinaryProducts C :=
  { has_limit := fun F => HasLimit.mk (limitConeOfTerminalAndPullbacks F) }

/-- A functor that preserves terminal objects and pullbacks preserves binary products. -/
/-
**preservesBinaryProducts_of_preservesTerminal_and_pullbacks** 是 Mathlib 中的一个引理，
位于命名空间 ``。
形式化陈述：preservesBinaryProducts_of_preservesTerminal_and_pullbacks [HasTerminal C]
 [HasPullbacks C] [PreservesLimitsOfShape (Discrete.{0} PEmpty) F] [PreservesLim
itsOfShape WalkingCospan F] : PreservesLimitsOfShape (Discrete WalkingPair) F
参数：Discrete.{0} PEmpty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone`：preservesL
imit_of_preserves_limit_cone {F : C ⥤ D} {t : Cone K} (h : IsLimit t) (hF : IsLi
mit (F.mapCone t)) : PreservesLimit K F where pres…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
A functor that preserves terminal objects and pullbacks preserves binary product
s.
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

/-- In a category with a terminal object and pullbacks,
a product of objects `X` and `Y` is isomorphic to a pullback. -/
/-
**prodIsoPullback** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：prodIsoPullback [HasTerminal C] [HasPullbacks C] (X Y : C) [HasBinaryProdu
ct X Y] : X ⨯ Y ≅ pullback (terminal.from X) (terminal.from Y)
参数：X Y : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a category with a terminal object and pullbacks,
a product of objects `X` and `Y` is isomorphic to a pullback.
-/
noncomputable def prodIsoPullback [HasTerminal C] [HasPullbacks C] (X Y : C)
    [HasBinaryProduct X Y] : X ⨯ Y ≅ pullback (terminal.from X) (terminal.from Y) :=
  limit.isoLimitCone (limitConeOfTerminalAndPullbacks _)

@[reassoc (attr := simp)]
/-
**prodIsoPullback_hom_fst** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：prodIsoPullback_hom_fst [HasTerminal C] [HasPullbacks C] (X Y : C) [HasBin
aryProduct X Y] : (prodIsoPullback X Y).hom ≫ pullback.fst _ _ = prod.fst
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.isoLimitCone_hom_π`：∀ {J : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Catego
ry.{v, u} C]   {F : CategoryTheory.F…
-/
lemma prodIsoPullback_hom_fst [HasTerminal C] [HasPullbacks C] (X Y : C)
    [HasBinaryProduct X Y] : (prodIsoPullback X Y).hom ≫ pullback.fst _ _ = prod.fst :=
  limit.isoLimitCone_hom_π (limitConeOfTerminalAndPullbacks _) ⟨.left⟩

@[reassoc (attr := simp)]
/-
**prodIsoPullback_hom_snd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：prodIsoPullback_hom_snd [HasTerminal C] [HasPullbacks C] (X Y : C) [HasBin
aryProduct X Y] : (prodIsoPullback X Y).hom ≫ pullback.snd _ _ = prod.snd
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.isoLimitCone_hom_π`：∀ {J : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Catego
ry.{v, u} C]   {F : CategoryTheory.F…
-/
lemma prodIsoPullback_hom_snd [HasTerminal C] [HasPullbacks C] (X Y : C)
    [HasBinaryProduct X Y] : (prodIsoPullback X Y).hom ≫ pullback.snd _ _ = prod.snd :=
  limit.isoLimitCone_hom_π (limitConeOfTerminalAndPullbacks _) ⟨.right⟩

@[reassoc (attr := simp)]
/-
**prodIsoPullback_inv_fst** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：prodIsoPullback_inv_fst [HasTerminal C] [HasPullbacks C] (X Y : C) [HasBin
aryProduct X Y] : (prodIsoPullback X Y).inv ≫ prod.fst = pullback.fst _ _
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.isoLimitCone_inv_π`：∀ {J : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Catego
ry.{v, u} C]   {F : CategoryTheory.F…
-/
lemma prodIsoPullback_inv_fst [HasTerminal C] [HasPullbacks C] (X Y : C)
    [HasBinaryProduct X Y] : (prodIsoPullback X Y).inv ≫ prod.fst = pullback.fst _ _ :=
  limit.isoLimitCone_inv_π (limitConeOfTerminalAndPullbacks _) ⟨.left⟩

@[reassoc (attr := simp)]
/-
**prodIsoPullback_inv_snd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：prodIsoPullback_inv_snd [HasTerminal C] [HasPullbacks C] (X Y : C) [HasBin
aryProduct X Y] : (prodIsoPullback X Y).inv ≫ prod.snd = pullback.snd _ _
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.limit.isoLimitCone_inv_π`：∀ {J : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Catego
ry.{v, u} C]   {F : CategoryTheory.F…
-/
lemma prodIsoPullback_inv_snd [HasTerminal C] [HasPullbacks C] (X Y : C)
    [HasBinaryProduct X Y] : (prodIsoPullback X Y).inv ≫ prod.snd = pullback.snd _ _ :=
  limit.isoLimitCone_inv_π (limitConeOfTerminalAndPullbacks _) ⟨.right⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If a cospan is the pushout cospan under the initial object, then it is a binary coproduct. -/
/-
**isBinaryCoproductOfIsInitialIsPushout** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：isBinaryCoproductOfIsInitialIsPushout (F : Discrete WalkingPair ⥤ C) (c : 
Cocone F) {X : C} (hX : IsInitial X) (f : X ⟶ F.obj ⟨WalkingPair.left⟩) (g : X ⟶
 F.obj ⟨WalkingPair.right⟩) (hc : IsColimit (PushoutCocone.mk (c.ι.app ⟨WalkingP
air.left⟩) (c.ι.app ⟨WalkingPair.right⟩ :) <| hX.hom_ext (f ≫ _) (g ≫ _))) : IsC
olimit c where desc s
参数：F : Discrete WalkingPair ⥤ C；c : Cocone F；hX : IsInitial X；f : X ⟶ F.obj ⟨Wal
kingPair.left⟩；g : X ⟶ F.obj ⟨WalkingPair.right⟩；hc : IsColimit (PushoutCocone.m
k (c.ι.app ⟨WalkingPair.left⟩) (c.ι.app ⟨WalkingPair.right⟩ :) <| hX.hom_ext (f 
≫ _) (g ≫ _))。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a cospan is the pushout cospan under the initial object, then it is a binary 
coproduct.
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

/-- The pushout under the initial object is the coproduct -/
/-
**isCoproductOfIsInitialIsPushout** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：isCoproductOfIsInitialIsPushout {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h :
 W ⟶ X) (k : W ⟶ Y) (H₁ : IsInitial W) (H₂ : IsColimit (PushoutCocone.mk _ _ (sh
ow h ≫ f = k ≫ g from H₁.hom_ext _ _))) : IsColimit (BinaryCofan.mk f g)
参数：f : X ⟶ Z；g : Y ⟶ Z；h : W ⟶ X；k : W ⟶ Y；H₁ : IsInitial W；H₂ : IsColimit (Push
outCocone.mk _ _ (show h ≫ f = k ≫ g from H₁.hom_ext _ _))。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pushout under the initial object is the coproduct
-/
def isCoproductOfIsInitialIsPushout {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ X) (k : W ⟶ Y)
    (H₁ : IsInitial W)
    (H₂ : IsColimit (PushoutCocone.mk _ _ (show h ≫ f = k ≫ g from H₁.hom_ext _ _))) :
    IsColimit (BinaryCofan.mk f g) := by
  apply isBinaryCoproductOfIsInitialIsPushout _ _ H₁
  exact H₂

/-- The coproduct is the pushout under the initial object. -/
/-
**isPushoutOfIsInitialIsCoproduct** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：isPushoutOfIsInitialIsCoproduct {W X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (h :
 W ⟶ X) (k : W ⟶ Y) (H₁ : IsInitial W) (H₂ : IsColimit (BinaryCofan.mk f g)) : I
sColimit (PushoutCocone.mk _ _ (show h ≫ f = k ≫ g from H₁.hom_ext _ _))
参数：f : X ⟶ Z；g : Y ⟶ Z；h : W ⟶ X；k : W ⟶ Y；H₁ : IsInitial W；H₂ : IsColimit (Bina
ryCofan.mk f g)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coproduct is the pushout under the initial object.
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

/-- Any category with pushouts and an initial object has a colimit cocone for each walking pair. -/
/-
**colimitCoconeOfInitialAndPushouts** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：colimitCoconeOfInitialAndPushouts [HasInitial C] [HasPushouts C] (F : Disc
rete WalkingPair ⥤ C) : ColimitCocone F where cocone
参数：F : Discrete WalkingPair ⥤ C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any category with pushouts and an initial object has a colimit cocone for each w
alking pair.
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
/-- Any category with pushouts and initial object has binary coproducts. -/
/-
**hasBinaryCoproducts_of_hasInitial_and_pushouts** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasBinaryCoproducts_of_hasInitial_and_pushouts [HasInitial C] [HasPushouts
 C] : HasBinaryCoproducts C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasColimit.mk`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…

--- 原说明 ---
Any category with pushouts and initial object has binary coproducts.
-/
theorem hasBinaryCoproducts_of_hasInitial_and_pushouts [HasInitial C] [HasPushouts C] :
    HasBinaryCoproducts C :=
  { has_colimit := fun F => HasColimit.mk (colimitCoconeOfInitialAndPushouts F) }

/-- A functor that preserves initial objects and pushouts preserves binary coproducts. -/
/-
**preservesBinaryCoproducts_of_preservesInitial_and_pushouts** 是 Mathlib 中的一个引理，
位于命名空间 ``。
形式化陈述：preservesBinaryCoproducts_of_preservesInitial_and_pushouts [HasInitial C] 
[HasPushouts C] [PreservesColimitsOfShape (Discrete.{0} PEmpty) F] [PreservesCol
imitsOfShape WalkingSpan F] : PreservesColimitsOfShape (Discrete WalkingPair) F
参数：Discrete.{0} PEmpty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_preserves_colimit_cocone`：pres
ervesColimit_of_preserves_colimit_cocone {F : C ⥤ D} {t : Cocone K} (h : IsColim
it t) (hF : IsColimit (F.mapCocone t)) : PreservesColimi…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
A functor that preserves initial objects and pushouts preserves binary coproduct
s.
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

/-- In a category with an initial object and pushouts,
a coproduct of objects `X` and `Y` is isomorphic to a pushout. -/
/-
**coprodIsoPushout** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：coprodIsoPushout [HasInitial C] [HasPushouts C] (X Y : C) [HasBinaryCoprod
uct X Y] : X ⨿ Y ≅ pushout (initial.to X) (initial.to Y)
参数：X Y : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a category with an initial object and pushouts,
a coproduct of objects `X` and `Y` is isomorphic to a pushout.
-/
noncomputable def coprodIsoPushout [HasInitial C] [HasPushouts C] (X Y : C)
    [HasBinaryCoproduct X Y] : X ⨿ Y ≅ pushout (initial.to X) (initial.to Y) :=
  colimit.isoColimitCocone (colimitCoconeOfInitialAndPushouts _)

@[reassoc (attr := simp)]
/-
**inl_coprodIsoPushout_hom** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inl_coprodIsoPushout_hom [HasInitial C] [HasPushouts C] (X Y : C) [HasBina
ryCoproduct X Y] : coprod.inl ≫ (coprodIsoPushout X Y).hom = pushout.inl _ _
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.isoColimitCocone_ι_hom`：∀ {J : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.
Category.{v, u} C]   {F : CategoryTheory.F…
-/
lemma inl_coprodIsoPushout_hom [HasInitial C] [HasPushouts C] (X Y : C)
    [HasBinaryCoproduct X Y] : coprod.inl ≫ (coprodIsoPushout X Y).hom = pushout.inl _ _ :=
  colimit.isoColimitCocone_ι_hom (colimitCoconeOfInitialAndPushouts _) _

@[reassoc (attr := simp)]
/-
**inr_coprodIsoPushout_hom** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inr_coprodIsoPushout_hom [HasInitial C] [HasPushouts C] (X Y : C) [HasBina
ryCoproduct X Y] : coprod.inr ≫ (coprodIsoPushout X Y).hom = pushout.inr _ _
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.isoColimitCocone_ι_hom`：∀ {J : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.
Category.{v, u} C]   {F : CategoryTheory.F…
-/
lemma inr_coprodIsoPushout_hom [HasInitial C] [HasPushouts C] (X Y : C)
    [HasBinaryCoproduct X Y] : coprod.inr ≫ (coprodIsoPushout X Y).hom = pushout.inr _ _ :=
  colimit.isoColimitCocone_ι_hom (colimitCoconeOfInitialAndPushouts _) _

@[reassoc (attr := simp)]
/-
**inl_coprodIsoPushout_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inl_coprodIsoPushout_inv [HasInitial C] [HasPushouts C] (X Y : C) [HasBina
ryCoproduct X Y] : pushout.inl _ _ ≫ (coprodIsoPushout X Y).inv = coprod.inl
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.isoColimitCocone_ι_inv`：∀ {J : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.
Category.{v, u} C]   {F : CategoryTheory.F…
-/
lemma inl_coprodIsoPushout_inv [HasInitial C] [HasPushouts C] (X Y : C)
    [HasBinaryCoproduct X Y] : pushout.inl _ _ ≫ (coprodIsoPushout X Y).inv = coprod.inl :=
  colimit.isoColimitCocone_ι_inv (colimitCoconeOfInitialAndPushouts (pair X Y)) ⟨.left⟩

@[reassoc (attr := simp)]
/-
**inr_coprodIsoPushout_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inr_coprodIsoPushout_inv [HasInitial C] [HasPushouts C] (X Y : C) [HasBina
ryCoproduct X Y] : pushout.inr _ _ ≫ (coprodIsoPushout X Y).inv = coprod.inr
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.colimit.isoColimitCocone_ι_inv`：∀ {J : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.
Category.{v, u} C]   {F : CategoryTheory.F…
-/
lemma inr_coprodIsoPushout_inv [HasInitial C] [HasPushouts C] (X Y : C)
    [HasBinaryCoproduct X Y] : pushout.inr _ _ ≫ (coprodIsoPushout X Y).inv = coprod.inr :=
  colimit.isoColimitCocone_ι_inv (colimitCoconeOfInitialAndPushouts (pair X Y)) ⟨.right⟩
