/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Adjunction.Opposites
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions

/-!
# The calculus of fractions deduced from an adjunction

If `G ⊣ F` is an adjunction, `F` is fully faithful,
and `W` is a class of morphisms that is inverted by `G`
and such that the morphism `adj.unit.app X` belongs to `W`
for any object `X`, then `G` is a localization functor
with respect to `W`. Moreover, if `W` is multiplicative,
then `W` has a calculus of left fractions. This
holds in particular if `W` is the inverse image of
the class of isomorphisms by `G`.

(The dual statement is also obtained.)

-/

public section

namespace CategoryTheory

open MorphismProperty

namespace Adjunction

variable {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
  {G : C₁ ⥤ C₂} {F : C₂ ⥤ C₁}

/-
**CategoryTheory.Adjunction.hasLeftCalculusOfFractions** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Adjunction`。
形式化陈述：hasLeftCalculusOfFractions (adj : G ⊣ F) (W : MorphismProperty C₁) [W.IsMu
ltiplicative] (hW : W.IsInvertedBy G) (hW' : (W.functorCategory C₁) adj.unit) : 
W.HasLeftCalculusOfFractions where exists_leftFraction X Y φ
参数：adj : G ⊣ F；W : MorphismProperty C₁；hW : W.IsInvertedBy G；hW' : (W.functorCat
egory C₁) adj.unit。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.RightFraction.cases`：cases (α : W.RightF
raction X Y) : exists (X' : C) (s : X' ⟶ X) (hs : W s) (f : X' ⟶ Y), α = RightFr
action.mk s hs f
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.Functor.map_inv`：map_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y
) [IsIso f] : F.map (inv f) = inv (F.map f)
· 使用定理 `CategoryTheory.IsIso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : X ⟶ Z), CategoryT…
· 使用定理 `CategoryTheory.Adjunction.unit_naturality`：unit_naturality {X Y : C} (f 
: X ⟶ Y) : dsimp% adj.unit.app X ≫ G.map (F.map f) = f ≫ adj.unit.app Y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.IsSplitEpi.epi`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [hf : CategoryTheory.IsSplitEpi f],   C
ategoryTheory.Epi f
· 使用定理 `CategoryTheory.IsSplitEpi.of_iso`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   Category
Theory.IsSplitEpi f
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
-/
lemma hasLeftCalculusOfFractions (adj : G ⊣ F) (W : MorphismProperty C₁)
    [W.IsMultiplicative] (hW : W.IsInvertedBy G) (hW' : (W.functorCategory C₁) adj.unit) :
    W.HasLeftCalculusOfFractions where
  exists_leftFraction X Y φ := by
    obtain ⟨T, s, _, f, rfl⟩ := φ.cases
    dsimp
    have := hW s (by assumption)
    exact ⟨{
      f := adj.unit.app X ≫ F.map (inv (G.map s)) ≫ F.map (G.map f)
      s := adj.unit.app Y
      hs := hW' Y}, by
      have := adj.unit.naturality s
      dsimp at this ⊢
      rw [reassoc_of% this, Functor.map_inv, IsIso.hom_inv_id_assoc, adj.unit_naturality]⟩
  ext X' X Y f₁ f₂ s _ h := by
    have := hW s (by assumption)
    refine ⟨_, adj.unit.app Y, hW' _, ?_⟩
    rw [← adj.unit_naturality f₁, ← adj.unit_naturality f₂]
    congr 2
    rw [← cancel_epi (G.map s), ← G.map_comp, ← G.map_comp, h]
/-
**CategoryTheory.Adjunction.hasRightCalculusOfFractions** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Adjunction`。
形式化陈述：hasRightCalculusOfFractions (adj : F ⊣ G) (W : MorphismProperty C₁) [W.IsM
ultiplicative] (hW : W.IsInvertedBy G) (hW' : (W.functorCategory _) adj.counit) 
: W.HasRightCalculusOfFractions
参数：adj : F ⊣ G；W : MorphismProperty C₁；hW : W.IsInvertedBy G；hW' : (W.functorCat
egory _) adj.counit。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.hasLeftCalculusOfFractions`：hasLeftCalculusOfF
ractions (adj : G ⊣ F) (W : MorphismProperty C₁) [W.IsMultiplicative] (hW : W.Is
InvertedBy G) (hW' : (W.functorCategory C₁…
· 使用定理 `CategoryTheory.MorphismProperty.IsInvertedBy.op`：op {W : MorphismPropert
y C} {L : C ⥤ D} (h : W.IsInvertedBy L) : W.op.IsInvertedBy L.op
-/
lemma hasRightCalculusOfFractions (adj : F ⊣ G) (W : MorphismProperty C₁)
    [W.IsMultiplicative] (hW : W.IsInvertedBy G) (hW' : (W.functorCategory _) adj.counit) :
    W.HasRightCalculusOfFractions :=
  have := hasLeftCalculusOfFractions adj.op W.op hW.op (fun _ ↦ hW' _)
  inferInstanceAs W.op.unop.HasRightCalculusOfFractions

section

variable [F.Full] [F.Faithful]

/-
**CategoryTheory.Adjunction.isLocalization_leftAdjoint** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Adjunction`。
形式化陈述：isLocalization_leftAdjoint (adj : G ⊣ F) (W : MorphismProperty C₁) (hW : W
.IsInvertedBy G) (hW' : (W.functorCategory C₁) adj.unit) : G.IsLocalization W
参数：adj : G ⊣ F；W : MorphismProperty C₁；hW : W.IsInvertedBy G；hW' : (W.functorCat
egory C₁) adj.unit。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.isIso_iff_isIso_app`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `CategoryTheory.Functor.IsLocalization.of_equivalence_target`：of_equivale
nce_target {E : Type*} [Category* E] (L' : C ⥤ E) (eq : D ≌ E) [L.IsLocalization
 W] (e : L ⋙ eq.functor ≅ L') : L'.IsLocalization…
-/
lemma isLocalization_leftAdjoint
    (adj : G ⊣ F) (W : MorphismProperty C₁)
    (hW : W.IsInvertedBy G) (hW' : (W.functorCategory C₁) adj.unit) :
    G.IsLocalization W := by
  let Φ : W.Localization ⥤ C₂ := Localization.lift _ hW W.Q
  let e : W.Q ⋙ Φ ≅ G := by apply Localization.fac
  have : IsIso (Functor.whiskerRight adj.unit W.Q) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    exact Localization.inverts W.Q W _ (hW' X)
  exact Functor.IsLocalization.of_equivalence_target W.Q W _
    (Equivalence.mk Φ (F ⋙ W.Q)
      (Localization.liftNatIso W.Q W W.Q (G ⋙ F ⋙ W.Q) _ _
        (W.Q.leftUnitor.symm ≪≫ asIso (Functor.whiskerRight adj.unit W.Q) ≪≫
        Functor.associator _ _ _))
      (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ e ≪≫ asIso adj.counit)) e
/-
**CategoryTheory.Adjunction.isLocalization_rightAdjoint** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Adjunction`。
形式化陈述：isLocalization_rightAdjoint (adj : F ⊣ G) (W : MorphismProperty C₁) (hW : 
W.IsInvertedBy G) (hW' : (W.functorCategory C₁) adj.counit) : G.IsLocalization W
参数：adj : F ⊣ G；W : MorphismProperty C₁；hW : W.IsInvertedBy G；hW' : (W.functorCat
egory C₁) adj.counit。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.isLocalization_leftAdjoint`：isLocalization_lef
tAdjoint (adj : G ⊣ F) (W : MorphismProperty C₁) (hW : W.IsInvertedBy G) (hW' : 
(W.functorCategory C₁) adj.unit) : G.IsLoc…
· 使用定理 `CategoryTheory.Functor.instFullOppositeOp`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instFaithfulOppositeOp`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.MorphismProperty.IsInvertedBy.op`：op {W : MorphismPropert
y C} {L : C ⥤ D} (h : W.IsInvertedBy L) : W.op.IsInvertedBy L.op
-/
lemma isLocalization_rightAdjoint
    (adj : F ⊣ G) (W : MorphismProperty C₁)
    (hW : W.IsInvertedBy G) (hW' : (W.functorCategory C₁) adj.counit) :
    G.IsLocalization W := by
  simpa using isLocalization_leftAdjoint adj.op W.op hW.op (fun X ↦ hW' X.unop)
/-
**CategoryTheory.Adjunction.functorCategory_inverseImage_isomorphisms_unit** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.Adjunction`。
形式化陈述：functorCategory_inverseImage_isomorphisms_unit (adj : G ⊣ F) : ((isomorphi
sms C₂).inverseImage G).functorCategory C₁ adj.unit
参数：adj : G ⊣ F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Adjunction.instIsIsoMapAppUnitOfFaithfulOfFull`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   {L : CategoryTheor…
-/
lemma functorCategory_inverseImage_isomorphisms_unit (adj : G ⊣ F) :
    ((isomorphisms C₂).inverseImage G).functorCategory C₁ adj.unit := by
  intro
  simp only [Functor.id_obj, inverseImage_iff, isomorphisms.iff]
  infer_instance
/-
**CategoryTheory.Adjunction.functorCategory_inverseImage_isomorphisms_counit** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Adjunction`。
形式化陈述：functorCategory_inverseImage_isomorphisms_counit (adj : F ⊣ G) : ((isomorp
hisms C₂).inverseImage G).functorCategory C₁ adj.counit
参数：adj : F ⊣ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Adjunction.instIsIsoMapAppCounitOfFaithfulOfFull`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   {L : CategoryTheor…
-/
lemma functorCategory_inverseImage_isomorphisms_counit (adj : F ⊣ G) :
    ((isomorphisms C₂).inverseImage G).functorCategory C₁ adj.counit := by
  intro
  simp only [Functor.id_obj, inverseImage_iff, isomorphisms.iff]
  infer_instance
/-
**CategoryTheory.Adjunction.isLocalization_leftAdjoint'** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Adjunction`。
形式化陈述：isLocalization_leftAdjoint' (adj : G ⊣ F) : G.IsLocalization ((isomorphism
s C₂).inverseImage G)
参数：adj : G ⊣ F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.isLocalization_leftAdjoint`：isLocalization_lef
tAdjoint (adj : G ⊣ F) (W : MorphismProperty C₁) (hW : W.IsInvertedBy G) (hW' : 
(W.functorCategory C₁) adj.unit) : G.IsLoc…
· 使用引理 `CategoryTheory.Adjunction.functorCategory_inverseImage_isomorphisms_unit
`：functorCategory_inverseImage_isomorphisms_unit (adj : G ⊣ F) : ((isomorphisms 
C₂).inverseImage G).functorCategory C₁ adj.unit
-/
lemma isLocalization_leftAdjoint' (adj : G ⊣ F) :
    G.IsLocalization ((isomorphisms C₂).inverseImage G) :=
  adj.isLocalization_leftAdjoint _ (fun _ _ _ h ↦ h)
    adj.functorCategory_inverseImage_isomorphisms_unit
/-
**CategoryTheory.Adjunction.isLocalization_rightAdjoint'** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Adjunction`。
形式化陈述：isLocalization_rightAdjoint' (adj : F ⊣ G) : G.IsLocalization ((isomorphis
ms C₂).inverseImage G)
参数：adj : F ⊣ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.isLocalization_rightAdjoint`：isLocalization_ri
ghtAdjoint (adj : F ⊣ G) (W : MorphismProperty C₁) (hW : W.IsInvertedBy G) (hW' 
: (W.functorCategory C₁) adj.counit) : G.Is…
· 使用引理 `CategoryTheory.Adjunction.functorCategory_inverseImage_isomorphisms_coun
it`：functorCategory_inverseImage_isomorphisms_counit (adj : F ⊣ G) : ((isomorphi
sms C₂).inverseImage G).functorCategory C₁ adj.counit
-/
lemma isLocalization_rightAdjoint' (adj : F ⊣ G) :
    G.IsLocalization ((isomorphisms C₂).inverseImage G) :=
  adj.isLocalization_rightAdjoint _ (fun _ _ _ h ↦ h)
    adj.functorCategory_inverseImage_isomorphisms_counit
/-
**CategoryTheory.Adjunction.hasLeftCalculusOfFractions'** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Adjunction`。
形式化陈述：hasLeftCalculusOfFractions' (adj : G ⊣ F) : ((isomorphisms C₂).inverseImag
e G).HasLeftCalculusOfFractions
参数：adj : G ⊣ F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.hasLeftCalculusOfFractions`：hasLeftCalculusOfF
ractions (adj : G ⊣ F) (W : MorphismProperty C₁) [W.IsMultiplicative] (hW : W.Is
InvertedBy G) (hW' : (W.functorCategory C₁…
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instInverseImage`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [inst_1 : Cate
goryTheory.Category.{v', u'} D]   {P : CategoryTheory.M…
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instIsomorphisms`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C],   (CategoryTheory.MorphismP
roperty.isomorphisms C).IsMultiplicative
· 使用引理 `CategoryTheory.Adjunction.functorCategory_inverseImage_isomorphisms_unit
`：functorCategory_inverseImage_isomorphisms_unit (adj : G ⊣ F) : ((isomorphisms 
C₂).inverseImage G).functorCategory C₁ adj.unit
-/
lemma hasLeftCalculusOfFractions' (adj : G ⊣ F) :
    ((isomorphisms C₂).inverseImage G).HasLeftCalculusOfFractions :=
  hasLeftCalculusOfFractions adj _ (fun _ _ _ h ↦ h)
    adj.functorCategory_inverseImage_isomorphisms_unit
/-
**CategoryTheory.Adjunction.hasRightCalculusOfFractions'** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Adjunction`。
形式化陈述：hasRightCalculusOfFractions' (adj : F ⊣ G) : ((isomorphisms C₂).inverseIma
ge G).HasRightCalculusOfFractions
参数：adj : F ⊣ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.hasRightCalculusOfFractions`：hasRightCalculusO
fFractions (adj : F ⊣ G) (W : MorphismProperty C₁) [W.IsMultiplicative] (hW : W.
IsInvertedBy G) (hW' : (W.functorCategory _…
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instInverseImage`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u'} [inst_1 : Cate
goryTheory.Category.{v', u'} D]   {P : CategoryTheory.M…
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instIsomorphisms`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C],   (CategoryTheory.MorphismP
roperty.isomorphisms C).IsMultiplicative
· 使用引理 `CategoryTheory.Adjunction.functorCategory_inverseImage_isomorphisms_coun
it`：functorCategory_inverseImage_isomorphisms_counit (adj : F ⊣ G) : ((isomorphi
sms C₂).inverseImage G).functorCategory C₁ adj.counit
-/
lemma hasRightCalculusOfFractions' (adj : F ⊣ G) :
    ((isomorphisms C₂).inverseImage G).HasRightCalculusOfFractions :=
  hasRightCalculusOfFractions adj _ (fun _ _ _ h ↦ h)
    adj.functorCategory_inverseImage_isomorphisms_counit

end

end Adjunction

end CategoryTheory

