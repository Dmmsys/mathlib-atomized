/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Reid Barton, Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Products in the over category

Shows that products in the over category can be derived from wide pullbacks in the base category.
The main result is `over_product_of_widePullback`, which says that if `C` has `J`-indexed wide
pullbacks, then `Over B` has `J`-indexed products.

Note that the binary case is done separately to ensure defeqs with the pullback in the base
category.

## TODO

* Generalise from arbitrary products to arbitrary limits. This is done in Toric.
* Dualise to get the `Under X` results.
-/

@[expose] public section


universe w v u -- morphism levels before object levels. See note [category_theory universes].

open CategoryTheory CategoryTheory.Limits

variable {J : Type w}
variable {C : Type u} [Category.{v} C]
variable {X Y Z : C}

/-!
### Binary products

In this section we construct binary products in `Over X` and binary coproducts in `Under X`
explicitly as the pullbacks and pushouts of binary (co)fans in the base category.

For `Over X`, one could construct these binary products from the general theory of arbitrary
products from the next section, i.e.
```
(Cone.postcomposeEquivalence (diagramIsoCospan _).symm).trans
  (Over.ConstructProducts.conesEquiv _ (pair (Over.mk f) (Over.mk g)))
```
but this gives worse defeqs.

For `Under X`, there is currently no general theory of arbitrary coproducts.
-/

namespace CategoryTheory.Limits
section Over
variable {f : Y ⟶ X} {g : Z ⟶ X}

set_option backward.isDefEq.respectTransparency false in
/-- Pullback cones to `X` are the same thing as binary fans in `Over X`. -/
@[implicit_reducible, simps]
/-
**CategoryTheory.Limits.pullbackConeEquivBinaryFan** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：pullbackConeEquivBinaryFan : PullbackCone f g ≌ BinaryFan (Over.mk f) (.mk
 g) where functor.obj c
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pullback cones to `X` are the same thing as binary fans in `Over X`.
-/
def pullbackConeEquivBinaryFan : PullbackCone f g ≌ BinaryFan (Over.mk f) (.mk g) where
  functor.obj c := .mk (Over.homMk (U := .mk (c.fst ≫ f)) (V := .mk f) c.fst rfl)
      (Over.homMk (U := .mk (c.fst ≫ f)) (V := .mk g) c.snd c.condition.symm)
  functor.map {c₁ c₂} a := { hom := Over.homMk a.hom, w := by rintro (_ | _) <;> cat_disch }
  inverse.obj c := PullbackCone.mk c.fst.left c.snd.left (c.fst.w.trans c.snd.w.symm)
  inverse.map {c₁ c₂} a := {
    hom := a.hom.left
    w := by rintro (_ | _ | _) <;> simp [← Over.comp_left_assoc, ← Over.comp_left]
  }
  unitIso := NatIso.ofComponents (fun c ↦ c.eta) (by intros; ext; simp)
  counitIso := NatIso.ofComponents (fun X ↦ BinaryFan.ext (Over.isoMk (Iso.refl _)
    (by simpa using X.fst.w.symm)) (by ext; simp) (by ext; simp))
    (by intros; ext; simp [BinaryFan.ext])
  functor_unitIso_comp c := by ext; simp [BinaryFan.ext]

set_option backward.isDefEq.respectTransparency false in
/-- A binary fan in `Over X` is a limit if its corresponding pullback cone to `X` is a limit. -/
-- `IsLimit.ofConeEquiv` isn't used here because the lift it defines is `𝟙 _ ≫ pullback.lift`.
-- TODO: Define `IsLimit.copy`?
@[simps!]
/-
**CategoryTheory.Limits.IsLimit.pullbackConeEquivBinaryFanFunctor** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.Limits.IsLimit`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y Z : 
C} →       {f : Y ⟶ X} →         {g : Z ⟶ X} →           {c : CategoryTheory.Lim
its.PullbackCone f g} →             CategoryTheory.Limits.IsLimit c →           
    CategoryTheory.Limits.IsLimit (CategoryTheory.Limits.pullbackConeEquivBinary
Fan.functor.obj c)
参数：CategoryTheory.Limits.pullbackConeEquivBinaryFan.functor.obj c。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def IsLimit.pullbackConeEquivBinaryFanFunctor {c : PullbackCone f g} (hc : IsLimit c) :
    IsLimit <| pullbackConeEquivBinaryFan.functor.obj c :=
  BinaryFan.isLimitMk
    -- TODO: Drop `BinaryFan.IsLimit.lift'`. Instead provide the lemmas it bundles separately.
    -- TODO: Define `abbrev BinaryFan.IsLimit (c : BinaryFan X Y) := IsLimit c` for dot notation?
    (fun s ↦ Over.homMk (hc.lift <| pullbackConeEquivBinaryFan.inverse.obj s) <| by
      simpa using! s.fst.w)
    (fun s ↦ Over.OverMorphism.ext (hc.fac _ _)) (fun s ↦ Over.OverMorphism.ext (hc.fac _ _))
    fun s m e₁ e₂ ↦ by
      ext1
      apply PullbackCone.IsLimit.hom_ext hc
      · simpa using! congr(($e₁).left)
      · simpa using! congr(($e₂).left)

/-- A pullback cone to `X` is a limit if its corresponding binary fan in `Over X` is a limit. -/
-- This could also be `(IsLimit.ofConeEquiv pullbackConeEquivBinaryFan.symm).symm hc`, but possibly
-- bad defeqs?
/-
**CategoryTheory.Limits.IsLimit.pullbackConeEquivBinaryFanInverse** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.Limits.IsLimit`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y Z : 
C} →       {f : Y ⟶ X} →         {g : Z ⟶ X} →           {c : CategoryTheory.Lim
its.BinaryFan (CategoryTheory.Over.mk f) (CategoryTheory.Over.mk g)} →          
   CategoryTheory.Limits.IsLimit c →               CategoryTheory.Limits.IsLimit
 (CategoryTheory.Limits.pullbackConeEquivBinaryFan.inverse.obj c)
参数：CategoryTheory.Over.mk f；CategoryTheory.Over.mk g；CategoryTheory.Limits.pullb
ackConeEquivBinaryFan.inverse.obj c。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def IsLimit.pullbackConeEquivBinaryFanInverse {c : BinaryFan (Over.mk f) (.mk g)} (hc : IsLimit c) :
    IsLimit <| pullbackConeEquivBinaryFan.inverse.obj c :=
  PullbackCone.IsLimit.mk
    (c.fst.w.trans c.snd.w.symm)
    (fun s ↦ (hc.lift <| pullbackConeEquivBinaryFan.functor.obj s).left)
    (fun s ↦ by simpa only using! congr($(hc.fac _ _).left))
    (fun s ↦ by simpa only using! congr($(hc.fac _ _).left))
    <| fun s m hm₁ hm₂ ↦ by
      change PullbackCone f g at s
      have := hc.uniq (pullbackConeEquivBinaryFan.functor.obj s) (Over.homMk m <| by
        simp [← hm₁, dsimp% c.fst.w])
        (by rintro (_ | _) <;> ext <;> simpa)
      exact congr(($this).left)

end Over

section Under
variable {f : X ⟶ Y} {g : X ⟶ Z}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Pushout cocones from `X` are the same thing as binary cofans in `Under X`. -/
@[simps]
/-
**CategoryTheory.Limits.pushoutCoconeEquivBinaryCofan** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：pushoutCoconeEquivBinaryCofan : PushoutCocone f g ≌ BinaryCofan (Under.mk 
f) (.mk g) where functor.obj c
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pushout cocones from `X` are the same thing as binary cofans in `Under X`.
-/
def pushoutCoconeEquivBinaryCofan : PushoutCocone f g ≌ BinaryCofan (Under.mk f) (.mk g) where
  functor.obj c := .mk (Under.homMk (U := .mk f) (V := .mk (f ≫ c.inl)) c.inl rfl)
      (Under.homMk (U := .mk g) (V := .mk (f ≫ c.inl)) c.inr c.condition.symm)
  functor.map {c₁ c₂} a := { hom := Under.homMk a.hom, w := by rintro (_ | _) <;> cat_disch }
  inverse.obj c := .mk c.inl.right c.inr.right (c.inl.w.trans c.inr.w.symm)
  inverse.map {c₁ c₂} a := {
    hom := a.hom.right
    w := by rintro (_ | _ | _) <;> simp [← Under.comp_right]
  }
  unitIso := NatIso.ofComponents (fun c ↦ c.eta) (fun f ↦ by ext; simp)
  counitIso := NatIso.ofComponents (fun X ↦ BinaryCofan.ext (Under.isoMk (.refl _)
    (by dsimp; simpa using X.inl.w)) (by ext; simp) (by ext; simp))
    (by intros; ext; simp)
  functor_unitIso_comp c := by ext; simp

set_option backward.isDefEq.respectTransparency false in
/-- A binary cofan in `Under X` is a colimit if its corresponding pushout cocone from `X` is a
colimit. -/
-- `IsColimit.ofCoconeEquiv` isn't used here because the lift it defines is `pushout.desc ≫ 𝟙 _`.
-- TODO: Define `IsColimit.copy`?
@[simps!]
/-
**CategoryTheory.Limits.IsColimit.pushoutCoconeEquivBinaryCofanFunctor** 是 Mathl
ib 中的一个定义，位于命名空间 `CategoryTheory.Limits.IsColimit`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y Z : 
C} →       {f : X ⟶ Y} →         {g : X ⟶ Z} →           {c : CategoryTheory.Lim
its.PushoutCocone f g} →             CategoryTheory.Limits.IsColimit c →        
       CategoryTheory.Limits.IsColimit (CategoryTheory.Limits.pushoutCoconeEquiv
BinaryCofan.functor.obj c)
参数：CategoryTheory.Limits.pushoutCoconeEquivBinaryCofan.functor.obj c。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def IsColimit.pushoutCoconeEquivBinaryCofanFunctor {c : PushoutCocone f g} (hc : IsColimit c) :
    IsColimit <| pushoutCoconeEquivBinaryCofan.functor.obj c :=
  BinaryCofan.isColimitMk
    (fun s ↦ Under.homMk
      (hc.desc (PushoutCocone.mk s.inl.right s.inr.right (s.inl.w.trans s.inr.w.symm))) <| by
        simpa using! s.inl.w)
    (fun s ↦ Under.UnderMorphism.ext (hc.fac _ _)) (fun s ↦ Under.UnderMorphism.ext (hc.fac _ _))
      fun s m e₁ e₂ ↦ by
    ext1
    refine PushoutCocone.IsColimit.hom_ext hc ?_ ?_
    · simpa using! congr(($e₁).right)
    · simpa using! congr(($e₂).right)

set_option backward.defeqAttrib.useBackward true in
/-- A pushout cocone from `X` is a colimit if its corresponding binary cofan in `Under X` is a
colimit. -/
-- This could also be `(IsColimit.ofCoconeEquiv pushoutCoconeEquivBinaryCofan.symm).symm hc`,
-- but possibly bad defeqs?
/-
**CategoryTheory.Limits.IsColimit.pushoutCoconeEquivBinaryCofanInverse** 是 Mathl
ib 中的一个定义，位于命名空间 `CategoryTheory.Limits.IsColimit`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X Y Z : 
C} →       {f : X ⟶ Y} →         {g : X ⟶ Z} →           {c : CategoryTheory.Lim
its.BinaryCofan (CategoryTheory.Under.mk f) (CategoryTheory.Under.mk g)} →      
       CategoryTheory.Limits.IsColimit c →               CategoryTheory.Limits.I
sColimit (CategoryTheory.Limits.pushoutCoconeEquivBinaryCofan.inverse.obj c)
参数：CategoryTheory.Under.mk f；CategoryTheory.Under.mk g；CategoryTheory.Limits.pus
houtCoconeEquivBinaryCofan.inverse.obj c。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def IsColimit.pushoutCoconeEquivBinaryCofanInverse {c : BinaryCofan (Under.mk f) (.mk g)}
    (hc : IsColimit c) : IsColimit <| pushoutCoconeEquivBinaryCofan.inverse.obj c :=
  PushoutCocone.IsColimit.mk
    (c.inl.w.trans c.inr.w.symm)
    (fun s ↦ (hc.desc <| pushoutCoconeEquivBinaryCofan.functor.obj s).right)
    (fun s ↦ by simpa only using! congr($(hc.fac _ _).right))
    (fun s ↦ by simpa only using! congr($(hc.fac _ _).right))
    <| fun s m hm₁ hm₂ ↦ by
      change PushoutCocone f g at s
      have := hc.uniq (pushoutCoconeEquivBinaryCofan.functor.obj s) (Under.homMk m <| by
        simp [← hm₁, dsimp% c.inl.w_assoc])
        (by rintro (_ | _) <;> ext <;> simpa)
      exact congr(($this).right)

end Under
end Limits

namespace Over
section BinaryProduct
variable {X : C} {Y Z : Over X}

open Limits

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Over.isPullback_of_binaryFan_isLimit** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Over`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X : C} {Y Z : Ca
tegoryTheory.Over X}   (c : CategoryTheory.Limits.BinaryFan Y Z) (hc : CategoryT
heory.Limits.IsLimit c),   CategoryTheory.IsPullback (CategoryTheory.Over.Hom.le
ft c.fst) (CategoryTheory.Over.Hom.left c.snd) Y.hom Z.hom
参数：c : CategoryTheory.Limits.BinaryFan Y Z；hc : CategoryTheory.Limits.IsLimit c；
CategoryTheory.Over.Hom.left c.fst；CategoryTheory.Over.Hom.left c.snd。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Over.w`：w : φ.left ≫ g.hom = f.hom
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
-/
lemma isPullback_of_binaryFan_isLimit (c : BinaryFan Y Z) (hc : IsLimit c) :
    IsPullback c.fst.left c.snd.left Y.hom Z.hom :=
  ⟨by simp, ⟨hc.pullbackConeEquivBinaryFanInverse⟩⟩

variable (Y Z) [HasPullback Y.hom Z.hom] [HasBinaryProduct Y Z]

set_option backward.isDefEq.respectTransparency false in
/-- The product of `Y` and `Z` in `Over X` is isomorphic to `Y ×ₓ Z`. -/
noncomputable
/-
**CategoryTheory.Over.prodLeftIsoPullback** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Over`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {X : C} →
       (Y Z : CategoryTheory.Over X) →         [inst_1 : CategoryTheory.Limits.H
asPullback Y.hom Z.hom] →           [inst_2 : CategoryTheory.Limits.HasBinaryPro
duct Y Z] →             (Y ⨯ Z).left ≅ CategoryTheory.Limits.pullback Y.hom Z.ho
m
参数：Y Z : CategoryTheory.Over X；Y ⨯ Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def prodLeftIsoPullback :
    (Y ⨯ Z).left ≅ pullback Y.hom Z.hom :=
  (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd Y Z)).isoPullback

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Over.prodLeftIsoPullback_hom_fst** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Over`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X : C} (Y Z : Ca
tegoryTheory.Over X)   [inst_1 : CategoryTheory.Limits.HasPullback Y.hom Z.hom] 
[inst_2 : CategoryTheory.Limits.HasBinaryProduct Y Z],   CategoryTheory.Category
Struct.comp (Y.prodLeftIsoPullback Z).hom (CategoryTheory.Limits.pullback.fst Y.
hom Z.hom) =     CategoryTheory.Over.Hom.left CategoryTheory.Limits.prod.fst
参数：Y Z : CategoryTheory.Over X；Y.prodLeftIsoPullback Z；CategoryTheory.Limits.pul
lback.fst Y.hom Z.hom。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.isoPullback_hom_fst`：isoPullback_hom_fst (h : 
IsPullback fst snd f g) [HasPullback f g] : h.isoPullback.hom ≫ pullback.fst _ _
 = fst
-/
lemma prodLeftIsoPullback_hom_fst :
    (prodLeftIsoPullback Y Z).hom ≫ pullback.fst _ _ = (prod.fst (X := Y)).left :=
  IsPullback.isoPullback_hom_fst _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Over.prodLeftIsoPullback_hom_snd** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Over`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X : C} (Y Z : Ca
tegoryTheory.Over X)   [inst_1 : CategoryTheory.Limits.HasPullback Y.hom Z.hom] 
[inst_2 : CategoryTheory.Limits.HasBinaryProduct Y Z],   CategoryTheory.Category
Struct.comp (Y.prodLeftIsoPullback Z).hom (CategoryTheory.Limits.pullback.snd Y.
hom Z.hom) =     CategoryTheory.Over.Hom.left CategoryTheory.Limits.prod.snd
参数：Y Z : CategoryTheory.Over X；Y.prodLeftIsoPullback Z；CategoryTheory.Limits.pul
lback.snd Y.hom Z.hom。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.isoPullback_hom_snd`：isoPullback_hom_snd (h : 
IsPullback fst snd f g) [HasPullback f g] : h.isoPullback.hom ≫ pullback.snd _ _
 = snd
-/
lemma prodLeftIsoPullback_hom_snd :
    (prodLeftIsoPullback Y Z).hom ≫ pullback.snd _ _ = (prod.snd (X := Y)).left :=
  IsPullback.isoPullback_hom_snd _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Over.prodLeftIsoPullback_inv_fst** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Over`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X : C} (Y Z : Ca
tegoryTheory.Over X)   [inst_1 : CategoryTheory.Limits.HasPullback Y.hom Z.hom] 
[inst_2 : CategoryTheory.Limits.HasBinaryProduct Y Z],   CategoryTheory.Category
Struct.comp (Y.prodLeftIsoPullback Z).inv       (CategoryTheory.Over.Hom.left Ca
tegoryTheory.Limits.prod.fst) =     CategoryTheory.Limits.pullback.fst Y.hom Z.h
om
参数：Y Z : CategoryTheory.Over X；Y.prodLeftIsoPullback Z；CategoryTheory.Over.Hom.l
eft CategoryTheory.Limits.prod.fst。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.isoPullback_inv_fst`：isoPullback_inv_fst (h : 
IsPullback fst snd f g) [HasPullback f g] : h.isoPullback.inv ≫ fst = pullback.f
st _ _
-/
lemma prodLeftIsoPullback_inv_fst :
    (prodLeftIsoPullback Y Z).inv ≫ (prod.fst (X := Y)).left = pullback.fst _ _ :=
  IsPullback.isoPullback_inv_fst _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Over.prodLeftIsoPullback_inv_snd** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Over`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X : C} (Y Z : Ca
tegoryTheory.Over X)   [inst_1 : CategoryTheory.Limits.HasPullback Y.hom Z.hom] 
[inst_2 : CategoryTheory.Limits.HasBinaryProduct Y Z],   CategoryTheory.Category
Struct.comp (Y.prodLeftIsoPullback Z).inv       (CategoryTheory.Over.Hom.left Ca
tegoryTheory.Limits.prod.snd) =     CategoryTheory.Limits.pullback.snd Y.hom Z.h
om
参数：Y Z : CategoryTheory.Over X；Y.prodLeftIsoPullback Z；CategoryTheory.Over.Hom.l
eft CategoryTheory.Limits.prod.snd。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.isoPullback_inv_snd`：isoPullback_inv_snd (h : 
IsPullback fst snd f g) [HasPullback f g] : h.isoPullback.inv ≫ snd = pullback.s
nd _ _
-/
lemma prodLeftIsoPullback_inv_snd :
    (prodLeftIsoPullback Y Z).inv ≫ (prod.snd (X := Y)).left = pullback.snd _ _ :=
  IsPullback.isoPullback_inv_snd _

end BinaryProduct

/-!
### Arbitrary products

In this section, we prove that `J`-indexed products in `Over X` correspond to `J`-indexed pullbacks
in `C`.
-/

namespace ConstructProducts

/-- (Implementation)
Given a product diagram in `C/B`, construct the corresponding wide pullback diagram
in `C`.
-/
/-
**CategoryTheory.Over.ConstructProducts.widePullbackDiagramOfDiagramOver** 是 Mat
hlib 中的一个定义，位于命名空间 `CategoryTheory.Over.ConstructProducts`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     (B : C) →
       {J : Type w} →         CategoryTheory.Functor (CategoryTheory.Discrete J)
 (CategoryTheory.Over B) →           CategoryTheory.Functor (CategoryTheory.Limi
ts.WidePullbackShape J) C
参数：B : C；CategoryTheory.Discrete J；CategoryTheory.Over B；CategoryTheory.Limits.W
idePullbackShape J。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation)
Given a product diagram in `C/B`, construct the corresponding wide pullback diag
ram
in `C`.
-/
abbrev widePullbackDiagramOfDiagramOver (B : C) {J : Type w} (F : Discrete J ⥤ Over B) :
    WidePullbackShape J ⥤ C :=
  WidePullbackShape.wideCospan B (fun j => (F.obj ⟨j⟩).left) fun j => (F.obj ⟨j⟩).hom

set_option backward.defeqAttrib.useBackward true in
/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simps]
/-
**CategoryTheory.Over.ConstructProducts.conesEquivInverseObj** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Over.ConstructProducts`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     (B : C) →
       {J : Type w} →         (F : CategoryTheory.Functor (CategoryTheory.Discre
te J) (CategoryTheory.Over B)) →           CategoryTheory.Limits.Cone F →       
      CategoryTheory.Limits.Cone (CategoryTheory.Over.ConstructProducts.widePull
backDiagramOfDiagramOver B F)
参数：B : C；F : CategoryTheory.Functor (CategoryTheory.Discrete J) (CategoryTheory.
Over B)；CategoryTheory.Over.ConstructProducts.widePullbackDiagramOfDiagramOver B
 F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Impl) A preliminary definition to avoid timeouts.
-/
def conesEquivInverseObj (B : C) {J : Type w} (F : Discrete J ⥤ Over B) (c : Cone F) :
    Cone (widePullbackDiagramOfDiagramOver B F) where
  pt := c.pt.left
  π :=
    { app := fun X => Option.casesOn X c.pt.hom fun j : J => (c.π.app ⟨j⟩).left
      -- `tidy` can do this using `case_bash`, but let's try to be a good `-T50000` citizen:
      naturality := fun X Y f => by
        dsimp; cases X <;> cases Y <;> cases f
        · rw [Category.id_comp, Category.comp_id]
        · rw [Over.w, Category.id_comp]
        · rw [Category.id_comp, Category.comp_id] }

set_option backward.defeqAttrib.useBackward true in
/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simps]
/-
**CategoryTheory.Over.ConstructProducts.conesEquivInverse** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Over.ConstructProducts`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     (B : C) →
       {J : Type w} →         (F : CategoryTheory.Functor (CategoryTheory.Discre
te J) (CategoryTheory.Over B)) →           CategoryTheory.Functor (CategoryTheor
y.Limits.Cone F)             (CategoryTheory.Limits.Cone (CategoryTheory.Over.Co
nstructProducts.widePullbackDiagramOfDiagramOver B F))
参数：B : C；F : CategoryTheory.Functor (CategoryTheory.Discrete J) (CategoryTheory.
Over B)；CategoryTheory.Limits.Cone F；CategoryTheory.Limits.Cone (CategoryTheory.
Over.ConstructProducts.widePullbackDiagramOfDiagramOver B F)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Impl) A preliminary definition to avoid timeouts.
-/
def conesEquivInverse (B : C) {J : Type w} (F : Discrete J ⥤ Over B) :
    Cone F ⥤ Cone (widePullbackDiagramOfDiagramOver B F) where
  obj := conesEquivInverseObj B F
  map f :=
    { hom := f.hom.left
      w := fun j => by
        obtain - | j := j
        · simp
        · dsimp
          rw [← f.w ⟨j⟩]
          rfl }

-- Porting note: this should help with the additional `naturality` proof we now have to give in
-- `conesEquivFunctor`, but doesn't.
-- attribute [local aesop safe cases (rule_sets := [CategoryTheory])] Discrete

set_option backward.isDefEq.respectTransparency false in
/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simps]
/-
**CategoryTheory.Over.ConstructProducts.conesEquivFunctor** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Over.ConstructProducts`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     (B : C) →
       {J : Type w} →         (F : CategoryTheory.Functor (CategoryTheory.Discre
te J) (CategoryTheory.Over B)) →           CategoryTheory.Functor             (C
ategoryTheory.Limits.Cone (CategoryTheory.Over.ConstructProducts.widePullbackDia
gramOfDiagramOver B F))             (CategoryTheory.Limits.Cone F)
参数：B : C；F : CategoryTheory.Functor (CategoryTheory.Discrete J) (CategoryTheory.
Over B)；CategoryTheory.Limits.Cone (CategoryTheory.Over.ConstructProducts.widePu
llbackDiagramOfDiagramOver B F)；CategoryTheory.Limits.Cone F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Impl) A preliminary definition to avoid timeouts.
-/
def conesEquivFunctor (B : C) {J : Type w} (F : Discrete J ⥤ Over B) :
    Cone (widePullbackDiagramOfDiagramOver B F) ⥤ Cone F where
  obj c :=
    { pt := Over.mk (c.π.app none)
      π :=
        { app := fun ⟨j⟩ => Over.homMk (c.π.app (some j)) (c.w (WidePullbackShape.Hom.term j))
          -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10888): added proof for `naturality`
          naturality := fun ⟨X⟩ ⟨Y⟩ ⟨⟨f⟩⟩ => by dsimp at f ⊢; cat_disch } }
  map f := { hom := Over.homMk f.hom }

-- Porting note: unfortunately `aesop` can't cope with a `cases` rule here for the type synonym
-- `WidePullbackShape`.
-- attribute [local aesop safe cases (rule_sets := [CategoryTheory])] WidePullbackShape
-- If this worked we could avoid the `rintro` in `conesEquivUnitIso`.

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simps!]
/-
**CategoryTheory.Over.ConstructProducts.conesEquivUnitIso** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Over.ConstructProducts`。
形式化陈述：{J : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       (B : C) →         (F : CategoryTheory.Functor (CategoryTheory.Discre
te J) (CategoryTheory.Over B)) →           CategoryTheory.Functor.id            
   (CategoryTheory.Limits.Cone                 (CategoryTheory.Over.ConstructPro
ducts.widePullbackDiagramOfDiagramOver B F)) ≅             (CategoryTheory.Over.
ConstructProducts.conesEquivFunctor B F).comp               (CategoryTheory.Over
.ConstructProducts.conesEquivInverse B F)
参数：B : C；F : CategoryTheory.Functor (CategoryTheory.Discrete J) (CategoryTheory.
Over B)；CategoryTheory.Limits.Cone                 (CategoryTheory.Over.Construc
tProducts.widePullbackDiagramOfDiagramOver B F)；CategoryTheory.Over.ConstructPro
ducts.conesEquivFunctor B F；CategoryTheory.Over.ConstructProducts.conesEquivInve
rse B F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Impl) A preliminary definition to avoid timeouts.
-/
def conesEquivUnitIso (B : C) (F : Discrete J ⥤ Over B) :
    𝟭 (Cone (widePullbackDiagramOfDiagramOver B F)) ≅
      conesEquivFunctor B F ⋙ conesEquivInverse B F :=
  NatIso.ofComponents fun _ => Cone.ext
    { hom := 𝟙 _
      inv := 𝟙 _ }
    (by rintro (j | j) <;> cat_disch)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
-- TODO: Can we add `:= by aesop` to the second arguments of `NatIso.ofComponents` and
--       `Cone.ext`?
/-- (Impl) A preliminary definition to avoid timeouts. -/
@[simps!]
/-
**CategoryTheory.Over.ConstructProducts.conesEquivCounitIso** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Over.ConstructProducts`。
形式化陈述：{J : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       (B : C) →         (F : CategoryTheory.Functor (CategoryTheory.Discre
te J) (CategoryTheory.Over B)) →           (CategoryTheory.Over.ConstructProduct
s.conesEquivInverse B F).comp               (CategoryTheory.Over.ConstructProduc
ts.conesEquivFunctor B F) ≅             CategoryTheory.Functor.id (CategoryTheor
y.Limits.Cone F)
参数：B : C；F : CategoryTheory.Functor (CategoryTheory.Discrete J) (CategoryTheory.
Over B)；CategoryTheory.Over.ConstructProducts.conesEquivInverse B F；CategoryTheo
ry.Over.ConstructProducts.conesEquivFunctor B F；CategoryTheory.Limits.Cone F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Impl) A preliminary definition to avoid timeouts.
-/
def conesEquivCounitIso (B : C) (F : Discrete J ⥤ Over B) :
    conesEquivInverse B F ⋙ conesEquivFunctor B F ≅ 𝟭 (Cone F) :=
  NatIso.ofComponents fun _ => Cone.ext
    { hom := Over.homMk (𝟙 _)
      inv := Over.homMk (𝟙 _) }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- (Impl) Establish an equivalence between the category of cones for `F` and for the "grown" `F`.
-/
@[simps]
/-
**CategoryTheory.Over.ConstructProducts.conesEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Over.ConstructProducts`。
形式化陈述：{J : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       (B : C) →         (F : CategoryTheory.Functor (CategoryTheory.Discre
te J) (CategoryTheory.Over B)) →           CategoryTheory.Limits.Cone (CategoryT
heory.Over.ConstructProducts.widePullbackDiagramOfDiagramOver B F) ≌            
 CategoryTheory.Limits.Cone F
参数：B : C；F : CategoryTheory.Functor (CategoryTheory.Discrete J) (CategoryTheory.
Over B)；CategoryTheory.Over.ConstructProducts.widePullbackDiagramOfDiagramOver B
 F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Impl) Establish an equivalence between the category of cones for `F` and for th
e "grown" `F`.
-/
def conesEquiv (B : C) (F : Discrete J ⥤ Over B) :
    Cone (widePullbackDiagramOfDiagramOver B F) ≌ Cone F where
  functor := conesEquivFunctor B F
  inverse := conesEquivInverse B F
  unitIso := conesEquivUnitIso B F
  counitIso := conesEquivCounitIso B F

/-- Use the above equivalence to prove we have a limit. -/
/-
**CategoryTheory.Over.ConstructProducts.has_over_limit_discrete_of_widePullback_
limit** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Over.ConstructProducts`。
形式化陈述：∀ {J : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {B :
 C}   (F : CategoryTheory.Functor (CategoryTheory.Discrete J) (CategoryTheory.Ov
er B))   [CategoryTheory.Limits.HasLimit (CategoryTheory.Over.ConstructProducts.
widePullbackDiagramOfDiagramOver B F)],   CategoryTheory.Limits.HasLimit F
参数：F : CategoryTheory.Functor (CategoryTheory.Discrete J) (CategoryTheory.Over B
)；CategoryTheory.Over.ConstructProducts.widePullbackDiagramOfDiagramOver B F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…

--- 原说明 ---
Use the above equivalence to prove we have a limit.
-/
theorem has_over_limit_discrete_of_widePullback_limit {B : C} (F : Discrete J ⥤ Over B)
    [HasLimit (widePullbackDiagramOfDiagramOver B F)] : HasLimit F :=
  HasLimit.mk
    { cone := _
      isLimit := IsLimit.ofRightAdjoint (conesEquiv B F).symm.toAdjunction
        (limit.isLimit (widePullbackDiagramOfDiagramOver B F)) }

/-- Given a wide pullback in `C`, construct a product in `C/B`. -/
/-
**CategoryTheory.Over.ConstructProducts.over_product_of_widePullback** 是 Mathlib
 中的一个定理，位于命名空间 `CategoryTheory.Over.ConstructProducts`。
形式化陈述：∀ {J : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   [C
ategoryTheory.Limits.HasLimitsOfShape (CategoryTheory.Limits.WidePullbackShape J
) C] {B : C},   CategoryTheory.Limits.HasLimitsOfShape (CategoryTheory.Discrete 
J) (CategoryTheory.Over B)
参数：CategoryTheory.Limits.WidePullbackShape J；CategoryTheory.Discrete J；CategoryT
heory.Over B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Over.ConstructProducts.has_over_limit_discrete_of_widePul
lback_limit`：∀ {J : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} 
C] {B : C}   (F : CategoryTheory.Functor (CategoryTheory.Discrete J) (Cat…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…

--- 原说明 ---
Given a wide pullback in `C`, construct a product in `C/B`.
-/
theorem over_product_of_widePullback [HasLimitsOfShape (WidePullbackShape J) C] {B : C} :
    HasLimitsOfShape (Discrete J) (Over B) :=
  { has_limit := fun F => has_over_limit_discrete_of_widePullback_limit F }

/-- Given a pullback in `C`, construct a binary product in `C/B`. -/
/-
**CategoryTheory.Over.ConstructProducts.over_binaryProduct_of_pullback** 是 Mathl
ib 中的一个定理，位于命名空间 `CategoryTheory.Over.ConstructProducts`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.L
imits.HasPullbacks C] {B : C},   CategoryTheory.Limits.HasBinaryProducts (Catego
ryTheory.Over B)
参数：CategoryTheory.Over B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Over.ConstructProducts.over_product_of_widePullback`：∀ {J
 : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   [CategoryThe
ory.Limits.HasLimitsOfShape (CategoryTheory.Limits.WideP…

--- 原说明 ---
Given a pullback in `C`, construct a binary product in `C/B`.
-/
theorem over_binaryProduct_of_pullback [HasPullbacks C] {B : C} : HasBinaryProducts (Over B) :=
  over_product_of_widePullback

/-- Given all wide pullbacks in `C`, construct products in `C/B`. -/
/-
**CategoryTheory.Over.ConstructProducts.over_products_of_widePullbacks** 是 Mathl
ib 中的一个定理，位于命名空间 `CategoryTheory.Over.ConstructProducts`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.L
imits.HasWidePullbacks C] {B : C},   CategoryTheory.Limits.HasProducts (Category
Theory.Over B)
参数：CategoryTheory.Over B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Over.ConstructProducts.over_product_of_widePullback`：∀ {J
 : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   [CategoryThe
ory.Limits.HasLimitsOfShape (CategoryTheory.Limits.WideP…

--- 原说明 ---
Given all wide pullbacks in `C`, construct products in `C/B`.
-/
theorem over_products_of_widePullbacks [HasWidePullbacks.{w} C] {B : C} :
    HasProducts.{w} (Over B) :=
  fun _ => over_product_of_widePullback

/-- Given all finite wide pullbacks in `C`, construct finite products in `C/B`. -/
/-
**CategoryTheory.Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbac
ks** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Over.ConstructProducts`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.L
imits.HasFiniteWidePullbacks C] {B : C},   CategoryTheory.Limits.HasFiniteProduc
ts (CategoryTheory.Over B)
参数：CategoryTheory.Over B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Over.ConstructProducts.over_product_of_widePullback`：∀ {J
 : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   [CategoryThe
ory.Limits.HasLimitsOfShape (CategoryTheory.Limits.WideP…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
Given all finite wide pullbacks in `C`, construct finite products in `C/B`.
-/
theorem over_finiteProducts_of_finiteWidePullbacks [HasFiniteWidePullbacks C] {B : C} :
    HasFiniteProducts (Over B) :=
  ⟨fun _ => over_product_of_widePullback⟩

end ConstructProducts

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Construct terminal object in the over category. This isn't an instance as it's not typically the
way we want to define terminal objects.
(For instance, this gives a terminal object which is different from the generic one given by
`over_product_of_widePullback` above.)
-/
/-
**CategoryTheory.Over.over_hasTerminal** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Over`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (B : C),   Catego
ryTheory.Limits.HasTerminal (CategoryTheory.Over B)
参数：B : C；CategoryTheory.Over B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Aesop.BuiltinRules.pEmpty_false`：∀ (h : PEmpty.{u_1}), False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Over.OverMorphism.ext`：∀ {T : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Over X} {f g : U ⟶ V},  
 CategoryTheory.Over.Hom.l…
· 使用定理 `CategoryTheory.Over.Hom.w`：∀ {T : Type u₁} [inst : CategoryTheory.Catego
ry.{v₁, u₁} T] {X : T} {f g : CategoryTheory.Over X} (φ : f ⟶ g),   CategoryTheo
ry.CategoryStru…

--- 原说明 ---
Construct terminal object in the over category. This isn't an instance as it's n
ot typically the
way we want to define terminal objects.
(For instance, this gives a terminal object which is different from the generic 
one given by
`over_product_of_widePullback` above.)
-/
theorem over_hasTerminal (B : C) : HasTerminal (Over B) where
  has_limit F := HasLimit.mk
    { cone :=
        { pt := Over.mk (𝟙 _)
          π :=
            { app := fun p => p.as.elim } }
      isLimit :=
        { lift s := Over.homMk s.pt.hom
          fac _ j := j.as.elim
          uniq s m _ := by ext; simpa using m.w } }

end CategoryTheory.Over

