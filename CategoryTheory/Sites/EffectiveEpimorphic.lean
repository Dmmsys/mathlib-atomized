/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.CategoryTheory.Sites.SheafOfTypes
public import Mathlib.CategoryTheory.EffectiveEpi.Basic

/-!

# Effective epimorphic sieves

We define the notion of effective epimorphic (pre)sieves and provide some API for relating the
notion with the notions of effective epimorphism and effective epimorphic family.

More precisely, if `f` is a morphism, then `f` is an effective epi if and only if the sieve
it generates is effective epimorphic; see `CategoryTheory.Sieve.effectiveEpimorphic_singleton`.
The analogous statement for a family of morphisms is in the theorem
`CategoryTheory.Sieve.effectiveEpimorphic_family`.

-/

universe w v u

@[expose] public section

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

/-- A sieve is effective epimorphic if the associated cocone is a colimit cocone. -/
/-
**CategoryTheory.Sieve.EffectiveEpimorphic** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Sieve`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → {X : C} → Categ
oryTheory.Sieve X → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sieve is effective epimorphic if the associated cocone is a colimit cocone.
-/
def Sieve.EffectiveEpimorphic {X : C} (S : Sieve X) : Prop :=
  Nonempty (IsColimit (S : Presieve X).cocone)

/-- A presieve is effective epimorphic if the cocone associated to the sieve it generates
is a colimit cocone. -/
/-
**CategoryTheory.Presieve.EffectiveEpimorphic** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Presieve`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → {X : C} → Categ
oryTheory.Presieve X → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A presieve is effective epimorphic if the cocone associated to the sieve it gene
rates
is a colimit cocone.
-/
abbrev Presieve.EffectiveEpimorphic {X : C} (S : Presieve X) : Prop :=
  (Sieve.generate S).EffectiveEpimorphic

/--
The sieve of morphisms which factor through a given morphism `f`.
This is equal to `Sieve.generate (Presieve.singleton f)`, but has
more convenient definitional properties.
-/
/-
**CategoryTheory.Sieve.generateSingleton** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Sieve`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → {X Y : C} → (Y 
⟶ X) → CategoryTheory.Sieve X
参数：Y ⟶ X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sieve of morphisms which factor through a given morphism `f`.
This is equal to `Sieve.generate (Presieve.singleton f)`, but has
more convenient definitional properties.
-/
def Sieve.generateSingleton {X Y : C} (f : Y ⟶ X) : Sieve X where
  arrows Z g := ∃ (e : Z ⟶ Y), e ≫ f = g
  downward_closed := by
    rintro W Z g ⟨e, rfl⟩ q
    exact ⟨q ≫ e, by simp⟩
/-
**CategoryTheory.Sieve.generateSingleton_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Sieve`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (f : Y 
⟶ X),   CategoryTheory.Sieve.generate (CategoryTheory.Presieve.singleton f) = Ca
tegoryTheory.Sieve.generateSingleton f
参数：f : Y ⟶ X；CategoryTheory.Presieve.singleton f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.ext`：∀ {C : Type u₁} [inst : CategoryTheory.Categor
y.{v₁, u₁} C] {X : C} {R S : CategoryTheory.Sieve X},   (∀ ⦃Y : C⦄ (f : Y ⟶ X), 
R.arrows f ↔ S…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma Sieve.generateSingleton_eq {X Y : C} (f : Y ⟶ X) :
    Sieve.generate (Presieve.singleton f) = Sieve.generateSingleton f := by
  ext Z g
  constructor
  · rintro ⟨W, i, p, ⟨⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨g, h⟩
    exact ⟨Y, g, f, ⟨⟩, h⟩
/-
**CategoryTheory.Sieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.Sieve.EffectiveEpimorphic`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X : C} (S : Cate
goryTheory.Sieve X),   S.EffectiveEpimorphic ↔ ∀ (Y : C), CategoryTheory.Presiev
e.IsSheafFor (CategoryTheory.yoneda.obj Y) S.arrows
参数：S : CategoryTheory.Sieve X；Y : C；CategoryTheory.yoneda.obj Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `CategoryTheory.Sieve.forallYonedaIsSheaf_iff_colimit`：forallYonedaIsShea
f_iff_colimit (S : Sieve X) : (forall W : C, Presieve.IsSheafFor (yoneda.obj W) 
(S : Presieve X)) ↔ Nonempty (IsColimit S.…
-/
lemma Sieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda {X : C} (S : Sieve X) :
    S.EffectiveEpimorphic ↔ ∀ Y, S.arrows.IsSheafFor (yoneda.obj Y) :=
  S.forallYonedaIsSheaf_iff_colimit.symm
/-
**CategoryTheory.Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda** 是 M
athlib 中的一个定理，位于命名空间 `CategoryTheory.Presieve.EffectiveEpimorphic`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X : C} (R : Cate
goryTheory.Presieve X),   R.EffectiveEpimorphic ↔ ∀ (Y : C), CategoryTheory.Pres
ieve.IsSheafFor (CategoryTheory.yoneda.obj Y) R
参数：R : CategoryTheory.Presieve X；Y : C；CategoryTheory.yoneda.obj Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `CategoryTheory.Presieve.isSheafFor_iff_generate`：isSheafFor_iff_generate
 (R : Presieve X) : IsSheafFor P R ↔ IsSheafFor P (generate R : Presieve X)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda {X : C} (R : Presieve X) :
    R.EffectiveEpimorphic ↔ ∀ Y, R.IsSheafFor (yoneda.obj Y) := by
  simp_rw [Presieve.isSheafFor_iff_generate R,
    Presieve.EffectiveEpimorphic, Sieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda]

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Presieve.EffectiveEpimorphic.isSheafFor_of_isRepresentable** 是 
Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Presieve.EffectiveEpimorphic`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X : C} {R : Cate
goryTheory.Presieve X},   R.EffectiveEpimorphic →     ∀ (F : CategoryTheory.Func
tor Cᵒᵖ (Type w)) [F.IsRepresentable], CategoryTheory.Presieve.IsSheafFor F R
参数：F : CategoryTheory.Functor Cᵒᵖ (Type w)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Presieve.isSheafFor_comp_uliftFunctor_iff`：isSheafFor_com
p_uliftFunctor_iff {R : Presieve X} : R.IsSheafFor (P ⋙ uliftFunctor.{w'}) ↔ R.I
sSheafFor P
· 使用定理 `CategoryTheory.Presieve.isSheafFor_iso`：isSheafFor_iso {P' : Cᵒᵖ ⥤ Type 
w} (i : P ≅ P') (hP : IsSheafFor P R) : IsSheafFor P' R
· 使用定理 `CategoryTheory.Functor.instIsRepresentableCompOppositeUliftFunctor`：∀ {C
 : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (F : CategoryTheory.Func
tor Cᵒᵖ (Type v))   [F.IsRepresentable], (F.comp Categor…
· 使用定理 `CategoryTheory.Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda
`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X : C} (R : Category
Theory.Presieve X),   R.EffectiveEpimorphic ↔ ∀ (Y : C), Categ…
-/
lemma Presieve.EffectiveEpimorphic.isSheafFor_of_isRepresentable {X : C} {R : Presieve X}
    (hR : R.EffectiveEpimorphic) (F : Cᵒᵖ ⥤ Type w) [F.IsRepresentable] :
    R.IsSheafFor F := by
  rw [Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda] at hR
  rw [← isSheafFor_comp_uliftFunctor_iff]
  refine Presieve.isSheafFor_iso (F ⋙ uliftFunctor.{v}).uliftYonedaReprXIso ?_
  dsimp only [uliftYoneda, Functor.comp_obj, Functor.whiskeringRight_obj_obj]
  rw [isSheafFor_comp_uliftFunctor_iff]
  exact hR _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Implementation: This is a construction which will be used in the proof that
the sieve generated by a single arrow is effective epimorphic if and only if
the arrow is an effective epi.
-/
/-
**CategoryTheory.isColimitOfEffectiveEpiStruct** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory`。
形式化陈述：isColimitOfEffectiveEpiStruct {X Y : C} (f : Y ⟶ X) (Hf : EffectiveEpiStru
ct f) : IsColimit (Sieve.generateSingleton f : Presieve X).cocone
参数：f : Y ⟶ X；Hf : EffectiveEpiStruct f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implementation: This is a construction which will be used in the proof that
the sieve generated by a single arrow is effective epimorphic if and only if
the arrow is an effective epi.
-/
def isColimitOfEffectiveEpiStruct {X Y : C} (f : Y ⟶ X) (Hf : EffectiveEpiStruct f) :
    IsColimit (Sieve.generateSingleton f : Presieve X).cocone :=
  letI D := ObjectProperty.FullSubcategory fun T : Over X => Sieve.generateSingleton f T.hom
  letI F : D ⥤ _ := (Sieve.generateSingleton f).arrows.diagram
  { desc := fun S => Hf.desc (S.ι.app ⟨Over.mk f, ⟨𝟙 _, by simp⟩⟩) <| by
      intro Z g₁ g₂ h
      let Y' : D := ⟨Over.mk f, 𝟙 _, by simp⟩
      let Z' : D := ⟨Over.mk (g₁ ≫ f), g₁, rfl⟩
      let g₁' : Z' ⟶ Y' := ObjectProperty.homMk (Over.homMk g₁)
      let g₂' : Z' ⟶ Y' := ObjectProperty.homMk (Over.homMk g₂ (by simp [Y', Z', h]))
      change F.map g₁' ≫ _ = F.map g₂' ≫ _
      simp only [Y', F, S.w]
    fac := by
      rintro S ⟨T, g, hT⟩
      dsimp
      generalize_proofs h₁ h₂ h₃
      simp only [← hT, Category.assoc, Hf.fac _ h₂]
      let y : D := ⟨Over.mk f, 𝟙 _, by simp⟩
      let x : D := ⟨Over.mk T.hom, g, hT⟩
      let g' : x ⟶ y := ObjectProperty.homMk (Over.homMk g)
      change F.map g' ≫ _ = _
      rw [S.w]
      rfl
    uniq := by
      intro S m hm
      dsimp
      generalize_proofs h1 h2
      apply Hf.uniq _ h2
      exact hm ⟨Over.mk f, 𝟙 _, by simp⟩ }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Implementation: This is a construction which will be used in the proof that
the sieve generated by a single arrow is effective epimorphic if and only if
the arrow is an effective epi.
-/
noncomputable
/-
**CategoryTheory.effectiveEpiStructOfIsColimit** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory`。
形式化陈述：effectiveEpiStructOfIsColimit {X Y : C} (f : Y ⟶ X) (Hf : IsColimit (Sieve
.generateSingleton f : Presieve X).cocone) : EffectiveEpiStruct f
参数：f : Y ⟶ X；Hf : IsColimit (Sieve.generateSingleton f : Presieve X).cocone。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def effectiveEpiStructOfIsColimit {X Y : C} (f : Y ⟶ X)
    (Hf : IsColimit (Sieve.generateSingleton f : Presieve X).cocone) :
    EffectiveEpiStruct f :=
  let aux {W : C} (e : Y ⟶ W)
    (h : ∀ {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f → g₁ ≫ e = g₂ ≫ e) :
    Cocone (Sieve.generateSingleton f).arrows.diagram :=
    { pt := W
      ι := {
        app := fun ⟨_,hT⟩ => hT.choose ≫ e
        naturality := by
          rintro ⟨A, hA⟩ ⟨B, hB⟩ ⟨q : A ⟶ B⟩
          dsimp; simp only [← Category.assoc, Category.comp_id]
          apply h
          rw [Category.assoc, hB.choose_spec, hA.choose_spec, Over.w] } }
  { desc := fun {_} e h => Hf.desc (aux e h)
    fac {W} e h := by
      have := Hf.fac (aux e h) ⟨Over.mk f, 𝟙 _, by simp⟩
      dsimp [aux] at this; rw [this]; clear this
      nth_rewrite 2 [← Category.id_comp e]
      apply h
      generalize_proofs hh
      rw [hh.choose_spec, Category.id_comp]
    uniq {W} e h m hm := by
      apply Hf.uniq (aux e h)
      rintro ⟨A, g, hA⟩
      dsimp
      simp only [← hA, Category.assoc, hm]
      apply h
      generalize_proofs hh
      rwa [hh.choose_spec] }
/-
**CategoryTheory.Sieve.effectiveEpimorphic_singleton** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Sieve`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (f : Y 
⟶ X),   (CategoryTheory.Presieve.singleton f).EffectiveEpimorphic ↔ CategoryTheo
ry.EffectiveEpi f
参数：f : Y ⟶ X；CategoryTheory.Presieve.singleton f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Sieve.generateSingleton_eq`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {X Y : C} (f : Y ⟶ X),   CategoryTheory.Sieve.genera
te (CategoryTheory.Presieve.sin…
-/
theorem Sieve.effectiveEpimorphic_singleton {X Y : C} (f : Y ⟶ X) :
    (Presieve.singleton f).EffectiveEpimorphic ↔ (EffectiveEpi f) := by
  constructor
  · intro (h : Nonempty _)
    rw [Sieve.generateSingleton_eq] at h
    constructor
    apply Nonempty.map (effectiveEpiStructOfIsColimit _) h
  · rintro ⟨h⟩
    change Nonempty _
    rw [Sieve.generateSingleton_eq]
    apply Nonempty.map (isColimitOfEffectiveEpiStruct _) h
/-
**CategoryTheory.Presieve.IsSheafFor.singleton_of_isRepresentable_of_effectiveEp
i** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Presieve.IsSheafFor`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (f : X 
⟶ Y) [CategoryTheory.EffectiveEpi f]   (F : CategoryTheory.Functor Cᵒᵖ (Type u_1
)) [F.IsRepresentable],   CategoryTheory.Presieve.IsSheafFor F (CategoryTheory.P
resieve.singleton f)
参数：f : X ⟶ Y；F : CategoryTheory.Functor Cᵒᵖ (Type u_1)；CategoryTheory.Presieve.s
ingleton f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.EffectiveEpimorphic.isSheafFor_of_isRepresentabl
e`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X : C} {R : Categor
yTheory.Presieve X},   R.EffectiveEpimorphic →     ∀ (F : Categ…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Sieve.effectiveEpimorphic_singleton`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] {X Y : C} (f : Y ⟶ X),   (CategoryTheory.Pr
esieve.singleton f).EffectiveEpimorphic …
-/
lemma Presieve.IsSheafFor.singleton_of_isRepresentable_of_effectiveEpi {X Y : C} (f : X ⟶ Y)
    [EffectiveEpi f] (F : Cᵒᵖ ⥤ Type*) [F.IsRepresentable] :
    (Presieve.singleton f).IsSheafFor F :=
  Presieve.EffectiveEpimorphic.isSheafFor_of_isRepresentable
    ((Sieve.effectiveEpimorphic_singleton f).mpr ‹_›) _

/--
The sieve of morphisms which factor through a morphism in a given family.
This is equal to `Sieve.generate (Presieve.ofArrows X π)`, but has
more convenient definitional properties.
-/
/-
**CategoryTheory.Sieve.generateFamily** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Sieve`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {B : C} →
 {α : Type u_1} → (X : α → C) → ((a : α) → X a ⟶ B) → CategoryTheory.Sieve B
参数：X : α → C；(a : α) → X a ⟶ B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sieve of morphisms which factor through a morphism in a given family.
This is equal to `Sieve.generate (Presieve.ofArrows X π)`, but has
more convenient definitional properties.
-/
def Sieve.generateFamily {B : C} {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B)) :
    Sieve B where
  arrows Y f := ∃ (a : α) (g : Y ⟶ X a), g ≫ π a = f
  downward_closed := by
    rintro Y₁ Y₂ g₁ ⟨a, q, rfl⟩ e
    exact ⟨a, e ≫ q, by simp⟩
/-
**CategoryTheory.Sieve.generateFamily_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Sieve`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {B : C} {α : Type
 u_1} (X : α → C) (π : (a : α) → X a ⟶ B),   CategoryTheory.Sieve.generate (Cate
goryTheory.Presieve.ofArrows X π) = CategoryTheory.Sieve.generateFamily X π
参数：X : α → C；π : (a : α) → X a ⟶ B；CategoryTheory.Presieve.ofArrows X π。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sieve.ext`：∀ {C : Type u₁} [inst : CategoryTheory.Categor
y.{v₁, u₁} C] {X : C} {R S : CategoryTheory.Sieve X},   (∀ ⦃Y : C⦄ (f : Y ⟶ X), 
R.arrows f ↔ S…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma Sieve.generateFamily_eq {B : C} {α : Type*} (X : α → C) (π : (a : α) → (X a ⟶ B)) :
    Sieve.generate (Presieve.ofArrows X π) = Sieve.generateFamily X π := by
  ext Y g
  constructor
  · rintro ⟨W, g, f, ⟨a⟩, rfl⟩
    exact ⟨a, g, rfl⟩
  · rintro ⟨a, g, rfl⟩
    exact ⟨_, g, π a, ⟨a⟩, rfl⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Implementation: This is a construction which will be used in the proof that
the sieve generated by a family of arrows is effective epimorphic if and only if
the family is an effective epi.
-/
/-
**CategoryTheory.isColimitOfEffectiveEpiFamilyStruct** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory`。
形式化陈述：isColimitOfEffectiveEpiFamilyStruct {B : C} {α : Type*} (X : α -> C) (π : 
(a : α) -> (X a ⟶ B)) (H : EffectiveEpiFamilyStruct X π) : IsColimit (Sieve.gene
rateFamily X π : Presieve B).cocone
参数：X : α -> C；π : (a : α) -> (X a ⟶ B)；H : EffectiveEpiFamilyStruct X π。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implementation: This is a construction which will be used in the proof that
the sieve generated by a family of arrows is effective epimorphic if and only if
the family is an effective epi.
-/
def isColimitOfEffectiveEpiFamilyStruct {B : C} {α : Type*}
    (X : α → C) (π : (a : α) → (X a ⟶ B)) (H : EffectiveEpiFamilyStruct X π) :
    IsColimit (Sieve.generateFamily X π : Presieve B).cocone :=
  letI D := ObjectProperty.FullSubcategory fun T : Over B => Sieve.generateFamily X π T.hom
  letI F : D ⥤ _ := (Sieve.generateFamily X π).arrows.diagram
  { desc := fun S => H.desc (fun a => S.ι.app ⟨Over.mk (π a), ⟨a,𝟙 _, by simp⟩⟩) <| by
      intro Z a₁ a₂ g₁ g₂ h
      let A₁ : D := ⟨Over.mk (π a₁), a₁, 𝟙 _, by simp⟩
      let A₂ : D := ⟨Over.mk (π a₂), a₂, 𝟙 _, by simp⟩
      let Z' : D := ⟨Over.mk (g₁ ≫ π a₁), a₁, g₁, rfl⟩
      let i₁ : Z' ⟶ A₁ := ObjectProperty.homMk (Over.homMk g₁)
      let i₂ : Z' ⟶ A₂ := ObjectProperty.homMk (Over.homMk g₂)
      change F.map i₁ ≫ _ = F.map i₂ ≫ _
      simp only [F, A₁, A₂, S.w]
    fac := by
      intro S ⟨T, a, (g : T.left ⟶ X a), hT⟩
      dsimp
      generalize_proofs h₁ h₂ h₃
      simp only [← hT, Category.assoc, H.fac _ h₂]
      let A : D := ⟨Over.mk (π a), a, 𝟙 _, by simp⟩
      let B : D := ⟨Over.mk T.hom, a, g, hT⟩
      let i : B ⟶ A := ObjectProperty.homMk (Over.homMk g)
      change F.map i ≫ _ = _
      rw [S.w]
      rfl
    uniq := by
      intro S m hm; dsimp
      generalize_proofs h₁ h₂
      apply H.uniq _ h₂
      intro a
      exact hm ⟨Over.mk (π a), a, 𝟙 _, by simp⟩ }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Implementation: This is a construction which will be used in the proof that
the sieve generated by a family of arrows is effective epimorphic if and only if
the family is an effective epi.
-/
noncomputable
/-
**CategoryTheory.effectiveEpiFamilyStructOfIsColimit** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory`。
形式化陈述：effectiveEpiFamilyStructOfIsColimit {B : C} {α : Type*} (X : α -> C) (π : 
(a : α) -> (X a ⟶ B)) (H : IsColimit (Sieve.generateFamily X π : Presieve B).coc
one) : EffectiveEpiFamilyStruct X π
参数：X : α -> C；π : (a : α) -> (X a ⟶ B)；H : IsColimit (Sieve.generateFamily X π :
 Presieve B).cocone。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def effectiveEpiFamilyStructOfIsColimit {B : C} {α : Type*}
    (X : α → C) (π : (a : α) → (X a ⟶ B))
    (H : IsColimit (Sieve.generateFamily X π : Presieve B).cocone) :
    EffectiveEpiFamilyStruct X π :=
  let aux {W : C} (e : (a : α) → (X a ⟶ W))
    (h : ∀ {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
      g₁ ≫ π _ = g₂ ≫ π _ → g₁ ≫ e _ = g₂ ≫ e _) :
    Cocone (Sieve.generateFamily X π).arrows.diagram := {
      pt := W
      ι := {
        app := fun ⟨_, hT⟩ => hT.choose_spec.choose ≫ e hT.choose
        naturality := by
          rintro ⟨A, a, (g₁ : A.left ⟶ _), ha⟩ ⟨B, b, (g₂ : B.left ⟶ _), hb⟩ ⟨q : A ⟶ B⟩
          dsimp; rw [Category.comp_id, ← Category.assoc]
          apply h; rw [Category.assoc]
          generalize_proofs h1 h2 h3 h4
          rw [h2.choose_spec, h4.choose_spec, Over.w] } }
  { desc := fun {_} e h => H.desc (aux e h)
    fac {W} e h a := by
      have := H.fac (aux e h) ⟨Over.mk (π a), a, 𝟙 _, by simp⟩
      dsimp [aux] at this; rw [this]; clear this
      conv_rhs => rw [← Category.id_comp (e a)]
      apply h
      generalize_proofs h1 h2
      rw [h2.choose_spec, Category.id_comp]
    uniq {W} e h m hm := by
      apply H.uniq (aux e h)
      rintro ⟨T, a, (g : T.left ⟶ _), ha⟩
      dsimp
      simp only [← ha, Category.assoc, hm]
      apply h
      generalize_proofs h1 h2
      rwa [h2.choose_spec] }
/-
**CategoryTheory.Sieve.effectiveEpimorphic_family** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Sieve`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {B : C} {α : Type
 u_1} (X : α → C) (π : (a : α) → X a ⟶ B),   (CategoryTheory.Presieve.ofArrows X
 π).EffectiveEpimorphic ↔ CategoryTheory.EffectiveEpiFamily X π
参数：X : α → C；π : (a : α) → X a ⟶ B；CategoryTheory.Presieve.ofArrows X π。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Sieve.generateFamily_eq`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {B : C} {α : Type u_1} (X : α → C) (π : (a : α) → X a ⟶
 B),   CategoryTheory.Sieve.…
-/
theorem Sieve.effectiveEpimorphic_family {B : C} {α : Type*}
    (X : α → C) (π : (a : α) → (X a ⟶ B)) :
    (Presieve.ofArrows X π).EffectiveEpimorphic ↔ EffectiveEpiFamily X π := by
  constructor
  · intro (h : Nonempty _)
    rw [Sieve.generateFamily_eq] at h
    constructor
    apply Nonempty.map (effectiveEpiFamilyStructOfIsColimit _ _) h
  · rintro ⟨h⟩
    change Nonempty _
    rw [Sieve.generateFamily_eq]
    apply Nonempty.map (isColimitOfEffectiveEpiFamilyStruct _ _) h

end CategoryTheory

