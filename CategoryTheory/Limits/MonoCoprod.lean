/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.Forget
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!

# Categories where inclusions into coproducts are monomorphisms

If `C` is a category, the class `MonoCoprod C` expresses that left
inclusions `A ⟶ A ⨿ B` are monomorphisms when `HasCoproduct A B`
holds. If so, it is shown that right inclusions are
also monomorphisms.

More generally, we deduce that when suitable coproducts exist, then
if `X : I → C` and `ι : J → I` is an injective map,
then the canonical morphism `∐ (X ∘ ι) ⟶ ∐ X` is a monomorphism.
It also follows that for any `i : I`, `Sigma.ι X i : X i ⟶ ∐ X` is
a monomorphism.

TODO: define distributive categories, and show that they satisfy `MonoCoprod`, see
<https://ncatlab.org/toddtrimble/published/distributivity+implies+monicity+of+coproduct+inclusions>

-/

@[expose] public section


noncomputable section

universe u

namespace CategoryTheory

open CategoryTheory.Category CategoryTheory.Limits

namespace Limits

variable (C : Type*) [Category* C]

/--
Definition of `MonoCoprod` / `MonoCoprod` 的定义

English:
class MonoCoprod
  parameters: : Prop where
  axioms and operations (1):
    - binaryCofan_inl : forall ⦃A B : C⦄ (c : BinaryCofan A B) (_ : IsColimit c), Mono c.inl

中文:
类 MonoCoprod
  参数: : 命题 where
  公理与运算 (1 个):
    - binaryCofan_inl : 对任意 ⦃A B : C⦄ (c : BinaryCofan A B) (_ : IsColimit c), Mono c.inl
-/
class MonoCoprod : Prop where
  /-- the left inclusion of a colimit binary cofan is mono -/
  binaryCofan_inl : forall ⦃A B : C⦄ (c : BinaryCofan A B) (_ : IsColimit c), Mono c.inl

variable {C}

instance (priority := 100) monoCoprodOfHasZeroMorphisms [HasZeroMorphisms C] : MonoCoprod C :=
  ⟨fun A B c hc => by
    have : IsSplitMono c.inl :=
      IsSplitMono.mk' (SplitMono.mk (BinaryCofan.IsColimit.desc hc (𝟙 A) 0) (IsColimit.fac _ _ _))
    infer_instance⟩

namespace MonoCoprod

set_option backward.isDefEq.respectTransparency false in
/--
theorem `binaryCofan_inr` / 定理 `binaryCofan_inr`

English:
theorem binaryCofan_inr
  given: {A B : C} [MonoCoprod C] (c : BinaryCofan A B) (hc : IsColimit c)
  proof: by
  have hc' : IsColimit (BinaryCofan.mk c.inr c.inl) :=
    BinaryCofan.IsColimit.mk _
      (fun f₁ f₂ => BinaryCofan.IsColimit.desc (s := c) hc f₂ f₁)
      (by simp) (by simp)
      (fun f₁ f₂ m h₁ h₂ => BinaryCofan.IsColimit.hom_ext hc (by cat_disch) (by cat_disch))
  exact binaryCofan_inl _ h

中文:
定理 binaryCofan_inr
  条件: {A B : C} [MonoCoprod C] (c : BinaryCofan A B) (hc : IsColimit c)
  证明: by
  have hc' : IsColimit (BinaryCofan.mk c.inr c.inl) :=
    BinaryCofan.IsColimit.mk _
      (fun f₁ f₂ => BinaryCofan.IsColimit.desc (s := c) hc f₂ f₁)
      (by simp) (by simp)
      (fun f₁ f₂ m h₁ h₂ => BinaryCofan.IsColimit.hom_ext hc (by cat_disch) (by cat_disch))
  exact binaryCofan_inl _ h

Depends on / 依赖: BinaryCofan, BinaryCofan.IsColimit.desc, BinaryCofan.IsColimit.hom_ext, BinaryCofan.IsColimit.mk, BinaryCofan.mk, IsColimit, binaryCofan_inl, c.inl, c.inr, cat_disch, hom_ext
-/
theorem binaryCofan_inr {A B : C} [MonoCoprod C] (c : BinaryCofan A B) (hc : IsColimit c) :
    Mono c.inr := by
  have hc' : IsColimit (BinaryCofan.mk c.inr c.inl) :=
    BinaryCofan.IsColimit.mk _
      (fun f₁ f₂ => BinaryCofan.IsColimit.desc (s := c) hc f₂ f₁)
      (by simp) (by simp)
      (fun f₁ f₂ m h₁ h₂ => BinaryCofan.IsColimit.hom_ext hc (by cat_disch) (by cat_disch))
  exact binaryCofan_inl _ hc'

instance {A B : C} [MonoCoprod C] [HasBinaryCoproduct A B] : Mono (coprod.inl : A ⟶ A ⨿ B) :=
  binaryCofan_inl _ (colimit.isColimit _)

instance {A B : C} [MonoCoprod C] [HasBinaryCoproduct A B] : Mono (coprod.inr : B ⟶ A ⨿ B) :=
  binaryCofan_inr _ (colimit.isColimit _)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mono_inl_iff` / 定理 `mono_inl_iff`

English:
theorem mono_inl_iff
  given: {A B : C} {c₁ c₂ : BinaryCofan A B} (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂)
  proof: by
  suffices
    forall (c₁ c₂ : BinaryCofan A B) (_ : IsColimit c₁) (_ : IsColimit c₂) (_ : Mono c₁.inl),
      Mono c₂.inl
    ⟨fun h₁ => this _ _ hc₁ hc₂ h₁, fun h₂ => this _ _ hc₂ hc₁ h₂⟩
  intro c₁ c₂ hc₁ hc₂ _
  simpa only [IsColimit.comp_coconePointUniqueUpToIso_hom] using!
    mono_comp c₁.

中文:
定理 mono_inl_iff
  条件: {A B : C} {c₁ c₂ : BinaryCofan A B} (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂)
  证明: by
  suffices
    forall (c₁ c₂ : BinaryCofan A B) (_ : IsColimit c₁) (_ : IsColimit c₂) (_ : Mono c₁.inl),
      Mono c₂.inl
    ⟨fun h₁ => this _ _ hc₁ hc₂ h₁, fun h₂ => this _ _ hc₂ hc₁ h₂⟩
  intro c₁ c₂ hc₁ hc₂ _
  simpa only [IsColimit.comp_coconePointUniqueUpToIso_hom] using!
    mono_comp c₁.

Depends on / 依赖: BinaryCofan, IsColimit, IsColimit.comp_coconePointUniqueUpToIso_hom, coconePointUniqueUpToIso, comp_coconePointUniqueUpToIso_hom, mono_comp
-/
theorem mono_inl_iff {A B : C} {c₁ c₂ : BinaryCofan A B} (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂) :
    Mono c₁.inl ↔ Mono c₂.inl := by
  suffices
    forall (c₁ c₂ : BinaryCofan A B) (_ : IsColimit c₁) (_ : IsColimit c₂) (_ : Mono c₁.inl),
      Mono c₂.inl
    ⟨fun h₁ => this _ _ hc₁ hc₂ h₁, fun h₂ => this _ _ hc₂ hc₁ h₂⟩
  intro c₁ c₂ hc₁ hc₂ _
  simpa only [IsColimit.comp_coconePointUniqueUpToIso_hom] using!
    mono_comp c₁.inl (hc₁.coconePointUniqueUpToIso hc₂).hom

/--
theorem `mk'` / 定理 `mk'`

English:
theorem mk'
  given: (h : forall A B : C, exists (c : BinaryCofan A B) (_ : IsColimit c), Mono c.inl)
  statement: MonoCoprod C
  proof: ⟨fun A B c' hc' => by
    obtain ⟨c, hc₁, hc₂⟩ := h A B
    simpa only [mono_inl_iff hc' hc₁] using hc₂⟩

中文:
定理 mk'
  条件: (h : 对任意 A B : C, 存在 (c : BinaryCofan A B) (_ : IsColimit c), Mono c.inl)
  结论: MonoCoprod C
  证明: ⟨fun A B c' hc' => by
    obtain ⟨c, hc₁, hc₂⟩ := h A B
    simpa only [mono_inl_iff hc' hc₁] using hc₂⟩

Depends on / 依赖: mono_inl_iff
-/
theorem mk' (h : forall A B : C, exists (c : BinaryCofan A B) (_ : IsColimit c), Mono c.inl) : MonoCoprod C :=
  ⟨fun A B c' hc' => by
    obtain ⟨c, hc₁, hc₂⟩ := h A B
    simpa only [mono_inl_iff hc' hc₁] using hc₂⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `monoCoprodType` / 实例 `monoCoprodType`

English:
instance monoCoprodType
  signature: : MonoCoprod (Type u)
  body: MonoCoprod.mk' fun A B => by
    refine ⟨BinaryCofan.mk (↾(Sum.inl : A -> A oplus B))
      (↾Sum.inr), ?_, ?_⟩
    · exact BinaryCofan.IsColimit.mk _
        (fun f₁ f₂ => ↾fun x => by
          rcases x with x | x
          exacts [f₁ x, f₂ x])
        (fun f₁ f₂ => by rfl)
        (fun f₁ f₂ => b

中文:
实例 monoCoprodType
  签名: : MonoCoprod (类型u)
  定义体: MonoCoprod.mk' fun A B => by
    refine ⟨BinaryCofan.mk (↾(Sum.inl : A -> A oplus B))
      (↾Sum.inr), ?_, ?_⟩
    · exact BinaryCofan.IsColimit.mk _
        (fun f₁ f₂ => ↾fun x => by
          rcases x with x | x
          exacts [f₁ x, f₂ x])
        (fun f₁ f₂ => by rfl)
        (fun f₁ f₂ => b

Depends on / 依赖: BinaryCofan, BinaryCofan.IsColimit.mk, BinaryCofan.mk, ConcreteCategory, ConcreteCategory.congr_hom, IsColimit, MonoCoprod, MonoCoprod.mk, Sum.inl, Sum.inr, congr_hom, exacts, mono_iff_injective
-/
instance monoCoprodType : MonoCoprod (Type u) :=
  MonoCoprod.mk' fun A B => by
    refine ⟨BinaryCofan.mk (↾(Sum.inl : A -> A oplus B))
      (↾Sum.inr), ?_, ?_⟩
    · exact BinaryCofan.IsColimit.mk _
        (fun f₁ f₂ => ↾fun x => by
          rcases x with x | x
          exacts [f₁ x, f₂ x])
        (fun f₁ f₂ => by rfl)
        (fun f₁ f₂ => by rfl)
        (fun f₁ f₂ m h₁ h₂ => by
          ext x
          rcases x with x | x
          · exact ConcreteCategory.congr_hom h₁ x
          · exact ConcreteCategory.congr_hom h₂ x)
    · rw [mono_iff_injective]
      intro a₁ a₂ h
      simpa using h

section

variable {I₁ I₂ : Type*} {X : I₁ oplus I₂ -> C} (c : Cofan X)
  (c₁ : Cofan (X ∘ Sum.inl)) (c₂ : Cofan (X ∘ Sum.inr))
  (hc : IsColimit c) (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂)
include hc hc₁ hc₂

/-- Given a family of objects `X : I₁ ⊕ I₂ → C`, a cofan of `X`, and two colimit cofans
of `X ∘ Sum.inl` and `X ∘ Sum.inr`, this is a cofan for `c₁.pt` and `c₂.pt` whose
point is `c.pt`. -/
@[simp]
/--
Definition of `binaryCofanSum` / `binaryCofanSum` 的定义

English:
definition binaryCofanSum
  signature: : BinaryCofan c₁.pt c₂.pt
  body: BinaryCofan.mk (Cofan.IsColimit.desc hc₁ (fun i₁ => c.inj (Sum.inl i₁)))
    (Cofan.IsColimit.desc hc₂ (fun i₂ => c.inj (Sum.inr i₂)))

中文:
定义 binaryCofanSum
  签名: : BinaryCofan c₁.pt c₂.pt
  定义体: BinaryCofan.mk (Cofan.IsColimit.desc hc₁ (fun i₁ => c.inj (Sum.inl i₁)))
    (Cofan.IsColimit.desc hc₂ (fun i₂ => c.inj (Sum.inr i₂)))

Depends on / 依赖: BinaryCofan, BinaryCofan.mk, Cofan.IsColimit.desc, IsColimit, Sum.inl, Sum.inr, c.inj
-/
def binaryCofanSum : BinaryCofan c₁.pt c₂.pt :=
  BinaryCofan.mk (Cofan.IsColimit.desc hc₁ (fun i₁ => c.inj (Sum.inl i₁)))
    (Cofan.IsColimit.desc hc₂ (fun i₂ => c.inj (Sum.inr i₂)))

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isColimitBinaryCofanSum` / `isColimitBinaryCofanSum` 的定义

English:
definition isColimitBinaryCofanSum
  signature: : IsColimit (binaryCofanSum c c₁ c₂ hc₁ hc₂)
  body: BinaryCofan.IsColimit.mk _ (fun f₁ f₂ => Cofan.IsColimit.desc hc (fun i => match i with
      | Sum.inl i₁ => c₁.inj i₁ ≫ f₁
      | Sum.inr i₂ => c₂.inj i₂ ≫ f₂))
    (fun f₁ f₂ => Cofan.IsColimit.hom_ext hc₁ _ _ (by simp))
    (fun f₁ f₂ => Cofan.IsColimit.hom_ext hc₂ _ _ (by simp))
    (fun f₁ f₂

中文:
定义 isColimitBinaryCofanSum
  签名: : IsColimit (binaryCofanSum c c₁ c₂ hc₁ hc₂)
  定义体: BinaryCofan.IsColimit.mk _ (fun f₁ f₂ => Cofan.IsColimit.desc hc (fun i => match i with
      | Sum.inl i₁ => c₁.inj i₁ ≫ f₁
      | Sum.inr i₂ => c₂.inj i₂ ≫ f₂))
    (fun f₁ f₂ => Cofan.IsColimit.hom_ext hc₁ _ _ (by simp))
    (fun f₁ f₂ => Cofan.IsColimit.hom_ext hc₂ _ _ (by simp))
    (fun f₁ f₂

Depends on / 依赖: BinaryCofan, BinaryCofan.IsColimit.mk, Cofan.IsColimit.desc, Cofan.IsColimit.hom_ext, IsColimit, Sum.inl, Sum.inr, cat_disch, hom_ext
-/
def isColimitBinaryCofanSum : IsColimit (binaryCofanSum c c₁ c₂ hc₁ hc₂) :=
  BinaryCofan.IsColimit.mk _ (fun f₁ f₂ => Cofan.IsColimit.desc hc (fun i => match i with
      | Sum.inl i₁ => c₁.inj i₁ ≫ f₁
      | Sum.inr i₂ => c₂.inj i₂ ≫ f₂))
    (fun f₁ f₂ => Cofan.IsColimit.hom_ext hc₁ _ _ (by simp))
    (fun f₁ f₂ => Cofan.IsColimit.hom_ext hc₂ _ _ (by simp))
    (fun f₁ f₂ m hm₁ hm₂ => by
      apply Cofan.IsColimit.hom_ext hc
      rintro (i₁ | i₂) <;> cat_disch)

/--
lemma `mono_binaryCofanSum_inl` / 引理 `mono_binaryCofanSum_inl`

English:
lemma mono_binaryCofanSum_inl
  given: [MonoCoprod C]
  proof: MonoCoprod.binaryCofan_inl _ (isColimitBinaryCofanSum c c₁ c₂ hc hc₁ hc₂)

中文:
引理 mono_binaryCofanSum_inl
  条件: [MonoCoprod C]
  证明: MonoCoprod.binaryCofan_inl _ (isColimitBinaryCofanSum c c₁ c₂ hc hc₁ hc₂)

Depends on / 依赖: MonoCoprod, MonoCoprod.binaryCofan_inl, binaryCofan_inl, isColimitBinaryCofanSum
-/
lemma mono_binaryCofanSum_inl [MonoCoprod C] :
    Mono (binaryCofanSum c c₁ c₂ hc₁ hc₂).inl :=
  MonoCoprod.binaryCofan_inl _ (isColimitBinaryCofanSum c c₁ c₂ hc hc₁ hc₂)

/--
lemma `mono_binaryCofanSum_inr` / 引理 `mono_binaryCofanSum_inr`

English:
lemma mono_binaryCofanSum_inr
  given: [MonoCoprod C]
  proof: MonoCoprod.binaryCofan_inr _ (isColimitBinaryCofanSum c c₁ c₂ hc hc₁ hc₂)

中文:
引理 mono_binaryCofanSum_inr
  条件: [MonoCoprod C]
  证明: MonoCoprod.binaryCofan_inr _ (isColimitBinaryCofanSum c c₁ c₂ hc hc₁ hc₂)

Depends on / 依赖: MonoCoprod, MonoCoprod.binaryCofan_inr, binaryCofan_inr, isColimitBinaryCofanSum
-/
lemma mono_binaryCofanSum_inr [MonoCoprod C] :
    Mono (binaryCofanSum c c₁ c₂ hc₁ hc₂).inr :=
  MonoCoprod.binaryCofan_inr _ (isColimitBinaryCofanSum c c₁ c₂ hc hc₁ hc₂)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mono_binaryCofanSum_inl'` / 引理 `mono_binaryCofanSum_inl'`

English:
lemma mono_binaryCofanSum_inl'
  statement: [MonoCoprod C] (inl : c₁.pt ⟶ c.pt)
  proof: by
  suffices inl = (binaryCofanSum c c₁ c₂ hc₁ hc₂).inl by
    rw [this]
    exact MonoCoprod.binaryCofan_inl _ (isColimitBinaryCofanSum c c₁ c₂ hc hc₁ hc₂)
  exact Cofan.IsColimit.hom_ext hc₁ _ _ (by simpa using hinl)

中文:
引理 mono_binaryCofanSum_inl'
  结论: [MonoCoprod C] (inl : c₁.pt ⟶ c.pt)
  证明: by
  suffices inl = (binaryCofanSum c c₁ c₂ hc₁ hc₂).inl by
    rw [this]
    exact MonoCoprod.binaryCofan_inl _ (isColimitBinaryCofanSum c c₁ c₂ hc hc₁ hc₂)
  exact Cofan.IsColimit.hom_ext hc₁ _ _ (by simpa using hinl)

Depends on / 依赖: Cofan.IsColimit.hom_ext, IsColimit, MonoCoprod, MonoCoprod.binaryCofan_inl, binaryCofanSum, binaryCofan_inl, hom_ext, isColimitBinaryCofanSum
-/
lemma mono_binaryCofanSum_inl' [MonoCoprod C] (inl : c₁.pt ⟶ c.pt)
    (hinl : forall (i₁ : I₁), c₁.inj i₁ ≫ inl = c.inj (Sum.inl i₁)) :
    Mono inl := by
  suffices inl = (binaryCofanSum c c₁ c₂ hc₁ hc₂).inl by
    rw [this]
    exact MonoCoprod.binaryCofan_inl _ (isColimitBinaryCofanSum c c₁ c₂ hc hc₁ hc₂)
  exact Cofan.IsColimit.hom_ext hc₁ _ _ (by simpa using hinl)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mono_binaryCofanSum_inr'` / 引理 `mono_binaryCofanSum_inr'`

English:
lemma mono_binaryCofanSum_inr'
  statement: [MonoCoprod C] (inr : c₂.pt ⟶ c.pt)
  proof: by
  suffices inr = (binaryCofanSum c c₁ c₂ hc₁ hc₂).inr by
    rw [this]
    exact MonoCoprod.binaryCofan_inr _ (isColimitBinaryCofanSum c c₁ c₂ hc hc₁ hc₂)
  exact Cofan.IsColimit.hom_ext hc₂ _ _ (by simpa using hinr)

中文:
引理 mono_binaryCofanSum_inr'
  结论: [MonoCoprod C] (inr : c₂.pt ⟶ c.pt)
  证明: by
  suffices inr = (binaryCofanSum c c₁ c₂ hc₁ hc₂).inr by
    rw [this]
    exact MonoCoprod.binaryCofan_inr _ (isColimitBinaryCofanSum c c₁ c₂ hc hc₁ hc₂)
  exact Cofan.IsColimit.hom_ext hc₂ _ _ (by simpa using hinr)

Depends on / 依赖: Cofan.IsColimit.hom_ext, IsColimit, MonoCoprod, MonoCoprod.binaryCofan_inr, binaryCofanSum, binaryCofan_inr, hom_ext, isColimitBinaryCofanSum
-/
lemma mono_binaryCofanSum_inr' [MonoCoprod C] (inr : c₂.pt ⟶ c.pt)
    (hinr : forall (i₂ : I₂), c₂.inj i₂ ≫ inr = c.inj (Sum.inr i₂)) :
    Mono inr := by
  suffices inr = (binaryCofanSum c c₁ c₂ hc₁ hc₂).inr by
    rw [this]
    exact MonoCoprod.binaryCofan_inr _ (isColimitBinaryCofanSum c c₁ c₂ hc hc₁ hc₂)
  exact Cofan.IsColimit.hom_ext hc₂ _ _ (by simpa using hinr)

end

section

variable [MonoCoprod C] {I J : Type*} (X : I -> C) (ι : J -> I)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `mono_of_injective_aux` / 引理 `mono_of_injective_aux`

English:
lemma mono_of_injective_aux
  statement: (hι : Function.Injective ι) (c : Cofan X) (c₁ : Cofan (X ∘ ι))
  proof: by
  classical
  let e := ((Equiv.ofInjective ι hι).sumCongr (Equiv.refl _)).trans (Equiv.Set.sumCompl _)
  refine mono_binaryCofanSum_inl' (Cofan.mk c.pt (fun i' => c.inj (e i'))) _ _ ?_
    hc₁ hc₂ _ (by simp [e])
  exact IsColimit.ofIsoColimit ((IsColimit.ofCoconeEquiv (Cocone.equivalenceOfReinde

中文:
引理 mono_of_injective_aux
  结论: (hι : Function.Injective ι) (c : Cofan X) (c₁ : Cofan (X ∘ ι))
  证明: by
  classical
  let e := ((Equiv.ofInjective ι hι).sumCongr (Equiv.refl _)).trans (Equiv.Set.sumCompl _)
  refine mono_binaryCofanSum_inl' (Cofan.mk c.pt (fun i' => c.inj (e i'))) _ _ ?_
    hc₁ hc₂ _ (by simp [e])
  exact IsColimit.ofIsoColimit ((IsColimit.ofCoconeEquiv (Cocone.equivalenceOfReinde

Depends on / 依赖: Cocone, Cocone.equivalenceOfReindexing, Cocone.ext, Cofan.mk, Discrete, Discrete.equivalence, Equiv.Set.sumCompl, Equiv.ofInjective, Equiv.refl, IsColimit, IsColimit.ofCoconeEquiv, IsColimit.ofIsoColimit, Iso.refl, c.inj, c.pt, classical, equivalence, equivalenceOfReindexing, mono_binaryCofanSum_inl, ofCoconeEquiv
-/
lemma mono_of_injective_aux (hι : Function.Injective ι) (c : Cofan X) (c₁ : Cofan (X ∘ ι))
    (hc : IsColimit c) (hc₁ : IsColimit c₁)
    (c₂ : Cofan (fun (k : ((Set.range ι)ᶜ : Set I)) => X k.1))
    (hc₂ : IsColimit c₂) : Mono (Cofan.IsColimit.desc hc₁ (fun i => c.inj (ι i))) := by
  classical
  let e := ((Equiv.ofInjective ι hι).sumCongr (Equiv.refl _)).trans (Equiv.Set.sumCompl _)
  refine mono_binaryCofanSum_inl' (Cofan.mk c.pt (fun i' => c.inj (e i'))) _ _ ?_
    hc₁ hc₂ _ (by simp [e])
  exact IsColimit.ofIsoColimit ((IsColimit.ofCoconeEquiv (Cocone.equivalenceOfReindexing
    (Discrete.equivalence e) (Iso.refl _))).symm hc) (Cocone.ext (Iso.refl _))

variable (hι : Function.Injective ι) (c : Cofan X) (c₁ : Cofan (X ∘ ι))
  (hc : IsColimit c) (hc₁ : IsColimit c₁)
include hι

include hc in
/--
lemma `mono_of_injective` / 引理 `mono_of_injective`

English:
lemma mono_of_injective
  given: [HasCoproduct (fun (k : ((Set.range ι)ᶜ : Set I)) => X k.1)]
  proof: mono_of_injective_aux X ι hι c c₁ hc hc₁ _ (colimit.isColimit _)

中文:
引理 mono_of_injective
  条件: [HasCoproduct (fun (k : ((Set.range ι)ᶜ : Set I)) => X k.1)]
  证明: mono_of_injective_aux X ι hι c c₁ hc hc₁ _ (colimit.isColimit _)

Depends on / 依赖: colimit, colimit.isColimit, isColimit, mono_of_injective_aux
-/
lemma mono_of_injective [HasCoproduct (fun (k : ((Set.range ι)ᶜ : Set I)) => X k.1)] :
    Mono (Cofan.IsColimit.desc hc₁ (fun i => c.inj (ι i))) :=
  mono_of_injective_aux X ι hι c c₁ hc hc₁ _ (colimit.isColimit _)

/--
lemma `mono_of_injective'` / 引理 `mono_of_injective'`

English:
lemma mono_of_injective'
  statement: [HasCoproduct (X ∘ ι)] [HasCoproduct X]
  proof: mono_of_injective X ι hι _ _ (colimit.isColimit _) (colimit.isColimit _)

中文:
引理 mono_of_injective'
  结论: [HasCoproduct (X ∘ ι)] [HasCoproduct X]
  证明: mono_of_injective X ι hι _ _ (colimit.isColimit _) (colimit.isColimit _)
-/
lemma mono_of_injective' [HasCoproduct (X ∘ ι)] [HasCoproduct X]
    [HasCoproduct (fun (k : ((Set.range ι)ᶜ : Set I)) => X k.1)] :
    Mono (Sigma.desc (f := X ∘ ι) (fun j => Sigma.ι X (ι j))) :=
  mono_of_injective X ι hι _ _ (colimit.isColimit _) (colimit.isColimit _)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mono_map'_of_injective` / 引理 `mono_map'_of_injective`

English:
lemma mono_map'_of_injective
  statement: [HasCoproduct (X ∘ ι)] [HasCoproduct X]
  proof: by
  convert! mono_of_injective' X ι hι
  apply Sigma.hom_ext
  intro j
  rw [Sigma.ι_comp_map']; rw [id_comp]; rw [colimit.ι_desc]
  simp

中文:
引理 mono_map'_of_injective
  结论: [HasCoproduct (X ∘ ι)] [HasCoproduct X]
  证明: by
  convert! mono_of_injective' X ι hι
  apply Sigma.hom_ext
  intro j
  rw [Sigma.ι_comp_map']; rw [id_comp]; rw [colimit.ι_desc]
  simp

Depends on / 依赖: Sigma.hom_ext, colimit, convert, hom_ext, id_comp, mono_of_injective
-/
lemma mono_map'_of_injective [HasCoproduct (X ∘ ι)] [HasCoproduct X]
    [HasCoproduct (fun (k : ((Set.range ι)ᶜ : Set I)) => X k.1)] :
    Mono (Sigma.map' ι (fun j => 𝟙 ((X ∘ ι) j))) := by
  convert! mono_of_injective' X ι hι
  apply Sigma.hom_ext
  intro j
  rw [Sigma.ι_comp_map']; rw [id_comp]; rw [colimit.ι_desc]
  simp

end

section

variable [MonoCoprod C] {I : Type*} (X : I -> C)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `mono_inj` / 引理 `mono_inj`

English:
lemma mono_inj
  statement: (c : Cofan X) (h : IsColimit c) (i : I)
  proof: by
  let ι : Unit -> I := fun _ => i
  have hι : Function.Injective ι := fun _ _ _ => rfl
  exact mono_of_injective X ι hι c (Cofan.mk (X i) (fun _ => 𝟙 _)) h
    (Cofan.IsColimit.mk _ (fun s => s.inj ()))

中文:
引理 mono_inj
  结论: (c : Cofan X) (h : IsColimit c) (i : I)
  证明: by
  let ι : Unit -> I := fun _ => i
  have hι : Function.Injective ι := fun _ _ _ => rfl
  exact mono_of_injective X ι hι c (Cofan.mk (X i) (fun _ => 𝟙 _)) h
    (Cofan.IsColimit.mk _ (fun s => s.inj ()))

Depends on / 依赖: Cofan.IsColimit.mk, Cofan.mk, Function, Function.Injective, Injective, IsColimit, mono_of_injective, s.inj
-/
lemma mono_inj (c : Cofan X) (h : IsColimit c) (i : I)
    [HasCoproduct (fun (k : ((Set.range (fun _ : Unit => i))ᶜ : Set I)) => X k.1)] :
    Mono (Cofan.inj c i) := by
  let ι : Unit -> I := fun _ => i
  have hι : Function.Injective ι := fun _ _ _ => rfl
  exact mono_of_injective X ι hι c (Cofan.mk (X i) (fun _ => 𝟙 _)) h
    (Cofan.IsColimit.mk _ (fun s => s.inj ()))

/--
Instance `mono_ι` / 实例 `mono_ι`

English:
instance mono_ι
  signature: [HasCoproduct X] (i : I)
  body: mono_inj X _ (colimit.isColimit _) i

中文:
实例 mono_ι
  签名: [HasCoproduct X] (i : I)
  定义体: mono_inj X _ (colimit.isColimit _) i

Depends on / 依赖: colimit, colimit.isColimit, isColimit, mono_inj
-/
instance mono_ι [HasCoproduct X] (i : I)
    [HasCoproduct (fun (k : ((Set.range (fun _ : Unit => i))ᶜ : Set I)) => X k.1)] :
    Mono (Sigma.ι X i) :=
  mono_inj X _ (colimit.isColimit _) i

end

open CategoryTheory.Functor

section Preservation

variable {D : Type*} [Category* D] (F : C ⥤ D)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `monoCoprod_of_preservesCoprod_of_reflectsMono` / 定理 `monoCoprod_of_preservesCoprod_of_reflectsMono`

English:
theorem monoCoprod_of_preservesCoprod_of_reflectsMono
  statement: [MonoCoprod D]
  proof: by
    let c' := BinaryCofan.mk (F.map c.inl) (F.map c.inr)
    apply mono_of_mono_map F
    change Mono c'.inl
    apply MonoCoprod.binaryCofan_inl
    apply mapIsColimitOfPreservesOfIsColimit F
    apply IsColimit.ofIsoColimit h
    refine Cocone.ext (φ := eqToIso rfl) ?_
    rintro ⟨(j₁ | j₂)⟩ <;

中文:
定理 monoCoprod_of_preservesCoprod_of_reflectsMono
  结论: [MonoCoprod D]
  证明: by
    let c' := BinaryCofan.mk (F.map c.inl) (F.map c.inr)
    apply mono_of_mono_map F
    change Mono c'.inl
    apply MonoCoprod.binaryCofan_inl
    apply mapIsColimitOfPreservesOfIsColimit F
    apply IsColimit.ofIsoColimit h
    refine Cocone.ext (φ := eqToIso rfl) ?_
    rintro ⟨(j₁ | j₂)⟩ <;

Depends on / 依赖: BinaryCofan, BinaryCofan.mk, BinaryCofan.mk_inl, BinaryCofan.mk_inr, Category, Category.comp_id, Cocone, Cocone.ext, F.map, IsColimit, IsColimit.ofIsoColimit, Iso.refl_hom, MonoCoprod, MonoCoprod.binaryCofan_inl, binaryCofan_inl, c.inl, c.inr, comp_id, eqToIso, eqToIso_refl
-/
theorem monoCoprod_of_preservesCoprod_of_reflectsMono [MonoCoprod D]
    [PreservesColimitsOfShape (Discrete WalkingPair) F]
    [ReflectsMonomorphisms F] : MonoCoprod C where
  binaryCofan_inl {A B} c h := by
    let c' := BinaryCofan.mk (F.map c.inl) (F.map c.inr)
    apply mono_of_mono_map F
    change Mono c'.inl
    apply MonoCoprod.binaryCofan_inl
    apply mapIsColimitOfPreservesOfIsColimit F
    apply IsColimit.ofIsoColimit h
    refine Cocone.ext (φ := eqToIso rfl) ?_
    rintro ⟨(j₁ | j₂)⟩ <;> simp only [eqToIso_refl, Iso.refl_hom,
      Category.comp_id, BinaryCofan.mk_inl, BinaryCofan.mk_inr]

end Preservation

section Concrete

instance {FC : outParam <| C -> C -> Type*} {CC : outParam <| C -> Type*}
    [outParam <| forall X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
    [PreservesColimitsOfShape (Discrete WalkingPair) (forget C)]
    [ReflectsMonomorphisms (forget C)] : MonoCoprod C :=
  monoCoprod_of_preservesCoprod_of_reflectsMono (forget C)

end Concrete

end MonoCoprod

instance (A : C) [HasCoproducts.{u} C] [MonoCoprod C] :
    (sigmaConst.{u}.obj A).PreservesMonomorphisms where
  preserves {J I} ι hι := by
    rw [mono_iff_injective] at hι
    exact MonoCoprod.mono_map'_of_injective (fun (i : I) => A) ι hι

end Limits

end CategoryTheory
