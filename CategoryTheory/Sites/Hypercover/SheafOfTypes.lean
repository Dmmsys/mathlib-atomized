/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Hypercover.One
public import Mathlib.CategoryTheory.Limits.Types.Multiequalizer

/-!

# `1`-hypercovers and (pre)sheaves of types

In this file we provide some API for working with `1`-hypercovers for sheaves of types.

## Main declarations

- `CategoryTheory.PreOneHypercover.IsStronglySheafFor`: A pre-`1`-hypercover `E`
  satisfies the strong sheaf condition for a presheaf of types `F` if
  `F` is a sheaf for the `0`-covering and separated for the `1`-coverings.
- `CategoryTheory.PreOneHypercover.IsStronglySheafFor.amalgamate`: Glue
  a family of compatible sections along `E` if `E` satisfies the strong sheaf condition.
- `CategoryTheory.PreOneHypercover.IsStronglySheafFor.isLimitMultifork`: If `E`
  satisfies the strong sheaf condition for `F`, then the multiequalizer diagram
  for `E` is limiting.

-/

universe w

@[expose] public section

namespace CategoryTheory

open Limits Opposite

variable {C : Type*} [Category* C]

namespace PreZeroHypercover

variable {S : C}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If the pre-`0`-hypercover `E` has pairwise pullbacks, the sections over the multifork
associated to a presheaf of types are equivalent to the compatible families on `E`. -/
@[simps]
/--
Definition of `sectionsEquivOfHasPullbacks` / `sectionsEquivOfHasPullbacks` 的定义

English:
definition sectionsEquivOfHasPullbacks
  signature: (E : PreZeroHypercover S)
  body: ⟨s.val, fun i j W gi gj hgij => by
      have heq := s.property ⟨(i, j), ⟨⟩⟩
      dsimp at heq
      rw [← pullback.lift_fst _ _ hgij]
      conv_rhs => rw [← pullback.lift_snd _ _ hgij]
      rw [op_comp]; rw [Functor.map_comp]; rw [op_comp]; rw [Functor.map_comp]
      simp [heq]⟩
  invFun s := ⟨s.val, fun r => s.property _ _ _ _ _ pullback.condition⟩
  left_inv _ := rfl
  right_inv _ := rfl

中文:
定义 sectionsEquivOfHasPullbacks
  签名: (E : PreZeroHypercover S)
  定义体: ⟨s.val, fun i j W gi gj hgij => by
      have heq := s.property ⟨(i, j), ⟨⟩⟩
      dsimp at heq
      rw [← pullback.lift_fst _ _ hgij]
      conv_rhs => rw [← pullback.lift_snd _ _ hgij]
      rw [op_comp]; rw [Functor.map_comp]; rw [op_comp]; rw [Functor.map_comp]
      simp [heq]⟩
  invFun s := ⟨s.val, fun r => s.property _ _ _ _ _ pullback.condition⟩
  left_inv _ := rfl
  right_inv _ := rfl

Depends on / 依赖: Functor, Functor.map_comp, condition, conv_rhs, invFun, left_inv, lift_fst, lift_snd, map_comp, op_comp, property, pullback, pullback.condition, pullback.lift_fst, pullback.lift_snd, right_inv, s.property, s.val
-/
def sectionsEquivOfHasPullbacks (E : PreZeroHypercover S)
    [E.HasPullbacks] (F : Cᵒᵖ ⥤ Type*) :
    (E.toPreOneHypercover.multicospanIndex F).sections ≃
      Subtype (Presieve.Arrows.Compatible F E.f) where
  toFun s :=
    ⟨s.val, fun i j W gi gj hgij => by
      have heq := s.property ⟨(i, j), ⟨⟩⟩
      dsimp at heq
      rw [← pullback.lift_fst _ _ hgij]
      conv_rhs => rw [← pullback.lift_snd _ _ hgij]
      rw [op_comp]; rw [Functor.map_comp]; rw [op_comp]; rw [Functor.map_comp]
      simp [heq]⟩
  invFun s := ⟨s.val, fun r => s.property _ _ _ _ _ pullback.condition⟩
  left_inv _ := rfl
  right_inv _ := rfl

/--
lemma `isLimit_toPreOneHypercover_type_iff` / 引理 `isLimit_toPreOneHypercover_type_iff`

English:
lemma isLimit_toPreOneHypercover_type_iff
  statement: (E : PreZeroHypercover.{w} S) [E.HasPullbacks]
  proof: by
  rw [Multifork.isLimit_types_iff]; rw [Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible]; rw [← Function.Bijective.of_comp_iff' (E.sectionsEquivOfHasPullbacks F).symm.bijective]
  rfl

中文:
引理 isLimit_toPreOneHypercover_type_iff
  结论: (E : PreZeroHypercover.{w} S) [E.有Pullbacks]
  证明: by
  rw [Multifork.isLimit_types_iff]; rw [Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible]; rw [← Function.Bijective.of_comp_iff' (E.sectionsEquivOfHasPullbacks F).symm.bijective]
  rfl

Depends on / 依赖: Bijective, E.sectionsEquivOfHasPullbacks, Function, Function.Bijective.of_comp_iff, Multifork, Multifork.isLimit_types_iff, Presieve, Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible, bijective, isLimit_types_iff, isSheafFor_ofArrows_iff_bijective_toCompabible, of_comp_iff, sectionsEquivOfHasPullbacks, symm.bijective
-/
lemma isLimit_toPreOneHypercover_type_iff (E : PreZeroHypercover.{w} S) [E.HasPullbacks]
    (F : Cᵒᵖ ⥤ Type*) :
    Nonempty (IsLimit <| E.toPreOneHypercover.multifork F) ↔ E.presieve₀.IsSheafFor F := by
  rw [Multifork.isLimit_types_iff]; rw [Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible]; rw [← Function.Bijective.of_comp_iff' (E.sectionsEquivOfHasPullbacks F).symm.bijective]
  rfl

end PreZeroHypercover

/--
lemma `Precoverage.ZeroHypercover.Hom.isSheafFor_iff` / 引理 `Precoverage.ZeroHypercover.Hom.isSheafFor_iff`

English:
lemma Precoverage.ZeroHypercover.Hom.isSheafFor_iff
  statement: [Limits.HasPullbacks C] {K : Precoverage C}
  proof: by
  rw [Presieve.isSheafFor_iff_generate]
  apply Presieve.isSheafFor_subsieve_aux (S := .generate (.ofArrows 𝒰.X 𝒰.f))
  · rw [← Sieve.generate_le_iff, Sieve.generate_sieve, Sieve.generate_le_iff,
      Presieve.ofArrows_le_iff]
    intro i
    rw [← f.w₀]
    exact ⟨_, f.h₀ i, 𝒱.f _, ⟨_⟩, rfl⟩
  · rwa [← Presieve.isSheafFor_iff_generate]
  · intro Y f hf
    rw [← Sieve.pullbackArrows_comm]; rw [← Presieve.isSeparatedFor_iff_generate]; rw [← Presieve.ofArrows_pullback]
    apply H₂

中文:
引理 Precoverage.ZeroHypercover.态射.isSheafFor_iff
  结论: [Limits.有Pullbacks C] {K : Precoverage C}
  证明: by
  rw [Presieve.isSheafFor_iff_generate]
  apply Presieve.isSheafFor_subsieve_aux (S := .generate (.ofArrows 𝒰.X 𝒰.f))
  · rw [← Sieve.generate_le_iff, Sieve.generate_sieve, Sieve.generate_le_iff,
      Presieve.ofArrows_le_iff]
    intro i
    rw [← f.w₀]
    exact ⟨_, f.h₀ i, 𝒱.f _, ⟨_⟩, rfl⟩
  · rwa [← Presieve.isSheafFor_iff_generate]
  · intro Y f hf
    rw [← Sieve.pullbackArrows_comm]; rw [← Presieve.isSeparatedFor_iff_generate]; rw [← Presieve.ofArrows_pullback]
    apply H₂

Depends on / 依赖: Presieve, Presieve.isSeparatedFor_iff_generate, Presieve.isSheafFor_iff_generate, Presieve.isSheafFor_subsieve_aux, Presieve.ofArrows_le_iff, Presieve.ofArrows_pullback, Sieve.generate_le_iff, Sieve.generate_sieve, Sieve.pullbackArrows_comm, generate, generate_le_iff, generate_sieve, isSeparatedFor_iff_generate, isSheafFor_iff_generate, isSheafFor_subsieve_aux, ofArrows, ofArrows_le_iff, ofArrows_pullback, pullbackArrows_comm
-/
lemma Precoverage.ZeroHypercover.Hom.isSheafFor_iff [Limits.HasPullbacks C] {K : Precoverage C}
    [K.IsStableUnderBaseChange] {S : C} {F : Cᵒᵖ ⥤ Type*} {𝒰 𝒱 : K.ZeroHypercover S}
    (f : 𝒰.Hom K 𝒱) (H₁ : Presieve.IsSheafFor F (.ofArrows _ 𝒰.f))
    (H₂ : forall {X : C} (f : X ⟶ S),
      Presieve.IsSeparatedFor F (.ofArrows (𝒰.pullback₂ f).X (𝒰.pullback₂ f).f)) :
    Presieve.IsSheafFor F (.ofArrows 𝒱.X 𝒱.f) := by
  rw [Presieve.isSheafFor_iff_generate]
  apply Presieve.isSheafFor_subsieve_aux (S := .generate (.ofArrows 𝒰.X 𝒰.f))
  · rw [← Sieve.generate_le_iff, Sieve.generate_sieve, Sieve.generate_le_iff,
      Presieve.ofArrows_le_iff]
    intro i
    rw [← f.w₀]
    exact ⟨_, f.h₀ i, 𝒱.f _, ⟨_⟩, rfl⟩
  · rwa [← Presieve.isSheafFor_iff_generate]
  · intro Y f hf
    rw [← Sieve.pullbackArrows_comm]; rw [← Presieve.isSeparatedFor_iff_generate]; rw [← Presieve.ofArrows_pullback]
    apply H₂

namespace PreOneHypercover

variable {X : C} {E : PreOneHypercover.{w} X} {F : Cᵒᵖ ⥤ Type*}

/--
Definition of `IsStronglySeparatedFor` / `IsStronglySeparatedFor` 的定义

English:
structure IsStronglySeparatedFor
  parameters: {X : C} (E : PreOneHypercover X) (F : Cᵒᵖ ⥤ Type*)
  axioms and operations (2):
    - isSeparatedFor_presieve₀ : E.presieve₀.IsSeparatedFor F
    - isSeparatedFor_sieve₁(⦃i j) : E.I₀⦄ ⦃W : C⦄ (p₁ : W ⟶ E.X i) (p₂ : W ⟶ E.X j) (h : p₁ ≫ E.f i = p₂ ≫ E.f j) : (E.sieve₁ p₁ p₂).arrows.IsSeparatedFor F

中文:
结构 是StronglySeparatedFor
  参数: {X : C} (E : PreOneHypercover X) (F : Cᵒᵖ ⥤ 类型)
  公理与运算 (2 个):
    - isSeparatedFor_presieve₀ : E.presieve₀.IsSeparatedFor F
    - isSeparatedFor_sieve₁(⦃i j) : E.I₀⦄ ⦃W : C⦄ (p₁ : W ⟶ E.X i) (p₂ : W ⟶ E.X j) (h : p₁ ≫ E.f i = p₂ ≫ E.f j) : (E.sieve₁ p₁ p₂).arrows.IsSeparatedFor F
-/
structure IsStronglySeparatedFor {X : C} (E : PreOneHypercover X) (F : Cᵒᵖ ⥤ Type*) : Prop where
  isSeparatedFor_presieve₀ : E.presieve₀.IsSeparatedFor F
  isSeparatedFor_sieve₁ ⦃i j : E.I₀⦄ ⦃W : C⦄ (p₁ : W ⟶ E.X i) (p₂ : W ⟶ E.X j)
    (h : p₁ ≫ E.f i = p₂ ≫ E.f j) :
    (E.sieve₁ p₁ p₂).arrows.IsSeparatedFor F

/--
Definition of `IsStronglySheafFor` / `IsStronglySheafFor` 的定义

English:
structure IsStronglySheafFor
  parameters: {X : C} (E : PreOneHypercover X) (F : Cᵒᵖ ⥤ Type*)
  axioms and operations (2):
    - isSheafFor_presieve₀ : E.presieve₀.IsSheafFor F
    - isSeparatedFor_sieve₁(⦃i j) : E.I₀⦄ ⦃W : C⦄ (p₁ : W ⟶ E.X i) (p₂ : W ⟶ E.X j) (h : p₁ ≫ E.f i = p₂ ≫ E.f j) : (E.sieve₁ p₁ p₂).arrows.IsSeparatedFor F

中文:
结构 是StronglySheafFor
  参数: {X : C} (E : PreOneHypercover X) (F : Cᵒᵖ ⥤ 类型)
  公理与运算 (2 个):
    - isSheafFor_presieve₀ : E.presieve₀.IsSheafFor F
    - isSeparatedFor_sieve₁(⦃i j) : E.I₀⦄ ⦃W : C⦄ (p₁ : W ⟶ E.X i) (p₂ : W ⟶ E.X j) (h : p₁ ≫ E.f i = p₂ ≫ E.f j) : (E.sieve₁ p₁ p₂).arrows.IsSeparatedFor F
-/
structure IsStronglySheafFor {X : C} (E : PreOneHypercover X) (F : Cᵒᵖ ⥤ Type*) : Prop where
  isSheafFor_presieve₀ : E.presieve₀.IsSheafFor F
  isSeparatedFor_sieve₁ ⦃i j : E.I₀⦄ ⦃W : C⦄ (p₁ : W ⟶ E.X i) (p₂ : W ⟶ E.X j)
    (h : p₁ ≫ E.f i = p₂ ≫ E.f j) :
    (E.sieve₁ p₁ p₂).arrows.IsSeparatedFor F

/--
lemma `IsStronglySheafFor.isStronglySeparatedFor` / 引理 `IsStronglySheafFor.isStronglySeparatedFor`

English:
lemma IsStronglySheafFor.isStronglySeparatedFor
  given: (h : E.IsStronglySheafFor F)
  proof: h.isSheafFor_presieve₀.isSeparatedFor
  isSeparatedFor_sieve₁ _ _ _ p₁ p₂ w := h.isSeparatedFor_sieve₁ p₁ p₂ w

中文:
引理 是StronglySheafFor.isStronglySeparatedFor
  条件: (h : E.是StronglySheafFor F)
  证明: h.isSheafFor_presieve₀.isSeparatedFor
  isSeparatedFor_sieve₁ _ _ _ p₁ p₂ w := h.isSeparatedFor_sieve₁ p₁ p₂ w

Depends on / 依赖: h.isSheafFor_presieve, isSeparatedFor
-/
lemma IsStronglySheafFor.isStronglySeparatedFor (h : E.IsStronglySheafFor F) :
    E.IsStronglySeparatedFor F where
  isSeparatedFor_presieve₀ := h.isSheafFor_presieve₀.isSeparatedFor
  isSeparatedFor_sieve₁ _ _ _ p₁ p₂ w := h.isSeparatedFor_sieve₁ p₁ p₂ w

/--
lemma `IsStronglySeparatedFor.arrowsCompatible` / 引理 `IsStronglySeparatedFor.arrowsCompatible`

English:
lemma IsStronglySeparatedFor.arrowsCompatible
  statement: (h : E.IsStronglySeparatedFor F)
  proof: by
  rintro i₁ i₂ Z g₁ g₂ heq
  refine (h.isSeparatedFor_sieve₁ g₁ g₂ heq).ext fun W f ⟨T, u, h₁, h₂⟩ => ?_
  rw [← comp_apply]; rw [← Functor.map_comp]; rw [← op_comp]; rw [h₁]
  conv_rhs => rw [← comp_apply, ← Functor.map_comp, ← op_comp, h₂]
  simp [hc]

中文:
引理 是StronglySeparatedFor.arrowsCompatible
  结论: (h : E.是StronglySeparatedFor F)
  证明: by
  rintro i₁ i₂ Z g₁ g₂ heq
  refine (h.isSeparatedFor_sieve₁ g₁ g₂ heq).ext fun W f ⟨T, u, h₁, h₂⟩ => ?_
  rw [← comp_apply]; rw [← Functor.map_comp]; rw [← op_comp]; rw [h₁]
  conv_rhs => rw [← comp_apply, ← Functor.map_comp, ← op_comp, h₂]
  simp [hc]

Depends on / 依赖: Functor, Functor.map_comp, comp_apply, conv_rhs, h.isSeparatedFor_sieve, map_comp, op_comp
-/
lemma IsStronglySeparatedFor.arrowsCompatible (h : E.IsStronglySeparatedFor F)
    (x : forall i, F.obj (op <| E.X i))
    (hc : forall ⦃i j : E.I₀⦄ (k : E.I₁ i j), F.map (E.p₁ k).op (x i) = F.map (E.p₂ k).op (x j)) :
    Presieve.Arrows.Compatible _ E.f x := by
  rintro i₁ i₂ Z g₁ g₂ heq
  refine (h.isSeparatedFor_sieve₁ g₁ g₂ heq).ext fun W f ⟨T, u, h₁, h₂⟩ => ?_
  rw [← comp_apply]; rw [← Functor.map_comp]; rw [← op_comp]; rw [h₁]
  conv_rhs => rw [← comp_apply, ← Functor.map_comp, ← op_comp, h₂]
  simp [hc]

/--
Definition of `IsStronglySheafFor.amalgamate` / `IsStronglySheafFor.amalgamate` 的定义

English:
definition IsStronglySheafFor.amalgamate
  signature: (h : E.IsStronglySheafFor F)
  body: (h.isSheafFor_presieve₀).amalgamate _
    ((h.isStronglySeparatedFor.arrowsCompatible x hc).familyOfElements_compatible)

@[simp]

中文:
定义 是StronglySheafFor.amalgamate
  签名: (h : E.是StronglySheafFor F)
  定义体: (h.isSheafFor_presieve₀).amalgamate _
    ((h.isStronglySeparatedFor.arrowsCompatible x hc).familyOfElements_compatible)

@[simp]

Depends on / 依赖: amalgamate, arrowsCompatible, familyOfElements_compatible, h.isSheafFor_presieve, h.isStronglySeparatedFor.arrowsCompatible, isStronglySeparatedFor
-/
noncomputable def IsStronglySheafFor.amalgamate (h : E.IsStronglySheafFor F)
    (x : forall i, F.obj (op <| E.X i))
    (hc : forall ⦃i j : E.I₀⦄ (k : E.I₁ i j), F.map (E.p₁ k).op (x i) = F.map (E.p₂ k).op (x j)) :
    F.obj (op X) :=
  (h.isSheafFor_presieve₀).amalgamate _
    ((h.isStronglySeparatedFor.arrowsCompatible x hc).familyOfElements_compatible)

@[simp]
/--
lemma `IsStronglySheafFor.map_amalgamate` / 引理 `IsStronglySheafFor.map_amalgamate`

English:
lemma IsStronglySheafFor.map_amalgamate
  statement: (h : E.IsStronglySheafFor F)
  proof: by
  rw [amalgamate]; rw [Presieve.IsSheafFor.valid_glue _ _ _ ⟨i⟩]
  simp

中文:
引理 是StronglySheafFor.map_amalgamate
  结论: (h : E.是StronglySheafFor F)
  证明: by
  rw [amalgamate]; rw [Presieve.IsSheafFor.valid_glue _ _ _ ⟨i⟩]
  simp

Depends on / 依赖: IsSheafFor, Presieve, Presieve.IsSheafFor.valid_glue, amalgamate, valid_glue
-/
lemma IsStronglySheafFor.map_amalgamate (h : E.IsStronglySheafFor F)
    (x : forall i, F.obj (op <| E.X i))
    (hc : forall ⦃i j : E.I₀⦄ (k : E.I₁ i j), F.map (E.p₁ k).op (x i) = F.map (E.p₂ k).op (x j))
    (i : E.I₀) :
    F.map (E.f i).op (h.amalgamate x hc) = x i := by
  rw [amalgamate]; rw [Presieve.IsSheafFor.valid_glue _ _ _ ⟨i⟩]
  simp

/-- `F` satisfies the (strong) sheaf condition for the pre-`1`-hypercover `E`, then
the multiequalizer diagram attached to `E` is limiting. -/
noncomputable
/--
Definition of `IsStronglySheafFor.isLimitMultifork` / `IsStronglySheafFor.isLimitMultifork` 的定义

English:
definition IsStronglySheafFor.isLimitMultifork
  signature: (h : E.IsStronglySheafFor F)
  body: by
  refine Nonempty.some ?_
  rw [Multifork.isLimit_types_iff]
  refine ⟨fun s t hst => ?_, fun s => ?_⟩
  · exact h.isSheafFor_presieve₀.isSeparatedFor.ext fun _ _ ⟨i⟩ => congr($(hst).val i)
  · exact ⟨h.amalgamate s.val fun i j k => s.property ⟨(i, j), k⟩, by
      ext; exact map_amalgamate _ _ _ _⟩

中文:
定义 是StronglySheafFor.isLimitMultifork
  签名: (h : E.是StronglySheafFor F)
  定义体: by
  refine Nonempty.some ?_
  rw [Multifork.isLimit_types_iff]
  refine ⟨fun s t hst => ?_, fun s => ?_⟩
  · exact h.isSheafFor_presieve₀.isSeparatedFor.ext fun _ _ ⟨i⟩ => congr($(hst).val i)
  · exact ⟨h.amalgamate s.val fun i j k => s.property ⟨(i, j), k⟩, by
      ext; exact map_amalgamate _ _ _ _⟩

Depends on / 依赖: Multifork, Multifork.isLimit_types_iff, Nonempty, Nonempty.some, amalgamate, h.amalgamate, h.isSheafFor_presieve, isLimit_types_iff, isSeparatedFor, isSeparatedFor.ext, map_amalgamate, property, s.property, s.val
-/
def IsStronglySheafFor.isLimitMultifork (h : E.IsStronglySheafFor F) :
    IsLimit (E.multifork F) := by
  refine Nonempty.some ?_
  rw [Multifork.isLimit_types_iff]
  refine ⟨fun s t hst => ?_, fun s => ?_⟩
  · exact h.isSheafFor_presieve₀.isSeparatedFor.ext fun _ _ ⟨i⟩ => congr($(hst).val i)
  · exact ⟨h.amalgamate s.val fun i j k => s.property ⟨(i, j), k⟩, by
      ext; exact map_amalgamate _ _ _ _⟩

/--
lemma `IsStronglySheafFor.isSheafFor_sieve_of_pullback` / 引理 `IsStronglySheafFor.isSheafFor_sieve_of_pullback`

English:
lemma IsStronglySheafFor.isSheafFor_sieve_of_pullback
  statement: (h₁ : E.IsStronglySheafFor F)
  proof: by
  intro t ht
  choose s hs huniq using fun i => H i (t.pullback (E.f i)) (ht.pullback (E.f i))
  have hr : Presieve.Arrows.Compatible _ E.f s := by
    intro i j Z gi gj hgij
    refine (h₁.isSeparatedFor_sieve₁ gi gj hgij).ext fun Y f ⟨k, h, hf₁, hf₂⟩ => ?_
    simp only [← comp_apply, ← Functor.map_comp, ← op_comp, hf₁, hf₂]
    simp only [op_comp, Functor.map_comp, comp_apply]
    congr! 1
    refine (H' k).ext fun W p hp => ?_
    simp only [← comp_apply, ← Functor.map_comp, ← op_comp, hs i (p ≫ E.p₁ k) (by simpa),
      hs j (p ≫ E.p₂ k) (by simpa [← E.w])]
    dsimp only [Presieve.FamilyOfElements.pullback]
    congr 1
    simp [E.w]
  obtain ⟨s', hs'⟩ := hr.exists_familyOfElements
  obtain ⟨t', ht', hunique⟩ := (Presieve.isSheafFor_arrows_iff _ _).mp h₁.isSheafFor_presieve₀ _ hr
  refine ⟨t', fun T f hf => (h₂ f).ext fun Z g hg => ?_, fun y hy => ?_⟩
  · obtain ⟨W, w, u, ⟨i⟩, heq⟩ := hg
    rw [← comp_apply]; rw [← Functor.map_comp]; rw [← op_comp]
    have : t (g ≫ f) (by simp [hf]) = t (w ≫ E.f i) (by simp [heq, hf]) := by
      congr 1
      rw [heq]
    simpa [← heq, ht' i, ← t.comp_of_compatible _ ht, this] using! hs i w _
  · refine hunique _ fun i => huniq _ _ fun Z g hg => ?_
    simp [Presieve.FamilyOfElements.pullback, ← hy _ hg]

中文:
引理 是StronglySheafFor.isSheafFor_sieve_of_pullback
  结论: (h₁ : E.是StronglySheafFor F)
  证明: by
  intro t ht
  choose s hs huniq using fun i => H i (t.pullback (E.f i)) (ht.pullback (E.f i))
  have hr : Presieve.Arrows.Compatible _ E.f s := by
    intro i j Z gi gj hgij
    refine (h₁.isSeparatedFor_sieve₁ gi gj hgij).ext fun Y f ⟨k, h, hf₁, hf₂⟩ => ?_
    simp only [← comp_apply, ← Functor.map_comp, ← op_comp, hf₁, hf₂]
    simp only [op_comp, Functor.map_comp, comp_apply]
    congr! 1
    refine (H' k).ext fun W p hp => ?_
    simp only [← comp_apply, ← Functor.map_comp, ← op_comp, hs i (p ≫ E.p₁ k) (by simpa),
      hs j (p ≫ E.p₂ k) (by simpa [← E.w])]
    dsimp only [Presieve.FamilyOfElements.pullback]
    congr 1
    simp [E.w]
  obtain ⟨s', hs'⟩ := hr.exists_familyOfElements
  obtain ⟨t', ht', hunique⟩ := (Presieve.isSheafFor_arrows_iff _ _).mp h₁.isSheafFor_presieve₀ _ hr
  refine ⟨t', fun T f hf => (h₂ f).ext fun Z g hg => ?_, fun y hy => ?_⟩
  · obtain ⟨W, w, u, ⟨i⟩, heq⟩ := hg
    rw [← comp_apply]; rw [← Functor.map_comp]; rw [← op_comp]
    have : t (g ≫ f) (by simp [hf]) = t (w ≫ E.f i) (by simp [heq, hf]) := by
      congr 1
      rw [heq]
    simpa [← heq, ht' i, ← t.comp_of_compatible _ ht, this] using! hs i w _
  · refine hunique _ fun i => huniq _ _ fun Z g hg => ?_
    simp [Presieve.FamilyOfElements.pullback, ← hy _ hg]

Depends on / 依赖: Arrows, Compatible, Functor, Functor.map_comp, Presieve, Presieve.Arrows.Compatible, comp_apply, ht.pullback, map_comp, op_comp, pullback, t.pullback
-/
lemma IsStronglySheafFor.isSheafFor_sieve_of_pullback (h₁ : E.IsStronglySheafFor F)
    (h₂ : forall ⦃Y : C⦄ (f : Y ⟶ X), Presieve.IsSeparatedFor F (E.sieve₀.pullback f).arrows)
    {S : Sieve X}
    (H : forall (i : E.I₀), Presieve.IsSheafFor F (S.pullback (E.f i)).arrows)
    (H' : forall ⦃i j : E.I₀⦄ (k : E.I₁ i j),
      Presieve.IsSeparatedFor F (S.pullback (E.p₁ k ≫ E.f i)).arrows) :
    Presieve.IsSheafFor F S.arrows := by
  intro t ht
  choose s hs huniq using fun i => H i (t.pullback (E.f i)) (ht.pullback (E.f i))
  have hr : Presieve.Arrows.Compatible _ E.f s := by
    intro i j Z gi gj hgij
    refine (h₁.isSeparatedFor_sieve₁ gi gj hgij).ext fun Y f ⟨k, h, hf₁, hf₂⟩ => ?_
    simp only [← comp_apply, ← Functor.map_comp, ← op_comp, hf₁, hf₂]
    simp only [op_comp, Functor.map_comp, comp_apply]
    congr! 1
    refine (H' k).ext fun W p hp => ?_
    simp only [← comp_apply, ← Functor.map_comp, ← op_comp, hs i (p ≫ E.p₁ k) (by simpa),
      hs j (p ≫ E.p₂ k) (by simpa [← E.w])]
    dsimp only [Presieve.FamilyOfElements.pullback]
    congr 1
    simp [E.w]
  obtain ⟨s', hs'⟩ := hr.exists_familyOfElements
  obtain ⟨t', ht', hunique⟩ := (Presieve.isSheafFor_arrows_iff _ _).mp h₁.isSheafFor_presieve₀ _ hr
  refine ⟨t', fun T f hf => (h₂ f).ext fun Z g hg => ?_, fun y hy => ?_⟩
  · obtain ⟨W, w, u, ⟨i⟩, heq⟩ := hg
    rw [← comp_apply]; rw [← Functor.map_comp]; rw [← op_comp]
    have : t (g ≫ f) (by simp [hf]) = t (w ≫ E.f i) (by simp [heq, hf]) := by
      congr 1
      rw [heq]
    simpa [← heq, ht' i, ← t.comp_of_compatible _ ht, this] using! hs i w _
  · refine hunique _ fun i => huniq _ _ fun Z g hg => ?_
    simp [Presieve.FamilyOfElements.pullback, ← hy _ hg]

/--
lemma `IsStronglySheafFor.isSheafFor_of_pullback` / 引理 `IsStronglySheafFor.isSheafFor_of_pullback`

English:
lemma IsStronglySheafFor.isSheafFor_of_pullback
  statement: (h₁ : E.IsStronglySheafFor F)
  proof: by
  rw [Presieve.isSheafFor_iff_generate]
  exact h₁.isSheafFor_sieve_of_pullback h₂ H H'

中文:
引理 是StronglySheafFor.isSheafFor_of_pullback
  结论: (h₁ : E.是StronglySheafFor F)
  证明: by
  rw [Presieve.isSheafFor_iff_generate]
  exact h₁.isSheafFor_sieve_of_pullback h₂ H H'

Depends on / 依赖: Presieve, Presieve.isSheafFor_iff_generate, isSheafFor_iff_generate, isSheafFor_sieve_of_pullback
-/
lemma IsStronglySheafFor.isSheafFor_of_pullback (h₁ : E.IsStronglySheafFor F)
    (h₂ : forall ⦃Y : C⦄ (f : Y ⟶ X), Presieve.IsSeparatedFor F (E.sieve₀.pullback f).arrows)
    {R : Presieve X}
    (H : forall (i : E.I₀), Presieve.IsSheafFor F ((Sieve.generate R).pullback (E.f i)).arrows)
    (H' : forall ⦃i j : E.I₀⦄ (k : E.I₁ i j),
      Presieve.IsSeparatedFor F ((Sieve.generate R).pullback (E.p₁ k ≫ E.f i)).arrows) :
    Presieve.IsSheafFor F R := by
  rw [Presieve.isSheafFor_iff_generate]
  exact h₁.isSheafFor_sieve_of_pullback h₂ H H'

end PreOneHypercover

namespace GrothendieckTopology.OneHypercover

variable {J : GrothendieckTopology C} {X : C} {E : OneHypercover.{w} J X} {F : Cᵒᵖ ⥤ Type*}

/--
lemma `isStronglySeparatedFor` / 引理 `isStronglySeparatedFor`

English:
lemma isStronglySeparatedFor
  given: (hf : Presieve.IsSeparated J F)
  statement: E.IsStronglySeparatedFor F where
  proof: by
    rw [Presieve.isSeparatedFor_iff_generate]
    exact hf _ E.mem₀
  isSeparatedFor_sieve₁ i j W p₁ p₂ h := hf _ (E.mem₁ _ _ _ _ h)

中文:
引理 isStronglySeparatedFor
  条件: (hf : Presieve.是分离 J F)
  结论: E.是StronglySeparatedFor F where
  证明: by
    rw [Presieve.isSeparatedFor_iff_generate]
    exact hf _ E.mem₀
  isSeparatedFor_sieve₁ i j W p₁ p₂ h := hf _ (E.mem₁ _ _ _ _ h)

Depends on / 依赖: E.mem, Presieve, Presieve.isSeparatedFor_iff_generate, isSeparatedFor_iff_generate
-/
lemma isStronglySeparatedFor (hf : Presieve.IsSeparated J F) : E.IsStronglySeparatedFor F where
  isSeparatedFor_presieve₀ := by
    rw [Presieve.isSeparatedFor_iff_generate]
    exact hf _ E.mem₀
  isSeparatedFor_sieve₁ i j W p₁ p₂ h := hf _ (E.mem₁ _ _ _ _ h)

/--
lemma `isStronglySheafFor` / 引理 `isStronglySheafFor`

English:
lemma isStronglySheafFor
  given: (hf : Presieve.IsSheaf J F)
  statement: E.IsStronglySheafFor F where
  proof: by
    rw [Presieve.isSheafFor_iff_generate]
    exact hf _ E.mem₀
  isSeparatedFor_sieve₁ i j W p₁ p₂ h := hf.isSeparated _ (E.mem₁ _ _ _ _ h)

中文:
引理 isStronglySheafFor
  条件: (hf : Presieve.是层 J F)
  结论: E.是StronglySheafFor F where
  证明: by
    rw [Presieve.isSheafFor_iff_generate]
    exact hf _ E.mem₀
  isSeparatedFor_sieve₁ i j W p₁ p₂ h := hf.isSeparated _ (E.mem₁ _ _ _ _ h)

Depends on / 依赖: E.mem, Presieve, Presieve.isSheafFor_iff_generate, hf.isSeparated, isSeparated, isSheafFor_iff_generate
-/
lemma isStronglySheafFor (hf : Presieve.IsSheaf J F) : E.IsStronglySheafFor F where
  isSheafFor_presieve₀ := by
    rw [Presieve.isSheafFor_iff_generate]
    exact hf _ E.mem₀
  isSeparatedFor_sieve₁ i j W p₁ p₂ h := hf.isSeparated _ (E.mem₁ _ _ _ _ h)

variable (E) in
/--
lemma `isSheafFor_sieve_of_pullback` / 引理 `isSheafFor_sieve_of_pullback`

English:
lemma isSheafFor_sieve_of_pullback
  statement: (hF : Presieve.IsSheaf J F) {S : Sieve X}
  proof: by
  refine (E.isStronglySheafFor hF).isSheafFor_sieve_of_pullback ?_ h₁ h₂
  intro Y f
  exact (hF _ (J.pullback_stable _ E.mem₀)).isSeparatedFor

中文:
引理 isSheafFor_sieve_of_pullback
  结论: (hF : Presieve.是层 J F) {S : 筛 X}
  证明: by
  refine (E.isStronglySheafFor hF).isSheafFor_sieve_of_pullback ?_ h₁ h₂
  intro Y f
  exact (hF _ (J.pullback_stable _ E.mem₀)).isSeparatedFor

Depends on / 依赖: E.isStronglySheafFor, E.mem, J.pullback_stable, isSeparatedFor, isSheafFor_sieve_of_pullback, isStronglySheafFor, pullback_stable
-/
lemma isSheafFor_sieve_of_pullback (hF : Presieve.IsSheaf J F) {S : Sieve X}
    (h₁ : forall (i : E.I₀), Presieve.IsSheafFor F (S.pullback (E.f i)).arrows)
    (h₂ : forall ⦃i j : E.I₀⦄ (k : E.I₁ i j),
      Presieve.IsSeparatedFor F (S.pullback (E.p₁ k ≫ E.f i)).arrows) :
    Presieve.IsSheafFor F S.arrows := by
  refine (E.isStronglySheafFor hF).isSheafFor_sieve_of_pullback ?_ h₁ h₂
  intro Y f
  exact (hF _ (J.pullback_stable _ E.mem₀)).isSeparatedFor

/--
lemma `isSheafFor_of_pullback` / 引理 `isSheafFor_of_pullback`

English:
lemma isSheafFor_of_pullback
  statement: (hF : Presieve.IsSheaf J F) {R : Presieve X}
  proof: by
  rw [Presieve.isSheafFor_iff_generate]
  exact E.isSheafFor_sieve_of_pullback hF h₁ h₂

中文:
引理 isSheafFor_of_pullback
  结论: (hF : Presieve.是层 J F) {R : Presieve X}
  证明: by
  rw [Presieve.isSheafFor_iff_generate]
  exact E.isSheafFor_sieve_of_pullback hF h₁ h₂

Depends on / 依赖: E.isSheafFor_sieve_of_pullback, Presieve, Presieve.isSheafFor_iff_generate, isSheafFor_iff_generate, isSheafFor_sieve_of_pullback
-/
lemma isSheafFor_of_pullback (hF : Presieve.IsSheaf J F) {R : Presieve X}
    (h₁ : forall (i : E.I₀), Presieve.IsSheafFor F ((Sieve.generate R).pullback (E.f i)).arrows)
    (h₂ : forall ⦃i j : E.I₀⦄ (k : E.I₁ i j),
      Presieve.IsSeparatedFor F ((Sieve.generate R).pullback (E.p₁ k ≫ E.f i)).arrows) :
    Presieve.IsSheafFor F R := by
  rw [Presieve.isSheafFor_iff_generate]
  exact E.isSheafFor_sieve_of_pullback hF h₁ h₂

end CategoryTheory.GrothendieckTopology.OneHypercover
