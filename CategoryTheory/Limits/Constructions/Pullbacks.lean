/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Constructing pullbacks from binary products and equalizers

If a category has binary products and equalizers, then it has pullbacks.
Also, if a category has binary coproducts and coequalizers, then it has pushouts.
-/

public section


universe v u

open CategoryTheory

namespace CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false in
/--
theorem `hasLimit_cospan_of_hasLimit_pair_of_hasLimit_parallelPair` / 定理 `hasLimit_cospan_of_hasLimit_pair_of_hasLimit_parallelPair`

English:
theorem hasLimit_cospan_of_hasLimit_pair_of_hasLimit_parallelPair
  statement: {C : Type u} [𝒞 : Category.{v} C]
  proof: let π₁ : X ⨯ Y ⟶ X := prod.fst
  let π₂ : X ⨯ Y ⟶ Y := prod.snd
  let e := equalizer.ι (π₁ ≫ f) (π₂ ≫ g)
  HasLimit.mk
    { cone :=
PullbackCone.mk (e ≫ π₁) (e ≫ π₂) by
          rw [Category.assoc]; rw [equalizer.condition]
          simp [e]
      isLimit :=
        PullbackCone.IsLimit.mk _ (fun s => equalizer.lift
(prod.lift (s.π.app WalkingCospan.left) (s.π.app WalkingCospan.right)) by
            rw [← Category.assoc]; rw [limit.lift_π]; rw [← Category.assoc]; rw [limit.lift_π]
            exact PullbackCone.condition _)
          (by simp [π₁, e]) (by simp [π₂, e]) fun s m h₁ h₂ => by
          ext
          · simpa using h₁
          · simpa using h₂ }

中文:
定理 hasLimit_cospan_of_hasLimit_pair_of_hasLimit_parallelPair
  结论: {C : 类型u} [𝒞 : 范畴.{v} C]
  证明: let π₁ : X ⨯ Y ⟶ X := prod.fst
  let π₂ : X ⨯ Y ⟶ Y := prod.snd
  let e := equalizer.ι (π₁ ≫ f) (π₂ ≫ g)
  HasLimit.mk
    { cone :=
PullbackCone.mk (e ≫ π₁) (e ≫ π₂) by
          rw [Category.assoc]; rw [equalizer.condition]
          simp [e]
      isLimit :=
        PullbackCone.IsLimit.mk _ (fun s => equalizer.lift
(prod.lift (s.π.app WalkingCospan.left) (s.π.app WalkingCospan.right)) by
            rw [← Category.assoc]; rw [limit.lift_π]; rw [← Category.assoc]; rw [limit.lift_π]
            exact PullbackCone.condition _)
          (by simp [π₁, e]) (by simp [π₂, e]) fun s m h₁ h₂ => by
          ext
          · simpa using h₁
          · simpa using h₂ }

Depends on / 依赖: Category, Category.assoc, HasLimit, HasLimit.mk, IsLimit, PullbackCone, PullbackCone.IsLimit.mk, PullbackCone.condition, PullbackCone.mk, UnivLE, WalkingCospan, WalkingCospan.left, WalkingCospan.right, condition, equalizer, equalizer.condition, equalizer.lift, hasColimitsOfSize, isLimit, limit.lift_
-/
theorem hasLimit_cospan_of_hasLimit_pair_of_hasLimit_parallelPair {C : Type u} [𝒞 : Category.{v} C]
    {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasLimit (pair X Y)]
    [HasLimit (parallelPair (prod.fst ≫ f) (prod.snd ≫ g))] : HasLimit (cospan f g) :=
  let π₁ : X ⨯ Y ⟶ X := prod.fst
  let π₂ : X ⨯ Y ⟶ Y := prod.snd
  let e := equalizer.ι (π₁ ≫ f) (π₂ ≫ g)
  HasLimit.mk
    { cone :=
PullbackCone.mk (e ≫ π₁) (e ≫ π₂) by
          rw [Category.assoc]; rw [equalizer.condition]
          simp [e]
      isLimit :=
        PullbackCone.IsLimit.mk _ (fun s => equalizer.lift
(prod.lift (s.π.app WalkingCospan.left) (s.π.app WalkingCospan.right)) by
            rw [← Category.assoc]; rw [limit.lift_π]; rw [← Category.assoc]; rw [limit.lift_π]
            exact PullbackCone.condition _)
          (by simp [π₁, e]) (by simp [π₂, e]) fun s m h₁ h₂ => by
          ext
          · simpa using h₁
          · simpa using h₂ }

section

attribute [local instance] hasLimit_cospan_of_hasLimit_pair_of_hasLimit_parallelPair

/--
theorem `hasPullbacks_of_hasBinaryProducts_of_hasEqualizers` / 定理 `hasPullbacks_of_hasBinaryProducts_of_hasEqualizers`

English:
theorem hasPullbacks_of_hasBinaryProducts_of_hasEqualizers
  statement: (C : Type u) [Category.{v} C]
  proof: { has_limit := fun F => hasLimit_of_iso (diagramIsoCospan F).symm }

中文:
定理 hasPullbacks_of_hasBinaryProducts_of_hasEqualizers
  结论: (C : 类型u) [范畴.{v} C]
  证明: { has_limit := fun F => hasLimit_of_iso (diagramIsoCospan F).symm }

Depends on / 依赖: diagramIsoCospan, hasLimit_of_iso, has_limit
-/
theorem hasPullbacks_of_hasBinaryProducts_of_hasEqualizers (C : Type u) [Category.{v} C]
    [HasBinaryProducts C] [HasEqualizers C] : HasPullbacks C :=
  { has_limit := fun F => hasLimit_of_iso (diagramIsoCospan F).symm }

end

set_option backward.isDefEq.respectTransparency false in
/--
theorem `hasColimit_span_of_hasColimit_pair_of_hasColimit_parallelPair` / 定理 `hasColimit_span_of_hasColimit_pair_of_hasColimit_parallelPair`

English:
theorem hasColimit_span_of_hasColimit_pair_of_hasColimit_parallelPair
  statement: {C : Type u}
  proof: let ι₁ : Y ⟶ Y ⨿ Z := coprod.inl
  let ι₂ : Z ⟶ Y ⨿ Z := coprod.inr
  let c := coequalizer.π (f ≫ ι₁) (g ≫ ι₂)
  HasColimit.mk
    { cocone :=
PushoutCocone.mk (ι₁ ≫ c) (ι₂ ≫ c) by
          rw [← Category.assoc]; rw [← Category.assoc]; rw [coequalizer.condition]
      isColimit :=
        PushoutCocone.IsColimit.mk _
          (fun s => coequalizer.desc
(coprod.desc (s.ι.app WalkingSpan.left) (s.ι.app WalkingSpan.right)) by
            rw [Category.assoc]; rw [colimit.ι_desc]; rw [Category.assoc]; rw [colimit.ι_desc]
            exact PushoutCocone.condition _)
          (by simp [ι₁, c]) (by simp [ι₂, c]) fun s m h₁ h₂ => by
          ext
          · simpa using h₁
          · simpa using h₂ }

中文:
定理 hasColimit_span_of_hasColimit_pair_of_hasColimit_parallelPair
  结论: {C : 类型u}
  证明: let ι₁ : Y ⟶ Y ⨿ Z := coprod.inl
  let ι₂ : Z ⟶ Y ⨿ Z := coprod.inr
  let c := coequalizer.π (f ≫ ι₁) (g ≫ ι₂)
  HasColimit.mk
    { cocone :=
PushoutCocone.mk (ι₁ ≫ c) (ι₂ ≫ c) by
          rw [← Category.assoc]; rw [← Category.assoc]; rw [coequalizer.condition]
      isColimit :=
        PushoutCocone.IsColimit.mk _
          (fun s => coequalizer.desc
(coprod.desc (s.ι.app WalkingSpan.left) (s.ι.app WalkingSpan.right)) by
            rw [Category.assoc]; rw [colimit.ι_desc]; rw [Category.assoc]; rw [colimit.ι_desc]
            exact PushoutCocone.condition _)
          (by simp [ι₁, c]) (by simp [ι₂, c]) fun s m h₁ h₂ => by
          ext
          · simpa using h₁
          · simpa using h₂ }

Depends on / 依赖: Category, Category.assoc, HasColimit, HasColimit.mk, IsColimit, PushoutCocone, PushoutCocone.IsColimit.mk, PushoutCocone.condition, PushoutCocone.mk, WalkingSpan, WalkingSpan.left, WalkingSpan.right, cocone, coequalizer, coequalizer.condition, coequalizer.desc, colimit, condition, coprod, coprod.desc
-/
theorem hasColimit_span_of_hasColimit_pair_of_hasColimit_parallelPair {C : Type u}
    [𝒞 : Category.{v} C] {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasColimit (pair Y Z)]
    [HasColimit (parallelPair (f ≫ coprod.inl) (g ≫ coprod.inr))] : HasColimit (span f g) :=
  let ι₁ : Y ⟶ Y ⨿ Z := coprod.inl
  let ι₂ : Z ⟶ Y ⨿ Z := coprod.inr
  let c := coequalizer.π (f ≫ ι₁) (g ≫ ι₂)
  HasColimit.mk
    { cocone :=
PushoutCocone.mk (ι₁ ≫ c) (ι₂ ≫ c) by
          rw [← Category.assoc]; rw [← Category.assoc]; rw [coequalizer.condition]
      isColimit :=
        PushoutCocone.IsColimit.mk _
          (fun s => coequalizer.desc
(coprod.desc (s.ι.app WalkingSpan.left) (s.ι.app WalkingSpan.right)) by
            rw [Category.assoc]; rw [colimit.ι_desc]; rw [Category.assoc]; rw [colimit.ι_desc]
            exact PushoutCocone.condition _)
          (by simp [ι₁, c]) (by simp [ι₂, c]) fun s m h₁ h₂ => by
          ext
          · simpa using h₁
          · simpa using h₂ }

section

attribute [local instance] hasColimit_span_of_hasColimit_pair_of_hasColimit_parallelPair

/--
theorem `hasPushouts_of_hasBinaryCoproducts_of_hasCoequalizers` / 定理 `hasPushouts_of_hasBinaryCoproducts_of_hasCoequalizers`

English:
theorem hasPushouts_of_hasBinaryCoproducts_of_hasCoequalizers
  statement: (C : Type u) [Category.{v} C]
  proof: hasPushouts_of_hasColimit_span C

中文:
定理 hasPushouts_of_hasBinaryCoproducts_of_hasCoequalizers
  结论: (C : 类型u) [范畴.{v} C]
  证明: hasPushouts_of_hasColimit_span C

Depends on / 依赖: hasPushouts_of_hasColimit_span
-/
theorem hasPushouts_of_hasBinaryCoproducts_of_hasCoequalizers (C : Type u) [Category.{v} C]
    [HasBinaryCoproducts C] [HasCoequalizers C] : HasPushouts C :=
  hasPushouts_of_hasColimit_span C

end

end CategoryTheory.Limits
