/-
Copyright (c) 2024 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Lifting properties and (co)limits

In this file, we show some consequences of lifting properties in the presence of
certain (co)limits.

-/

public section

universe v

namespace CategoryTheory

open Category Limits

variable {C : Type*} [Category* C] {X Y Z W : C}
  {f : X ⟶ Y} {s : X ⟶ Z} {g : Z ⟶ W} {t : Y ⟶ W}

/--
lemma `IsPushout.hasLiftingProperty` / 引理 `IsPushout.hasLiftingProperty`

English:
lemma IsPushout.hasLiftingProperty
  statement: (h : IsPushout s f g t)
  proof: fun {u v} sq => by
    have w : (s ≫ u) ≫ g' = f ≫ (t ≫ v) := by
      rw [← Category.assoc]; rw [← h.w]; rw [Category.assoc]; rw [Category.assoc]; rw [sq.w]
    exact ⟨h.desc u (CommSq.mk w).lift (by rw [CommSq.fac_left]), h.inl_desc ..,
      h.hom_ext (by rw [h.inl_desc_assoc, sq.w]) (by rw [h.inr_desc_assoc, CommSq.fac_right])⟩

中文:
引理 是推出.hasLiftingProperty
  结论: (h : 是推出 s f g t)
  证明: fun {u v} sq => by
    have w : (s ≫ u) ≫ g' = f ≫ (t ≫ v) := by
      rw [← Category.assoc]; rw [← h.w]; rw [Category.assoc]; rw [Category.assoc]; rw [sq.w]
    exact ⟨h.desc u (CommSq.mk w).lift (by rw [CommSq.fac_left]), h.inl_desc ..,
      h.hom_ext (by rw [h.inl_desc_assoc, sq.w]) (by rw [h.inr_desc_assoc, CommSq.fac_right])⟩

Depends on / 依赖: Category, Category.assoc, CommSq, CommSq.fac_left, CommSq.fac_right, CommSq.mk, fac_left, fac_right, h.desc, h.hom_ext, h.inl_desc, h.inl_desc_assoc, h.inr_desc_assoc, hom_ext, inl_desc, inl_desc_assoc, inr_desc_assoc, sq.w
-/
lemma IsPushout.hasLiftingProperty (h : IsPushout s f g t)
    {Z' W' : C} (g' : Z' ⟶ W') [HasLiftingProperty f g'] : HasLiftingProperty g g' where
  sq_hasLift := fun {u v} sq => by
    have w : (s ≫ u) ≫ g' = f ≫ (t ≫ v) := by
      rw [← Category.assoc]; rw [← h.w]; rw [Category.assoc]; rw [Category.assoc]; rw [sq.w]
    exact ⟨h.desc u (CommSq.mk w).lift (by rw [CommSq.fac_left]), h.inl_desc ..,
      h.hom_ext (by rw [h.inl_desc_assoc, sq.w]) (by rw [h.inr_desc_assoc, CommSq.fac_right])⟩

/--
lemma `IsPullback.hasLiftingProperty` / 引理 `IsPullback.hasLiftingProperty`

English:
lemma IsPullback.hasLiftingProperty
  statement: (h : IsPullback s f g t)
  proof: fun {u v} sq => by
    have w : (u ≫ s) ≫ g = f' ≫ v ≫ t := by
      rw [Category.assoc]; rw [h.toCommSq.w]; rw [← Category.assoc]; rw [← Category.assoc]; rw [sq.w]
    exact ⟨h.lift (CommSq.mk w).lift v (by rw [CommSq.fac_right]),
      h.hom_ext (by rw [Category.assoc, h.lift_fst, CommSq.fac_left])
        (by rw [Category.assoc, h.lift_snd, sq.w]), h.lift_snd _ _ _⟩

中文:
引理 是拉回.hasLiftingProperty
  结论: (h : 是拉回 s f g t)
  证明: fun {u v} sq => by
    have w : (u ≫ s) ≫ g = f' ≫ v ≫ t := by
      rw [Category.assoc]; rw [h.toCommSq.w]; rw [← Category.assoc]; rw [← Category.assoc]; rw [sq.w]
    exact ⟨h.lift (CommSq.mk w).lift v (by rw [CommSq.fac_right]),
      h.hom_ext (by rw [Category.assoc, h.lift_fst, CommSq.fac_left])
        (by rw [Category.assoc, h.lift_snd, sq.w]), h.lift_snd _ _ _⟩

Depends on / 依赖: Category, Category.assoc, CommSq, CommSq.fac_left, CommSq.fac_right, CommSq.mk, fac_left, fac_right, h.hom_ext, h.lift, h.lift_fst, h.lift_snd, h.toCommSq.w, hom_ext, lift_fst, lift_snd, sq.w, toCommSq
-/
lemma IsPullback.hasLiftingProperty (h : IsPullback s f g t)
    {X' Y' : C} (f' : X' ⟶ Y') [HasLiftingProperty f' g] : HasLiftingProperty f' f where
  sq_hasLift := fun {u v} sq => by
    have w : (u ≫ s) ≫ g = f' ≫ v ≫ t := by
      rw [Category.assoc]; rw [h.toCommSq.w]; rw [← Category.assoc]; rw [← Category.assoc]; rw [sq.w]
    exact ⟨h.lift (CommSq.mk w).lift v (by rw [CommSq.fac_right]),
      h.hom_ext (by rw [Category.assoc, h.lift_fst, CommSq.fac_left])
        (by rw [Category.assoc, h.lift_snd, sq.w]), h.lift_snd _ _ _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasPushout
  signature: s f] {T₁ T₂
  body: (IsPushout.of_hasPushout s f).hasLiftingProperty p

中文:
实例 [HasPushout
  签名: s f] {T₁ T₂
  定义体: (IsPushout.of_hasPushout s f).hasLiftingProperty p

Depends on / 依赖: IsPushout, IsPushout.of_hasPushout, hasLiftingProperty, of_hasPushout
-/
instance [HasPushout s f] {T₁ T₂ : C} (p : T₁ ⟶ T₂) [HasLiftingProperty f p] :
    HasLiftingProperty (pushout.inl s f) p :=
  (IsPushout.of_hasPushout s f).hasLiftingProperty p

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasPushout
  signature: s f] {T₁ T₂
  body: (IsPushout.of_hasPushout s f).flip.hasLiftingProperty p

中文:
实例 [HasPushout
  签名: s f] {T₁ T₂
  定义体: (IsPushout.of_hasPushout s f).flip.hasLiftingProperty p

Depends on / 依赖: IsPushout, IsPushout.of_hasPushout, flip.hasLiftingProperty, hasLiftingProperty, of_hasPushout
-/
instance [HasPushout s f] {T₁ T₂ : C} (p : T₁ ⟶ T₂) [HasLiftingProperty s p] :
    HasLiftingProperty (pushout.inr s f) p :=
  (IsPushout.of_hasPushout s f).flip.hasLiftingProperty p

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasPullback
  signature: g t] {T₁ T₂
  body: (IsPullback.of_hasPullback g t).hasLiftingProperty p

中文:
实例 [HasPullback
  签名: g t] {T₁ T₂
  定义体: (IsPullback.of_hasPullback g t).hasLiftingProperty p

Depends on / 依赖: IsPullback, IsPullback.of_hasPullback, hasLiftingProperty, of_hasPullback
-/
instance [HasPullback g t] {T₁ T₂ : C} (p : T₁ ⟶ T₂) [HasLiftingProperty p g] :
    HasLiftingProperty p (pullback.snd g t) :=
  (IsPullback.of_hasPullback g t).hasLiftingProperty p

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasPullback
  signature: g t] {T₁ T₂
  body: (IsPullback.of_hasPullback g t).flip.hasLiftingProperty p

中文:
实例 [HasPullback
  签名: g t] {T₁ T₂
  定义体: (IsPullback.of_hasPullback g t).flip.hasLiftingProperty p

Depends on / 依赖: IsPullback, IsPullback.of_hasPullback, flip.hasLiftingProperty, hasLiftingProperty, of_hasPullback
-/
instance [HasPullback g t] {T₁ T₂ : C} (p : T₁ ⟶ T₂) [HasLiftingProperty p t] :
    HasLiftingProperty p (pullback.fst g t) :=
  (IsPullback.of_hasPullback g t).flip.hasLiftingProperty p

set_option backward.isDefEq.respectTransparency false in
instance {J : Type*} {A B : J -> C} [HasProduct A] [HasProduct B]
    (f : (j : J) -> A j ⟶ B j) {X Y : C} (p : X ⟶ Y)
    [forall j, HasLiftingProperty p (f j)] :
    HasLiftingProperty p (Limits.Pi.map f) where
  sq_hasLift {t b} sq := by
    have sq' (j : J) :
        CommSq (t ≫ Pi.π _ j) p (f j) (b ≫ Pi.π _ j) :=
      ⟨by rw [← Category.assoc, ← sq.w]; simp⟩
    exact ⟨⟨{ l := Pi.lift (fun j => (sq' j).lift) }⟩⟩

set_option backward.isDefEq.respectTransparency false in
instance {J : Type*} {A B : J -> C} [HasCoproduct A] [HasCoproduct B]
    (f : (j : J) -> A j ⟶ B j) {X Y : C} (p : X ⟶ Y)
    [forall j, HasLiftingProperty (f j) p] :
    HasLiftingProperty (Limits.Sigma.map f) p where
  sq_hasLift {t b} sq := by
    have sq' (j : J) :
        CommSq (Sigma.ι _ j ≫ t) (f j) p (Sigma.ι _ j ≫ b) :=
      ⟨by simp [sq.w]⟩
    exact ⟨⟨{ l := Sigma.desc (fun j => (sq' j).lift) }⟩⟩

end CategoryTheory
