/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Creation of limits and pullbacks

We show some lemmas relating creation of (co)limits and pullbacks (resp. pushouts).
-/

public section

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] {D : Type*} [Category* D]

/--
lemma `HasPullback.of_createsLimit` / 引理 `HasPullback.of_createsLimit`

English:
lemma HasPullback.of_createsLimit
  statement: (F : C ⥤ D) {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S)
  proof: have : HasLimit (cospan f g ⋙ F) := hasLimit_of_iso (cospanCompIso F f g).symm
  hasLimit_of_created _ F

中文:
引理 HasPullback.of_createsLimit
  结论: (F : C ⥤ D) {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S)
  证明: have : HasLimit (cospan f g ⋙ F) := hasLimit_of_iso (cospanCompIso F f g).symm
  hasLimit_of_created _ F

Depends on / 依赖: HasLimit, cospan, cospanCompIso, hasLimit_of_created, hasLimit_of_iso
-/
lemma HasPullback.of_createsLimit (F : C ⥤ D) {X Y S : C} (f : X ⟶ S) (g : Y ⟶ S)
    [CreatesLimit (cospan f g) F] [HasPullback (F.map f) (F.map g)] :
    HasPullback f g :=
  have : HasLimit (cospan f g ⋙ F) := hasLimit_of_iso (cospanCompIso F f g).symm
  hasLimit_of_created _ F

/--
lemma `HasPushout.of_createsColimit` / 引理 `HasPushout.of_createsColimit`

English:
lemma HasPushout.of_createsColimit
  statement: (F : C ⥤ D) {X Y S : C} (f : S ⟶ X) (g : S ⟶ Y)
  proof: have : HasColimit (span f g ⋙ F) := hasColimit_of_iso (spanCompIso F f g)
  hasColimit_of_created _ F

中文:
引理 HasPushout.of_createsColimit
  结论: (F : C ⥤ D) {X Y S : C} (f : S ⟶ X) (g : S ⟶ Y)
  证明: have : HasColimit (span f g ⋙ F) := hasColimit_of_iso (spanCompIso F f g)
  hasColimit_of_created _ F

Depends on / 依赖: HasColimit, hasColimit_of_created, hasColimit_of_iso, spanCompIso
-/
lemma HasPushout.of_createsColimit (F : C ⥤ D) {X Y S : C} (f : S ⟶ X) (g : S ⟶ Y)
    [CreatesColimit (span f g) F] [HasPushout (F.map f) (F.map g)] :
    HasPushout f g :=
  have : HasColimit (span f g ⋙ F) := hasColimit_of_iso (spanCompIso F f g)
  hasColimit_of_created _ F

end CategoryTheory.Limits
